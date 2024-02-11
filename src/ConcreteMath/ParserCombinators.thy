section \<open>Parser Combinators\<close>
theory ParserCombinators
  imports
    Main
    Show.Show
    "HOL-Library.Monad_Syntax"
    "HOL-Library.Sublist"
begin

type_synonym error_message_type = string

type_synonym ('i, 'o) parser_function = "'i list \<Rightarrow> error_message_type + ('i list \<times> 'o)"

definition is_parser :: "('i, 'o) parser_function \<Rightarrow> bool" where
  "is_parser p \<equiv> \<forall>i r v. p i = Inr (r, v) \<longrightarrow> length i \<ge> length r"

lemma is_parserI [intro]:
  assumes "\<And>i r v. p i = Inr (r, v) \<Longrightarrow> length i \<ge> length r"
  shows "is_parser p"
  using assms is_parser_def by blast

lemma is_parserE [elim]:
  assumes "is_parser p"
    and "(\<And>i r v. p i = Inr (r, v) \<Longrightarrow> length i \<ge> length r) \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: is_parser_def)

definition greedy_parser :: "('i, 'o) parser_function \<Rightarrow> bool" where
  "greedy_parser p \<equiv> \<forall>i r v. p i = Inr (r, v) \<longrightarrow> length i > length r"

lemma greedy_parserI [intro]:
  assumes "\<And>i r v. p i = Inr (r, v) \<Longrightarrow> length i > length r"
  shows "greedy_parser p"
  using assms greedy_parser_def by blast

lemma greedy_parserE [elim]:
  assumes "greedy_parser p"
    and "(\<And>i r v. p i = Inr (r, v) \<Longrightarrow> length i > length r) \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: greedy_parser_def)

lemma greedy_parser_implies_is_parser:
  "greedy_parser p \<Longrightarrow> is_parser p"
  unfolding is_parser_def greedy_parser_def
  by (simp add: nat_less_le)

typedef ('i, 'o) parser_scheme = "{p::('i, 'o) parser_function. is_parser p}"
morphisms run_parser abs_parser by auto
setup_lifting type_definition_parser_scheme

typedef ('i, 'o) greedy_parser_scheme = "{p::('i, 'o) parser_function. greedy_parser p}"
morphisms run_greedy abs_greedy by auto
setup_lifting type_definition_greedy_parser_scheme

subsection \<open>Primitive Combinators\<close>

subsubsection \<open>Fail\<close>
definition
  fail_raw :: "error_message_type \<Rightarrow> ('i, 'o) parser_function" where
  "fail_raw msg i = Inl msg"

lemma fail_is_greedy_parser [intro]:
  "greedy_parser (fail_raw s)"
  by (simp add: fail_raw_def greedy_parser_def)

lemma fail_is_parser [intro]:
  "is_parser (fail_raw s)"
  using greedy_parser_implies_is_parser by blast

lift_definition
  fail :: "error_message_type \<Rightarrow> ('i, 'o) parser_scheme"
  is fail_raw by blast

lift_definition
  fail\<g> :: "error_message_type \<Rightarrow> ('i, 'o) greedy_parser_scheme"
  is fail_raw by blast

subsubsection \<open>Expected\<close>
definition
  expected_raw :: "string \<Rightarrow> ('t::show, 'a) parser_function" where
  "expected_raw msg ts = Inl
    (''Expected '' @ msg @ '', but found: '' @ shows_quote (shows (take 30 ts)) [])"

lemma expected_raw_is_parser [intro]:
  "is_parser (expected_raw s)"
  unfolding is_parser_def expected_raw_def shows_quote_def
  by fastforce

lemma expected_raw_is_greedy_parser [intro]:
  "greedy_parser (expected_raw s)"
  unfolding greedy_parser_def expected_raw_def shows_quote_def
  by fastforce

lift_definition
  expected :: "string \<Rightarrow> ('t::show, 'a) parser_scheme"
  is expected_raw by blast

lift_definition
  expected\<g> :: "string \<Rightarrow> ('t::show, 'a) greedy_parser_scheme"
  is expected_raw by blast

subsubsection \<open>Pure\<close>
definition
  pure_raw :: "'o \<Rightarrow> ('i, 'o) parser_function" where
  "pure_raw output i = Inr (i, output)"

lemma pure_raw_is_parser [intro]:
  "is_parser (pure_raw x)"
  by (simp add: is_parser_def pure_raw_def)

lift_definition
  pure :: "'o \<Rightarrow> ('i, 'o) parser_scheme"
  is pure_raw by blast

subsubsection \<open>Satisfy\<close>
definition
  satisfy_raw :: "('i \<Rightarrow> bool) \<Rightarrow> ('i::show, 'i) parser_function" where
  "satisfy_raw P xs =
    (case xs of
       []   \<Rightarrow> expected_raw ''symbol that satisfies predicate'' xs
     | x#xs \<Rightarrow> if P x then Inr (xs, x) else Inl ''satisfy predicate failed'')"

lemma satisfy_is_greedy_parser [intro]:
  "greedy_parser (satisfy_raw P)"
  unfolding greedy_parser_def satisfy_raw_def expected_def expected_raw_def
  using expected_raw_is_parser
    by (simp add: list.case_eq_if)

lift_definition
  satisfy\<g> :: "('i \<Rightarrow> bool) \<Rightarrow> ('i::show, 'i) greedy_parser_scheme"
  is satisfy_raw by blast

subsubsection \<open>Bind\<close>
definition
  bind_raw :: "('i, 'a) parser_function \<Rightarrow> ('a \<Rightarrow> ('i, 'b) parser_function) \<Rightarrow> ('i, 'b) parser_function" where
  "bind_raw p k i =
    (case p i of
       Inl err \<Rightarrow> Inl err
     | Inr (rest, output) \<Rightarrow> k output rest)"

(* NOTE: Following four lemmas Look like `\<or>` truth table, could this be simplified? *)
lemma bind_raw_is_parser [intro]:
  assumes "is_parser p" and "\<And>x. is_parser (f x)" shows "is_parser (bind_raw p f)"
  unfolding greedy_parser_def bind_raw_def is_parser_def
  by (smt (verit, ccfv_SIG) Inl_Inr_False assms is_parser_def order_trans prod.split_sel split_beta sum.case_eq_if sum.collapse(2) sum.disc(2))

lift_definition
  bind :: "('i, 'a) parser_scheme \<Rightarrow> ('a \<Rightarrow> ('i, 'b) parser_scheme) \<Rightarrow> ('i, 'b) parser_scheme"
  is bind_raw by auto

lemma bind_raw_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "\<And>x. greedy_parser (f x)" shows "greedy_parser (bind_raw p f)"
  unfolding greedy_parser_def
  by (smt (verit) Inl_Inr_False ParserCombinators.bind_raw_def assms greedy_parserE order_less_trans prod.split_sel split_beta sum.case_eq_if sum.collapse(2) sum.disc(2))

lift_definition
  bind\<g> :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('a \<Rightarrow> ('i, 'b) greedy_parser_scheme) \<Rightarrow> ('i, 'b) greedy_parser_scheme"
  is bind_raw by blast

lemma greedy_parser_bind_raw_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "\<And>x. is_parser (f x)" shows "greedy_parser (bind_raw p f)"
  unfolding greedy_parser_def bind_raw_def
  by (smt (verit, ccfv_SIG) Inl_Inr_False assms dual_order.strict_trans2 greedy_parser_def is_parserE prod.split_sel split_beta sum.case_eq_if sum.collapse(2) sum.disc(2))

lift_definition
  bind\<g>\<l> :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('a \<Rightarrow> ('i, 'b) parser_scheme) \<Rightarrow> ('i, 'b) greedy_parser_scheme"
  is bind_raw by blast

lemma parser_greedy_bind_raw_is_greedy_parser [intro]:
  assumes "is_parser p" and "\<And>x. greedy_parser (f x)" shows "greedy_parser (bind_raw p f)"
  unfolding greedy_parser_def bind_raw_def
  by (smt (verit, best) Inl_Inr_False assms greedy_parserE is_parserE linorder_not_less not_less_iff_gr_or_eq order_less_trans prod.split_sel split_beta sum.case_eq_if sum.collapse(2) sum.disc(2))

lift_definition
  bind\<g>\<r> :: "('i, 'a) parser_scheme \<Rightarrow> ('a \<Rightarrow> ('i, 'b) greedy_parser_scheme) \<Rightarrow> ('i, 'b) greedy_parser_scheme"
  is bind_raw by (simp add: parser_greedy_bind_raw_is_greedy_parser)

adhoc_overloading
  Monad_Syntax.bind bind_raw bind bind\<g> bind\<g>\<l> bind\<g>\<r>

subsubsection \<open>Map\<close>
definition
  map_raw :: "('a \<Rightarrow> 'b) \<Rightarrow> ('i, 'a) parser_function \<Rightarrow> ('i, 'b) parser_function" (infixl "<$>\<r>" 58) where
  "map_raw f p  = do {
    x \<leftarrow> p;
    pure_raw (f x)
  }"

lemma map_raw_is_parser [intro]:
  assumes "is_parser p" shows "is_parser (map_raw f p)"
  by (simp add: assms bind_raw_is_parser map_raw_def pure_raw_is_parser)

lift_definition
  map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme" (infixl "<$>" 58)
  is map_raw by blast

lemma map_raw_is_greedy_parser [intro]:
  assumes "greedy_parser p" shows "greedy_parser (map_raw f p)"
  by (simp add: assms greedy_parser_bind_raw_is_greedy_parser map_raw_def pure_raw_is_parser)

lift_definition
  mapG :: "('a \<Rightarrow> 'b) \<Rightarrow> ('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme" (infixl "<$>\<g>" 58)
  is map_raw by blast

subsubsection \<open>Product\<close>
(* TODO: Rewrite with overloaded definition *)
definition
  product_raw :: "('i, 'a) parser_function \<Rightarrow> ('i, 'b) parser_function \<Rightarrow> ('i, 'a \<times> 'b) parser_function" where
  "product_raw p q = do {
    a \<leftarrow> p;
    b \<leftarrow> q;
    pure_raw (a, b)
  }"

(* NOTE: Following four lemmas Look like `\<or>` truth table, could this be simplified? *)
lemma product_raw_is_parser [intro]:
  assumes "is_parser p" and "is_parser q" shows "is_parser (product_raw p q)"
  unfolding product_raw_def
  by (simp add: assms bind_raw_is_parser pure_raw_is_parser)

lift_definition
  product :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme \<Rightarrow> ('i, 'a \<times> 'b) parser_scheme"
  is product_raw by blast

lemma product_raw_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "greedy_parser q" shows "greedy_parser (product_raw p q)"
  unfolding product_raw_def
  by (simp add: assms greedy_parser_bind_raw_is_greedy_parser greedy_parser_implies_is_parser pure_raw_is_parser)

lift_definition
  product\<g> :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme \<Rightarrow> ('i, 'a \<times> 'b) greedy_parser_scheme"
  is product_raw by blast

lemma parser_greedy_product_raw_is_greedy_parser [intro]:
  assumes "is_parser p" and "greedy_parser q" shows "greedy_parser (product_raw p q)"
  by (simp add: assms(1) assms(2) greedy_parser_bind_raw_is_greedy_parser parser_greedy_bind_raw_is_greedy_parser product_raw_def pure_raw_is_parser)

lift_definition
  product\<g>\<r> :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme \<Rightarrow> ('i, 'a \<times> 'b) greedy_parser_scheme"
  is product_raw by blast

lemma greedy_parser_product_raw_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "is_parser q" shows "greedy_parser (product_raw p q)"
  unfolding product_raw_def
  by (simp add: assms bind_raw_is_parser greedy_parser_bind_raw_is_greedy_parser pure_raw_is_parser)

lift_definition
  product\<g>\<l> :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) parser_scheme \<Rightarrow> ('i, 'a \<times> 'b) greedy_parser_scheme"
  is product_raw by blast

subsubsection \<open>Either\<close>
definition
  either_raw :: "('i, 'a) parser_function \<Rightarrow> ('i, 'a) parser_function \<Rightarrow> ('i, 'a) parser_function" (infixl "<|>\<r>" 57)
where
  "either_raw p1 p2 i =
    (case p1 i of
      Inr output \<Rightarrow> Inr output
    | Inl _ \<Rightarrow> p2 i)"

lemma alternative_indepotent[simp]:
  "(u <|>\<r> u) = u"
proof -
  have "\<And>i. (u <|>\<r> u) i = u i" by (simp add: either_raw_def sum.case_eq_if)
  thus ?thesis by auto
qed

lemma alternative_associativity:
  "(u <|>\<r> (v <|>\<r> w)) = ((u <|>\<r> v) <|>\<r> w)"
  unfolding either_raw_def
  by (auto split: sum.split)

lemma either_raw_parsers:
  assumes "is_parser (either_raw p q)" shows "is_parser p \<or> is_parser q"
  unfolding either_raw_def is_parser_def
  by (metis assms either_raw_def is_parser_def sum.case(2))

lemma either_raw_greedy_parsers:
  assumes "greedy_parser (either_raw p q)" shows "greedy_parser p \<or> greedy_parser q"
  unfolding either_raw_def greedy_parser_def
  by (metis assms either_raw_def greedy_parser_def sum.case(2))

lemma either_raw_is_parser [intro]:
  assumes "is_parser p" and "is_parser q" shows "is_parser (either_raw p q)"
  unfolding either_raw_def
  by (smt (verit) assms is_parser_def sum.case_eq_if sum.disc(2) sum.expand sum.sel(2))

lift_definition
  either :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme" (infixl "<|>" 57)
  is either_raw by blast

lemma either_raw_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "greedy_parser q" shows "greedy_parser (either_raw p q)"
  unfolding either_raw_def
  by (metis (mono_tags, lifting) assms greedy_parser_def sum.case_eq_if sum.collapse(2))

lift_definition
  either\<g> :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'a) greedy_parser_scheme" (infixl "<|>\<g>" 57)
  is either_raw by blast

lemma parser_greedy_either_raw_is_parser [intro]:
  assumes "is_parser p" and "greedy_parser q" shows "is_parser (either_raw p q)"
  unfolding either_raw_def is_parser_def
  by (metis assms greedy_parserE is_parserE less_imp_le_nat sum.case_eq_if sum.collapse(2))

lift_definition
  either\<p>\<l> :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'a) parser_scheme" (infixl "<|>\<p>\<l>" 57)
  is either_raw by blast

lemma greedy_parser_either_raw_is_parser [intro]:
  assumes "greedy_parser p" and "is_parser q" shows "is_parser (either_raw p q)"
  unfolding either_raw_def is_parser_def greedy_parser_def
  by (metis assms greedy_parser_implies_is_parser is_parserE sum.case_eq_if sum.collapse(2))

lift_definition
  either\<p>\<r> :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'a) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme" (infixl "<|>\<p>\<r>" 57)
  is either_raw by blast

lemma greedy_parser_either_raw_fail [simp]:
  "greedy_parser (p <|>\<r> fail_raw s) = greedy_parser p"
  unfolding fail_raw_def
  by (metis Inl_Inr_False either_raw_def either_raw_is_greedy_parser greedy_parser_def sum.case(2))

lemma greedy_parser_either_raw_expected [simp]:
  "greedy_parser (p <|>\<r> expected_raw s) = greedy_parser p"
  unfolding expected_raw_def
  by (smt (verit, best) Inl_Inr_False either_raw_def either_raw_is_greedy_parser greedy_parser_def sum.case(2))

lemma is_parser_either_raw_fail [simp]:
  "is_parser (p <|>\<r> fail_raw s) = is_parser p"
  by (metis (full_types) either_raw_def either_raw_is_parser fail_is_parser is_parser_def old.sum.simps(6))

lemma is_parser_either_raw_expected [simp]:
  "is_parser (p <|>\<r> expected_raw s) = is_parser p"
  unfolding expected_raw_def
  by (smt (verit, best) Inl_Inr_False either_raw_def either_raw_is_parser is_parser_def sum.case(2))

subsection \<open>Additional combinators\<close>

abbreviation
  empty :: "('i, 'o) parser_scheme" where
  "empty \<equiv> fail ''''"

subsubsection \<open>Applicative map\<close>

definition
  amap_raw :: "('i, ('a \<Rightarrow> 'b)) parser_function \<Rightarrow> ('i, 'a) parser_function \<Rightarrow> ('i, 'b) parser_function" (infixl "<*>\<r>" 58)
where
  "amap_raw pf px = ((\<lambda>(f, x). f x) <$>\<r> (product_raw pf px))"

lemma amap_raw_is_parser [intro]:
  assumes "is_parser pf" and "is_parser px" shows "is_parser (amap_raw pf px)"
  unfolding amap_raw_def
  using assms by blast

lift_definition
  amap :: "('i, ('a \<Rightarrow> 'b)) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme" (infixl "<*>" 58)
  is amap_raw by blast

lemma amap_raw_is_greedy_parser [intro]:
  assumes "greedy_parser pf" and "greedy_parser px" shows "greedy_parser (amap_raw pf px)"
  unfolding amap_raw_def
  using assms by blast

lift_definition
  amap\<g> :: "('i, ('a \<Rightarrow> 'b)) greedy_parser_scheme \<Rightarrow> ('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme" (infixl "<*>\<g>" 58)
  is amap_raw by blast

lemma parser_greedy_amap_raw_is_greedy_parser [intro]:
  assumes "is_parser pf" and "greedy_parser px" shows "greedy_parser (amap_raw pf px)"
  unfolding amap_raw_def
  using assms by blast

lift_definition
  amap\<g>\<r> :: "('i, ('a \<Rightarrow> 'b)) parser_scheme \<Rightarrow> ('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme" (infixl "<*>\<g>\<r>" 58)
  is amap_raw by blast

lemma greedy_parser_amap_raw_is_greedy_parser [intro]:
  assumes "greedy_parser pf" and "is_parser px" shows "greedy_parser (amap_raw pf px)"
  unfolding amap_raw_def
  using assms by blast

lift_definition
  amap\<g>\<l> :: "('i, ('a \<Rightarrow> 'b)) greedy_parser_scheme \<Rightarrow> ('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme" (infixl "<*>\<g>\<l>" 58)
  is amap_raw by blast

lemma pure_raw_f_amap [simp, code_unfold]:
  "(pure_raw f <*>\<r> p) = (f <$>\<r> p)"
  unfolding amap_raw_def map_raw_def pure_raw_def product_raw_def bind_raw_def
  by (auto split: sum.split)

lemma applicative_identity [simp, code_unfold]:
  "(pure_raw id <*>\<r> p) = p"
  unfolding pure_raw_def amap_raw_def map_raw_def product_raw_def bind_raw_def
  by (auto split: sum.split)

lemma applicative_homomorphism [simp, code_unfold]:
  "(pure_raw f <*>\<r> pure_raw x) = pure_raw (f x)"
  unfolding map_raw_def pure_raw_def amap_raw_def product_raw_def bind_raw_def
  by (auto split: sum.split)

lemma applicative_interchange:
  "(u <*>\<r> pure_raw x) = (pure_raw (\<lambda>f. f x) <*>\<r> u)"
  unfolding product_raw_def pure_raw_def amap_raw_def map_raw_def bind_raw_def
  by (auto split: sum.split)

lemma applicative_composition [simp]:
  "(((pure_raw (\<circ>) <*>\<r> u) <*>\<r> v) <*>\<r> w) = (u <*>\<r> (v <*>\<r> w))"
  unfolding pure_raw_def map_raw_def amap_raw_def product_raw_def bind_raw_def
  by (auto split: sum.split)

subsubsection \<open>Right\<close>
definition
  right_raw :: "('i, 'a) parser_function \<Rightarrow> ('i, 'b) parser_function \<Rightarrow> ('i, 'b) parser_function" (infixl "*>\<r>" 58)
where
  "right_raw p q = ((\<lambda>x.\<lambda>y. y) <$>\<r> p <*>\<r> q)"

lemma right_raw_is_parser [intro]:
  assumes "is_parser p" and "is_parser q" shows "is_parser (right_raw p q)"
  unfolding right_raw_def
  using assms by blast

lift_definition
  right :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme" (infixl "*>" 58)
  is right_raw by blast

lemma right_raw_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "greedy_parser q" shows "greedy_parser (right_raw p q)"
  unfolding right_raw_def
  using assms by blast

lift_definition
  right\<g> :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme" (infixl "*>\<g>" 58)
  is right_raw by blast

lemma parser_greedy_right_raw_is_greedy_parser [intro]:
  assumes "is_parser p" and "greedy_parser q" shows "greedy_parser (right_raw p q)"
  unfolding right_raw_def
  using assms by blast

lift_definition
  right\<g>\<r> :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme" (infixl "*>\<g>\<r>" 58)
  is right_raw by blast

lemma greedy_parser_right_raw_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "is_parser q" shows "greedy_parser (right_raw p q)"
  unfolding right_raw_def
  using assms by blast

lift_definition
  right\<g>\<l> :: "('i, 'a') greedy_parser_scheme \<Rightarrow> ('i, 'b) parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme" (infixl "*>\<g>\<l>" 58)
  is right_raw by blast

subsubsection \<open>Left\<close>
definition
  left_raw :: "('i, 'a) parser_function \<Rightarrow> ('i, 'b) parser_function \<Rightarrow> ('i, 'a) parser_function" (infixl "<*\<r>" 58)
where
  "left_raw p q = ((\<lambda>x.\<lambda>y. x) <$>\<r> p <*>\<r> q)"

lemma left_raw_is_parser [intro]:
  assumes "is_parser p" and "is_parser q" shows "is_parser (left_raw p q)"
  unfolding left_raw_def
  using assms by blast

lift_definition
  left :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme" (infixl "<*" 58)
  is left_raw by blast

lemma left_raw_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "greedy_parser q" shows "greedy_parser (left_raw p q)"
  unfolding left_raw_def
  using assms by blast

lift_definition
  left\<g> :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme \<Rightarrow> ('i, 'a) greedy_parser_scheme" (infixl "<*\<g>" 58)
  is left_raw by blast

lemma parser_greedy_left_raw_is_greedy_parser [intro]:
  assumes "is_parser p" and "greedy_parser q" shows "greedy_parser (left_raw p q)"
  unfolding left_raw_def
  using assms by blast

lift_definition
  left\<g>\<r> :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme \<Rightarrow> ('i, 'a) greedy_parser_scheme" (infixl "<*\<g>\<r>" 58)
  is left_raw by blast

lemma greedy_parser_left_raw_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "is_parser q" shows "greedy_parser (left_raw p q)"
  unfolding left_raw_def
  using assms by blast

lift_definition
  left\<g>\<l> :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) parser_scheme \<Rightarrow> ('i, 'a) greedy_parser_scheme" (infixl "<*\<g>\<l>" 58)
  is left_raw by blast

subsubsection \<open>Entry\<close>
definition
  entry_raw :: "'i \<Rightarrow> ('i, 'i::show) parser_function" where
  "entry_raw s = (satisfy_raw (\<lambda>x. x = s) <|>\<r> (expected_raw (''entry `'' @ show s @ ''`'')))"

lemma entry_is_greedy_parser [intro]:
  "greedy_parser (entry_raw c)"
  unfolding entry_raw_def
  by (simp add: satisfy_is_greedy_parser)

lift_definition
  entry :: "'i \<Rightarrow> ('i, 'i::show) parser_scheme"
  is entry_raw by (simp add: entry_is_greedy_parser greedy_parser_implies_is_parser)

lift_definition
  entry\<g> :: "'i \<Rightarrow> ('i, 'i::show) greedy_parser_scheme"
  is entry_raw by blast

subsubsection \<open>Exactly\<close>

definition
  exactly_raw ::  "'i list \<Rightarrow> ('i, 'i::show list) parser_function" where
  "exactly_raw s i =
  (if prefix s i \<and> length s > 0
  then Inr (drop (length s) i, take (length s) i)
  else expected_raw (''exactly \"'' @ show s @ ''\"'') i)"

lemma exactly_raw_is_parser [intro]:
  "is_parser (exactly_raw s)"
  unfolding is_parser_def exactly_raw_def expected_raw_def
  by simp

lemma exactly_raw_is_greedy_parser [intro]:
  "greedy_parser (exactly_raw s)"
  unfolding greedy_parser_def exactly_raw_def expected_raw_def
  by (metis Inl_Inr_False Inr_inject Pair_inject diff_less length_drop length_greater_0_conv prefix_bot.extremum_unique)

lift_definition
  exactly :: "'i list \<Rightarrow> ('i, 'i::show list) parser_scheme"
  is exactly_raw by blast

lift_definition
  exactly\<g> :: "'i list \<Rightarrow> ('i, 'i::show list) greedy_parser_scheme"
  is exactly_raw by blast

subsubsection \<open>Optional\<close>
definition
  optional_raw :: "('i, 'o) parser_function \<Rightarrow> ('i, 'o option) parser_function" where
  "optional_raw p = (Some <$>\<r> p <|>\<r> pure_raw None)"

lemma optional_raw_is_parser [intro]:
  assumes "is_parser p" shows "is_parser (optional_raw p)"
  unfolding optional_raw_def
  by (simp add: assms either_raw_is_parser map_raw_is_parser pure_raw_is_parser)

lift_definition
  optional :: "('i, 'o) parser_scheme \<Rightarrow> ('i, 'o option) parser_scheme"
  is optional_raw by blast

subsubsection \<open>Repeated\<close>
fun
  repeated_raw :: "nat \<Rightarrow> ('i, 'o) parser_function \<Rightarrow> ('i, 'o list) parser_function" where
  "repeated_raw 0 p = pure_raw []" |
  "repeated_raw (Suc n) p = ((#) <$>\<r> p <*>\<r> repeated_raw n p)"

lemma repeated_raw_is_parser [intro]:
  assumes "is_parser p" shows "is_parser (repeated_raw n p)"
proof (induction n)
  case 0
  thus ?case
    by (simp add: pure_raw_is_parser)
next
  case (Suc n)
  thus ?case
  proof
    assume "(\<And>i r v. repeated_raw n p i = Inr (r, v) \<Longrightarrow> length r \<le> length i)"
    show "is_parser (repeated_raw (Suc n) p)"
      using repeated_raw.simps
      by (simp add: Suc amap_raw_is_parser assms map_raw_is_parser)
  qed
qed

lift_definition
  repeated :: "nat \<Rightarrow> ('i, 'o) parser_scheme \<Rightarrow> ('i, 'o list) parser_scheme"
  is repeated_raw by blast

lemma repeated_raw_is_greedy [intro]:
  assumes "greedy_parser p" shows "greedy_parser (repeated_raw (Suc n) p)"
proof (induction n)
  case 0
  thus ?case
    unfolding repeated_raw.simps
    using assms
    by blast
next
  case (Suc n)
  thus ?case unfolding repeated_raw.simps(2)
    by (simp add: amap_raw_is_greedy_parser assms map_raw_is_greedy_parser)
qed

text \<open>Please be aware that this function just adds 1 to the number of repetitions!\<close>
lift_definition
  repeated\<g> :: "nat \<Rightarrow> ('i, 'o) greedy_parser_scheme \<Rightarrow> ('i, 'o list) greedy_parser_scheme"
  is "(\<lambda>n. repeated_raw (Suc n))" using repeated_raw_is_greedy by auto

lemma repeated_raw_pure_eq_pure_raw_replicate [simp, code_unfold]:
  "repeated_raw n (pure_raw x) = pure_raw (replicate n x)"
proof (induction n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  moreover have "(amap_raw (map_raw (#) (pure_raw x)) (pure_raw (replicate n x))) = pure_raw (replicate (Suc n) x)"
    by (metis applicative_homomorphism pure_raw_f_amap replicate_Suc)
  ultimately show ?case unfolding repeated_raw.simps by simp
qed

subsubsection \<open>Many\<close>

function
  many_raw :: "('i, 'o) greedy_parser_scheme \<Rightarrow> ('i, 'o list) parser_function" where
  "many_raw p i =
  (case run_greedy p i of
    Inl _ \<Rightarrow> Inr (i, [])
  | Inr (r, v) \<Rightarrow>
    (case many_raw p r of
      Inl _ \<Rightarrow> Inr (r, [v])
    | Inr (r', v') \<Rightarrow> Inr (r', (v # v'))))"
by auto

termination
  using run_greedy
  by (relation \<open>measure (\<lambda>(_, i). length i)\<close>) fastforce+

lemma many_raw_is_parser [intro]:
  "is_parser (many_raw p)" unfolding is_parser_def
proof
  show "\<forall>r v. many_raw p i = Inr (r, v) \<longrightarrow> length r \<le> length i" for i
  proof (induct rule: many_raw.induct)
    case (1 xs) thus ?case
      using run_greedy
      by (subst many_raw.simps)
         (fastforce split: sum.splits simp del: many_raw.simps)
  qed
qed

lift_definition
  many :: "('i, 'o) greedy_parser_scheme \<Rightarrow> ('i, 'o list) parser_scheme"
  is many_raw by blast

subsubsection \<open>Many1\<close>
definition
  many1_raw :: "('i, 'o) greedy_parser_scheme \<Rightarrow> ('i, 'o list) parser_function" where
  "many1_raw p = ((#) <$>\<r> run_greedy p <*>\<r> many_raw p)"

lemma many1_raw_is_greedy_parser [intro]:
  "greedy_parser (many1_raw p)"
  unfolding many1_raw_def
proof -
  have "greedy_parser (map_raw (#) (run_greedy p))" using run_greedy by auto
  moreover have "is_parser (many_raw p)" by auto
  ultimately show "greedy_parser (amap_raw (map_raw (#) (run_greedy p)) (many_raw p))" by auto
qed

lemma many1_raw_is_parser [intro]:
  "is_parser (many1_raw p)"
  by (simp add: greedy_parser_implies_is_parser many1_raw_is_greedy_parser)

lift_definition
  many1 :: "('i, 'o) greedy_parser_scheme \<Rightarrow> ('i, 'o list) parser_scheme"
  is many1_raw by blast

lift_definition
  many1\<g> :: "('i, 'o) greedy_parser_scheme \<Rightarrow> ('i, 'o list) greedy_parser_scheme"
  is many1_raw by blast

subsubsection \<open>Separated by, at least one\<close>
definition
  sep_by1 :: "('i, 'sep) greedy_parser_scheme \<Rightarrow> ('i, 'o) greedy_parser_scheme \<Rightarrow> ('i, 'o list) greedy_parser_scheme" where
  "sep_by1 sep p = ((#) <$>\<g> p <*>\<g>\<l> (many (sep *>\<g> p)))"

subsubsection \<open>Separated by\<close>
definition
  sep_by :: "('i, 'sep) greedy_parser_scheme \<Rightarrow> ('i, 'o) greedy_parser_scheme \<Rightarrow> ('i, 'o list) parser_scheme" where
  "sep_by sep p = (sep_by1 sep p <|>\<p>\<r> pure [])"

subsubsection \<open>Take while\<close>
definition
  take_while :: "('i \<Rightarrow> bool) \<Rightarrow> ('i, 'i::show list) parser_scheme" where
  "take_while p = many (satisfy\<g> p)"

subsubsection \<open>Drop while\<close>
definition
  drop_while :: "('i::show \<Rightarrow> bool) \<Rightarrow> ('i, unit) parser_scheme" where
  "drop_while p = ((\<lambda>_. ()) <$> many (satisfy\<g> p))"

subsection \<open>Common parsers\<close>

subsubsection \<open>Ascii white space\<close>
text \<open>Removes all characters that belong to ASCII white space characters: ' ', '\t', '\r', '\n', '\f', '\v'\<close>
definition
  ascii_space_chars :: "char list" where
  "ascii_space_chars = List.map char_of [0x20::nat, 0x9, 0xd, 0xa, 0xc, 0xb]"

definition
  ascii_spaces :: "(char, unit) parser_scheme" where
  "ascii_spaces = ((\<lambda>_. Unity) <$> many (satisfy\<g> (\<lambda>c. c \<in> (set ascii_space_chars))))"

definition
  ascii_spaces\<g> :: "(char, unit) greedy_parser_scheme" where
  "ascii_spaces\<g> = ((\<lambda>_. Unity) <$>\<g> many1\<g> (satisfy\<g> (\<lambda>c. c \<in> (set ascii_space_chars))))"

subsubsection \<open>Number\<close>
definition
  alphabet :: string where
  "alphabet = ''0123456789ABCDEF''"

definition
  nat_of_char :: "char \<Rightarrow> nat" where
  "nat_of_char c = of_char c - (of_char CHR ''0'')"

definition
  decimal_digit :: "(char, nat) greedy_parser_scheme" where
  "decimal_digit = (nat_of_char <$>\<g> (satisfy\<g> (\<lambda>c. c \<in> set (take 10 alphabet))))"

definition
  nat_of_decimal_digits :: "nat list \<Rightarrow> nat" where
  "nat_of_decimal_digits = foldl (\<lambda>a n. a * 10 + n) 0"

definition
  decimal :: "(char, nat) greedy_parser_scheme" where
  "decimal = (nat_of_decimal_digits <$>\<g> many1\<g> decimal_digit)"

end
