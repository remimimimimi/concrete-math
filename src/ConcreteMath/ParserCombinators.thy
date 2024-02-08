section \<open>Parser Combinators\<close>
theory ParserCombinators
  imports
    Main
    Show.Show
    "HOL-Library.Monad_Syntax"
    Certification_Monads.Error_Monad
begin

type_synonym error_message_type = string

type_synonym ('i, 'o) parser_scheme = "'i list \<Rightarrow> error_message_type + ('i list \<times> 'o)"

definition is_parser :: "('i, 'o) parser_scheme \<Rightarrow> bool" where
  "is_parser p \<equiv> \<forall>i r v. p i = return (r, v) \<longrightarrow> length i \<ge> length r"

lemma is_parserI [intro]:
  assumes "\<And>i r v. p i = return (r, v) \<Longrightarrow> length i \<ge> length r"
  shows "is_parser p"
  using assms is_parser_def by blast

lemma is_parserE [elim]:
  assumes "is_parser p"
    and "(\<And>i r v. p i = return (r, v) \<Longrightarrow> length i \<ge> length r) \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: is_parser_def)

definition greedy_parser :: "('i, 'o) parser_scheme \<Rightarrow> bool" where
  "greedy_parser p \<equiv> \<forall>i r v. p i = return (r, v) \<longrightarrow> length i > length r"

lemma greedy_parserI [intro]:
  assumes "\<And>i r v. p i = return (r, v) \<Longrightarrow> length i > length r"
  shows "greedy_parser p"
  using assms greedy_parser_def by blast

lemma greedy_parserE [elim]:
  assumes "greedy_parser p"
    and "(\<And>i r v. p i = return (r, v) \<Longrightarrow> length i > length r) \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: greedy_parser_def)

lemma greedy_parser_implies_is_parser:
  "greedy_parser p \<Longrightarrow> is_parser p"
  unfolding is_parser_def greedy_parser_def
  by (simp add: nat_less_le)

typedef ('i, 'o) greedy_parser_scheme = "{p::('i, 'o) parser_scheme. (greedy_parser p)}"
morphisms rep_greedy abs_greedy
by auto

setup_lifting type_definition_greedy_parser_scheme

definition expected :: "string \<Rightarrow> ('t::show, 'a) parser_scheme" where
  "expected msg ts = error
    (''Expected '' @ msg @ '', but found: '' @ shows_quote (shows (take 30 ts)) [])"

subsection \<open>Primitive Combinators\<close>

definition
  fail :: "error_message_type \<Rightarrow> ('i, 'o) parser_scheme" where
  "fail msg i = error msg"

definition
  pure :: "'o \<Rightarrow> ('i, 'o) parser_scheme" where
  "pure output i = return (i, output)"

(* TODO: Add show*)
definition
  satisfy :: "('i \<Rightarrow> bool) \<Rightarrow> ('i::show, 'i) parser_scheme" where
  "satisfy P xs =
    (case xs of
       []   \<Rightarrow> expected ''symbol that satisfies predicate'' xs
     | x#xs \<Rightarrow> if P x then Inr (xs, x) else error ''hi'')"

definition
  bind :: "('i, 'a) parser_scheme \<Rightarrow> ('a \<Rightarrow> ('i, 'b) parser_scheme) \<Rightarrow> ('i, 'b) parser_scheme" where
  "bind p k i =
    (case p i of
       Inl err \<Rightarrow> Inl err
     | Inr (rest, output) \<Rightarrow> k output rest)"

adhoc_overloading
  Monad_Syntax.bind bind

definition
  map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme" (infixl "<$>" 58) where
  "map f p i =
    (case p i of
       Inl err \<Rightarrow> Inl err
     | Inr (i', v) \<Rightarrow> Inr (i', f v))"

definition
  product :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme \<Rightarrow> ('i, 'a \<times> 'b) parser_scheme" where
  "product p1 p2 i =
    (case p1 i of
       Inl err \<Rightarrow> Inl err
     | Inr (i1, v1) \<Rightarrow>
       (case p2 i1 of
          Inl err' \<Rightarrow> Inl err'
        | Inr (i2, v2) \<Rightarrow> Inr (i2, (v1, v2))))"

definition
  either :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme" (infixl "<|>" 57)
where
  "either p1 p2 i =
    (case p1 i of
      Inr output \<Rightarrow> Inr output
    | Inl _ \<Rightarrow> p2 i)"

subsection \<open>Additional combinators\<close>

abbreviation
  empty :: "('i, 'o) parser_scheme" where
  "empty \<equiv> fail ''''"

definition
  amap :: "('i, ('a \<Rightarrow> 'b)) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme" (infixl "<*>" 58)
where
  "amap pf px = ((\<lambda>(f, x). f x) <$> (product pf px))"

definition
  right :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme" (infixl "*>" 58)
where
  "right p q = ((\<lambda>x.\<lambda>y. y) <$> p <*> q)"

definition
  left :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme" (infixl "<*" 58)
where
  "left p q = ((\<lambda>x.\<lambda>y. x) <$> p <*> q)"

definition
  entry :: "'i \<Rightarrow> ('i, 'i::show) parser_scheme" where
  "entry s = (satisfy (\<lambda>x. x = s) <|> (expected (''entry `'' @ show s @ ''`'')))"

definition
  optional :: "('i, 'o) parser_scheme \<Rightarrow> ('i, 'o option) parser_scheme" where
  "optional p = (Some <$> p <|> pure None)"

function (sequential)
  many_aux :: "('i, 'a) greedy_parser_scheme \<Rightarrow> 'a list \<Rightarrow> ('i, 'a list) parser_scheme" where
  "many_aux p acc i =
  (case rep_greedy p i of
    Inl _ \<Rightarrow> Inr (i, acc)
  | Inr (i', a) \<Rightarrow>
    (case many_aux p (a # acc) i' of
      Inl _ \<Rightarrow> undefined
    | Inr (i'', a') \<Rightarrow> Inr (i'', a')))"
by pat_completeness auto

termination many_aux
proof
  show "wf (measure (\<lambda>(p, a, i). length i))" by simp
next
  fix p acc i x2 x y
  assume "rep_greedy p i = Inr x2"
    and "(x, y) = x2"
  hence "length x < length i" using rep_greedy by fastforce
  thus "((p, y # acc, x), p, acc, i) \<in> measure (\<lambda>(p, a, y). length y)" by auto
qed

definition
  many :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'a list) parser_scheme" where
  "many p = (rev <$> many_aux p [])"

definition
  many1 :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'a list) parser_scheme" where
  "many1 p = ((#) <$> (rep_greedy p) <*> many p)"

subsection \<open>Main properties\<close>

lemma map_id [simp, code_unfold]:
  "(id <$> p) = p" unfolding map_def
  by (auto split: sum.split)

lemma pure_f_amap [simp, code_unfold]:
  "(pure f <*> p) = (f <$> p)"
  unfolding amap_def map_def pure_def product_def
  by (auto split: sum.split)

lemma applicative_identity [simp, code_unfold]:
  "(pure id <*> p) = p"
  by simp

lemma applicative_homomorphism [simp, code_unfold]:
  "(pure f <*> pure x) = pure (f x)"
  unfolding map_def pure_def amap_def product_def
  by (auto split: sum.split)

lemma applicative_interchange:
  "(u <*> pure x) = (pure (\<lambda>f. f x) <*> u)"
  unfolding product_def pure_def amap_def map_def
  by (auto split: sum.split)

lemma applicative_composition [simp]:
  "(((pure (\<circ>) <*> u) <*> v) <*> w) = (u <*> (v <*> w))"
  unfolding pure_def map_def amap_def product_def
  by (auto split: sum.split)

lemma alternative_identity_left [simp, code_unfold]:
  "(empty <|> u) = u"
  unfolding empty_def fail_def either_def
  by simp

(* NOTE: Broken due to migration to sum type *)
(* lemma alternative_identity_right [simp, code_unfold]:
 *   "(p <|> empty) = p"
 *   unfolding either_def empty_def fail_def
 *   by (auto split: sum.split) *)

lemma alternative_associativity:
  "(u <|> (v <|> w)) = ((u <|> v) <|> w)"
  unfolding either_def
  by (auto split: sum.split)

subsubsection \<open>Consumption analysis\<close>

text \<open>We've defined two type of predicates that check if parser not producs new input both strict and non-strict.\<close>

lemma fail_is_parser [intro]:
  "is_parser (fail s)"
  by (simp add: is_parser_def fail_def)

lemma pure_is_parser [intro]:
  "is_parser (pure x)"
  by (simp add: is_parser_def pure_def)

lemma satisfy_is_greedy_parser [intro]:
  "greedy_parser (satisfy P)"
  by (simp add: greedy_parser_def list.case_eq_if satisfy_def expected_def)

lemma bind_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "\<And>x. greedy_parser (f x)" shows "greedy_parser (bind p f)"
  unfolding greedy_parser_def
  by (smt (verit) Inl_Inr_False ParserCombinators.bind_def assms greedy_parserE order_less_trans prod.split_sel split_beta sum.case_eq_if sum.collapse(2) sum.disc(2))

lemma map_is_greedy_parser [intro]:
  assumes "greedy_parser p" shows "greedy_parser (map f p)"
  using assms unfolding is_parser_def greedy_parser_def map_def
  by (smt (verit, best) Inl_Inr_False Inr_inject fstI old.prod.exhaust old.sum.exhaust split_beta sum.case(1) sum.case(2))

lemma product_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "greedy_parser q" shows "greedy_parser (product p q)"
  unfolding product_def greedy_parser_def
  by (smt (verit, best) Inl_Inr_False assms dual_order.strict_trans2 fstI greedy_parserE less_imp_le_nat prod.collapse split_beta sum.case_eq_if sum.collapse(2) sum.sel(2))

lemma either_greedy_parsers:
  assumes "greedy_parser (either p q)" shows "greedy_parser p \<or> greedy_parser q"
  unfolding either_def greedy_parser_def
  by (metis assms either_def greedy_parser_def sum.case(2))

lemma either_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "greedy_parser q" shows "greedy_parser (either p q)"
  unfolding either_def
  by (metis (mono_tags, lifting) assms greedy_parser_def sum.case_eq_if sum.collapse(2))

lemma either_parsers:
  assumes "is_parser (either p q)" shows "is_parser p \<or> is_parser q"
  unfolding is_parser_def either_def
  by (metis assms either_def is_parser_def sum.case(2))

lemma either_is_parser [intro]:
  assumes "is_parser p" and "is_parser q" shows "is_parser (either p q)"
  unfolding either_def
  by (smt (verit) assms is_parser_def sum.case_eq_if sum.disc(2) sum.expand sum.sel(2))

lemma greedy_parser_either_fail [simp]:
  "greedy_parser (p <|> fail s) = greedy_parser p"
  by (metis (mono_tags, lifting) Inl_Inr_False either_def either_is_greedy_parser fail_def greedy_parser_def old.sum.simps(6))

lemma greedy_parser_either_expected [simp]:
  "greedy_parser (p <|> expected s) = greedy_parser p"
  unfolding expected_def
  by (smt (verit, best) Inl_Inr_False either_def either_is_greedy_parser greedy_parser_def sum.case(2))

lemma amap_is_greedy_parser [intro]:
  assumes "greedy_parser pf" and "greedy_parser px" shows "greedy_parser (amap pf px)"
  by (simp add: amap_def assms(1) assms(2) map_is_greedy_parser product_is_greedy_parser)

lemma right_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "greedy_parser q" shows "greedy_parser (right p q)"
  by (simp add: amap_is_greedy_parser assms map_is_greedy_parser right_def)

lemma left_is_greedy_parser [intro]:
  assumes "greedy_parser p" and "greedy_parser q" shows "greedy_parser (left p q)"
  by (simp add: amap_is_greedy_parser assms map_is_greedy_parser left_def)

lemma entry_is_greedy_parser[intro]:
  "greedy_parser (entry c)"
  unfolding entry_def
  by (simp add: satisfy_is_greedy_parser)

lemma optional_is_parser[intro]:
  assumes "is_parser p" shows "is_parser (optional p)"
  unfolding optional_def
  by (smt (z3) ParserCombinators.map_def assms case_prod_unfold either_def eq_fst_iff is_parserE is_parserI old.sum.simps(5) pure_is_parser sum.case_eq_if sum.collapse(2) sum.sel(2))

subsection \<open>Greedy lifted definitions\<close>

text \<open>In order to construct parsers that repeat many times we introduce convention for lifted defintions of greedy parsers - postfix `G`.\<close>

lift_definition satisfyG :: "('i \<Rightarrow> bool) \<Rightarrow> ('i::show, 'i) greedy_parser_scheme"
  is satisfy by blast

lift_definition bindG :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('a \<Rightarrow> ('i, 'b) greedy_parser_scheme) \<Rightarrow> ('i, 'b) greedy_parser_scheme"
  is bind by blast

adhoc_overloading
  Monad_Syntax.bind bindG

lift_definition mapG :: "('a \<Rightarrow> 'b) \<Rightarrow> ('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme" (infixl "<$>G" 58)
  is map by blast

lift_definition productG :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme \<Rightarrow> ('i, 'a \<times> 'b) greedy_parser_scheme"
  is product by blast

lift_definition eitherG :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'a) greedy_parser_scheme" (infixl "<|>G" 57)
  is either by blast

lift_definition amapG :: "('i, ('a \<Rightarrow> 'b)) greedy_parser_scheme \<Rightarrow> ('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme" (infixl "<*>G" 58)
  is amap by blast

lift_definition rightG :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme" (infixl "*>G" 58)
  is right by blast

lift_definition leftG :: "('i, 'a) greedy_parser_scheme \<Rightarrow> ('i, 'b) greedy_parser_scheme \<Rightarrow> ('i, 'a) greedy_parser_scheme" (infixl "<*G" 58)
  is left by blast

lift_definition entryG :: "'i \<Rightarrow> ('i, 'i::show) greedy_parser_scheme"
  is entry by blast

end
