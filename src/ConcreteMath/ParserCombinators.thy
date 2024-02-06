section \<open>Parser Combinators\<close>
theory ParserCombinators
  imports
    Main
    "HOL-Library.Monad_Syntax"
begin

type_synonym ('i, 'o) parser_scheme = "'i list \<Rightarrow> ('i list * 'o) option"

definition not_produces_input :: "('i, 'o) parser_scheme \<Rightarrow> bool" where
  "not_produces_input p = (\<forall>i r v. p i = (Some (r, v)) \<longrightarrow> length r \<le> length i)"

lemma not_produces_input_introduction [intro]:
  assumes "\<And>i r v. p i = (Some (r, v)) \<Longrightarrow> length r \<le> length i"
  shows "not_produces_input p"
  using assms not_produces_input_def by blast

lemma not_produces_input_elimination [elim]:
  assumes "not_produces_input p"
    and "(\<And>i r v. p i = (Some (r, v)) \<Longrightarrow> length r \<le> length i) \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: not_produces_input_def)

definition consumes :: "('i, 'o) parser_scheme \<Rightarrow> bool" where
  "consumes p = (\<forall>i r v. p i = (Some (r, v)) \<longrightarrow> length r < length i)"

lemma consumes_introduction [intro]:
  assumes "\<And>i r v. p i = (Some (r, v)) \<Longrightarrow> length r < length i"
  shows "consumes p"
  using assms consumes_def by blast

lemma consumes_elimination [elim]:
  assumes "consumes p"
    and "(\<And>i r v. p i = (Some (r, v)) \<Longrightarrow> length r < length i) \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: consumes_def)

lemma consumes_implies_not_produces_input:
  "consumes p \<Longrightarrow> not_produces_input p"
  unfolding not_produces_input_def consumes_def
  by (simp add: nat_less_le)

subsection \<open>Primitive Combinators\<close>

definition
  fail :: "('i, 'o) parser_scheme" where
  "fail i = None"

definition
  pure :: "'o \<Rightarrow> ('i, 'o) parser_scheme" where
  "pure output i = Some (i, output)"

text \<open>Returns input value if it equal to expected\<close>

(* TODO: Add show*)
definition
  satisfy :: "('i \<Rightarrow> bool) \<Rightarrow> ('i, 'i) parser_scheme" where
  "satisfy P xs =
    (case xs of
       []   \<Rightarrow> None
     | x#xs \<Rightarrow> if P x then Some (xs, x) else None)"

definition
  bind :: "('i, 'a) parser_scheme \<Rightarrow> ('a \<Rightarrow> ('i, 'b) parser_scheme) \<Rightarrow> ('i, 'b) parser_scheme" (infixl ">>=" 1) where
  "bind p k i =
    (case p i of
       None \<Rightarrow> None
     | Some (rest, output) \<Rightarrow> k output rest)"

adhoc_overloading
  Monad_Syntax.bind bind

definition
  map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme" (infixl "<$>" 4) where
  "map f p i =
    (case p i of
       None \<Rightarrow> None
     | Some (i', v) \<Rightarrow> Some (i', f v))"

definition
  product :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme \<Rightarrow> ('i, 'a \<times> 'b) parser_scheme" where
  "product p1 p2 i =
    (case p1 i of
       None \<Rightarrow> None
     | Some (i1, v1) \<Rightarrow>
       (case p2 i1 of
          None \<Rightarrow> None
        | Some (i2, v2) \<Rightarrow> Some (i2, (v1, v2))))"

definition
  either :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme" (infixl "<|>" 3)
where
  "either p1 p2 i =
    (case p1 i of
      Some output \<Rightarrow> Some output
    | None \<Rightarrow> p2 i)"

value "
  (do {
  x \<leftarrow> (pure 1 :: (char, nat) parser_scheme);
  y \<leftarrow> pure 3;
  pure (x + y)
}) ''hi''"

(* value "Rep_parser_scheme_consumes" *)

(* do {
 *     (i', v) \<leftarrow> Rep_parser_scheme_consumes p i;
 *     (i'', vs) \<leftarrow> many p i';
 *     Some (i'', v # vs)
 *   } *)

subsection \<open>Additional combinators\<close>

abbreviation
  empty :: "('i, 'o) parser_scheme" where
  "empty \<equiv> fail"

definition
  amap :: "('i, ('a \<Rightarrow> 'b)) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme" (infixl "<*>" 4)
where
  "amap pf px = ((\<lambda>(f, x). f x) <$> (product pf px))"

typedef ('i, 'o) parser_scheme_many = "{p::('i, 'o) parser_scheme. (consumes p)}"
morphisms rep_many abs_many
by auto

setup_lifting type_definition_parser_scheme_many

function (sequential)
  many_aux :: "('i, 'a) parser_scheme_many \<Rightarrow> 'a list \<Rightarrow> ('i, 'a list) parser_scheme" where
  "many_aux p acc i =
  (case rep_many p i of
    None \<Rightarrow> Some (i, acc)
  | Some (i', a) \<Rightarrow>
    (case many_aux p (a # acc) i' of
      None \<Rightarrow> undefined
    | Some (i'', a') \<Rightarrow> Some (i'', a')))"
by pat_completeness auto

termination many_aux
proof
  show "wf (measure (\<lambda>(p, a, i). length i))" by simp
next
  fix p acc i x2 x y
  assume "rep_many p i = Some x2"
    and "(x, y) = x2"
  hence "length x < length i" using rep_many by fastforce
  thus "((p, y # acc, x), p, acc, i)
    \<in> measure (\<lambda>(p, a, y). length y)" by auto
qed

definition
  many :: "('i, 'a) parser_scheme_many \<Rightarrow> ('i, 'a list) parser_scheme" where
  "many p = (rev <$> many_aux p [])"

definition
  right :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme" (infixl "*>" 4)
where
  "right p q = ((\<lambda>x.\<lambda>y. y) <$> p <*> q)"

definition
  left :: "('i, 'a) parser_scheme \<Rightarrow> ('i, 'b) parser_scheme \<Rightarrow> ('i, 'a) parser_scheme" (infixl "<*" 4)
where
  "left p q = ((\<lambda>x.\<lambda>y. x) <$> p <*> q)"

definition
  symbol :: "'i \<Rightarrow> ('i, 'i) parser_scheme" where
  "symbol s = satisfy (\<lambda>x. x = s)"

definition
  optional :: "('i, 'o) parser_scheme \<Rightarrow> ('i, 'o option) parser_scheme" where
  "optional p = (Some <$> p <|> pure None)"

(* definition
 *   many1 :: "('i, 'o) parser_scheme \<Rightarrow> ('i, 'o list) parser_scheme" where
 *   "many1 p = ((#) <$> p <*> many p)" *)

subsection \<open>Main properties\<close>

lemma map_id [simp, code_unfold]:
  "(id <$> p) = p" unfolding map_def
  by (auto split: option.split)

lemma pure_f_amap [simp, code_unfold]:
  "(pure f <*> p) = (f <$> p)"
  unfolding amap_def map_def pure_def product_def
  by (auto split: option.split)

lemma applicative_identity [simp, code_unfold]:
  "(pure id <*> p) = p"
  by simp

lemma applicative_homomorphism [simp, code_unfold]:
  "(pure f <*> pure x) = pure (f x)"
  unfolding map_def pure_def amap_def product_def
  by (auto split: option.split)

lemma applicative_interchange:
  "(u <*> pure x) = (pure (\<lambda>f. f x) <*> u)"
  unfolding product_def pure_def amap_def map_def
  by (auto split: option.split)

lemma applicative_composition [simp]:
  "(((pure (\<circ>) <*> u) <*> v) <*> w) = (u <*> (v <*> w))"
  unfolding pure_def map_def amap_def product_def
  by (auto split: option.split)

lemma alternative_identity_left [simp, code_unfold]:
  "(empty <|> u) = u"
  unfolding empty_def fail_def either_def
  by simp

lemma alternative_identity_right [simp, code_unfold]:
  "(p <|> empty) = p" unfolding either_def fail_def
  by (auto split: option.split)

lemma alternative_associativity:
  "(u <|> (v <|> w)) = ((u <|> v) <|> w)"
  unfolding either_def
  by (auto split: option.split)

subsubsection \<open>Consumption analysis\<close>

text \<open>We define two type of predicates that check if parser not producs new input both strict and non-strict.\<close>

lemma fail_not_produce_input [intro]:
  "not_produces_input fail"
  by (simp add: not_produces_input_def fail_def)

lemma pure_not_produces_input [intro]:
  "not_produces_input (pure x)"
  by (simp add: not_produces_input_def pure_def)

lemma satisfy_consumes [intro]:
  "consumes (satisfy P)"
  by (simp add: consumes_def list.case_eq_if satisfy_def)

lemma map_not_produces_input [intro]:
  assumes "consumes p \<or> not_produces_input p" shows "not_produces_input (map f p)"
  using assms unfolding not_produces_input_def consumes_def map_def
  by (smt (verit, del_insts) fstI less_imp_le_nat option.case_eq_if option.distinct(1) option.exhaust_sel option.sel prod.collapse split_beta)

lemma product_not_produces_input [intro]:
  assumes "consumes p \<or> not_produces_input p" and "consumes q \<or> not_produces_input q" shows "not_produces_input (product p q)"
proof
  fix i r v
  assume "product p q i = Some (r, v)"
  then obtain i' x y
    where P: "p i = Some (i', x )" and Q: "q i' = Some (r, y)"
    unfolding product_def
    by (smt (verit) Pair_inject option.case_eq_if option.distinct(1) option.exhaust_sel option.sel prod.collapse split_beta)
  show "product p q i = Some (r, v) \<Longrightarrow> length r \<le> length i"
    by (meson P Q assms consumes_implies_not_produces_input not_produces_input_elimination order_trans)
qed

lemma either_consumption:
  "consumes (either p q) \<Longrightarrow> consumes p \<or> consumes q"
  by (simp add: consumes_def either_def)

lemma either_not_procuces_input:
  "not_produces_input (either p q) \<Longrightarrow> not_produces_input p \<or> not_produces_input q"
  by (simp add: not_produces_input_def either_def)

lemma symbol_consumption[intro]:
  "consumes (symbol c)" by (simp add: satisfy_consumes symbol_def)

(* find_theorems "abs_many"
 *
 * lemma "(satisfy P) \<in> {p. consumes p}"
 * by blast
 *
 * lift_definition Satisfy :: "('i \<Rightarrow> bool) \<Rightarrow> ('i, 'i) parser_scheme_many" is satisfy
 * by auto
 *
 * value "(Satisfy (\<lambda>c. c = CHR ''x'')) :: (char, char) parser_scheme_many"
 *
 *
 * definition
 *   "exes = many (Satisfy (\<lambda>c. c = CHR ''x''))"
 *
 * value "many (Satisfy (\<lambda>c. c = CHR ''x'')) ''xxxxxkj''"
 *
 * export_code exes in Haskell *)

end
