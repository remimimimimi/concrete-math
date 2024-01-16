section "Concrete Math"

theory ConcreteMath
  imports
    Main
    (* HOL.Map *)
    (* "HOL-Library.Mapping" *)
    (* "HOL-Library.Finite_Map" *)
    "HOL-Library.Monad_Syntax"
    ParserCombinators
begin

text
  "Every following subsection will describe certain types that necessary to
  represent Metamath proof database, and helpful function to work with them,
  alongside with, no less useful, lemmas about them."

(* subsection "Utils"
 *
 * definition guard :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b option" where
 *   "guard p v f = (if p v then Some (f v) else None)" *)

subsection
  "Essential Metamath syntax"

(* TODO: Make subsets of allowed string characters for LABEL and MATH_SYMBOL *)
type_synonym
  label = String.literal
type_synonym
  math_symbol = String.literal

type_synonym
  const = math_symbol
type_synonym
  var = math_symbol

type_synonym
  typecode = const

datatype
  declare_kind = Variables | Constants

datatype
  axiom_kind = Essential | Normal

datatype
  proof_kind = Normal | Compressed

datatype
  statement =
    Scope "statement list"
  | Declare declare_kind "math_symbol list"
  | TypeBinding label typecode var
  (* Disjoint variables statement must have at least two elements *)
  | DisjointVariables var var "var list"
  | Axiom axiom_kind label typecode "math_symbol list"
  | Theorem label typecode  "math_symbol list" "proof_kind"

subsection
  "Grammar"

text \<open> In order to follow metamath grammar rules \cite[Appendix E]{metamath} as
  close as possilbe, we will break Isabelle naming convention. But their order
  will be reversed. \<close>

subsubsection "Tokens"

type_synonym 'a parser  = "(char, 'a) parser_scheme"

definition
  WHITECHAR :: "char parser" where
  "WHITECHAR = satisfy (\<lambda>c. c \<in> {CHR 0x20, CHR 0x09, CHR 0x0d, CHR 0x0a, CHR 0x0c})"

definition
  "PRINTABLE_CHARACTER = satisfy (\<lambda> c. let n = of_char c :: nat in 0x21 \<le> n \<and> n \<le> 0x7e)"



(* definition
 *   COMMENT :: "unit parser" where
 *   "COMMENT = do {
 *   exactly ''$('';
 *   (do {
 *   manyof1 WHITECHAR;
 *
 *   return ()
 *   });
 *   manyof1 WHITECHAR;
 *   exactly ''$)'';
 *   manyof WHITECHAR;
 *   return ()
 *   }" *)

(* definition
 *   WHITESPACE :: "unit parser" where
 *   "WHITESPACE = undefined" *)

subsubsection "Parser"

subsection "Database"

(* TODO: Rephrase and move to appropriate place *)
text \<open>

  Metamath specification defines context through the stack of frames, which is
  conscious choice due to the mutable nature of most of the commonly used
  languages. We have no such necessity as in Isabelle everything is immutable,
  thus every update of a record will result another record, ergo this is stack
  in some sense.

\<close>
record database =
  constants :: "const set"
  (* Frame start *)
  vars :: "var set"

  disj :: "(var set) set" (* NOTE: Maybe just "var set"? *)

  fhyp :: "(var \<times> const) list"  (* Maps  *)
  flab :: "var \<rightharpoonup> label"

  ehyp :: "(math_symbol list) list"
  elab :: "math_symbol list \<rightharpoonup> label"
  (* Frame end *)
  labels :: "label list"

definition
  empty_db :: database where
  "empty_db = \<lparr>
    constants = {},
    vars = {},
    disj = {},
    fhyp = [],
    flab = Map.empty,
    ehyp = [],
    elab = Map.empty,
    labels = []
  \<rparr>"

definition
  declared_constant :: "database \<Rightarrow> const \<Rightarrow> bool" where
  "declared_constant db c = (c \<in> constants db)"

definition
  declared_var :: "database \<Rightarrow> var \<Rightarrow> bool" where
  "declared_var db v = (v \<in> vars db)"

definition
  disjoint_vars :: "database \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool" where
  "disjoint_vars db v1 v2 = (\<exists>d \<in> disj db. v1 \<in> d \<and> v2 \<in> d)"

(* Lookup active floating hypothesis *)
definition
  lookup_afh :: "database \<Rightarrow> var \<Rightarrow> label option" where
  "lookup_afh db v = flab db v"

(* Lookup earliest essential hypothesis *)
definition
  lookup_eeh :: "database \<Rightarrow> math_symbol list \<Rightarrow> label option" where
  "lookup_eeh db stmt = elab db stmt"

definition
  add_constant :: "database \<Rightarrow> const \<Rightarrow> database option" where
  "add_constant db c =
    (if declared_constant db c \<or> declared_var db c
         then None
         else Some (db \<lparr>constants := constants db \<union> {c} \<rparr>))"

definition
  add_var :: "database \<Rightarrow> var \<Rightarrow> database option" where
  "add_var db v =
    (if declared_constant db v \<or> declared_var db v
         then None
         else Some (db \<lparr>vars := vars db \<union> {v} \<rparr>))"

definition
  add_disjoint_vars :: "database \<Rightarrow> var set \<Rightarrow> database" where
  "add_disjoint_vars db vs = db \<lparr>
    disj := disj db \<union> {vs}
  \<rparr>"

definition
  add_floating_hypothesis :: "database \<Rightarrow> const \<Rightarrow> var \<Rightarrow> label \<Rightarrow> database option" where
  "add_floating_hypothesis db c v l =
    (if declared_var db v \<and> declared_constant db c \<and> Option.is_none (flab db v)
         then Some (db \<lparr>fhyp := (v, c) # fhyp db, flab := (flab db)(v \<mapsto> l)\<rparr>)
         else None)"

definition
  add_essential_hypothesis :: "database \<Rightarrow> math_symbol list \<Rightarrow> label \<Rightarrow> database" where
  "add_essential_hypothesis db stmt l = db \<lparr>
    ehyp := (stmt # ehyp db),
    elab := (elab db)(stmt \<mapsto> l)
  \<rparr>"



(* Functions below more related to verification process*)
definition
  find_vars :: "database \<Rightarrow> math_symbol list \<Rightarrow> var set" where
  "find_vars db stmt = set [v \<leftarrow> stmt . declared_var db v]"

text \<open>

Assertion is a quadruple (disjoint variable conditions, floating hypotheses,
essential hypotheses, conclusion) describing the given assertion.

\<close>
type_synonym assertion = "var set \<times> (var \<times> const) list \<times> (math_symbol list) list \<times> math_symbol list"

definition
  make_assertion :: "database \<Rightarrow> math_symbol list \<Rightarrow> assertion" where
  "make_assertion db stmt = (
    let
      vars = List.fold (@) (ehyp db) stmt;
      mandatory_vars = find_vars db vars;

      dvs = {v. v \<in> \<Union> (disj db) \<and> v \<in> mandatory_vars};
      fhyps = [(v, t) \<leftarrow> (fhyp db). v \<in> mandatory_vars];
      ehyps = ehyp db
    in (dvs, fhyps, ehyps, stmt)
  )"

primrec
  substitute :: "math_symbol list \<Rightarrow> (var \<rightharpoonup> (math_symbol list)) \<Rightarrow> math_symbol list" where
  "substitute [] subst = []" |
  "substitute (s # stmt) subst =
  (case (subst s) of
    None \<Rightarrow> [s] |
    Some sstmt \<Rightarrow> sstmt) @ substitute stmt subst"

subsection "Verifier"



end
