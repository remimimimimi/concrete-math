section "Concrete Math"

theory ConcreteMath
  imports
    Main
    (* HOL.Map *)
    (* "HOL-Library.Mapping" *)
    (* "HOL-Library.Finite_Map" *)
    "Certification_Monads.Parser_Monad"
begin

text
  "Every following subsection will describe certain types that necessary to
  represent Metamath proof database, and helpful function to work with them,
  alongside with, no less useful, lemmas about them."

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

subsection "Grammar"

text \<open> In order to follow metamath grammar rules \cite[Appendix E]{metamath} as
  close as possilbe, we will break Isabelle naming convention. But their order
  will be reversed. \<close>

subsubsection "Parsing utils"

definition
  char_in_range :: "nat \<Rightarrow> nat \<Rightarrow> char \<Rightarrow> bool" where
  "char_in_range s e c = (let n = of_char c :: nat in s \<le> n \<and> n \<le> e)"

fun
  definitely :: "string \<Rightarrow> unit parser" where
  "definitely [] i = Inr ((), i)" |
  "definitely s [] = Inl (''expecting \"'' @ s @ ''\", but found: EOI'')" |
  "definitely (s#ss) (i#is) =
  (if s = i
   then definitely ss is
   else err_expecting (s#ss) (i#is))"

subsubsection "Tokens"

definition
  "WHITECHAR_PREDICATE = (\<lambda>c. c \<in> {CHR 0x20, CHR 0x09, CHR 0x0d, CHR 0x0a, CHR 0x0c})"

definition
  WHITECHAR :: "char parser" where
  "WHITECHAR i =
  (case i of
    [] \<Rightarrow> Inl ''expecting WHITECHAR, but found: EOI''
  | (t#ts) \<Rightarrow> (if WHITECHAR_PREDICATE t then Inr (t, ts) else err_expecting [t] ts))"

definition
  WHITECHARS :: "string parser" where
  "WHITECHARS = many WHITECHAR_PREDICATE"

definition
  "PRINTABLE_CHARACTER_PREDICATE = char_in_range 0x21 0x7e"

definition
  PRINTABLE_CHARACTER :: "char parser" where
  "PRINTABLE_CHARACTER i =
  (case i of
    [] \<Rightarrow> Inl ''expecting PRINTABLE_CHARACTER, but found: EOI''
  | (t#ts) \<Rightarrow> (if PRINTABLE_CHARACTER_PREDICATE t then Inr (t, ts) else err_expecting ''PRINTABLE_CHARACTER'' (t#ts)))"

definition
  PRINTABLE_SEQUENCE :: "string parser" where
  "PRINTABLE_SEQUENCE = do {
    c \<leftarrow> PRINTABLE_CHARACTER;
    cs \<leftarrow> many PRINTABLE_CHARACTER_PREDICATE;
    return (c # cs)
  }"

text \<open>Following parser should be equivalent to the definition in grammar as don't want to use comment content.\<close>
definition
  COMMENT :: "unit parser" where
  "COMMENT = do {
    definitely ''$('';
    WHITECHAR;
    many (\<lambda>c. ((PRINTABLE_CHARACTER_PREDICATE c) \<or> (WHITECHAR_PREDICATE c)) \<and> (c \<noteq> CHR ''$''));
    definitely ''$)'';
    WHITECHAR;
    return ()
  }"

definition
  WHITESPACE :: "unit parser" where
  "WHITESPACE i =
  (case WHITECHARS i of
    Inr x \<Rightarrow> Error_Monad.return ((), [])
  | Inl err \<Rightarrow> COMMENT i)"

definition
  "COMPRESSED_PROOF_BLOCK_CHAR_PREDICATE c \<equiv> char_in_range (of_char CHR ''A'') (of_char CHR ''Z'') c \<or> c = CHR ''?''"

definition
  COMPRESSED_PROOF_BLOCK_CHAR :: "char parser" where
  "COMPRESSED_PROOF_BLOCK_CHAR i =
  (case i of
    [] \<Rightarrow> Inl ''Expected COMPRESSED_PROOF_BLOCK_CHAR''
  | (t#ts) \<Rightarrow> (if COMPRESSED_PROOF_BLOCK_CHAR_PREDICATE t then Inr (t, ts) else Inl ''Expected COMPRESSED_PROOF_BLOCK_CHAR''))"

definition
  COMPRESSED_PROOF_BLOCK :: "string parser" where
  "COMPRESSED_PROOF_BLOCK = do {
    c \<leftarrow> COMPRESSED_PROOF_BLOCK_CHAR;
    cs \<leftarrow> many COMPRESSED_PROOF_BLOCK_CHAR_PREDICATE;
    return (c#cs)
  } "

definition
  "LABEL_CHAR_PREDICATE c \<equiv> char_in_range (of_char CHR ''A'') (of_char CHR ''Z'') c
                            \<or> char_in_range (of_char CHR ''a'') (of_char CHR ''z'') c
                            \<or> char_in_range (of_char CHR ''0'') (of_char CHR ''9'') c
                            \<or> c \<in> {CHR ''.'', CHR ''-'', CHR ''_''}"

definition
  LABEL_CHAR :: "char parser" where
  "LABEL_CHAR i =
  (case i of
    [] \<Rightarrow> Inl ''Expected LABEL_CHAR''
  | (t#ts) \<Rightarrow> (if LABEL_CHAR_PREDICATE t then Inr (t, ts) else Inl ''Expected LABEL_CHAR''))"

definition
  LABEL :: "string parser" where
  "LABEL = do {
    c \<leftarrow> LABEL_CHAR;
    cs \<leftarrow> many LABEL_CHAR_PREDICATE;
    return (c#cs)
  }"

definition
  "MATH_SYMBOL_CHAR_PREDICATE c \<equiv> PRINTABLE_CHARACTER_PREDICATE c \<and> c \<noteq> CHR ''$''"

definition
  MATH_SYMBOL_CHAR :: "char parser" where
  "MATH_SYMBOL_CHAR i =
  (case i of
    [] \<Rightarrow> Inl ''Expected MATH_SYMBOL_CHAR''
  | (t#ts) \<Rightarrow> (if MATH_SYMBOL_CHAR_PREDICATE t then Inr (t, ts) else Inl ''Expected MATH_SYMBOL_CHAR''))"

definition
  MATH_SYMBOL :: "string parser" where
  "MATH_SYMBOL = do {
    c \<leftarrow> MATH_SYMBOL_CHAR;
    cs \<leftarrow> many MATH_SYMBOL_CHAR_PREDICATE;
    return (c#cs)
  }"

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
