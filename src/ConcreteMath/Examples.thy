section \<open>Examples\<close>
theory Examples
  imports ParserCombinators
    "Show.Show_Instances"
    HOL.Real
begin

type_synonym 'a parser = "(char, 'a) parser_scheme"
type_synonym 'a greedy_parser = "(char, 'a) greedy_parser_scheme"

subsection \<open>S-expression\<close>

subsubsection \<open>Types\<close>
datatype builtin =
  Plus |
  Minus |
  Times

datatype atom = Num int

datatype sexpr =
  Atom atom |
  Application builtin "sexpr list"

derive "show" builtin atom sexpr

subsubsection \<open>Parser\<close>
definition
  builtin_parser :: "builtin parser" where
  "builtin_parser = ((\<lambda>_. Plus)  <$> entry CHR ''+'' <|>
                     (\<lambda>_. Minus) <$> entry CHR ''-'' <|>
                     (\<lambda>_. Times) <$> entry CHR ''*'')"

definition
  sign_parser :: "int parser" where
  "sign_parser = ((\<lambda>_. -1) <$> entry CHR ''-'' <|> pure 1)"

definition
  int_parser :: "int greedy_parser" where
  "int_parser = ((*) <$> sign_parser <*>\<g>\<r> (int <$>\<g> decimal))"

lift_definition
  int_parser\<p> :: "int parser"
  is "run_greedy int_parser"
  using greedy_parser_implies_is_parser run_greedy by auto

definition
  atom_parser :: "atom greedy_parser" where
  "atom_parser = (Num <$>\<g> int_parser)"

(* (\* definition
 *  *   sexpr_prefix :: "unit greedy_parser" where
 *  *   "sexpr_prefix " *\)
 *   ascii_spaces;
 *   entry CHR ''('';
 *   ascii_spaces; *)

(* definition
 *   sexpr_postfix
 *   entry CHR '')'';
 *   ascii_spaces; *)

(* FIXME: Resolve paradox with recursive parsers. Probably requires rewriting
   using only parser_function type and then proving that it's a parser. *)
function
  sexpr_parser :: "char list \<Rightarrow> sexpr greedy_parser" where
  "sexpr_parser i = undefined"

subsubsection \<open>Evaluator\<close>
  (* TODO *)
