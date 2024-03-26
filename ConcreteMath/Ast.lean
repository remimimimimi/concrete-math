namespace ConcreteMath.Ast



-- (* TODO: Make subsets of allowed string characters for LABEL and MATH_SYMBOL *)
-- type_synonym
--   label = String.literal
-- type_synonym
--   math_symbol = String.literal

-- type_synonym
--   const = math_symbol
-- type_synonym
--   var = math_symbol

-- type_synonym
--   typecode = const

-- datatype
--   declare_kind = Variables | Constants

-- datatype
--   axiom_kind = Essential | Normal

-- datatype
--   proof_kind = Normal | Compressed

-- datatype
--   statement =
--     Scope "statement list"
--   | Declare declare_kind "math_symbol list"
--   | TypeBinding label typecode var
--   (* Disjoint variables statement must have at least two elements *)
--   | DisjointVariables var var "var list"
--   | Axiom axiom_kind label typecode "math_symbol list"
--   | Theorem label typecode  "math_symbol list" "proof_kind"
