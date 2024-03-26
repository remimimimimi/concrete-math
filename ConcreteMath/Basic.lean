import Std.Data.HashMap
import Std.Data.List
import Init.Data.Array.QSort
namespace ConcreteMath.Ast
-- import Init.Data.Repr

namespace ConcreteMath.Basic

open Lean

-- #check IO.FS.readBinFile

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

inductive Sym
  | const (c : String)
  | var (v : String)

abbrev Formula := List Sym

def Formula.subst (σ : HashMap String Formula) (f : Formula) : Except String Formula := do
  let mut f' := []
  for c in f do
    match c with
    | Sym.const _ => f' := c :: f'
    | Sym.var v =>
      match σ.find? v with
      | none => throw s!"variable {v} not found"
      | some e => f' := e ++ f'
  pure f'

inductive Object where



inductive Frame where


structure Database where
  frame : Frame
  -- scopes : Array (Nat × Nat)
  objects : HashMap String Object
