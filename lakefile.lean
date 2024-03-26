import Lake
open Lake DSL

package «ConcreteMath» where
  -- add package configuration options here

require std from git "https://github.com/leanprover/std4" @ "main"

lean_lib «ConcreteMath» where
  -- add library configuration options here

@[default_target]
lean_exe «concretemath» where
  root := `Main
