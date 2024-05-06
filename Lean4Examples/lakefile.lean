import Lake
open Lake DSL

package «Lean4Examples» where
  -- add package configuration options here

lean_lib «Lean4Examples» where
  -- add library configuration options here

@[default_target]
lean_exe «lean4examples» where
  root := `Main
