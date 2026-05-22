import Lake
open Lake DSL

package dSeparation where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib DSeparation
