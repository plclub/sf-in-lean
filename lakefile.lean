import Lake
open Lake DSL

package sf where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Basics where
  srcDir := "lf"

lean_lib Induction where
  srcDir := "lf"

lean_lib Lists where
  srcDir := "lf"
