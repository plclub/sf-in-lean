import Lake
open Lake DSL

package SFL where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩
  ]

@[default_target]
lean_lib LF where
  roots := #[`LF]
  globs := #[`LF.+]
