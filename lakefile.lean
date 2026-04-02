import Lake
open Lake DSL

package sf where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩
  ]

@[default_target]
lean_lib LF where
  globs := #[`lf.+]
