import Lake
open Lake DSL

package sf where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩
  ]

@[default_target]
lean_lib Basics where
  srcDir := "lf"

lean_lib Induction where
  srcDir := "lf"

lean_lib UsingLean where
  srcDir := "lf"

lean_lib Lists where
  srcDir := "lf"

lean_lib Poly where
  srcDir := "lf"

lean_lib Tactics where
  srcDir := "lf"

lean_lib Logic where
  srcDir := "lf"

lean_lib IndProp where
  srcDir := "lf"

lean_lib IndPropRegexp where
  srcDir := "lf"

lean_lib Auto where
  srcDir := "lf"

lean_lib Maps where
  srcDir := "lf"

lean_lib ProofObjects where
  srcDir := "lf"

lean_lib IndPrinciples where
  srcDir := "lf"

lean_lib Rel where
  srcDir := "lf"

lean_lib Imp where
  srcDir := "lf"

lean_lib ImpParser where
  srcDir := "lf"

lean_lib ImpCEvalFun where
  srcDir := "lf"

lean_lib Compilation where
  srcDir := "lf"
