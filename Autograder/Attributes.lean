module

public import Lean

public section

open Lean

/-- The points parameter to `@[graded]` is a rational number -/
abbrev PointAmount := Rat

inductive Graded
  /-- This marks an assignment with points -/
  | assignment (points : PointAmount)
  /-- This marks an ignored definition -/
  | ignore
  deriving Repr, Inhabited

declare_syntax_cat graded_opts

/-- The precise value of this definition is ignored by checks of subsequent graded items.
In other words, this can be set to anything, as long as its type is exactly as in the original assignment. -/
syntax "ignore" : graded_opts
/-- The number of points awarded for a correct proof. -/
syntax scientific : graded_opts

/-- Configuration related to automatic grading. Modifications to these attributes are ignored and the original assignment is used as the source of truth. -/
syntax (name := graded) "graded" (ppSpace graded_opts) : attr

initialize gradedAttr : ParametricAttribute Graded ←
  registerParametricAttribute {
    name := `graded
    descr := "This declaration is graded and awards the specified number of points"
    getParam := fun _ => fun
      | `(attr| graded $points:scientific) =>
        let sci := points.getScientific
        pure <| Graded.assignment <| Rat.ofScientific sci.1 sci.2.1 sci.2.2
      | `(attr| graded ignore) => pure Graded.ignore
      | _ => Elab.throwUnsupportedSyntax
  }
