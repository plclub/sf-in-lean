import VersoManual
import SFLMeta.Comment

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace SFLMeta

/-!
`Block.grade` records a `-- GRADE_THEOREM <pts>: <name>` grading directive from
the code-forward source.  For now it is a pure noop — rendered empty, body
discarded at elaboration, exactly like `:::dev` (it shares `noopDirectiveFor`).
The grading spec survives verbatim in the generated `…Verso.lean` source, so the
grading infrastructure can later parse `:::grade` blocks (or this block can be
given real behaviour) to drive autograding scripts. -/
block_extension Block.grade where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX := none

@[directive]
def grade : DirectiveExpanderOf Unit
  | args, contents => noopDirectiveFor ``Block.grade args contents

/-! ## `:::gradeTheorem` directive

The structured successor to a `:::grade` block wrapping a `GRADE_THEOREM <pts>:
<name>` spec.  Rather than carry the spec as opaque body text, `:::gradeTheorem
<pts> "<name>"` records the point value and theorem name as directive arguments,
so a future autograding build can consume them directly.  Like `:::grade` it is
a noop for now: it renders nothing and emits nothing to the generated `.lean`
files, while the arguments survive in the Verso source. -/

/-- Author-facing configuration for `:::gradeTheorem`: a point value and the
name of the theorem to grade, both positional (`:::gradeTheorem 1 "double_add"`).
Points are kept as a *string* so fractional values (`0.5`, `0.25`) survive
exactly; write an integer bare (`1`) and a fraction quoted (`"0.5"`). -/
structure GradeTheoremConfig where
  /-- Points awarded for the theorem, as written (`"1"`, `"0.5"`). -/
  points : String
  /-- The name of the graded theorem. -/
  name : String
deriving Repr

section
variable [Monad m] [MonadError m]

/-- A point value written either bare as a natural-number literal (`1`) or, for
a fractional value, as a quoted string (`"0.5"`); yields the value's text. -/
def ValDesc.pointsText : ValDesc m String where
  description := doc!"a point value (a number, or a quoted decimal)"
  signature := CanMatch.Num ∪ CanMatch.String
  get
    | .num n => Pure.pure (toString n.getNat)
    | .str s => Pure.pure s.getString
    | other => throwError "Expected a point value, got {toMessageData other}"

/-- Argument parser for `GradeTheoremConfig`: `points` then `name`, positional. -/
def GradeTheoremConfig.parse : ArgParse m GradeTheoremConfig :=
  GradeTheoremConfig.mk
    <$> .positional `points ValDesc.pointsText <*> .positional `name .string

instance : FromArgs GradeTheoremConfig m := ⟨GradeTheoremConfig.parse⟩

end

/-! `Block.gradeTheorem` records a `GRADE_THEOREM <pts>: <name>` grading
directive as structured `(points, name)` data.  A noop like `Block.grade`:
rendered empty and dropped at elaboration; the spec survives verbatim in the
`…Verso.lean` source for later autograding. -/
block_extension Block.gradeTheorem (points : String) (name : String) where
  data := Json.arr #[.str points, .str name]
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX := none

@[directive]
def gradeTheorem : DirectiveExpanderOf GradeTheoremConfig
  | cfg, _contents => do
    ``(Verso.Doc.Block.other
        (SFLMeta.Block.gradeTheorem $(quote cfg.points) $(quote cfg.name)) #[])

end SFLMeta
