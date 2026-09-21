import VersoManual
import SFLMeta.Comment

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace SFLMeta

variable [Monad m] [MonadError m] [MonadLiftT TermElabM m]

block_extension Block.grade where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX := none

@[directive]
def grade : DirectiveExpanderOf Unit
  | args, contents => noopDirectiveFor ``Block.grade args contents

structure GradeTheoremConfig where
  /-- Points awarded for the theorem, as written (`1`, `"0.5"`). -/
  points : String
  /-- The names of the graded theorems. Each is graded as specified by `points`. -/
  names : List Name
  deriving Repr, TypeName

def ValDesc.pointsText : ValDesc m String where
  description := doc!"a point value (a number, or a quoted decimal)"
  signature := CanMatch.Num ∪ CanMatch.String
  get
    | .num n => Pure.pure (toString n.getNat)
    | .str s => Pure.pure s.getString
    | other => throwError "Expected a point value, got {toMessageData other}"

/-- Resolve a name using `InlineLean`'s scope (stored in an environment extension). -/
defmethod ValDesc.inlineLeanResolvedName : ValDesc m Name where
  description := doc!"a name resolved in the current inline Lean scope"
  signature := .Ident
  get
    | .name x => InlineLean.Scopes.runWithOpenDecls <| realizeGlobalConstNoOverloadWithInfo x
    | other => throwError "Expected identifier, got {other}"

/-- Argument parser for `GradeTheoremConfig` -/
def GradeTheoremConfig.parse : ArgParse m GradeTheoremConfig :=
  GradeTheoremConfig.mk
    <$> .positional `points ValDesc.pointsText <*> many1 (.positional `name .inlineLeanResolvedName)
where
  many1 p := (· :: ·) <$> p <*> .many p

instance : FromArgs GradeTheoremConfig m := ⟨GradeTheoremConfig.parse⟩

block_extension Block.gradeTheorem (points : String) (names : List Name) where
  data := Json.arr #[.str points, .arr <| (names.map (Json.str ∘ Name.toString)).toArray]
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX := none

@[directive]
def gradeTheorem : DirectiveExpanderOf GradeTheoremConfig
  | cfg, _contents => do
    pushInfoLeaf <| .ofCustomInfo {stx := ← getRef, value := .mk cfg}
    ``(Verso.Doc.Block.other
        (SFLMeta.Block.gradeTheorem $(quote cfg.points) $(quote cfg.names)) #[])

def decodeGradeTheoremData (data : Json) : String × Array Name :=
  match data with
  | .arr #[Json.str points, Json.arr names] => (
      points,
      names.map fun
        | .str s => s.toName
        | _ => unreachable!
    )
  | _ => unreachable!

block_extension Block.autogradedHole (names : List Name) where
  data := Json.arr #[.arr <| (names.map (Json.str ∘ Name.toString)).toArray]
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX := none

structure AutogradedHoleConfig where
  /-- The names of definitions to treat as holes. -/
  names : List Name
  deriving Repr, TypeName

def AutogradedHoleConfig.parse : ArgParse m AutogradedHoleConfig :=
  AutogradedHoleConfig.mk
    <$> many1 (.positional `name .inlineLeanResolvedName)
where
  many1 p := (· :: ·) <$> p <*> .many p

instance : FromArgs AutogradedHoleConfig m := ⟨AutogradedHoleConfig.parse⟩

@[directive]
def autogradedHole : DirectiveExpanderOf AutogradedHoleConfig
  | cfg, _contents => do
    pushInfoLeaf <| .ofCustomInfo {stx := ← getRef, value := .mk cfg}
    ``(Verso.Doc.Block.other (SFLMeta.Block.autogradedHole $(quote cfg.names)) #[])

def decodeAutogradedHoleData (data : Json) : Array Name :=
  match data with
  | .arr #[Json.arr names] =>
    names.map fun
      | .str s => s.toName
      | _ => unreachable!
  | _ => unreachable!

end SFLMeta
