import VersoManual
import Batteries.Lean.Position

import SFLMeta.Exercise
import SFLMeta.Grade
import SFLMeta.Terse

open Lean Elab Command Linter
open Verso Doc Elab
open Lean.Doc.Syntax

/-- Checks that exercises specify their visibility through `:::full` or `:::terse`. -/
register_option linter.sf.exerciseVisibility : Bool := {
  defValue := true
  descr := "if true, check that exercises are inside full or terse directives"
}

/-- Checks that `:::full` and `:::terse` do not nest. -/
register_option linter.sf.variantNesting : Bool := {
  defValue := true
  descr := "if true, check that full and terse directives do not nest"
}

/-- Checks that optional exercises do not autograde declarations they contain. -/
register_option linter.sf.optionalAutograding : Bool := {
  defValue := true
  descr := "if true, warn when an optional exercise autogrades a declaration in its body"
}

/-- Checks that autograder directives and their targets belong to an exercise. -/
register_option linter.sf.autogradingScope : Bool := {
  defValue := true
  descr := "if true, check that autograder directives target declarations in their exercise"
}

namespace SFLMeta.Linter

/-- An occurrence of a directive in a document. -/
private structure Occurrence where
  name : Name
  ident : Ident
  line : Nat

/--
The declaration a directive name refers to, as recorded in the info tree when the directive was
elaborated. A name that resolved to several declarations, or to none, is not a directive.
-/
private def directiveName (name : Ident) : CommandElabM (Option Name) := do
  let some pos := name.raw.getPos? | return none
  let mut found : Option Name := none
  for tree in (← get).infoState.trees do
    let names := tree.foldInfo (init := #[]) fun _ info acc =>
      match info with
      | .ofTermInfo {stx, expr := .const n _, ..} =>
        if stx.getPos? == some pos then acc.push n else acc
      | _ => acc
    for n in names do
      if found.any (· != n) then return none
      found := some n
  return found

/--
Constructs `MessageData` that refers to a directive at a particular occurrence. Hovering the name
shows the directive's documentation, but "go to definition" jumps to the occurrence. This makes
linter messages more clickable.
-/
private def directiveAt (occ : Occurrence) : CommandElabM MessageData := do
  let module := (← getEnv).mainModule
  let some range ← getDeclarationRange? occ.ident | return .ofConstName occ.name
  let location : DeclarationLocation := {module, range}
  return .ofLazy (fun
    | none => pure <| .mk (MessageData.ofConstName occ.name)
    | some ctx => do
      let ⟨fmt, infos⟩ ← ppConstNameWithInfos ctx occ.name
      let infos := infos.foldl (init := {}) fun acc pos info =>
        acc.insert pos <| match info with
          | .ofTermInfo i => .ofDelabTermInfo {toTermInfo := i, location? := some location}
          | .ofDelabTermInfo i => .ofDelabTermInfo {i with location? := some location}
          | i => i
      pure <| .mk (MessageData.ofFormatWithInfos ⟨fmt, infos⟩))
    (fun _ => false)

/-- The command inside any number of `set_option ... in` and `open ... in` wrappers. -/
private partial def unwrapIn (stx : Syntax) : Syntax :=
  if stx.getKind == ``Lean.Parser.Command.in then unwrapIn stx[2] else stx

/-- The custom info value of type `α` attached to the directive containing `name`, if any. -/
private def directiveConfig? (α : Type) [TypeName α]
    (name : Ident) : CommandElabM (Option (Syntax × α)) := do
  let some pos := name.raw.getPos? | return none
  for tree in (← get).infoState.trees do
    let values := tree.foldInfo (init := #[]) fun _ info acc =>
      match info with
      | .ofCustomInfo {stx, value} =>
        if stx.getRange?.any fun range => range.start ≤ pos && pos < range.stop then
          match value.get? α with
          | some config => acc.push (stx, config)
          | none => acc
        else
          acc
      | _ => acc
    if let some value := values[0]? then return some value
  return none

/-- An occurrence for `name`, including its source line. -/
private def occurrence (name : Ident) (resolvedName : Name) : CommandElabM (Option Occurrence) := do
  let some pos := name.raw.getPos? | return none
  let line := (← getFileMap).toPosition pos |>.line
  return some {name := resolvedName, ident := name, line}

private partial def checkExerciseVisibility
    (mode : Option Occurrence) : Syntax → CommandElabM Unit
  | `(block|:::%$_ $name $_args* { $blocks* }%$_) => do
    let mut mode := mode
    if let some n ← directiveName name then
      if n == ``SFLMeta.full || n == ``SFLMeta.terse then
        mode := ← occurrence name n
      else if n == ``SFLMeta.exercise then
        let exerciseData ← directiveConfig? ExerciseData name
        if mode.isNone && exerciseData.all fun (_, data) => data.checkVisibility then
          logLint linter.sf.exerciseVisibility name
            m!"`{.ofConstName n}` is not inside a \
              `{.ofConstName ``SFLMeta.full}` or `{.ofConstName ``SFLMeta.terse}`"
    for block in blocks do
      checkExerciseVisibility mode block
  | stx =>
    for child in stx.getArgs do
      checkExerciseVisibility mode child

/-- Checks that exercises are inside `:::full` or `:::terse`. -/
private def exerciseVisibility : Linter where
  run := withSetOptionIn fun stx => do
    unless (`Verso.Doc.Concrete).isPrefixOf (unwrapIn stx).getKind do return
    unless getLinterValue linter.sf.exerciseVisibility (← getLinterOptions) do return
    checkExerciseVisibility none stx

initialize addLinter exerciseVisibility

private partial def checkVariantNesting
    (mode : Option Occurrence) : Syntax → CommandElabM Unit
  | `(block|:::%$_ $name $_args* { $blocks* }%$_) => do
    let mut mode := mode
    if let some n ← directiveName name then
      if n == ``SFLMeta.full || n == ``SFLMeta.terse then
        if let some outer := mode then
          if let some this ← occurrence name n then
            logLint linter.sf.variantNesting name
              m!"`{← directiveAt this}` nested inside a \
                `{← directiveAt outer}` on line {outer.line}"
        mode := ← occurrence name n
    for block in blocks do
      checkVariantNesting mode block
  | stx =>
    for child in stx.getArgs do
      checkVariantNesting mode child

/-- Checks that `:::full` and `:::terse` do not nest. -/
private def variantNesting : Linter where
  run := withSetOptionIn fun stx => do
    unless (`Verso.Doc.Concrete).isPrefixOf (unwrapIn stx).getKind do return
    unless getLinterValue linter.sf.variantNesting (← getLinterOptions) do return
    checkVariantNesting none stx

initialize addLinter variantNesting

private def declaredWithin (range : Syntax.Range) (declName : Name) : CommandElabM Bool := do
  let some declRange ← findDeclarationSyntaxRange? declName (fullRange := true)
    | return false
  return range.includes declRange true true

private def autogradingTargets? (directive : Name) (name : Ident) :
    CommandElabM (Option (Array Name)) := do
  if directive == ``SFLMeta.gradeTheorem then
    return (← directiveConfig? GradeTheoremConfig name).map fun (_, cfg) => (cfg.names.toArray)
  if directive == ``SFLMeta.autogradedHole then
    return (← directiveConfig? AutogradedHoleConfig name).map fun (_, cfg) => (cfg.names.toArray)
  return none

private partial def checkOptionalAutograding
    (optionalExercise : Option (Occurrence × Syntax.Range)) : Syntax → CommandElabM Unit
  | `(block|:::%$_ $name $_args* { $blocks* }%$_) => do
    let mut optionalExercise := optionalExercise
    if let some n ← directiveName name then
      if n == ``SFLMeta.exercise then
        optionalExercise := match ← occurrence name n, ← directiveConfig? ExerciseData name with
          | some exercise, some (stx, data) =>
            if data.optional then stx.getRange?.map (exercise, ·) else none
          | _, _ => none
      else if let some (exercise, range) := optionalExercise then
        if let some targets ← autogradingTargets? n name then
          for targetName in targets do
            if ← declaredWithin range targetName then
              logLint linter.sf.optionalAutograding name
                m!"optional `{← directiveAt exercise}` autogrades \
                  declaration `{.ofConstName targetName}` from its body"
    for block in blocks do
      checkOptionalAutograding optionalExercise block
  | stx =>
    for child in stx.getArgs do
      checkOptionalAutograding optionalExercise child

/-- Checks that optional exercises do not autograde declarations in their bodies. -/
private def optionalAutograding : Linter where
  run := withSetOptionIn fun stx => do
    unless (`Verso.Doc.Concrete).isPrefixOf (unwrapIn stx).getKind do return
    unless getLinterValue linter.sf.optionalAutograding (← getLinterOptions) do return
    checkOptionalAutograding none stx

initialize addLinter optionalAutograding

/-- Checks that autograder directives and their targets belong to an exercise. -/
private partial def checkAutogradingScope
    (exercise : Option (Occurrence × Syntax.Range)) : Syntax → CommandElabM Unit
  | `(block|:::%$_ $name $_args* { $blocks* }%$_) => do
    let mut exercise := exercise
    if let some n ← directiveName name then
      if n == ``SFLMeta.exercise then
        exercise := match ← occurrence name n, ← directiveConfig? ExerciseData name with
          | some exercise, some (stx, _) => stx.getRange?.map (exercise, ·)
          | _, _ => none
      else if let some targets ← autogradingTargets? n name then
        match exercise with
        | none =>
          logLint linter.sf.autogradingScope name
            m!"`{.ofConstName n}` is not inside an \
              `{.ofConstName ``SFLMeta.exercise}`"
        | some (exerciseOcc, range) =>
          for targetName in targets do
            unless ← declaredWithin range targetName do
              logLint linter.sf.autogradingScope name
                m!"`{.ofConstName n}` target `{.ofConstName targetName}` was not declared \
                  inside `{← directiveAt exerciseOcc}`"
    for block in blocks do
      checkAutogradingScope exercise block
  | stx =>
    for child in stx.getArgs do
      checkAutogradingScope exercise child

/-- Checks that autograder directives target declarations in their exercise. -/
private def autogradingScope : Linter where
  run := withSetOptionIn fun stx => do
    unless (`Verso.Doc.Concrete).isPrefixOf (unwrapIn stx).getKind do return
    unless getLinterValue linter.sf.autogradingScope (← getLinterOptions) do return
    checkAutogradingScope none stx

initialize addLinter autogradingScope

end SFLMeta.Linter
