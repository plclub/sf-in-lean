-- AI-generated regression test for inversion's proof-state buttons.
-- Run with: lake env lean tests/inversion_highlighting.lean
import LF.CustomTactics
import SubVerso.Highlighting
import Verso.Code.Highlighted

open Lean Elab Command SubVerso Highlighting Verso.Code

private def highlightInput (input : String) : CommandElabM Highlighted := do
  let inputCtx := Parser.mkInputContext input "<input>"
  let (headerStx, parserState, msgs) ← Parser.parseHeader inputCtx
  let commandState : Command.State := {
    env := (← getEnv)
    maxRecDepth := (← get).maxRecDepth
    messages := msgs
  }
  let (result, _) ← Compat.Frontend.processCommands headerStx
    |>.run { inputCtx } |>.run { commandState, parserState, cmdPos := parserState.pos }
  let result := result.updateLeading input
  for item in result.items do
    let msgs := Compat.messageLogArray item.messages
    unless msgs.isEmpty do
      throwError "Unexpected messages: {← msgs.mapM (·.toString)}"
  runTermElabM fun _ =>
    withTheReader Core.Context (fun ctx => { ctx with fileMap := inputCtx.fileMap }) do
      let hls ← highlightFrontendResult result
      return hls.foldl (· ++ ·) .empty

-- Compare visible names and types without internal free-variable identifiers.
private partial def statesOf : Highlighted → Array (String × Array String)
  | .seq xs => xs.flatMap statesOf
  | .span _ h => statesOf h
  | .tactics goals _ _ h => #[(h.toString, goals.map (·.toString))] ++ statesOf h
  | _ => #[]

private def renderHtml (hl : Highlighted) : String :=
  let ctx : HighlightHtmlM.Context Verso.Doc.Genre.none :=
    { linkTargets := {}, traverseContext := (), definitionIds := {}, options := {} }
  let (html, _) := (hl.blockHtml "inversion-test").run ctx |>.run {}
  html.asString

run_cmd do
  let tests := #[
    ("example (p q : Prop) (h : p ∨ q) : q ∨ p := by\n",
      "  | inl hp => exact Or.inr hp\n  | inr hq => exact Or.inl hq\n",
      #[("by", 1), ("| inl hp =>", 1), ("exact Or.inr hp", 0),
        ("| inr hq =>", 1), ("exact Or.inl hq", 0)]),
    ("example (p : Prop) (h : p ∨ p) : p := by\n",
      "  | inl hp | inr hp => exact hp\n",
      #[("by", 1), ("| inl hp", 1), ("| inr hp", 1), ("=>", 2), ("exact hp", 0)]),
    ("example (p : Prop) (h : p ∨ p) : p := by\n",
      "  | _ hp => exact hp\n",
      #[("by", 1), ("| _ hp =>", 2), ("exact hp", 0)])]
  for (header, alternatives, expected) in tests do
    let casesCode ← highlightInput (header ++ "  cases h with\n" ++ alternatives)
    let inversionCode ← highlightInput (header ++ "  inversion h with\n" ++ alternatives)
    let casesStates := statesOf casesCode
    let inversionStates := statesOf inversionCode
    unless inversionStates == casesStates do
      throwError "Proof states differ:\ncases: {repr casesStates}\ninversion: {repr inversionStates}"
    unless inversionStates.map (fun (label, goals) => (label, goals.size)) == expected do
      throwError "Missing branch proof states: {repr inversionStates}"
    for code in [casesCode, inversionCode] do
      let buttons := (renderHtml code).splitOn "class=\"tactic-toggle\"" |>.length
      unless buttons == expected.size + 1 do
        throwError "Expected {expected.size} HTML proof-state buttons, got {buttons - 1}"

-- Reusing the core parser does not add support for its other alternative forms.
/-- error: Could not parse inversion alternative -/
#guard_msgs(error) in
example (p : Prop) (h : p ∨ p) : p := by
  inversion h with
  | @inl hp => exact hp
  | inr hp => exact hp

/-- error: Could not parse inversion alternatives -/
#guard_msgs(error) in
example (p : Prop) (h : p ∨ p) : p := by
  inversion h with
  | inl hp

/-- error: Could not parse inversion alternatives -/
#guard_msgs(error) in
example (p : Prop) (h : p ∨ p) : p := by
  inversion h with
  | inl hp => _
  | inr hp => exact hp

/-- error: Could not parse inversion alternatives -/
#guard_msgs(error) in
example (p : Prop) (h : p ∨ p) : p := by
  inversion h with
  | inl hp => ?_
  | inr hp => exact hp
