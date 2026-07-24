module

public meta import Lean.Elab.BuiltinCommand

namespace SLFCommand

open Lean Elab Command

meta section

-- Copied from `SubVerso.Compat` to avoid making generated projects depend on verso.
-- We want to have info state and messages available right after the elaboration,
-- so we need to disable `Elab.async` which would let diagnostics produced asynchronously
-- through spanshot tasks.
private def commandWithoutAsync (act : CommandElabM Unit) : CommandElabM Unit := do
  match (← get).scopes with
  | [] => act
  | h :: t =>
    let mut orig : Option Bool := none
    try
      orig := h.opts.get? `Elab.async
      modify fun s => { s with scopes := { h with opts := h.opts.setBool `Elab.async false } :: t }
      act
    finally
      if let h :: t := (← get).scopes then
        let opts := orig.map (h.opts.setBool `Elab.async) |>.getD (h.opts.erase `Elab.async)
        modify fun s => { s with scopes := { h with opts := opts } :: t }

private def withRestoringState (keepMsgs : Bool) (m : CommandElabM Unit) : CommandElabM Unit := do
  let savedState ← get
  try
    m
  finally
    let state ← get
    set { savedState with
      -- Preserve the info tree
      infoState := state.infoState
      messages := if keepMsgs then state.messages else savedState.messages }

namespace IndentedCommands

/-! # Block Commands Parser
  Parse an indented command block. Commands are separated by new lines.
  Since we want to capture parsing errors in `sf_expect_failure`,
  we can't use Lean command parser directly in our command's syntax,
  because any parsing error occurred would fail `sf_expect_failure` itself.
  One possible solution is to first parse the whole indented body as raw syntax,
  and then run Lean's command parser followed by command elaboration.
-/

open Parser

private def rawLineEndFn : ParserFn :=
  eoiFn <|> satisfyFn (· == '\n') "line break"

/-- Consumes everything until the next newline and then consumes the newline itself. -/
private def rawLineFn : ParserFn :=
  takeUntilFn (· == '\n') >> rawLineEndFn

/- For each line after the first body line, consumes leading whitespaces.
  If it's blank, consumes the newline; otherwise consumes the line
  requiring the indentation.
-/
private def rawIndentedLineFn : ParserFn := atomicFn <|
  takeWhileFn (· == ' ') >>
  (satisfyFn (· == '\n') "line break" <|>
    (checkColGeFn "indented command sequence" >> rawLineFn))

private def rawCommandBlockFn : ParserFn :=
  rawFn (rawLineFn >> manyFn rawIndentedLineFn) (trailingWs := true)

private def rawCommandBlock : Parser := { fn := rawCommandBlockFn }

@[combinator_parenthesizer rawCommandBlock]
private def rawCommandBlock.parenthesizer := PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter rawCommandBlock]
private def rawCommandBlock.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

private partial def runRawCmdsAux
    (ictx : InputContext) (pstate : ModuleParserState) : CommandElabM Unit := do
  let state ← get
  let scope := state.scopes.head!
  let pctx :=  {
      env := state.env
      options := scope.opts
      currNamespace := scope.currNamespace
      openDecls := scope.openDecls : ParserModuleContext
    }
  let (cmd, pstate, messages) := parseCommand ictx pctx pstate state.messages
  modify fun state => { state with messages }
  unless cmd.isOfKind ``Command.eoi do
    elabCommand cmd
    runLinters cmd
    unless isTerminalCommand cmd do
      runRawCmdsAux ictx pstate

/- Recovers the source info and elaborates the commands -/
private def runRawCmds (body : Syntax) : CommandElabM Unit := do
  let some source := body.getSubstring? (withLeading := false) (withTrailing := false)
    | throwErrorAt body "command sequence has no source range"
  let fileName ← getFileName
  let fileMap ← getFileMap
  -- Recall that `rawIndentedLineFn` may consume whitespaces after the newline.
  -- Here we move the ending back to the last non-whitespace character to produce
  -- correctly positioned diagnostics.
  let stopPos := source.trimRight.stopPos
  if h : stopPos ≤ fileMap.source.rawEndPos then
    let ictx := InputContext.mk fileMap.source fileName
      (fileMap := fileMap) (endPos := stopPos) (endPos_valid := h)
    runRawCmdsAux ictx { pos := source.startPos, recovering := false, hasLeading := false }
  else
    throwErrorAt body "invalid command-sequence source range"

end IndentedCommands

end

public meta section

open Parser IndentedCommands

/--
Elaborates the enclosed commands and reports their diagnostics,
but discards their effects afterwards.

Example:
```lean
sf_experiment
  def hidden : Nat := 1
  #check hidden
-- `hidden` is not available here.
```
-/
def experimentTk := leading_parser
  "sf_experiment"

@[command_parser] def experimentCmd := leading_parser
  experimentTk >> checkLinebreakBefore "indented command sequence" >>
    checkColGt "indented command sequence" >> withPosition rawCommandBlock

/--
Succeeds only if the enclosed commands fail.
Diagnostics from the expected failure are suppressed.

Example:
```lean
sf_expect_failure
  example : 1 = 2 := rfl
```
-/
def expectFailureTk := leading_parser
  "sf_expect_failure"

/-
  Like `sf_expect_failure` but reports the diagnostics.
-/
def expectFailureInfoTk := leading_parser
  "sf_expect_failure?"

@[command_parser] def expectFailureCmd := leading_parser
  expectFailureTk >> checkLinebreakBefore "indented command sequence" >>
    checkColGt "indented command sequence" >> withPosition rawCommandBlock

@[command_parser] def expectFailureInfoCmd := leading_parser
  expectFailureInfoTk >> checkLinebreakBefore "indented command sequence" >>
    checkColGt "indented command sequence" >> withPosition rawCommandBlock

@[command_elab experimentCmd]
def elabExperimentCmd : CommandElab := fun stx => do
  let body := stx.getArgs.back!
  commandWithoutAsync <| withRestoringState true do
    runRawCmds body

@[command_elab expectFailureCmd, command_elab expectFailureInfoCmd]
def elabExpectFailureCmd : CommandElab := fun stx => do
  let keepMsgs := stx.isOfKind ``expectFailureInfoCmd
  unless keepMsgs || stx.isOfKind ``expectFailureCmd do
    throwUnsupportedSyntax
  let tk := stx[0]
  let body := stx.getArgs.back!
  commandWithoutAsync <| withRestoringState keepMsgs do
    withRef tk <| failIfSucceeds <| runRawCmds body

end

namespace Tests

/--
@ +3:11...+4:8
info: unexpected token '#check'; expected 'with'
---
@ +3:4...9
info: Missing cases:
_
---
@ +4:2...8
info: 1 : Nat
-/
#guard_msgs (positions := true) in
sf_expect_failure?
  def f (n : Nat) : Nat :=
    match n
  #check 1

/-- info: Nat : Type -/
#guard_msgs in
#check Nat

/--
info: SLFCommand.Tests.x : Nat
---
info: 3
-/
#guard_msgs in
sf_experiment
  def x : Nat := 1
  #check x
  def f : Nat → Nat
    | 0 => 0
    | n + 1 => n + 2
  #eval f 2

/-- error: Unknown identifier `x` -/
#guard_msgs in
#check x

/--
error: Type mismatch
  "qwq"
has type
  String
but is expected to have type
  Nat
-/
#guard_msgs in
sf_experiment
  def y : Nat := "qwq"

/-- info: invalid 'import' command, it must be used in the beginning of the file -/
#guard_msgs in
sf_expect_failure?
  import Lean

/-- warning: using 'exit' to interrupt Lean -/
#guard_msgs in
sf_experiment
  #exit

end Tests

end SLFCommand
