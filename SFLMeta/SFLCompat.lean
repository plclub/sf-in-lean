module

public meta import Lean.Elab.BuiltinCommand

namespace SLFCommand

meta section

open Lean Elab Command Parser

-- Copied from `SubVerso.Compat` to avoid making generated projects depend on verso.
-- We want to have info state and messages available right after the elaboration,
-- so we need to disable `Elab.async` which would let diagnostics produced asynchronously
-- through spanshot tasks.
def commandWithoutAsync (act : CommandElabM Unit) : CommandElabM Unit := do
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

private def runCmds (cmds : TSyntaxArray `command) : CommandElabM Unit := do
  for cmd in cmds do
    elabCommand cmd
    runLinters cmd

private def runSandboxedCmds (ref : Syntax)
    (expectError : Bool)
    (keepMsgs : Bool)
    (cmds : TSyntaxArray `command) : CommandElabM Unit :=
  commandWithoutAsync <| withRestoringState keepMsgs do
    if expectError then
      withRef ref <| failIfSucceeds <| runCmds cmds
    else
      runCmds cmds

/--
Elaborates the enclosed commands and reports their diagnostics,
but discards their effects afterwards.

Example:
```lean
sf_experiment

  def hidden : Nat := 1
  #check hidden

end
-- `hidden` is not available here.
```
-/
public def experimentTk := leading_parser
  "sf_experiment"

/--
  Closes `sf_experiment`.
-/
public def experimentEndTk := leading_parser
  "end"

@[command_parser] public def experimentCmd := leading_parser
  experimentTk >> many1 (ppLine >> notSymbol "end" >> commandParser) >>
  ppDedent (ppLine >> experimentEndTk)

/--
Succeeds only if the enclosed commands fail.
Diagnostics from the expected failure are suppressed.

Example:
```lean
sf_expect_failure
  example : 1 = 2 := rfl
end
```
-/
public def expectFailureTk := leading_parser
  "sf_expect_failure"

/-
  Like `sf_expect_failure` but reports the diagnostics.
-/
public def expectFailureInfoTk := leading_parser
  "sf_expect_failure?"

/--
  Closes `sf_expect_failure`.
-/
public def expectFailureEndTk := leading_parser
  "end"

@[command_parser] public def expectFailureCmd := leading_parser
  expectFailureTk >> many1 (ppLine >> notSymbol "end" >> commandParser) >>
  ppDedent (ppLine >> expectFailureEndTk)

@[command_parser] public def expectFailureInfoCmd := leading_parser
  expectFailureInfoTk >> many1 (ppLine >> notSymbol "end" >> commandParser) >>
  ppDedent (ppLine >> expectFailureEndTk)

@[command_elab experimentCmd]
public def elabExperimentCmd : CommandElab := fun stx => do
  match stx with
    | `(command| sf_experiment%$tk $cmds:command* end) =>
      runSandboxedCmds tk false true cmds
    | _ => throwUnsupportedSyntax

@[command_elab expectFailureCmd, command_elab expectFailureInfoCmd]
public def elabExpectFailureCmd : CommandElab := fun stx => do
  let (tk, keepMsgs, cmds) ← match stx with
    | `(command| sf_expect_failure%$tk $cmds:command* end) => pure (tk, false, cmds)
    | `(command| sf_expect_failure?%$tk $cmds:command* end) => pure (tk, true, cmds)
    | _ => throwUnsupportedSyntax
  runSandboxedCmds tk true keepMsgs cmds

end

end SLFCommand
