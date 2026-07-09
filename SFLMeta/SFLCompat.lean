module

public meta import Lean.Elab.BuiltinCommand

namespace SLFCommand

meta section

open Lean Elab Command

private def withRestoringState (keepMsgs : Bool) (m : CommandElabM Unit) : CommandElabM Unit := do
  let savedState ← get
  try
    m
  finally
    let msgs := (← get).messages
    set { savedState with messages := if keepMsgs then msgs else savedState.messages }

private def runCmds (cmds : TSyntaxArray `command) : CommandElabM Unit := do
  for cmd in cmds do
    elabCommand cmd
    runLinters cmd

private def runSandboxedCmds (ref : Syntax)
    (expectError : Bool)
    (keepMsgs : Bool)
    (cmds : TSyntaxArray `command) : CommandElabM Unit := do
  let f := withRestoringState keepMsgs
  if expectError then
    f <| withRef ref <| failIfSucceeds <| runCmds cmds
  else
    f <| runCmds cmds

/--
Elaborates the enclosed commands and reports their diagnostics,
but discards their effects afterwards.

Example:
```lean
experiment

  def hidden : Nat := 1
  #check hidden

end_experiment
-- `hidden` is not available here.
```
-/
syntax (name := experimentCmd)
  "experiment" ppLine command* "end_experiment": command

/--
Succeeds only if the enclosed commands fail.
Diagnostics from the expected failure are suppressed.

Example:
```lean
expect_failure
  example : 1 = 2 := rfl
end_expect_failure
```
-/
syntax (name := expectFailureCmd)
  "expect_failure" ppLine command* "end_expect_failure" : command

/--
Similar to `expect_failure` but preserves expected-failure diagnostics as informational messages.
-/
syntax (name := expectFailureInfoCmd)
  "expect_failure?" ppLine command* "end_expect_failure" : command

@[command_elab experimentCmd]
public def elabExperimentCmd : CommandElab := fun stx => do
  match stx with
    | `(command| experiment $cmds:command* end_experiment) =>
      runSandboxedCmds stx false true cmds
    | _ => throwUnsupportedSyntax

@[command_elab expectFailureCmd, command_elab expectFailureInfoCmd]
public def elabExpectFailureCmd : CommandElab := fun stx => do
  let (keepMsgs, cmds) ← match stx with
    | `(command| expect_failure $cmds:command* end_expect_failure) => pure (false, cmds)
    | `(command| expect_failure? $cmds:command* end_expect_failure) => pure (true, cmds)
    | _ => throwUnsupportedSyntax
  runSandboxedCmds stx true keepMsgs cmds

end

end SLFCommand
