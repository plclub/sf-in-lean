module

public import Lean
public import Autograder.Basic

public def main (args : List String) : IO Unit := do
  let some (assignment : String) := args[0]?
    | throw <| .userError "Expected ASSIGNMENT"
  let some (submission : String) := args[1]?
    | throw <| .userError "Expected SUBMISSION"

  let debug := (← IO.getEnv "AUTOGRADER_DEBUG") == some "1"

  let sysroot ← Lean.findSysroot
  IO.println s!"Using toolchain: {sysroot}"
  Lean.initSearchPath sysroot

  -- Note: this requires the modules to be built with lake first!
  let env_assignment ← Lean.importModules #[
    { module := Lean.Syntax.decodeNameLit ("`" ++ assignment) |>.get! }
  ] {}
  let env_submission ← Lean.importModules #[
    { module := Lean.Syntax.decodeNameLit ("`" ++ submission) |>.get! }
  ] {}

  let _ ← ((check env_assignment env_submission).runWithDebug debug).run' ∅
