import VersoManual
import TS
import LF.Typeclasses
import SFLMeta.Run

open Verso Genre Manual

/-- Executable `sfl-ts`: builds the Type Systems volume.
    Usage: `lake exe sfl-ts <mode>`  (mode: student | solutions | terse). -/
def main (args : List String) : IO UInt32 :=
  SFLMeta.runVolume "ts" (%doc TS) [("LF", %doc LF.Typeclasses)] args
