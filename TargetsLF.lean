import VersoManual
import LF
import SFLMeta.Run

open Verso Genre Manual

/-- Executable `sfl-lf`: builds the Logical Foundations volume.
    Usage: `lake exe sfl-lf <mode>`  (mode: student | solutions | terse). -/
def main (args : List String) : IO UInt32 :=
  SFLMeta.runVolume "lf" (%doc LF) [] args
