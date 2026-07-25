import VersoManual
import HL
import LF.Typeclasses
import SFLMeta.Run

open Verso Genre Manual

/-- Executable `sfl-hl`: builds the Hoare Logic volume.
    Usage: `lake exe sfl-hl <mode>`  (mode: student | solutions | terse).

    `HL.Imp` imports `LF.Typeclasses`, so that prerequisite chapter is handed to
    the saver as a cross-volume pair (see `SFLMeta.runVolume`). -/
def main (args : List String) : IO UInt32 :=
  SFLMeta.runVolume "hl" (%doc HL) [("LF", %doc LF.Typeclasses)] args
