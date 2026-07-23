import VersoManual
import LF
import HL
import TS
import SFLMeta.Theme

open Verso Genre Manual

private def mkConfig (vol mode : String) : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraCss := {SFLMeta.sfTheme}
  draft := mode == "terse"
  destination := s!"_out/{vol}/{mode}"

def main (args : List String) : IO UInt32 := do
  match args with
  | vol :: mode :: rest =>
    let showSols := mode == "solutions"
    SFLMeta.Save.showSolutions.set showSols
    -- Verso chapters from earlier volumes that a later volume's chapters import
    -- (e.g. `HL.Imp` imports `LF.Typeclasses`).  They must go through the same
    -- Verso → Lean transformation as the volume's own chapters when their
    -- standalone `.lean` is extracted, so they are handed to the saver as
    -- `(volume-prefix, chapter-part)` pairs rather than bundled verbatim.
    let crossVol : List (String × Verso.Doc.Part Manual) :=
      match vol with
      | "hl" => [("LF", %doc LF.Typeclasses)]
      | _ => []
    let extraSteps :=
      if showSols then [SFLMeta.Save.emitSavedSolutions vol.toUpper crossVol]
      else if mode == "terse" then [SFLMeta.Save.emitSavedTerse vol.toUpper crossVol]
      else [SFLMeta.Save.emitSavedStudent vol.toUpper crossVol]
    let config := mkConfig vol mode
    match vol with
    | "lf" => manualMain (%doc LF) (options := rest) (config := config) (extraSteps := extraSteps)
    | "hl" => manualMain (%doc HL) (options := rest) (config := config) (extraSteps := extraSteps)
    | "ts" => manualMain (%doc TS) (options := rest) (config := config) (extraSteps := extraSteps)
    | _ => IO.eprintln s!"unknown volume '{vol}'"; return 1
  | _ =>
    IO.eprintln "usage: sfl <volume> <mode>  (volume: lf | hl | ts; mode: student | solutions | terse)"
    return 1
