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
    let extraSteps :=
      if showSols then [SFLMeta.Save.emitSavedSolutions vol.toUpper]
      else if mode == "terse" then [SFLMeta.Save.emitSavedTerse vol.toUpper]
      else [SFLMeta.Save.emitSavedStudent vol.toUpper]
    let config := mkConfig vol mode
    match vol with
    | "lf" => manualMain (%doc LF) (options := rest) (config := config) (extraSteps := extraSteps)
    | "hl" => manualMain (%doc HL) (options := rest) (config := config) (extraSteps := extraSteps)
    | "ts" => manualMain (%doc TS) (options := rest) (config := config) (extraSteps := extraSteps)
    | _ => IO.eprintln s!"unknown volume '{vol}'"; return 1
  | _ =>
    IO.eprintln "usage: sfl <volume> <mode>  (volume: lf | hl | ts; mode: student | solutions | terse)"
    return 1
