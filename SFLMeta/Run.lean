import VersoManual
-- Import the full `SFLMeta` aggregate (not just `Save`/`Theme`): `manualMain`'s
-- default `extension_impls%` collects the registered block/inline extensions
-- from *this* module's environment, so every `block_extension` (`:::instructors`,
-- `:::hide`, `:::gradeTheorem`, …) must be in scope here or HTML rendering panics
-- with "No block traversal implementation found".  (This module is deliberately
-- *not* part of the `SFLMeta` aggregate, so importing it back is not a cycle.)
import SFLMeta

open Verso Genre Manual

namespace SFLMeta

/-- Render configuration for a single volume/mode build.  `vol` is the lowercase
volume slug (`lf`/`hl`/`ts`); `mode` is `student`/`solutions`/`terse`. -/
def mkConfig (vol mode : String) : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraCss := {SFLMeta.sfTheme}
  draft := mode == "terse"
  destination := s!"_out/{vol}/{mode}"

/-- Build one volume in one mode.  Each per-volume executable (`sfl-lf`,
`sfl-hl`, `sfl-ts`) calls this with its own `%doc` so that no single module ever
imports two volume roots — that keeps chapters shared across volumes (a symlinked
`HL/Slang.lean` ↔ `TS/Slang.lean`) from colliding on their `namespace`
declarations.

`crossVol` lists any prerequisite chapters from *earlier* volumes that this
volume's chapters `import` (e.g. `HL.Imp` imports `LF.Typeclasses`).  They must
go through the same Verso → Lean transformation as the volume's own chapters when
their standalone `.lean` is extracted, so they are handed to the saver as
`(volume-prefix, chapter-part)` pairs rather than bundled verbatim. -/
def runVolume (vol : String) (doc : Verso.Doc.Part Manual)
    (crossVol : List (String × Verso.Doc.Part Manual) := []) (args : List String) : IO UInt32 := do
  match args with
  | mode :: rest =>
    let showSols := mode == "solutions"
    Save.showSolutions.set showSols
    let extraSteps :=
      if showSols then [Save.emitSavedSolutions vol.toUpper crossVol]
      else if mode == "terse" then [Save.emitSavedTerse vol.toUpper crossVol]
      else [Save.emitSavedStudent vol.toUpper crossVol]
    let config := mkConfig vol mode
    manualMain doc (options := rest) (config := config) (extraSteps := extraSteps)
  | _ =>
    IO.eprintln "usage: sfl-<vol> <mode>  (mode: student | solutions | terse)"
    return 1

end SFLMeta
