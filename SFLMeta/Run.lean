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
volume slug (`lf`/`hl`/`ts`); `mode` is `student`/`solutions`/`terse`; `stamp` is
this build's stamp (`SFLMeta.buildStamp`), which `extraContents` puts at the foot
of every page and the saver repeats as a comment at the end of every generated
`.lean` file. -/
def mkConfig (vol mode stamp : String) : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraCss := {SFLMeta.sfTheme}
  extraContents := #[buildStampHtml stamp]
  destination := s!"_out/{vol}/{mode}"

/-- Verso hardwires the multi-page HTML output directory to `html-multi/`.  SFL
only ever emits the multi-page form, so the qualifier buys nothing and the
directory is renamed to plain `html/` once the build has finished. -/
def renameHtmlDir (dest : System.FilePath) : IO Unit := do
  let multi := dest.join "html-multi"
  let html := dest.join "html"
  if ← multi.pathExists then
    if ← html.pathExists then
      IO.FS.removeDirAll html
    IO.FS.rename multi html

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
  | mode :: rest => do
    let some variant := Variant.fromString? mode
      | IO.eprintln s!"invalid mode: {mode}"
        IO.eprintln "mode must be student, solutions, or terse"
        return 1
    setCurrVariant variant
    -- Read the clock once: the HTML pages and the extracted `.lean` files of a
    -- single build must carry the same stamp, not two readings a few seconds
    -- apart.
    let stamp ← buildStamp
    let extraStep := match variant with
      | .student => Save.emitSavedStudent vol.toUpper stamp crossVol
      | .solutions => Save.emitSavedSolutions vol.toUpper stamp crossVol
      | .terse => Save.emitSavedTerse vol.toUpper stamp crossVol
      | .grading => Save.emitSavedGrading vol.toUpper stamp crossVol
    let config := mkConfig vol mode stamp
    let rc ← manualMain doc (options := rest) (config := config) (extraSteps := [extraStep])
    if rc == 0 then
      renameHtmlDir config.destination
    return rc
  | _ =>
    IO.eprintln "usage: sfl-<vol> <mode>  (mode: student | solutions | terse | grading)"
    return 1

end SFLMeta
