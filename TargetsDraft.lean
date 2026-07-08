-- AI-generated (Claude), temporary scaffolding.
--
-- Executable that builds the draft LF book (LFDraft.lean) and emits solutions
-- (or student) `.lean` for its included generated chapters under
-- `_out/lf-draft/<mode>/lean/LF/`.  See LFDraft.lean for the purpose.
--
--   lake exe sfl-draft solutions   -- solution-filled `.lean` (the default)
--   lake exe sfl-draft student     -- student (`sorry`-elided) `.lean`
import VersoManual
import LFDraft
import SFLMeta.Theme

open Verso Genre Manual

private def mkConfig (mode : String) : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraCss := {SFLMeta.sfTheme}
  draft := false
  destination := s!"_out/lf-draft/{mode}"

def main (args : List String) : IO UInt32 := do
  let mode := args.headD "solutions"
  let showSols := mode == "solutions"
  SFLMeta.showSolutions.set showSols
  let extraSteps :=
    if showSols then [SFLMeta.emitSavedSolutionsTo "lf-draft" "LF"]
    else [SFLMeta.emitSavedStudentTo "lf-draft" "LF"]
  let config := mkConfig mode
  manualMain (%doc LFDraft) (options := args.drop 1) (config := config) (extraSteps := extraSteps)
