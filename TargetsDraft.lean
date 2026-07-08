-- AI-generated (Claude), temporary scaffolding.
--
-- Executable that builds the draft LF book (LFDraft.lean) and emits solutions
-- (or student) `.lean` for its included generated chapters under
-- `_out/lf-draft/<mode>/lean/LF/`.  See LFDraft.lean for the purpose.
--
--   lake exe sfl-draft solutions   -- solution-filled `.lean` (the default)
--   lake exe sfl-draft student     -- student (`sorry`-elided) `.lean`
--   lake exe sfl-draft terse       -- lecture `.lean` (solutions and
--                                  -- `workinclass!` proofs stubbed)
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
  draft := mode == "terse"   -- the terse build is the draft build (cf. Targets)
  destination := s!"_out/lf-draft/{mode}"

def main (args : List String) : IO UInt32 := do
  let mode := args.headD "solutions"
  let showSols := mode == "solutions"
  SFLMeta.showSolutions.set showSols
  -- NB: written without `[…]` literals: importing LFDraft pulls in the Lists
  -- chapter's high-priority NatList square-bracket macro, which hijacks list
  -- literals here.  (Real fix: make that macro `scoped`/local to the chapter.)
  let extraSteps :=
    if showSols then List.cons (SFLMeta.emitSavedSolutionsTo "lf-draft" "LF") List.nil
    else if mode == "terse" then List.cons (SFLMeta.emitSavedTerseTo "lf-draft" "LF") List.nil
    else List.cons (SFLMeta.emitSavedStudentTo "lf-draft" "LF") List.nil
  let config := mkConfig mode
  manualMain (%doc LFDraft) (options := args.drop 1) (config := config) (extraSteps := extraSteps)
