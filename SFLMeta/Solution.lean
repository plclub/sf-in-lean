import VersoManual
import SFLMeta.Save

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace SFLMeta

/-!
`Block.solution` wraps a worked solution (prose or non-compiling illustrative
code) that should appear only in the *solutions* build.  It mirrors
`Block.terse` / `Block.full`, but keys on `Save.showSolutions` (set by the
`lf_solutions` executable) instead of `isDraft`: in the solutions build the
content is kept and rendered; in the student and terse builds traversal replaces
it with an empty block, so it reaches neither the HTML nor the extracted `.lean`.

This complements the two code-level solution mechanisms (`solution!(…)` and the
textual `-- SOLUTION … -- END SOLUTION`), which elide *compilable* answers; this
one is for answers that are not compilable Lean (e.g. a `:::solution` worked
discussion). -/
block_extension Block.solution where
  data := Json.null
  traverse _ _ _ := do
    if ← Save.showSolutions.get then
      return none                 -- solutions build: keep, recurse into children
    else
      return some (.concat #[])   -- student/terse build: hide
  toHtml :=
    some fun _ goB _ _ contents =>
      Verso.Output.Html.seq <$> contents.mapM goB
  toTeX := none

@[directive]
def solution : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other SFLMeta.Block.solution #[$blocks,*])

end SFLMeta
