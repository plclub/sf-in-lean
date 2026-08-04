import VersoManual
import SFLMeta.Save

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace SFLMeta

/-!
`Block.solution` wraps a worked solution (prose or non-compiling illustrative
code) that should appear only in the *solutions* build. -/
block_extension Block.solution where
  data := Json.null
  traverse _ _ _ := do
    if (← getCurrVariant).isSolution then
      -- keep solution blocks in solution variant
      return none
    else
      return some (.concat #[])
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
