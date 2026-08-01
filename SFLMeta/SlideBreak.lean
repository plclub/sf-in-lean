import VersoManual

import SFLMeta.Variant

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace SFLMeta

/-!
`Block.slidebreak` marks a slide-break point. In terse HTML output it renders
as an empty `<div class="slide-break">` (a hook for slide tooling via CSS);
in student and solutions HTML output it is removed, and in all generated `.lean`
files it emits nothing. -/
block_extension Block.slidebreak where
  data := Json.null
  traverse _ _ _ := do
    if (← getCurrVariant).isTerse then
      -- keep slidebreak blocks in terse variant
      return none
    else
      return some (.concat #[])
  toHtml :=
    some fun _ _ _ _ _ =>
      pure (.tag "div" #[("class", "slide-break")] .empty)
  toTeX := none

@[directive]
def slidebreak : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Verso.Doc.Block.other SFLMeta.Block.slidebreak #[])

end SFLMeta
