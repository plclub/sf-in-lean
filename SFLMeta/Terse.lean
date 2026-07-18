import VersoManual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace SFLMeta

/-!
`Block.terse` wraps content that appears only in terse (lecture/live-coding)
builds. During traversal of a full build it is replaced with an empty block. -/
block_extension Block.terse where
  data := Json.null
  traverse _ _ _ := do
    if ← isDraft then
      return none            -- terse build: keep, recurse into children
    else
      return some (.concat #[])  -- full build: hide
  toHtml :=
    some fun _ goB _ _ contents =>
      Verso.Output.Html.seq <$> contents.mapM goB
  toTeX := none

/-!
`Block.full` wraps content that appears only in full (reading/HTML) builds.
During traversal of a terse build it is replaced with an empty block. -/
block_extension Block.full where
  data := Json.null
  traverse _ _ _ := do
    if ← isDraft then
      return some (.concat #[])  -- terse build: hide
    else
      return none            -- full build: keep, recurse into children
  toHtml :=
    some fun _ goB _ _ contents =>
      Verso.Output.Html.seq <$> contents.mapM goB
  toTeX := none

/-!
`Block.suppressPreviousHeaderWhenTerse` marks the section heading immediately
before it as full-only. A heading cannot sit inside a `:::full` directive
(headings create document parts; directives hold blocks), so a heading that the
source scopes to the full build stays at part level and this empty sibling
marker carries the intent instead. During traversal of a full build the marker
disappears (the heading shows normally); in a terse build it survives, and its
consumers suppress the heading: `walkSection` (SFLMeta.Save) omits the heading
comment from the generated terse `.lean`, and the marker's HTML (an empty
`<div class="suppress-previous-header-when-terse">`) lets the theme CSS hide
the rendered heading. -/
block_extension Block.suppressPreviousHeaderWhenTerse where
  data := Json.null
  traverse _ _ _ := do
    if ← isDraft then
      return none            -- terse build: keep the marker for its consumers
    else
      return some (.concat #[])  -- full build: heading shows; no marker needed
  toHtml :=
    some fun _ _ _ _ _ =>
      pure (Verso.Output.Html.tag "div"
        #[("class", "suppress-previous-header-when-terse")] .empty)
  toTeX := none

@[directive]
def terse : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other SFLMeta.Block.terse #[$blocks,*])

@[directive]
def full : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other SFLMeta.Block.full #[$blocks,*])

@[directive]
def suppressPreviousHeaderWhenTerse : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Verso.Doc.Block.other SFLMeta.Block.suppressPreviousHeaderWhenTerse #[])

end SFLMeta
