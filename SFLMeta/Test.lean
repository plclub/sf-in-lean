import VersoManual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual

namespace SFLMeta

/-!
`Block.test` wraps content that must *elaborate* when the book is built but that
appears in no build product: nothing is rendered in HTML or TeX, and the saver
emits nothing into the generated `.lean` files.

It is the home for regression checks on a chapter's own machinery — a run of
`#check`s confirming that a notation still parses the way the chapter claims,
say.  Those checks are worth keeping and worth running, but they are not part of
the exposition, and a reader working through the extracted `.lean` should never
meet them.

Contrast the neighbouring directives, none of which does this job:

* `:::ignore` elaborates and renders, and is dropped only from the extracted
  `.lean` — so its content is still in the book.
* `::::hide` drops its body at *elaboration* (like `:::dev` and
  `:::instructors`), so Lean code inside it is inert text that is never checked.
  That is the right treatment for the parked, aspirational code those blocks
  hold across the LF chapters, but it is the opposite of what a live check
  needs.

Because the body really is elaborated, a ` ```lean ` block inside `:::test` runs
for real: it can fail the build, which is the point. -/
block_extension Block.test where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX  := some fun _ _ _ _ _ => pure .empty

/--
A `:::test` directive: Lean content that is checked when the book is built but
that reaches neither the HTML book nor the generated `.lean` files. -/
@[directive]
def test : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other SFLMeta.Block.test #[$blocks,*])

end SFLMeta
