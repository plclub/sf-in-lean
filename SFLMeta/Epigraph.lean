import VersoManual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace SFLMeta

/-! ## `:::epigraph` directive

A section-opening quotation (an *epigraph*). In the Rocq sources these were
written `#<div class="quote">#"…"#</div>#`; that block markup was lost in the
port and now survives only as a bare quoted comment at the head of a section
(`/- "…" -/`). This directive restores it.

For the moment it simply renders its contents in italics (HTML and TeX) — a
placeholder for a future proper pull-quote treatment. The saver emits the
contents unwrapped: the epigraph is a display concern, not part of the
extracted `.lean` source.

Author syntax:

````markdown
:::epigraph
"Informal proofs are algorithms; formal proofs are code."
:::
```` -/

block_extension Block.epigraph where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ _ contents => do
      let body : Verso.Output.Html ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      return {{ <div class="sf-quote">{{body}}</div> }}
  toTeX :=
    open Verso.Output.TeX in
    some fun _ goB _ _ contents => do
      let body : Verso.Output.TeX ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      pure <| .seq #[.raw "\\textit{", body, .raw "}"]
  extraCss := [
r##"
div.sf-quote {
  font-style: italic;
  margin: 1em 0;
}
"##
  ]

/-- A `:::epigraph` directive wraps its contents in a section-opening
quotation, rendered (for now) in italics. -/
@[directive]
def epigraph : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other SFLMeta.Block.epigraph #[$blocks,*])

end SFLMeta
