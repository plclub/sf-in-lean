import VersoManual

open Lean (Json quote)
open Verso Doc Elab

namespace SFLMeta

/-! ## Block extensions used by the saver -/

/-!
`Block.diagramWithAlt` wraps a diagram and an ASCII-text fallback. The HTML
and TeX renderings emit only the diagram child; the saver emits only the
text-fallback child wrapped in a `/-! … -/` module-doc comment. -/

block_extension Block.diagramWithAlt where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ _ contents => do
      contents.foldlM (init := (.empty : Verso.Output.Html)) fun acc b => do
        match b with
        | .code _ => pure acc
        | _ => return acc ++ (← goB b)
  toTeX :=
    open Verso.Output.TeX in
    some fun _ goB _ _ contents => do
      contents.foldlM (init := (.empty : Verso.Output.TeX)) fun acc b => do
        match b with
        | .code _ => pure acc
        | _ => return acc ++ (← goB b)

/-! ## `:::diagramWithAlt` directive -/

/--
A `:::diagramWithAlt` directive wraps a diagram code block and an ASCII text
fallback. The HTML book renders only the diagram; the saver emits only the
text fallback. Use it to attach an ASCII alt that ends up in the generated
`.lean` files in place of the SVG. -/
@[directive]
def diagramWithAlt : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other SFLMeta.Block.diagramWithAlt #[$blocks,*])


/-! ## `importBlock` code block

A chapter's cross-chapter `import` lines (e.g. `import LF.Basics`) must live in
the Verso module *header* (where they are rewritten to the `…Verso` module
names), so they never appear in the chapter's elaborated `lean` blocks — yet
the book reader should still see them where the prose introduces them.  An
` ```importBlock ` code block carries the original import line(s) verbatim and
renders as a plain code block in HTML.  It is display-only: the extracted
student/solutions/terse chapter files get their `import` preamble from the
chapter source's header in `emitSavedImpl` (which also bundles non-chapter
prerequisite modules into the generated project). -/

block_extension Block.importBlock (source : String) where
  data := Json.str source
  traverse _ _ _ := pure none
  toHtml := some fun _ goB _ _ contents => contents.mapM goB
  toTeX := some fun _ goB _ _ contents => contents.mapM goB

/-- An ` ```importBlock ` code block: cross-chapter `import` lines for the
generated projects, rendered to the reader as a plain code block. The body is
not elaborated here (the real imports for the book build are in the Verso
module header). -/
@[code_block]
def importBlock : CodeBlockExpanderOf Unit
  | (), str => do
    let src := str.getString
    ``(Verso.Doc.Block.other (SFLMeta.Block.importBlock $(quote src))
        #[Verso.Doc.Block.code $(quote src)])
