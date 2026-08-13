import VersoManual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace SFLMeta

/-! ## `:::details` directive

A collapsible disclosure block: the optional positional `summary` string is
shown by default as a one-line teaser; the contents are revealed only when the
reader expands the block. When omitted, the summary defaults to `"Details"`.
Useful for tucking away encoding details (macro plumbing, helper notation) that
aren't part of the main narrative.

Author syntax:

````markdown
:::details "Lean encoding"
The macros below set up the `<{ … }>` notation for STLC terms.

```lean
…
```
:::
````

HTML output uses native `<details>` / `<summary>` so it works without JS.
TeX output renders the summary as italic running text followed by the
contents. The saver emits the contents unwrapped — collapsibility is a UI
concern, not part of the source. -/

/-- Configuration for `:::details`. -/
structure DetailsConfig where
  /-- The clickable teaser shown when the block is collapsed. Defaults to
  `"Details"` when omitted. -/
  summary : Option String
deriving Repr

section
variable [Monad m] [MonadError m]

def DetailsConfig.parse : ArgParse m DetailsConfig :=
  DetailsConfig.mk <$> ((some <$> .positional `summary .string) <|> pure none)

instance : FromArgs DetailsConfig m := ⟨DetailsConfig.parse⟩

end

block_extension Block.details (summary : String) where
  data := Json.str summary
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ data contents => do
      let summary :=
        match data with
        | .str s => s
        | _ => ""
      let body : Verso.Output.Html ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      return {{
        <details class="sf-details">
          <summary>{{summary}}</summary>
          {{body}}
        </details>
      }}
  toTeX :=
    open Verso.Output.TeX in
    some fun _ goB _ data contents => do
      let summary :=
        match data with
        | .str s => s
        | _ => ""
      let body : Verso.Output.TeX ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      pure <| .seq #[.raw s!"\\textit\{{summary}.} ", body]
  extraCss := [
r##"
details.sf-details {
  margin: 1em 0;
  padding: 0.4em 0.8em;
  border-left: 3px solid var(--sf-rule, #ccc);
  background: rgba(0, 0, 0, 0.015);
  border-radius: 2px;
}
details.sf-details > summary {
  cursor: pointer;
  font-family: var(--verso-structure-font-family);
  font-weight: 600;
  color: var(--sf-heading, inherit);
  list-style: none;
}
details.sf-details > summary::-webkit-details-marker { display: none; }
details.sf-details > summary::before {
  content: "▸ ";
  display: inline-block;
  width: 1em;
  transition: transform 120ms ease-in-out;
}
details.sf-details[open] > summary::before {
  content: "▾ ";
}
details.sf-details[open] {
  background: rgba(0, 0, 0, 0.03);
}
"##
  ]

/-- A `:::details "…"` directive wraps its contents in a collapsible
disclosure block. The summary string is optional (defaults to `"Details"`). -/
@[directive]
def details : DirectiveExpanderOf DetailsConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other
        (SFLMeta.Block.details $(quote (cfg.summary.getD "Details")))
        #[$blocks,*])

end SFLMeta
