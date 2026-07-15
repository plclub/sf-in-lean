import VersoManual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output Verso.Output.Html

namespace SFLMeta

/-!
## Displayed code (`display`)

`Block.display` sets a block of material off from the surrounding prose — the way
a textbook sets off a displayed line — but does **no** typesetting: it simply
shows the material verbatim, as (non-elaborated) Lean code.  It is deliberately
dumb: the body is never parsed or elaborated, so deliberately ill-formed snippets
("the following definition is rejected…"), shell transcripts, and the informal
`[[ … ]]` equations of the paper proofs all render without complaint.

This is the interim home for the coqdoc `[[ … ]]` displays: `to_verso` emits a
`` ```display `` block for each one, so the content is preserved and marked as a
display (rather than left as an anonymous code fence), and a later editing pass
can promote the genuinely-mathematical ones to `` ```displaymath `` for real
typesetting.

    ```display
    n + (m + p) = (n + m) + p.
    ```
-/
block_extension Block.display (source : String) where
  data := Json.str source
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some fun _ _ _ data _ => do
      match data with
      | .str s => pure {{ <div class="sf-display"><pre><code>{{s}}</code></pre></div> }}
      | _ =>
        Verso.reportError "display: malformed data"
        pure .empty
  toTeX :=
    open Verso.Output.TeX in
    some fun _ _ _ data _ => do
      match data with
      | .str s => pure <| .seq #[.raw "\\begin{verbatim}\n", .raw s, .raw "\n\\end{verbatim}\n"]
      | _ => pure .empty
  extraCss := [
r##"
.sf-display {
  margin: 1em 0;
}
.sf-display pre {
  margin: 0;
  padding: 0.5em 0.8em;
  overflow-x: auto;
  background: var(--verso-code-background, rgba(0, 0, 0, 0.03));
  border-left: 3px solid var(--sf-rule, #ccc);
  border-radius: 2px;
}
.sf-display pre code {
  font-family: var(--verso-code-font-family, monospace);
  white-space: pre;
}
"##
  ]

/-- A ` ```display ` code block: shows its body verbatim as (non-elaborated,
non-highlighted) Lean code, set off as a display.  The body is stored as-is and
never elaborated, so any text — including deliberately ill-formed code — is
safe. -/
@[code_block]
def display : CodeBlockExpanderOf Unit
  | (), str => do
    let src := str.getString
    `(Verso.Doc.Block.other (SFLMeta.Block.display $(quote src))
        #[Verso.Doc.Block.code $(quote src)])

/-!
## Displayed math

`Block.displaymath` renders a "displayed equation" the way a textbook does: the
content is set off from the surrounding prose, centered on its own line(s), and
typeset as mathematics (via Verso's bundled KaTeX) rather than as a monospace
code block.

This is the *real-math* counterpart to `Block.display` above: where `display`
shows the coqdoc `[[ … ]]` material verbatim as Lean code (the safe interim that
`to_verso` emits), `displaymath` typesets a genuine displayed equation — lines
like

    n + (m + p) = (n + m) + p.

In coqdoc those render as verbatim `<pre>` blocks (monospace code); `displaymath`
is how a later editing pass turns the genuinely-mathematical ones into real
textbook math.

Authoring convention (a fenced code block, parallel to ` ```lean ` / ` ```bnf `):

    ```displaymath
    n + (m + p) = (n + m) + p.
    ```

Each non-blank line of the body becomes one centered display equation.  The body
is treated as **LaTeX** — for the plain arithmetic identities that pervade the
informal proofs (`0 + (m + p) = (0 + m) + p.`, `S (n' + (m + p)) = S ((n' + m) +
p),`) the source text is already valid LaTeX and renders directly; where an
author wants finer control (roman constructors, `\text{and}` between two columns,
aligned `=`) they write the corresponding LaTeX.

Verso also accepts single inline displays natively as `` $$`…` `` inside prose;
the `displaymath` block is the preferred form for the multi-line, set-off
displays.  `to_verso` does not emit `displaymath` automatically — promoting a
`` ```display `` to `` ```displaymath `` is a manual step.
-/
block_extension Block.displaymath where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ _ contents => do
      let body : Html ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      return {{ <div class="sf-displaymath">{{body}}</div> }}
  toTeX :=
    open Verso.Output.TeX in
    some fun _ goB _ _ contents => do
      contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
  extraCss := [
r##"
.sf-displaymath {
  margin: 1em 0;
}
/* KaTeX already centers `displayMode` output and gives it vertical margin; keep
   our own rhythm tight so successive displays in a multi-line proof don't drift
   apart, and make sure a wide equation scrolls rather than overflowing prose. */
.sf-displaymath .katex-display {
  margin: 0.35em 0;
  overflow-x: auto;
  overflow-y: hidden;
}
"##
  ]

/-- A ` ```displaymath ` code block: each non-blank line of the body is set as a
centered display equation (Verso `MathMode.display`, rendered by KaTeX).  Blank
lines separate nothing structurally — they are simply dropped — so the author can
group related lines visually in the source. -/
@[code_block]
def displaymath : CodeBlockExpanderOf Unit
  | (), str => do
    let src := str.getString
    let lines : Array String :=
      (src.splitOn "\n").toArray.filterMap fun l =>
        let t := l.trimAscii.toString
        if t.isEmpty then none else some t
    if lines.isEmpty then
      throwErrorAt str "displaymath: empty body"
    let paras ← lines.mapM fun l =>
      `(Verso.Doc.Block.para #[Verso.Doc.Inline.math Verso.Doc.MathMode.display $(quote l)])
    `(Verso.Doc.Block.other SFLMeta.Block.displaymath #[$paras,*])

end SFLMeta
