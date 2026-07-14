import VersoManual
import SFLMeta.Comment

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace SFLMeta

/-! ## `::::quiz` / `:::answer`

`::::quiz` wraps an in-text review question (marked `-- QUIZ … -- /QUIZ` in the
code-forward source).  Unlike `:::hide`, a quiz is *shown*: its body — the
question prose and any illustrative code — renders normally.  A quiz may contain
a `:::answer` giving the solution.

`:::answer` (the `-- HIDE` region inside a `-- QUIZ`) currently behaves like
`:::hide`: its body is dropped at elaboration and preserved verbatim in the
generated source.  Rendering the answer *sensibly* (revealable, syntax-
highlighted) is a deliberate later step; for now the structure is captured so the
translation round-trips and the answer text is not lost. -/

block_extension Block.quiz where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ _ contents => do
      let body : Verso.Output.Html ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      return {{ <div class="sf-quiz">{{body}}</div> }}
  toTeX :=
    open Verso.Output.TeX in
    some fun _ goB _ _ contents => do
      let body : Verso.Output.TeX ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      pure body
  extraCss := [
r##"
div.sf-quiz {
  margin: 1em 0;
  padding: 0.4em 0.8em;
  border-left: 3px solid var(--sf-rule, #ccc);
  background: rgba(0, 0, 0, 0.02);
  border-radius: 2px;
}
"##
  ]

/-- A `::::quiz` directive wraps an in-text review question; its contents render
normally (it is a container, not a noop). -/
@[directive]
def quiz : DirectiveExpanderOf Unit
  | _, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (SFLMeta.Block.quiz) #[$blocks,*])

/-! `Block.answer` is a noop for now (like `Block.hide`): the body is dropped at
elaboration and preserved verbatim in the source.  A later build will render it
as a revealable answer. -/
block_extension Block.answer where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX := none

/-- A `:::answer` directive holds the answer to a quiz (the `-- HIDE` region
inside a `-- QUIZ`).  Currently a noop; rendered sensibly in a later step. -/
@[directive]
def answer : DirectiveExpanderOf Unit
  | args, contents => noopDirectiveFor ``Block.answer args contents

end SFLMeta
