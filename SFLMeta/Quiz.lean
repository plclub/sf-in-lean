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
      return {{
        <div class="sf-quiz">
          <div class="sf-quiz-label">"Quiz"</div>
          {{body}}
        </div>
      }}
  toTeX :=
    open Verso.Output.TeX in
    some fun _ goB _ _ contents => do
      let body : Verso.Output.TeX ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      pure <| .seq #[.raw "\\paragraph{Quiz.} ", body]
  extraCss := [
r##"
div.sf-quiz {
  margin: 1em 0;
  padding: 0.4em 0.8em;
  border-left: 3px solid var(--sf-rule, #ccc);
  background: rgba(0, 0, 0, 0.02);
  border-radius: 2px;
}
div.sf-quiz > .sf-quiz-label {
  font-family: var(--verso-structure-font-family);
  font-weight: 600;
  margin-bottom: 0.4em;
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
as a revealable answer.

Superseded by `Block.quizSolution` (the uniform, *shown* quiz-answer block); the
`:::answer` directive is kept only so any lingering source still elaborates. -/
block_extension Block.answer where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX := none

/-- A `:::answer` directive holds the answer to a quiz (the `-- HIDE` region
inside a `-- QUIZ`).  A noop; superseded by `:::quizSolution`. -/
@[directive]
def answer : DirectiveExpanderOf Unit
  | args, contents => noopDirectiveFor ``Block.answer args contents

/-! ## `:::quizSolution`

The uniform quiz-answer block.  Unlike the old `:::answer`/`:::instructors`
quiz-answer conventions (which dropped the answer from every build), a
`:::quizSolution` is *shown in all build products*: its body is elaborated and
kept through traversal, so it reaches the HTML book and every generated `.lean`
file.  In HTML it renders as a native disclosure widget — a "Show solution"
button that reveals the answer when clicked — so the answer is present but not
spoiling the quiz.  The generated `.lean` files carry it as a labelled comment. -/

block_extension Block.quizSolution where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ _ contents => do
      let body : Verso.Output.Html ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      return {{
        <details class="sf-quiz-solution">
          <summary>"Show solution"</summary>
          <div class="sf-quiz-solution-body">{{body}}</div>
        </details>
      }}
  toTeX :=
    open Verso.Output.TeX in
    some fun _ goB _ _ contents => do
      let body : Verso.Output.TeX ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      pure <| .seq #[.raw "\\paragraph{Solution.} ", body]
  extraCss := [
r##"
details.sf-quiz-solution {
  margin: 0.6em 0;
}
details.sf-quiz-solution > summary {
  cursor: pointer;
  display: inline-block;
  font-family: var(--verso-structure-font-family);
  font-weight: 600;
  font-size: 0.85em;
  padding: 0.2em 0.7em;
  border: 1px solid var(--sf-rule, #ccc);
  border-radius: 4px;
  background: rgba(0, 0, 0, 0.04);
  user-select: none;
}
details.sf-quiz-solution[open] > summary {
  margin-bottom: 0.5em;
}
details.sf-quiz-solution > .sf-quiz-solution-body {
  padding: 0.2em 0.8em;
  border-left: 3px solid var(--sf-rule, #ccc);
}
"##
  ]

/-- A `:::quizSolution` directive holds the answer to a quiz.  It is a real
container (its body is elaborated and kept in every build): shown as a
click-to-reveal disclosure in HTML and as a labelled comment in the generated
`.lean` files. -/
@[directive]
def quizSolution : DirectiveExpanderOf Unit
  | _, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (SFLMeta.Block.quizSolution) #[$blocks,*])

end SFLMeta
