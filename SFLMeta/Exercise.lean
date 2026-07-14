import VersoManual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output Verso.Output.Html
open Verso.Doc.Html

namespace SFLMeta

/-! ## Exercise directive -/

/-- Author-facing configuration for `:::exercise`. -/
structure ExerciseConfig where
  /-- Difficulty rating, conventionally a star count from 1 to 5. -/
  rating : Nat
  /-- A short identifier for the exercise, used in headings and cross-references. -/
  name : String
deriving Repr

section
variable [Monad m] [MonadError m]

/-- Argument parser for `ExerciseConfig`. -/
def ExerciseConfig.parse : ArgParse m ExerciseConfig :=
  ExerciseConfig.mk <$> .named `rating .nat false <*> .named `name .string false

instance : FromArgs ExerciseConfig m := ⟨ExerciseConfig.parse⟩

end

/-! `Block.exercise` carries the exercise rating and name; HTML output wraps the
contents in a styled box; TeX output emits a paragraph header; the saver emits
a `### Exercise (rating⭐): name` module-doc heading before the contents. -/

block_extension Block.exercise (rating : Nat) (name : String) where
  data := Json.arr #[.num (.fromNat rating), .str name]
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ data contents => do
      let (rating, name) :=
        match data with
        | .arr #[.num jr, .str n] => (jr.toFloat.toUInt32.toNat, n)
        | _ => (0, "")
      let stars := String.ofList (List.replicate rating '★')
      let body : Verso.Output.Html ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      return {{
        <div class={{s!"exercise stars-{rating}"}}>
          <div class="exercise-header">
            <span class="exercise-label">"Exercise"</span>
            <span class="exercise-stars">{{stars}}</span>
            <span class="exercise-name">{{s!"({name})"}}</span>
          </div>
          {{body}}
        </div>
      }}
  toTeX :=
    open Verso.Output.TeX in
    some fun _ goB _ data contents => do
      let (rating, name) :=
        match data with
        | .arr #[.num jr, .str n] => (jr.toFloat.toUInt32.toNat, n)
        | _ => (0, "")
      let body : Verso.Output.TeX ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      pure <| .seq #[
        .raw s!"\\paragraph\{Exercise ({rating} stars): {name}.}",
        body
      ]
  extraCss := [
r##"
.exercise {
  margin: 1.2em 0;
  padding: 0.6em 1em;
  border-left: 3px solid #a00;
  background: #fdf8ee;
}
.exercise-header {
  font-family: var(--verso-structure-font-family);
  font-weight: 600;
  margin-bottom: 0.5em;
}
.exercise-header .exercise-label,
.exercise-header .exercise-stars,
.exercise-header .exercise-name {
  font-family: inherit;
}
.exercise-stars { margin: 0 0.5em; color: #c08000; }
.exercise-name  {
  font-family: var(--verso-code-font-family);
  font-style: italic;
  color: #555;
}
"##
  ]

/-- A `:::exercise(rating := N, name := "foo")` directive wraps content as an
exercise with the given metadata. -/
@[directive]
def exercise : DirectiveExpanderOf ExerciseConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other
        (SFLMeta.Block.exercise $(quote cfg.rating) $(quote cfg.name))
        #[$blocks,*])

/-! ## `solution!` marker macros and source-range registry

A `solution!(…)` wraps a term that should be elaborated normally in the teacher
build, but eliminated by the saver when emitting the student-side `.lean` file
(the entire `solution!(…)` invocation is replaced with `sorry`). The same
`solution!(…)` form works for tactic sequences inside a `by` block.

The macros are *elaborators* rather than plain `macro_rules`: as a side effect
of running, each one registers the source range of its invocation (the whole
`solution!(…)` and just the `solution!` keyword atom) in an `IO.Ref`. The
project-local `lean` code-block expander snapshots this ref around its call to
the upstream Lean elaborator and uses the resulting ranges to compute the
teacher and student source variants. -/

structure Replacement where
  range : Syntax.Range
  replacement : String
deriving Repr, Inhabited

structure SolutionEditRaw where
  /-- The ranges that represent the tokens of the `solution!` form. -/
  edits : Array Replacement
  nonempty : edits.size > 0
deriving Repr

instance : Inhabited SolutionEditRaw where
  default.edits := #[default]
  default.nonempty := by simp

initialize studentEditRef : IO.Ref (Array SolutionEditRaw) ← IO.mkRef #[]
initialize teacherEditRef : IO.Ref (Array SolutionEditRaw) ← IO.mkRef #[]
/-- Edits producing the *terse* (lecture) source variant.  `solution!` records
the same span-to-`sorry` edit here as for the student variant (exercises are
stubbed on slides too); `workinclass!` records its edit *only* here (the proof
is shown in the student and solutions builds but worked live in lecture). -/
initialize terseEditRef : IO.Ref (Array SolutionEditRaw) ← IO.mkRef #[]

private def recordStudentEdit (edits : Array (Syntax × String)) : IO Unit := do
    let ranges := edits.filterMap fun (stx, replacement) => do
      let range ← stx.getRange?
      pure { range, replacement}
    if h : ranges.size > 0 then
      studentEditRef.modify
        (·.push ⟨ranges, h⟩)

private def recordTeacherEdit (edits : Array (Syntax × String)) : IO Unit := do
    let ranges := edits.filterMap fun (stx, replacement) => do
      let range ← stx.getRange?
      pure { range, replacement}
    if h : ranges.size > 0 then
      teacherEditRef.modify
        (·.push ⟨ranges, h⟩)

private def recordTerseEdit (edits : Array (Syntax × String)) : IO Unit := do
    let ranges := edits.filterMap fun (stx, replacement) => do
      let range ← stx.getRange?
      pure { range, replacement}
    if h : ranges.size > 0 then
      terseEditRef.modify
        (·.push ⟨ranges, h⟩)

syntax (name := solutionTerm) "solution!" "(" term ")" : term

@[term_elab solutionTerm]
def elabSolutionTerm : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(solution!%$tk1 ( $e )) =>
    recordStudentEdit #[(stx, "sorry")]
    recordTerseEdit #[(stx, "sorry")]
    recordTeacherEdit #[(tk1, "")]
    Term.elabTerm e expectedType?
  | _ => throwUnsupportedSyntax

open Tactic

syntax (name := solutionTac) withPosition("solution!" tacticSeqIndentGt) : tactic

@[tactic solutionTac]
def evalSolutionTac : Tactic := fun stx => do
  match stx with
  | `(tactic| solution!%$tk $t:tacticSeq ) =>
    recordStudentEdit #[(stx, "sorry")]
    recordTerseEdit #[(stx, "sorry")]
    recordTeacherEdit #[(tk, "all_goals")]
    evalTactic t
  | _ => throwUnsupportedSyntax

/-! ## `workinclass!` marker

The inverse of `solution!` along the build axis: a `workinclass!` tactic block
is elaborated normally and *shown* in both the student and solutions builds,
but replaced by `sorry` in the terse (lecture) build, where the instructor
works the proof out live. -/

syntax (name := workinclassTac) withPosition("workinclass!" tacticSeqIndentGt) : tactic

@[tactic workinclassTac]
def evalWorkinclassTac : Tactic := fun stx => do
  match stx with
  | `(tactic| workinclass!%$tk $t:tacticSeq ) =>
    recordTerseEdit #[(stx, "sorry")]
    recordStudentEdit #[(tk, "all_goals")]
    recordTeacherEdit #[(tk, "all_goals")]
    evalTactic t
  | _ => throwUnsupportedSyntax
