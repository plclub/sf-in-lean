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
  /-- Difficulty level, written as a bare identifier: `Advanced` marks an
  advanced exercise (SF's `A` flag).  Absent means a standard exercise. -/
  level : Option String
  /-- Whether the exercise is graded manually rather than automatically (SF's
  `M` flag).  Written `(manual := true)`. -/
  manual : Bool
deriving Repr

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

/-- An argument value written as a bare identifier (`Advanced`), yielding its
text.  Shared with `:::dev`'s urgency argument (see `SFLMeta.Comment`). -/
def ValDesc.identText : ValDesc m String where
  description := doc!"an identifier"
  signature := CanMatch.Ident
  get
    | .name x => Pure.pure x.getId.toString
    | other => throwError "Expected identifier, got {toMessageData other}"

/-- Argument parser for `ExerciseConfig`.  `rating`/`name` are required; the
`level` (`Advanced`) and `manual` (`true`/`false`) designations are optional. -/
def ExerciseConfig.parse : ArgParse m ExerciseConfig :=
  ExerciseConfig.mk
    <$> .named `rating .nat false
    <*> .named `name .string false
    <*> .named `level ValDesc.identText true
    <*> namedD `manual .bool false

instance : FromArgs ExerciseConfig m := ⟨ExerciseConfig.parse⟩

end

/-- The parenthetical designation string for an exercise's level/grading flags,
e.g. `" (Advanced)"`, `" (Advanced, manually graded)"`, `" (manually graded)"`,
or `""` when the exercise is standard and auto-graded.  Shared by the HTML, TeX,
and `.lean` renderings so they mark advanced/manual exercises identically. -/
def exerciseDesignation (level : Option String) (manual : Bool) : String :=
  let parts := (if level == some "Advanced" then ["Advanced"] else []) ++
               (if manual then ["manually graded"] else [])
  match parts with
  | [] => ""
  | _  => " (" ++ String.intercalate ", " parts ++ ")"

/-! `Block.exercise` carries the exercise rating and name; HTML output wraps the
contents in a styled box; TeX output emits a paragraph header; the saver emits
a `### Exercise (rating⭐): name` module-doc heading before the contents. -/

/-- Decode a `Block.exercise` payload `(rating, name, level, manual)`, tolerating
the older 2-element `(rating, name)` form. -/
def decodeExerciseData (data : Json) : Nat × String × Option String × Bool :=
  match data with
  | .arr #[.num jr, .str n, lvl, .bool man] =>
    let level := match lvl with | .str s => some s | _ => none
    (jr.toFloat.toUInt32.toNat, n, level, man)
  | .arr #[.num jr, .str n] => (jr.toFloat.toUInt32.toNat, n, none, false)
  | _ => (0, "", none, false)

block_extension Block.exercise (rating : Nat) (name : String)
    (level : Option String) (manual : Bool) where
  data := Json.arr #[.num (.fromNat rating), .str name, toJson level, .bool manual]
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ data contents => do
      let (rating, name, level, manual) := decodeExerciseData data
      let stars := String.ofList (List.replicate rating '★')
      let desig := exerciseDesignation level manual
      let levelHtml : Verso.Output.Html :=
        if desig.isEmpty then .empty
        else {{ <span class="exercise-level">{{desig}}</span> }}
      let body : Verso.Output.Html ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      return {{
        <div class={{s!"exercise stars-{rating}"}}>
          <div class="exercise-header">
            <span class="exercise-label">"Exercise"</span>
            <span class="exercise-stars">{{stars}}</span>
            <span class="exercise-name">{{s!"({name})"}}</span>
            {{levelHtml}}
          </div>
          {{body}}
        </div>
      }}
  toTeX :=
    open Verso.Output.TeX in
    some fun _ goB _ data contents => do
      let (rating, name, level, manual) := decodeExerciseData data
      let desig := exerciseDesignation level manual
      let body : Verso.Output.TeX ← contents.foldlM (init := .empty) fun acc b =>
        return acc ++ (← goB b)
      pure <| .seq #[
        .raw s!"\\paragraph\{Exercise ({rating} stars): {name}{desig}.}",
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
.exercise-header .exercise-name,
.exercise-header .exercise-level {
  font-family: inherit;
}
.exercise-stars { margin: 0 0.5em; color: #c08000; }
.exercise-name  {
  font-family: var(--verso-code-font-family);
  font-style: italic;
  color: #555;
}
.exercise-level {
  margin-left: 0.5em;
  font-weight: 700;
  color: #a00;
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
        (SFLMeta.Block.exercise $(quote cfg.rating) $(quote cfg.name)
          $(quote cfg.level) $(quote cfg.manual))
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
