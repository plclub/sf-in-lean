import VersoManual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output Verso.Output.Html
open Verso.Doc.Html

namespace SFLMeta

/-! ## Exercise directive -/

/-- Author-facing configuration for `:::exercise`. -/
structure ExerciseConfig where
  /-- Difficulty rating, a star count from 1 to `maxExerciseRating`. -/
  rating : Nat
  /-- A short identifier for the exercise, used in headings and cross-references. -/
  name : String
  /-- Difficulty level, written as a bare identifier: `Advanced` marks an
  advanced exercise (SF's `A` flag).  Absent means a standard exercise. -/
  level : Option String
  /-- Whether the exercise is optional (SF's `?` flag).  Written as a bare
  identifier, `(optional := Yes)`; absent means `No`. -/
  optional : String
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

/-- The highest difficulty rating an exercise may carry.  SF rates exercises
from one star (easy) to five (hard); anything above that is a typo — most often
a `GRADE_THEOREM` point value copied into the rating slot — and the HTML
renderer would dutifully print that many stars. -/
def maxExerciseRating : Nat := 5

/-- The `rating` argument: a numeric literal between 1 and `maxExerciseRating`.
Verso's stock `ValDesc.nat` accepts any `Nat`, so the range is checked here. -/
def ValDesc.exerciseRating : ValDesc m Nat where
  description := doc!"a difficulty rating from 1 to 5"
  signature := CanMatch.Num
  get
    | .num n =>
      let r := n.getNat
      if r == 0 || r > maxExerciseRating then
        throwError "Exercise rating must be between 1 and {maxExerciseRating}, got {r}"
      else Pure.pure r
    | other => throwError "Expected a number, got {toMessageData other}"

/-- Canonicalize an exercise `optional` keyword, recognized case-insensitively:
`Yes` and `No` map to their canonical spelling and every other keyword yields
`none` (an error at parse time). -/
def canonExerciseOptional? (s : String) : Option String :=
  match s.toUpper with
  | "YES" => some "Yes"
  | "NO" => some "No"
  | _ => none

/-- The `optional` argument: a bare identifier, `Yes` or `No` (recognized in
any case), stored canonicalized.  Unlike `:::dev`'s urgency — a *positional*
argument whose `get`-time errors would be swallowed by the `<|>` that makes it
optional — `optional` is named, so validating here gives a precise error. -/
def ValDesc.exerciseOptional : ValDesc m String where
  description := doc!"`Yes` or `No`"
  signature := CanMatch.Ident
  get
    | .name x =>
      match canonExerciseOptional? x.getId.toString with
      | some s => Pure.pure s
      | none => throwError "Expected `Yes` or `No`, got `{x.getId}`"
    | other => throwError "Expected identifier, got {toMessageData other}"

/-- Argument parser for `ExerciseConfig`.  `rating` (1 to 5) and `name` are
required; the `level` (`Advanced`), `optional` (`Yes`/`No`, defaulting to `No`),
and `manual` (`true`/`false`) designations are optional. -/
def ExerciseConfig.parse : ArgParse m ExerciseConfig :=
  ExerciseConfig.mk
    <$> .named `rating ValDesc.exerciseRating false
    <*> .named `name .string false
    <*> .named `level ValDesc.identText true
    <*> namedD `optional ValDesc.exerciseOptional "No"
    <*> namedD `manual .bool false

instance : FromArgs ExerciseConfig m := ⟨ExerciseConfig.parse⟩

end

/-- The parenthetical designation string for an exercise's level/optional/
grading flags, e.g. `" (Advanced)"`, `" (Optional, manually graded)"`, or `""`
when the exercise is standard, required, and auto-graded.  Shared by the HTML,
TeX, and `.lean` renderings so they mark advanced/optional/manual exercises
identically. -/
def exerciseDesignation (level : Option String) (optional : String)
    (manual : Bool) : String :=
  let parts := (if level == some "Advanced" then ["Advanced"] else []) ++
               (if optional == "Yes" then ["Optional"] else []) ++
               (if manual then ["manually graded"] else [])
  match parts with
  | [] => ""
  | _  => " (" ++ String.intercalate ", " parts ++ ")"

/-! `Block.exercise` carries the exercise rating and name; HTML output wraps the
contents in a styled box; TeX output emits a paragraph header; the saver emits
a `### Exercise (rating⭐): name` module-doc heading before the contents. -/

/-- Decode a `Block.exercise` payload `(rating, name, level, optional, manual)`,
tolerating the older 4-element `(rating, name, level, manual)` and 2-element
`(rating, name)` forms.  The two longer forms are told apart by their fourth
element: the optional-flag string in the current form, the manual flag in the
older one. -/
def decodeExerciseData (data : Json) : Nat × String × Option String × String × Bool :=
  let level? (j : Json) : Option String := match j with | .str s => some s | _ => none
  match data with
  | .arr #[.num jr, .str n, lvl, .str opt, .bool man] =>
    (jr.toFloat.toUInt32.toNat, n, level? lvl, opt, man)
  | .arr #[.num jr, .str n, lvl, .bool man] =>
    (jr.toFloat.toUInt32.toNat, n, level? lvl, "No", man)
  | .arr #[.num jr, .str n] => (jr.toFloat.toUInt32.toNat, n, none, "No", false)
  | _ => (0, "", none, "No", false)

block_extension Block.exercise (rating : Nat) (name : String)
    (level : Option String) (optional : String) (manual : Bool) where
  data := Json.arr #[.num (.fromNat rating), .str name, toJson level, .str optional,
                     .bool manual]
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ data contents => do
      let (rating, name, level, optional, manual) := decodeExerciseData data
      let stars := String.ofList (List.replicate rating '★')
      let desig := exerciseDesignation level optional manual
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
      let (rating, name, level, optional, manual) := decodeExerciseData data
      let desig := exerciseDesignation level optional manual
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
          $(quote cfg.level) $(quote cfg.optional) $(quote cfg.manual))
        #[$blocks,*])

/-! ## `solution!` marker macros and source-range registry

A `solution!(…)` wraps a term that is elaborated normally in the solutions
build, but replaced by `sorry` in the student and terse source variants emitted
by the saver. The teacher/solutions variant removes only the `solution!` marker
while retaining and checking the wrapped term. The same `solution!(…)` form
works for tactic sequences inside a `by` block.

The macros are *elaborators* rather than plain `macro_rules`: as a side effect
of running, each one registers the source range of its invocation (the whole
`solution!(…)` and just the `solution!` keyword atom) in an `IO.Ref`. The
project-local `lean` code-block expander snapshots this ref around its call to
the upstream Lean elaborator and uses the resulting ranges to compute the
teacher/solutions, student, and terse source variants. -/

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

/-- Record student-variant edits given `Replacement`s directly (rather than
deriving their ranges from syntax).  Needed by `suggested!`, whose student edit
includes a zero-width insertion — a comment closer spliced at the body's end
position — for which there is no corresponding syntax node. -/
private def recordStudentRepls (repls : Array Replacement) : IO Unit := do
    if h : repls.size > 0 then
      studentEditRef.modify (·.push ⟨repls, h⟩)

/-- Drop up to `n` leading space characters from a list of characters. -/
private def dropLeadingSpaces : Nat → List Char → List Char
  | 0, cs => cs
  | _+1, [] => []
  | n+1, c :: cs => if c = ' ' then dropLeadingSpaces n cs else c :: cs

private def dedentLine (delta : Nat) (line : String) : String :=
  (dropLeadingSpaces delta line.toList).foldl String.push ""

private def leadingSpaceCount (line : String) : Nat :=
  (line.takeWhile (· = ' ')).toString.length

/-- The literal source text of tactic block `t`, for splicing in place of the
`solution!`/`workinclass!`/`suggested!` keyword at `tk` in a build where the
wrapped proof should be shown verbatim rather than stubbed. `t` is usually an
indented block starting on the line after `tk` (required by
`tacticSeqIndentGt`), one indent level deeper — in which case every line but
the first is dedented by that level, so the spliced text parses as a sibling
of whatever precedes/follows the marker in its enclosing tactic sequence
rather than staying orphaned at `t`'s original, deeper column. But `t` can
also be a single parenthesized tactic group starting right after `tk` on the
same line (the `solution!( … )` idiom borrowed from the term form); there the
column gap from `tk` reflects nothing about the body's own indentation, so
dedenting by it would flatten the group's internal structure. To cover both,
the dedent amount is derived from the body's own minimum indentation among
its continuation lines relative to `tk`'s column, not from `t`'s start
column — which comes out to the same "one indent level" in the first case,
and to zero (no rewrite) in the second, since a parenthesized group's own
lines are already indented well past `tk`. -/
private def dedentSpliceText (tk t : Syntax) : CoreM String := do
  let fileMap ← getFileMap
  match tk.getRange?, t.getRange? with
  | some tkR, some tR =>
    if h : tR.start.IsValid fileMap.source ∧ tR.stop.IsValid fileMap.source then
      let text := (fileMap.source.slice! ⟨tR.start, h.1⟩ ⟨tR.stop, h.2⟩).toString
      match text.splitOn "\n" with
      | [] => pure text
      | first :: rest =>
        let tkCol := (fileMap.toPosition tkR.start).column
        let nonBlank := rest.filter fun l => !l.trimAscii.toString.isEmpty
        let delta := match nonBlank with
          | [] => 0
          | l :: ls =>
            (ls.foldl (fun acc l => min acc (leadingSpaceCount l)) (leadingSpaceCount l)) - tkCol
        pure <| "\n".intercalate (first :: rest.map (dedentLine delta))
    else
      throwError "dedentSpliceText: invalid source range"
  | _, _ => throwError "dedentSpliceText: missing source range"

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
    recordTeacherEdit #[(stx, ← dedentSpliceText tk t.raw)]
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
    let shown ← dedentSpliceText tk t.raw
    recordStudentEdit #[(stx, shown)]
    recordTeacherEdit #[(stx, shown)]
    evalTactic t
  | _ => throwUnsupportedSyntax

/-! ## `suggested!` marker

The SF idiom `OPEN COMMENT WHEN HIDING SOLUTIONS` … `CLOSE COMMENT WHEN HIDING
SOLUTIONS`: an exercise whose "solution" is a suggested proof that the student
is invited to uncomment and adapt.  The body is a real proof, elaborated (and
so typechecked) in the teacher and terse builds and shown live there — exactly
as `solution!` treats the teacher build.  In the *student* build it is not
stubbed to a bare `sorry`; instead the goal is closed with `sorry` and the
suggested proof is preserved, commented out, for the student to uncomment. -/

syntax (name := suggestedTac) withPosition("suggested!" tacticSeqIndentGt) : tactic

@[tactic suggestedTac]
def evalSuggestedTac : Tactic := fun stx => do
  match stx with
  | `(tactic| suggested!%$tk $t:tacticSeq ) =>
    -- Teacher and terse builds keep the suggested proof live and shown.
    let shown ← dedentSpliceText tk t.raw
    recordTeacherEdit #[(stx, shown)]
    recordTerseEdit #[(stx, shown)]
    -- Student build: close the goal with `sorry`, then wrap the suggested proof
    -- in a block comment so it survives verbatim for the student to uncomment.
    -- The opening `/-` replaces the `suggested!` keyword (indented to its
    -- column); the closing `-/` is a zero-width insertion at the body's end.
    let fileMap ← getFileMap
    let indent := match tk.getPos? with
      | some p => String.ofList (List.replicate (fileMap.toPosition p).column ' ')
      | none   => ""
    match tk.getRange?, t.raw.getRange? with
    | some tkR, some tR =>
      recordStudentRepls #[
        { range := tkR,
          replacement := s!"sorry\n{indent}/- Suggested proof — uncomment and adapt:" },
        { range := { start := tR.stop, stop := tR.stop },
          replacement := s!"\n{indent}-/" }]
    | _, _ => recordStudentEdit #[(stx, "sorry")]
    evalTactic t
  | _ => throwUnsupportedSyntax
