# Progress tracker

https://github.com/orgs/plclub/projects/2/views/1

# Commentary

General notes on translation specifics go here.

## Differences from Rocq

### Aborting

Suggestion from Roger: Use unnamed `example`s closed with `sorry`
to replace functionality of (named) `Abort`ed lemmas.

### Induction/inversion and generalization

DHS: We teach students to think about inversion like inverting an inference rule
("I know H, what must have been true for H to be true"),
but it's not intuitive that that process of inverting the rule should require the hypothesis to be general. 
Maybe the way we were teaching inversion before was overly specific to Rocq?

Concrete example: Inversion on `n ≤ 0` requires `generalizing e : 0 = m`,
since one of the constructors of `≤` has a `succ` argument on the RHS,
which Lean can't unify with `0`.

### Notation and simplification

JC: If we use typeclass instances to implement notation for a definition,
`dsimp` doesn't resolve the instances down to that definition,
e.g. `dsimp [add]` doesn't work on `n + (m + 1)`,
`dsimp [app]` doesn't work on `(h :: t) ++ l`.
While Rocq's `simpl` and Lean's `simp` both do this,
`simp` is also too powerful at times.
Instead, we explicitly rewrite by equalities such as
`n + (m + 1) = n + m + 1` or `(h :: t) ++ l = h :: t ++ l`.

## Style guide

* In comments, use Markdown as needed (they will render in VSCode)
  * Section, subsection, etc. headers begin with `#`, `##`, etc.
  * Unnumbered lists use `*`, not `-`
* Prefer `cases h; case ...` and `induction h; case ...`
  over `cases h with | ...` and `induction h with | ...`
* Prefer named cases over `.` goal selector
  when the goal names are meaningful
* Select cases without indentation or `.` after `cases`:
  ```lean
  cases b
  case true  => ...
  case false => ...
  ```
* Use unnamed examples with `#guard_msgs` where `sorry`s appear:
  ```lean
  /-- warning: declaration uses `sorry` -/
  #guard_msgs in
  example : ... := sorry
  ```
* Indent continued type declarations one further than proofs:
  ```lean
  theorem myTheorem : ∀ {A : Type} (this : Bool) (is : Nat) (a : A),
      really → long → Type :=
    intro really long
    exact A
  ```

### Comments

#### Line comments

* Instructor notes, e.g. `-- BCP:`
* Section dividers and headings, i.e. `-- #`
* Directives, e.g. `-- FULL` and `-- /FULL`
  * Full list of directives:
    `FULL`, `TERSE`, `ADMITTED`, `ADMIT_DEF`, `GRADE_THEOREM`, `[]`,
    `HIDE`, `HIDEFROMADVANCED`, `HIDEFROMHTML`

#### Block comments

* Student-facing prose
* Declaration doc comments `/-- -/` attached to top-level declarations as need
  (they will appear on hover in VSCode)
* General doc comments `/-! -/` currently unused

## Tactics

From FPiL: "The grind tactic is very powerful, customizable, and extensible; due to this power and flexibility,
its output when it fails to prove a theorem contains a lot of information that can help trained Lean users diagnose the reason for the failure.
This can be overwhelming in the beginning, so this chapter uses only decide and simp."

Tactics to consider introducing:
`rcases`, `obtain`, `show`, `assumption`, `rename_i`, `revert`, `constructor`, `split`, `subst`, `suffices`, `specialize`

### Inventory

* `Basics.lean`: `rfl`, `intro`, `rewrite`, `rw`, `cases`, `dsimp`, `exact`, `contradiction`, `<;>` (to move), `all_goals` (to remove)
* `Induction.lean`: `induction`, `have`, `calc`, `generalize`
* `Lists.lean`: `unfold`
* `Poly.lean`: N/A
* `Tactics.lean`: `apply`, `symm`, `injection`, `injections`, `congr`

### `rewrite` vs `rw`

Roger: It seems that the `rw` tactic might be a bit to strong for what we want to teach.
`rewrite [h]` rewrites with a hypothesis, whereas `rw [h]` does something like `rewrite [h]; rfl`.
This leads to many proofs, in which the students' only tools are `rfl` and rewriting, not using `rfl` in the induction case at all.
Furthermore, the way stepping through the proof goes is a bit confusing: the goal disappears when you step over the final`]`.
Essentially, `rw` is kind of like `now rewrite` in Rocq. Good for people who know what they're doing, hard to read for those who don't.
I'll give a soft proposal that we use `rewrite` rather than `rw`.

Daniel: I am mostly in agreement with Roger's point above, especially for early chapters where we want to be as explicit
as possible about what's happening in proofs. However I think after the first few chapters we can probably relax this restriction?

JC: Because the `rewrite [...]; rfl` occurs so often immediately,
I've opted to use `rewrite` the first time,
then introduce `rw` and mostly just use `rw` onwards.

## Course content

### `Basics.lean`

JC: There should be some instruction on interaction with the IDE, namely:
* how to read the proof state
* clicking immediately after a tactic will show you what it changed
* clicking after each `h` in `rw [h₁, h₂, ...]` will show you what was rewritten
* hovering over a tactic will provide documentation on how to use it
* hovering over a definition will give its type
* hovering over a Unicode character will tell you how to type it
* Ctrl-clicking on a definition will take you to the definition location

### `Induction.lean`

JC: A lot of the proofs on the naturals rely on how operations on naturals were defined in `Basics.lean`,
but in the stdlib they're slightly different
(e.g. `sub` is defined via `pred` rather than directly by recursion),
and the notations all go through typeclasses,
which makes the proofs a lot less direct
(e.g. the existing `0 + n` proof refers to `Nat.add_succ`).
We should do one of the following:
1.  Not use `+`, `-`, `*` notation and instead use `add`, `sub`, `mul` directly; or
2.  Override stdlib notation with ones pointing to the definitions in `Basics.lean`.

HG: 1. is a very reasonable way to go about this if we’re attached to arithmetic being the way we teach induction.
My primary concern is that operators and type classes are already so confusing
that adding another meaning of `+` is liable to throw someone way off.
Is there another context we can teach induction in that also doesn’t require a ton of background?

JC: `Basics.lean` now overrides the typeclasses for `-`, `*`, and `^`,
but not `+`, since that one is pervasive throughout the stdlib and causes problems;
I think this works okay and isn't too confusing.

JC: If we continue doing arithmetic proofs,
this is a good place to introduce equational reasoning via `calc`.

### `Lists.lean`

DHS: Weird that this file contains the first `inductive` definition students have seen up to this point,
but that definition is also actually a `structure`. Probably need to restructure this.

DHS: Unsure if it's a good idea to actually use the built-in `List` definition here, since it's polymorphic,
and we aren't introducing this idea until a later chapter. This also means we don't get the chance
to show students how to actually produce an inductive definition if we're relying on the built-in ones.
DHS: We probably need to actually take time to explain what a `@[simp]` annotation on a lemma
means before we introduce it, and I don't think this chapter is the right place to do it anyway.
This is probably a better fit for `Auto.lean`.

DHS: Claude picked a bad definition for `nonzeroes`:
```
  match l with
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
```
which makes many of the later proofs hard to do without the full automation of `simp`. 
I changed it, but it's worth pointing this out.

### `Poly.lean`

DHS: None of the comments at the start of the chapter motivating the polymorphic
definition of lists make sense with the change to use `List Nat` in the previous chapter.

DHS: Using the built-in definition of `List.reverse` is dramatically more complicated
than implementing our own reverse function, since it is implemented in terms of an auxiliary
function.

DHS: The associativity of `++` in Lean is different than Rocq. In Rocq the definition
of `app_assoc` is `l ++ m ++ n = (l ++ m) ++ n`, but in Lean it's
`l ++ m ++ n = l ++ (m ++ n)`.
