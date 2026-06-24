This file has been used for temporary / ongoing discussions among translators. 
It should probably be deleted.

Normative conventions — live in [STYLEGUIDE.md](STYLEGUIDE.md) now. 

# Potential rules for collaboration

**To do**: take inspiration from Jimmy Wales' [Seven Rules of Trust](https://en.wikipedia.org/wiki/The_Seven_Rules_of_Trust), which underpin Wikipedia's distributed development.

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

## Tactics

From FPiL: "The grind tactic is very powerful, customizable, and extensible; due to this power and flexibility,
its output when it fails to prove a theorem contains a lot of information that can help trained Lean users diagnose the reason for the failure.
This can be overwhelming in the beginning, so this chapter uses only decide and simp."

Tactics to consider introducing:
`rcases`, `show`, `rename_i`, `revert`, `split`, `subst`, `suffices`

(The per-chapter tactic-introduction inventory now lives as a table in
[STYLEGUIDE.md](STYLEGUIDE.md), derived from the current sources.)

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

KK: The `Baz` "how many elements does this type have?" exercise (the last exercise
in the chapter) is a *manual* exercise, and that's a poor fit: a student who
doesn't realize an inductive definition needs a base case will simply fail it and
only see why in the grader comment — and it's easy to wrongly think you have the
right answer and move on without thinking. Better to either add a short section
that explains this directly, or add a hint like the `one_true_baz` / `count_trues`
scaffold ("try to write a value of type `Baz` for which the lemma holds"). Worth
reworking for easier grading.

### `Poly.lean`

DHS: None of the comments at the start of the chapter motivating the polymorphic
definition of lists make sense with the change to use `List Nat` in the previous chapter.

DHS: Using the built-in definition of `List.reverse` is dramatically more complicated
than implementing our own reverse function, since it is implemented in terms of an auxiliary
function.

DHS: The associativity of `++` in Lean is different than Rocq. In Rocq the definition
of `app_assoc` is `l ++ m ++ n = (l ++ m) ++ n`, but in Lean it's
`l ++ m ++ n = l ++ (m ++ n)`.

### `Tactics.lean`

DHS: There is a section here on unfolding definitions that should probably move earlier,
to `Basics` or `Induction`, once those chapters are rewritten to not use arithmetic. This will
also require changing the examples.

### `Logic.lean`

JC: Classical axioms are more pervasive in Lean and the section from Rocq needs to be rewritten
to acknowledge this and teach idiomatic style.

CH: There's several style things to mention here like `classical` vs. `open Classical`.


### (Another note about simplification)

1. While writing library code, it's fine and necessary to unfold and simplify through definitions. When using that code, the idiomatic way is not to "peek through the interface".


## Book Structure

The Structure of SFL will differ from Rocq SF in that the LF/PLF books will be
divided into three books: Logical Foundations, something about Hoare Logic and imperative PL, 
and something about types and functional PL. The contents will also be somewhat different:

* Volume 1 will go until the Automation chapter; the Imp chapter will be moved to the Hoare Logic volume.
  * This will also mean that the automation material in `Imp` should be moved to the Volume 1 automation chapter, which has the benefit of separating the concerns of learning about automation from learning about operational semantics. 
  * The automation chapter will focus on `simp` and other tactics of similar power level to `lia` or `auto` (i.e., `tauto`, `omega`, etc), but not `grind` or `aesop` or `try`, which probably make sense to delay until a future volume about AI use for Lean. The `RegExp` example which was previously a large chunk of the `IndProp` chapter will be moved from that chapter to the automation chapter, and retooled to have a smoother on-ramp but also focus on teaching automation and how to use `simp`. 
* Volume 2 will be the Type Systems and Lambda Calculus book
* Volume 3 will be the Imperative Languages and Hoare Logic book
  * Moving this to after the Type Systems book should make a smoother transition to later material about specification and imperative proofs, rather than having it come before the Type Systems work. 
