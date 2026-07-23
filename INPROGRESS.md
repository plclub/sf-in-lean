This file has been used for temporary / ongoing discussions among translators. 
It should probably be deleted once the following comments are checked.


## Differences from Rocq

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
