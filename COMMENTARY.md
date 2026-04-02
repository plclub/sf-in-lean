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

## Stylistic conventions

### Induction/inversion

JC: We should avoid the `induction h with | ...` and `cases h with | ...` style
since they don't show the proof goals immediately after induction/inversion,
whereas `induction h` and `cases h` would let you teach
"and now you have a new goal to prove for each case" incrementally.
(There are also performance issues with very large `with`s
since the whole thing gets processed all at once instead of incrementally,
but that won't be a problem in this book.)

JC: We should also prefer e.g. `case zero => ...`, `case succ n => ...`
over the dot list syntax for clarity,
and only use the latter where the generated tag names aren't meaningful.

### Comments

| Style | Syntax   |
| ----- | -------- |
| Line  | `--`     |
| Block | `/- -/`  |
| Doc   | `/-- -/` |
| Doc   | `/-! -/` |

## Notable tactics

These might require a little more textual explanation.

* `split`
* `dsimp`, `whnf`
* `have` vs. `rcases` vs. `obtain`

From FPiL: "The grind tactic is very powerful, customizable, and extensible; due to this power and flexibility, its output when it fails to prove a theorem contains a lot of information that can help trained Lean users diagnose the reason for the failure. This can be overwhelming in the beginning, so this chapter uses only decide and simp."

Roger: It seems that the `rw`` tactic might be a bit to strong for what we want to teach.
`rewrite [h]` rewrites with a hypothesis, whereas `rw [h]` does something like `rewrite [h]; rfl`.
This leads to many proofs, in which the students' only tools are `rfl` and rewriting, not using `rfl` in the induction case at all.
Furthermore, the way stepping through the proof goes is a bit confusing: the goal disappears when you step over the final`]`.
Essentially, `rw` is kind of like `now rewrite` in Rocq. Good for people who know what they're doing, hard to read for those who don't.
I'll give a soft proposal that we use `rewrite` rather than `rw`.
