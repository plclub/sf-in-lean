import VersoManual
import VersoManual.InlineLean
import Illuminate
import SFLMeta.Bnf
import SFLMeta.Ignore
import SFLMeta.Save
import SFLMeta.Comment
import SFLMeta.Exercise
import SFLMeta.Grade
import SFLMeta.Hide
import SFLMeta.Instructors
import SFLMeta.SlideBreak
import SFLMeta.Solution
import SFLMeta.Terse

import LF.IndProp

open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "Automation: More Automation" =>
%%%
htmlSplit := .never
file := "Automation"
%%%

::::full
Up to now, we've used the manual part of Lean's tactic
facilities.  In this chapter, we'll learn more about some of
Lean's powerful automation features, including
tactic combinators like `try` and `repeat`, decision procedures like `lia`,
and automatic simplification using `simp`.
Using these features together with Lean's metaprogramming facilities will enable us to make
some of our proofs startlingly short!  Used properly, they can
also make proofs more maintainable and robust to changes in
underlying definitions.

Our motivating example will be the following proof, repeated with
just a few small changes from the `IndProp` chapter.  We will
simplify this proof in several stages.
::::

::::terse
Consider the proof below. Notice all the repetition and near-repetition...
::::

:::dev
@dsainati1: come up with new motivating example
:::

# The `lia` Tactic

::::full
The `lia` tactic implements a decision procedure for integer linear
arithmetic, a subset of propositional logic and arithmetic.

If the goal is a universally quantified formula made out of

  - numeric constants, addition (`+` and `succ`), subtraction (`-` and `pred`)
    and multiplication by constants (this is what makes it Presburger arithmetic),

  - equality (`=` and `≠`) and ordering (`≤` and `<`), and

  - the logical connectives `∧`, `∨`, `¬`, and `→`,

then invoking `lia` will either solve the goal or fail, meaning
that the goal is actually false.  (If the goal is _not_ of this
form, `lia` will fail.)
::::

```lean
example : forall (m n o p : Nat),
    m + n ≤ n + o ∧ o + 3 = p + 3 ->
    m ≤ p := by
  lia

example : forall (m n : Nat),
    m + n = n + m := by
  lia

example : forall (m n p : Nat),
    m + (n + p) = m + n + p := by
  lia
```

# Tactic Combinators

:::dev
@dsainati1 - this example comes directly from the Rocq textbook, but it's a bit weird
(there and here!) becuase we could also just solve this with `lia` directly
:::

::::full
In `Induction`, we saw how to use the `<;>` combinator in order to apply the same
tactic to every subgoal in a proof. As a reminder, consider this example,
where splitting on `n` leaves two subgoals that are discharged identically:
::::

::::terse
Recall the `<;>` combinator...
::::

```lean
example (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n with
  | zero   => lia
  | succ k => lia

example (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n <;> lia -- run `cases n`, then `lia` on each subgoal
```

::::full
This `<;>` is not the only such combinator that Lean has to offer, however.
In general, _combinators_ allow us to build tactics out of smaller ones, letting us
discharge many similar subgoals at once. Getting used to them takes a
little energy, but it lets us scale up to more complex definitions and
more interesting properties without drowning in boring, repetitive detail.
::::

## The `try` combinator

::::full
The first such combinator we'll discuss is `try`. If `t` is a tactic,
then `try t` is a tactic that is just like `t`
except that, if `t` fails, `try t` _successfully_ does nothing at all
(rather than failing).
::::

::::terse
The `try` combinator allows tactics to fail.
::::

```lean
example (P : Prop) (hp : P) : P := by
  try rfl -- `rfl` would fail here, but `try` swallows the failure...
  exact hp -- ...so we can still finish some other way.

example : 1 = 1 := by
  try rfl -- here `try rfl` just does `rfl`
```

::::full
There is not much reason to use `try` in completely manual proofs like
these, but it is very useful together with the `<;>` combinator.

... FILL IN ....

Here, we can use the ... tactic to close some of these goals, but not all of them. So,
a more compact way to write this proof would be:
::::

::::terse
The `try` and `<;>` combinators used together allow you to use a tactic to some,
but not all, goals...
::::

::::dev
@dsainati1: Come up with sample proof using `<;>` and try together
::::

::::full
However, be careful when using `try` with tactics that cannot fail; in some circumstances,
this can leave you with unprovable goals! Recall the proof of `Perm3_symm` from `IndProp`

:::dev
TODO (@dsainati1) - example of using `try` and `<;>` to make your proof state unrecoverable
:::

... FILL IN ....
::::

## The `repeat` combinator

The  `repeat` combinator takes another tactic or parenthesized sequence of tactics
and keeps applying it until it fails.

Here is an example proving that `10` is in a long list using `repeat`:

```lean
example : 10 ∈ [1,2,3,4,5,6,7,8,9,10] := by
  repeat rw [List.mem_cons]
  -- repeats `right` until `left; rfl` succeeds
  repeat (try left; rfl); right
  left; rfl
```

::::full
The tactic `repeat t` never fails: if the tactic `t` doesn't apply
to the original goal, then repeat _succeeds_ without changing the
goal at all (i.e., it repeats zero times).

```lean
example : 10 ∈ [1,2,3,4,5,6,7,8,9,10] := by
  repeat rw [List.mem_cons]
  -- This is a no-op
  repeat (left; rfl)
  repeat (try left; rfl); right
  left; rfl
```
::::

::::full
The tactic `repeat t` does not have any upper bound on the
number of times it applies `t`.  If `t` is a tactic that _always_
succeeds (and makes progress), then `repeat t` will loop
forever.
::::

::::terse
`repeat` can loop forever
::::

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : forall (m n : Nat),
  m + n = n + m := by
  intros m n
  /- Uncomment the next line to see the infinite loop occur.  You will
     then need to recomment it make Lean listen to you again. -/
  -- repeat rewrite [Nat.add_comm]
  sorry
```

::::full
Wait -- did we just write an infinite loop in Lean?!?!

Sort of.

While evaluation in Lean's term language is guaranteed to
terminate, _tactic_ evaluation is not.  This does not affect Lean's
logical consistency, however, since the job of `repeat` and other
tactics is to guide Lean in constructing proofs; if the
construction process diverges (i.e., it does not terminate), this
simply means that we have failed to construct a proof at all, not
that we have constructed a bad proof.
::::

# The `simp` Tactic
