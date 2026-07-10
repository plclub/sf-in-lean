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



# Tactic Combinators

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
::::

::::dev
@dsainati1: Come up with sample proof using `<;>` and try together
::::


# The `simp` Tactic
