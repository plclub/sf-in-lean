prelude
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

import LF.Poly
import LF.CustomTactics

open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "Tactics: More Basic Tactics" =>
%%%
htmlSplit := .never
file := "Tactics"
%%%

:::instructors
This material is a bit too much to cover in detail in
one 80-minute lecture. 90-100 minutes is more reasonable, but that
may still involve going a bit fast at the end.
:::

:::dev
This chapter could maybe use one or two more WORKINCLASS tags...

BCP 25: General comment: All the previous chapters have
felt pretty smooth. This one suddenly feels like we're throwing a
huge amount of information at them, with little scaffolding -- just
a bunch of miscellaneous tactics and examples.  Wish it flowed
better, somehow.
:::

:::full
This chapter introduces several additional proof strategies
and tactics that allow us to begin proving more interesting
properties of functional programs.

We will see:
* how to use auxiliary lemmas in both "forward-" and "backward-style" proofs;
* how to reason about data constructors — in particular,
how to use the fact that they are injective and disjoint;
* how to strengthen an induction hypothesis, and when such strengthening is required; and
* more details on how to reason by case analysis.
:::

:::dev "One An (meluge)"
added these to use Lean's Nat. `open Nat (add_comm add_assoc add_zero add_succ mul_one succ_sub_succ)`
YL: I prefer not to `open Nat` because it's not a good practice in idiomatic Lean code:
some of them are `protected` (accessible via `simp`, not supposed to be opened);
and in Mathlib-style code they should have meant the generalized algebraic version.
Although we don't have Mathlib here, IMO it would be better to make `Nat.` prefix explicit.
:::

# The `apply` Tactic

:::full
We often encounter situations where the goal to be proved is
_exactly_ the same as some hypothesis in the context or some
previously proved lemma.
:::

The `apply` tactic is useful when some hypothesis or an
earlier lemma exactly matches the goal:

```lean
example (n m : Nat) : n = m → n = m := by
  intro h
  /- Here, we could finish with `rw [h]` as we
    have done several times before. Or we can finish
    by using `apply`: -/
  apply h
```

:::full
The `apply` tactic also works with _conditional_ hypotheses
and lemmas: if the statement being applied is an implication, then
the premises of this implication will be added to the list of
subgoals needing to be proved.
:::

:::slidebreak
:::

`apply` also works with _conditional_ hypotheses:

```lean
example (n m o p : Nat) :
    n = m →
    (n = m → [n, o] = [m, p]) →
    [n, o] = [m, p] := by
  intro hnm h
  apply h
  apply hnm
```

:::full
Typically, when we use `apply h`, the statement `h` will
begin with a `forall` that introduces some _universally quantified variables_.

When Lean matches the current goal against the conclusion of `h`,
it will try to find appropriate values for these variables.

For example, when we do `apply h₂` in the following proof, the
universal variable `q` in `h₂` gets instantiated with `n`, and
`r` gets instantiated with `m` — Lean tries to
unify `[q]` with `[n]` and `[r]` with `[m]` respectively.
:::

:::slidebreak
:::

:::terse
Observe how Lean picks appropriate values for the
`forall`-quantified variables of the hypothesis:
:::

```lean
example (n m : Nat) :
    (n, n) = (m, m) →
    (∀ (q r : Nat), (q, q) = (r, r) → [q] = [r]) →
    [n] = [m] := by
  intro h₁ h₂
  apply h₂
  apply h₁
```

:::exercise (rating := 1) (name := "intro_apply_ex")
Complete the following proof using only `intro` and `apply`.

```lean
example (p : Nat) :
    (∀ n, even n = true → even (n + 1) = false) →
    (∀ n, even n = false → odd n = true) →
    even p = true →
    odd (p + 1) = true := by
  solution!
    intro h₁ h₂ h₃
    apply h₂
    apply h₁
    apply h₃
```
:::

:::full
To use the `apply` tactic, the (conclusion of the) fact
being applied must match the goal exactly (perhaps after
simplification) — for example, `apply` will not work if the left
and right sides of the equality are swapped.
:::

:::terse
The goal must match the hypothesis _exactly_ for `apply` to work:
:::

```lean
example (n m : Nat) :
    n = m →
    m = n := by
  intro h
  /- Here we cannot use `apply` directly...
     but we can use the `symm` tactic, which switches the left
    and right sides of an equality in the goal. -/
  symm
  apply h
```

::::full

:::exercise (rating := 2) (name := "apply_exercise1")
You can use `apply` with previously defined theorems, not
just hypotheses in the context.
Use a previously-defined theorem about `rev` from the `Poly` chapter.
Use that theorem as part of your (relatively short) solution to this
exercise. You do not need `induction`.

```lean
theorem rev_exercise1 {α} (l l' : List α) :
    l = l'.rev →
    l' = l.rev := by
  solution!
    intro h
    rw [h]
    symm
    apply rev_involutive
```
:::

:::grade
GRADE_THEOREM 2: rev_exercise1
:::

:::exercise (rating := 1) (name := "apply_rewrite")
Briefly explain the difference between the tactics `apply` and `rw`.
What are the situations where both can usefully be applied?
:::

:::solution
The `rw` tactic is used to apply a known equality (a
hypothesis from the context or a previously proved lemma) to
modify the goal, replacing all occurrences of one side by the
other.

The `apply` tactic uses a known implication (a hypothesis from the
context, a previously proved lemma, or a constructor) to replace a
goal that matches the conclusion of the implication with subgoals,
one for each premise of the implication.

If the known fact is itself an equality (with no premises), then
either tactic can be used.  (We will see below that each tactic
can also be used to modify a hypothesis rather than the goal.)
:::

::::

## Supplying arguments to `apply`

The following example uses two rewrites in a row to get from `[a, b]` to `[e, f]`.

```lean
example (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro h₁ h₂
  rw [h₁, h₂]
```

:::slidebreak
:::

Since this is a common pattern, we might like to pull it out as a
lemma that records, once and for all, the fact that equality is transitive.

```lean
theorem trans_eq {α : Type} (x y z : α) :
    x = y → y = z → x = z := by
  intro h₁ h₂
  rw [h₁, h₂]
```

Lean already provides exactly this theorem as {name}`Eq.trans`.
In Lean's version, the arguments corresponding to `x`, `y`, and `z` are _implicit_,
since they can usually be inferred from the equality hypotheses and the goal.

```lean
#check Eq.trans
```

Now let's use our {name}`trans_eq` to prove the example above.

:::full

If we simply write `apply trans_eq`, Lean can infer some arguments from the goal,
but not the intermediate list or the hypotheses needed for the lemma's premises.
If you inspect the proof state after `apply`, you will see that Lean has created three goals:

1. `[a, b] = ?y`
2. `?y = [e, f]`
3. `List Nat`

Recall that {name}`trans_eq` has five arguments. From the goal, Lean can infer the endpoints `x` and `z`,
namely `[a, b]` and `[e, f]`. But it still needs an intermediate term `y`.

We want to prove `[a, b] = [e, f]`. By transitivity, it's enough to prove `[a, b] = ?y` and `?y = [e, f]`,
for some intermidiate list `?y`.
Here `?y` is a _metavariable_: a place holder for a value Lean has not yet determined.
Before we provide the hypothesis `h₂`, Lean doesn't know that this intermediate list shoud be `[c, d]`.

One way to resolve this is to supply all the arguments and hypotheses explicity.
:::

:::terse
Doing `apply trans_eq` doesn't finish the proof, but.`apply trans_eq [a, b] [c, d] [e, f] h₁ h₂` does.
:::

```lean
example (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro h₁ h₂
  apply trans_eq [a, b] [c, d] [e, f] h₁ h₂
```

In the previous example, we had to specify the `x` and `z` arguments
to `trans_eq` before we could supply `[c, d]` for `y` or `h₁` and `h₂` for
the premises. However, we just said that Lean was able to infer these arguments, so it's
a bit redundant (and wordy) for us to do that. Thankfully,
Lean allows us to use `_`s for positional arguments that it is able to infer.

```lean
example (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro h₁ h₂
  apply trans_eq _ _ _ h₁ h₂
```

If we know the name of the argument we are supplying (in this case `y`), we can
just name it directly, and avoid typing any `_`s.

```lean
example (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro h₁ h₂
  apply trans_eq (y := [c, d])
  apply h₁
  apply h₂
```

:::full
Like any other kind of software, there are conventions and best practices associated
with writing proofs in Lean. One of these conventions concerns the use of the `exact`
tactic. When fully applying another theorem like in the previous examples,
it is considered good practice to use the `exact` tactic instead of `apply`. This signals to
a reader of the proof that the proof is "exactly" an instance of another lemma, and that nothing
of particular interest is happening here. This achieves a similar goal as when
a mathematician says that one result is "just" an instance of another.
:::

:::terse
By convention, we use `exact` for situations when we can completely finish the proof
with a single application.
:::

```lean
example (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro h₁ h₂
  exact trans_eq _ _ _ h₁ h₂
```

As an aside, Lean's {name}`Eq.trans` theorem uses implicit arguments, so we can write the proof even more directly:

:::dev
YL: IMO this is worth mentioning.
:::

```lean
example (a b c d e f : Nat) :
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro h₁ h₂
  -- apply Eq.trans h₁ h₂ would also close the goal
  exact Eq.trans h₁ h₂
```

:::dev
YL: Removed `calc` examples as we've discussed it a lot in UsingLean
:::


# The `injection` and `contradiction` Tactics

:::full
Recall the definition of natural numbers:

```lean -show
namespace Temp
```

```lean
inductive Nat where
  | zero
  | succ (n : Nat)
```

```lean -show
end Temp
```

It is obvious from this definition that every number has one of
two forms: either it is the constructor `0` or it is built by
applying the constructor `.succ` to another number.  But there is more
here than meets the eye: implicit in the definition are two
additional facts:

- The constructor `.succ` is _injective_ (or _one-to-one_).
  That is, if `n + 1 = m + 1`, it must also be that `n = m`.

- The constructors `0` and `.succ` are _disjoint_.  That is, `0` is not
  equal to `n + 1` for any `n`.

Similar principles apply to every inductively defined type:
all constructors are injective, and the values built from distinct
constructors are never equal. For lists, the `cons` constructor
is injective and the empty list `nil` is different from every
non-empty list. For booleans, `true` and `false` are different.
(Since `true` and `false` take no arguments, their injectivity is
neither here nor there.)  And so on.
:::

:::terse
The constructors of inductive types are _injective_ (or _one-to-one_) and _disjoint_.

E.g., for {name}`Nat`:

- if `n + 1 = m + 1` then it must be that `n = m`
- `0` is not equal to `n + 1` for any `n`

:::

## Injectivity

We can _prove_ the injectivity of `succ` by using the `pred` function:

```lean
example (n m : Nat) :
    n + 1 = m + 1 →
    n = m := by
  intros h₁
  have h₂ : n = Nat.pred (n + 1) := by rfl
  rw [h₂, h₁]
  rfl
```

:::dev
YL: I'm not sure whether to keep this example.
To me it's more like showing that `pred` is a left inverse of `succ`, not `succ` is injective.
BTW it's also interesting to see an actual example of `rw [...]` not equivalent to `rewrite [...]; rfl`,
as the former does `rfl` with transparency mode `.reducible`, while the latter does `rfl` with `.default`.
:::

:::full
Lean's `have` tactic, used above, adds the given hypothesis
to the context, but it first requires you to prove the hypothesis
as a new goal.

This technique for injectivity can be generalized to any constructor
by writing the equivalent of `pred` — i.e., writing a function that
"undoes" one application of the constructor.

As a convenient alternative, Lean provides a tactic called
`injection` that allows us to exploit the injectivity of any
constructor.  Here is an alternate proof of the above theorem
using `injection`:
:::

:::terse
As a convenience, the `injection` tactic allows us to
exploit injectivity of any constructor (not just `succ`).
:::

:::full
By writing `injection h with hmn` at this point, we are asking Lean
to generate all equations that it can infer from `h` using the
injectivity of constructors (in the present example, the equation
`n = m`). This equation is added as a hypothesis (called `hmn` in this case) into the context.
Because this equation is exactly our goal,
in this case the `injection` tactic is able to automatically close the goal.


`with ...` can be omitted if the generated equations are not used.
:::

```lean
example (n m : Nat) :
    n + 1 = m + 1 →
    n = m := by
  intro h
  injection h with hmn
```

:::slidebreak
:::


Here's a more interesting example that shows how `injection` can
derive multiple equations at once.

:::instructors
Good in-class example.
:::

```lean
example (n m o : Nat) :
    [n, m] = [o, o] →
    n = m := by
  intro h
  injection h with h₁ h₂
  injection h₂ with h₃
  rw [h₁, h₃]
```

There is also a related tactic, `injections`, that applies the `injection`
tactic to all your hypotheses at once, as many times in a row as it can. Using this
tactic can avoid needing to repeatedly use `injection` on lists, for example:

:::instructors
Good in-class example.
:::

```lean
example (n m o : Nat) :
    [n, m] = [o, o] →
    n = m := by
  intro h
  injections h₁ _ h₃
  rw [h₁, h₃]
```

::::full

:::exercise (rating := 3) (name := "injection_ex3")
```lean
theorem injection_ex3 {α : Type} (x y z : α) (l j : List α) :
    x :: y :: l = z :: j →
    j = z :: l →
    x = y := by
  solution!
    intro h₁ h₂
    injections hxz hyl_j
    have hyl_zl : y :: l = z :: l := by rw [hyl_j, h₂]
    injections hyz
    rw [hxz, hyz]
```
:::

:::grade
GRADE_THEOREM 3: injection_ex3
:::

:::exercise (rating := 3) (name := "injection_ex3'")
```lean
example {α : Type} (x y z w : α) (l j : List α) :
    x :: y :: l = w :: z :: j →
    x :: l = z :: [] →
    x = y := by
  solution!
    intro eq1 eq2
    injections _ _ hyz _ hxz _
    rw [hxz, hyz]
```
:::

::::

:::dev
YL: Should we mention `cases` handles injectivity? I personally never use `injection` though...
Also I'm not sure if I arranged exercise correctly.
:::

## Disjointness

So much for injectivity of constructors. What about disjointness?

:::full
 The principle of disjointness says that two terms beginning
with different constructors (like `0` and `succ`, or `true` and `false`)
can never be equal. This means that, any time we find ourselves
in a context where we've _assumed_ that two such terms are equal,
we are justified in concluding anything we want, since the
assumption is nonsensical.
:::

:::terse
Two terms beginning with different constructors (like `0` and `succ`, or `true` and `false`) can never be equal!
:::

:::slidebreak
:::

The `contradiction` tactic, which we've already seen for handling
cases where we have assumed `False`, also embodies this principle:
if we have a a hypothesis involving an equality between different
constructors (e.g., `false = true`), `contradiction` solves the current
goal immediately. Some examples:

```lean
example (n m : Nat) :
    false = true →
    n = m := by
  intro contra
  contradiction

example (n : Nat) :
    n + 1 = 0 →
    2 + 2 = 5 := by
  intro contra
  contradiction
```

These examples are instances of a logical principle known as the
_principle of explosion_, which asserts that a contradictory
hypothesis entails anything (even manifestly false things!).

::::full
If you find the principle of explosion confusing, remember
that these proofs are _not_ showing that the conclusion of the
statement holds. Rather, they are showing that, _if_ the
nonsensical situation described by the premise did somehow hold,
_then_ the nonsensical conclusion would too -- because we'd be
living in an inconsistent universe where every statement is true.

We'll explore the principle of explosion in more detail in the
next chapter.

:::exercise (rating := 1) (name := "disjoint_ex3")
```lean
theorem disjoint_ex3 {α : Type} (x y z : α) (l : List α) :
    x :: y :: l = [] →
    x = z := by
  solution!
    intros h
    contradiction
```
:::

:::grade
GRADE_THEOREM 1: disjoint_ex3
:::

::::

:::slidebreak
:::


:::dev
YL: `beq_0_l` removed.
:::


::::terse
:::ignore

YL: Commented quizzes out for now

```
-- QUIZ
/- Recall our rgb and color types:

inductive RGB : Type where
  | red | green | blue
inductive Color : Type where |
  black | white | primary (p: RGB)

Suppose Lean's proof state looks like
    x : RGB
    y : RGB
    h : .primary x = .primary y

    ⊢ y = x
    and we apply the tactic `injection h with hxy`.  What will happen?

    (1) "No goals."

    (2) The tactic fails.

    (3) Hypothesis `h` becomes `hxy : x = y`.

    (4) None of the above.
-/

-- HIDE
theorem quiz0 (x y : RGB) :
    Color.primary x = Color.primary y →
    x = y := by
  intro h
  injection h
-- /HIDE
-- /QUIZ

-- QUIZ
/- Suppose Lean's proof state looks like
      x : Bool
      y : Bool
      h : !x = !y

      ⊢ y = x
    and we apply the tactic `injection h with hxy`  What will happen?

    (A) "No more goals."

    (B) The tactic fails.

    (C) Hypothesis `h` becomes `hxy : x = y`.

    (D) None of the above.
-/
-- HIDE
/-- error: Tactic `injection` failed: equality of constructor applications expected

x y : Bool
h : (!decide (x = !y)) = true
⊢ y = x -/
#guard_msgs in
theorem quiz1 (x y : Bool) : !x = !y → y = x := by
  intro h
  injection h with hxy
-- /HIDE
-- /QUIZ

-- QUIZ
/- Now suppose Lean's proof state looks like

        x : Nat
        y : Nat
        h : x + 1 = y + 1

        ⊢ y = x

    and we apply the tactic `injection h with hxy`.  What will happen?

    (A) "No more goals."

    (B) The tactic fails.

    (C) Hypothesis `h` becomes `hxy : x = y`.

    (D) None of the above.
-/
-- HIDE
theorem quiz2 (x y : Nat) : x + 1 = y + 1 → y = x := by
  intro h
  injection h with hxy
  symm
  assumption
-- /HIDE
-- /QUIZ

-- QUIZ
/- Finally, suppose Lean's proof state looks like

         x : Nat
         y : Nat
         h : 1 + x = 1 + y

         ⊢ y = x

    and we apply the tactic `injection h with hxy`.  What will happen?

    (A) "No more goals."

    (B) The tactic fails.

    (C) Hypothesis `h` becomes `hxy : x = y`.

    (D) None of the above.
-/
-- HIDE
/-- error: Tactic `injection` failed: equality of constructor applications expected

x y : Nat
h : 1 + x = 1 + y
⊢ y = x -/
#guard_msgs in
theorem quiz3 (x y : Nat) : 1 + x = 1 + y → y = x := by
  intro h
  injection h with hxy
-- /HIDE
-- /QUIZ
-- /TERSE
```
:::

::::

:::slidebreak
:::

The injectivity of constructors allows us to reason that
`∀ (n m : Nat), n + 1 = m + 1 → n = m`.  The converse of this
implication is an instance of a more general fact about both
constructors and functions, which we will find useful below:

```lean
example {α β : Type} (f : α → β) (x y : α) :
    x = y → f x = f y := by
  intro h
  rw [h]

example (n m : Nat) :
    n = m → n + 1 = m + 1 := by
  intro h
  rw [h]
```

:::full
Indeed, there is also a tactic named `congr` that can
prove such theorems directly.  Given a goal of the form
`f a1 ... an = g b1 ... bn`, the tactic `congr` will produce subgoals
of the form `f = g`, `a1 = b1`, ..., `an = bn`. At the same time,
any of these subgoals that are simple enough (e.g., immediately
provable by `rfl`) will be automatically discharged.
:::

:::terse
Lean also provides `congr` as a tactic.
:::

```lean
example (n m : Nat) :
    n = m → n + 1 = m + 1 := by
  intro h
  congr
```
