import SFLMeta

import LF.Poly
import LF.CustomTactics

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Tactics: More Basic Tactics" =>
%%%
tag := "Tactics"
htmlSplit := .never
file := some "Tactics"
%%%

:::dev "Daniel Sainati (dsainati1)"
\[BCP: Old comment -- might be out of date?\]
There is a section here on unfolding definitions that should probably move earlier,
to `Basics` or `Induction`, once those chapters are rewritten to not use arithmetic. This will
also require changing the examples.
:::

:::dev "Benjamin Pierce (bcpierce00)"
(Old and possibly out of date -- check!)
Many exercises in this chapter are
based on defining and proving properties about Nat.ble and BEq.eq, which are not
idiomatic in Lean. We should consider replacing these with a different set of exercises.
:::


:::instructors
This material is a bit too much to cover in detail in
one 80-minute lecture.  90-100 minutes is more reasonable, but that
may still involve going a bit fast at the end.
:::

:::dev BeforeNextRelease
This chapter could maybe use one or two more WORKINCLASS
tags...
:::

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2025)
General comment: All the previous chapters have
felt pretty smooth. This one suddenly feels like we're throwing a
huge amount of information at them, with little scaffolding -- just
a bunch of miscellaneous tactics and examples.  Wish it flowed
better, somehow.
:::

::::full
This chapter introduces several additional proof strategies
and tactics that allow us to begin proving more interesting
properties of functional programs.

We will see:
- how to use auxiliary lemmas in both "forward-" and
  "backward-style" proofs;
- how to reason about data constructors -- in particular, how to
  use the fact that they are injective and disjoint;
- how to strengthen an induction hypothesis, and when such
  strengthening is required; and
- more details on how to reason by case analysis.
::::

```importBlock
import LF.Poly
import LF.CustomTactics
```

# The `apply` Tactic

::::full
We often encounter situations where the goal to be proved is
_exactly_ the same as some hypothesis in the context or some
previously proved lemma.
::::

::::terse
The {tactic}`apply` tactic is useful when some hypothesis or an
earlier lemma exactly matches the goal:
::::

```lean
example (n m : Nat) (h : n = m) : n = m := by
  /- Here, we could finish with `rw [h]` as we
    have done several times before.  Or we can finish
    by using `apply`: -/
  apply h
```

::::full
The {tactic}`apply` tactic also works with hypotheses
and lemmas whose types are implementations.
If the conclusion of the implication matches the current goal,
its premises become new subgoals to be proved.
::::

:::slidebreak
:::

::::terse
{tactic}`apply` also works with hypotheses whose types are implications:
::::

```lean
example (n m o p : Nat) (hnm : n = m) (h : n = m → [n, o] = [m, p]) :
    [n, o] = [m, p] := by
  apply h
  apply hnm
```

::::full
When we use `apply h`, Lean tries to match the conclusion of the type
of `h` with the current goal. Here `h : n = m → [n, o] = [m, p]` has conclusion
`[n, o] = [m, p]`, which matches the current goal. Lean then replaces the goal
with the premise that is still need, `n = m`. Then we close the goal with `apply hnm`.

More generally, the type of a theorem or hypothesis used with {tactic}`apply` may have
universally quantified variables and premises. Lean tries to unify its conclusion with
the current goal to determine appropriate values for the quantified variables.
::::

:::slidebreak
:::

::::terse
Observe how Lean picks appropriate values for the
universally quantified variables of the hypothesis:
::::

```lean
example (n m : Nat) (h₁ : (n, n) = (m, m))
    (h₂ : ∀ (q r : Nat), (q, q) = (r, r) → [q] = [r]) :
    [n] = [m] := by
  apply h₂
  apply h₁
```

::::::full
:::::exercise (rating := 2) (name := "apply_exercise")
Complete the following proof using only {tactic}`apply`.

```lean
theorem apply_exercise (m : Nat)
    (h₁ : ∀ (n : Nat), n.even = true → (n + 1).even = false)
    (h₂ : ∀ (n : Nat), n.even = false → n.odd = true)
    (hEven : m.even = true) :
    (m + 1).odd = true := by
  solution!
    apply h₂
    apply h₁
    apply hEven
```
:::::

::::::

::::full
To use the {tactic}`apply` tactic, the (conclusion of the) fact
being applied must match the goal exactly (perhaps after
simplification) —bodies for example, {tactic}`apply` will not work if the left
and right sides of the equality are swapped.
::::

:::slidebreak
:::

::::terse
The goal must match the hypothesis _exactly_ for {tactic}`apply` to
work:
::::

```lean
example(n m : Nat) (h : n = m) : m = n := by
  -- Here we cannot use `apply` directly...
  /- ...but we can use the `symm` tactic, which switches the left
      and right sides of an equality in the goal. -/
  symm; apply h
```

::::::full
:::::exercise (rating := 2) (name := "apply_exercise1")
You can use {tactic}`apply` with previously defined theorems, not
just hypotheses in the context.  Use a
previously-defined theorem about `rev` from {ref "Poly"}[Poly].  Use
that theorem as part of your (relatively short) solution to this
exercise. You do not need {tactic}`induction`.

```lean
theorem rev_exercise1 {α : Type} (l l' : List α) (h : l = l'.rev) :
    l' = l.rev := by
  solution!
    rw [h]
    symm
    apply reverse_reverse
```

:::gradeTheorem 2 rev_exercise1
:::
:::::

:::::exercise (rating := 1) (name := "apply_rewrite") (manual := true)
Briefly explain the difference between the tactics {tactic}`apply` and
{tactic}`rw`.  What are the situations where both can usefully be
applied?

:::solution
The {tactic}`rw` tactic is used to apply a known *equality* (a
hypothesis from the context or a previously proved lemma) to
modify the goal, replacing all occurrences of one side by the
other.

The {tactic}`apply` tactic uses a known *implication* (a hypothesis from the
context, a previously proved lemma, or a constructor) to replace a
goal that matches the conclusion of the implication with subgoals,
one for each premise of the implication.

If the known fact is itself an equality (with no premises), then
either tactic can be used.  (We will see below that each tactic
can also be used to modify a hypothesis rather than the goal.)
:::
:::::

::::::

## Supplying arguments to {tactic}`apply`

The following silly example uses two rewrites in a row to
get from `[a, b]` to `[e, f]`.

```lean
example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  rw [h₁, h₂]
```

:::slidebreak
:::

Since this is a common pattern, we might like to pull it out as a
lemma that records, once and for all, the fact that equality is
_transitive_.

```lean
theorem trans_eq {α : Type} (x y z : α) :
    x = y → y = z → x = z := by
  intro h₁ h₂
  rw [h₁, h₂]
```

Lean already provides exactly this theorem as {name}`Eq.trans`:

```lean (name := eq_trans)
#check Eq.trans
```

```leanOutput eq_trans
Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c
```

In Lean's version, the arguments corresponding to `x`, `y`, and `z` are implicit,
since they can usually be inferred from the equality hypotheses and the goal.

Now let's use our {name}`trans_eq` to prove the example above.


::::full
If we simply write `apply trans_eq`, Lean can infer some arguments from the goal,
but not the intermediate list or the hypotheses needed for the lemma's premises.
If you inspect the proof state after {tactic}`apply`, you will see that Lean has created three goals:

1. `[a, b] = ?y`
2. `?y = [e, f]`
3. `List Nat`

Recall that {name}`trans_eq` has five arguments.
From the goal, Lean can infer the endpoints `x` and `z`,
namely `[a, b]` and `[e, f]`. But it still needs an intermediate term `y`.

We want to prove `[a, b] = [e, f]`.
By transitivity, it's enough to prove `[a, b] = ?y` and `?y = [e, f]`, for some intermidiate list `?y`.
Here `?y` is a _metavariable_: a place holder for a value Lean has not yet determined.
Before we provide the hypothesis `h₂`, Lean doesn't know that this intermediate list shoud be `[c, d]`.
::::

```lean +error (name := trans_err1)
example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  apply trans_eq
```

```leanOutput trans_err1
unsolved goals
case a
a b c d e f : Nat
h₁ : [a, b] = [c, d]
h₂ : [c, d] = [e, f]
⊢ [a, b] = ?y

case a
a b c d e f : Nat
h₁ : [a, b] = [c, d]
h₂ : [c, d] = [e, f]
⊢ ?y = [e, f]

case y
a b c d e f : Nat
h₁ : [a, b] = [c, d]
h₂ : [c, d] = [e, f]
⊢ List Nat
```

One way to resolve this is to supply all the arguments and hypotheses explicity:

```lean
example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  apply trans_eq [a, b] [c, d] [e, f] h₁ h₂
```

:::full
In the previous example, we had to specify the `x` and `z` arguments
to {name}`trans_eq` before we could supply `[c, d]` for `y` or `eq1` and `eq2` for
the premises. However, we just said that Lean was able to infer these arguments, so it's
a bit redundant (and wordy) for us to do it.
:::

Thankfully, Lean allows us to use `_`s for positional arguments that it can infer.

```lean
example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  apply trans_eq _ _ _ h₁ h₂
```
If we know the name of the argument we are supplying (in this case `y`), we can
just name it directly, and avoid typing any `_`s.

```lean
example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  apply trans_eq (y := [c, d])
  apply h₁
  apply h₂
```

::::full
Like any other kind of software, there are conventions and best practices associated
with writing proofs in Lean. One of these conventions concerns the use of the {tactic}`exact`
tactic. When fully applying another theorem like in the previous examples,
it is considered good practice to use the {tactic}`exact` tactic instead of {tactic}`apply`.This signals to
a reader of the proof that the proof is "exactly" an instance of another lemma, and that nothing
of particular interest is happening here. This achieves a similar goal as when
a mathematician says that one result is "just" an instance of another.
::::

::::terse
By convention, we use {tactic}`exact` for situations when we can completely finish the proof
with a single application.
::::

```lean
example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  exact trans_eq _ _ _ h₁ h₂
```

::::full
Recall the {tactic}`calc` we have learned in the {ref "UsingLean"}[UsingLean] chapter.
It works by chaining equalities together using transitivity,
serving the same purpose here as applying {name}`trans_eq`.
::::

::::terse
We can also use {tactic}`calc`.
::::

```lean
example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  calc
  [a, b] = [c, d] := by rw [h₁]
  [c, d] = [e, f] := by rw [h₂]
```

:::::exercise (rating := 3) (name := "trans_eq_exercise")
```lean
theorem trans_eq_exercise (n m o p : Nat)
    (h₁ : m = o.minusTwo)
    (h₂ : (n + p) = m) :
    (n + p) = o.minusTwo := by
  solution!
    calc n + p
    _ = m := by rw [h₂]
    _ = o.minusTwo := by rw [h₁]
```
:::::

# The {tactic}`injection` and {tactic}`contradiction` Tactics

::::full
Recall the definition of natural numbers:

```display
inductive Nat : Type :=
  | zero
  | succ (n : Nat)
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
constructors are never equal. For lists, the {name}`List.cons` constructor
is injective and the empty list {name}`List.nil` is different from every
non-empty list. For booleans, {name}`true` and {name}`false` are different.
(Since {name}`true` and {name}`false` take no arguments, their injectivity is
neither here nor there.)  And so on.
::::

::::terse
The constructors of inductive types are _injective_ (or _one-to-one_) and _disjoint_.

E.g., for {name}`Nat`:

- if `n + 1 = m + 1` then it must be that `n = m`
- `0` is not equal to `n + 1` for any `n`

::::

## Injectivity

We can _prove_ the injectivity of {name}`Nat.succ` by using the {name}`Nat.pred` function:

```lean
example (n m : Nat)
    (h : n + 1 = m + 1) :
    n = m := by
  have : n = Nat.pred (n + 1) := by rfl
  /- The hypothesis name defaults to `this` when unspecified. -/
  rewrite [this, h]
  rfl
```

::::full
This technique for injectivity can be generalized to any constructor
by writing the equivalent of `pred` — i.e., writing a function that
"undoes" one application of the constructor.

As a convenient alternative, Lean provides a tactic called
{tactic}`injection` that allows us to exploit the injectivity of any
constructor.  Here is an alternate proof of the above theorem
using {tactic}`injection`:
::::

::::terse
As a convenience, the {tactic}`injection` tactic allows us to
exploit injectivity of any constructor (not just {name}`Nat.succ`).
::::

```lean
example (n m : Nat)
    (h : n + 1 = m + 1) :
    n = m := by
  injection h with hmn
```

::::full
By writing `injection h with hmn` at this point, we are asking Lean
to generate all equations that it can infer from `h` using the
injectivity of constructors (in the present example, the equation
`n = m`). This equation is added as a hypothesis (called
`hmn` in this case) into the context. Because this equation is exactly our goal,
in this case the {tactic}`injection` tactic is able to automatically close the goal.
::::

`with ...` can be omitted if the generated equations are not used.

```lean
example (n m : Nat)
    (h : n + 1 = m + 1) :
    n = m := by
  injection h
```

:::slidebreak
:::

Here's a more interesting example that shows how {tactic}`injection` can
derive multiple equations at once.

```lean
example (n m o : Nat)
    (h : [n, m] = [o, o]) :
    n = m := by
  workinclass!
    injection h with h₁ h₂
    injection h₂ with h₃
    rw [h₁, h₃]
```

There is also a related tactic, {tactic}`injections`, that applies the {tactic}`injection`
tactic to all your hypotheses at once, as many times in a row as it can. Using this
tactic can avoid needing to repeatedly use {tactic}`injection` on lists. For example:

```lean
example (n m o : Nat)
    (h : [n, m] = [o, o]) :
    n = m := by
  workinclass!
    injections h₁ _ h₃
    rw [h₁, h₃]
```

:::::exercise (rating := 3) (name := "injection_ex3")
```lean
theorem injection_ex3 {α : Type} (x y z : α) (l j : List α)
    (h₁ : x :: y :: l = z :: j)
    (h₂ : j = z :: l) :
    x = y := by
  injections hxz hyl_j
  rw [h₂] at hyl_j
  injection hyl_j with hyz
  rw [hyz, hxz]
```

:::gradeTheorem 3 injection_ex3
:::
:::::

So much for injectivity of constructors.  What about disjointness?

::::full
 he principle of disjointness says that two terms beginning
with different constructors (like `0` and {name}`Nat.succ`, or {name}`true` and {name}`false`)
can never be equal. This means that, any time we find ourselves
in a context where we've _assumed_ that two such terms are equal,
we are justified in concluding anything we want, since the
assumption is nonsensical.
::::

::::terse
Two terms beginning with different constructors (like
like `0` and {name}`Nat.succ`, or {name}`true` and {name}`false`) can never be equal.
::::

:::slidebreak
:::

The {tactic}`contradiction` tactic, which we've already seen for handling
cases where we have assumed {name}`False`, also embodies this principle:
if we have a a hypothesis involving an equality between different
constructors (e.g., {lean}`false = true`), {tactic}`contradiction` solves the current
goal immediately.  Some examples:

```lean
example (n m : Nat)
    (h : false = true) :
    n = m := by
  contradiction

example (n : Nat)
    (h : n + 1 = 0) :
    2 + 2 = 5 := by
  contradiction
```

These examples are instances of a logical principle known as the
_principle of explosion_, which asserts that a contradictory
hypothesis entails anything (even manifestly false things!).

::::full
If you find the principle of explosion confusing, remember
that these proofs are _not_ simply showing that the conclusion of the
statement holds.  Rather, they are showing that, _if_ the
nonsensical situation described by the premise did somehow hold,
_then_ the nonsensical conclusion would hold too (because we'd be
living in an inconsistent universe where every statement is true).

We'll explore the principle of explosion in more detail in the
{ref "Logics"}[next chapter].
::::

:::::exercise (rating := 1) (name := "disjoint_ex3")
```lean
theorem disjoint_ex3 {α : Type} (x y z : α) (l : List α)
    (h : x :: y :: l = []) :
    x = z := by
  solution!
    contradiction
```

:::gradeTheorem 1 disjoint_ex3
:::
:::::

:::slidebreak
:::

## Quizzes

Recall our {name}`RGB` and {name}`Color` types:
```display
inductive RGB : Type where
  | red
  | green
  | blue

inductive Color : Type where
  | black
  | white
  | primary (p: RGB)
```

::::quiz
Suppose Lean's proof state looks like

```display
x : RGB
y : RGB
h : .primary x = .primary y
------------------------------
⊢ y = x
```

and we apply the tactic `injection h with hxy`.  What will happen?

(1) "No goals."

(2) The tactic fails.

(3) Hypothesis `h` becomes `hxy : x = y`.

(4) None of the above.

:::quizSolution

```lean
example (x y : RGB)
    (h : Color.primary x = Color.primary y) :
    x = y := by injection h
```

:::
::::

::::quiz
Suppose Lean's proof state looks like

```display
x : Bool
y : Bool
h : !x = !y
--------------
⊢ y = x
```

and we apply the tactic `injection h with hxy`.  What will happen?

(A) "No more goals."

(B) The tactic fails.

(C) Hypothesis `h` becomes `hxy : x = y`.

(D) None of the above.

:::quizSolution

```lean +error (name := qz2)
example (x y : Bool) (h : !x = !y) : y = x := by
  injection h with hxy
```

```leanOutput qz2
Tactic `injection` failed: equality of constructor applications expected

x y : Bool
h : (!decide (x = !y)) = true
⊢ y = x
```

:::
::::

::::quiz
Now suppose Lean's proof state looks like

```display
x : Nat
y : Nat
h : x + 1 = y + 1
-------------------
⊢ y = x
```

and we apply the tactic `injection h with hxy`.  What will happen?

(A) "No more goals."

(B) The tactic fails.

(C) Hypothesis `h` becomes `hxy : x = y`.

(D) None of the above.

:::quizSolution
```lean
example (x y : Nat) (h : x + 1 = y + 1) : y = x := by
  injection h with hxy
  symm
  assumption
```
:::
::::

::::quiz
Finally, suppose Lean's proof state looks like

```display
x : Nat
y : Nat
h : 1 + x = 1 + y
-------------------
⊢ y = x
```

and we apply the tactic `injection h with hxy`.  What will happen?

(A) "No more goals."

(B) The tactic fails.

(C) Hypothesis `h` becomes `hxy : x = y`.

(D) None of the above.

:::quizSolution

```lean +error (name := qz4)
theorem quiz3 (x y : Nat) (h : 1 + x = 1 + y) : y = x := by
  injection h with hxy
```

```leanOutput qz4
Tactic `injection` failed: equality of constructor applications expected

x y : Nat
h : 1 + x = 1 + y
⊢ y = x
```
:::
::::

:::slidebreak
:::

The injectivity of constructors allows us to reason that
{lean}`∀ (n m : Nat), n + 1 = m + 1 → n = m`.  The converse of this
implication is an instance of a more general fact about both
constructors and functions:

```lean
example {α β : Type} (f : α → β) (x y : α)
    (h : x = y) : f x = f y := by
  rw [h]

example (n m : Nat) (h : n = m) :
    n + 1 = m + 1 := by
  rw [h]
```

::::full
Indeed, there is also a tactic named {tactic}`congr` that can
prove such goals directly.  Given a goal of the form
`f a₁ ... aₙ = g b₁ ... bₙ`, the tactic {tactic}`congr` will produce subgoals
of the form `f = g`, `a₁ = b₁`, ..., `aₙ = bₙ`. At the same time,
any of these subgoals that are simple enough (e.g., immediately
provable by {tactic}`rfl`) will be automatically discharged.
::::

:::terse
Lean also provides {tactic}`congr` as a tactic.
:::

```lean
example (n m : Nat) (h : n = m) :
    n + 1 = m + 1 := by
  congr
```

::::full
The `congr` tactic also accepts a numerical argument,
which tells Lean how deeply to decompose the goal.
So, given a goal like `((a, b), (c, d)) = ((e, f), (g, h))`,
`congr 1` only applies {tactic}`congr` once to the goal, and would produce
two subgoals: `(a, b) = (e, f)` and `(c, d) = (g, h)`.
`congr 2`, meanwhile, would apply {tactic}`congr` again to
both these subgoals, and produce four subgoals: `a = e`, `b = f`,
`c = g` and `d = h`. Using {tactic}`congr` without an argument always
decomposes the goal as deeply as possible.

Why does Lean provide this level of flexibility? Depending
on what we are trying to prove, deeper applications
of {tactic}`congr` may make our goal unprovable. Consider
this example:
::::

::::terse
We can specify the recursion-depth with `congr n`.
::::

```lean +error (name := congr1)
example (a b c d : Nat) (hab : a = b) (hcd : c = d) :
    (a, c + 1) = (b, 1 + d) := by
  congr
```

We now have three goals: `c = 1`, `1 = d`, and `1 = d`,
but these are not provable from our hypotheses! {tactic}`congr`
has gone too deep.

```leanOutput congr1
unsolved goals
case e_snd.e_a
a b c d : Nat
hab : a = b
hcd : c = d
⊢ c = 1

case e_snd.e_a.e_2
a b c d : Nat
hab : a = b
hcd : c = d
⊢ 1 = d

case e_snd.e_a.e_3
a b c d : Nat
hab : a = b
hcd : c = d
⊢ 1 = d
```

```lean
example (a b c d : Nat) (hab : a = b) (hcd : c = d) :
    (a, c + 1) = (b, 1 + d) := by
  /- Only shallowly using `congr` here allows us to complete the proof -/
  congr 1
  rw [Nat.add_comm]
  congr
```

# Using {tactic}`apply` on Hypotheses

::::full
The tactic `apply t at h` matches an implication `t`
(say, of the form `a → b`) against a hypothesis `h` in the local
context. Unlike ordinary {tactic}`apply`, which matches the goal against `b`
and replaces it with the subgoal `a`), `apply t at h` matches the type of `h`
against `a` and, if successful, replaces `h` with a hypothesis of type `b`.

In other words, `apply t at h` gives us a form of "forward
reasoning": given `t : a → b` and `h : a`, it replaces `h` with a proof of `b`.

By contrast, ordinart `apply t` is "backward reasoning": given `t : a → b`
and a goal `⊢ b`, it replaces the goal with `⊢ a`.

Here is a variant of the proof that uses forward reasoning rather than backward reasoning:
::::

:::slidebreak
:::

::::terse
The ordinary {tactic}`apply` tactic is a form of "backward
reasoning." It says "We are trying to prove `a` and we know
`b → a`, so if we can prove `b` we'll be done."

By contrast, the variant `apply ... at ...` is "forward reasoning":
it says "We know `b` and we know `b → a`, so we also know `a`."
::::


```lean
example (n m p q : Nat)
    (h : n = m → p = q)
    (hnm : n = m) :
    p = q := by
  apply h at hnm
  exact hnm
```

::::full
Forward reasoning begins with what is already known — premises and
previously proven theorems — and derives new facts from
them until the goal is reached.  Backward reasoning begins with
the _goal_ and works backward through implications that would prove
it, until remaining goals are facts that are already known.

The informal proofs in mathematics and computer science often
use forward reasoning.  In Lean, however, backward reasoning is often more
idiomatic, though forward reas can sometimes be easier to follow or more natural for
particular proofs.

You may be interested to know that the `apply ... at ...` tactic
is not part of Lean's core set of tactics. However, Lean makes it
very easy for users to define new tactics that suit their
particular proof style, and so the developers of the [Mathlib](https://github.com/leanprover-community/mathlib4) library
defined the `apply ... at ...` tactic to
better support forward reasoning. Mathlib is a very large development,
so we will not import the whole thing here, but we have
made `apply ... at ...` available because it is quite useful.
::::

# Specializing Hypotheses

We've already seen how we can use {tactic}`have` to do
forward reasoning, by letting us state and prove useful facts
that get us closer to the main goal we're trying to prove. Often,
though, these facts are just special cases of more general hypotheses
we already have.

If `h` is a quantified hypothesis in the current context — i.e.,
`h : ∀ (x : α), P x` — then we can use {tactic}`have` to obtain a special
case of `h` by supplying a value for `x`. For example, `have h := h (x := e)`
introduces a new `h` which `x` has been instantiated with `e`.

For example:

```lean
example (m : Nat) (h : ∀ n, m * n = 0) : m = 0 := by
  have h := h (n := 1)
  rw [Nat.mul_one] at h
  exact h
```

You may notice that, in the above proof, the original `h` is still
present in the contenxt, although it is shadowed by the new `h`.
Often we don't care to keep this old hypothesis around, and so we can use the {tactic}`replace`
tactic instead. It behaves like {tactic}`have`, except that
it gets rid of the old hypothesis afterwards when possible:

```lean
example (m : Nat) (h : ∀ n, m * n = 0) : m = 0 := by
  replace h := h (n := 1)
  rw [Nat.mul_one] at h
  exact h
```

Specializing a hypothesis in this way is common enough that Lean provides the
{tactic}`specialize` tactic for it. For example,
`specialize h 1` is a more concise way of writing `replace h := h 1`:

```lean
example (m : Nat) (h : ∀ n, m * n = 0) : m = 0 := by
  specialize h 1
  rw [Nat.mul_one] at h
  exact h
```

:::::exercise (rating := 3) (name := "nth?_always_none")
Use {tactic}`have`, {tactic}`replace`, or {tactic}`specialize` to prove the the following lemma,
following the model of the examples above. Do not use {tactic}`induction`.

```lean
theorem nth?_always_none (l : List Nat) (h : ∀ i, nth? l i = none) :
    l = [] := by
  solution!
    cases l with
    | nil => rfl
    | cons x xs =>
      have h := h (i := 0)
      dsimp [nth?] at h
      contradiction
```
:::::


Tactics like {tactic}`have` and {tactic}`replace` can also be used with lemmas and
theorems we've already proven, not just things in our context.
Using these tactis before {tactic}`apply` gives us yet another way to
control where {tactic}`apply` does its work.

```lean
example (a b c d e f : Nat)
    (h₁ : [a, b] = [c, d])
    (h₂ : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  have h := trans_eq (y:= [c, d])
  apply h
  /- This tactic closes a goal if it appears anywhere in the context.
     In this case we could also write `exact h₁` ... -/
  assumption
  /- .. and here we could also write `exact h₂` -/
  assumption
```

# Generalizing the Induction Hypothesis

Recall this function for doubling a natural number from the
{ref "Induction"}[Induction] chapter:

```display
def double (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => (double n') + 2
```

::::terse
Suppose we want to show that {name}`Nat.double` is injective (i.e.,
it maps different arguments to different results).
::::

::::full
Sometimes {tactic}`induction` gives us an an induction hypothesis too specific to be useful.
This can happen when another varaible in the theorem is fixed during the induction,
even though the induction step might need to use it with different values of that
variables.

For example, suppose we want to show that {name}`Nat.double` is injective —
i.e., that it maps different arguments to different results:

```lean
example (n m : Nat) (h : n.double = m.double) : n = m := sorry
```

If we begin it with

::::

:::dev "Yipeng Liu (berberman)"
A single {tactic}`contradiction` can close `zero.succ` case without any rewrite as shown below —
`h : Nat.double 0 = Nat.double (m' + 1)` gets unfolded to `0 = ((Nat.double m').add 1).succ`,
and then `noConfusion` kicks in. The unfold can happen because {name}`Nat.double` is not marked as
`irreducible`. Similarly it can close `succ.zero` case. I think this is fine, and I removed the
{name}`Nat.double_zero`/{name}`Nat.double_succ` rewrites.
:::

```lean  +error (name := gen1)
example (n m : Nat) (h : n.double = m.double) : n = m := by
  induction n with
  | zero =>
    cases m with
    | zero => rfl
    | succ m' => contradiction
  | succ n' ih =>
    cases m with
    | zero => contradiction
    | succ m' =>
      congr
```

```leanOutput gen1
unsolved goals
case succ.succ.e_a
n' m' : Nat
ih : Nat.double n' = Nat.double (m' + 1) → n' = m' + 1
h : Nat.double (n' + 1) = Nat.double (m' + 1)
⊢ n' = m'
```

:::terse
We get stuck, because the induction hypothesis `ih` is too specific to be useful.
:::

::::full
We get stuck — `m` is fixed during the induction,
so in the successor case the induction hypothesis `ih` is specialized to the current value of `m`.
After the case split, that value is `m' + 1`, and the induction hypothesis has the form:

```display
ih : n'.double = (.succ m').double → n' = .succ m'
```

From `h`, using the definition of {name}`Nat.double` we can obtain

```display
Nat.double n' = Nat.double m'
```

and to prove the goal we would like to apply an induction hypothesis at `m'`.
Nevertheless, `ih` is specialized to `m' + 1` — it would require

```display
Nat.double n' = Nat.double (m' + 1)
```

and would conclude

```
n' = m' + 1
```

which is not what we need. Instead, we need an induction hypothesis that is general in `m`:

```display
ih : ∀ m, Nat.double n' = Nat.double m → n' = m
```

Then in this branch we can instantiate it with `m'`.
::::

We can obtain a more generalized induction hypothesis by writing

```display
induction n generalizing m with
```

:::slidebreak
:::

What went wrong?

::::full
The problem is that `m` is already in the context when we invoke
`induction n`. Since `m` is an ordinary argument of the theorem,
this is exactly what we normally want — we are considering some particular
`n` and `m`, together with the hypothesis `n.double = m.double` and trying
to prove `n = m`.

But if we now do `induction n`, the induction is carried out while keeping this particular
`m` fixed. That is, we are proving for all `n`, the proposition

  - `P n` = "if `double n = double m`, then `n = m`"

for this fixed `m`, by showing

  - `P 0`

     (i.e., "if `double 0 = double m` then `0 = m`") and

  - `P n → P (n + 1)`

    (i.e., "if `double n = double m` then `n = m`" implies "if
    `double (n + 1) = double m` then `n + 1 = m`").

If we look closely at the second statement, it is saying something
rather strange: that, for a _particular_ `m`, if we know

  - "if `double n = double m` then `n = m`"

then we can prove

   - "if `double (n + 1) = double m` then `n = m + 1`".

To see why this is strange, let's choose of a particular `m` —
say, `5`.  The statement is then saying that, if we know

  - `Q` = "if `double n = 10` then `n = 5`"

then we can prove

  - `R` = "if `double (n + 1) = 10` then `n + 1 = 5`".

But knowing `Q` doesn't give us any help at all with proving `R`.
If we tried to prove `R` from `Q`, we would start with something
like "Suppose `double (n + 1) = 10`..." but then we would be stuck:
knowing that `double (n + 1)` is `10` tells us nothing helpful about
whether `double n` is `10` (indeed, it strongly suggests that
`double n` is _not_ `10`), so `Q` is useless.

This is exactly what we saw in the proof state.
::::

Trying to carry out this proof by induction on `n` with `m` fixed
doesn't work, because we are then trying to
prove a statement involving _every_ `n` but just a _particular_
`m`.

:::slidebreak
:::

A successful proof of `double_injective` keeps `m` universally
quantified in the goal statement at the point where the
`induction` tactic is invoked on `n`.

:::dev "Yipeng Liu (berberman)"

I decided to ot to cover this "delayed {tactic}`intro`" trick at all, given that we are sticking
to the declaration-header style (i.e. theorem arguments are already in the context), and the
more idiomatic way is to use `induction ... generalizing ...`.

We can bring this trick back if we later find it useful though, and at that time we should introduce
{tactic}`revert` as well.

```lean
theorem double_injective : ∀ (n m : Nat),
    n.double = m.double →
    n = m := by
  intro n
  induction n
  case zero =>
    rw [Nat.double_zero]
    intro m eq
    cases m
    case zero => rfl
    case succ _ =>
      rw [Nat.double_succ] at eq
      contradiction
  case succ n' ih =>
  -- Notice that both the goal and the induction hypothesis are
  -- different this time: the goal asks us to prove something more
  -- general (i.e., we must prove the statement for _every_ `m`), but
  -- the induction hypothesis `ih` is correspondingly more flexible,
  -- allowing us to choose any `m` we like when we apply it.
  intro m eq
  -- Now we've introduced the assumption that `double n = double m`.
  -- Since we are doing a case analysis on `n`, we also need a case
  -- analysis on `m` to keep the two in sync.
  cases m
  case zero =>
    -- The 0 case is trivial:
    rw [Nat.double_zero, Nat.double_succ] at eq
    contradiction
  case succ m' =>
    congr
    -- Since we are now in the second branch of the `cases m`, the
    -- `m'` mentioned in the context is the predecessor of the `m` we
    -- started out talking about.  Since we are also in the `succ` branch of
    -- the induction, this is perfect: if we instantiate the generic `m`
    -- in the IH with the current `m'` (this instantiation is performed
    -- automatically by the `apply` in the next step), then `ih` gives
    -- us exactly what we need to finish the proof.
    apply ih; rw [Nat.double_succ, Nat.double_succ] at eq; injections
```

:::

:::slidebreak
:::

 The thing to take away from all this is that you need to be
careful, when using induction, that you are not trying to prove
something too specific: When proving a property quantified over
variables `n` and `m` by induction on `n`, it is sometimes crucial
to leave `m` "generic."

::::full
The following exercise, which further strengthens the link between
`==` and `=`, follows the same pattern.
::::

::::terse
The following theorem, which further strengthens the link between
`==` and `=`, follows the same pattern.
::::


```lean
theorem beq_eq : ∀ (n m : Nat),
    (n == m) = true → n = m := by
  solution!
    intro n
    induction n
    case zero =>
      intro m eq; cases m
      case zero => rfl
      case succ m' =>
        contradiction
    case succ n' ih =>
      intro m eq; cases m
      case zero => contradiction
      case succ m' =>
        congr
        apply ih
        rw [beq_succ] at eq
        assumption
```

:::gradeTheorem 2 beq_eq
:::

::::::full
:::::exercise (rating := 2) (name := "beq_eq_informal")
Give a careful informal proof of `beq_eq`, stating the induction
hypothesis explicitly and being as explicit as possible about
quantifiers, everywhere.

:::solution
```
_Theorem_: For all natural numbers `n` and `m`, if [n == m =
true], then `n = m`.

_Proof_ (more pedantic, arguably less clear): We argue by
induction on `n`.

- Base case: `n = 0`.  We must show, for all natural numbers
  `m`, that `0 == m = true` implies `0 = m`.  We proceed by
  cases on `m`.

    - If `m = 0`, we must show that `0 == 0 = true` implies [0 =
      0], which holds by reflexivity.

    - If `m = .succ m'` for some `m'`, we must show that [0 == .succ m'
      = true] implies `0 = .succ m'`.  But `0 == .succ m'` evaluates to
      `false`, so the antecedent of this implication is [false =
      true], which is absurd, and hence the whole implication is
      true.

- Inductive case: `n = .succ n'`. We must show that for all natural
  numbers `m`, `.succ n' == m = true` implies `.succ n' = m`.

  We may assume the induction hypothesis: for all natural
  numbers `m`, `n' == m = true`, implies `n' = m`.

  We again proceed by cases on `m`.

    - If `m = 0`, we must show that `.succ n' == 0 = true` implies
      `.succ n' = m`. But `.succ n' == 0` evaluates to `false`, so the
      antecedent of this implies is again absurd, and hence the
      whole implication is true.

    - If `m = .succ m'` for some `m'`, we must show that [.succ n' == .succ
      m' = true] implies `.succ n' = .succ m'`.  So let us assume the [.succ
      n' == .succ m' = true].  This simplifies to [n' == m' =
      true]. Hence we can apply the induction hypothesis (with
      `m` instantiated to `m'`) to obtain `n' = m'`.  Hence, to
      show `.succ n' = .succ m'` it suffices to show `.succ n' = .succ n'`,
      which is true by reflexivity. []

_Alternate proof_ (in a more natural style):
By induction on `n`.

- Suppose `n = 0`.  We must show that if `0 == m = true` then [0
  = m]. Now if `m` were of the form `.succ m'` for some `m'`, then
  we would have `0 == .succ m' = true`, which is absurd. So `m` must
  indeed be 0.

- Otherwise, we have `n = .succ n'`. The induction hypothesis states
  that for all m, if `n' == m = true`, then `n' = m`; and on the
  assumption `.succ n' == m = true`, we must show that `.succ n' = m`.
  In this case `m` must have the form `.succ m'` for some `m'`, for
  if `m` were 0, our assumption would be `.succ n' == 0 = true`,
  which is absurd.  So our assumption has the form [.succ n' == .succ m'
  = true], which simplifies to `n' == m' = true`. Applying the
  induction hypothesis to the assumption (with `m` instantiated
  to `m'`) gives us that `n' = m'`, which directly implies our
  goal `.succ n' = .succ m'`. []
```
:::

:::grade
`GRADE_MANUAL 2: informal_proof`
:::
:::::

:::::exercise (rating := 3) (name := "plus_n_n_injective")
:::slidebreak
:::

In addition to being careful about how you use `intro`, practice
using "at" variants in this proof.  (Hint: use `plus_n_Sm`.)

```lean
theorem plus_n_n_injective : ∀ (n m : Nat),
    n + n = m + m →
    n = m := by
  solution!
    intro n
    induction n
    . case zero =>
      intro m eq; cases m
      . case zero => rfl
      . case succ => dsimp at eq; contradiction
    . case succ n' ih =>
      intro m eq; cases m
      . case zero => dsimp at eq; contradiction
      . case succ m' =>
        rw [add_succ, add_succ (m' + 1)] at eq
        injection eq with eq
        rw [add_comm, add_comm (m' + 1)] at eq
        injections eq; congr; exact ih _ eq
```

:::gradeTheorem 3 plus_n_n_injective
:::
:::::

::::::

:::slidebreak
:::

The strategy of doing fewer `intros` before an `induction` to
obtain a more general IH doesn't always work; sometimes some
_rearrangement_ of quantified variables is needed.  Suppose, for
example, that we wanted to prove `double_injective` by induction
on `m` instead of `n`.

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs(warning) in
theorem double_injective_take2_FAILED (n m : Nat) :
    n.double = m.double →
    n = m := by
  induction m
  case zero =>
    intro eq
    cases n
    case zero => rfl
    case succ =>
      rw [Nat.double_zero, Nat.double_succ] at eq
      contradiction
  case succ =>
    intro eq
    cases n
    case zero =>
      rw [Nat.double_zero, Nat.double_succ] at eq
      contradiction
    case succ =>
      congr
    -- We are stuck here, just like before.
      sorry
```

:::slidebreak
:::

The problem is that, to do induction on `m`, we must first
introduce `n`.

::::full
What can we do about this?  One possibility is to rewrite the
statement of the lemma so that `m` is quantified before `n`.  This
works, but it's not nice: We don't want to have to twist the
statements of lemmas to fit the needs of a particular strategy for
proving them!  Rather we want to state them in the clearest and
most natural way.
::::

:::slidebreak
:::

What we can do instead is to first introduce all the quantified
variables and then explicitly generalize one or more of them
The `generalizing` option for the `induction` tactic does this.

```lean
theorem double_injective_take2 (n m : Nat) :
    n.double = m.double →
    n = m := by
  intro eq
  -- `n` and `m` are both in the context
  -- This lets us do induction on `m` and get a sufficiently general IH
  induction m generalizing n
  case zero =>
    cases n
    case zero => rfl
    case succ =>
      rw [Nat.double_zero, Nat.double_succ] at eq
      contradiction
  case succ _ ih =>
    cases n
    case zero =>
      rw [Nat.double_zero, Nat.double_succ] at eq
      contradiction
    case succ =>
      congr
      rw [Nat.double_succ, Nat.double_succ] at eq
      injections _ eq; exact ih _ eq
```

:::dev PotentialImprovement
Somewhere (in this file? in Poly?), we might want to include
a more careful discussion of the way generalized IHs are handled in
informal proofs.  Basically, the practice seems to be to assume
we're working with a "general enough" IH, but seldom to bother
saying exactly what it is!
:::

::::full
Let's look at an informal proof of this theorem.  Note that
the proposition we prove by induction leaves `n` quantified,
corresponding to the use of generalize dependent in our formal
proof.

_Theorem_: For any nats `n` and `m`, if `double n = double m`, then
  `n = m`.

_Proof_: Let `m` be a `Nat`. We prove by induction on `m` that, for
  any `n`, if `double n = double m` then `n = m`.

  - First, suppose `m = 0`, and suppose `n` is a number such
    that `double n = double m`.  We must show that `n = 0`.

    Since `m = 0`, by the definition of `double` we have \[double n =
    0\].  There are two cases to consider for `n`.  If `n = 0` we are
    done, since `m = 0 = n`, as required.  Otherwise, if `n = .succ n'`
    for some `n'`, we derive a contradiction: by the definition of
    `double`, we can calculate `double n = .succ (.succ (double n'))`, but
    this contradicts the assumption that `double n = 0`.

  - Second, suppose `m = .succ m'` and that `n` is again a number such
    that `double n = double m`.  We must show that `n = .succ m'`, with
    the induction hypothesis that for every number `s`, if \[double s =
    double m'\] then `s = m'`.

    By the fact that `m = .succ m'` and the definition of `double`, we
    have `double n = .succ (.succ (double m'))`.  There are two cases to
    consider for `n`.

    If `n = 0`, then by definition `double n = 0`, a contradiction.

    Thus, we may assume that `n = .succ n'` for some `n'`, and again by
    the definition of `double` we have
    `.succ (.succ (double n')) = .succ (.succ (double m'))`,
    which implies by injectivity that `double n' = double m'`.
    Instantiating the induction hypothesis with `n'` thus
    allows us to conclude that `n' = m'`, and it follows immediately
    that `.succ n' = .succ m'`.  Since `.succ n' = n` and `.succ m' = m`, this is just
    what we wanted to show. \[\]
::::

:::dev PotentialImprovement
Maybe we should put one more good example to round out this section?
:::

# Rewriting with Conditional Statements

We'll use a boolean "less or equal" test on numbers, written `n ≤? m`
(the library function `Nat.ble`), together with the fact that it
commutes with successor on both sides.

:::dev "Benjamin Pierce (bcpierce00)"
Added, to make the file compile, on Claude's suggestion. But is this the right way?
Answer: No, just replaces uses of it by Nat.ble!
:::

```lean
infix:52 " ≤? " => Nat.ble

theorem zero_ble (m : Nat) : (0 ≤? m) = true := rfl
theorem succ_ble_succ (n m : Nat) : ((n + 1) ≤? (m + 1)) = (n ≤? m) := rfl
```

:::dev "Claude" BeforeNextRelease
Claude-generated note.
(BCP: Whoever reviews this part of the chapter next should read and delete it.)

The `leb_*` → `ble_*` rename is now applied across
`Lists`, `Tactics`, and `Logic`, matching the `ble_complete` / `ble_correct` /
`ble_iff` names already used in `IndProp`: every one of these is stated over
`≤?`, which is notation for `Nat.ble` (declared just above), so the name now
tracks the function. Statements keep the `≤?` notation rather than spelling out
`Nat.ble`, following `IndProp`.

One thing to think about:
`beq_succ` (above, and used in `Logic`) is a separate `BEq` question: it could
likewise be restated via `Nat.beq_eq_true_eq` / `BEq.comm`, which would let the
`beq_symm` exercise below drop its induction. Worth a decision, but it changes
an exercise's shape, not just a name.
:::

Suppose that we want to show that `add` is the inverse of
`sub`.  Since we are working with natural numbers, we need an
assumption to prevent `sub` from truncating its result. With
this assumption, the induction hypothesis becomes
`forall m, n' ≤? m = true → (m - n') + n' = m`.  The beginning of the proof
uses techniques we have already seen -- in particular, notice how
we induct on `n` before introducing `m`, so that the induction
hypothesis becomes sufficiently general.

```lean
theorem sub_add_ble : ∀ (n m : Nat),
    n ≤? m = true → (m - n) + n = m := by
  intro n
  induction n
  case zero =>
    intro m h; rw [add_zero]; cases m
    case zero => rfl
    case succ => rfl
  case succ n' ih =>
    intro m h; cases m
    case zero => contradiction
    case succ m' =>
      rw [succ_ble_succ] at h
      rw [succ_sub_succ, add_succ]
    -- At this point, we need to show `(m' - n') + n' + 1 = m' + 1`
    -- from the assumption `(n' <= m') = true`.  We could use the
    -- `have` tactic to prove `(m' - n') + n' = m'` from the IH.
    -- However, we can also just use `rw` directly...
      rw [ih]
      assumption
```

::::full
if we rewrite with a conditional statement of the form
`P → a = b`, then Lean tries to rewrite with `a = b`, and then
asks us to prove `P` in a new subgoal.  If the statement has more
than one assumption, then we get one subgoal for each assumption.
::::

::::::full
:::::exercise (rating := 3) (name := "gen_dep_practice")
Prove this by induction on `l`.

```lean
theorem nth_error_after_last {α : Type} (n : Nat) (l : List α) :
    l.length = n →
    nth? l n = none := by
  solution!
    intros hlen
    induction l generalizing n
    case nil => rfl
    case cons hd tl ih =>
      rw [List.length_cons] at hlen
      rw [← hlen]
      dsimp [nth?]; apply ih _; rfl
```

:::gradeTheorem 3 nth_error_after_last
:::
:::::

::::::

::::hide
```
/- LATER: BCP 9/16: Hiding the following three exercises, which
   need some fixing or moving elsewhere... -/
-- EX3? (app_length_cons)
/- Prove this by induction on `l1`, without using `app_length`
    from `Lists`. -/

theorem app_length_cons {α : Type} (l1 l2 : List α) (x : α) (n : Nat) :
    (l1 ++ (x :: l2)).length = n →
    ((l1 ++ l2).length) + 1 = n := by
  solution!
    intro heq
    induction l1 generalizing n
    case nil =>
      assumption
    case cons hd tl ih =>
      rw [List.cons_append, List.length_cons] at *
      rw [← heq]
      have h : (tl ++ l2).length + 1 = (tl ++ x :: l2).length := by apply ih _; rfl
      rw [h]
-- []

-- EX4? (app_length_twice)
/- Prove this by induction on `l`, without using `app_length` from `Lists`. -/
/- LATER: This might be a little bit hard??
   There are a couple of tricky little points!
   APT: Yes: the nested induction is a first, I think. And it would
     be good to have seen rewrite with an applied term; otherwise
     a kludgy forward `assert` or `pose proof` seems needed. -/
/- LATER: no need for a _nested_ induction per se -- side lemmas will
   do the trick, too, and students have been exposed to that
   already. -/
/- LATER: APT: Yes, but the lemma above is terribly ad-hoc, as well
   as ill-suited for its use here!
   I realize that the pedagogical point here has nothing to do with
   developing sensible lemmas for lists, but these seem pretty distorted. -/

theorem app_length_twice {α : Type} (n : Nat) (l : List α) :
    l.length = n →
    (l ++ l).length = n + n := by
  solution!
    intros heq
    induction l generalizing n
    case nil => rw [List.append_nil, List.length_nil, ← heq]; rfl
    case cons hd tl ih =>
      rw [List.cons_append]
      rw [List.length_cons] at *
      have h : (tl ++ tl).length + 1 = (tl ++ hd :: tl).length := by
        apply app_length_cons _ _ hd _; rfl
      rw [← heq, ← h, ih tl.length, ← add_assoc]
      congr 1
      rw [add_assoc, add_assoc]
      congr 1
      rw [add_comm]
      rfl
-- []

-- EX3? (diagonal_induction)
/- LATER: Uses `Prop`, which has not been introduced.  This
   exercise should be moved to another chapter. -/
-- Prove the following principle of induction over two naturals.

theorem diagonal_induction : ∀ (P : Nat → Nat → Prop),
    P 0 0 →
    (∀ m, P m 0 → P (m + 1) 0) →
    (∀ n, P 0 n → P 0 (n + 1)) →
    (∀ m n, P m n → P (m + 1) (n + 1)) →
    ∀ m n, P m n := by
  intro P H00 HS0 H0S HSS m n
  induction m generalizing n
  case zero =>
    induction n
    case zero => exact H00
    case succ _ ih => exact H0S _ ih
  case succ _ ih =>
    cases n
    case zero => exact HS0 _ (ih _)
    case succ => exact HSS _ _ (ih _ )

-- /ADMITTED
-- []
```
::::

::::hide
```
 TODO: (DHS) This should all move to Induction.lean, probably, but that
   means we will need to redo the examples here. Keeping the original
   Rocq here for posterity

(* ###################################################### *)
(** * Unfolding Definitions *)

(** It sometimes happens that we need to manually unfold a name that
    has been introduced by a `Definition` so that we can manipulate
    the expression it stands for.

    For example, if we define... *)

Definition square n := n * n.

(** ...and try to prove a simple fact about `square`... *)

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.

(** ...we appear to be stuck: `simpl` doesn't simplify anything, and
    since we haven't proved any other facts about `square`, there is
    nothing we can `apply` or `rewrite` with. *)

(** TERSE: *** *)
(** To make progress, we can manually `unfold` the definition of
    `square`: *)

  unfold square.

(** Now we have plenty to work with: both sides of the equality are
    expressions involving multiplication, and we have lots of facts
    about multiplication at our disposal.  In particular, we know that
    it is commutative and associative, and from these it is not hard
    to finish the proof. *)

  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

(** TERSE: *** *)
(** At this point, a bit deeper discussion of unfolding and
    simplification is in order.

    We already have observed that tactics like `simpl`, `reflexivity`,
    and `apply` will often unfold the definitions of functions
    automatically when this allows them to make progress.  For
    example, if we define `foo m` to be the constant `5`... *)

Definition foo (x: Nat) := 5.

(** .... then the `simpl` in the following proof (or the
    `reflexivity`, if we omit the `simpl`) will unfold `foo m` to
    `(fun x => 5) m` and further simplify this expression to just
    `5`. *)

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(** TERSE: *** *)
(** But this automatic unfolding is somewhat conservative.  For
    example, if we define a slightly more complicated function
    involving a pattern match... *)

Definition bar x :=
  match x with
  | 0 => 5
  | .succ _ => 5
  end.

(** ...then the analogous proof will get stuck: *)

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

(** FULL: The reason that `simpl` doesn't make progress here is that it
    notices that, after tentatively unfolding `bar m`, it is left with
    a match whose scrutinee, `m`, is a variable, so the `match` cannot
    be simplified further.  It is not smart enough to notice that the
    two branches of the `match` are identical, so it gives up on
    unfolding `bar m` and leaves it alone.

    Similarly, tentatively unfolding `bar (m+1)` leaves a `match`
    whose scrutinee is a function application (that cannot itself be
    simplified, even after unfolding the definition of `+`), so
    `simpl` leaves it alone. *)

(** TERSE: *** *)
(** FULL: At this point, there are two ways to make progress.  One is to use
    `destruct m` to break the proof into two cases, each focusing on a
    more concrete choice of `m` (`O` vs `.succ _`).  In each case, the
    `match` inside of `bar` can now make progress, and the proof is
    easy to complete. *)
(** TERSE: There are now two ways make progress.

    First, we can use `destruct m` to break the proof into two cases: *)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** This approach works, but it depends on our recognizing that the
    `match` hidden inside `bar` is what was preventing us from making
    progress. *)

(** TERSE: *** *)
(** A more straightforward way forward is to explicitly tell Rocq to
    unfold `bar`. *)

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.

(** Now it is apparent that we are stuck on the `match` expressions on
    both sides of the `=`, and we can use `destruct` to finish the
    proof without thinking so hard. *)

  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.
```
::::

# Using `cases` on Compound Expressions

:::dev
HIDE: CH: If eqn is only useful for compound expressions and those
are only discussed here, why has eqn been introduced before this
point? It seems that so far its only use was for documentation, and
while one might argue that it's good practice to always use eqn,
that's not the case, as illustrated by its disappearance in Logics.
BCP '19: Fixed Logic.v -- I do think it's good documentation!
:::

::::full
We have seen many examples where `cases` is used to
perform case analysis of the value of some variable.  Sometimes we
need to reason by cases on the result of some _expression_.  We
can also do this with `cases`.

Here are some examples:
::::

::::terse
The `cases` tactic can be used on expressions as well as
variables:
::::

```lean
def sillyfun (n : Nat) : Bool :=
  if n == 3 then false
  else if n == 5 then false
  else false

theorem sillyfun_false (n : Nat) :
    sillyfun n = false := by
  unfold sillyfun
  cases (n == 3)
  case false =>
    dsimp; cases (n == 5)
    case false => rfl
    case true => rfl
  case true => rfl
```

::::full
After unfolding `sillyfun` in the above proof, we find that
we are stuck on `if (n == 3) then ... else ...`.  But either
`n` is equal to `3` or it isn't, so we can use `cases (n == 3)` to let us reason about the two cases.

In general, the `cases` tactic can be used to perform case
analysis of the results of arbitrary computations.  If `e` is an
expression whose type is some inductively defined type `T`, then,
for each constructor `c` of `T`, `cases e` generates a subgoal
in which all occurrences of `e` (in the goal and in the context)
are replaced by `c`.
::::

## Destructing Tuples

`cases` is useful when we are dealing with inductively defined types
that can be one thing or another; a `Bool` is either a `false` or a `true`,
and a `Nat` is either `0` or `succ n`. When we want more information about
inductively defined types that are products of multiple things, we instead
want a way to get the pieces of that value out from it.

When we have a value `v : α × β` in our context, we can
get the first and second projections of `v` using this tactic:

```display
let ⟨a, β⟩ := v
```

::::::full
:::::exercise (rating := 3) (name := "combine_split")
Here is an implementation of the `unzip` function mentioned in
chapter {ref "Poly"}[Poly]. We'll call it `split` so as not to
confuse Lean.

```lean
def split {α β : Type} (l : List (α × β)) : (List α) × (List β) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    match split t with
    | (lx, ly) => (x :: lx, y :: ly)
```

Prove that `split` and `zip` are inverses in the following sense:

```lean
theorem split_zip {α β : Type} (l : List (α × β)) l1 l2 :
    split l = (l1, l2) →
    zip l1 l2 = l := by
  solution!
    intro h
    induction l generalizing l1 l2
    case nil =>
      injections h1 h2
      rw [← h1, ← h2]
      rfl
    case cons hd tl ih =>
      let ⟨a, b⟩ := hd
      dsimp [split] at h
      injections h1 h2
      rw [← h1, ← h2]
      dsimp [zip]
      rw [ih]
      rfl
```
:::::

::::::

::::terse
When using `cases`, we can specify to Lean that it should
remember an equality between a compound expression and what we are
decomposing it into, using `cases h: ...` syntax. This information
can actually be critical, and, if we leave it out, we might lack
information we need to complete a proof.
::::

::::full
For example, suppose we define a function `sillyfun1` like this:
::::

```lean
def sillyfun1 (n : Nat) : Bool :=
  if n == 3 then true
  else if n == 5 then true
  else false
```

::::full
Now suppose that we want to convince Lean that `sillyfun1 n`
yields `true` only when `n` is odd.  If we start the proof like
this (with no `h:` on the `cases`)...
::::

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs(warning) in
example (n : Nat) :
    sillyfun1 n = true →
    n.odd = true := by
  intro eq
  unfold sillyfun1 at eq
  cases (n == 3)
  case false => sorry
  case true => sorry
```

::::full
... then we are stuck at this point because the context does
not contain enough information to prove the goal!
Because `n == 3` appears in our hypothesis, rather than in our
goal, `cases (n == 3)` does not automatically replace the expression
with `false` or `true` like it did during the proof of `sillyfun_false`.
We want to add an equation to the context that records which case we are in.
This is precisely what the
`h:` qualifier does.
::::

:::slidebreak
:::

:::terse
Adding the `h:` qualifier saves this information so we can use it.
:::

```lean
theorem sillyfun1_odd (n : Nat) :
    sillyfun1 n = true →
    n.odd = true := by
  intro eq
  unfold sillyfun1 at eq
  cases h : (n == 3)
  case false =>
    -- Now we have the same state as at the point where we got stuck
    -- above, except that the context contains an extra equality
    -- assumption, which is exactly what we need to make progress.
    rw [h] at eq; dsimp at eq
    cases h': (n == 5)
    case false =>
      rw [h'] at eq; dsimp at eq
      contradiction
    case true =>
      apply beq_eq at h'
      rw [h']; rfl
      -- When we come to the second equality test in the body
      -- of the function we are reasoning about, we can use
      -- `h:` again in the same way, allowing us to finish the
      -- proof.
  case true =>
    apply beq_eq at h
    rw [h]; rfl
```

::::::full
:::::exercise (rating := 2) (name := "destruct_eqn_practice")
```lean
theorem bool_fn_applied_thrice (f : Bool → Bool) (b : Bool) :
    f (f (f b)) = f b := by
  solution!
    cases b
    case false =>
      cases heqffalse : (f false)
      case false =>
        rw [heqffalse, heqffalse]
      case true =>
        cases heqftrue : (f true)
        case false => assumption
        case true => assumption
    case true =>
      cases heqftrue : (f true)
      case false =>
        cases heqffalse : (f false)
        case false => assumption
        case true => assumption
      case true =>
          rw [heqftrue, heqftrue]
```

:::gradeTheorem 2 bool_fn_applied_thrice
:::
:::::

::::::

# Review

:::suppressPreviousHeaderWhenTerse
:::

:::dev "Noé De Santo (Ef55)" PotentialImprovement (year := 2025)
This list is getting pretty long; maybe it should be
further divided into catgories (I'd suggest: Basic hypotheses/goal
manipulation, equality, indutive types, others)
:::

::::full
We've now talked about many of Lean's most fundamental tactics.
We'll introduce a few more in the coming chapters, and later on
we'll see some more powerful _automation_ tactics that make Lean
help us with low-level details.  But basically we've got what we
need to get work done.

Here are the ones we've seen:

  - `intro`: move hypotheses/variables from goal to context

  - `rfl`: finish the proof (when the goal looks like \[e =
    e\])

  - `apply`: prove goal using a hypothesis, lemma, or constructor

  - `apply... at H`: apply a hypothesis, lemma, or constructor to
    a hypothesis in the context (forward reasoning)

  - `apply... with...`: explicitly specify values for variables
    that cannot be determined by pattern matching

  - `replace h (x:= ...)`: refine a hypothesis by fixing some of
    its variables

  - `dsimp`: simplify computations in the goal

  - `dsimp at H`: ... or a hypothesis

  - `rw`: use an equality hypothesis (or lemma) to rewrite the goal

  - `rw ... at H`: ... or a hypothesis

  - `symm`: changes a goal of the form `t=u` into `u=t`

  - `symm at H`: changes a hypothesis of the form `t=u` into
    `u=t`

  - `calc`: prove a goal about a transitive relation via a number of intermediate steps

  - `unfold`: replace a defined constant by its right-hand side in
    the goal

  - `unfold... at H`: ... or a hypothesis

  - `cases ...`: case analysis on values of inductively defined types

  - `cases h:...`: specify the name of an equation to be
    added to the context, recording the result of the case
    analysis

  - `induction ...`: induction on values of inductively
    defined types

  - `induction ... generalizing ...`: hold some variables general while doing induction

  - `injection ... with ...`: reason by injectivity on an equality between values of inductively defined types

  - `injections ... `: reason by injectivity on all the equalities in the context

  - `contradiction`: conclude a proof when there's a false hypothesis in the context

  - `have h : e := ... ` : introduce a "local lemma" `e` and call it `h`

  - `congr`: change a goal of the form `f x = f y` into `x = y`
::::

::::terse
Micro Sermon

Mindless proof-hacking is a terrible temptation...

Try to resist!
::::

::::::full
Additional Exercises

:::dev "Benjamin Pierce (bcpierce00)"
There seems to be nothing left for the student to fill in!
:::

:::::exercise (rating := 3) (name := "beq_symm")
```lean
theorem beq_symm (n m : Nat) :
    (n == m) = (m == n) := by
  induction n generalizing m
  case zero =>
    cases m
    case zero => rfl
    case succ => rfl
  case succ n' ih =>
    cases m
    case zero => rfl
    case succ =>
      rw [beq_succ, beq_succ]
      exact ih _
```

:::gradeTheorem 3 beq_symm
:::
:::::

:::::exercise (rating := 3) (name := "beq_symm_informal")
Give an informal proof of this lemma that corresponds to your
formal proof above:

Theorem: For any `Nat`s `n` `m`, `(n == m) = (m == n)`.

Proof:

:::solution
```
   Let an arbitrary Nat `n` be given.  Proceed by induction
   on `n`.

   - For the base case, we have `n = 0`.  Let `m` be given.
     We must show that
[[
       0 == m = m == 0
]]
     Either `m = 0` or not.

     - If `m = 0`, we must show `0 == 0 = 0 == 0`
       which is true by reflexivity.

     - Otherwise, `m = .succ m'` for some `m'`, and we must show
       `0 == (.succ m') = (.succ m') == 0`. By the definition
       of `beq`, both sides are `false`.

   - In the inductive case, we have `n = .succ n'` for some
     `n'` such that, for any `m`,
[[
       n' == m = m == n'
]]
     Let `m` be given.  Again, `m` is either zero or nonzero.

     - Suppose first `m = 0`.  It's
       enough to show `(.succ n') == 0 = 0 == (.succ n')`.
       By the definition of `beq`, both sides are `false`.

     - Otherwise, `m = .succ m'` for some `m'`.  By the
       assumption, it's enough to show:
[[
         (.succ n') == (.succ m') = (.succ m') == (.succ n')
]]
       And, by the definition of `beq`, this reduces to
       showing:
[[
         m' == n' = n' == m'.
]]
       which is exactly the induction hypothesis.
```
:::
:::::

::::::

::::::full
:::::exercise (rating := 3) (name := "beq_trans")
```lean
theorem beq_trans (n m p : Nat) :
    (n == m) = true →
    (m == p) = true →
    (n == p) = true := by
  solution!
    intros hnm hmp
    apply beq_eq at hnm
    rw [hnm, hmp]
```
:::::

::::::

::::::full
:::::exercise (rating := 3) (name := "split_combine") (level := Advanced) (manual := true)
We proved, in an exercise above, that `combine` is the inverse of
`split`.  Complete the definition of `split_combine_statement`
below with a property that states that `split` is the inverse of
`combine`. Then, prove that the property holds.

Hint: Take a look at the definition of `combine` in {ref "Poly"}[Poly].
Your property will need to account for the behavior of `combine`
in its base cases, which possibly drop some list elements.

```lean
def split_combine_statement : Prop :=
  /- ("`: Prop`" means that we are giving a name to a
     logical proposition here.) -/
  ∀ (α β : Type) (l1 : List α) (l2 : List β),
    l1.length = l2.length →
    split (zip l1 l2) = (l1, l2)

theorem split_combine : split_combine_statement := by
  solution!
    intros α β l1 l2 h
    induction l1 generalizing l2
    case nil =>
      cases l2
      case nil => rfl
      case cons => contradiction
    case cons hd tl ih =>
      cases l2
      case nil => contradiction
      case cons hd' tl' =>
        dsimp [split, zip]
        rw [ih]
        injections
-- SOLUTION

/- Here are more approaches -/
theorem split_combine' (α β :Type) l (l1 : List α) (l2 : List β) :
    (l1, l2) = split l → split (zip l1 l2) = (l1, l2) := by
  intro h
  induction l generalizing l1 l2
  case nil =>
    dsimp [split] at h
    injections h1 h2
    rw [h1, h2]
    rfl
  case cons hd tl ih =>
    let ⟨a, b⟩ := hd
    dsimp [split] at h
    injections h1 h2
    rw [h1, h2]
    dsimp [zip, split]
    rw [ih]
    rfl

-- HIDE
/- Theorem split_combine''_equiv :
    ∀ (X Y:Type) l (l1 : list X) (l2 : list Y),
    (split l = (l1, l2) → split (combine l1 l2) = (l1, l2))
    ↔ (split l = (l1, l2) → combine l1 l2 = l).
Proof.
  intros X Y.
  induction l; intros; split; intros;
    try solve [inversion H0; auto].
  - inversion H0. destruct x.
    destruct (split l). inversion H2; subst. simpl.
    f_equal. apply IHl; auto. apply H in H0.
    inversion H0. destruct (split (combine x0 y0)).
    inversion H3; subst; auto.
  - pose proof H0. apply H in H0. rewrite H0; auto.
Qed.

Theorem combine_split' : ∀ X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) → combine l1 l2 = l.
Proof.
  induction l as [| [x y] l' IHl'].
  - (* l = [] *) intros l1 l2 Heq.
    simpl in Heq. injection Heq as l2mt l1mt.
    rewrite <- l2mt. rewrite <- l1mt. reflexivity.
  - (* l = (x,y) :: l' *) intros l1 l2 Heq.
    simpl in Heq. destruct (split l') as [l1' l2'].
    injection Heq as l2in l1in.
    rewrite <- l2in. rewrite <- l1in. simpl. rewrite IHl'.
    reflexivity. reflexivity.  Qed. -/
-- /HIDE
-- END SOLUTION
```

:::grade
`GRADE_MANUAL 3: split_combine`
:::
:::::

::::::

::::::full
:::::exercise (rating := 3) (name := "filter_exercise") (level := Advanced)
```lean
theorem filter_exercise {α : Type} (test : α → Bool) (a : α) (l lf : List α) :
    filter test l = a :: lf →
    test a = true := by
  solution!
    intro h
    induction l generalizing a lf test
    case nil => contradiction
    case cons hd tl ih =>
      dsimp [filter] at h
      cases h' : (test hd)
      case false =>
        rw [h'] at h
        dsimp at h
        exact ih _ _ _ h
      case true =>
        rw [h'] at h
        dsimp at h
        injections h1 h2
        rw [← h1]
        assumption
```

:::gradeTheorem 3 filter_exercise
:::
:::::

:::::exercise (rating := 4) (name := "forall_exists_challenge") (level := Advanced)
Define two recursive `Fixpoints`, `forallb` and `existsb`.  The
first checks whether every element in a list satisfies a given
predicate:

```display
forallb Nat.odd [1,3,5,7,9] = true
forallb negb [false,false] = true
forallb Nat.even [0,2,4,5] = false
forallb (beq 5) [] = true
```

The second checks whether there exists an element in the list that
satisfies a given predicate:

```display
existsb (beq 5) [0,2,3,6] = false
existsb (andb true) [true,true,false] = true
existsb Nat.odd [1,0,0,0,0,3] = true
existsb even [] = false
```

Next, define a _nonrecursive_ version of `existsb` -- call it
`existsb'` -- using `forallb` and `negb`.

Finally, prove a theorem `existsb_existsb'` stating that
`existsb'` and `existsb` have the same behavior.

```lean
def forallb {α : Type} (test : α → Bool) (l : List α) : Bool := solution!(
  match l with
  | [] => true
  | x :: l' => (test x) && (forallb test l'))

example : forallb (Nat.odd) [1,3,5,7,9] = true := solution!(by rfl)
example : forallb not [false,false] = true := solution!(by rfl)
example : forallb (Nat.even) [0,2,4,5] = false := solution!(by rfl)
example : forallb (· == 5) [] = true := solution!(by rfl)

def existsb {α : Type} (test : α → Bool) (l : List α) : Bool := solution!(
  match l with
  | [] => false
  | x :: l' => (test x) || (existsb test l'))

example : existsb (· == 5) [0,2,3,6] = false := solution!(by rfl)
example : existsb (· && true) [true,true,false] = true := solution!(by rfl)
example : existsb (Nat.odd) [1,0,0,0,0,3] = true := solution!(by rfl)
example : existsb (Nat.even) ([] : List Nat) = false := solution!(by rfl)

def existsb' {α : Type} (test : α → Bool) (l : List α) : Bool := solution!(
  !(forallb (fun x => !(test x)) l))

theorem existsb_existsb' (α : Type) (test : α → Bool) (l : List α) :
    existsb test l = existsb' test l := by
  solution!
    induction l generalizing test
    case nil => rfl
    case cons hd tl ih =>
      dsimp [existsb]
      rw [ih]
      dsimp [existsb', forallb]
      rw [Bool.not_and, Bool.not_not]
```

:::gradeTheorem 6 existsb_existsb'
:::
:::::

:::dev PotentialImprovement
```
Another nice exercise would be to show how to
define forallb in terms of fold, as in...
   Complete the following definition of `every` as a recursive function:
      Definition forallb' (X:Type) (p:X → Bool) (l:list X) : Bool :=
        fold _ _
          (fun x acc => both_yes _________  __________) ________  _________.
```
:::
::::::

::::hide
```
-- Solutions to the above.

def forallbF {X : Type} (test : X → Bool) (l : List X) : Bool :=
  fold (fun x b => (test x) && b) l true

def existsbF {X : Type} (test : X → Bool) (l : List X) : Bool :=
  fold (fun x b => (test x) || b) l false

theorem existsbF_existsb {α : Type} (test : α → Bool) (l : List α) :
    existsbF test l = existsb test l := by
  unfold existsbF
  induction l
  case nil => rfl
  case cons hd tl ih =>
    dsimp [existsb, fold]
    rw [ih]
```
::::
