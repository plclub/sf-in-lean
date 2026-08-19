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
and lemmas whose types are implications.
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

::::full
To use the {tactic}`apply` tactic, the (conclusion of the) fact
being applied must match the goal exactly (perhaps after
simplification) — for example, {tactic}`apply` will not work if the left
and right sides of the equality are swapped.
::::

:::slidebreak
:::

::::terse
The goal must match the hypothesis _exactly_ for {tactic}`apply` to
work:
::::

```lean
example (n m : Nat) (h : n = m) : m = n := by
  -- Here we cannot use `apply` directly...
  /- ...but we can use the `symm` tactic, which switches the left
      and right sides of an equality in the goal. -/
  symm
  apply h
```

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
  rw [Nat.pred_succ]
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
The principle of disjointness says that two terms beginning
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

Notice that due to the way addition on naturals is defined, deriving a contradiction from `1 + n = 0` is not as trivial as it seems.

```lean +error -keep
example (n : Nat)
    (h : 1 + n = 0) :
    2 + 2 = 5 := by
  contradiction -- doesn't work because `1 + n` doesn't reduce to `n.succ`.
```

::::full
If you find the principle of explosion confusing, remember
that these proofs are _not_ simply showing that the conclusion of the
statement holds.  Rather, they are showing that, _if_ the
nonsensical situation described by the premise did somehow hold,
_then_ the nonsensical conclusion would hold too (because we'd be
living in an inconsistent universe where every statement is true).

We'll explore the principle of explosion in more detail in the
{ref "Logic"}[next chapter].
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
    x = y := by
  injection h with hxy
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
example (x y : Nat) (h : 1 + x = 1 + y) : y = x := by
  injection h with hxy
```

```leanOutput qz4
Tactic `injection` failed: equality of constructor applications expected

x y : Nat
h : 1 + x = 1 + y
⊢ y = x
```

The addition in `1 + x` (and `1 + y`) is blocked by the variable in the second argument.
Therefore it doesn't reduce to `x.succ`, so injectivity of constructors can't be used directly.
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

:::dev "Niklas Halonen (xhalo32)"
The above proof can be made simpler by just rewriting before the `congr`, so arguably it doesn't require limiting the depth.
```lean
example (a b c d : Nat) (hab : a = b) (hcd : c = d) :
    (a, c + 1) = (b, 1 + d) := by
  rw [Nat.add_comm]
  congr
```
:::

# Using {tactic}`apply` on Hypotheses

::::full
The tactic `apply t at h` matches an implication `t`
(say, of the form `a → b`) against a hypothesis `h` in the local
context. Unlike ordinary {tactic}`apply`, which matches the goal against `b`
and replaces it with the subgoal `a`), `apply t at h` matches the type of `h`
against `a` and, if successful, replaces `h` with a hypothesis of type `b`.

In other words, `apply t at h` gives us a form of "forward
reasoning": given `t : a → b` and `h : a`, it replaces `h` with a proof of `b`.

By contrast, ordinary `apply t` is "backward reasoning": given `t : a → b`
and a goal `⊢ b`, it replaces the goal with `⊢ a`.

Here is a proof that uses forward reasoning rather than backward reasoning:
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
  have h := trans_eq (y := [c, d])
  apply h
  /- This tactic closes a goal if it appears anywhere in the context.
     In this case we could also write `exact h₁` ... -/
  assumption
  /- .. and here we could also write `exact h₂` -/
  assumption
```

# Generalizing the Induction Hypothesis

:::ignore
```lean -show
variable (m n m' n' : Nat)
```
:::

Recall this function for doubling a natural number from the
{ref "Induction"}[Induction] chapter:

```display
def Nat.double (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => (n'.double) + 2
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

```lean -keep
theorem double_injective (n m : Nat) (h : n.double = m.double) : n = m := sorry
```

If we begin it with

::::

```lean -keep +error (name := gen1)
theorem double_injective (n m : Nat) (h : n.double = m.double) : n = m := by
  induction n with
  | zero =>
    cases m with
    | zero => rfl
    | succ m' =>
      rw [Nat.double_zero, Nat.double_succ] at h
      contradiction
  | succ n' ih =>
    cases m with
    | zero =>
      rw [Nat.double_zero, Nat.double_succ] at h
      contradiction
    | succ m' =>
      congr
```

```leanOutput gen1
unsolved goals
case succ.succ.e_a
n' m' : Nat
ih : n'.double = (m' + 1).double → n' = m' + 1
h : (n' + 1).double = (m' + 1).double
⊢ n' = m'
```

:::terse
We get stuck, because the induction hypothesis `ih` is too specific to be useful.
:::

::::full
We get stuck — {lean}`m` is fixed during the induction,
so in the successor case the induction hypothesis `ih` is specialized to the current value of {lean}`m`.
After the case split, that value is {lean}`m' + 1`, and the induction hypothesis has the form:

```display
ih : n'.double = (m' + 1).double → n' = m' + 1
```

From `h`, using the definition of {name}`Nat.double` we can obtain

```leanTerm
n'.double = m'.double
```

and to prove the goal we would like to apply an induction hypothesis at `m'`.
Nevertheless, `ih` is specialized to {lean}`m' + 1` — it would require

```leanTerm
n'.double = (m' + 1).double
```

and would conclude

```leanTerm
n' = m' + 1
```

which is not what we need. Instead, we need an induction hypothesis that is general in `m`:

```display
ih : ∀ m, n'.double = m.double → n' = m
```

Then in this branch we can instantiate it with {lean}`m'`.
::::

We can obtain a more generalized induction hypothesis by writing

```display
induction n generalizing m with
```

:::slidebreak
:::

What went wrong?

::::full
The problem is that {lean}`m` is already in the context when we invoke
`induction n`. Since {lean}`m` is an ordinary argument of the theorem,
this is exactly what we normally want — we are considering some particular
{lean}`n` and {lean}`m`, together with the hypothesis {lean}`n.double = m.double` and trying
to prove `n = m`.

The claim itself makes perfect sense, but for the induction, however, keeping {lean}`m` fixed
causes the trouble: we are proving, for _all_ {lean}`n`, the proposition

  - `P n` = "if {lean}`n.double = m.double`, then {lean}`n = m`"

by showing

  - `P 0`

     (i.e., "if {lean}`Nat.double 0 = m.double` then {lean}`0 = m`") and

  - `P n → P (n + 1)`

    (i.e., "if {lean}`n.double = m.double` then {lean}`n = m`" implies "if
    {lean}`(n + 1).double = m.double` then {lean}`n + 1 = m`").

If we look closely at the inductive step, it is saying something
rather strange: that, for a _particular_ {lean}`m`, if we know

  - "if {lean}`n.double = m.double` then {lean}`n = m`"

then we can prove

   - "if {lean}`(n + 1).double = m.double` then {lean}`n + 1 = m`".

To see why this is strange, let's choose of a particular {lean}`m` —
say, `5`.  The statement is then saying that, if we know

  - `Q` = "if {lean}`n.double = 10` then {lean}`n = 5`"

then we can prove

  - `R` = "if {lean}`(n + 1).double = 10` then {lean}`n + 1 = 5`".

But knowing `Q` doesn't give us any help at all with proving `R`.
If we tried to prove `R` from `Q`, we would start with something
like "Suppose {lean}`(n + 1).double = 10`..." but then we would be stuck:
the induction hypothesis `Q` only tells us what happens if {lean}`n.double = 10`,
whereas our assumption says {lean}`(n + 1).double = 10`, so `Q` is useless here.

This is exactly what we saw in the proof state.
::::

Trying to carry out this proof by induction on {lean}`n` with {lean}`m` fixed
doesn't work, because we are then trying to
prove a statement involving _every_ {lean}`n` but just a _particular_
{lean}`m`.

:::slidebreak
:::

A successful proof of `double_injective` _generalizes_ {lean}`m` when carrying out the induction on {lean}`n`,
so that the induction hypothesis holds for every {lean}`m`,
rather than for just the particular {lean}`m` in the context.

```lean
theorem double_injective (n m : Nat) (h : n.double = m.double) : n = m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m' => contradiction
  | succ n' ih =>
    cases m with
    | zero => contradiction
    | succ m' =>
      congr
      apply ih -- now works
      rw [Nat.double_succ, Nat.double_succ] at h
      injections
```

:::slidebreak
:::

::::full
Let's look at an informal proof of this theorem.  Notice that
the induction hypothesis is generalized over {lean}`m`, corresponding to
the use of `generalizing m`.

_Theorem_: For any natural numbers {lean}`n` and {lean}`m`, if {lean}`n.double = m.double`, then
  {lean}`n = m`.

_Proof_: We prove by induction on {lean}`n` that, for _any_ {lean}`m`,
  if {lean}`n.double = m.double` then {lean}`n = m`.

  - First, suppose {lean}`n = 0`. We must show that, for any {lean}`m`, if
    {lean}`Nat.double 0 = m.double`, then {lean}`0 = m`.

    There are two cases to consider for {lean}`m`:
    1. If {lean}`m = 0`, we are done.
    2. Otherwise if {lean}`m = m' + 1` for some {lean}`m'`, then by definition of {name}`Nat.double`
       we have `Nat.double 0 = 0` and `(m' + 1).double = m'.double + 2`.
       Clearly {lean}`0` cannot equal {lean}`m'.double + 2`, so this case is impossible.

  - Second, suppose {lean}`n = n' + 1`. The induction hypothesis says that, for every {lean}`m`,
    if {lean}`(n' + 1).double = m.double` then {lean}`n' + 1 = m`. Again there are two cases
    to consider for {lean}`m`:
    1. If {lean}`m = 0`, then by the definition of {name}`Nat.double` our assumption says
       {lean}`n'.double + 2 = 0`, which is impossible.
    2. Otherwise suppose {lean}`m = m' + 1`.
       Our assumption is then that {lean}`(n' + 1).double = (m' + 1).double`.
       By the definition of {name}`Nat.double`, this gives `n'.double + 2 = m'.double + 2`.
       By injectivity of {name}`Nat.succ`, we obtain {lean}`n'.double = m'.double`.
       We can now instantiate the induction hypothesis with {lean}`m'`, obtaining `n' = m'`.
       Now we can conclude `n' + 1 = m' + 1`, which is exactly what we wanted to show.

_Qed_.
::::

The thing to take away from all this is that you need to be
careful, when using induction, that your induction hypothesis
is not too specific. When proving a proposition quantified over
variables `n` and `m` by induction on `n`, it is sometimes crucial
to _generalize_ `m`, so that the induction hypothesis applies to every `m`
rather than just the particular `m` in the context.


:::::exercise (rating := 3) (name := "add_self_injective")

The following theorem follows the same pattern as {name}`double_injective`.

```lean
theorem add_self_injective (n m : Nat)
    (h : n + n = m + m) :
    n = m := by
  solution!
    induction n generalizing m with
    | zero =>
      cases m with
      | zero => rfl
      | succ m' => dsimp at h; contradiction
    | succ n' ih =>
      cases m with
      | zero => dsimp at h; contradiction
      | succ m' =>
        congr
        apply ih
        rw [Nat.add_succ, Nat.add_succ (m' + 1)] at h
        injection h with h
        rw [Nat.add_comm, Nat.add_comm (m' + 1)] at h
        injections h
```

:::gradeTheorem 3 add_self_injective
:::
:::::

::::exercise (rating := 2) (name := "add_self_injective_informal")
Give a careful informal proof of {name}`add_self_injective`, stating the induction
hypothesis explicitly and being as explicit as possible about
quantifiers, everywhere.

:::solution
_Theorem_: For any natural numbers {lean}`n` and {lean}`m`, if {lean}`n + n = m + m`, then
  {lean}`n = m`.
_Proof_: We prove by induction on {lean}`n` that for _every_ natrual number {lean}`m`,
  if {lean}`n + n = m + m`, then `n = m`.

  - First, suppose that {lean}`n = 0`. We must show that for every `m`, if {lean}`0 + 0 = m + m` then
    {lean}`0 = m`. There are two cases for {lean}`m`. If {lean}`m = 0`, we are done.
    Otherwise {lean}`m = m' + 1` for some {lean}`m'`.
    Then {lean}`m + m` cannot equal {lean}`0 + 0`. Thus this case is impossible.
  - Now suppose that {lean}`n = n' + 1`.
    The induction hypothesis says that, for every natrual number {lean}`m`,
    {lean}`n' + n' = m + m` implies {lean}`n' = m`.
    We must show, for every {lean}`m`, that {lean}`(n' + 1) + (n' + 1) = m + m`
    implies {lean}`n' + 1 = m`. Again there are two cases for {lean}`m`.
    If {lean}`m = 0`, then the assumed equality is impossible — {lean}`(n' + 1) + (n' + 1)`
    cannot equal to `0`. Otherwise {lean}`m = m' + 1` for some {lean}`m'`.
    Cancelling one successor from each side of the equality and rearranging the additions gives
    {lean}`n' + n' = m' + m'`. We can now apply the induction hypothesis with {lean}`m'` to obtain {lean}`n' = m'`.
    Then it follows that {lean}`n' + 1 = m' + 1`, which is our final goal.

_Qed_.
:::

::::


# Rewriting with Conditional Statements

:::full

Suppose that we know two numbers have the same double, and we want to
use this fact to rewrite one of them into the other. Recall the theorem
{name}`double_injective` from the previous section:

```lean (name := double_injective)
#check double_injective
```

```leanOutput double_injective
double_injective (n m : Nat) (h : n.double = m.double) : n = m
```

For example, we can prove:

:::

```lean
example (n m p q : Nat)
    (h : n.double = m.double)
    (hm : m + p = q) :
    n + p = q := by
  rw [double_injective n m]
  · assumption
  · assumption
```

:::full
The use of `rw` here is a little different from the examples we have seen so far.
The theorem {name}`double_injective` says {lean}`n = m`
_provided that_ {lean}`n.double = m.double`, not just {lean}`n = m`.
When we write `rw [double_injective n m]`, Lean uses the conclusion {lean}`n = m` to rewrite
the goal, and then asks us to prove the hypothesis needed by {name}`double_injective`.
Thus we get two goals: the updated main goal, `m + p = q`, which follows from `hm`, and the
condition from {name}`double_injective`, {lean}`n.double = m.double`, whicch follows from `h`.
:::

If we rewrite with a conditional statement of the form
`P → a = b`, then Lean tries to rewrite with `a = b`, and then
asks us to prove `P` in a new subgoal.  If the statement has more
than one assumption, then we get one subgoal for each assumption.

:::::exercise (rating := 3) (name := "nth?_after_last")
Prove this by induction on `l`.

```lean
theorem nth?_after_last {α : Type}
    {n : Nat} {l : List α} (h : l.length = n) :
    nth? l n = none := by
  solution!
    induction l generalizing n with
    | nil => rfl
    | cons x xs ih =>
      rw [List.length_cons] at h
      rw [← h]
      dsimp [nth?]
      apply ih
      rfl
```

:::gradeTheorem 3 nth?_after_last
:::
:::::

:::::exercise (rating := 3) (name := "length_append_cons")

Prove this by induction on `l₁`, without using {name}`List.length_append`.

```lean
theorem length_append_cons {α : Type} {l₁ l₂ : List α} {x : α} {n : Nat}
    (h : (l₁ ++ (x :: l₂)).length = n) :
    ((l₁ ++ l₂).length) + 1 = n := by
  solution!
    induction l₁ generalizing n with
    | nil => assumption
    | cons y ys ih =>
      rw [List.cons_append, List.length_cons] at *
      /- A trick here: by using `rfl` to close `(ys ++ x :: l₂).length = n`
         we effectively choose `n` to be `(ys ++ x :: l₂).length`
      -/
      rw [ih rfl]
      assumption
```

:::gradeTheorem 3 length_append_cons
:::
:::::

:::::exercise (rating := 3) (name := "length_append_self")

Prove this by induction on `l₁`, without using {name}`List.length_append`.
Hint: you might need to use {name}`length_append_cons` you just proved.

```lean
theorem length_append_self {α : Type} {n : Nat} {l : List α}
    (h : l.length = n) :
    (l ++ l).length = n + n := by
  induction l generalizing n with
  | nil =>
    rw [List.append_nil,  List.length_nil] at *
    rw [← h]
  | cons x xs ih =>
    rw [List.cons_append, List.length_cons] at *
    rw [← length_append_cons rfl]
    rw [ih rfl, ← h]
    rw [Nat.add_add_add_comm]
```

:::gradeTheorem 3 length_append_self
:::
:::::

:::::exercise (rating := 3) (name := "diagonal_induction")

Prove the following principle of induction over two naturals.

```lean

theorem diagonal_induction (p : Nat → Nat → Prop)
    (hzz : p 0 0)
    (hsz : ∀ m, p m 0 → p (m + 1) 0)
    (hzs : ∀ n, p 0 n → p 0 (n + 1))
    (hss : ∀ m n, p m n → p (m + 1) (n + 1)) :
    ∀ m n, p m n := by
  solution!
    intro m n
    induction m generalizing n with
    | zero =>
      induction n with
      | zero => exact hzz
      | succ n' ih =>
        apply hzs
        apply ih
    | succ m' ih =>
      induction n with
      | zero =>
        apply hsz
        apply ih
      | succ n' ih' =>
        apply hss
        apply ih
```

:::gradeTheorem 3 diagonal_induction
:::
:::::

# Using {tactic}`cases` on Expressions

::::full
We have seen many examples where {tactic}`cases` is used to
perform case analysis of the value of some variable.  Sometimes we
need to reason by cases on the result of some _expression_.  We
can also do this with {tactic}`cases`.

Here are some examples:
::::

::::terse
The {tactic}`cases` tactic can be used on expressions as well as
variables:
::::

```lean
def chooseIf {α : Type} (test : α → Bool) (x y : α) : α :=
  if test x then x else y

theorem chooseIf_self {α : Type} (test : α → Bool) (x : α) :
    chooseIf test x x = x := by
  dsimp [chooseIf]
  cases test x <;> rfl
```

::::full
After _unfolding_ {name}`chooseIf` in the above proof, we find that
we are stuck on `(if test x = true then x else x) = x`.  But either
`test x` is `true` or it isn't,
so we can use `cases (test x)` to let us reason about the two cases.

In general, the {tactic}`cases` tactic can be used to perform case
analysis of the results of arbitrary computations.  If `e` is an
expression whose type is some inductively defined type `T`, then,
for each constructor `c` of `T`, `cases e` generates a subgoal
in which all occurrences of `e` (in the goal and in the context)
are replaced by `c`.
::::

## Destructing Tuples

{tactic}`cases` is useful when we are dealing with inductively defined types
that can be one thing or another; a {name}`Bool` is either a {name}`false` or a {name}`true`,
and a {name}`Nat` is either `0` or `succ n`. When we want more information about
inductively defined types that are products of multiple things, we instead
want a way to get the pieces of that value out from it.

When we have a value `v : α × β` in our context, we can
get the first and second projections of `v` using this tactic:

```display
let ⟨a, β⟩ := v
```

:::::exercise (rating := 3) (name := "zip_unzip")
Here is an implementation of the {name}`unzip` function mentioned in
chapter {ref "Poly"}[Poly]:

```display
def unzip {α : Type} {β : Type} (l : List (α × β)) : List α × List β := solution!(
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    let (lx, ly) := unzip t
    (x :: lx, y :: ly))
```

Prove that {name}`unzip` and {name}`zip` are inverses in the following sense:

```lean
theorem zip_unzip {α β : Type} (l : List (α × β))
    (l₁ : List α) (l₂ : List β)
    (h : unzip l = (l₁, l₂)) :
    zip l₁ l₂ = l := by
  solution!
    induction l generalizing l₁ l₂ with
    | nil =>
      rw [unzip_nil] at h
      injections h₁ h₂
      rw [← h₁, ← h₂]
      rfl
    | cons x xs ih =>
      let ⟨a, b⟩ := x
      dsimp [unzip] at h
      injections h₁ h₂
      rw [← h₁, ← h₂]
      dsimp [zip]
      rw [ih]
      rfl
```

:::gradeTheorem 3 zip_unzip
:::

:::::

## Splitting with Equations

When using {tactic}`cases`, we can specify to Lean that it should
remember an equality between a compound expression and what we are
decomposing it into, using `cases h : ...` syntax. This information
can actually be critical, and, if we leave it out, we might lack
information we need to complete a proof.

::::full
For example, suppose we define a function `keepIf` like this:
::::

```lean
def keepIf {α : Type} (test : α → Bool) (x : α) : Option α :=
  if test x then some x else none
```

::::full
Now suppose that we want to prove `keepIf_some`. If we start the proof like
this (with no `h : ⋯` on the `cases`)...

```lean +error -keep (name := keepIf_some_e)
theorem keepIf_some {α : Type} (test : α → Bool) (x y : α)
    (h : keepIf test x = some y) :
    x = y := by
  dsimp [keepIf] at h
  cases (test x)
```

```leanOutput keepIf_some_e
unsolved goals
case false
α : Type
test : α → Bool
x y : α
h : (if test x = true then some x else none) = some y
⊢ x = y

case true
α : Type
test : α → Bool
x y : α
h : (if test x = true then some x else none) = some y
⊢ x = y
```

... then we are stuck at this point because the context does
not contain enough information to prove the goal.
Because `test x` appears in our hypothesis, rather than in our
goal, `cases (test x)` does not automatically replace the expression
with {name}`false` or {name}`true` like it did during the proof of {name}`chooseIf`.
We want to add an equation to the context that records which case we are in.
This is precisely what the
`h : ⋯` qualifier does.
::::

:::slidebreak
:::

:::terse
Adding the `h : ⋯ ` qualifier saves this information so we can use it.
:::

```lean
theorem keepIf_some {α : Type} (test : α → Bool) (x y : α)
    (h : keepIf test x = some y) :
    x = y := by
  dsimp [keepIf] at h
  cases hTest : test x
  -- Now we have the same state as at the point where we got stuck
  -- above, except that the context contains an extra equality
  -- assumption, which is exactly what we need to make progress.
  · rw [hTest] at h
    contradiction
  · rw [hTest] at h
    injections
```

::::::full
:::::exercise (rating := 2) (name := "bool_fn_iterate_three_eq_one")
```lean
theorem bool_fn_iterate_three_eq_one (f : Bool → Bool) (b : Bool) :
    f (f (f b)) = f b := by
  solution!
    cases b with
    | false =>
      cases h₁ : f false with
      | false => rw [h₁]; assumption
      | true =>
        cases h₂ : f true with
        | false => assumption
        | true => assumption
    | true =>
      cases h₁ : f true with
      | false =>
        cases h₂ : f false with
        | false => assumption
        | true => assumption
      | true => rw [h₁]; assumption
```

:::gradeTheorem 2 bool_fn_iterate_three_eq_one
:::
:::::

::::::

# Review

:::suppressPreviousHeaderWhenTerse
:::

::::full
We've now talked about many of Lean's most fundamental tactics.
We'll introduce a few more in the coming chapters, and later on
we'll see some more powerful _automation_ tactics that make Lean
help us with low-level details.  But basically we've got what we
need to get work done.

Here are the ones we've seen so far.

Managing goals and hypotheses:

  - `intro h`: move an assumption/quantified variable from the goal into the local context

  - `apply thm`: use a theorem, hypothesis, or constructor whose conclusion matches the goal;
     its premises become new goals

  - `apply thm at h`: use a theorem on a hypothesis in the context, replacing `h` by the resulting

    fact (forward reasoning)

  - `specialize h ...`: instantiate quantified variables in a hypothesis, modifying `h` in place

  - `replace h := ...`: replace a hypothesis with a newly proved fact

  - `have h : P := ...`: prove a local fact `P` and add it to the context with the name `h`

  -  `contradiction`: close the current goal when the context contains contradictory assumptions

Equality and rewriting:

  - `rfl`: close an equality that holds by reflexivity (possibly after computation)

  - `rw [h]`: rewrite the goal using an equality hypothesis or theorem

  - `rw [h] at h'`: rewrite a hypothesis using an equality hypothesis or theorem

  - `symm`: reverse an equality goal, changing `t = u` to `u = t`

  - `symm at h`: reverse an equality hypothesis

  - `calc`: prove a goal about equality or another transitive relation by
    giving a sequence of intermediate steps

  - `congr`: use congruence to reduce an equality between expressions with the same outer form;
    for example, a goal `f x = f y` may be reduced to `x = y`

  - `injection h with ...`: use injectivity of constructors to extract equalities from constructor applications equations

  - `injections`: repeatedly use constructor injectivity on suitable equalities in the context

Simplifying and unfolding definitions:

  - `dsimp`: simplify definitional computations in the goal

  - `dsimp at h`: simplify definitional computations in a hypothesis

Case analysis:

  - `cases x`: reason separately about the possible constructors of an inductively defined value

  - `cases h : e`: perform case analysis on an expression `e` and add an equation named `h`
    recording the result of the case analysis

Induction:

  - `induction x`: prove the goal by induction on an inductively defined value

  - `induction x generalizing y`: induction on `x` while generalizing the listed local variables,
    giving a more general induction hypothesis
::::

## Additional Exercises

:::::exercise (rating := 2) (name := "append_left_cancel")
:::dev "Niklas Halonen (xhalo32)"
After `injections _ eq`, `eq`'s type uses `.append` rather than `++` which is a bit confusing.
Not sure why that happens.
:::
```lean
theorem append_left_cancel {α : Type} (l₁ l₂ l₃ : List α)
    (h : l₁ ++ l₂ = l₁ ++ l₃) :
    l₂ = l₃ := by
  solution!
    induction l₁ with
    | nil => assumption
    | cons x xs ih =>
      injections _ eq
      exact ih eq
```
:::gradeTheorem 2 append_left_cancel
:::
:::::

:::::exercise (rating := 3) (name := "map_injective_of_injective")

Recall the {name}`map` we've defined in {ref "Poly"}[Poly]:

```display
def map {α : Type} {β : Type} (f : α → β) (l : List α) : List β :=
  match l with
  | [] => []
  | head :: tail => f head :: map f tail
```

Prove that {name}`map` is injective whenever the function is injective.

```lean
theorem map_injective_of_injective {α β : Type}
    (f : α → β)
    (hf : ∀ x y, f x = f y → x = y)
    (l₁ l₂ : List α)
    (h : map f l₁ = map f l₂) :
    l₁ = l₂ := by
  solution!
    induction l₁ generalizing l₂ with
    | nil =>
      cases l₂ with
      | nil => rfl
      | cons y ys =>
        rw [map_cons, map_nil] at h
        contradiction
    | cons x xs ih =>
      cases l₂ with
      | nil =>
        rw [map_cons, map_nil] at h
        contradiction
      | cons y ys =>
        rw [map_cons, map_cons] at h
        injection h with hxy hxs
        rw [hf x y hxy, ih ys hxs]
```
:::gradeTheorem 3 map_injective_of_injective
:::
:::::


:::::exercise (rating := 3) (name := "unzip_zip") (level := Advanced) (manual := true)
We proved {name}`zip_unzip` that {name}`zip`ping the result of {name}`unzip` recovers the original list. What about the other direction?  Complete and prove the following `unzip_zip`:

```display
theorem unzip_zip {α β : Type}
    {l₁ : List α} {l₂ : List β}
    /- add appropriate parameters and hypotheses here -/ :
    unzip (zip l₁ l₂) = (l₁, l₂) := sorry
```

Hint: Take a look at the definition of {name}`zip` in {ref "Poly"}[Poly].
Your definition will need to account for the behavior of {name}`zip`
in its base cases, which possibly drop some list elements.

```lean
-- SOLUTION
theorem unzip_zip {α β : Type}
    {l₁ : List α} {l₂ : List β}
    (h : l₁.length = l₂.length) :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons => contradiction
  | cons x xs ih =>
    cases l₂ with
    | nil => contradiction
    | cons y ys =>
      rw [zip_cons_cons]
      dsimp [unzip]
      rewrite [ih]
      · rfl
      · injections

/- Here is one more approach -/
theorem unzip_zip' {α β : Type}
    {l₁ : List α} {l₂ : List β}
    {l : List (α × β)} (h : (l₁, l₂) = unzip l) :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  induction l generalizing l₁ l₂ with
  | nil =>
    rw [unzip_nil] at h
    injections h₁ h₂
    rw [h₁, h₂]
    rfl
  | cons x xs ih =>
    let ⟨a, b⟩ := x
    dsimp [unzip] at h
    injections h₁ h₂
    rw [h₁, h₂]
    dsimp [zip, unzip]
    rewrite [ih]
    · rfl
    · rfl
-- END SOLUTION
```

:::::

:::::exercise (rating := 3) (name := "test_pos_of_filter_cons") (level := Advanced)
```lean
theorem test_pos_of_filter_cons {α : Type}
    (test : α → Bool) (x : α) (l l' : List α)
    (h : filter test l = x :: l') :
    test x = true := by
  solution!
    induction l generalizing x l' test with
    | nil => contradiction
    | cons y ys ih =>
      dsimp [filter] at h
      cases hy : (test y)
      · rw [hy] at h
        dsimp at h
        exact ih _ _ _ h
      · rw [hy] at h
        dsimp at h
        injections h1 h2
        rw [← h1]
        exact hy
```

:::gradeTheorem 3 test_pos_of_filter_cons
:::
:::::

:::::exercise (rating := 4) (name := "forall_exists_challenge") (level := Advanced)
Define two recursive functions, `allTrue` and `anyTrue`.

The first checks whether the given Boolean test returns {name}`true` for every element of the list.

```lean
def allTrue {α : Type} (test : α → Bool) (l : List α) : Bool := solution!(
  match l with
  | [] => true
  | x :: xs => (test x) && (allTrue test xs))

example : allTrue Nat.odd [1, 3, 5, 7, 9] = true := solution!(by rfl)
example : allTrue not [false, false] = true := solution!(by rfl)
example : allTrue Nat.even [0, 2, 4, 5] = false := solution!(by rfl)
example : allTrue Nat.even [] = true := solution!(by rfl)
```

The second checks whether it returns {name}`true` for at least one element.

```lean
def anyTrue {α : Type} (test : α → Bool) (l : List α) : Bool := solution!(
  match l with
  | [] => false
  | x :: xs => (test x) || (anyTrue test xs))

example : anyTrue Nat.even [1, 3, 4, 7] = true := solution!(by rfl)
example : anyTrue Nat.odd [0, 2, 4, 6] = false := solution!(by rfl)
example : anyTrue not [true, true, false] = true := solution!(by rfl)
example : anyTrue Nat.even [] = false := solution!(by rfl)
```

Next, define a _nonrecursive_ version of {name}`anyTrue` — call it
`anyTrue'` — using {name}`allTrue` and {name}`not`.

```lean
def anyTrue' {α : Type} (test : α → Bool) (l : List α) : Bool := solution!(
  !(allTrue (fun x => !(test x)) l))
```

Finally, prove a theorem `anyTrue_eq_anyTrue` stating that
`anyTrue'` and `anyTrue` have the same behavior.

```lean
theorem anyTrue_eq_anyTrue (α : Type) (test : α → Bool) (l : List α) :
    anyTrue test l = anyTrue' test l := by
  solution!
    induction l generalizing test with
    | nil => rfl
    | cons x xs ih =>
      dsimp [anyTrue]
      rw [ih]
      dsimp [anyTrue', allTrue]
      rw [Bool.not_and, Bool.not_not]
```

:::gradeTheorem 6 anyTrue_eq_anyTrue
:::
:::::
