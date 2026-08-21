import SFLMeta

import LF.IndProp

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Automation: More Automation" =>
%%%
tag := "Automation"
htmlSplit := .never
file := "Automation"
%%%

::::full
Up to now, we've used the manual part of Lean's tactic
facilities.  In this chapter, we'll learn more about some of
Lean's powerful automation features, including
tactic combinators like {tactic}`try` and {tactic}`repeat`, decision procedures like {tactic}`lia`,
and automatic simplification using {tactic}`simp`.
Using these features together with Lean's metaprogramming facilities will enable us to make
some of our proofs startlingly short!  Used properly, they can
also make proofs more maintainable and robust to changes in
underlying definitions.

Our motivating example will be the following proof, repeated with
just a few small changes from the {ref "IndProp"}[IndProp] chapter.  We will
simplify this proof in several stages.
::::

::::terse
Consider the proof below. Notice all the repetition and near-repetition...
::::

```lean
theorem Perm3_In_old (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm with
  | perm3_swap12 =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
    obtain h | h | h | h := hIn
    . right; left; assumption
    . left; assumption
    . right; right; left; assumption
    . contradiction
  | perm3_swap23 =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
    obtain h | h | h | h := hIn
    . left; assumption
    . right; right; left; assumption
    . right; left; assumption
    . contradiction
  | perm3_trans _ _ ih₁₂ ih₂₃ =>
    apply ih₂₃; apply ih₁₂; apply hIn
```

In this file, we will introduce tactics that will shrink this proof from
around eighteen lines to two.

# The {tactic}`lia` Tactic

::::full
The {tactic}`lia` tactic implements a decision procedure for integer linear
arithmetic, a subset of propositional logic and arithmetic. {tactic}`lia`
is also a decision procedure for first-order logic.
:::dev "@rogerburtonpatel"
Should we explain first-order logic? do they know what this is?
:::

If the goal is a universally quantified formula made out of

  - numeric constants, addition (`+` and `succ`), subtraction (`-` and `pred`)
    and multiplication by constants (this is what makes it Presburger arithmetic),

  - equality (`=` and `≠`) and ordering (`≤` and `<`), and

  - the logical connectives `∧`, `∨`, `¬`, and `→`,

then invoking {tactic}`lia` will either solve the goal or fail, meaning
that the goal is actually false.  If the goal is _not_ of this
form, {tactic}`lia` will fail. Note that when failing, {tactic}`lia`, may mention
another tactic, called {tactic}`grind`. This is another, more powerful tactic
that implements {tactic}`lia`, but we will not use it here.
::::

```lean
example (m n o p : Nat) :
    m + n ≤ n + o ∧ o + 3 = p + 3 →
    m ≤ p := by
  lia

example (m n : Nat) :
    m + n = n + m := by
  lia

example (m n p : Nat) :
    m + (n + p) = m + n + p := by
  lia

example (a b c d : Prop) :
    (a → b) → (b → c) → (c → d) → (a → d) := by
  lia
```

{tactic}`lia` can solve many of the cases of our old {name}`Perm3.In` example.

```lean
theorem Perm3_In_better_with_lia (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm with
  | perm3_swap12 =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
    obtain h | h | h | h := hIn
    /- In addition to basic arithmetic, `lia` can also discharge goals
      that are simple facts about logic. -/
    . lia -- was right; left; assumption
    . lia
    . lia
    . lia
  | perm3_swap23 =>
  /- Here, we solve _all_ goals ─ and eschew the `obtain` ─ with
    the <;> tactic combinator, which we saw in the `Induction` chapter. -/
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia
  | perm3_trans _ _ ih₁₂ ih₂₃ =>
    lia -- was apply ih₂₃; apply ih₁₂; apply hIn
```

# Tactic Combinators

::::full
In {ref "Induction"}[Induction], we saw how to use the {tactic}`<;>` combinator in order to apply the same
tactic to every subgoal in a proof. As a reminder, consider this example,
where {tactic}`cases` on `b` and `c` each leaves two subgoals that are discharged identically:
::::

::::terse
Recall the `<;>` combinator...
::::

```lean
example (b c : Bool) : (b && c) = (c && b) := by
  cases b <;> cases c <;> rfl
```

::::full
This `<;>` is not the only such combinator that Lean has to offer, however.
In general, combinators allow us to build tactics out of smaller ones, letting us
discharge many similar subgoals at once. Getting used to them takes a
little energy, but it lets us scale up to more complex definitions and
more interesting properties without drowning in boring, repetitive detail.
::::

:::dev "Benjamin Pierce (bcpierce00)"
```
INCOMING BOCHUM MATERIAL summarized by Claude (old/bochum-lf-updates/AltAuto.v): the
   Bochum LF updates extend AltAuto's discussion of the sequencing
   tactical with new material on Rocq's "local form with `..`":

     T; [T1 .. | Tn]

   which applies T1 to the first goal, Tn to the last, and T1 to all
   goals in between (variants: T; [T1 | .. | Tn] applies nothing in
   between; the `..` may also appear first, last, or alone).  The new
   material illustrates this by revisiting star_app from IndProp:

     Lemma star_app'': forall T (s1 s2 : list T) (re : reg_exp T),
       s1 =~ Star re ->
       s2 =~ Star re ->
       s1 ++ s2 =~ Star re.
     Proof.
       intros T s1 s2 re H1.
       remember (Star re) as re' eqn:Eq.
       induction H1
         as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
             |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
             |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2];
         [discriminate .. | intros H; apply H | idtac]. (* <=== *)
       (* MStarApp *)
       intros H1. rewrite <- app_assoc.
       apply MStarApp.
       + apply Hmatch1.
       + apply IH2.
         * apply Eq.
         * apply H1.
     Qed.

   (first shown in its long form with all seven cases spelled out, then
   shortened as above).  Bochum also adds a QUIETSOLUTION alternate
   solution to AltAuto's re_opt exercise that uses nested `..` lists
   instead of `try`, and rewords the introduction of `T; T'` to say
   simply that it is "equivalent to locally performing T' on all the
   subgoals".

   To incorporate: Lean has no direct analogue of the positional
   `[T1 .. | Tn]` goal-selector list; the closest idioms are
   case-labelled alternatives (`case ... =>`/`next`), `all_goals`,
   and `first`.  A future pass should decide whether to add a
   parallel discussion here (e.g. using `star_app` below, proving the
   six non-MStarApp cases uniformly) or to record the Rocq material
   as intentionally unported.
```
:::

## The {tactic}`try` Combinator

::::full
The first such combinator we'll discuss is {tactic}`try`. If `t` is a tactic,
then `try t` is a tactic that is just like `t`
except that, if `t` fails, `try t` _successfully_ does nothing at all
(rather than failing).
::::

::::terse
The {tactic}`try` combinator allows tactics to fail.
::::

```lean
example {a : Prop} (h : a) : a := by
  try rfl -- `rfl` would fail here, but `try` swallows the failure...
  exact h -- ...so we can still finish some other way.

example : 1 = 1 := by
  try rfl -- here `try rfl` just does `rfl`
```

::::full
There is not much reason to use {tactic}`try` in completely manual proofs like
these, but it is very useful together with the {tactic}`<;>` combinator.
::::

```lean
inductive silly : Nat → Prop where
| mk1 n (h : n > 1) : silly n
| mk2 n (h : 1 ∈ []) : silly n
| mk3 n (h : ∃ m, n = m + 2) : silly n

example {n} (h : silly n) : n ≠ 1 := by
  inversion h with
  | mk1 => lia
  | mk2 => contradiction
  | mk3 => lia
```

::::full
Here, we can use the {tactic}`lia` tactic to close some of these goals, but not all of them. So,
a more compact way to write this proof would be:
::::

::::terse
The {tactic}`try` and {tactic}`<;>` combinators used together allow you to use a tactic to some,
but not all, goals...
::::

```lean
example {n} (h : silly n) : n ≠ 1 := by
  cases h <;> try lia
  -- `lia` doesn't know that `1 ∈ []` is impossible, but we can use `contradiction`
  contradiction
```

We can further simplify our {name}`Perm3.In` example with {tactic}`try`.

```lean
theorem Perm3_In_better_with_try (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm with (try rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia)
  | perm3_trans => lia
```

Note that `try lia <;> try rw [...] <;> lia` _doesn't_ work, because
the first time that {tactic}`try` catches a failure in a {tactic}`<;>` sequence, the whole
sequence will stop executing.

```lean +error (name := Perm3_try)
example (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm <;> try lia <;>
    try rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia
```

```leanOutput Perm3_try
unsolved goals
case perm3_swap12
α : Type
x : α
l₁ l₂ : List α
x✝ y✝ z✝ : α
hIn : x ∈ [x✝, y✝, z✝]
⊢ x ∈ [y✝, x✝, z✝]

case perm3_swap23
α : Type
x : α
l₁ l₂ : List α
x✝ y✝ z✝ : α
hIn : x ∈ [x✝, y✝, z✝]
⊢ x ∈ [x✝, z✝, y✝]
```

## The {tactic}`repeat` Combinator

The {tactic}`repeat` combinator takes another tactic or parenthesized sequence of tactics
and keeps applying it until it fails.

Here is an example proving that {lean}`10` is in a long list using {tactic}`repeat`:

```lean
example : 10 ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  repeat
    rw [List.mem_cons]
    try left; rfl
    -- `try` makes this optional, which is necessary for the last repetition where `left; rfl` succeeds
    try right
```

::::full
The tactic `repeat t` never fails: if the tactic `t` doesn't apply
to the original goal, then repeat _succeeds_ without changing the
goal at all (i.e., it repeats zero times).

```lean
example : 10 ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  -- this is a no-op
  repeat lia
  repeat
    rw [List.mem_cons]
    try left; rfl
    try right
```
::::

::::full
The tactic `repeat t` does not have any upper bound on the
number of times it applies `t`.  If `t` is a tactic that _always_
succeeds (and makes progress), then `repeat t` will loop
forever.
::::

::::terse
{tactic}`repeat` can loop forever.
::::

```lean +error
example (m n : Nat) : m + n = n + m := by
  /- Uncomment the next line to see the infinite loop occur.  You will
     then need to recomment it make Lean listen to you again. -/
  -- repeat rewrite [Nat.add_comm]
```

::::full
Wait — did we just write an infinite loop in Lean?!?!

Sort of.

While evaluation in Lean's term language is guaranteed to
terminate, _tactic_ evaluation is not.  This does not affect Lean's
logical consistency, however, since the job of {tactic}`repeat` and other
tactics is to guide Lean in constructing proofs; if the
construction process diverges (i.e., it does not terminate), this
simply means that we have failed to construct a proof at all, not
that we have constructed a bad proof.
::::

## The {tactic}`first` Combinator

::::full
The {tactic}`first` combinator takes a sequence of tactics and tries them in order,
stopping after the first success. As a silly example:
::::

::::terse
The {tactic}`first` combinator applies the first successful tactic in a list:
::::

```lean
example (n m : Nat) : n * (m + 1) = n * m + n := by
  first | rfl | left | lia | induction n
```

::::full
Neither {tactic}`rfl` nor {tactic}`left` succeed on this goal,
but {tactic}`lia` does, so {tactic}`first` stops after {tactic}`lia`
and never tries {tactic}`induction`. As with {tactic}`try`,
{tactic}`first` is most useful in combination with other combinators.
For example, we can rewrite our previous examples that used
{tactic}`repeat` and {tactic}`try` like so:
::::

::::terse
We can combine {tactic}`first` with {tactic}`repeat`:
::::

```lean
example : 10 ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  repeat first
    | exact List.mem_cons_self
    | apply List.mem_cons_of_mem
```

::::full
The {tactic}`first` tactic here will attempt to close the goal with an application of {name}`List.mem_cons_self`,
if it can, and otherwise `apply List.mem_cons_of_mem` to proceed to checking the next element in the
list. Note that the order here is important! If we had instead written:

```lean +error
example : 10 ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  repeat first
    | apply List.mem_cons_of_mem
    | exact List.mem_cons_self
  -- unprovable state!
```

Here, when we reach the goal {lean}`10 ∈ [10]`, instead of closing the goal with {name}`List.mem_cons_self`
like before, we would instead first try `apply List.mem_cons_of_mem`, which would also succeed.
This leaves us with the goal {lean}`10 ∈ []`, which is of course false.
::::

With {tactic}`first`, we can solve the earlier issue with {tactic}`try` where it would stop executing
the sequence on the first failure.

```lean
theorem Perm3_In_better_with_first (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm <;>
    first
    | rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia
    | lia
```

Our {name}`Perm3.In` example is getting quite short! But can we do better?

# The {tactic}`simp` Tactic

::::full
The {tactic}`simp` tactic is Lean's _simplifier_, and it is one of the most powerful
tools in the language. Given a set of lemmas ─ some built-in, some user-provided ─
{tactic}`simp` attempts to reduce a goal or hypothesis by rewriting with those lemmas
as much as possible.

Indeed, the characterizing lemmas we've been writing for
our definitions all throughout this book are examples
of these _simplification lemmas_, or
_{tactic}`simp` lemmas_ as they're called by Lean programmers.
::::

::::terse
The lemmas we've been using for rewriting are
the same ones we'll give to {tactic}`simp` for it to automatically
solve goals involving those theorems.
::::

We tag theorems with `@[simp]` to add them to the set of rules {tactic}`simp` considers when
simplifying a term.

```lean
namespace simp_lemmas_example

/- `add_zero` and `add_succ` are the `simp` lemmas for `+`. -/
@[simp]
theorem add_zero (n : Nat) : n + 0 = n := by rfl

@[simp]
theorem add_succ (n m : Nat) : n + (m + 1) = (n + m) + 1:= by rfl
```

Instead of manually rewriting by the characterizing lemmas in the example below,
{tactic}`simp` does it automatically.

```lean
theorem add_succ_nested (n m : Nat) :
    n + (m + 1 + 1) = (n + m + 1)  + 1 := by
  simp
```

::::full
If you know what theorems you want {tactic}`simp` to use for your goal proof, you can write
`simp [<theorems>]`. If you want {tactic}`simp` to _only_ use those,
you can use `simp only [<theorems>]`. Like with {tactic}`dsimp`, you can also supply a
definition to {tactic}`simp` to simplify using that definition.
::::

::::terse
`simp only` uses only the provided theorems:
::::

```lean
theorem add_succ_nested_2 (n m : Nat) :
    n + (m + 1 + 1) = (n + m + 1)  + 1 := by
  simp only [add_succ, add_zero]
```

If you want to know what {tactic}`simp` is doing, you can run {tactic}`simp?`.

```lean
theorem add_succ_nested_3 (n m : Nat) :
    n + (m + 1 + 1) = (n + m + 1) + 1 := by
  simp?

end simp_lemmas_example
```

::::full
In the InfoView, Lean will show you what {tactic}`simp` is doing.
You can click the `[apply]` button to replace {tactic}`simp?` with
the suggested replacement. You should always do this
for your final proof scripts: {tactic}`simp?` is helpful for writing
a proof, but it should not show up in the final script.

{tactic}`simp` is quite a powerful automated tactic, and is used
heavily in real Lean developments. We can use {tactic}`simp` to further simplify our
{name}`Perm3.In` proof.
::::

::::terse
{tactic}`simp` makes our example _much_ shorter.
::::

```lean
theorem Perm3_In_almost_shortest (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm <;>
    first
    | simp at * <;> lia
    | lia
```

::::full
Like {tactic}`apply` and {tactic}`rw`, there's also a version of {tactic}`simp` that can simplify in
hypotheses, rather than the goal. Invoking {tactic}`simp` as `simp [<lemmas>] at h`
runs the simplifier with at hypothesis `h`.
::::

::::terse
The `simp ... at ...` tactic simplifies in a hypothesis.
::::

```lean
example α x (l₁ l₂ l₃ : List α)
    (h₁ : x ∈ l₁ ++ l₂)
    (h₂ : x ∈ l₂ ++ l₃) :
    x ∈ l₁ ++  l₃ ∨ x ∈ l₂ := by
  simp at h₁; simp at h₂; simp; lia
```

::::full
If we just want to simplify everywhere, we can use {tactic}`simp_all`, which
simplifies in all hypotheses and in the goal at the same time. Rewriting the
example above:
::::

::::terse
The {tactic}`simp_all` tactic simplifies in all hypotheses and the goal.
::::

```lean
example α x (l₁ l₂ l₃ : List α)
    (h₁ : x ∈ l₁ ++ l₂)
    (h₂ : x ∈ l₂ ++ l₃) :
    x ∈ l₁ ++  l₃ ∨ x ∈ l₂ := by
  simp_all; lia
```

The simplest version of our theorem uses {tactic}`simp_all`:

```lean
theorem Perm3_In_shortest (α : Type) (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  induction hPerm <;> simp_all <;> lia
```

## Idiomatic {tactic}`simp` Usage

::::full
Because {tactic}`simp` is such a powerful tactic, the Lean community has developed a number of
conventions surrounding appropriate usage. One such convention is around _terminal_ {tactic}`simp` usage.

A call to {tactic}`simp` is considered terminal either when it is the last tactic used to close a goal
or when it is followed only by other automatic (also called "flexible") tactics like
{tactic}`simp` or {tactic}`lia`. In idiomatic Lean, all non-terminal uses of {tactic}`simp` should use the `only`
qualifier and specify exactly which lemmas are being used to simplify. Use of {tactic}`simp`
without `only` should only occur in terminal positions.

In our example from before, the use of {tactic}`simp` is terminal (and therefore okay)
because it is followed only by other {tactic}`simp`s and {tactic}`lia`:

```lean
example α x (l₁ l₂ l₃ : List α)
    (h₁ : x ∈ l₁ ++ l₂)
    (h₂ : x ∈ l₂ ++ l₃) :
    x ∈ l₁ ++  l₃ ∨ x ∈ l₂ := by
  simp at h₁; simp at h₂; simp; lia
```

On the other hand, if we instead decline to use {tactic}`lia` and solve the goal manually,
this example uses {tactic}`simp` in a non-terminal position, and is considered poor style:
::::

::::terse
Don't use {tactic}`simp` without `only` unless you're closing a goal or following with a flexible tactic,
like in this example below:
::::

```lean
example α x (l₁ l₂ l₃ : List α)
    (h₁ : x ∈ l₁ ++ l₂)
    (h₂ : x ∈ l₂ ++ l₃) :
    x ∈ l₁ ++  l₃ ∨ x ∈ l₂ := by
  simp at h₁; simp at h₂; simp
  cases h₁ with
  | inl h => left; left; exact h
  | inr h => right; exact h
```

::::full
Using {tactic}`simp` this way is brittle because if we add new {tactic}`simp` lemmas to our library,
this can change the way that our hypotheses and goals are simplified. Because our proof
after the {tactic}`simp`s relies on the precise structure of the goals and hypotheses, these
changes could cause the proof to break as the structure of the development evolves.
::::

::::terse
This usage of {tactic}`simp` is brittle and can break due to upstream changes.
::::

We can fix the style of this proof by changing the {tactic}`simp`s to specify which theorems they are
using to simplify:

```lean
example α x (l₁ l₂ l₃ : List α)
    (h₁ : x ∈ l₁ ++ l₂)
    (h₂ : x ∈ l₂ ++ l₃) :
    x ∈ l₁ ++  l₃ ∨ x ∈ l₂ := by
  -- the * here targets all hypotheses and the goal
  simp only [List.mem_append] at *
  cases h₁ with
  | inl h => left; left; exact h
  | inr h => right; exact h
```

::::full
This usage of `simp only` is better because the addition of new {tactic}`simp` lemmas won't
cause this proof to change.
::::

:::dev "Daniel Sainati (@dsainati1)"
Chris suggested using Mathlib's `linter.flexible` option to enforce proper `simp` usage.
How do we feel about adding a Mathlib dependency for this?
:::

Another rule around proper {tactic}`simp` usage applies to the appropriate definition of {tactic}`simp` lemmas.

::::full
All of the theorems marked with the `@[simp]` attribute in a Lean library compose the _simp set_
for that library, and the result of simplifying an expression iteratively using all of the
theorems in the simp set is the _simp normal form_ of that expression.

It's important for the stability of proofs using {tactic}`simp` that all the theorems in the simp set
progress towards this normal form. Accordingly, library designers often first consider
what they want that normal form to look like, and then structure their theorem definitions
accordingly. As a simple example, the simp normal form for lists prefers to use the `++`
notation instead of {name}`List.append`, so there is a {tactic}`simp` theorem {name}`List.append_eq`
whose type is `List.append_eq {α : Type u} {as bs : List α} : as.append bs = as ++ bs`.

In this case, the {tactic}`simp` normal form appears on the right, while the expression in need of
simplification appears on the left. We can thus think of this theorem as simplifying from left
to right. Not every {tactic}`simp` lemma in the standard library has a {tactic}`simp` normal form on its right-hand
side, but all make progress towards {tactic}`simp` normal form when applied.

For our purposes, in this textbook and in later ones, we will take care to define our {tactic}`simp`
lemmas such that they respect this left-to-right simplification behavior.
::::

::::terse
Appropriately defined {tactic}`simp` lemmas simplify left to right.
::::

# The {tactic}`trivial` Tactic

A final automated tactic to have in your toolkit is {tactic}`trivial`,
which tries a number of different simple tactics
(such as {tactic}`rfl` or {tactic}`contradiction`)
to try to close the current goal. Some examples:

```lean
example : 1 = 1 := by trivial
example : (1, 2).fst = 1 := by trivial
example (A B : Prop) : ¬ A -> A -> B := by intro h₁ h₂; trivial
```

# Case Study: Regular Expressions

::::full
As a culminating exercise for this book and as practice using the automation techniques we
discussed above on a real proof,
we examine the theory of regular expressions,
eventually working up to a proof of the pumping lemma.
::::

## Definitions

::::full
Regular expressions are a formal language for describing sets of
strings. Their syntax is defined as follows:
::::

```lean
inductive RegExp (α : Type) : Type where
  | EmptySet
  | EmptyStr
  | Char (c : α)
  | App (r1 r2 : RegExp α)
  | Union (r1 r2 : RegExp α)
  | Star (r : RegExp α)
deriving BEq, DecidableEq, Repr

attribute [pp_nodot] RegExp.Char RegExp.App RegExp.Union RegExp.Star

namespace RegExp
```

Note that this definition is _polymorphic_: Regular
expressions in `RegExp α` describe strings with characters drawn
from `α` ─ which in this exercise we represent as _lists_ with
elements from `α`.

::::full
(Technical aside: We depart slightly from standard practice in
that we do not require the type `α` to be finite.  This results in
a somewhat different theory of regular expressions, but the
difference is not significant for present purposes.)
::::

::::dev "Daniel Sainati (@dsainati1)"
CH: Do you mean here that this is different because the inductive type doesn't specify α is finite? In Lean the convention is for inductives not to carry Prop-valued typeclass assumptions, enforcing this only at the theorems that use them. So this could give off a slightly wrong impression.
DHS: @bcpierce00 What was the purpose of this aside in the original Rocq text? Does it make sense to keep here?
::::

We connect regular expressions and strings by defining when a
regular expression _matches_ some string.

:::ignore
```lean -show
variable
  (α : Type)
  (x : α)
  (s s₁ s₂ s₃ : List α)
  (ss : List (List α))
  (re re₁ re₂ : RegExp α)
```
:::

Informally this looks as follows:

  - The regular expression {lean}`EmptySet` does not match any string.

  - {lean}`EmptyStr` matches the empty string {lean}`[]`.

  - {lean}`Char x` matches the one-character string {lean}`x`.

  - If {lean}`re₁` matches {lean}`s₁`, and {lean}`re₂` matches {lean}`s₂`,
    then {lean}`App re₁ re₂` matches {lean}`s₁ ++ s₂`.

  - If at least one of {lean}`re₁` and {lean}`re₂` matches {lean}`s`,
    then {lean}`Union re₁ re₂` matches {lean}`s`.

  - Finally, if we can write some string {lean}`s` as the concatenation
    of a sequence of strings `s = s₁ ++ ... ++ sₖ`, and the
    expression {lean}`re` matches each one of the strings `sᵢ`,
    then {lean}`Star re` matches {lean}`s`.

    In particular, the sequence of strings may be empty, so
    {lean}`Star re` always matches the empty string {lean}`[]` no matter what
    {lean}`re` is.

We can easily translate this intuition into a set of rules,
where we write `s =~ re` to say that {lean}`re` matches {lean}`s`:

:::dev "Benjamin Pierce (bcpierce00)"
Check typesetting here (rules should be centered, I think):
:::

```display
─────────────── (mEmpty)
[] =~ EmptyStr

─────────────── (mChar)
[x] =~ (Char x)

s₁ =~ re₁     s₂ =~ re₂
─────────────────────────── (mApp)
(s₁ ++ s₂) =~ (App re₁ re₂)

s₁ =~ re₁
───────────────────── (mUnionL)
s₁ =~ (Union re₁ re₂)

s₂ =~ re₂
───────────────────── (mUnionR)
s₂ =~ (Union re₁ re₂)

──────────────── (mStar0)
[] =~ (Star re)

s₁ =~ re     s₂ =~ (Star re)
──────────────────────────── (mStarApp)
(s₁ ++ s₂) =~ (Star re)
```

This directly corresponds to the following inductive definition:

```lean
inductive ExpMatch {α : Type} : List α → RegExp α → Prop where
  | mEmpty : ExpMatch [] EmptyStr
  | mChar (c : α) : ExpMatch [c] (Char c)
  | mApp (s₁ s₂ : List α) {re₁ re₂ : RegExp α}
         (h₁ : ExpMatch s₁ re₁) (h₂ : ExpMatch s₂ re₂)
       : ExpMatch (s₁ ++ s₂) (App re₁ re₂)
  | mUnionL (s₁ : List α) {re₁ re₂ : RegExp α}
            (h₁ : ExpMatch s₁ re₁) : ExpMatch s₁ (Union re₁ re₂)
  | mUnionR (s₂ : List α) {re₁ re₂ : RegExp α}
            (h₂ : ExpMatch s₂ re₂) : ExpMatch s₂ (Union re₁ re₂)
  | mStar0 (re : RegExp α) : ExpMatch [] (Star re)
  | mStarApp (s₁ s₂ : List α) {re : RegExp α}
             (h₁ : ExpMatch s₁ re) (h₂ : ExpMatch s₂ (Star re))
           : ExpMatch (s₁ ++ s₂) (Star re)
open ExpMatch

infix:40 " =~ " => ExpMatch
```

::::quiz
Notice that this clause in our informal definition...

  > "The expression `EmptySet` does not match any string."

... is not explicitly reflected in the above definition.  Do we
need to add something?

   (A) Yes, we should add a rule for this.
   (B) No, one of the other rules already covers this case.
   (C) No, the _lack_ of a rule actually gives us the behavior we
       want.

:::quizSolution
```lean
example α (s: List α) : ¬ (s =~ EmptySet) := by
  intro contra; inversion contra
```
:::
::::

::::full
Notice that these rules are not _quite_ the same as the
intuition that we gave at the beginning of the section. First, we
don't need to include a rule explicitly stating that no string is
matched by {name}`EmptySet`; indeed, the syntax of inductive definitions
doesn't even _allow_ us to give such a "negative rule." We just
don't happen to include any rule that would have the effect of
{name}`EmptySet` matching some string.

Second, the intuition we gave for {name}`Union` and {name}`Star` correspond
to two constructors each: {name}`mUnionL` / {name}`mUnionR`, and {name}`mStar0` /
{name}`mStarApp`.  The result is logically equivalent to the original
intuition but more convenient to use in Lean, since the recursive
occurrences of {name}`ExpMatch` are given as direct arguments to the
constructors, making it easier to perform induction on evidence.
(The exercises below ask you
to prove that the constructors given in the inductive declaration
and the ones that would arise from a more literal transcription of
the intuition is indeed equivalent.)

Let's illustrate these rules with a few examples.
::::

## Examples

```lean
example : [1] =~ Char 1 := by
  apply mChar

example : [1, 2] =~ App (Char 1) (Char 2):= by
  apply mApp [1] <;> constructor
```

::::full
Notice how the last example applies {name}`mApp` to the string
`[1]` directly.  Since the goal mentions `[1, 2]` instead of
`[1] ++ [2]`, Lean wouldn't be able to figure out how to split
the string on its own.

Using {tactic}`inversion`, we can also show that certain strings do _not_
match a regular expression:
::::

```lean
example : ¬([1, 2] =~ Char 1) := by
  intro contra; inversion contra
```

We can define helper functions for writing down regular
expressions. The `reg_exp_of_list` function constructs a regular
expression that matches exactly the string that it receives as an
argument:

```lean
def reg_exp_of_list {α} (l : List α) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')

example : [1, 2, 3] =~ reg_exp_of_list [1, 2, 3] := by
  apply mApp [1]; constructor
  apply mApp [2]; constructor
  apply mApp [3]; constructor
  constructor
```

::::exercise (rating := 1) (name := "regexp_match_of_list")
As a quick exercise, prove that every list matches `reg_exp_of_list` of itself:

```lean
theorem regexp_match_of_list α (l : List α) : l =~ reg_exp_of_list l := by
  solution!
    induction l with
    | nil => constructor
    | cons hd tl ih =>
      simp only [reg_exp_of_list]
      have h : hd :: tl = [hd] ++ tl := by simp
      rw [h]
      constructor; constructor; assumption
```
:::gradeTheorem 2 regexp_match_of_list
:::
::::

::::full
We can also prove general facts about {name}`ExpMatch`. For instance,
the following lemma shows that every string {lean}`s` matched by {lean}`re`
is also matched by {lean}`Star re`.
::::

::::terse
Something more interesting:
::::

```lean
theorem MStar1 α s (re : RegExp α) (h : s =~ re) : s =~ Star re := by
  workinclass!
    rw [← List.append_nil s]
    constructor
    . assumption
    . constructor
```

::::full
(Note the use of {name}`List.append_nil` to change the goal of the theorem to
exactly the shape expected by {name}`mStarApp`.)
::::

The following lemmas show that the intuition about matching given
at the beginning of the section can be obtained from the formal
inductive definition.

::::exercise (rating := 1) (name := "EmptySet_is_empty")

```lean
theorem EmptySet_is_empty α (s : List α) : ¬(s =~ EmptySet) := by
  solution!
    intro h
    inversion h
```
:::gradeTheorem "0.5" EmptySet_is_empty
:::
::::

::::exercise (rating := 1) (name := "MUnion'")

```lean
theorem MUnion' α (s : List α) (re₁ re₂ : RegExp α) :
    s =~ re₁ ∨ s =~ re₂ →
    s =~ Union re₁ re₂ := by
  solution!
    rintro (_ | _)
    case inl => apply mUnionL; assumption
    case inr => apply mUnionR; assumption
```
:::gradeTheorem "0.5" MUnion'
:::
::::

The next lemma is stated in terms of the `fold` function on Lists:
If `ss : List (List α)` represents a sequence of
strings `s₁, ..., sₙ`, then {lean}`List.foldr (· ++ ·) ss []` is the result of
concatenating them all together.

::::exercise (rating := 2) (name := "MStar'")

```lean
theorem MStar' α (ss : List (List α)) (re : RegExp α)
    (h : ∀ s, s ∈ ss → s =~ re) :
    ss.foldr (· ++ ·) [] =~ Star re := by
  solution!
    induction ss with
    | nil => constructor
    | cons s ss' ih =>
      simp only [List.foldr_cons]
      constructor
      · apply h; simp
      · apply ih; intro s' hs'
        apply h; right; assumption
```
:::gradeTheorem 2 MStar'
:::
::::

::::exercise (rating := 1) (name := "EmptyStr_not_needed")
It turns out that the {name}`EmptyStr` constructor is actually not
needed, since the regular expression matching the empty string can
also be defined from {name}`Star` and {name}`EmptySet`:

```lean
def EmptyStr' {α : Type} := @Star α (EmptySet)
```

State and prove that this `EmptyStr'` definition matches exactly
the same strings as the {name}`EmptyStr` constructor.

:::solution
```lean
theorem empty_equiv {α : Type} (s : List α) :
    s =~ EmptyStr ↔ s =~ EmptyStr' := by
  constructor <;> intro h
  . inversion h; constructor
  . inversion h with
    | mStar0 => constructor
    | mStarApp _ _ h₁ _ => inversion h₁
```
:::
::::

::::full
Since the definition of {name}`ExpMatch` has a recursive
structure, we might expect that proofs involving regular
expressions will often require induction on evidence.
::::

::::terse
Naturally, proofs about {name}`ExpMatch` often require induction (on evidence!).
::::

For example, suppose we want to prove the following intuitive
fact: If a string {lean}`s` is matched by a regular expression {lean}`re`,
then all elements of {lean}`s` must occur as character literals
somewhere in {lean}`re`.

To state this as a theorem, we first define a function `re_chars`
that lists all characters that occur in a regular expression:

```lean
def reChars {α : Type} (re : RegExp α) : List α :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re₁ re₂ => reChars re₁ ++ reChars re₂
  | Union re₁ re₂ => reChars re₁ ++ reChars re₂
  | Star re => reChars re
```

Now, the main theorem:

```lean
theorem in_re_match {α : Type} {s : List α} {re : RegExp α} {x : α}
    (hmatch : s =~ re) (hin : x ∈ s) : x ∈ reChars re := by
  induction hmatch with
  | mEmpty => simp at hin
  | mChar c => simp only [reChars]; assumption
  | mApp _ _ _ _ ih₁ ih₂ =>

  /- Something interesting happens in the `mApp` case.  We obtain
    _two_ induction hypotheses: One that applies when `x` occurs in
    `s₁` (which is matched by `re₁`), and a second one that applies when `x`
    occurs in `s₂` (matched by `re₂`). -/
    workinclass!
      simp only [reChars, List.mem_append] at *
      cases hin with
      | inl hin₁ => left; exact ih₁ hin₁
      | inr hin₂ => right; exact ih₂ hin₂
  | mUnionL _ _ ih =>
    simp only [reChars, List.mem_append]; left; exact ih hin
  | mUnionR _ _ ih =>
    simp only [reChars, List.mem_append]; right; exact ih hin
  | mStar0 => simp at hin
  | mStarApp _ _ _ _ ih₁ ih₂ =>

  /- Here again we get two induction hypotheses, and they illustrate
    why we need induction on evidence for `ExpMatch`, rather than
    induction on the regular expression `re`: The latter would only
    provide an induction hypothesis for strings that match `re`, which
    would not allow us to reason about the case `In x ∈ s₂`. -/
    workinclass!
      simp only [List.mem_append] at hin
      cases hin with
      | inl hin₁ => exact ih₁ hin₁
      | inr hin₂ => exact ih₂ hin₂
```


::::exercise (rating := 1) (name := "reNotEmpty")
Write a recursive function `reNotEmpty` that tests whether a
regular expression matches some string. Prove that your function
is correct.

:::solution
```lean
def reNotEmpty {α : Type} (re : RegExp α) : Bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App re₁ re₂ => reNotEmpty re₁ && reNotEmpty re₂
  | Union re₁ re₂ => reNotEmpty re₁ || reNotEmpty re₂
  | Star _ => true

theorem reNotEmpty_correct {α : Type} (re : RegExp α) :
    (∃ s, s =~ re) ↔ reNotEmpty re = true := by
  induction re with (simp only [reNotEmpty])
  | EmptySet =>
    simp only [Bool.false_eq_true, iff_false, not_exists]
    intro s h; inversion h
  | EmptyStr =>
    simp only [iff_true]; exists []; constructor
  | Char x =>
    simp only [iff_true]; exists [x]; constructor
  | App re₁ re₂ ih₁ ih₂ =>
    simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨s, h⟩
      inversion h with
      | mApp s₁ s₂ h₁ h₂ =>
        constructor
        case left  => apply ih₁.mp; exists s₁
        case right => apply ih₂.mp; exists s₂
    · rintro ⟨h₁, h₂⟩
      obtain ⟨s₁, hs₁⟩ := ih₁.mpr h₁
      obtain ⟨s₂, hs₂⟩ := ih₂.mpr h₂
      exists (s₁ ++ s₂); constructor <;> assumption
  | Union re₁ re₂ ih₁ ih₂ =>
    simp only [Bool.or_eq_true]
    constructor
    · rintro ⟨s, h⟩
      inversion h with
      | mUnionL h₁ => left; apply ih₁.mp; exists s
      | mUnionR h₂ => right; apply ih₂.mp; exists s
    · rintro (h₁ | h₂)
      case inl => obtain ⟨s, hs⟩ := ih₁.mpr h₁; exists s; constructor; assumption
      case inr => obtain ⟨s, hs⟩ := ih₂.mpr h₂; exists s; apply mUnionR; assumption
  | Star re _ =>
    simp only [iff_true]; exists []; constructor
```
:::
::::

## The {tactic}`generalize` Tactic

One potentially confusing feature of the {tactic}`induction` tactic is
that it won't let you perform an induction over a term that
isn't sufficiently general. Here's an example:

```lean +error (name := induction_generalize)
example α (s₁ s₂ : List α) (re : RegExp α) :
    s₁ =~ Star re →
    s₂ =~ Star re →
    s₁ ++ s₂ =~ Star re := by
  intro h₁
  /- Now, just doing an `inversion` on `h₁` won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence). We might try this, but Lean won't let us: -/
  induction h₁
```

```leanOutput induction_generalize
Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  Star re
```

The problem here is that {tactic}`induction` over a {lean}`Prop` hypothesis only
works properly with hypotheses that are "fully general," i.e.,
ones in which all the arguments are just variables, as opposed to more
specific expressions like {lean}`Star re`.

A possible, but awkward, way to solve this problem is "manually
generalizing" over the problematic expressions by adding
explicit equality hypotheses to the lemma:

```lean +error
example α (s₁ s₂ : List α) (re re' : RegExp α) :
    re' = Star re →
    s₁ =~ re' →
    s₂ =~ Star re →
    s₁ ++ s₂ =~ Star re := by
  intro h₁ h₂ h₃
  /- We can now proceed by performing induction over evidence
    directly, because the argument to the first hypothesis is
    sufficiently general, which means that we can discharge most cases
    by inverting the `re' = Star re` equality in the context. -/
  induction h₂
  /- This works, but it makes the statement of the lemma a bit ugly.
    Fortunately, there is a better way... -/
```

The tactic `generalize h : e = x` causes Lean to (1) replace all
occurrences of the expression `e` by the variable `x`, and (2) add
an equation `h : x = e` to the context.  Here's how we can use it
to show the above result:

```lean
theorem star_app α (s₁ s₂ : List α) (re : RegExp α) :
    s₁ =~ Star re →
    s₂ =~ Star re →
    s₁ ++ s₂ =~ Star re := by
  intro h₁
  generalize heq : Star re = re' at h₁
  /- We now have `heq : Star re = re'`.
    heq` is contradictory in most cases, allowing us to conclude immediately via `contradiction`. -/
  induction h₁ <;> try contradiction
  -- The interesting cases are those that correspond to `Star`.
  case mStar0 _ => intro h₂; simp only [List.nil_append]; exact h₂
  case mStarApp _ _ _ _ _ _ ih₂ =>
    injections heq; subst heq
    intro h₂; simp only [List.append_assoc]
    apply mStarApp
    . assumption
    . apply ih₂ <;> trivial
  /- Note that the induction hypothesis `ih₂` on the `mStarApp` case
    mentions an additional premise [Star re'' = Star re], which
    results from the equality generated by `generalize`. -/
```

::::exercise (rating := 1) (name := "exp_match_ex2")
The `MStar''` lemma below (combined with its converse, the
`MStar'` exercise above), shows that our definition of {name}`ExpMatch`
for {name}`Star` is equivalent to the informal one given previously.

```lean
theorem MStar'' α (s : List α) (re : RegExp α) (h : s =~ Star re) :
    exists ss : List (List α),
      s = List.foldr (· ++ ·) [] ss
      ∧ ∀ s', s' ∈ ss → s' =~ re := by
  solution!
    generalize heq : Star re = re' at h
    induction h <;> try trivial
    case mStar0 ih => exists []; simp
    case mStarApp s₁ s₂ re h₁ h₂ ih₁ ih₂ =>
      injections heq; subst heq
      obtain ⟨ss, hfold, hall⟩ := ih₂ rfl
      exists (s₁ :: ss)
      simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]; rw [← hfold]
      repeat
        constructor
        trivial
      intro s h; apply hall; trivial
```
::::

## The "Weak" Pumping Lemma

One of the first really interesting theorems in the theory of
regular expressions is the so-called _pumping lemma_, which
states, informally, that any sufficiently long string {lean}`s` matching
a regular expression {lean}`re` can be "pumped" by repeating some middle
section of {lean}`s` an arbitrary number of times to produce a new
string also matching {lean}`re`.  For the sake of simplicity, this
exercise considers a slightly weaker theorem than is usually
stated in courses on automata theory ─ hence the name
`weak_pumping`.  The stronger one can be found below.

To get started, we need to define "sufficiently long."  Since we
are working in a constructive logic, we actually need to be able
to _calculate_, for each regular expression {lean}`re`, a minimum length
for strings {lean}`s` to guarantee "pumpability."

```lean
namespace Pumping

def pumpingConstant {α : Type} (re : RegExp α) : Nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re₁ re₂ => pumpingConstant re₁ + pumpingConstant re₂
  | Union re₁ re₂ => pumpingConstant re₁ + pumpingConstant re₂
  | Star r => pumpingConstant r
```

You may find these lemmas about the pumping constant useful when
proving the pumping lemma below.

```lean
theorem pumping_constant_ge_1 {α : Type} (re : RegExp α) :
    pumpingConstant re ≥ 1 := by
  induction re with
  | EmptySet => simp [pumpingConstant]
  | EmptyStr => simp [pumpingConstant]
  | Char _ => simp [pumpingConstant]
  | App re₁ _ ih1 _ => simp only [pumpingConstant]; lia
  | Union re₁ _ ih1 _ => simp only [pumpingConstant]; lia
  | Star _ ih => simp only [pumpingConstant]; exact ih

theorem pumping_constant_0_false {α : Type} (re : RegExp α)
    (h : pumpingConstant re = 0) : False := by
  have := pumping_constant_ge_1 re; lia
```

Next, it is useful to define an auxiliary function that repeats a
string (appends it to itself) some number of times. Note
how we define {tactic}`simp` lemmas for `napp` to go with its definition.

```lean
def napp {α : Type} (n : Nat) (l : List α) : List α :=
  match n with
  | 0 => []
  | n' + 1 => l ++ napp n' l

@[simp]
theorem napp_zero {α : Type} (l : List α) : napp 0 l = [] := by rfl

@[simp]
theorem napp_succ {α : Type} (n : Nat) (l : List α) : napp (n + 1) l = l ++ napp n l := by rfl
```

These auxiliary lemmas might also be useful in your proof of the
pumping lemma.

```lean
@[simp]
theorem napp_plus {α : Type} (n m : Nat) (l : List α) :
    napp (n + m) l = napp n l ++ napp m l := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_add]; simp [ih]

theorem napp_star {α : Type} (m : Nat) (s₁ s₂ : List α) (re : RegExp α)
    (hs₁ : s₁ =~ re) (hs₂ : s₂ =~ Star re) :
    napp m s₁ ++ s₂ =~ Star re := by
  induction m with
  | zero => simp only [napp_zero, List.nil_append]; trivial
  | succ m ih =>
    simp only [napp_succ]
    rw [List.append_assoc]
    apply mStarApp <;> trivial
```

The (weak) pumping lemma itself says that, if {lean}`s =~ re` and if the
length of {lean}`s` is at least the pumping constant of {lean}`re`, then {lean}`s`
can be split into three substrings {lean}`s₁ ++ s₂ ++ s₃` in such a way
that {lean}`s₂` can be repeated any number of times and the result, when
combined with {lean}`s₁` and {lean}`s₃`, will still match {lean}`re`.
Since {lean}`s₂` is also guaranteed not to be the empty string, this gives us
a (constructive!) way to generate strings matching {lean}`re` that are
as long as we like.

This proof is quite long, so to make it more tractable we've
broken it up into a number of sub-proofs, which we then assemble
to prove the main lemma.

Your job is to complete the proofs of the helper lemmas; the main
lemma relies on these. Several of the lemmas about {name}`Nat.ble` that were
in an optional exercise earlier in the {ref "IndProp"}[IndProp] chapter may be
useful here ─ in particular, {name}`lt_ge_cases` and {name}`add_le`.

::::exercise (rating := 2) (name := "weak_pumping_char")
```lean
theorem weak_pumping_char {α : Type} (x : α)
    (h : pumpingConstant (Char x) ≤ [x].length) :
    ∃ s₁ s₂ s₃ : List α,
      [x] = s₁ ++ s₂ ++ s₃ ∧ s₂ ≠ [ ] ∧
      (∀ m : Nat, s₁ ++ napp m s₂ ++ s₃ =~ Char x) := by
  solution!
    simp [pumpingConstant] at h
```
::::

::::exercise (rating := 4) (name := "weak_pumping_app")
```lean
theorem weak_pumping_app {α : Type} (s₁ s₂ : List α) (re₁ re₂ : RegExp α)
    (h₁ : s₁ =~ re₁)
    (h₂ : s₂ =~ re₂)
    (ih₁ : pumpingConstant re₁ ≤ s₁.length →
      ∃ s₂ s₃ s₄ : List α,
        s₁ = s₂ ++ s₃ ++ s₄ ∧
        s₃ ≠ [ ] ∧
        (∀ m : Nat, s₂ ++ napp m s₃ ++ s₄ =~ re₁))
    (ih₂ : pumpingConstant re₂ ≤ s₂.length →
      ∃ s₁ s₃ s₄ : List α,
        s₂ = s₁ ++ s₃ ++ s₄ ∧
        s₃ ≠ [ ] ∧
        (∀ m : Nat, s₁ ++ napp m s₃ ++ s₄ =~ re₂))
    (hLen : pumpingConstant (App re₁ re₂) ≤ (s₁ ++ s₂).length) :
    ∃ s₀ s₃ s₄ : List α,
      s₁ ++ s₂ = s₀ ++ s₃ ++ s₄ ∧
      s₃ ≠ [ ] ∧
      (∀ m : Nat, s₀ ++ napp m s₃ ++ s₄ =~ App re₁ re₂) := by
  obtain h | h :
    pumpingConstant re₁ ≤ s₁.length ∨ pumpingConstant re₂ ≤ s₂.length := by
    solution!
      rw [append_length] at hLen
      apply add_le_cases
      apply hLen
  case inl =>
    solution!
      specialize ih₁ h
      let ⟨s₁₂, s₁₃, s₁₄, h₁, h₂, h₃⟩ := ih₁
      rw [h₁]
      exists s₁₂, s₁₃, s₁₄ ++ s₂
      constructor
      case left => simp
      case right =>
        constructor
        case left => assumption
        case right =>
          intro m; specialize h₃ m
          rw [← List.append_assoc]
          constructor <;> trivial
  case inr =>
    solution!
      specialize ih₂ h
      let ⟨s₂₁, s₂₂, s₂₃, h₁, h₂, h₃⟩ := ih₂
      rw [h₁]
      exists (s₁ ++ s₂₁), s₂₂, s₂₃
      constructor
      case left => simp
      case right =>
        constructor
        case left => assumption
        case right =>
          intro m; specialize h₃ m
          simp only [List.append_assoc] at *
          constructor <;> assumption
```
::::

::::exercise (rating := 3) (name := "weak_pumping_union_l")
```lean
theorem weak_pumping_union_l  {α : Type} (s₁ : List α) (re₁ re₂ : RegExp α)
    (h₁ : s₁ =~ re₁)
    (ih : pumpingConstant re₁ ≤ s₁.length →
      ∃ s₂ s₃ s₄ : List α,
        s₁ = s₂ ++ s₃ ++ s₄ ∧
        s₃ ≠ [ ] ∧
        (∀ m : Nat, s₂ ++ napp m s₃ ++ s₄ =~ re₁))
    (hLen : pumpingConstant (Union re₁ re₂) ≤ s₁.length) :
    ∃ s₀ s₂ s₃ : List α,
      s₁ = s₀ ++ s₂ ++ s₃ ∧
      s₂ ≠ [ ] ∧
      (∀ m : Nat, s₀ ++ napp m s₂ ++ s₃ =~ Union re₁ re₂) := by
  have h : pumpingConstant re₁ ≤ s₁.length := by
    solution!
      simp only [pumpingConstant] at hLen; lia
  solution!
    specialize ih h
    obtain ⟨s₁₁, s₁₂, s₁₃, h₁, h₂, h₃⟩ := ih
    exists s₁₁; exists s₁₂; exists s₁₃
    constructor
    case left => assumption
    case right =>
      constructor
      case left => assumption
      case right =>
        intro m; specialize h₃ m
        apply mUnionL
        assumption
```
::::

::::exercise (rating := 3) (name := "weak_pumping_union_r")
```lean
theorem weak_pumping_union_r {α : Type} (s₂ : List α) (re₁ re₂ : RegExp α)
  (h₂ : s₂ =~ re₂)
  (ih : pumpingConstant re₂ ≤ s₂.length →
    ∃ s₁ s₃ s₄ : List α,
      s₂ = s₁ ++ s₃ ++ s₄ ∧
      s₃ ≠ [ ] ∧
      (∀ m : Nat, s₁ ++ napp m s₃ ++ s₄ =~ re₂))
  (hLen : pumpingConstant (Union re₁ re₂) ≤ s₂.length) :
  ∃ s₁ s₀ s₃ : List α,
    s₂ = s₁ ++ s₀ ++ s₃ ∧
    s₀ ≠ [ ] ∧
    (∀ m : Nat, s₁ ++ napp m s₀ ++ s₃ =~ Union re₁ re₂) := by
  -- symmetric to the previous
  have h : pumpingConstant re₂ ≤ s₂.length := by
   solution!
      simp only [pumpingConstant] at hLen; lia
  solution!
    specialize ih h
    let ⟨s₂₁, s₂₂, s₂₃, h₁, h₂, h₃⟩ := ih
    exists s₂₁; exists s₂₂; exists s₂₃
    constructor
    case left => assumption
    case right =>
      constructor
      case left => assumption
      case right =>
        intro m; specialize h₃ m
        apply mUnionR
        assumption
```
::::

::::exercise (rating := 2) (name := "weak_pumping_star_zero")
```lean
theorem weak_pumping_star_zero {α : Type} (re : RegExp α)
    (h : pumpingConstant (Star re) ≤ @List.length α []) :
    ∃ s₁ s₂ s₃ : List α,
      [ ] = s₁ ++ s₂ ++ s₃ ∧
      s₂ ≠ [ ] ∧
      (∀ m : Nat, s₁ ++ napp m s₂ ++ s₃ =~ Star re) := by
  solution!
    simp only [List.length_nil] at h
    inversion h with
    | refl h h₁ =>
      have h₂ := pumping_constant_ge_1 re
      rw [← h₁] at h₂; inversion h₂
```
::::

::::exercise (rating := 5) (name := "weak_pumping_star_app")
```lean
theorem weak_pumping_star_app {α : Type} (s₁ s₂ : List α) (re : RegExp α)
    (h₁ : s₁ =~ re)
    (h₂ : s₂ =~ Star re)
    (ih₁ : pumpingConstant re ≤ List.length s₁ →
      ∃ s₂ s₃ s₄ : List α,
        s₁ = s₂ ++ s₃ ++ s₄
        ∧ s₃  ≠ [ ] ∧
        (∀ m : Nat, s₂ ++ napp m s₃ ++ s₄ =~ re))
    (ih₂ : pumpingConstant (Star re) ≤ s₂.length →
      ∃ s₁ s₃ s₄ : List α,
        s₂ = s₁ ++ s₃ ++ s₄ ∧
        s₃  ≠ [ ] ∧
        (∀ m : Nat, s₁ ++ napp m s₃ ++ s₄ =~ Star re))
    (hLen : pumpingConstant (Star re) ≤ (s₁ ++ s₂).length) :
    ∃ s₀ s₃ s₄ : List α,
      s₁ ++ s₂ = s₀ ++ s₃ ++ s₄ ∧
      s₃  ≠ [ ] ∧
      (∀ m : Nat, s₀ ++ napp m s₃ ++ s₄ =~ .Star re)  := by
  rw [append_length] at *
  obtain hs₁len0 | ⟨s₁len, hs₁re₁⟩ | hs₁re₁ :
    (s₁.length = 0
      ∨ (s₁.length ≠ 0 ∧ s₁.length < pumpingConstant re)
      ∨ pumpingConstant re ≤ s₁.length) := by
    cases s₁ with
    | nil => solution!(left; rfl)
    | cons h s₁' =>
      solution!
        right
        have hcases : (List.length (h :: s₁') < pumpingConstant re
                      ∨ pumpingConstant re ≤ List.length (h :: s₁')) := by
          apply lt_ge_cases
        cases hcases with
        | inl =>
          left; constructor
          case left => intro contra; contradiction
          case right => assumption
        | inr => right; assumption
  . solution!
      have hs₁nil : s₁ = [] := by
        cases s₁; rfl; contradiction
      subst hs₁nil
      simp only [List.length_nil, Nat.zero_add] at hLen
      apply ih₂; apply hLen
  . solution!
      exists []; exists s₁; exists s₂
      constructor; rfl
      constructor
      case left => intro contra; subst contra; contradiction
      case right =>
        intro m; apply napp_star
        assumption
        assumption
  . solution!
      specialize ih₁ hs₁re₁
      let ⟨s₁₁, s₁₂, s₁₃, h₁, h₂, h₃⟩ := ih₁
      exists s₁₁; exists s₁₂; exists (s₁₃ ++ s₂)
      rw [h₁]
      constructor
      case left => simp
      case right =>
        constructor
        case left => assumption
        case right =>
          intro m; specialize h₃ m
          rw [← List.append_assoc]
          apply mStarApp <;> assumption
```
::::

::::exercise (rating := 3) (name := "weak_pumping")
```lean
theorem weak_pumping {α : Type} {re : RegExp α} {s : List α}
    (hmatch : s =~ re) (hlen : pumpingConstant re ≤ s.length) :
    ∃ s₁ s₂ s₃ : List α,
      s = s₁ ++ s₂ ++ s₃ ∧ s₂ ≠ [] ∧
      ∀ m, s₁ ++ napp m s₂ ++ s₃ =~ re := by
  solution!
    induction hmatch
    case mEmpty   => simp [pumpingConstant] at hlen
    case mChar    => apply weak_pumping_char; assumption
    case mApp     => apply weak_pumping_app <;> assumption
    case mUnionL  => apply weak_pumping_union_l <;> assumption
    case mUnionR  => apply weak_pumping_union_r <;> assumption
    case mStar0   => apply weak_pumping_star_zero <;> assumption
    case mStarApp => apply weak_pumping_star_app <;> assumption
```
::::

## The (Strong) Pumping Lemma

:::dev "Daniel Sainati (@dsainati1)"
If this exercise is going to be optional we should still fill in the
solution but it's lower priority.
:::

::::exercise (rating := 10) (name := "weak_pumping")
Now here is the usual version of the pumping lemma. In addition to
requiring that {lean}`s₂ ≠ []`, it also strengthens the result to
include the claim that {lean}`s₁.length + s₂.length ≤ pumpingConstant re`.

```lean
theorem pumping {α : Type} {re : RegExp α} {s : List α}
    (hmatch : s =~ re) (hlen : pumpingConstant re ≤ s.length) :
    ∃ s₁ s₂ s₃ : List α,
      s = s₁ ++ s₂ ++ s₃ ∧ s₂ ≠ [] ∧
      s₁.length + s₂.length ≤ pumpingConstant re ∧
      ∀ m, s₁ ++ napp m s₂ ++ s₃ =~ re := by
  sorry
```
::::

```lean
end Pumping
end RegExp
```
