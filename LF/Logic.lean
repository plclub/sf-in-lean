import SFLMeta

import LF.Basics
import LF.Induction
import LF.Poly
import LF.Tactics
import LF.CustomTactics

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Logic in Lean" =>
%%%
tag := "Logic"
htmlSplit := .never
file := some "Logic"
%%%

:::instructors
Warning: This is a LOT of material to get through in
two 80-minute lectures, and the last couple of sections are quite
meaty.  Pacing is key!
:::

:::dev BeforeNextRelease
Unlike earlier chapters, there are probably too many
WORKINCLASSes in this chapter.  BCP 20: But conversely some more
quizzes would be great!
:::

```importBlock
import LF.Basics
import LF.Induction
import LF.Poly
import LF.Tactics
import LF.CustomTactics
```

:::dev "Mike Hicks (mwhicks1)"
It would be convenient to declare the variables below so that inline prose
throughout this chapter can use `a`, `b`, `c`, `n`, `m`, `α`, `e1`, `e2`, `x`,
and `y` without repeating their type annotations, but the same problem
described elsewhere in this chapter applies: an unused `variable` is silently
added to the local context in basically every proof from here on, even when the
theorem never mentions it. Until we have a
way to declare variables visible only for inline prose (rather than for every
`lean` block), we leave this commented out:

```
-- variable (a b c : Prop) (n m : Nat) (α : Type) (e1 e2 x y : α)
```

Yipeng Liu (berberman) said: Maybe we should implement a separate scope for
declaring variables only visible to `lean` role instead of `lean` block.
:::

::::hide
```
-- QUIZ
/- We've seen that there are goals that `cases` can't solve but
    `induction` can. What about the other way around? Are there steps
    in a proof that can be solved by pure case analysis `cases`
    but not using `induction`?

    (A) No

    (B) Yes
-/
-- /QUIZ
```
::::

# The {lean}`Prop` Type

::::full
We have now seen many examples of factual claims (i.e.,
_propositions_) and ways of presenting evidence of their truth
(_proofs_).  In particular, we have worked extensively with
equality propositions (`e1 = e2`), implications (`a → b`), and
quantified propositions (`∀ x, a`).  In this chapter, we will
see how Lean can be used to carry out other familiar forms of
logical reasoning.

Before diving into details, we should talk a bit about the status
of mathematical statements in Lean. Lean is a _typed_ language,
which means that every sensible expression has an associated type.
Logical claims are no exception: any statement we might try to
prove in Lean has a type, namely {lean}`Prop`, the type of
_propositions_.  We can see this with the `#check` command:
::::

::::terse
So far, we have seen:
- _propositions_: mathematical statements, so far only of three kinds:
  - equality propositions (`e1 = e2`)
  - implications (`a → b`)
  - quantified propositions (`∀ x, a`)
- _proofs_: ways of presenting evidence for the truth of a
   proposition

In this chapter we will introduce several more flavors of both
propositions and proofs.

Like everything in Lean, well-formed propositions have a _type_:
::::

```lean
#check (∀ n m : Nat, n + m = m + n : Prop)
```

Note that _all_ syntactically well-formed propositions have type
{lean}`Prop` in Lean, regardless of whether they are true or not.

Simply _being_ a proposition is one thing; being _provable_ is
something else!

```lean
#check (2 = 2 : Prop)
#check (3 = 2 : Prop)
#check (∀ n : Nat, n = 2 : Prop)
```

::::full
Indeed, propositions don't just have types — they are
_first-class_ entities that can be manipulated in all the same ways as
any of the other things in Lean's world.
::::

So far, we've seen one place where propositions can appear:
in `theorem` declarations.

```lean
theorem plus_2_2_is_4 : 2 + 2 = 4 := by rfl
```

::::full
But propositions can be used in other ways.  For example, we
can give a name to a proposition using a `def`, just as we
give names to other kinds of expressions.
::::

::::terse
Propositions are first-class entities.
For example, we can name them:
::::

```lean (name := PlusClaim)
def PlusClaim : Prop := 2 + 2 = 4

#check PlusClaim
```

```leanOutput PlusClaim
PlusClaim : Prop
```

::::full
We can later use this name in any situation where a proposition is
expected — for example, as the claim in a `theorem` declaration.
::::

```lean
theorem plusClaim_is_true : PlusClaim := by rfl
```

We can also write _parameterized_ propositions — that is,
functions that take arguments of some type and return a
proposition.

::::full
For instance, the following function takes a number and
returns a proposition asserting that this number is equal to three:
::::

```lean (name := IsThree)
def Nat.IsThree (n : Nat) : Prop := n = 3

#check (Nat.IsThree)
```

```leanOutput IsThree
Nat.IsThree : Nat → Prop
```

In Lean, functions that return propositions are said to define
_properties_ of their arguments.

For instance, here's a (polymorphic) property defining the
familiar notion of an _injective function_.

```lean
def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

theorem succ_inj' : Injective Nat.succ := by
  intro x y h
  injection h
```

:::dev "Mike Hicks (mwhicks1)"
Is it confusing that you can do `intro` _through_ the `Injective`
definition? Is it worth a word about that? Have students seen this
happen to this point?
:::

## Equality Propositions

The familiar equality operator `=` is a (binary) function that returns
a {lean}`Prop`. The expression `n = m` is notation for `Eq n m`.
Because {name}`Eq` can be used with elements of any type, it is also
polymorphic:

:::instructors
Actually it quantifies over {name}`Sort`, where {lean}`Prop = Sort 0`
and {lean}`Type u = Sort (u + 1)`. Not something that needs teaching
right at this moment, but they'll see {name}`Sort` when hovering.
:::

```lean (name := eq)
#check Eq
```

```leanOutput eq
Eq.{u_1} {α : Sort u_1} : α → α → Prop
```

::::full
Equality turns out to be an inductively defined proposition, with a single constructor,
{name}`Eq.refl`, standing for the proof that anything is equal to itself.
Recall from the {ref "Tactics"}[Tactics] chapter that the constructors
of an inductive type are _injective_ and _disjoint_, and that
{tactic}`injection` and {tactic}`contradiction` let us exploit those
facts about hypotheses concerning {lean}`Nat`, {lean}`List`, and so on.
The very same injectivity and disjointness reasoning applies to a hypothesis of the form
`a = b`. In fact, {tactic}`cases` can carry out this reasoning
directly on an equality hypothesis, without our having to name
{tactic}`injection` or {tactic}`contradiction`. Here are a few
examples.
::::

::::terse
The injectivity/disjointness principles from the `Tactics` chapter
apply to equality hypotheses too, and {tactic}`cases` can exploit them
directly:
::::

```lean
-- substitution
example (x : Nat) (h : x = 0) : Nat.succ x = 1 := by
  cases h
  rfl
```

```lean
-- injectivity
example {m n : Nat} (h : Nat.succ m = Nat.succ n) : m = n := by
  cases h
  rfl
```

::::full
(This is the same injectivity fact used above by the {tactic}`injection`
tactic in {lean}`succ_inj'`; here {tactic}`cases` gets us the same
conclusion in a single step.)
::::

```lean
-- disjointness
example (h : (0 : Nat) = 1) : False := by
  cases h
```

```lean
-- acyclicity
example (n : Nat) (h : n = Nat.succ n) : False := by
  cases h
```

::::full
We'll see this same disjointness principle put to use again shortly,
via {tactic}`contradiction`, to prove {lean}`0 ≠ 1` in the `Falsehood
and Negation` section below.
::::

::::terse
There are more examples of this kind of reasoning yet to come.
::::

As a convenience, Lean will cast booleans to propositions by equating them to {lean}`true`,
which is why checking them against {lean}`Prop` succeeds.
For clarity, we will generally avoid relying on these implicit casts.

```lean (name := false)
#check (false : Prop)
```

```leanOutput false
false = true : Prop
```

```lean (name := true)
#check (true : Prop)
```

```leanOutput true
true = true : Prop
```

## Quizzes

::::quiz
What is the type of the following expression?

```display
Nat.pred 1 = 0
```

1. {lean}`Prop`
2. {lean}`Nat → Prop`
3. {lean}`∀ n : Nat, Prop`
4. {lean}`Nat → Nat`
5. Not typeable

:::quizSolution
```lean (name := pred)
#check Nat.pred 1 = 0
```
```leanOutput pred
Nat.pred 1 = 0 : Prop
```
:::
::::

::::quiz
What is the type of the following expression?

```display
∀ n : Nat, (n + 1).pred = n
```

1. {lean}`Prop`
2. {lean}`Nat → Prop`
3. {lean}`∀ n : Nat, Prop`
4. {lean}`Nat → Nat`
5. Not typeable

:::quizSolution
```lean (name := succ_pred)
#check (∀ n : Nat, (n + 1).pred = n : Prop)
```
```leanOutput succ_pred
∀ (n : Nat), (n + 1).pred = n : Prop
```
:::
::::

::::quiz
What is the type of the following expression?

```display
∀ n : Nat, n.pred + 1
```

1. {lean}`Prop`
2. {lean}`Nat → Prop`
3. {lean}`∀ n : Nat, Prop`
4. {lean}`Nat → Nat`
5. Not typeable

:::quizSolution
```lean
#check_failure ∀ n : Nat, n.pred + 1
```
:::
::::

::::quiz
What is the type of the following expression?

```display
fun n : Nat => n.pred + 1
```

1. {lean}`Prop`
2. {lean}`Nat → Prop`
3. {lean}`∀ n : Nat, Prop`
4. {lean}`Nat → Nat`
5. Not typeable

:::quizSolution
```lean (name := pred_fun)
#check (fun n : Nat => n.pred + 1 : Nat → Nat)
```

```leanOutput pred_fun
fun n => n.pred + 1 : Nat → Nat
```
:::
::::

::::quiz
What is the type of the following expression?

```display
fun n : Nat => n.pred + 1 = n
```

1. {lean}`Prop`
2. {lean}`Nat → Prop`
3. {lean}`∀ n : Nat, Prop`
4. {lean}`Nat → Nat`
5. Not typeable

:::quizSolution
```lean (name := pred_fun2)
#check (fun n : Nat => n.pred + 1 = n : Nat → Prop)
```

```leanOutput pred_fun2
fun n => n.pred + 1 = n : Nat → Prop
```
:::
::::

::::quiz
Which of the following is _not_ a proposition?

1. {lean}`3 + 2 = 4`
2. {lean}`3 + 2 = 5`
3. {lean}`3 + 2 == 5`
4. {lean}`(3 + 2 == 4) = false`
5. {lean}`∀ n, (3 + 2 == n) = true → n = 5`
6. All of these are propositions

:::quizSolution
```lean (name := add_eq)
#check (3 + 2 == 5 : Bool)
```
```leanOutput add_eq
3 + 2 == 5 : Bool
```
:::
::::

# Logical Connectives

## Conjunction

The _conjunction_, or _logical and_, of propositions `a` and `b` is written
`a ∧ b`; it represents the claim that both `a` and `b` are true.

```lean
example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by sorry -- proofs below
```

The infix notation `∧` is actually just syntactic sugar for
`And a b`. That is, {lean}`And` is a Lean operator that takes two
propositions as arguments and yields a proposition.

```lean (name := and)
#check And
```

```leanOutput and
And (a b : Prop) : Prop
```

The sole constructor for conjunction is {name}`And.intro`,
which concludes `a ∧ b` given that `a` and `b` hold individually.

```lean (name := and_intro)
#check And.intro
```

```leanOutput and_intro
And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
```

We can {tactic}`apply` {lean}`And.intro` to carry out proofs.

```lean
example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  · rfl /- 3 + 4 = 7 -/
  · rfl /- 2 * 2 = 4 -/
```

Rather than applying the constructor, we can explicitly provide
the arguments to the constructor as an {tactic}`exact` proof.

```lean
example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact And.intro rfl rfl
```

Lean can figure out which constructor to use just from the goal's type, so we
don't have to name it ourselves. This is what the tactic {tactic}`constructor`
does automatically: it applies whatever constructor builds a value of the
goal's type, leaving one subgoal per argument of that constructor. Since
{lean}`And` has just one constructor, {tactic}`constructor` always picks it
here.

```lean
example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  constructor
  · rfl
  · rfl
```

We can also use Lean's anonymous constructor notation `⟨..., ...⟩`,
which works on constructors for proofs as well.

```lean
example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact ⟨rfl, rfl⟩
```

::::::full
:::::exercise (rating := 2) (name := "add_is_zero")
```lean
theorem Nat.add_is_zero (n m : Nat) : n + m = 0 → n = 0 ∧ m = 0 := by
  solution!
    intro h
    cases m with
    | zero =>
      rw [Nat.add_zero] at h
      constructor
      · exact h
      · rfl
    | succ =>
      rw [add_succ]
      contradiction
```

:::gradeTheorem 2 Nat.add_is_zero
:::
:::::

::::::

The tactics we've just used — {tactic}`constructor`, applying
{name}`And.intro`, and the anonymous constructor `⟨_, _⟩` — all conclude
`a ∧ b` from proofs of `a` and `b`. We say that these
tactics _introduce_ a conjunction: they derive it as a logical
consequence of hypotheses we already have.

We also sometimes want to go the other way: given a conjunctive
hypothesis, use it to help prove something else, by extracting the two
proofs it packages together. In Lean, this is done with
{tactic}`obtain`. We say that {tactic}`obtain` _eliminates_ a
conjunction: it takes the conjunction apart to expose the proofs
inside.

```lean
example (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  workinclass!
    intro h
    obtain ⟨hn, hm⟩ := h
    rw [hn, hm]
```

We can also match on `h` right at the point where we
introduce it, instead of introducing and then destructing it:

```lean
example (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  intro ⟨hn, hm⟩
  rw [hn, hm]
```

::::full
You may wonder why we bothered packing the two hypotheses `n = 0` and
`m = 0` into a single conjunction, since we could also have stated the
theorem with two separate premises:

```lean
example (n m : Nat) : n = 0 → m = 0 → n + m = 0 := by
  intro hn hm
  rw [hn, hm]
```
::::

::::terse
For the present example, both ways work.
But in other situations, we may wind up with a conjunctive hypothesis
in the middle of a proof...
::::

::::full
For this specific theorem, both formulations are fine.  But
it's important to understand how to work with conjunctive
hypotheses because conjunctions often arise from intermediate
steps in proofs, especially in larger developments.  Here's a
simple example:
::::

```lean
example (n m : Nat) (h : n + m = 0) : n * m = 0 := by
  workinclass!
    apply Nat.add_is_zero at h
    obtain ⟨hn, hm⟩ := h
    rw [hm]
    rfl
```

::::::full
Another common situation is that we know `a ∧ b` but in some
context we need just `a` or just `b`.  In such cases we can use
an underscore pattern `_` to indicate that the unneeded conjunct
should just be thrown away.

```lean
example (a b : Prop) (h : a ∧ b) : a := by
  obtain ⟨hP, _⟩ := h
  exact hP
```

Conjunctions come with their own built-in projections, `.left` and `.right`,
which we can use instead of pattern matching.

```lean
example (a b : Prop) (h : a ∧ b) : a := by
  exact h.left
```

:::::exercise (rating := 1) (name := "proj2") (optional := true)
```lean
theorem right (a b : Prop) (h : a ∧ b) : b := by
  solution!
    exact h.right
```
:::::

Finally, we sometimes need to rearrange the order of conjunctions
and/or the grouping of multi-way conjunctions. We can see this
at work in the proofs of the following commutativity and
associativity theorems.

```lean
theorem and_commute (a b : Prop) (h : a ∧ b) : b ∧ a := by
  constructor
  · exact h.right
  · exact h.left
```

The anonymous constructor allows us to write a much shorter proof.

```lean
theorem and_commute' (a b : Prop) (h : a ∧ b) : b ∧ a := by
  exact ⟨h.right, h.left⟩
```

In the following proof of associativity, notice how projections can be
chained in sequence to obtain components of nested conjunctions.
Complete the proof.

:::::exercise (rating := 1) (name := "and_associate")
```lean
theorem and_associate (a b c : Prop) (h : a ∧ (b ∧ c)) : (a ∧ b) ∧ c := by
  constructor
  · solution!
      constructor
      · exact h.left
      · exact h.right.left
  · exact h.right.right
```
:::gradeTheorem 1 and_associate
:::
:::::

::::::

## Disjunction

Another important connective is the _disjunction_, or _logical or_,
of two propositions: `a ∨ b` is true when either `a` or `b` is.
This infix notation stands for `Or a b`, where
`Or : Prop → Prop → Prop`.

To eliminate a disjunctive hypothesis — i.e., to use it in a proof —
we proceed by case analysis, which, as with other data types like
{name}`Nat`, is done using {tactic}`cases`. The two cases are `inl`
(for "left injection", or "in the left case") and `inr` (for "right
injection", or "in the right case").

```lean
theorem Nat.factor_is_zero (n m : Nat)
  (h : n = 0 ∨ m = 0) : n * m = 0 := by
    cases h with
    /- `n = 0` -/
    | inl hn => rw [hn, Nat.zero_mul]
    /- `m = 0` -/
    | inr hm => rw [hm, Nat.mul_zero]
```

::::full
We can see in this example that, when we perform case
analysis on a disjunction `a ∨ b`, we must separately discharge
two proof obligations, each showing that the conclusion holds
under a different assumption — `a` in the first subgoal and `b`
in the second.
::::

Rather than performing case analysis via {tactic}`cases`, we can also use {tactic}`obtain`
to match on the two possible injections, much like with {tactic}`obtain` and `∧`.

```lean
theorem and_is_false (b1 b2 : Bool) (h : (b1 = false) ∨ (b2 = false)) :
    (b1 && b2) = false := by
  obtain hb1 | hb2 := h
  · rw [hb1, Bool.false_and]
  · rw [hb2, Bool.and_false]
```

Conversely, to introduce a disjunction — i.e., to show that it holds —
it suffices to show that one of its sides holds. This can be done via
the tactics {tactic}`left` and {tactic}`right`.  As their names imply,
the first one requires proving the left side of the disjunction, while
the second requires proving the right side.  Here is a trivial use...

```lean
theorem or_intro_l (a b : Prop) (h : a) : a ∨ b := by
  left; exact h
```

... and here is a slightly more interesting example requiring both
{tactic}`left` and {tactic}`right`:

```lean
theorem Nat.zero_or_succ (n : Nat) : n = 0 ∨ n = (n + 1).pred := by
  workinclass!
    cases n with
    | zero => left; rfl
    | succ n => right; rw [Nat.pred_succ]
```

:::::exercise (rating := 2) (name := "mul_is_zero") (checkVisibility := false)
```lean
theorem Nat.mul_is_zero (n m : Nat) (h : n * m = 0) : n = 0 ∨ m = 0 := by
  solution!
    cases m with
    | zero => right; rfl
    | succ m' =>
      cases n with
      | zero => left; rfl
      | succ n' =>
        rw [mul_succ, add_succ] at h
        contradiction
```
:::gradeTheorem 2 Nat.mul_is_zero
:::
:::::

:::::exercise (rating := 1) (name := "or_commute") (checkVisibility := false)
```lean
theorem or_commute (a b : Prop) (h : a ∨ b) : b ∨ a := by
  solution!
    obtain ha | hb := h
    · right; exact ha
    · left; exact hb
```
:::gradeTheorem 1 or_commute
:::
:::::

## Falsehood and Negation

Up to this point, we have mostly been concerned with proving
"positive" statements — addition is commutative, appending lists
is associative, etc.  We are sometimes also interested in negative
results, demonstrating that some proposition is _not_ true. Such
statements are expressed with the logical negation operator `¬`,
which is prefix notation for {lean}`Not`.

To see how negation works, recall the _principle of explosion_
from the {ref "Tactics"}[Tactics] chapter, which asserts that, if we assume a
contradiction, then any other proposition can be derived.

Following this intuition, we could define `¬ a` ("not `a`") as
`∀ c, a → c`.
Lean makes an equivalent but slightly different choice,
defining `¬ a` as `a → False`, where {lean}`False` is a specific
unprovable proposition defined in the standard library.

```lean (name := not)
#check Not
#print Not

example (a : Prop) : Not a = (a → False) := by rfl
example (a : Prop) : (¬ a) = (a → False) := by rfl
```

```leanOutput not
Not (a : Prop) : Prop
```

```leanOutput not
@[implicit_reducible] def Not : Prop → Prop :=
fun a => a → False
```

Eliminating a {lean}`False` hypothesis
works differently from eliminating the connectives above.
Since {lean}`False` carries no information, there's nothing to
extract. Rather, since {lean}`False` is a contradictory proposition,
the principle of explosion applies to it:
using {tactic}`cases` on a {lean}`False` in the context completes
any goal:

```lean
theorem ex_falso_quodlibet (a : Prop) (h : False) : a := by
  cases h
```

::::full
The Latin _ex falso quodlibet_ means, literally, "from falsehood
follows whatever you like"; this is another common name for the
principle of explosion.
::::

::::::full
:::::exercise (rating := 2) (name := "not_implies_other_not") (optional := true)
```lean
theorem not_implies_other_not (a : Prop) (h : ¬ a) :
    (∀ c : Prop, a → c) := by
  solution!
    intro c ha
    apply ex_falso_quodlibet
    apply h
    exact ha
```
:::::

::::::

Inequality is a very common form of negated statement, so there is a
special notation for it: `≠`, which is infix notation for {lean}`Ne`.

```lean (name := ne)
#print Ne
```

```leanOutput ne
@[reducible] def Ne.{u} : {α : Sort u} → α → α → Prop :=
fun {α} a b => ¬a = b
```

```lean
theorem zero_not_one : 0 ≠ 1 := by
  /- The proposition `0 ≠ 1` is exactly the same as `¬ (0 = 1)`
      — that is, `Not (0 = 1)` — which unfolds to `(0 = 1) → False`. -/
  /- To prove an inequality, we may assume the opposite equality... -/
  intro contra
  /- ...and deduce a contradiction from it. Here, the equality
      `0 = 1` corresponds to `zero = succ zero`, which contradicts
      disjointness of constructors `zero` and `succ`, so `contradiction`
      takes care of it. -/
  contradiction
```

It takes a little practice to get used to working with negation in Lean.
Even though _you_ may see perfectly well why a claim involving
negation holds, it can be a little tricky at first to see how to make
Lean understand it!

Here are proofs of a few familiar facts to help get you warmed up.

```lean
theorem not_False : ¬ False := by
  intro h; exact h

theorem contradiction_implies_anything (a b : Prop) (h : a ∧ ¬ a) : b := by
  workinclass!
    obtain ⟨ha, hna⟩ := h
    apply hna at ha
    cases ha

theorem double_neg (a : Prop) (ha : a) : ¬ ¬ a := by
  workinclass!
    intro h; apply h; exact ha
```

::::::full
:::::exercise (rating := 2) (name := "double_neg_informal") (level := Advanced) (optional := true) (manual := true)
Write an _informal_ proof of  {name}`double_neg`:
_Theorem_: `a` implies `¬ ¬ a`, for any proposition  `a`.

:::solution
_Proof_: Suppose some proposition `a` holds. We must show `¬ ¬ a` —
i.e., `¬ a → False`, so suppose `¬ a` as well and try to derive {name}`False`.
Then we have both `a` and `¬ a` (i.e., `a → False`) from which
we can indeed derive `False`. So `¬ ¬ a` holds.
:::

:::grade
`GRADE_MANUAL 2: double_neg_informal`
:::
:::::

:::::exercise (rating := 1) (name := "contrapositive")
```lean
theorem contrapositive (a b : Prop) (h : a → b) : (¬ b → ¬ a) := by
  solution!
    intro hnb ha
    apply hnb
    apply h
    exact ha
```
:::gradeTheorem 1 contrapositive
:::
:::::

:::::exercise (rating := 1) (name := "not_PNP_informal") (level := Advanced) (manual := true)
Write an informal proof of the proposition
{lean}`∀ a : Prop, ¬ (a ∧ ¬ a)`.

:::solution
_Proof_: Suppose, for some `a`, that `a ∧ ¬ a` holds.
Recall that `¬ a` is defined as `a → False`.
Given `a` and `a → False`, we can prove {name}`False`,
so `(a ∧ ¬ a) → False`, i.e. `¬ (a ∧ ¬ a)`.
:::

:::grade
`GRADE_MANUAL 1: not_PNP_informal`
:::
:::::

:::::exercise (rating := 2) (name := "de_morgan_not_or")
 _De Morgan's Laws_, named for Augustus De Morgan, describe how
negation interacts with conjunction and disjunction.  The
following law says that "the negation of a disjunction is the
conjunction of the negations." There is a dual law
`de_morgan_not_and_not` to which we will return at the end of this
chapter.

```lean
theorem de_morgan_not_or {a b : Prop} (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b := by
  solution!
    constructor
    · intro ha
      apply h
      left
      exact ha
    · intro hb
      apply h
      right
      exact hb
```
:::gradeTheorem 2 de_morgan_not_or
:::
:::::

:::::exercise (rating := 1) (name := "not_succ_inverse_pred") (optional := true)
Since we are working with natural numbers, we can disprove that
{lean}`Nat.succ` and {lean}`Nat.pred` are inverses of each other. This proof
will require you to come up with a specific _counterexample_ to the
claim being disproved:

```lean
theorem not_succ_pred_n : ¬ (∀ n : Nat, n.pred + 1 = n) := by
  solution!
    intro h
    have h0 := h 0
    rw [Nat.pred_zero] at h0
    contradiction
```
:::::

::::::

::::terse
Since inequality involves a negation, getting comfortable
with it also often requires a little practice.

A useful trick: if you are trying to prove a nonsensical goal,
apply {lean}`ex_falso_quodlibet` to change the goal to {lean}`False`. This
makes it easier to use assumptions of the form `¬ a`, and in
particular of the form `x ≠ y`.
::::

::::full
Since inequality involves a negation, it also requires a little
practice to be able to work with it fluently. Here is one useful trick.

If you are trying to prove a goal that is nonsensical (e.g., the
goal state is {lean}`false = true`), apply {lean}`ex_falso_quodlibet` to
change the goal to {lean}`False`.

This makes it easier to use assumptions of the form `¬ a` that may
be available in the context — in particular, assumptions of the
form `x ≠ y`.
::::

```lean
theorem not_true_is_false (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | false => rfl
  | true =>
    rw [Ne, Not] at h
    apply ex_falso_quodlibet
    apply h
    rfl
```

::::full
Since reasoning with {lean}`ex_falso_quodlibet` is quite common,
Lean provides a tactic, {tactic}`exfalso`, for applying it.

```lean
theorem not_true_is_false' (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | false => rfl
  | true =>
    exfalso
    rw [Ne, Not] at h
    apply h
    rfl
```
::::

::::quiz
To prove the following proposition, which tactics will we need
besides {tactic}`intro`, {tactic}`apply`, and {tactic}`exact`?

```display
∀ α : Type, ∀ x y : α, x = y ∧ x ≠ y → False
```

1. {tactic}`intro`, {tactic}`apply`, and {tactic}`exact` suffice
2. {tactic}`cases`
3. {tactic}`left` and/or {tactic}`right`
4. {tactic}`cases` and {tactic}`left` and/or {tactic}`right`
5. none of the above

:::quizSolution
```lean
example (α : Type) (x y : α) : x = y ∧ x ≠ y → False := by
  intro h; cases h with
  | _ h₁ h₂ => apply h₂; exact h₁
```
:::
::::

::::quiz
To prove the following proposition, which tactics will we need
besides {tactic}`intro`, {tactic}`apply`, and {tactic}`exact`?

```display
∀ a b : Prop, a ∨ b → ¬ ¬ (a ∨ b)
```

1. {tactic}`intro`, {tactic}`apply`, and {tactic}`exact` suffice
2. {tactic}`cases`
3. {tactic}`left` and/or {tactic}`right`
4. {tactic}`cases` and {tactic}`left` and/or {tactic}`right`
5. none of the above

:::quizSolution
```lean
example (a b : Prop) (h : a ∨ b) : ¬ ¬ (a ∨ b) := by
  intro hn; apply hn; exact h
```
:::
::::

::::quiz
To prove the following proposition, which tactics will we need
besides {tactic}`intro`, {tactic}`apply`, and {tactic}`exact`?

```display
∀ a b : Prop, a → (a ∨ ¬ ¬ b)
```

1. {tactic}`intro`, {tactic}`apply`, and {tactic}`exact` suffice
2. {tactic}`cases`
3. {tactic}`left` and/or {tactic}`right`
4. {tactic}`cases` and {tactic}`left` and/or {tactic}`right`
5. none of the above

:::quizSolution
```lean
example (a b : Prop) : a → (a ∨ ¬ ¬ b) := by
  intro h; left; exact h
```
:::
::::

::::quiz
To prove the following proposition, which tactics will we need
besides {tactic}`intro`, {tactic}`apply`, and {tactic}`exact`?

```display
∀ a b : Prop, a ∨ b → (¬ ¬ a) ∨ (¬ ¬ b)
```

1. {tactic}`intro`, {tactic}`apply`, and {tactic}`exact` suffice
2. {tactic}`cases`
3. {tactic}`left` and/or {tactic}`right`
4. {tactic}`cases` and {tactic}`left` and/or {tactic}`right`
5. none of the above

:::quizSolution
```lean
example (a b : Prop) : a ∨ b → (¬ ¬ a) ∨ (¬ ¬ b) := by
  intro h; cases h with
  | inl ha => left; intro hna; apply hna; exact ha
  | inr hb => right; intro hnb; apply hnb; exact hb
```
:::
::::

::::quiz
To prove the following proposition, which tactics will we need
besides {tactic}`intro`, {tactic}`apply`, and {tactic}`exact`?

```display
∀ a : Prop, 1 = 0 → (a ∨ ¬ a)
```

1. {tactic}`intro`, {tactic}`apply`, and {tactic}`exact` suffice
2. {tactic}`contradiction`
3. {tactic}`left` and/or {tactic}`right`
4. {tactic}`contradiction` and {tactic}`left` and/or {tactic}`right`
5. none of the above

:::quizSolution
```lean
example (a : Prop) : 1 = 0 → (a ∨ ¬ a) := by
  intro h; contradiction
```
:::
::::

## Truth

Besides {lean}`False`, Lean's standard library also defines {lean}`True`,
a proposition that is trivially true. To prove it, we use
the constructor {lean}`True.intro` explicitly, or the anonymous
constructor `⟨⟩`, or the {tactic}`constructor` tactic.

```lean
example : True := by exact True.intro
example : True := by exact ⟨⟩
example : True := by constructor
```

Unlike {lean}`False`, which is used extensively, {lean}`True` is used
relatively rarely: it is trivial (and therefore uninteresting)
to prove as a goal, and it provides no useful information
when it appears as a hypothesis.

::::::full
However, {lean}`True` can be quite useful when defining complex {lean}`Prop`s using
conditionals or as a parameter to higher-order {lean}`Prop`s. We'll come back
to this later.

For now, let's take a look at how we can use {lean}`True` and {lean}`False` to
achieve an effect similar to that of the {tactic}`contradiction` tactic, without
literally using {tactic}`contradiction`.

Pattern-matching lets us do different things for different
constructors.  If the result of applying two different
constructors were hypothetically equal, then we could use {tactic}`match`
to convert an unprovable statement (like {lean}`False`) to one that is
provable (like {lean}`True`).

```lean
def DiscrFun (n : Nat) : Prop :=
  match n with
  | 0 => True
  | _ + 1 => False

theorem discrFun_zero : DiscrFun 0 := by constructor

theorem discrFun_succ (n : Nat) : ¬ DiscrFun (n + 1) := by
  rw [DiscrFun]; intro h; assumption

theorem discr_example (n : Nat) : ¬ (0 = n + 1) := by
  intro h
  have hd : DiscrFun 0 := discrFun_zero
  apply discrFun_succ 0
  rw [h] at hd
  exact hd
```

To generalize this to other constructors, we simply have to provide
an appropriate variant of {lean}`DiscrFun`. To generalize it to other
conclusions, we can use {tactic}`exfalso` to replace them with {lean}`False`.
The {tactic}`contradiction` tactic takes care of all of this for us.

:::::exercise (rating := 2) (name := "nil_is_not_cons") (level := Advanced) (optional := true) (manual := true)
Use the same technique as above to show that `[] ≠ x :: xs`.
Do not use the {tactic}`contradiction` tactic.

```lean
-- SOLUTION
def List.IsNil {α : Type} (l : List α) : Prop :=
  match l with
  | [] => True
  | _ => False

theorem isNil_nil {α : Type} : List.IsNil ([] : List α) := by constructor

theorem isNil_cons {α} (x : α) (l : List α) : ¬ List.IsNil (x :: l) := by
  rw [List.IsNil, Not]
  . intro h; assumption
  . intro h; contradiction
-- END SOLUTION

theorem nil_is_not_cons {α : Type} (x : α) (xs : List α) :
    ¬ ([] = x :: xs) := by
  solution!
    intro h
    have hn : List.IsNil ([] : List α) := isNil_nil
    apply isNil_cons x xs
    rw [←h]
    exact hn
```

:::grade
`GRADE_MANUAL 2: nil_is_not_cons`
:::
:::::

:::dev "Niklas Halonen (xhalo32)"
In `List.IsNil` changing the `_ =>` arm to `_ :: _ =>` would introduce a hidden dependency to `List.All` (and `List.In`) which is not emitted to the grading variant because it's in a solution block.
This would lead to the solution of `List.All_In` (and `List.in_mem` in IndProp) to not pass comparator because the underlying terms are different.
TLDR: Don't change `List.IsNil` to use `_ :: _ =>`.
:::

::::::

## Logical Equivalence

The handy "if and only if" connective, which asserts that two
propositions have the same truth value, is a structure containing
the two implication directions. `a ↔ b` is notation for `Iff a b`.

::::full
In Lean, {lean}`Iff` is a structure packaging two fields and a
constructor. Given an {lean}`Iff` hypothesis, you eliminate it to
access its component implications: the "forward direction" via the
{lean}`Iff.mp` (short for _modus ponens_, the Latin name for reasoning
by implication) field, and the "reverse direction" via the
{lean}`Iff.mpr` (_modus ponens reverse_) field.

If your goal is an {lean}`Iff`, you introduce it by proving both
implication directions: convert the goal into two subgoals, one for
each direction, via the {lean}`Iff.intro` constructor, or just use the
{tactic}`constructor` tactic.
::::

::::terse
You can use {lean}`Iff.mp` to access the forward direction of the iff and
{lean}`Iff.mpr` to access the backwards direction — these eliminate an
iff — and {lean}`Iff.intro` to convert a goal of the form `a ↔ b`
to two goals of the form `a → b` and `b → a`, which
introduces an iff.
::::

```lean (name := iff)
#print Iff
```

```leanOutput iff
structure Iff (a b : Prop) : Prop
number of parameters: 2
fields:
  Iff.mp : a → b
  Iff.mpr : b → a
constructor:
  Iff.intro {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b
```

```lean
theorem iff_sym (a b : Prop) (h : a ↔ b) : b ↔ a := by
  workinclass!
    constructor
    · exact h.mpr
    · exact h.mp

theorem not_true_iff_false (b : Bool) : b ≠ true ↔ b = false := by
  constructor
  · apply not_true_is_false
  · intro h; rw [h]; intro h'; contradiction
```

:::::exercise (rating := 1) (name := "iff_properties") (optional := true) (checkVisibility := false)
Using the above proof that `↔` is symmetric ({lean}`iff_sym`) as a guide,
prove that it is also reflexive and transitive.

```lean
theorem iff_refl (a : Prop) : a ↔ a := by
  solution!
    constructor
    · intro h; exact h
    · intro h; exact h

theorem iff_trans (a b c : Prop) (h₁ : a ↔ b) (h₂ : b ↔ c) : a ↔ c := by
  solution!
    constructor
    · intro ha; apply h₂.mp; apply h₁.mp; exact ha
    · intro hb; apply h₁.mpr; apply h₂.mpr; exact hb
```
:::::

:::::full
::::exercise (rating := 3) (name := "iff_practice")
Prove the following theorems about {lean}`Iff`:

```lean
theorem or_associate (a b c : Prop) : a ∨ (b ∨ c) ↔ (a ∨ b) ∨ c := by
  solution!
    constructor
    · intro h
      obtain ha | (hb | hc) := h
      · left; left; exact ha
      · left; right; exact hb
      · right; exact hc
    · intro h
      obtain (ha | hb) | hc := h
      · left; exact ha
      · right; left; exact hb
      · right; right; exact hc
```

```lean
theorem mul_eq_0 (n m : Nat) :
    n * m = 0 ↔ n = 0 ∨ m = 0 := by
  solution!
    constructor
    · apply Nat.mul_is_zero
    · apply Nat.factor_is_zero
```

```lean
theorem or_distributes_over_and (a b c : Prop) :
    a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) := by
  solution!
    constructor
    · intro h
      obtain ha | ⟨hb, hc⟩ := h
      · constructor
        · left; exact ha
        · left; exact ha
      · constructor
        · right; exact hb
        · right; exact hc
    · intro h
      obtain ⟨ha | hb, ha | hc⟩ := h
      · left; exact ha
      · left; exact ha
      · left; exact ha
      · right; exact ⟨hb, hc⟩
```

:::gradeTheorem 1 or_associate mul_eq_0 or_distributes_over_and
:::
::::
:::::

## Existential Quantification

:::dev "Mike Hicks (mwhicks1)"
It would be convenient to declare the variables below so that later code
blocks can use `α`, `β`, `x`, `y`, `l`, `f`, `g`, and `p` without repeating
their type annotations, but doing so adds all of them to every proof
context and leanOutput.

```
-- variable (α β : Type) (x x' y : α) (l l' : List α) (f g : α → β) (p : α → Prop)
```
:::

::::full
Another fundamental logical connective is _existential quantification_.
To say that there is some `x` of type `α` such that some property `a`
holds of `x`, we write `∃ x : α, a`. This is notation for the {lean}`Exists`
connective, and is defined as `Exists (fun (x : α) => a)`.
As with `∀ x : α`, the type annotation `: α` can be omitted if Lean
is able to infer from the context what the type of `x` should be.

To introduce a statement of the form `∃ x, a`, we must show that `a`
holds for some specific choice for `x`, known as the _witness_ of the
existential.  This is done in two steps: First, we explicitly tell Lean
which witness `y` we have in mind by invoking the tactic `exists y`.
Then we prove that `a` holds after all occurrences of `x`
are replaced by `y`. The {tactic}`exists` tactic tries to close the proof
with simple tactics such as {tactic}`rfl` or {tactic}`contradiction`, so we may not
have to prove `a` explicitly.
::::

```lean (name := exists)
#check Exists
```

```leanOutput exists
Exists.{u} {α : Sort u} (p : α → Prop) : Prop
```

```lean (name := ep)
def Nat.Even x := ∃ n : Nat, x = Nat.double n

#check (Nat.Even)
```

```leanOutput ep
Nat.Even : Nat → Prop
```

```lean
open Nat in
example : Even 4 := by exists 2
  -- `4 = double 2` holds by `rfl`,
  -- but is proven automatically by `exists`
```

Conversely, to eliminate an existential hypothesis `∃ x, a` in
the context, we destructure it to obtain a witness `x` and a
hypothesis stating that `a` holds of `x`.

```lean
example (n : Nat) : (∃ m, n = m + 4) → (∃ o, n = o + 2) := by
  intro ⟨m, hm⟩
  exists (m + 2)
```

::::::full
:::::exercise (rating := 1) (name := "dist_not_exists")
Prove that if `a` holds for all `x`, then there is no `x` for which
`a` does not hold. (Hint: `cases` and `obtain` work on existential assumptions!)

```lean
theorem dist_not_exists (α : Type) (p : α → Prop) (h : ∀ x, p x) :
    ¬ (∃ x, ¬ p x) := by
  solution!
    intro ⟨x, hx⟩
    apply hx; apply h
```

:::gradeTheorem 1 dist_not_exists
:::
:::::

:::::exercise (rating := 2) (name := "dist_exists_or")
Prove that existential quantification distributes over disjunction.

```lean
theorem dist_exists_or (α : Type) (p q : α → Prop) :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  solution!
    constructor
    · intro h
      obtain ⟨x, hp | hq⟩ := h
      · left; exists x
      · right; exists x
    · intro h
      obtain ⟨x, hx⟩ | ⟨x, hx⟩ := h
      · exists x; left; exact hx
      · exists x; right; exact hx
```

:::gradeTheorem 2 dist_exists_or
:::
:::::

:::::hide
:::dev "Yipeng Liu (berberman)"

TODO: Convert to prop version and move to IndProp chapter.

-- exercise (rating := 3) (name := "ble_plus_exists")
```lean
theorem ble_plus_exists (n m : Nat) : (Nat.ble n m = true) → ∃ x, m = x + n := by
  solution!
    induction n generalizing m with
    | zero => intro h; exists m
    | succ n' ih =>
      cases m with
      | zero => intro h; contradiction
      | succ m' =>
        intro h
        rw [succ_ble_succ] at h
        apply ih at h
        obtain ⟨x, hx⟩ := h
        exists x
        rw [hx]
        rfl

-- SOLUTION
theorem ble_plus (n m : Nat) : Nat.ble n (m + n) = true := by
  induction n with
  | zero => rfl
  | succ n' ih => rw [Nat.add_succ m, succ_ble_succ]; exact ih
-- END SOLUTION

theorem add_exists_ble (n m : Nat) (h : ∃ x, m = x + n) : Nat.ble n m = true := by
  solution!
    obtain ⟨x, hx⟩ := h
    rw [hx]
    apply ble_plus
```
```
/- A direct proof without a lemma. -/
theorem add_exists_ble' : ∀ n m, (∃ x, m = x + n) → Nat.ble n m = true := by
  intro n
  induction n with
  | zero => intro m h; rfl
  | succ n' ih =>
    intro m ⟨x, hx⟩
    rw [hx, Nat.add_succ x, succ_ble_succ]
    apply ih; exists x
```
:::
:::::

::::::

# Recap: Logical Connectives in Lean

Connectives introduced in this chapter:
- `a ∧ b` (conjunction):
  - introduced with {tactic}`constructor`
  - eliminated with `intro ⟨ha, hb⟩` or `obtain ⟨ha, hb⟩ := h`
- `a ∨ b` (disjunction):
  - introduced with {tactic}`left` and {tactic}`right`
  - eliminated with {tactic}`cases` or `obtain h | h := h`
- {lean}`False` (falsehood):
  - eliminated with {tactic}`cases` or {tactic}`contradiction`
- `¬ a` (negation):
  - defined as `a → False`
- {lean}`True` (truth):
  - introduced as {lean}`True.intro` or with {tactic}`constructor`
- `a ↔ b` (iff):
  - introduced with {tactic}`constructor`
  - eliminated with `intro ⟨hab, hba⟩`, `obtain ⟨hab, hba⟩ := h`, or {name}`Iff.mp` and {lean}`Iff.mpr`
- `∃ x : α, a` (existential):
  - introduced with `exists y`
  - eliminated with `intro ⟨x, hx⟩` or `obtain ⟨x, hx⟩ := h`

Fundamental connectives we've been using since the beginning:
- equality (`x = y`)
- implication (`a → b`)
- universal quantification (`∀ x, a`)

# Programming with Propositions

::::full
The logical connectives that we have seen provide a rich vocabulary
for defining complex propositions from simpler ones.
To illustrate, let's look at how to express the claim that an element `x`
occurs in a list `l`.
Notice that this property has a simple recursive structure:
::::

::::terse
What does it mean to say that
"an element `x` occurs in a list `l`"?
::::

- If `l` is the empty list, then `x` cannot occur in it,
  so the property "`x` appears in `l`" is simply false.
- Otherwise, `l` has the form `x' :: l'`.
  In this case, `x` occurs in `l` if it is equal to `x'`
  or if it occurs in `l'`.

We can translate this directly into a straightforward recursive function
taking an element and a list and returning... a proposition!

```lean
def List.In {α : Type} (x : α) (xs : List α) : Prop :=
  match xs with
  | [] => False
  | x' :: xs' => x = x' ∨ In x xs'

theorem List.In_nil {α : Type} {x : α} : ¬ (List.In x []) := by
  rw [List.In]; intro h; assumption

theorem List.In_cons {α : Type} {x x' : α} {xs : List α} :
  List.In x (x' :: xs) = (x = x' ∨ List.In x xs) := by rfl
```

When {lean}`List.In` is applied to a concrete list, it expands into a concrete sequence
of nested disjunctions.

```lean
example : List.In 4 [1, 2, 3, 4, 5] := by
  workinclass!
    rw [List.In]; right; right; right; left; rfl

example (n : Nat) (h : List.In n [2, 4]) :
  ∃ n' : Nat, n = 2 * n' := by
    workinclass!
      rw [List.In] at h
      obtain h | h | h := h
      · exists 1
      · exists 2
      . contradiction
```

We can also reason about more generic statements involving {lean}`List.In`.

```lean
theorem List.In_map {α β : Type} {f : α → β} {xs : List α} {x : α}
  (h : In x xs) : In (f x) (map f xs) := by
  induction xs with
  | nil =>
    apply In_nil at h; contradiction
  | cons x' xs' ih =>
    rw [In_cons] at h
    obtain h | h := h
    · rw [h, map_cons, In_cons]; left; rfl
    · rw [map_cons, In_cons]; right; exact ih h
```

::::::full
This way of defining propositions recursively is very convenient in
some cases, less so in others.  In particular, it is subject to the
usual restrictions regarding definitions of recursive functions,
e.g., the requirement that they be "obviously terminating."

In the next chapter, we will see how to define propositions
_inductively_ — a different technique with its own strengths and
limitations.

:::::exercise (rating := 2) (name := "In_map_iff")
```lean
theorem List.In_map_iff {α β : Type} {f : α → β} {xs : List α} {y : β} :
    In y (map f xs) ↔ ∃ x, f x = y ∧ In x xs := by
  constructor
  · solution!
      induction xs with
      | nil =>
        intro h; rw [map_nil] at h
        exfalso; apply List.In_nil; assumption
      | cons x' xs' ih =>
        intro h
        rw [List.map_cons, In_cons] at h
        obtain h | h := h
        · rw [h]; exists x'
          constructor
          · rfl
          · rw [In_cons]; left; rfl
        · obtain ⟨x', h₁, h₂⟩ := ih h
          exists x'
          constructor
          · exact h₁
          · rw [In_cons]; right; exact h₂
  · solution!
      intro ⟨x, h₁, h₂⟩
      rw [← h₁]; apply In_map; exact h₂
```
:::gradeTheorem 2 List.In_map_iff
:::
:::::

::::::

::::::full
:::::exercise (rating := 3) (name := "All")
We noted above that functions returning propositions can be seen as
_properties_ of their arguments. For instance, if `p` has type
{lean}`Nat → Prop`, then `p n` says that property `p` holds of `n`.

Drawing inspiration from {lean}`List.In`, write a recursive function `All`
stating that some property `p` holds of all elements of a list
`l`. To make sure your definition is correct, prove the `All_In`
lemma below.  (Of course, your definition should _not_ just
restate the left-hand side of `All_In`.)

```lean
def List.All {α : Type} (p : α → Prop) (l : List α) : Prop := solution!(
  match l with
  | [] => True
  | x :: l' => p x ∧ List.All p l')
theorem List.All_nil {α : Type} {a : α → Prop} : List.All a [] := solution!(by constructor)

theorem List.All_cons {α : Type} {p : α → Prop} {x : α} {l : List α} :
    List.All p (x :: l) = (p x ∧ All p l) := solution!(rfl)

theorem List.All_In {α : Type} {p : α → Prop} {l : List α} :
    (∀ x : α, In x l → p x) ↔ All p l := by
  solution!
    induction l with
    | nil =>
      constructor
      · intro _; exact All_nil
      · intro _ _ h; apply In_nil at h; contradiction
    | cons x' xs' ih =>
      obtain ⟨ih₁, ih₂⟩ := ih
      constructor
      · intro h
        rw [All_cons]
        constructor
        · apply h; rw [In_cons]; left; rfl
        · apply ih₁
          intro x' hx'; apply h
          rw [In_cons]; right; exact hx'
      · rw [All_cons]
        intro ⟨hx, hp⟩ x' h
        rw [In_cons] at h
        obtain h₁ | h₂ := h
        · rw [h₁]; exact hx
        · apply ih₂; apply hp; exact h₂
```

:::autogradedHole List.All
:::
:::gradeTheorem 3 List.All_In
:::
:::::

:::dev "Yipeng Liu (berberman)"
I found this exercise combining too many awkward details for too little conceptual payoff:
1. the construction is artificial
2. before `simp` is introduced, `bif` requires noisy `rw` and Boolean case equations
:::

:::::exercise (rating := 2) (name := "CombineOddEven") (optional := true)
Complete the definition of `CombineOddEven` below. It takes as arguments
two properties of numbers, `Odd` and `Even`, and it should return
a predicate `p` such that `p n` is equivalent to `Odd n` when `n` is odd
and equivalent to `Even n` otherwise.

```lean
def CombineOddEven (Odd Even : Nat → Prop) : Nat → Prop := solution!(
  fun n => bif Nat.odd n then Odd n else Even n)
```

To test your definition, prove the following facts:

```lean
theorem combineOddEven_intro (Odd Even : Nat → Prop)
    (n : Nat)
    (hOdd : Nat.odd n = true → Odd n)
    (hEven : Nat.odd n = false → Even n) :
    CombineOddEven Odd Even n := by
  solution!
    rw [CombineOddEven]
    /- `cases h : Nat.odd n` splits on `Nat.odd n` and records
      the corresponding equation as `h`. -/
    cases h : Nat.odd n with
    | false =>
      apply hEven
      rw [h]
    | true =>
      apply hOdd
      exact h

theorem combineOddEven_elim_odd
    (Odd Even : Nat → Prop)
    (n : Nat)
    (h : CombineOddEven Odd Even n)
    (hOdd : Nat.odd n = true) : Odd n := by
  solution!
    rw [CombineOddEven, hOdd, Bool.cond_true] at h
    exact h

theorem combineOddEven_elim_even
    (Odd Even : Nat → Prop)
    (n : Nat)
    (h : CombineOddEven Odd Even n)
    (hOdd : Nat.odd n = false) : Even n := by
  solution!
    rw [CombineOddEven, hOdd, Bool.cond_false] at h
    exact h
```

:::::

::::::

# Applying Theorems to Arguments

::::full
Lean treats _proofs_ as first-class objects.
There is a great deal to be said about this, but it is not necessary
to understand it all to use Lean. This section gives just a taste.
::::

:::dev "Daniel Sainati (@dsainati1)" PotentialImprovement
Add this text back later if and when these chapters actually exist:

leaving a deeper exploration for the optional chapters
`ProofObjects` and `IndPrinciples`.
:::

::::terse
Lean also treats _proofs_ as first-class objects!
::::

We have seen that we can use `#check` to ask Lean whether an expression
has a given type:

```lean
#check (Nat.add : Nat → Nat → Nat)
```

We can also use it to check what theorem a particular identifier refers to:

```lean (name := add_comm)
#check Nat.add_comm
```
```leanOutput add_comm
Nat.add_comm (n m : Nat) : n + m = m + n
```

```lean (name := add_assoc)
#check Nat.add_assoc
```
```leanOutput add_assoc
Nat.add_assoc (n m k : Nat) : n + m + k = n + (m + k)
```

Lean checks the _statements_ of the {lean}`Nat.add_comm` and {lean}`Nat.add_assoc` theorems
in the same way that it checks the _type_ of any term (e.g., {lean}`Nat.add`).
If we leave off the colon and the type, Lean prints these types
in the infoview for us.

Why?

The reason is that the identifier {lean}`Nat.add_comm` actually refers to a
_proof object_ — a logical derivation establishing the truth of the
statement {lean}`∀ n m : Nat, n + m = m + n`. The type of this object
is the proposition that it is a proof of.

The type of an ordinary function tells us what we can do with it.
  - If we have a term of type {lean}`Nat → Nat → Nat`, we can give it
    two {lean}`Nat`s as arguments and get a {lean}`Nat` back.
Similarly, the statement of a theorem tells us what we can use
that theorem for.
  - If we have a term of type {lean}`∀ n m : Nat, n = m → n + n = m + m`,
    and we provide it two numbers `n` and `m` and a third "argument"
    of type `n = m`, we get back a proof object of type `n + n = m + m`.

::::full
Operationally, this analogy goes even further: by applying a theorem
as if it were a function, i.e., applying it to values and hypotheses
with matching types, we can specialize its result without having to
resort to intermediate assertions. For example, suppose we wanted
to prove the following result:
::::

::::terse
Lean actually allows us to _apply_ a theorem as if it were
a function. This is often handy in proof scripts — e.g., suppose
we want to prove the following:
::::

```lean +error (name := comm)
example (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [Nat.add_comm]
  rw [Nat.add_comm]
```

```leanOutput comm
unsolved goals
x y z : Nat
⊢ x + (y + z) = z + y + x
```

It appears at first sight that we ought to be able to prove this
by rewriting with {lean}`Nat.add_comm` twice to make the two sides match.
The problem is that the second rewrite undoes the effect
of the first, leaving us back where we started...

We encountered similar issues back in the Induction chapter, and we
saw that we can fix them by applying {lean}`Nat.add_comm` to the arguments we want it
to be instantiated with, in much the same way as we apply
a polymorphic function to a type argument. Then the rewrite is forced
to happen exactly where we want it.

```lean
example (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [Nat.add_comm]
  rw [Nat.add_comm z y]
```

::::full
If we really wanted, we could in fact do it for both rewrites.

```lean
example (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [Nat.add_comm x (y + z)]
  rw [Nat.add_comm z y]
```
::::

The fact that implications are functions means we can prove them by
explicitly providing a function.

```lean
theorem identity {a : Prop} : a → a := fun h => h
```

::::terse
```lean
namespace FunctionTheoremQuiz
```
::::

::::quiz
Suppose we have

```display
n m : Nat
h₁ : n = m
h₂ : m = 42
trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z
```

What is the type of this "proof object"?

```display
@trans_eq Nat n m 42 h₁ h₂
```

1. `n = m`
2. `42 = n`
3. `n = 42`
4. Does not typecheck

:::quizSolution
```lean
example (n m : Nat) (h₁ : n = m) (h₂ : m = 42)
    (trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z) : n = 42 :=
  @trans_eq Nat n m 42 h₁ h₂
```
:::
::::

::::quiz
Suppose, again, we have

```display
n m : Nat
h₁ : n = m
h₂ : m = 42
trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z
```

What is the type of this proof object?

```display
trans_eq h₁ h₂
```

1. `n = m`
2. `42 = n`
3. `n = 42`
4. Does not typecheck

:::quizSolution
```lean
example (n m : Nat) (h₁ : n = m) (h₂ : m = 42)
    (trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z) : n = 42 :=
  trans_eq h₁ h₂
```
:::
::::

::::quiz
Suppose, again, we have

```display
n m : Nat
h₁ : n = m
h₂ : m = 42
trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z
```

What is the type of this proof object?

```display
@trans_eq Nat m 42 n h₂
```

1. `m = n`
2. `m = n → 42 = n`
3. `42 = n → m = n`
4. Does not typecheck

:::quizSolution
```lean
example (n m : Nat) (h₁ : n = m) (h₂ : m = 42)
    (trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z) :
    42 = n → m = n :=
  @trans_eq Nat m 42 n h₂
```
:::
::::

::::quiz
Suppose, again, we have

```display
n m : Nat
h₁ : n = m
h₂ : m = 42
trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z
```

What is the type of this proof object?

```display
@trans_eq _ 42 n m
```

1. `n = m → m = 42 → n = 42`
2. `42 = n → n = m → 42 = m`
3. `n = 42 → 42 = m → n = m`
4. Does not typecheck

:::quizSolution
```lean
example (n m : Nat) (h₁ : n = m) (h₂ : m = 42)
    (trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z) :
    42 = n → n = m → 42 = m :=
  @trans_eq _ 42 n m
```
:::
::::

::::quiz
Suppose, again, we have

```display
n m : Nat
h₁ : n = m
h₂ : m = 42
trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z
```

What is the type of this proof object?

```display
trans_eq h₂ h₁
```

1. `m = n`
2. `42 = n`
3. `n = 42`
4. Does not typecheck

:::quizSolution
```lean +error (name := qe)
example (n m : Nat) (h₁ : n = m) (h₂ : m = 42)
    (trans_eq : ∀ {α : Type} {x y z : α}, x = y → y = z → x = z) : True := by
  have := trans_eq h₂ h₁
```

```leanOutput qe
Application type mismatch: The argument
  h₁
has type
  n = m
but is expected to have type
  42 = ?m.13
in the application
  trans_eq h₂ h₁
```

:::
::::

::::terse
```lean
end FunctionTheoremQuiz
```
::::

::::full
As an aside, some tactics that accept an `at` clause can target
several locations at once, including the goal, written using the `⊢` symbol, by listing them
together after `at` — for instance, both {tactic}`rw` and
{tactic}`dsimp` support this.
::::

::::terse
Aside: some tactics, like {tactic}`rw` and {tactic}`dsimp`, can list
several locations at once with `at`, including the goal:
::::

```lean
example (n m : Nat) (h : n + 0 = m) : n = m + 0 := by
  rw [Nat.add_zero] at h ⊢
  assumption
```

# Working with Decidable Properties

We've seen two different ways of expressing logical claims in Lean:
with _booleans_ (of type {lean}`Bool`), and with _propositions_ (of type {lean}`Prop`).
Here are the key differences between {lean}`Bool` and {lean}`Prop`:

```display
|                     | `Bool` | `Prop` |
| ------------------- | ------ | ------ |
| decidable?          | yes    | no     |
| usable with match?  | yes    | no     |
```

::::full
The crucial difference between the two worlds is _decidability_.
Every (closed) expression of type {lean}`Bool` can be simplified in a finite
number of steps to either {lean}`true` or {lean}`false` — i.e., there is a terminating
mechanical procedure for deciding whether or not it is {lean}`true`.

This means that, for example, the type {lean}`Nat → Bool` is inhabited only by
functions that, given a {lean}`Nat`, always yield either {lean}`true` or {lean}`false` in
finite time; this, in turn, means (by a standard computability argument)
that there is _no_ function in {lean}`Nat → Bool` that checks whether a given
number is the code of a terminating Turing machine.

By contrast, the type {lean}`Prop` includes both decidable and undecidable
mathematical propositions; in particular, the type {lean}`Nat → Prop`
does contain functions representing properties like
"the nth Turing machine halts."

The second table row follows directly from this essential difference.
To evaluate a pattern match (or conditional) on a boolean, we need to know
whether the scrutinee evaluates to {lean}`true` or {lean}`false`; this only works for
{lean}`Bool`, not {lean}`Prop`.
::::

::::terse
Since functions in Lean by default must terminate on all inputs,
a terminating function of type {lean}`Nat → Bool` is a _decision procedure_ —
i.e., it yields {lean}`true` or {lean}`false` on all inputs.

For example, {lean}`Nat.even` is a decision procedure for the property
"is even".
::::

Since {lean}`Prop` includes _both_ decidable and undecidable properties,
we have two options when we want to formalize a property that happens
to be decidable: we can express it either as a boolean computation,
or as a function into {lean}`Prop`.

For instance, to claim that a number `n` is even,
we can say either that `Nat.even n` evaluates to `true`...

```lean
example : Nat.even 42 = true := by rfl
```

... or that there exists some `k` such that `n = double k`.

```lean
example : Nat.Even 42 := by rw [Nat.Even]; exists 21
```

Of course, it would be deeply strange if these two characterizations
of evenness did not describe the same set of natural numbers!
Fortunately, they do!

To prove this, we first need two helper lemmas.

```lean
theorem even_double (k : Nat) :
    Nat.even (Nat.double k) = true := by
  induction k with
  | zero => rw [Nat.double_zero]; rfl
  | succ k' ih => rw [Nat.double_succ]; exact ih
```

:::dev "Yipeng Liu (berberman)"
Same issue as `CombineOddEven`.
:::

:::::exercise (rating := 3) (name := "even_double_conv") (checkVisibility := false)
```lean
theorem even_double_conv (n : Nat) : ∃ k : Nat,
    n = bif Nat.even n then Nat.double k else Nat.double k + 1 := by
  solution!
    induction n with
    | zero =>
      rw [Nat.even_zero]
      exists 0  -- (`0 = Nat.double 0` is closed by `exists`'s final `rfl`)
    | succ n' ihn =>
      obtain ⟨k', ihk⟩ := ihn
      rw [Nat.even_succ]
      cases h : Nat.even n' with
      | false =>
        rw [h] at ihk; rw [not] at *; rw [Bool.cond_false] at ihk
        exists (k' + 1); rw [ihk, Bool.cond_true, Nat.double_succ]
      | true =>
        rw [h] at ihk; rw [not] at *; rw [Bool.cond_true] at ihk
        exists k'; congr
```
:::gradeTheorem 3 even_double_conv
:::
:::::

Now the main theorem:

```lean
theorem Nat.even_bool_prop (n : Nat) : Nat.even n = true ↔ Even n := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := even_double_conv n
    rw [h] at hk; rw [Bool.cond_true] at hk; rw [Even]; exists k
  · intro ⟨k, hk⟩; rw [hk]; apply even_double
```

In view of this theorem, we can say that the boolean computation `Nat.even n`
is _reflected_ in the truth of the proposition `∃ k, n = Nat.double k`.

::::hide
Similarly, we can state what it means for a number to be nonzero
in two different ways:

```lean
def Nonzero (n : Nat) : Prop := ∃ m, n = Nat.succ m

def nonzero (n : Nat) := not (n == 0)

theorem nonzero_bool_prop (n : Nat) :
    nonzero n = true ↔ Nonzero n := by
  workinclass!
    constructor
    · intro h
      cases n with
      | zero =>
        rw [nonzero, not] at h; contradiction
      | succ n' => rw [Nonzero]; exists n'
    · intro ⟨m, hm⟩; rw [hm]; rfl
```
::::

Similarly, to state that two numbers `n` and `m` are equal,
we can say either

1. that `n == m` returns {lean}`true`, or
2. that `n = m`.

Again, these two notions are equivalent.

```lean
theorem beq_eq_true (n m : Nat) :
    (n == m) = true ↔ n = m := by
  rw [Nat.beq_eq_true_eq]
```

(We use {name}`Nat.beq_eq_true_eq` because `n == m` is a wrapper of {inst}`DecidableEq Nat`.
We will go over this in the {ref "Typeclasses"}[Typeclasses] chapter.)

So what should we do in situations where some claim could be formalized
as either a proposition or a boolean computation?
Which should we choose?

In general, _both_ can be useful. For example, booleans are more useful
for defining functions, since we can test whether they are true using
conditional expressions.

```lean
def is_even_prime (n : Nat) : Bool :=
  bif n == 2 then true else false
```

::::full
Beyond the fact that non-computable properties are impossible
in general to phrase as boolean computations, even many _computable_
properties are easier to express using {lean}`Prop` than {lean}`Bool`, since
recursive function definitions are subject to significant restrictions.
For instance, the {ref "Automation"}[Automation] chapter shows how to define the property that
a regular expression matches a given string using {lean}`Prop`.
Doing the same with {lean}`Bool` would amount to writing a regular expression
matching algorithm, which would be more complicated, harder to understand,
and harder to reason about than a simple (non-algorithmic) definition
of this property.

Conversely, an important side benefit of stating facts using booleans
is enabling some proof automation through computation with terms, a
technique known as _proof by reflection_.
::::

::::terse
An important benefit of stating facts using booleans
is enabling some proof automation through computation with terms, a
technique known as _proof by reflection_.
::::

Consider the following statement:

```display
Nat.Even 100
```

The most direct way to prove this is to give the value of `k` explicitly.

```lean
example : Nat.Even 100 := by
  exists 50
```

The proof of the corresponding boolean statement is simpler,
because we don't have to invent the witness {lean}`50`:
computation does it for us!

```lean
example : Nat.even 100 = true := by rfl
```

:::dev "Mike Hicks (mwhicks1)"
Basically this is saying that computation is a good proof tactic. But this is a little confusing to me because we seem to want to eschew computation in favor of "simplification rules", which imply a preference for the Prop version, despite the downside shown here.
:::

Now, the useful observation is that, since the two notions are equivalent,
we can use the boolean formulation to prove the other one
without mentioning the value 50 explicitly:

```lean
example : Nat.Even 100 := by
  obtain ⟨h, _⟩ := Nat.even_bool_prop 100
  apply h; rfl
```

Although we haven't gained much in terms of proof-script simplicity
in this case, larger proofs can often be made considerably simpler
by the use of reflection.

::::full
As an extreme example, a famous mechanized proof of the even more famous
_four-color theorem_ uses reflection to reduce the analysis of hundreds
of different cases to a boolean computation.
::::

Another advantage of booleans is that the _negation_ of a claim about
booleans is straightforward to state and (when true) to prove:
simply flip the expected boolean result.

```lean
example : Nat.even 101 = false := by rfl
```

In contrast, propositional negation can be difficult to work with directly.
For example, suppose we state the nonevenness of {lean}`101` propositionally:

```display
¬ Nat.Even 101
```

Proving this directly — by assuming that there is some `n` such that
`101 = Nat.double n` and then somehow reasoning to a contradiction —
would be rather complicated.

But if we convert it to a claim about the boolean {lean}`Nat.even` function,
we can let Lean do the work for us.

```lean
example : ¬ Nat.Even 101 := by
  workinclass!
    intro h; apply (Nat.even_bool_prop 101).mpr at h
    rw [Nat.even] at h; contradiction
```

Conversely, there are situations where it can be easier to work with
propositions rather than booleans. In particular, knowing that
`(n == m) = true` is generally of little direct help in the middle of
a proof involving `n` and `m`. But if we convert the statement to
the equivalent form `n = m`, then we can easily rewrite with it.

```lean
theorem add_beq_true (n m p : Nat) (h : (n == m) = true) :
    (n + p == m + p) = true := by
  workinclass!
    apply (beq_eq_true n m).mp at h
    rw [h, BEq.refl]
```

::::full
We'll come back to
reflection and decidable propositions in a later chapter,
but the examples above already illustrate the different strengths
of booleans and general propositions.
Being able to cross back and forth between the boolean and propositional
worlds will often be convenient in later chapters.
::::

::::::full
:::::exercise (rating := 2) (name := "logical_connectives")
The following theorems relate the propositional connectives studied
in this chapter to the corresponding boolean operations.

```lean
theorem andb_true_iff (b1 b2 : Bool) :
    (b1 && b2) = true ↔ b1 = true ∧ b2 = true := by
  solution!
    constructor
    · intro h
      cases b1 with
      | false => rw [and] at h; contradiction
      | true => rw [and] at h; exact ⟨rfl, h⟩
    · intro h
      cases b1 with
      | false => exfalso; cases h.left
      | true => rw [and]; exact h.right

theorem orb_true_iff (b1 b2 : Bool) :
    (b1 || b2) = true ↔ b1 = true ∨ b2 = true := by
  solution!
    constructor
    · intro h
      cases b1 with
      | false => rw [or] at h; right; exact h
      | true => rw [or] at h; left; rfl
    · intro h
      cases b1 with
      | false =>
        obtain h | h := h
        · contradiction
        · rw [or]; exact h
      | true => rw [or]
```

:::gradeTheorem 1 andb_true_iff
:::

:::gradeTheorem 2 orb_true_iff
:::
:::::

:::::exercise (rating := 3) (name := "beqList")
Given a boolean operator `beq` for testing equality of elements
of some type `α`, we can define a function `beqList` for testing
equality of lists with elements in `α`. Complete the definition
of the `beqList` function below. To make sure that your definition
is correct, prove the lemma `beqList_true_iff`.

```lean
def beqList {α : Type} (beq : α → α → Bool) (xs ys : List α) : Bool := solution!(
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => beq x y && beqList beq xs ys
  | _, _ => false)

theorem beqList_nil_nil {α : Type} {beq : α → α → Bool} :
    beqList beq [] [] = true := solution!(rfl)

theorem beqList_cons_cons {α : Type} {beq : α → α → Bool}
    {x y : α} {xs ys : List α} :
    beqList beq (x :: xs) (y :: ys) = (beq x y && beqList beq xs ys) :=
  solution!(rfl)

theorem beqList_nil_cons {α : Type} {beq : α → α → Bool}
    {x : α} {xs : List α} : beqList beq [] (x :: xs) = false := solution!(rfl)

theorem beqList_cons_nil {α : Type} {beq : α → α → Bool}
    {x : α} {xs : List α} : beqList beq (x :: xs) [] = false := solution!(rfl)

theorem beqList_true_iff α (beq : α → α → Bool)
    (h : ∀ (x y : α), beq x y = true ↔ x = y) :
    ∀ {xs ys : List α}, beqList beq xs ys = true ↔ xs = ys := by
  solution!
    intro xs;
    induction xs with
    | nil =>
      intro ys
      cases ys with
      | nil =>
        rw [beqList_nil_nil]
        constructor
        · intro; rfl
        · intro; rfl
      | cons y ys =>
        rw [beqList_nil_cons]
        constructor
        · intro; contradiction
        · intro; contradiction
    | cons x xs ih =>
      intro ys
      cases ys with
      | nil =>
        rw [beqList_cons_nil]
        constructor
        · intro; contradiction
        · intro; contradiction
      | cons y ys =>
        rw [beqList_cons_cons]
        obtain ⟨h₁, h₂⟩ := andb_true_iff (beq x y) (beqList beq xs ys)
        obtain ⟨hx, hy⟩ := h x y
        obtain ⟨ih₁, ih₂⟩ := ih
        constructor
        · intro h
          congr
          · exact hx (h₁ h).left
          · exact ih₁ (h₁ h).right
        · intro h
          injection h with hxy hxsys
          apply h₂
          exact ⟨hy hxy, ih₂ hxsys⟩
```

:::autogradedHole beqList
:::
:::gradeTheorem 3 beqList_true_iff
:::
:::::

::::::

::::::full
:::::exercise (rating := 2) (name := "List.allb")
Prove the theorem below, which relates `List.allb`, from the exercise
`Tactics.forall_exists_challenge`, to the {lean}`List.All` property defined above.

Copy the definition of `List.allb` from Tactics here so that this file can be
graded on its own.

```lean
def List.allb {α : Type} (test : α → Bool) (l : List α) : Bool := solution!(
  match l with
  | [] => true
  | x :: xs' => test x && allb test xs')

theorem List.allb_nil {α : Type} {test : α → Bool} : allb test [] = true := solution!(rfl)

theorem List.allb_cons {α : Type} {test : α → Bool} {x : α} {l : List α} :
    allb test (x :: l) = (test x && allb test l) := solution!(rfl)

theorem List.allb_true_iff α {test : α → Bool} {l : List α} :
    allb test l = true ↔ All (fun x => test x = true) l := by
  solution!
    induction l with
    | nil =>
      rw [allb_nil]
      constructor
      · intro _
        apply All_nil
      · intro _
        rfl
    | cons x xs' ih =>
      obtain ⟨h₁, h₂⟩ := andb_true_iff (test x) (allb test xs')
      obtain ⟨ih₁, ih₂⟩ := ih
      rw [allb_cons, All_cons]
      constructor
      · intro h; exact ⟨(h₁ h).left, ih₁ (h₁ h).right⟩
      · intro ⟨h₁', h₂'⟩; exact h₂ ⟨h₁', ih₂ h₂'⟩
```

(Ungraded thought question) Are there any important properties of
the function {lean}`List.allb` that are not captured by this specification?

:::solution
This theorem exactly captures the input-output behavior of {lean}`List.allb`.
However, it does not say anything about the running time.
:::

:::autogradedHole List.allb
:::
:::gradeTheorem 2 List.allb_true_iff
:::
:::::

::::::

# The Logic of Lean

::::full
Lean's logical core differs in some important ways from other formal
systems that are used by mathematicians to write down precise and rigorous
definitions and proofs — in particular from Zermelo–Fraenkel Set Theory
(ZFC), the most popular foundation for paper-and-pencil mathematics.

We conclude this chapter with a brief discussion of some of the
most significant differences between these two worlds.
::::

::::terse
Lean's logical core is a "metalanguage for mathematics" in
the same sense as familiar foundations for paper-and-pencil math, like
Zermelo–Fraenkel Set Theory (ZFC).

Mostly, the differences are not too important,
but a few points are useful to understand.
::::

## Propositional Extensionality

Lean's logic is quite minimalistic. This means that one occasionally
encounters cases where translating standard mathematical reasoning
into Lean is cumbersome — or even impossible — unless we enrich
its core logic with additional axioms.

::::full
For example, the equality assertions that we have seen so far have
mostly involved inductive types ({name}`Nat`, {name}`Bool`, etc.).
But since the equality operator is polymorphic, we can use it at _any_ type —
in particular, we can write propositions claiming that two _propositions_
are equal to each other:
::::

::::terse
A first instance has to do with equality of propositions.
::::

```lean
#check (∀ a b : Prop, (a ∧ b) = (b ∧ a) : Prop)
```

This is an equality between two conjunctions, which itself is also
a proposition. It states that commuted conjunctions are equal propositions.
However, we cannot prove this equality by reflexivity, as the two sides
don't compute to the same term, and we cannot proceed by cases on
`a` or `b`, as they are not inductive.

```lean +error (name := e1)
example (a b : Prop) : a ∧ b = b ∧ a := by rfl
```

```leanOutput e1
Tactic `rfl` failed: The left-hand side
  a
is not definitionally equal to the right-hand side
  b = b ∧ a

a b : Prop
⊢ a ∧ b = b ∧ a
```

```lean +error (name := e2)
example (a b : Prop) : a ∧ b = b ∧ a := by cases a
```

```leanOutput e2
Tactic `cases` failed: major premise type is not an inductive type
  Prop

Explanation: the `cases` tactic is for constructor-based reasoning as well as for applying custom cases principles with a 'using' clause or a registered '@[cases_eliminator]' theorem. The above type neither is an inductive type nor has a registered theorem.

Consider using the 'by_cases' tactic, which does true/false reasoning for propositions.

a b : Prop
⊢ a ∧ b = b ∧ a
```

However, we _can_ prove that `a ∧ b` implies `b ∧ a`, and vice versa — this is
the commutativity of conjunction that we have seen earlier.

```lean (name := and_comm)
#check and_comm
```

```leanOutput and_comm
and_comm {a b : Prop} : a ∧ b ↔ b ∧ a
```

Since it would be convenient to be able to rewrite propositions from
one side of `↔` to the other, Lean provides an axiom to turn `↔` into `=`,
which is called _propositional extensionality_ ({lean}`propext`).

```lean (name := propext)
#print propext
```

```leanOutput propext
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
```

::::full
(Informally, an {deftech}_extensional_ property is one that pertains to observable
behavior. Thus, propositional extensionality means that a proposition's
identity is completely determined by what we can observe from it — i.e.,
whether the proposition holds.) We can state this more explicitly:

```lean
theorem prop_true (a : Prop) (h : a) : a = True := by
  apply propext
  constructor
  · intro _
    exact ⟨⟩
  · intro _
    exact h
```
::::

Lean provides an {tactic}`ext` tactic that applies {lean}`propext` for us.
We can use it to show that commuted conjoined propositions are equal.

```lean
theorem and_comm_eq (a b : Prop) : (a ∧ b) = (b ∧ a) := by
  ext; apply and_comm
```

Similarly, we can use it to show that reassociated conjoined propositions
are equal as well.

```lean (name := and_assoc)
#check and_assoc
```

```leanOutput and_assoc
and_assoc {a b c : Prop} : (a ∧ b) ∧ c ↔ a ∧ b ∧ c
```

```lean
theorem and_assoc_eq (a b c : Prop) : ((a ∧ b) ∧ c) = (a ∧ (b ∧ c)) := by
  ext; apply and_assoc
```

Here is an example of where using `=` instead of `↔` is more convenient:
we show that it's possible to "flip" three conjoined propositions.

One way to prove this is to construct the `↔`, destruct the `↔`s provided by
{lean}`and_comm` and {lean}`and_assoc`, and apply the resulting implications a few times.
But this is a lot of hassle when the proof is conceptually simple:
we flip `b` and `c`, then we flip that conjunction with `a`, and we
finish by associativity. By using {lean}`and_comm_eq`, this is easily done
by rewriting equal propositions.

```lean
theorem and_comm_flip (a b c : Prop) : (a ∧ b ∧ c) ↔ (c ∧ b ∧ a) := by
  rw [and_comm_eq b c, and_comm_eq a, and_assoc_eq]
```

The pattern of deriving an equality of propositions out of `↔`
then rewriting by that equality is so common that Lean will implicitly
cast `↔` to `=`, allowing you to rewrite on `↔` directly.
Notice that {tactic}`rw` is also able to close goals of the form `a ↔ a` by reflexivity.

```lean
theorem and_comm_flip' (a b c : Prop) : (a ∧ b ∧ c) ↔ (c ∧ b ∧ a) := by
  rw [@and_comm b c, @and_comm a, and_assoc]
```

Under the hood, this proof still uses {lean}`propext`, which you can check by
asking for all of the axioms used by a declaration.

```lean (name := a_and_comm_flip)
#print axioms and_comm_flip
```

```leanOutput a_and_comm_flip
'and_comm_flip' depends on axioms: [propext]
```

```lean (name := a_and_comm_flip')
#print axioms and_comm_flip'
```

```leanOutput a_and_comm_flip'
'and_comm_flip'' depends on axioms: [propext]
```

:::::exercise (rating := 1) (name := "mul_eq_0_ternary") (checkVisibility := false)
```lean
theorem mul_eq_0_ternary (n m p : Nat) :
    n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 := by
  solution!
    rw [mul_eq_0, mul_eq_0, or_associate]
```
:::gradeTheorem 1 mul_eq_0_ternary
:::
:::::

::::::full
:::::exercise (rating := 2) (name := "In_append_iff")
```lean
theorem In_append_iff (α : Type) (l l' : List α) (x : α) :
    List.In x (l ++ l') ↔ List.In x l ∨ List.In x l' := by
  solution!
    induction l with
    | nil =>
      constructor
      · intro h; right; exact h
      · intro h; obtain ⟨⟨⟩⟩ | h := h; exact h
    | cons y ys ih => rw [List.cons_append, List.In_cons, List.In_cons, ih, or_assoc]
```
:::gradeTheorem 2 In_append_iff
:::
:::::

::::::

::::::full
:::::exercise (rating := 1) (name := "beq_neq_false")
The following theorem is an alternative "negative" formulation of {lean}`beq_eq_true`
that is more convenient in certain situations.
(We'll see examples in later chapters.) Hint: {lean}`not_true_iff_false`.

```lean
theorem beq_neq_false (n m : Nat) : (n == m) = false ↔ n ≠ m := by
  solution!
    rw [← not_true_iff_false, Ne, beq_eq_true n m]
```
:::gradeTheorem 1 beq_neq_false
:::
:::::

::::::

## Functional Extensionality

We can also write propositions claiming that two _functions_ are equal
to each other. In some cases, we can also prove that two functions are
equal by reflexivity when both reduce to the same expression:

```lean
example : (fun x => x + 2) = (fun x => x + (Nat.pred 3)) := by rfl
```

In general, functions can be equal for more interesting reasons.
In common mathematical practice, two functions `f` and `g` are considered
equal if they produce the same output on every input:

```display
(∀ x, f x = g x) → f = g
```

This is known as _functional extensionality_,
which Lean provides as {lean}`funext`.

```lean
#check (fun f g => funext (f := f) (g := g) :
    ∀ {α β : Type} (f g : α → β), (∀ x, f x = g x) → f = g)
```

::::terse
Technically, `funext` is not an axiom, but its proof depends on one
(which we will not explain).
::::

::::full
Functional extensionality means that a function's identity is
completely determined by what we can observe from it — i.e., the results
we obtain after applying it.
(Its full type is actually slightly more general,
and is defined in terms of a more fundamental concept called _quotients_
rather than added directly as an axiom, but we will only discuss {lean}`funext`
here. This is also why, when printing axioms for theorems using {lean}`funext`,
it will instead display a {lean}`Quot.sound` axiom.)
::::

```lean (name := a_funext)
#print axioms funext
```

```leanOutput a_funext
'funext' depends on axioms: [Quot.sound]
```

Now we can prove some intuitively obvious equalities about functions
that would not be provable without {lean}`funext`.

```lean
theorem add_comm_fun :
  (fun (n m : Nat) => n + m) = (fun (n m : Nat) => m + n) := by
    apply funext; intro n
    apply funext; intro m
    exact Nat.add_comm n m
```

The {tactic}`ext` tactic will also apply {lean}`funext` as many times as possible,
introducing all variables in one go.
The singular version of the tactic is {tactic}`ext1`.

```lean
theorem add_comm_fun' :
  (fun (n m : Nat) => n + m) = (fun (n m : Nat) => m + n) := by
    ext n m; exact Nat.add_comm n m
```

::::quiz
Is the following statement provable by just {tactic}`rfl`, without {lean}`funext`?
```display
(fun xs => 1 :: xs) = (fun xs => [1] ++ xs)
```

1. Yes
2. No

:::quizSolution
```lean
example : (fun xs => 1 :: xs) = (fun xs => [1] ++ xs) := by rfl
```
:::
::::

## Other Extensionality Principles

::::full
Functions and propositions are not the only things that have extensionality principles.
Many structures like pairs also have them:
::::

::::terse
We can use {tactic}`ext` on pairs as follows:
::::

```lean
example {n : Nat} {p : Nat × Nat}
  (hx_fst : p.fst = n + 1) (hx_snd : p.snd = 0) : (n + 1, 0) = p := by
    ext -- uses the `Prod.ext` lemma
    · rw [hx_fst]
    · rw [hx_snd]
```

::::exercise (rating := 2) (name := "prod_ext_example") (checkVisibility := false)
Now, use {tactic}`ext1` to prove the following.
Remember that `dsimp only` simplifies projections like `(a, b).fst` to `a`.

```lean
theorem prod_ext_example {m : Nat} {p : Nat × Nat}
  (hp_snd : p.snd = 4) (hp_fst : p.fst = m) :
    ((p.fst + 1, 2), (p.fst, 4)) = ((m + 1, p.snd - 2), p) := by
  solution!
    ext1
    · dsimp only
      ext1
      · dsimp only
        rw [hp_fst]
      · dsimp only
        rw [hp_snd]
    · dsimp only
      ext1
      · rfl
      · dsimp only
        rw [hp_snd]
```

:::gradeTheorem 2 prod_ext_example
:::

::::

::::::full
:::::exercise (rating := 4) (name := "trRev_correct")
One problem with the definition of the list-reversing function {lean}`List.rev`
is that it performs a call to `++` on each step.
Running `++` takes time asymptotically linear in the size of the list,
which means that {lean}`List.rev` is asymptotically quadratic.

We can improve this with the following two-argument definition:

```lean
def revAppend {α} (xs ys : List α) : List α :=
  match xs with
  | [] => ys
  | x :: xs => revAppend xs (x :: ys)

theorem revAppend_nil {α : Type} {xs : List α} : revAppend [] xs = xs := by rfl

theorem revAppend_cons {α : Type} {x : α} {xs ys : List α} :
    revAppend (x :: xs) ys = revAppend xs (x :: ys) := by rfl

def trRev {α} (xs : List α) : List α := revAppend xs []
```

This version of {lean}`List.rev` is said to be _tail recursive_, because the recursive
call to the function is the last operation that needs to be performed
(i.e., we don't have to execute `++` after the recursive call);
a decent compiler will generate very efficient code in this case.

Prove that the two definitions are indeed equivalent.

```lean
-- SOLUTION
theorem revAppend_rev {α : Type} {xs ys : List α} :
    revAppend xs ys = xs.rev ++ ys := by
  induction xs generalizing ys with
  | nil => rw [revAppend_nil]; rfl
  | cons x xs ih =>
    rw [revAppend_cons, List.rev, ← List.append_cons]
    apply ih
-- END SOLUTION

theorem trRev_correct {α : Type} : @trRev α = @List.rev α := by
  solution!
    ext1 xs; rw [trRev, revAppend_rev, List.append_nil]
```

:::gradeTheorem 4 trRev_correct
:::
:::::

::::::

## Classical vs. Constructive Logic

::::full
We have seen that it is not possible to test whether or not a
proposition `a` holds while defining a Lean function. You may be
surprised to learn that a similar restriction applies in _proofs_!
In other words, the following intuitive reasoning principle is not
derivable in Lean with the tools we've seen so far:
::::

::::terse
The following reasoning principle is _not_ derivable with the tools we've seen so far:
::::

```lean
def ExcludedMiddle := ∀ a : Prop, a ∨ ¬ a
```

::::full
To understand operationally why this is the case, recall that,
to prove a statement of the form `a ∨ b`, we use the {tactic}`left` and {tactic}`right`
tactics, which effectively require knowing which side of the disjunction
holds. But the universally quantified `a` in {lean}`ExcludedMiddle` is an
_arbitrary_ proposition, which we know nothing about. We don't have enough
information to choose which of {tactic}`left` or {tactic}`right` to apply.

However, in the special case where we happen to know that `a` is reflected
in some boolean term `b`, knowing whether it holds or not is trivial:
we just have to check the value of `b`.

```lean
theorem restricted_excluded_middle (a : Prop) (b : Bool) (h : a ↔ b = true) :
    a ∨ ¬ a := by
  cases b with
  | false => right; rw [h]; intro; contradiction
  | true => left; rw [h]
```

In particular, the excluded middle is valid for equations `n = m` between
natural numbers `n` and `m`.

```lean
theorem excluded_middle_nat_eq (n m : Nat) : n = m ∨ n ≠ m := by
  apply restricted_excluded_middle (n = m) (n == m)
  symm; apply beq_eq_true
```

Sadly, this trick only works for decidable propositions.
::::

Logical systems in which excluded middle does not hold are referred to as
_constructive logics_. They are so called because to prove a proposition,
we must give a construction for it; for instance, `∃ x, p x`
is proven by providing a particular value of `x`.

Logical systems in which excluded middle does hold,
such as ZFC set theory, are referred to as _classical_.
Lean provides classical reasoning principles in the `Classical` library,
including excluded middle.

```lean (name := em)
#check Classical.em
```

```leanOutput em
Classical.em (p : Prop) : p ∨ ¬p
```

::::full
All classical reasoning principles in `Classical` are derived from
one axiom, the axiom of choice. This is the C in ZFC.

```lean (name := choice)
#print Classical.choice
```

```leanOutput choice
axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α
```

```lean (name := a_choice)
#print axioms Classical.em
```

```leanOutput a_choice
'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean also provides a {tactic}`by_cases` tactic that applies {lean}`Classical.em` on a
given proposition. Theorems proven using this tactic implicitly use
classical axioms.

```lean (name := my_em)
theorem em : ∀ a, a ∨ ¬ a := by
  intro a
  by_cases h : a
  /- h : a -/
  · left; exact h
  /- h : ¬ a -/
  · right; exact h

#print axioms em
```

```leanOutput my_em
'em' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The following example illustrates why assuming the excluded middle may
lead to nonconstructive proofs:

_Claim_: There exist irrational numbers `n` and `m` such that `n ^ m`
  (`n` to the power `m`) is rational.

_Proof_: It is not difficult to show that `sqrt 2` is irrational.
  So if `sqrt 2 ^ sqrt 2` is rational, it suffices to take `n = m = sqrt 2`
  and we are done. Otherwise, `sqrt 2 ^ sqrt 2` is irrational.
  In this case, we can take `n = sqrt 2 ^ sqrt 2` and `m = sqrt 2`,
  since `n ^ m = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2`. QED.

Do you see what happened here?  We used the excluded middle to
consider separately the cases where `sqrt 2 ^ sqrt 2` is rational and
where it is not, without knowing which one actually holds!
Because of this, we finish the proof knowing that such `n` and `m` exist,
but not being sure of their actual values.

As useful as constructive logic is, it does have its limitations:
there are many statements that can easily be proven in classical logic
but that have only much more complicated constructive proofs,
and there are some that are known to have no constructive proof at all!
Fortunately, like functional extensionality, the excluded middle is known
to be compatible with Lean's logic, allowing it to be added safely as an axiom.
However, the results that we cover in Logical Foundations can be developed
entirely within constructive logic.

It takes some practice to understand which proof techniques must be
avoided in constructive reasoning, but arguments by contradiction,
in particular, are infamous for leading to nonconstructive proofs.
Here's a typical example: suppose that we want to show that there exists
`x` with some property `p`, i.e., such that `p x`. We start by assuming
that our conclusion is false; that is, `¬ ∃ x, p x`. From this premise,
it is not hard to derive `∀ x, ¬ p x`. If we manage to show that this
results in a contradiction, we arrive at an existence proof without ever
exhibiting a value of `x` for which `p x` holds!

The technical flaw here, from a constructive standpoint, is that we
claimed to prove `∃ x, p x` using a proof of `¬ ¬ ∃ x, p x`.
Allowing ourselves to remove double negations from arbitrary statements
is equivalent to assuming the excluded middle law, as shown in one of the
exercises below.
::::

::::::full
Once again, Lean's `Classical` library provides double negation elimination,
which relies on the {lean}`Classical.choice` axiom.

```lean (name := not_not)
#check Classical.not_not

#print axioms Classical.not_not
```

```leanOutput not_not
Classical.not_not {a : Prop} : ¬¬a ↔ a
```

```leanOutput not_not
'Classical.not_not' depends on axioms: [propext, Classical.choice, Quot.sound]
```

:::::exercise (rating := 3) (name := "excluded_middle_irrefutable")
The following theorem implies that it is always safe to assume
a decidability axiom (i.e., an instance of excluded middle) for any
_particular_ proposition `a`. Why? Because the negation of such an axiom
leads to a contradiction. If `¬ (a ∨ ¬ a)` were provable, then by
{lean}`de_morgan_not_or` as proven above, `¬ a ∧ ¬ ¬ a` would be provable,
which would be a contradiction. So, it is safe to add `a ∨ ¬ a` as an axiom
for any particular `a`.

```lean
theorem excluded_middle_irrefutable (a : Prop) : ¬ ¬ (a ∨ ¬ a) := by
  solution!
    intro h
    obtain ⟨hna, hnna⟩ := de_morgan_not_or h
    exact hnna hna
```
:::gradeTheorem 3 excluded_middle_irrefutable
:::
:::::

:::::exercise (rating := 3) (name := "not_exists_dist") (level := Advanced)
It is a theorem of classical logic that the following two assertions
are equivalent:

```display
¬ ∃ x, ¬ p x
∀ x, p x
```

The {lean}`dist_not_exists` theorem proves one side of this equivalence.
Interestingly, the other direction cannot be proven in constructive logic,
but we can prove it here using {tactic}`by_cases`.

```lean
theorem not_exists_dist (α : Type) (p : α → Prop) :
    (¬ ∃ x : α, ¬ p x) → (∀ x : α, p x) := by
  solution!
    intro h x
    by_cases hx : (p x)
    · exact hx
    · exfalso; apply h; exists x
```
:::gradeTheorem 3 not_exists_dist
:::
:::::

:::::exercise (rating := 5) (name := "classical_axioms") (optional := true)
For those who like a challenge, here is an exercise adapted from the Coq'Art
book by Bertot and Castéran (p. 123). Each of the following five statements,
together with {lean}`ExcludedMiddle`, can be considered as characterizing
classical logic. We can't prove any one of them in Lean without `Classical`,
but adding any _one_ of them as an axiom allows us to work classically.

To see this, prove that all six propositions (these five plus
{lean}`ExcludedMiddle`) are equivalent.

Hint: Rather than considering all pairs of statements,
prove a single circular chain of implications that connects them all.
You should not use {tactic}`by_cases`, as this implicitly introduces
a dependency on {lean}`ExcludedMiddle`.

:::dev "Jonathan Chan"
If the hint suggests proving the implications in a loop,
why do the solutions not do this?
:::

```lean
def Peirce := ∀ a b : Prop, ((a → b) → a) → a

def NotNot := ∀ a : Prop, ¬ ¬ a → a

def DeMorganNotAndNot := ∀ a b : Prop, ¬ (¬ a ∧ ¬ b) → a ∨ b

def ImpOr := ∀ a b : Prop, (a → b) → (¬ a ∨ b)

def ConsequentiaMirabilis := ∀ a : Prop, (¬ a → a) → a

theorem ImpOr_em : ImpOr → ExcludedMiddle := by
  solution!
    intro h a
    obtain hna | ha := h a a (fun ha => ha)
    · right; exact hna
    · left; exact ha

theorem em_ImpOr : ExcludedMiddle → ImpOr := by
  solution!
    intro h a b hab
    obtain ha | hna := h a
    · right; exact hab ha
    · left; exact hna

theorem em_demorgan : ExcludedMiddle → DeMorganNotAndNot := by
  solution!
    intro h a b hnn
    obtain ha | hna := h a
    · left; exact ha
    · obtain hb | hnb := h b
      · right; exact hb
      · exfalso; exact hnn ⟨hna, hnb⟩

theorem demorgan_em : DeMorganNotAndNot → ExcludedMiddle := by
  solution!
    intro h a
    apply h a (¬ a)
    intro ⟨hna, hnna⟩
    exact hnna hna

theorem em_not_not : ExcludedMiddle → NotNot := by
  solution!
    intro h a hnna
    obtain ha | hna := h a
    · exact ha
    · exfalso; exact hnna hna

theorem not_not_em' : NotNot → ExcludedMiddle := by
  solution!
    intro h a; exact h _ (excluded_middle_irrefutable a)

theorem em_cm : ExcludedMiddle → ConsequentiaMirabilis := by
  solution!
    intro h a hnaa
    obtain ha | hna := h a
    · exact ha
    · exact (hnaa hna)

theorem cm_em : ConsequentiaMirabilis → ExcludedMiddle := by
  solution!
    intro hc a; apply hc
    intro h; right
    intro ha; apply h
    left; exact ha

theorem cm_not_not : ConsequentiaMirabilis → NotNot := by
  solution!
    intro h a hnna; apply h
    intro hna; exfalso; exact hnna hna

theorem not_not_cm : NotNot → ConsequentiaMirabilis := by
  solution!
    intro h a hnaa; apply h
    intro hna; exact hna (hnaa hna)

theorem cm_peirce : ConsequentiaMirabilis → Peirce := by
  solution!
    intro h a b haba; apply h
    intro hna; apply haba
    intro ha; contradiction

theorem peirce_cm : Peirce → ConsequentiaMirabilis := by
  solution!
    intro h a; exact h a False
```

:::::

::::::
