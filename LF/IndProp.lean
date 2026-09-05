import SFLMeta

import LF.Logic
import LF.CustomTactics

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "IndProp: Inductively Defined Propositions" =>
%%%
tag := "IndProp"
htmlSplit := .never
file := some "IndProp"
%%%

:::instructors
```
In one 80-minute lecture, I (BCP) was able to get
_to_, but not _through_, the proof of in_re_match in the regexp
case study.  I covered the rest in an hour, going pretty slowly and
working lots of examples in real time.  That left 20 minutes to
show them just the first half of the ProofObjects chapter.

Making time for at least a bit of discussion of ProofObjects is
pretty important, even if you don't go into it in detail.  Entirely
skipping this material leads to needless confusion and beating
around the bush in later discussions.
```
:::

:::dev BeforeNextRelease
This chapter needs more (and better!) quizzes
:::

```importBlock
import LF.Logic
import LF.CustomTactics
```

:::ignore
```lean -show
variable
  (n n' m m' k : Nat)
  (α : Type)
  (x y : α)
  (l l₁ l₂ l₃ : List α)
```
:::

# Inductively Defined Propositions

In the {ref "Logic"}[Logic] chapter, we looked at several ways of writing
propositions, including conjunction, disjunction, and existential
quantification.

In this chapter, we bring yet another new tool into the mix:
_inductively defined propositions_.

To begin, some examples...

## Example: The Collatz Conjecture

The _Collatz Conjecture_ is a famous open problem in number theory.

Its statement is quite simple.  First, we define a function `collatzStep`
on numbers as follows:

```lean
def div2 (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | 1      => 0
  | n' + 2 => div2 n' + 1

def collatzStep (n : Nat) : Nat :=
  bif n.even then div2 n
  else (3 * n) + 1
```

:::slidebreak
:::

Next, we look at what happens when we repeatedly apply {lean}`collatzStep` to
some given starting number.  For example, {lean}`collatzStep 12` is {lean}`6`, and
{lean}`collatzStep 6` is {lean}`3`, so by repeatedly applying {lean}`collatzStep` we get the
sequence `12, 6, 3, 10, 5, 16, 8, 4, 2, 1`.

Similarly, if we start with {lean}`19`, we get the longer sequence `19,
58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8,
4, 2, 1`.

Both of these sequences eventually reach {lean}`1`.  The question posed
by Collatz was: Is the sequence starting from _any_ positive
natural number guaranteed to reach {lean}`1` eventually?

To formalize this question in Lean, we might try to define a
recursive _function_ that calculates the total number of steps
that it takes for such a sequence to reach `1`.  You can write
this definition in a standard programming language, but it is
rejected by Lean's termination checker, since the argument to
the recursive call, {lean}`collatzStep n`, is not "obviously smaller" than {lean}`n`.

```lean -keep +error (name := reaches1In)
def reaches1In (n : Nat) : Nat :=
  bif n == 1 then 0
  else 1 + reaches1In (collatzStep n)
```

```leanOutput reaches1In
fail to show termination for
  reaches1In
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    reaches1In (collatzStep n)


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
⊢ collatzStep n < n
```

Indeed, this isn't just a pointless limitation: functions in Lean
are required to be total, to ensure logical consistency.

Moreover, we can't fix it by devising a more clever termination
checker: deciding whether this particular function is total
would be equivalent to settling the Collatz conjecture!

:::slidebreak
:::

Another idea could be to express the concept "eventually reaches
{lean}`1` in the Collatz sequence" as a _recursively defined property_
of numbers `CollatzHoldsFor : Nat → Prop`. This is also rejected
by the termination checker. In principle, we could convince Lean
that {lean}`div2 n` is smaller than {lean}`n` by supplying an
appropriate proof. However, we still can't convince it that
{lean}`(3 * n) + 1` is smaller than {lean}`n`!

```lean -keep +error (name := CollatzHoldsFor)
def CollatzHoldsFor (n : Nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => bif n.even then CollatzHoldsFor (div2 n)
                   else CollatzHoldsFor ((3 * n) + 1)
```

```leanOutput CollatzHoldsFor
fail to show termination for
  CollatzHoldsFor
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    CollatzHoldsFor (div2 n)


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n x✝ : Nat
⊢ div2 n < x✝
```

:::slidebreak
:::

Fortunately, there is another way to do it: We can express the
concept "reaches {lean}`1` eventually in the Collatz sequence" as an
_inductively defined property_ of numbers. Intuitively, this
property is defined by a set of rules:

```display
              ─────────────────── (one)
               CollatzHoldsFor 1

n.even = true     CollatzHoldsFor (div2 n)
─────────────────────────────────────────── (even)
               CollatzHoldsFor n

n.even = false    CollatzHoldsFor ((3 * n) + 1)
─────────────────────────────────────────────── (odd)
               CollatzHoldsFor n
```

So there are three ways to prove that a number {lean}`n` eventually
reaches {lean}`1` in the Collatz sequence:
- {lean}`n` is {lean}`1`;
- {lean}`n` is even and {lean}`div2 n` eventually reaches {lean}`1`;
- {lean}`n` is odd and {lean}`(3 * n) + 1` eventually reaches {lean}`1`.

:::slidebreak
:::

We can prove that a number reaches {lean}`1` by constructing a (finite)
derivation using these rules. For instance, here is the
derivation proving that {lean}`12` reaches {lean}`1`
(where we leave out the evenness/oddness premises):

```display
─────────────────────── (one)
  CollatzHoldsFor 1
─────────────────────── (even)
  CollatzHoldsFor 2
─────────────────────── (even)
  CollatzHoldsFor 4
─────────────────────── (even)
  CollatzHoldsFor 8
─────────────────────── (even)
  CollatzHoldsFor 16
─────────────────────── (odd)
  CollatzHoldsFor 5
─────────────────────── (even)
  CollatzHoldsFor 10
─────────────────────── (odd)
  CollatzHoldsFor 3
─────────────────────── (even)
  CollatzHoldsFor 6
─────────────────────── (even)
  CollatzHoldsFor 12
```

:::slidebreak
:::

Formally in Lean, the `CollatzHoldsFor` property is
_inductively defined_:

```lean
inductive CollatzHoldsFor : Nat → Prop where
  | one  : CollatzHoldsFor 1
  | even {n : Nat} (h₁ : n.even = true)
    (h₂ : CollatzHoldsFor (div2 n)) : CollatzHoldsFor n
  | odd  {n : Nat} (h₁ : n.even = false)
    (h₂ : CollatzHoldsFor ((3 * n) + 1)) : CollatzHoldsFor n
```

::::full
What we've done here is to use Lean's `inductive`
definition mechanism to characterize the property "Collatz holds
for..." by stating three different ways in which it can hold:
(1) Collatz holds for {lean}`1`, (2) if Collatz holds for
{lean}`div2 n` and {lean}`n` is even then Collatz holds for
{lean}`n`, and (3) if Collatz holds for {lean}`(3 * n) + 1` and
{lean}`n` is odd then Collatz holds for {lean}`n`.
This Lean definition directly corresponds to the three rules we
wrote informally above.
::::

:::slidebreak
:::

For particular numbers, we can now prove that the Collatz
sequence reaches {lean}`1` (we'll look more closely at how it works a
bit later in the chapter).  Each step applies a rule and
discharges the boolean evenness premise by {tactic}`rfl`; the recursive
premise is then reduced by the kernel from
{lean}`CollatzHoldsFor (div2 12)` to {lean}`CollatzHoldsFor 6`, etc.

```lean
example : CollatzHoldsFor 12 := by
  apply CollatzHoldsFor.even;  rfl
  apply CollatzHoldsFor.even;  rfl
  apply CollatzHoldsFor.odd;   rfl
  apply CollatzHoldsFor.even;  rfl
  apply CollatzHoldsFor.odd;   rfl
  apply CollatzHoldsFor.even;  rfl
  apply CollatzHoldsFor.even;  rfl
  apply CollatzHoldsFor.even;  rfl
  apply CollatzHoldsFor.even;  rfl
  exact CollatzHoldsFor.one
```

:::slidebreak
:::

The Collatz conjecture then states that the sequence beginning
from _any_ positive number reaches {lean}`1`:

```lean
def Collatz := ∀ n : Nat, n ≠ 0 → CollatzHoldsFor n
```

If you succeed in proving this conjecture, you've got a bright
future as a number theorist! But don't spend too long on it ─
it's been open since 1937.

:::dev "Chris Henson (@chenson2018)"
We may want to add an exercise later proving false if one assumes
Collatz' conjecture without the `n ≠ 0` assumption. We had that
mistake in the script for years and no one noticed, wow!

```lean
theorem Collatz0' {n : Nat} (h₀ : n = 0) : ¬ CollatzHoldsFor n := by
  intro h
  induction h with
  | one => contradiction
  | even _ _ ih => apply ih; rw [h₀]; dsimp [div2]
  | odd h _ _ => rw [h₀] at h; dsimp [Nat.even] at h; contradiction

theorem Collatz0 : ¬ (∀ n, CollatzHoldsFor n) := by
  intro h; apply Collatz0'; rfl; apply h
```
:::

## Example: Binary Relation for Comparing Numbers

A binary _relation_ on a set {lean}`α` has Lean type {lean}`α → α → Prop`.
This is a family of propositions parameterized by two elements
of {lean}`α` ─ i.e., a proposition about pairs of elements of {lean}`α`.

For example, one familiar binary relation on {name}`Nat` is
`Le : Nat → Nat → Prop`, the less-than-or-equal-to relation,
which can be inductively defined by the following two rules:

```display
  ─────── (le_refl)
  Le n n

  Le n m
──────────── (le_step)
Le n (m + 1)
```

::::full
These rules say that there are two ways to show that a
number is less than or equal to another: either observe that
they are the same number, or, if the second has the form
{lean}`m + 1`, give evidence that the first is less than or
equal to {lean}`m`.
::::

```lean
namespace LePlayground

inductive Le : Nat → Nat → Prop where
  | refl {n : Nat}                : Le n n
  | step {n m : Nat} (h : Le n m) : Le n (m + 1)

scoped infix:50 (priority := high) " ≤ " => Le
```

::::full
This definition is a bit simpler and more elegant than the
Boolean function {name}`Nat.ble` we defined in {ref "Basics"}[Basics].
As usual, {name}`Le` and {name}`Nat.ble` are equivalent, and there is
an exercise about that later.
::::

```lean
example : 3 ≤ 5 := by
  apply Le.step; apply Le.step; exact Le.refl

end LePlayground
```

## Example: Transitive Closure

Another example: The _transitive closure_ of a relation `r` is the
smallest relation that contains `r` and that is transitive. This can
be defined by the following two rules:

```display
              r x y
         ─────────────── (t_step)
         TransGen r x y

TransGen r x y    TransGen r y z
──────────────────────────────────── (t_trans)
         TransGen r x z
```

In Lean this looks as follows:

```lean
inductive TransGen {α : Type} (r : α → α → Prop) : α → α → Prop where
  | step {x y : α} (h : r x y) : TransGen r x y
  | trans {x y z : α}
    (h₁ : TransGen r x y)
    (h₂ : TransGen r y z) :
    TransGen r x z
```

"Gen" is short for generated by — `TransGen r` means
the smallest transitive relation generated by `r`.

:::slidebreak
:::

For example, suppose we define a "parent of" relation on a group
of people...

```lean
inductive Person : Type where
  | sage
  | cleo
  | ridley
  | moss

inductive ParentOf : Person → Person → Prop where
  | sage_cleo : ParentOf .sage .cleo
  | sage_ridley : ParentOf .sage .ridley
  | cleo_moss : ParentOf .cleo .moss
```

:::ignore
```lean -show
open Person
```
:::

::::full
In this example, {name}`sage` is a parent of both {name}`cleo` and
{name}`ridley`; and {name}`cleo` is a parent of {name}`moss`.
::::

The {name}`ParentOf` relation is not transitive, but we can define
an "ancestor of" relation as its transitive closure:

```lean
def AncestorOf : Person → Person → Prop := TransGen ParentOf
```

Here is a derivation showing that {name}`Person.sage` is an ancestor of {name}`moss`:

```display
 ——————————————————— (sage_cleo) ——————————————————— (cleo_moss)
 ParentOf .sage .cleo            ParentOf .cleo .moss
————————————————————— (step)    ————————————————————— (step)
AncestorOf .sage .cleo          AncestorOf .cleo .moss
———————————————————————————————————————————————————— (trans)
                AncestorOf .sage .moss
```

```lean
example : AncestorOf .sage .moss := by
  apply TransGen.trans
  · apply TransGen.step; apply ParentOf.sage_cleo
  · apply TransGen.step; apply ParentOf.cleo_moss
```

:::dev
HIDE: CH: A simple exercise could be nice here?
:::

::::full
Computing the transitive closure can be undecidable even for
a relation `r` that is decidable (e.g., the `CollatzStepMulti` relation below), so in
general we can't expect to define transitive closure as a boolean
function. Fortunately, Lean allows us to define transitive closure
as an inductive relation.

The transitive closure of a binary relation cannot, in general, be
expressed in first-order logic. The logic of Lean is, however, much
more powerful, and can easily define such inductive relations.
::::

## Example: Reflexive and Transitive Closure

As another example, the _reflexive and transitive closure_ of a
relation `r` is the smallest relation that contains `r` and that is
reflexive and transitive. This can be defined by the following three
rules (where we added a reflexivity rule to {name}`TransGen`):

```display
                   r x y
         ——————————————————————— (step)
           ReflTransGen r x y

         ——————————————————————— (refl)
           ReflTransGen r x x

   ReflTransGen r x y    ReflTransGen r y z
—————————————————————————————————————————————— (trans)
           ReflTransGen r x z
```

```lean
inductive ReflTransGen {α : Type} (r : α → α → Prop) : α → α → Prop where
  | step {x y : α} (h : r x y) : ReflTransGen r x y
  | refl {x : α} : ReflTransGen r x x
  | trans {x y z : α}
    (h₁ : ReflTransGen r x y)
    (h₂ : ReflTransGen r y z) :
    ReflTransGen r x z
```

:::slidebreak
:::

For instance, this enables an equivalent definition of the Collatz
conjecture.  First we define a binary relation corresponding to
the "Collatz step function" {name}`collatzStep`:

```lean
def CollatzStep (n m : Nat) : Prop := collatzStep n = m
```

This Collatz step relation can be used in conjunction with the
reflexive and transitive closure operation to define a _Collatz
multi-step_ relation, expressing that a number {lean}`n`
reaches another number {lean}`m` in zero or more Collatz steps:

```lean
def CollatzStepMulti (n m : Nat) : Prop := ReflTransGen CollatzStep n m
def Collatz' : Prop := ∀ (n : Nat), n ≠ 0 → CollatzStepMulti n 1
```

::::full
This {name}`CollatzStepMulti` relation defined in terms of
{name}`ReflTransGen` allows for more interesting derivations than the
linear ones of the directly-defined {name}`CollatzHoldsFor` relation:

```display
collatzStep 16 = 8          collatzStep 8 = 4          collatzStep 4 = 2          collatzStep 2 = 1
────────────────── (step)   ───────────────── (step)   ───────────────── (step)   ───────────────── (step)
CollatzStepMulti 16 8       CollatzStepMulti 8 4       CollatzStepMulti 4 2       CollatzStepMulti 2 1
──────────────────────────────────────────── (trans)   ─────────────────────────────────────────── (trans)
              CollatzStepMulti 16 4                                  CollatzStepMulti 4 1
              ───────────────────────────────────────────────────────────────────────── (trans)
                                     CollatzStepMulti 16 1
```
::::

::::::full
:::::exercise (rating := 1) (name := "EqvGen") (optional := true) (manual := true)
How would you modify the {name}`ReflTransGen` definition above to define the reflexive,
symmetric, and transitive closure—in other words, the equivalence closure?

```lean
-- SOLUTION
inductive EqvGen {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl {x : α} : EqvGen r x x
  | step {x y : α} (h : r x y) : EqvGen r x y
  | sym {x y : α}
    (h : EqvGen r y x) :
    EqvGen r x y
  | trans {x y z : α}
    (h₁ : EqvGen r x y)
    (h₂ : EqvGen r y z) :
    EqvGen r x z
-- END SOLUTION
```
:::::

::::::

## Example: Permutations

The familiar mathematical concept of _permutation_ also has an
elegant formulation as an inductive relation.  For simplicity,
let's focus on permutations of lists with exactly three
elements.

We can define such permutations by the following rules:

```display
   ───────────────────────── (swap12)
   Perm3 [a, b, c] [b, a, c]

   ───────────────────────── (swap23)
   Perm3 [a, b, c] [a, c, b]

Perm3 l₁ l₂       Perm3 l₂ l₃
───────────────────────────── (trans)
         Perm3 l₁ l₃
```

For instance we can derive `Perm3 [1, 2, 3] [3, 2, 1]` as follows:

```display
───────────────────────── (swap12)  ─────────────────────── (swap23)
Perm3 [1, 2, 3] [2, 1, 3]            Perm3 [2, 1, 3] [2, 3, 1]
─────────────────────────────────────────────────────────────────(trans)    ───────────────────── (swap12)
Perm3 [1, 2, 3] [2, 3, 1]                                                    Perm3 [2, 3, 1] [3, 2, 1]
───────────────────────────────────────────────────────────────────────────────────────────────────────── (trans)
Perm3 [1, 2, 3] [3, 2, 1]
```

::::full
This definition says:
- If {lean}`l₂` can be obtained from {lean}`l₁` by swapping the first and
  second elements, then {lean}`l₂` is a permutation of {lean}`l₁`.
- If {lean}`l₂` can be obtained from {lean}`l₁` by swapping the second and
  third elements, then {lean}`l₂` is a permutation of {lean}`l₁`.
- If {lean}`l₂` is a permutation of {lean}`l₁` and {lean}`l₃` is a permutation
  of{lean}`l₂`, then {lean}`l₃` is a permutation of {lean}`l₁`.
::::

:::slidebreak
:::

In Lean, we can define `Perm3` as follows:

```lean
inductive Perm3 {α : Type} : List α → List α → Prop where
  | swap12 {x y z : α} : Perm3 [x, y, z] [y, x, z]
  | swap23 {x y z : α} : Perm3 [x, y, z] [x, z, y]
  | trans {l₁ l₂ l₃ : List α}
    (h₁₂ : Perm3 l₁ l₂)
    (h₂₃ : Perm3 l₂ l₃) :
    Perm3 l₁ l₃
```

::::::full
:::::exercise (rating := 1) (name := "perm") (optional := true) (manual := true)
According to this definition, is `[1, 2, 3]` a permutation of
itself?

:::solution
Yes! Just apply {lean}`Perm3.swap12` twice (or {name}`Perm3.swap23` twice).
:::
:::::

::::::

## Example: Evenness (yet again)

We've already seen two ways of stating a proposition that a number
{lean}`n` is even: We can say

  (1) {lean}`Nat.even n = true` (using the recursive boolean function {name}`Nat.even`), or

  (2) {lean}`∃ k, n = Nat.double k` (using an existential quantifier).

:::slidebreak
:::

A third possibility, which we'll use as a simple running example
in this chapter, is to say that a number is even if we can
_establish_ its evenness from the following two rules:

```display
  ────────── (zero)
    Even 0

    Even n
—————————————— (succ_succ)
  Even (n + 2)
```

::::full
Intuitively these rules say that:
- The number {lean}`0` is even.
- If {lean}`n` is even, then {lean}`n + 2` is even.

(Defining evenness in this way may seem a bit confusing,
since we have already seen two perfectly good ways of doing
it. It makes a convenient running example because it is
simple and compact, but we will soon return to the more compelling
examples above.)
::::

To illustrate how this new definition of evenness works, let's
imagine using it to show that {lean}`4` is even:

```display
                 ──────── (zero)
                  Even 0
          ─────────────────────── (succ_succ)
          Even (.succ (.succ 0))
────────────────────────────────────────────── (succ_succ)
Even (.succ (.succ (.succ (.succ 0))))
```

::::full
In words, to show that {lean}`4` is even, by rule `succ_succ`, it
suffices to show that {lean}`2` is even. This, in turn, is again
guaranteed by rule `succ_succ`, as long as we can show that {lean}`0` is
even. But this last fact follows directly from the `zero` rule.
::::

:::slidebreak
:::

We can translate the informal definition of evenness from above
into a formal `inductive` declaration, where each "way that a
number can be even" corresponds to a separate constructor:

```lean
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ {n : Nat} (h : Even n) : Even (n + 2)
```

::::terse
There are both similarities and a few differences between
inductive _properties_ like {name}`Even` and the inductive _types_ like
{name}`Nat` or {name}`List` that we have been using throughout the course:

```lean -keep +error
inductive List (α : Type) : Type where
  | nil                       : List α
  | cons (x : α) (l : List α) : List α
```

The most important difference is that the constructors of {name}`Even`,
{name}`Even.zero` and {name}`Even.succ_succ`, yield different types
({lean}`Even 0` and {lean}`Even (n + 2)`), whereas the {name}`List`
constructors both build {lean}`List α` values.
::::

::::full
Such definitions are interestingly different from previous uses of
`inductive` for defining inductive datatypes like {name}`Nat` or {name}`List`.
For one thing, we are defining not a {lean}`Type` (like {name}`Nat`) or a
function yielding a {lean}`Type` (like {name}`List`), but rather a function
from {name}`Nat` to {lean}`Prop` ─ that is, a property of numbers. But what
is really new is that, because the {name}`Nat` argument of {name}`Even` appears
to the _right_ of the colon on the first line, it is allowed to
take _different_ values in the types of different constructors:
{lean}`0` in the type of {lean}`Even.zero` and {lean}`(n + 2)`
in the type of {lean}`Even.succ_succ`.
Accordingly, the type of each constructor must be specified
explicitly (after a colon), and each constructor's type must have
the form {lean}`Even n` for some natural number {lean}`n`.

In contrast, recall the definition of {name}`List`:

```lean -keep +error
inductive List (α : Type) : Type where
  | nil
  | cons (x : α) (l : List α)
```

or (equivalently but more explicitly):

```lean -keep +error
inductive List (α : Type) : Type where
  | nil                       : List α
  | cons (x : α) (l : List α) : List α
```

This definition introduces the {lean}`α` parameter _globally_, to the
_left_ of the colon, forcing the result of {lean}`List.nil` and
{lean}`List.cons` to be the same type (i.e., {lean}`List α`).
But if we had tried to bring {name}`Nat` to the left of the colon in
defining {name}`Even`, we would have seen an error:

```lean -keep +error (name := WrongEven)
inductive WrongEven (n : Nat) : Prop where
  | zero : WrongEven 0
  | succ_succ (h : WrongEven n) : WrongEven (.succ (.succ n))
```

```leanOutput WrongEven
Mismatched inductive type parameter in
  WrongEven 0
The provided argument
  0
is not definitionally equal to the expected parameter
  n

Note: The value of parameter `n` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```

In an `inductive` definition, an argument to the type constructor
on the left of the colon is called a "parameter", whereas an
argument on the right is called an "index" or "annotation."

For example, in `inductive List (α : Type) ...`, the `α` is a
parameter, while in `inductive Even : Nat → Prop ...`, the
unnamed {name}`Nat` argument is an index.
::::

:::slidebreak
:::

We can think of the inductive definition of {name}`Even` as defining a
Lean property `Even : Nat → Prop`, together with two "evidence
constructors":

```lean (name := Evens)
#check (Even)
#check Even.zero
#check Even.succ_succ
```

```leanOutput Evens
Even : Nat → Prop
```

```leanOutput Evens
Even.zero : Even 0
```

```leanOutput Evens
Even.succ_succ {n : Nat} (h : Even n) : Even (n + 2)
```

:::slidebreak
:::

These evidence constructors can be thought of as "primitive evidence
of evenness", and they can be used later on just like proven theorems.
In particular, we can use Lean's {tactic}`apply` and {tactic}`exact`
tactics with the constructor names to obtain evidence for {name}`Even` of
particular numbers...

```lean
namespace Even

example : Even 4 := by
  apply succ_succ; apply succ_succ; exact zero
```

... or we can use function application syntax to combine several
constructors:

```lean
example : Even 4 := by
  exact succ_succ (succ_succ zero)
```

... or we can also use the {tactic}`constructor` tactic we saw
earlier to select the appropriate inductive constructor:

```lean
example : Even 4 := by
  constructor; constructor; constructor
```

In this way, we can also prove theorems that have hypotheses
involving {name}`Even`.

```lean
theorem plus4 (n : Nat) (h : Even n) : Even (4 + n) := by
  rw [Nat.add_comm]
  exact (succ_succ (succ_succ h))
```

::::::full
:::::exercise (rating := 1) (name := "double")
```lean
theorem double (n : Nat) : Even n.double := by
  solution!
    induction n with
    | zero =>
      rw [Nat.double_zero]; exact zero
    | succ n ih =>
      rw [Nat.double_succ]; exact succ_succ ih
```

:::gradeTheorem 1 double
:::
:::::

::::::

```lean
end Even
```

## Constructing Evidence for Permutations

Similarly we can apply the evidence constructors to obtain
evidence of {lean}`Perm3 [1, 2, 3] [3, 2, 1]`:

```lean
namespace Perm3

theorem rev : Perm3 [1, 2, 3] [3, 2, 1] := by
  apply trans (l₂:= [2, 3, 1])
  · apply trans (l₂ := [2, 1, 3])
    · apply swap12
    · apply swap23
  · apply swap12
```

:::slidebreak
:::

And again we can equivalently use function application syntax to
combine several constructors. (Note that the Lean type checker can
infer not only types, but also {name}`Nat`s and {name}`List`s,
when they are clear from the context.)

```lean
theorem rev' : Perm3 [1, 2, 3] [3, 2, 1] := by
  exact (trans (trans swap12 swap23) swap12)
```

So the informal derivation trees we drew above are not too far
from what's happening formally. Formally we're using the evidence
constructors to build _evidence trees_, similar to the finite trees we
built using the constructors of data types such as {name}`Nat`,
{name}`List`, binary trees, etc.

::::::full
:::::exercise (rating := 1) (name := "Perm3")
```lean
theorem ex1 : Perm3 [1, 2, 3] [2, 3, 1] := by
  solution!
    apply trans (l₂ := [2, 1, 3])
    · apply swap12
    · apply swap23

theorem refl (α : Type) (a b c : α) : Perm3 [a, b, c] [a, b, c] := by
  solution!
    apply trans (l₂ := [b, a, c])
    · apply swap12
    · apply swap12
```

:::gradeTheorem "0.5" Perm3.ex1 Perm3.refl
:::
:::::

::::::

```lean
end Perm3
```

# Using Evidence in Proofs

Besides _constructing_ evidence that numbers are even, we can also
_destruct_ such evidence, reasoning about how it could have been
built.

Defining {name}`Even` with an `inductive` declaration tells Lean not
only that the constructors {name}`Even.zero` and {name}`Even.succ_succ`
are valid ways to build evidence that some number is {name}`Even`,
but also that these two constructors are the _only_ ways to build
evidence that numbers are {name}`Even`.

:::slidebreak
:::

In other words, if someone gives us evidence `e` for the proposition
{lean}`Even n`, then we know that `e` must be one of two things:

  - `e = Even.zero` and `n = 0`, or
  - `e = Even.succ_succ n' e'` and `n = n' + 2`, where `e'` is
    evidence for `Even n'`.

::::full
This suggests that it should be possible to analyze a
hypothesis of the form {lean}`Even n` much as we do inductively defined
data structures; in particular, it should be possible to argue either by
_case analysis_ or by _induction_ on such evidence.  Let's look at a
few examples to see what this means in practice.
::::

::::terse
This suggests that it should be possible to do _case
analysis_ and even _induction_ on evidence of evenness...
::::

## Destructing and Inverting Evidence

::::full
Suppose we are proving some fact involving a number {lean}`n`, and
we are given {lean}`Even n` as a hypothesis.  We already know how to
perform case analysis on {lean}`n` using {tactic}`cases` or
{tactic}`induction`, generating separate subgoals for the case where
{lean}`n = 0` and the case where {lean}`n = n' + 1` for some {lean}`n'`.
But for some proofs we may instead want to analyze the evidence for
{lean}`Even n` _directly_.

As a tool for such proofs, we can formalize the intuitive
characterization that we gave above for evidence of {lean}`Even n`,
using {tactic}`cases`.
::::

::::terse
We can prove our characterization of evidence for {lean}`Even n`,
using {tactic}`cases`.
::::

```lean
theorem Even.inversion (n : Nat) (h : Even n) :
    (n = 0) ∨ ∃ n', n = n' + 2 ∧ Even n' := by
  cases h with
  | zero => left; rfl
  | @succ_succ n h => right; exists n
```

Facts like this are often called "inversion lemmas" because they
allow us to "invert" some given information to reason about all
the different ways it could have been derived.

::::full
Here there are two ways to prove {lean}`Even n`, and the inversion
lemma makes this explicit.
::::

::::::full
:::::exercise (rating := 1) (name := "le_inversion")
Let's prove a similar inversion lemma for `le`.

```lean
namespace LePlayground

theorem le_inversion (n m : Nat) (h : n ≤ m) :
    (n = m) ∨ (∃ m', m = m' + 1 ∧ n ≤ m') := by
  solution!
    cases h with
    | refl => left; rfl
    | @step m h => right; exists m
```

:::gradeTheorem 1 le_inversion
:::
:::::

```lean
end LePlayground
```
::::::

::::quiz
Which tactics are needed to prove this goal?

```display
∀ (n : Nat), Ev n → n = 1 → true = false
```

(A) {tactic}`cases`
(B) {tactic}`contradiction`
(C) Both {tactic}`cases` and {tactic}`contradiction`
(D) these tactics are not sufficient to solve the goal.

:::quizSolution
```lean
example (n : Nat) (hEven : Even n) (h : n = 1) : true = false := by
  cases hEven with
  | zero => contradiction
  | succ_succ => injection h; contradiction
```
:::
::::

We can use the inversion lemma that we proved above to help
structure proofs:

```lean
theorem Even.of_succ_succ (n : Nat) (h : Even (n + 2)) : Even n := by
  apply inversion at h
  obtain ⟨⟨⟩⟩ | ⟨n', ⟨h₁,  h₂⟩⟩ := h
  injections h₁ heq
  subst heq
  exact h₂
```

::::full
Note how the inversion lemma produces two subgoals, which
correspond to the two ways of proving {name}`Even`.  The first subgoal is
a contradiction that is discharged with {tactic}`contradiction`. The
second subgoal makes use of {tactic}`injections` and {tactic}`subst`.
The {tactic}`subst` tactic takes an equation `x = t` and replaces
`x` by `t` in the context's hypotheses and in the goal, then removes
that equation from the context.

We've defined a handy tactic called {tactic}`inversion` that factors out
this common pattern, saving us the trouble of explicitly stating
and proving an inversion lemma for every `inductive` definition we
make.

Here, the {tactic}`inversion` tactic can detect (1) that the first case,
where {lean}`n = 0`, does not apply and (2) that the {lean}`n'` that appears
in the {name}`Even.succ_succ` case must be the same as {lean}`n`.

The details of how {tactic}`inversion` is implemented are beyond the scope
of this course, but suffice to say Lean's metaprogramming capabilities
are such that almost any sequence of reasoning steps can be implemented
as a new tactic.
::::

:::slidebreak
:::

::::terse
We've provided a handy tactic called {tactic}`inversion` that does
the work of our inversion lemma and more besides.
::::

```lean
example (n : Nat) (h : Even (n + 2)) : Even n := by
  inversion h; assumption
```

::::full
The {tactic}`inversion` tactic can apply the principle of explosion to
"obviously contradictory" hypotheses involving inductively defined
properties, something that takes a bit more work using our
inversion lemma. Compare:

```lean
example : ¬ Even 1 := by
  intro h; apply Even.inversion at h
  obtain ⟨⟨⟩⟩ | ⟨n', ⟨h₁,  h₂⟩⟩ := h
  injections

example : ¬ Even 1 := by
  intro h; inversion h
```
::::

::::::full
:::::exercise (rating := 1) (name := "inversion_practice")
Prove the following result using {tactic}`inversion`.
(For extra practice, you can also prove it using the inversion lemma.)

```lean
theorem Even.of_add_four {n : Nat} (h : Even (n + 4)) : Even n := by
  solution!
    inversion h with
    | succ_succ h' => apply of_succ_succ; exact h'
```

:::gradeTheorem 1 Even.of_add_four
:::

:::::

:::::exercise (rating := 1) (name := "even5_nonsense")
Prove the following result using {tactic}`inversion`.

```lean
theorem Even.even5_nonsense (h : Even 5) : 2 + 2 = 9 := by
  solution!
    inversion h with
    | succ_succ h' =>
      inversion h' with
      | succ_succ h'' =>
        /- Contradiction, as neither constructor can possibly apply... -/
        inversion h''
```

:::gradeTheorem 1 Even.even5_nonsense
:::
:::::

::::::

:::dev "Yipeng Liu (berberman)" NOW
Explain how `cases` works on equalities in Tactics or Logic!

(The following text assums we've alrady done that.)
:::

Recall that equality ({name}`Eq`) is itself an inductively defined proposition,
so {tactic}`inversion` can also be used on equality propositions.

We can use {tactic}`inversion` to re-prove some theorems from
{ref "Tactics"}[Tactics].

```lean
example (n m o : Nat) (h : [n, m] = [o, o]) : [n] = [m] := by
  inversion h; rfl

example (n : Nat) (h : n + 1 = 0) : 2 + 2 = 5 := by
  inversion h
```

For the inductively defined propositions we use,
{tactic}`inversion` behaves much like {tactic}`cases`:
it performs case analysis on the constructors of the hypothesis's inductive type.
However, when the case analysis on an indexed proposition gives _unsolvable_ equations
between its indices, {tactic}`cases` itself fails, whereas {tactic}`inversion` leaves
such equations in the context.

For example, {tactic}`cases` would immediately fail on `h`:

```lean +error (name := elim_failed)
example (n : Nat) (h : Even (n * n)) :
  n * n = 0 ∨ ∃ m, n * n = m + 2 := by
  cases h
```

```leanOutput elim_failed
Dependent elimination failed: Failed to solve equation
  n.mul n = 0
```

{tactic}`inversion` instead leaves the equations in the context,
where we can use them directly:

```lean
example (n : Nat) (h : Even (n * n)) :
  n * n = 0 ∨ ∃ m, n * n = m + 2 := by
  inversion h with
  | zero => left; assumption
  | succ_succ m' _ _ _ => right; exists m'
```

:::full
Here is useful way to think about {tactic}`inversion`.
For an inductively defined hypothesis `h`, `inversion h`
starts with one case for each constructor, then uses the indices of the type of `h`
to eliminate impossible cases, and simplifies the remaining ones.
In the remaining cases, it solves these equations to foce some expressions or substeitue some variables.
If an equation cannot be solved, {tactic}`inversion` leaves it in the context and we can
use tie in the rest of the proof.
:::

::::quiz

Which tactics are needed to prove this goal, in addition to
{tactic}`apply` or {tactic}`exact`?

```display
∀ n, Even (2 + n) → Even n
```

(A) {tactic}`inversion`
(B) {tactic}`inversion`, {tactic}`injections`
(C) {tactic}`inversion`, `rw [Nat.add_comm]`
(D) {tactic}`inversion`, `rw [Nat.add_comm]`, {tactic}`injections`

:::quizSolution
```lean
example (n : Nat) (h : Even (2 + n)) : Even n := by
  rw [Nat.add_comm] at h
  inversion h with | _ h => exact h
```
:::
::::

:::slidebreak
:::

::::full
The {name}`Even.double` exercise above allows us to easily show that
our new notion of evenness is implied by the two earlier ones.
In fact, by {name}`Nat.even_bool_prop` in the {ref "Logic"}[Logic] chapter,
we already know that those are equivalent to each other. To show that
`Nat.Even`, `Even`, and `Nat.even` coincide, we just need the following lemma.
::::

::::terse
Let's try to show that our new notion of evenness implies
our earlier notion (the one based on {name}`Nat.double`).
::::

:::full
We could try to proceed by case analysis or induction on `n`.  But
since {name}`Even` is mentioned in a premise, this strategy seems
unpromising, because (as we've noted before) the induction
hypothesis will talk about `n - 1` (which is _not_ even!).  Thus, it
seems better to first try {tactic}`inversion` on the evidence for {name}`Even`.
:::

```lean +error
example (n : Nat) (h : Even n) : Nat.Even n := by
  inversion h with
  | zero => exists 0 -- The first case can be solved triviall.
  | succ_succ n' h' =>
```

Unfortunately, the second case is harder.  We need to show
`∃ n₀, n' + 2 = double n₀`, but the only available assumption is
`h'`, which states that `Even n'` holds.
In other words, what we need here is precisely the result we
are trying to prove, but applied to the smaller evidence `h'`.

## Induction on Evidence

If this story feels familiar, it is no coincidence: We
encountered similar problems in the {ref "Induction"}[Induction] chapter,
when trying to use case analysis to prove results that required
induction.  And once again the solution is... induction!

::::full
The behavior of {tactic}`induction` on evidence is the same as its
behavior on data: It causes Lean to generate one subgoal for each
constructor that could have been used to build that evidence, while
providing an induction hypothesis for each recursive occurrence of
the property in question.

To prove that a property of {lean}`n` holds for all even numbers
(i.e., those for which {lean}`Even n` holds), we can use induction on
{lean}`Even n`. This requires us to prove two things, corresponding to
the two ways in which {lean}`Even n` could have been constructed. If it
was constructed by {lean}`Even.zero`, then {lean}`n = 0` and the
property must hold of {lean}`0`. If it was constructed by
{lean}`Even.succ_succ`, then the evidence of {lean}`Even n`
is of the form `Even.succ_succ n' h'`, where {lean}`n = n' + 2` and
`h'` is evidence for {lean}`Even n'`. In this case, the inductive hypothesis
says that the property we are trying to prove holds for {lean}`n'`.
::::

Let's try proving that lemma again:

```lean
theorem Even.nat_even (n : Nat) (h : Even n) : Nat.Even n := by
  induction h with
  | zero => exists 0 -- (`0 = double 0` is closed by `exists`'s final `rfl`)
  | succ_succ h' ih =>
    let ⟨k, hk⟩ := ih
    exists k + 1; rw [Nat.double_succ, hk]
```

::::full
Here, we can see that Lean produced an `ih` that corresponds
to `h`, the single recursive occurrence of {name}`Even` in its own
definition.  Since `h'` mentions {lean}`n'`, the induction hypothesis
talks about {lean}`n'`, as opposed to {lean}`n` or some other number.
::::

::::::full
The equivalence between the second and third definitions of
evenness now follows.

```lean
theorem Even.iff_nat_even (n : Nat) : Even n ↔ Nat.Even n := by
  apply Iff.intro
  · intro h; exact nat_even _ h
  · intro ⟨k, hk⟩; rw [hk]; exact double k
```

As we will see in later chapters, induction on evidence is a
recurring technique across many areas ─ in particular for
formalizing the semantics of programming languages.

The following exercises provide simpler examples of this
technique, to help you familiarize yourself with it.

:::::exercise (rating := 2) (name := "Even.add")
```lean
theorem Even.add (n m : Nat) (hn : Even n) (hm : Even m) : Even (n + m) := by
  solution!
    induction hn with
    | zero => rw [Nat.zero_add]; exact hm
    | succ_succ h' ih =>
      rw [Nat.add_comm, Nat.add_succ, Nat.add_succ, Nat.add_comm]
      apply Even.succ_succ; exact ih
```

:::gradeTheorem 2 Even.add
:::
:::::

:::::exercise (rating := 3) (name := "Even.of_add_left") (level := Advanced)
```lean
theorem Even.of_add_left (n m : Nat) (h : Even (n + m)) (hn : Even n) : Even m := by
  /- Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. -/
  solution!
    induction hn generalizing m with
    | zero => rw [Nat.zero_add] at h; exact h
    | succ_succ h' ih =>
      rw [Nat.add_comm, Nat.add_succ, Nat.add_succ, Nat.add_comm] at h
      inversion h; apply ih; assumption
```

:::gradeTheorem 3 Even.of_add_left
:::
:::::

:::::exercise (rating := 3) (name := "add_of_add_left") (optional := true)
This exercise can be completed without induction or case analysis.
But, you will need a clever `have` and some tedious rewriting.
Hint: Is {lean}`(n + m) + (n + k)` even?

```lean
theorem Even.add_of_add_left (n m k : Nat)
    (hₙₘ : Even (n + m))
    (hₙₚ : Even (n + k)) :
    Even (m + k) := by
  solution!
    apply of_add_left (n + n)
    · have h : n + n + (m + k) = n + m + (n + k) := by
        rw [Nat.add_assoc, Nat.add_assoc]
        congr 1
        apply Nat.add_left_comm
      rw [h]
      apply add
      · assumption
      · assumption
    · rw [← Nat.double_add]; exact Even.double n
```

:::::

::::::

:::full
Another example of a proposition that can be characterized both recursively and
inductively is the {lean}`List.In` predicate we defined in the {ref "Logic"}[Logic] chapter.
As a reminder, the recursive definition we saw looked like this:
:::

:::terse
Recall the definition of {name}`List.In` from last chapter:
:::

```recall
def List.In {α : Type} (x : α) (xs : List α) : Prop :=
  match xs with
  | [] => False
  | x' :: xs' => x = x' ∨ In x xs'
```

We can also write this definition inductively like so:

```lean
inductive List.In' {α : Type} (x : α) : List α → Prop
  | head {l : List α} : In' x (x :: l)
  | tail {y : α} {l : List α} (h : In' x l) : In' x (y :: l)
```

In fact, this is exactly how Lean defines this proposition,
which it calls {name}`Membership.mem` and which is written {lean}`x ∈ l`.
Its negation {lean}`¬ x ∈ l` is also written as {lean}`x ∉ l`.

:::::full
A good exercise to test your understanding of induction on
evidence is to prove the equivalence of these definitions:

::::exercise (rating := 2) (name := "in_mem")
```lean
theorem List.in_iff_mem {α} (x : α) (l : List α) : List.In x l ↔ x ∈ l := by
  solution!
    constructor
    · intro h; induction l with
      | nil => apply List.In_nil at h; contradiction
      | cons x xs ih =>
        rw [List.In_cons] at h
        obtain h | h := h
        · subst h; constructor
        · constructor; exact ih h
    · intro h; induction h with
      | head l' => rw [List.In_cons]; left; rfl
      | tail h ih => rw [List.In_cons]; right; assumption
```

:::gradeTheorem 3 List.in_iff_mem
:::
::::
:::::

The characterizing lemmas for `∈` are called
{name}`List.mem_nil_iff` and {name}`List.mem_cons`.

## Multiple Induction Hypotheses

:::suppressPreviousHeaderWhenTerse
:::

::::full
Recall the definition of the reflexive, transitive, closure of a relation:

```recall
inductive ReflTransGen {α : Type} (r : α → α → Prop) : α → α → Prop where
  | step {x y : α} (h : r x y) : ReflTransGen r x y
  | refl {x : α} : ReflTransGen r x x
  | trans {x y z : α}
    (h₁ : ReflTransGen r x y)
    (h₂ : ReflTransGen r y z) :
    ReflTransGen r x z
```

Let's say that a relation on a type {lean}`α` is _diagonal_ if it
refines the identity relation ─ i.e., if `r x y` implies {lean}`x = y`.

:::dev
NDS 25: I originally wanted to do this with the empty
relation, defined inductively, but this requires introducing the
surprising behavior of unhabitated types, which I don't think have
been covered (yet?). Maybe they should be?
BCP 25: This one seems good.
:::

```lean
def Diagonal {α : Type} (r : α → α → Prop) := ∀ {x y}, r x y → x = y
```

Now consider the following lemma about diagonal relations:

```lean
theorem closure_of_diagonal_is_diagonal {α : Type} (r : α → α → Prop)
    (hDiag : Diagonal r) :
    Diagonal (ReflTransGen r) := by
  intro x y h
  induction h with
  | step hr => rw [hDiag hr]
  | refl => rfl
  | trans _ _ ihxy ihyz => rw [ihxy, ihyz]
```

Something interesting happens here: there are two
induction hypotheses, `ihxy` and `ihyz`! If you think about it, it
is not that weird: we are in the case `trans`, which has
two recursive components, `hxy`, relating `x` to `y` and `hyz`,
relating `y` to `z`. Hence we may want (and will actually need)
an induction hypothesis for `hxy` and one for `hyz` ─ they are
called `ihxy` and `ihyz` here. In general, Lean will always
generate one induction hypothesis per recursive constructor of
the type being inducted over.

:::dev
HIDE: NDS comparing the previous proof to the pen-and-paper version
could be an idea to consider, as the way people tend to write it
on paper differs a bit from the mechanized proof.  BCP 25: Yes.
:::
::::

::::::full
:::::exercise (rating := 4) (name := "Even'") (level := Advanced) (optional := true)
:::instructors
This is pretty hard, unless you know the trick that
the sample proof uses!!  But at least it's marked as
advanced and optional. :-)
:::

In general, there may be multiple ways of defining a
property inductively.  For example, here's a (slightly contrived)
alternative definition for {name}`Even`:

```lean
inductive Even' : Nat → Prop where
  | zero : Even' 0
  | two : Even' 2
  | add {n m : Nat} (h₁ : Even' n) (h₂ : Even' m) : Even' (n + m)
```

Prove that this definition is logically equivalent to the old one.
To streamline the proof, use the technique (from the {ref "Logic"}[Logic]
chapter) of applying theorems to arguments, and note that the same
technique works with constructors of inductively defined
propositions.

```lean
theorem Even'.iff_Even n : Even' n ↔ Even n := by
  solution!
    apply Iff.intro
    · intro h; induction h
      · constructor
      · constructor; constructor
      · apply Even.add; assumption; assumption
    · intro h; induction h with
      | zero => constructor
      | @succ_succ n _ _ =>
        rw [← Nat.add_zero n]
        constructor; assumption; constructor
```

:::::

We can do similar inductive proofs on the {name}`Perm3` relation,
which we defined earlier as follows:

```recall
inductive Perm3 {α : Type} : List α → List α → Prop where
  | swap12 {x y z : α} : Perm3 [x, y, z] [y, x, z]
  | swap23 {x y z : α} : Perm3 [x, y, z] [x, z, y]
  | trans {l₁ l₂ l₃ : List α}
    (h₁₂ : Perm3 l₁ l₂)
    (h₂₃ : Perm3 l₂ l₃) :
    Perm3 l₁ l₃
```

```lean
namespace Perm3

theorem symm {α} (l₁ l₂ : List α)
    (h : Perm3 l₁ l₂) : Perm3 l₂ l₁ := by
  induction h with
  | swap12 => constructor
  | swap23 => constructor
  | trans _ _ ih₁₂ ih₂₃ =>
    exact trans ih₂₃ ih₁₂
```

:::::exercise (rating := 2) (name := "Perm3_In")
If you find yourself dealing with deeply nested {tactic}`cases` in
this proof, think back to {ref "Logic"}[Logic] where you learned
about the {tactic}`obtain` tactic.

```lean
theorem In {α} (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∈ l₁) : x ∈ l₂ := by
  solution!
    induction hPerm with
    | swap12 =>
      rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
      obtain h | h | h | h := hIn
      · right; left; assumption
      · left; assumption
      · right; right; left; assumption
      · contradiction
    | swap23 =>
      rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
      obtain h | h | h | h := hIn
      · left; assumption
      · right; right; left; assumption
      · right; left; assumption
      · contradiction
    | trans _ _  ih₁₂ ih₂₃ =>
      apply ih₂₃; apply ih₁₂; apply hIn
```

:::gradeTheorem 2 In
:::
:::::

:::::exercise (rating := 1) (name := "Perm3_NotIn") (optional := true)
```lean
theorem NotIn {α} (x : α) (l₁ l₂ : List α)
    (hPerm : Perm3 l₁ l₂) (hIn : x ∉ l₁) : x ∉ l₂ := by
  solution!
    intro hContra
    apply hIn; apply In
    . apply symm; exact hPerm
    . exact hContra
```

:::::

:::::exercise (rating := 2) (name := "NotPerm3") (optional := true)
Proving that something is NOT a permutation is quite tricky. Some
of the lemmas above, like {name}`Perm3.In` can be useful for this.

```lean
theorem Not : ¬ Perm3 [1, 2, 3] [1, 2, 4] := by
  solution!
    intro h; apply (Perm3.In 3) at h
    have h4 : 3 ∉ [1, 2, 4] := by
      rw [List.mem_cons, List.mem_cons, List.mem_cons]; intro h4
      obtain h | h | h | h := h4
      · contradiction
      · contradiction
      · contradiction
      · contradiction
    apply h4; apply h
    rw [List.mem_cons, List.mem_cons, List.mem_cons]
    right; right; left; rfl
```

```lean
end Perm3
```
:::::

:::dev PotentialImprovement
Optional / advanced exercise (or exam question???): Extend
this definition to permutations on arbitrary-length lists.  Make
sure that you can prove the following...
- length-invariant
- if we filter a {name}`Nat` list and its permutation by equality to some
  number, we get the same length (indeed, this could be an
  alternate characterization, I guess)
:::
::::::

# Exercising with Inductive Relations

:::suppressPreviousHeaderWhenTerse
:::

:::dev "Chris Henson (chenson2018)" BeforeNextRelease
Bad flow + duplication needs fixing.
Could move some of this to the top.
In the terse version this whole section is useless,
it only has a (mostly) duplicated definition.
For now FULLED the whole thing, but better fix seems needed.
:::

::::::full
```lean
namespace LePlayground
```

Recall the "less than or equal to" relation on numbers that we briefly saw above.

```recall
inductive Le : Nat → Nat → Prop where
  | refl {n : Nat}                : Le n n
  | step {n m : Nat} (h : Le n m) : Le n (m + 1)
```

Proofs of facts about `≤` using the constructors {name}`Le.refl` and
{name}`Le.step` follow the same patterns as proofs about properties, like
{name}`Even` above. We can {tactic}`apply` the constructors to prove `≤`
goals (e.g., to show that {lean}`3 ≤ 3` or {lean}`3 ≤ 6`), and we can use
tactics like {tactic}`inversion` to extract information from `≤`
hypotheses in the context (e.g., to prove that {lean}`(2 ≤ 1) → 2 + 2 = 5`.)

:::slidebreak
:::

Here are some sanity checks on the definition.  (Notice that,
although these are the same kind of simple "unit tests" as we gave
for the testing functions we wrote in the first few lectures, we
must construct their proofs explicitly ─ {tactic}`rw` and {tactic}`rfl` don't do the job,
because the proofs aren't just a matter of simplifying computations.)

Some sanity checks...

```lean
example : 3 ≤ 3 := by
  workinclass!
    apply Le.refl

example : 3 ≤ 6 := by
  workinclass!
    apply Le.step; apply Le.step
    apply Le.step; apply Le.refl

example (h : 2 ≤ 1) : 2 + 2 = 5 := by
  workinclass!
    inversion h with
    | step h' => inversion h'
```

:::slidebreak
:::

The "strictly less than" relation {lean}`n < m` can now be defined
in terms of {lean}`Nat.le`.

```lean
def Lt (n m : Nat) : Prop := Le (n + 1) m

scoped infix:50 (priority := high) " < " => Lt
```

:::slidebreak
:::

The `≥` operation is defined in terms of `≤`.
Lean provides a theorem {name}`ge_iff_le` allowing us to rewrite between them.

```lean
def Ge (m n : Nat) : Prop := Le n m

scoped infix:50 (priority := high) " ≥ " => Ge

example (m n : Nat) (h : m ≥ n) : n ≤ m := by
  rw [Ge] at h
  assumption
```

From the definition of {name}`Le`, we can sketch the behaviors of
{tactic}`cases` and {tactic}`induction` on a hypothesis `h`
providing evidence of the form {lean}`n ≤ m`.  Doing `cases h`
will generate two cases. In the first case, {lean}`n = m`, and it
will replace instances of {lean}`m` with {lean}`n` in the goal and context.
In the second case, {lean}`n = m' + 1` for some {lean}`m'` for which {lean}`n ≤ m'`
holds, and it will replace instances of {lean}`m` with {lean}`m' + 1`.
Doing `inversion h` will remove impossible cases and add generated
equalities to the context for further use. Doing `induction h`
will, in the second case, add the induction hypothesis that the
goal holds when {lean}`m` is replaced with {lean}`m'`.

Here are a number of facts about the `≤` and `<` relations that
we are going to need later in the course.  The proofs make good
practice exercises.

:::::exercise (rating := 3) (name := "le_facts")
```lean
theorem le_trans (m n k : Nat) (h₁ : m ≤ n) (h₂ : n ≤ k) : m ≤ k := by
  solution!
    induction h₂ with
    | refl => assumption
    | step _ ih => constructor; exact ih
```

:::gradeTheorem "0.5" le_trans
:::

```lean
theorem zero_le (n : Nat) : 0 ≤ n := by
  solution!
    induction n with
    | zero => constructor
    | succ n ih => constructor; exact ih
```

:::gradeTheorem "0.5" zero_le
:::

```lean
theorem succ_le_succ (n m : Nat) (h : n ≤ m) : n + 1 ≤ m + 1 := by
  solution!
    induction h with
    | refl => constructor
    | step h ih =>
      rw [Nat.succ_add]
      constructor; exact ih
```

:::gradeTheorem "0.5" succ_le_succ
:::

```lean
theorem le_of_succ_le_succ (n m : Nat) (h : n + 1 ≤ m + 1) : n ≤ m := by
  solution!
    inversion h with
    | refl => constructor
    | step h' =>
      apply le_trans _ (n + 1) _
      · constructor; constructor
      · assumption
```

:::gradeTheorem 1 le_of_succ_le_succ
:::

```lean
theorem le_not_succ_le_self (n : Nat) : ¬ (n + 1 ≤ n) := by
  solution!
    induction n with
    | zero => intro h; contradiction
    | succ n' ih =>
      intro h
      apply ih
      apply le_of_succ_le_succ
      assumption
```

```lean
theorem le_add_right (n m : Nat) : n ≤ n + m := by
  solution!
    induction n with
    | zero => rw [Nat.zero_add]; apply zero_le
    | succ n' ih =>
      rw [Nat.succ_add]
      apply succ_le_succ
      assumption
```

:::gradeTheorem "0.5" le_add_right
:::
:::::

:::::exercise (rating := 2) (name := "le_facts1")
```lean
theorem le_and_le_of_add_le (n₁ n₂ m : Nat) (h : n₁ + n₂ ≤ m) : n₁ ≤ m ∧ n₂ ≤ m := by
  solution!
    induction h with
    | refl =>
      constructor
      · apply le_add_right
      · rw [Nat.add_comm]; apply le_add_right
    | step =>
      constructor
      · apply le_trans (n := n₁ + n₂)
        · apply le_add_right
        · apply Le.step; assumption
      · apply le_trans (n := n₁ + n₂)
        · rw [Nat.add_comm]; apply le_add_right
        · apply Le.step; assumption
```

:::gradeTheorem 1 le_and_le_of_add_le
:::

```lean
theorem le_or_le_of_add_le_add (n m p q : Nat) (h : n + m ≤ p + q) : n ≤ p ∨ m ≤ q := by
  /- Hint: May be easiest to prove by induction on `n`. -/
  solution!
    induction n generalizing m p q with
    | zero => left; apply zero_le
    | succ n' ih =>
      cases p with
      | zero =>
        right; apply le_and_le_of_add_le at h
        have ⟨_, h⟩ := h
        rw [Nat.zero_add] at h; assumption
      | succ p' =>
        rw [Nat.succ_add, Nat.succ_add] at h
        apply le_of_succ_le_succ at h
        apply ih at h
        cases h with
        | inl => left; apply succ_le_succ; assumption
        | inr => right; assumption
```

:::gradeTheorem 1 le_or_le_of_add_le_add
:::
:::::

:::::exercise (rating := 2) (name := "plus_le_facts2")
```lean
theorem add_le_add_left (n m p : Nat) (h : n ≤ m) : p + n ≤ p + m := by
  solution!
    induction p with
    | zero =>
      rw [Nat.zero_add, Nat.zero_add]; assumption
    | succ p' ih =>
      rw [Nat.succ_add, Nat.succ_add]
      apply succ_le_succ
      assumption
```

:::gradeTheorem "0.5" add_le_add_left
:::

```lean
theorem add_le_add_right (n m p : Nat) (h : n ≤ m) : n + p ≤ m + p := by
  solution!
    rw [Nat.add_comm, Nat.add_comm m]
    apply add_le_add_left
    assumption
```

:::gradeTheorem "0.5" add_le_add_right
:::

```lean
theorem le_add_right_of_le (n m p : Nat) (h : n ≤ m) : n ≤ m + p := by
  solution!
    induction p with
    | zero => rw [Nat.add_zero]; assumption
    | succ p' ih =>
      rw [← Nat.add_assoc]; constructor; assumption
```

:::gradeTheorem 1 le_add_right_of_le
:::
:::::

:::::exercise (rating := 3) (name := "lt_facts") (optional := true)


```lean
theorem lt_not_lt_zero (n : Nat) : ¬ n < 0 := by
  intro h
  inversion h
```

```lean
theorem lt_or_ge (n m : Nat) : n < m ∨ n ≥ m := by
  solution!
    induction n generalizing m with
    | zero =>
      cases m with
      | zero => right; constructor
      | succ _ =>
        left;
        apply succ_le_succ;
        apply zero_le
    | succ n' ih =>
      cases m with
      | zero =>
        rw [Ge]; right
        apply zero_le
      | succ m' =>
        cases ih m' with
        | inl ih =>
          left
          apply succ_le_succ
          exact ih
        | inr ih =>
          right
          apply succ_le_succ
          exact ih
```

```lean
theorem le_of_lt (n m : Nat) (h : n < m) : n ≤ m := by
  solution!
    apply le_of_succ_le_succ
    constructor; assumption
```

```lean
theorem lt_and_lt_of_add_lt (n₁ n₂ m : Nat) (h : n₁ + n₂ < m) : n₁ < m ∧ n₂ < m := by
  solution!
    constructor
    · apply le_trans (n := (n₁ + n₂) + 1)
      · apply succ_le_succ
        apply le_add_right
      · exact h
    · apply le_trans (n := (n₂ + n₁) + 1)
      · apply succ_le_succ
        apply le_add_right
      · rw [Nat.add_comm n₂]; assumption
```

:::::

:::::exercise (rating := 4) (name := "ble") (optional := true)
```lean
theorem le_of_ble_eq_true (n m : Nat) (h : Nat.ble n m = true) : n ≤ m := by
  solution!
    induction n generalizing m with
    | zero => apply zero_le
    | succ n' ih =>
      cases m with
      | zero =>
        contradiction
      | succ m' =>
        rw [Nat.ble] at h
        apply succ_le_succ
        apply ih; apply h
```

```lean
theorem ble_eq_true_of_le n m (h : n ≤ m) : Nat.ble n m = true := by
  solution!
    induction n generalizing m with
    | zero => rw [Nat.ble]
    | succ n' ih =>
      cases m with
      | zero => contradiction
      | succ m' =>
        rw [Nat.ble]
        apply le_of_succ_le_succ at h
        apply ih at h
        assumption
```

Hint: The next two can easily be proved without using `induction`.

```lean
theorem ble_eq (n m : Nat) : Nat.ble n m = true ↔ n ≤ m := by
  solution!
    constructor
    · apply le_of_ble_eq_true
    · apply ble_eq_true_of_le
```

```lean
theorem ble_trans (n m k : Nat) :
    Nat.ble n m = true →
    Nat.ble m k = true →
    Nat.ble n k = true := by
  solution!
    rw [ble_eq, ble_eq, ble_eq]
    apply le_trans
```
:::::

:::dev PotentialImprovement
Another potential exercise:  m ≤ n → n = m + (n - m).
See p. 188 in CoqArt.
:::

```lean
end LePlayground
```

:::::exercise (rating := 3) (name := "R_provability") (manual := true)
We can define three-place relations, four-place relations,
etc., in just the same way as binary relations.  For example,
consider the following three-place relation on numbers:

```lean
namespace RProvability
```

```lean
inductive R : Nat → Nat → Nat → Prop where
  | c1                                               : R  0      0       0
  | c2 {m n k : Nat} (h : R  m       n       k)      : R (m + 1) n      (k + 1)
  | c3 {m n k : Nat} (h : R  m       n       k)      : R  m     (n + 1) (k + 1)
  | c4 {m n k : Nat} (h : R (m + 1) (n + 1) (k + 2)) : R  m      n       k
  | c5 {m n k : Nat} (h : R  m       n       k)      : R  n      m       k
```

1. Which of the following propositions are provable?
- `R 1 1 2`
- `R 2 2 6`

2. If we dropped constructor `c5` from the definition of `R`,
would the set of provable propositions change?  Briefly (1
sentence) explain your answer.

3. If we dropped constructor `c4` from the definition of `R`,
would the set of provable propositions change?  Briefly (1
sentence) explain your answer.

::::solution

1. The first proposition is provable and the second is not.

```lean
example : R 1 1 2 := by
  apply R.c2
  apply R.c3
  apply R.c1
```

The key invariant here is that whenever `R m n k` holds, we must have `k = m + n`.
We can prove this invariant as the follows:

```lean
theorem R.eq_add {m n k : Nat} (h : R m n k) : k = m + n := by
  induction h with lia
```

{tactic}`lia` helps us solve linear arithmetic goals.
We'll learn more about it in the {ref "Automation"}[Automation] chapter.

Now we can disprove the second proposition:

```lean
example : ¬ R 2 2 6 := by
  intro h
  apply R.eq_add at h
  contradiction
```

2. Dropping `c5` would not change the set of provable
  propositions. `c4` and `c1` don't interact with `c5`, since
  they're already symmetric in `m` and `n`; `c2` followed by
  `c5` is equivalent to `c3`, and vice versa.

3. Dropping `c4` would not change the set of provable
  propositions. This constructor just "undoes" one application
  of `c2` and one application of `c3`. More precisely, the
  only way we can construct evidence for `R (S m) (S n) (S (S o))`
  is by applying `c2` and `c3` (in either order) to evidence for
  `R m n o`, so the latter must already hold. (This can be proved
  by induction, although the proof is surprisingly tedious.)

We can prove `c4` and `c5` are redundant by re-defining `R'` with only `c1`, `c2`, and `c3`,
and prove `R'` is equivalent to {name}`R`.

Another useful fact is that the converse of the above invariant, {name}`R.eq_add`, is also true:

```lean
theorem R.of_eq_add {m n k : Nat} (h : k = m + n) : R m n k := by
  subst h
  induction n with
  | zero => induction m with
    | zero => apply c1
    | succ n _ => apply c2; assumption
  | succ n _ => apply c3; assumption
```

Now we are ready to define `R'`.

```lean -keep
inductive R' : Nat → Nat → Nat → Prop where
  | c1 : R' 0 0 0
  | c2 m n k (h : R' m n k) : R' (m + 1) n (k + 1)
  | c3 m n k (h : R' m n k) : R' m (n + 1) (k + 1)

theorem R'.c5 {m n k : Nat} (h : R' m n k) : R' n m k := by
  induction h with
  | c1 => apply c1
  | c2 m n o h ih => apply c3; assumption
  | c3 m n o h ih => apply c2; assumption

theorem R'.eq_add {m n k : Nat} (h : R' m n k) : k = m + n := by
  induction h with lia

theorem R'.of_eq_add {m n : Nat} : R' m n (m + n) := by
  induction n with
  | zero => induction m with
    | zero => apply c1
    | succ n _ => apply c2; assumption
  | succ n _ => apply c3; assumption

theorem R'.c4 {m n k : Nat} (h : R' (m + 1) (n + 1) (k + 2)) : R' m n k := by
  have := eq_add h
  have hk : k = m + n := by lia
  subst hk
  exact of_eq_add

theorem R'.iff_R {m n k : Nat} : R' m n k ↔ R m n k := by
  constructor
  · intro h
    induction h with
    | c1 => apply R.c1
    | c2 m n k h ih => apply R.c2; assumption
    | c3 m n k h ih => apply R.c3; assumption
  · intro h
    induction h with
    | c1 => apply c1
    | c2 h ih => apply c2; assumption
    | c3 h ih => apply c3; assumption
    | c4 h ih => apply c4; assumption
    | c5 h ih => apply c5; assumption
```
::::

:::grade
`GRADE_MANUAL 3: R_provability`
:::
:::::

:::::exercise (rating := 3) (name := "R_fact") (optional := true)
The relation {name}`R` above actually encodes a familiar function.
Figure out which function; then state and prove this equivalence
in Lean.

```lean
def funR : Nat → Nat → Nat
  := solution!(fun m n => m + n)

theorem funR_iff_R {m n k : Nat} : funR m n = k ↔ R m n k := by
  constructor
  · intro h
    rw [funR] at h
    subst h
    apply R.of_eq_add
    rfl
  · intro h
    have := R.eq_add h
    rw [funR, this]
```

```lean
end RProvability
```
:::::

:::::exercise (rating := 4) (name := "subsequence") (level := Advanced)
A list is a _subsequence_ of another list if all of the elements
in the first list occur in the same order in the second list,
possibly with some extra elements in between. For example,

```display
[1, 2, 3]
```

is a subsequence of each of the lists

```display
[1, 2, 3]
[1, 1, 1, 2, 2, 3]
[1, 2, 7, 3]
[5, 6, 1, 9, 9, 2, 7, 3, 8]
```

but it is _not_ a subsequence of any of the lists

```display
[1, 2]
[1, 3]
[5, 6, 2, 1, 7, 3, 8].
```

- Define an inductive proposition `Subseq` on {lean}`List Nat` that
  captures what it means to be a subsequence. There are a number
  of correct ways to do this. You should make sure that your
  definition behaves correctly on all the positive and negative
  examples above, but you do not need to prove this formally.

- Prove `Subseq.refl` that subsequence is reflexive, that is,
  any list is a subsequence of itself.

- Prove `Subseq.append` that for any lists {lean}`l₁`, {lean}`l₂`, and {lean}`l₃`,
  if {lean}`l₁` is a subsequence of {lean}`l₂`, then {lean}`l₁` is also a subsequence
  of {lean}`l₂ ++ l₃`.

- (Harder) Prove `Subseq.trans` that subsequence is transitive ─
  that is, if {lean}`l₁` is a subsequence of {lean}`l₂` and {lean}`l₂` is a
  subsequence of {lean}`l₃`, then {lean}`l₁` is a subsequence of {lean}`l₃`.

::::hide
```lean
/- SOONER: (BCP'20) One of my students this semester pointed out
   that there is another definition that is intuitively perhaps just
   as reasonable and that makes these properties either easy or
   trivial: -/
inductive Subseq' : List Nat → List Nat → Prop where
  | subseq'_0 {l : List Nat} : Subseq' l l
  | subseq'_inductive1 {l l₁ l₂ lx ly lz: List Nat}
    (h : Subseq' l (l₁ ++ l₂)) :
    Subseq' l (lx ++ l₁ ++ ly ++ l₂ ++ lz)
  | subseq'_inductive2 {l₁ l₂ l₃ : List Nat}}
    (h₁ : Subseq' l₁ l₂)
    (h₂ : Subseq' l₂ l₃) :
    Subseq' l₁ l₃

/- SOONER: MRC 3/22: It's MUCH worse than that! a total relation
   suffices! (BCP 25: Really? It gets all the positive examples above,
   obviously, but not the negative ones... right?) Also this is
   another case where a [Fixpoint] would suffice instead of an
   inductively-defined proposition: [subseq] is definable as a
   structurally recursive function. -/
/- SOONER: FSR'25 - This definition of subseq also works, though it requires a
   lemma mirroring subseq_app that allows prepending an excess List.
   Notably, this only has two cases, in spite of the hint above.
   (BCP 25: Removed the hint.) -/
inductive Subseq'' : List Nat → List Nat → Prop where
  | sub_nil'' {l : List Nat} : Subseq'' [] l
  | sub_cons'' {l l' l₀ : List Nat} {x : Nat}
    (h : Subseq'' l l') :
    Subseq'' (x :: l) (l₀ ++ (x :: l'))
```
::::

:::dev BeforeNextRelease
```
AC'21: I think that it is more atomic to consider
[sub_nil : subseq [] []]. The benefits is that it makes calls to
[inversion] produce fewer goals. The downside is that one has to
state as a lemma [sub_nil_l : forall l, subseq [] l], however it
would be nice to have this as an exercise anyway, because otherwise
students who go for the definition of [sub_seq [] []] are required
to guess the need for [sub_nil_l].
BCP: I agree this version could be nicer to suggest, and I agree that
adding this lemma as a warm-up exercise is nice.
```

Sainati 25: I am generally not against proofs that can be
made much easier with smart inductive definitions (this is sort of the
whole ball game in a way, isn't it?) but one way to make sure students
can't trivialize the exercise is to just give them the definition we
want them to use? We could also add a (maybe optional) question
afterwards to provide a different definition that makes the proofs
easier (and maybe prove them equivalent).
:::

```lean
inductive Subseq : List Nat → List Nat → Prop where
-- SOLUTION
  | nil {l : List Nat} : Subseq [] l
  | take {x : Nat} {l₁ l₂ : List Nat}
      (h : Subseq l₁ l₂) :
      Subseq (x :: l₁) (x :: l₂)
  | skip {x : Nat} {l₁ l₂ : List Nat}
      (h : Subseq l₁ l₂) :
      Subseq l₁ (x :: l₂)
-- END SOLUTION

namespace Subseq

theorem refl (l : List Nat) : Subseq l l := by
  solution!
    induction l with
    | nil => constructor
    | cons x xs ih =>
      constructor; assumption

theorem append (l₁ l₂ l₃ : List Nat)
    (h : Subseq l₁ l₂) : Subseq l₁ (l₂ ++ l₃) := by
  solution!
    induction h with
    | nil  => constructor
    | take => constructor; assumption
    | skip => constructor; assumption
```

:::autogradedHole Subseq
:::

```lean
theorem trans (l₁ l₂ l₃ : List Nat)
    (h12 : Subseq l₁ l₂)
    (h23 : Subseq l₂ l₃) :
    Subseq l₁ l₃ := by
  /- Hint: be careful about what you are doing induction on and which
     other things need to be generalized... -/
  solution!
    induction h23 generalizing l₁ with
    | nil => inversion h12; constructor
    | take _ ih =>
      inversion h12; constructor
      · constructor; apply ih; assumption
      · constructor; apply ih; assumption
    | skip _ ih =>
      constructor; apply ih; assumption

end Subseq
```

:::gradeTheorem 1 Subseq.refl
:::

:::gradeTheorem 2 Subseq.append
:::

:::gradeTheorem 3 Subseq.trans
:::
:::::

:::::exercise (rating := 2) (name := "R_provability2") (optional := true) (manual := true)
Suppose we give Lean the following definition:

```lean
namespace RProvability2

inductive R : Nat → List Nat → Prop where
  | c1                                            : R  0      []
  | c2 {n : Nat} {l : List Nat} (h : R  n      l) : R (n + 1) (n :: l)
  | c3 {n : Nat} {l : List Nat} (h : R (n + 1) l) : R  n      l
```

Which of the following propositions are provable?

- `R 2 [1, 0]`
- `R 1 [1, 2, 1, 0]`
- `R 6 [3, 2, 1, 0]`

:::solution
The first two are provable, the third is not.

```lean
example : R 2 [1, 0] := by
  apply R.c2
  apply R.c2
  apply R.c1
```

```lean
example : R 1 [1, 2, 1, 0] := by
  apply R.c3
  apply R.c2
  apply R.c3
  apply R.c3
  apply R.c2
  apply R.c2
  apply R.c2
  apply R.c1
```

In case this question puzzled you, one good way to understand
definitions like this is to explore their implications with
concrete examples, e.g.
```display
R 0 []           by c1
R 1 [0]          by c2 using R 0 []
R 2 [1, 0]       by c2 using R 1 [0]
R 3 [2, 1, 0]    by c2 using R 2 [1, 0]
R 2 [2, 1, 0]    by c3 using R 3 [2, 1, 0]
R 1 [2, 1, 0]    by c3 using R 2 [2, 1, 0]
R 2 [1, 2, 1, 0] by c2 using R 1 [2, 1, 0]
R 1 [1, 2, 1, 0] by c3 using R 2 [1, 2, 1, 0]
etc.
```
If you do a few more of these yourself, you should see the pattern
emerging.
:::


```lean
end RProvability2
```

:::::

::::::

::::::full
:::::exercise (rating := 2) (name := "total_relation") (optional := true)
Define an inductive binary relation `total_relation` that holds
between every pair of natural numbers.

```lean
inductive TotalRelation : Nat → Nat → Prop where
  -- SOLUTION
  | tot (n m : Nat) : TotalRelation n m
  -- END SOLUTION

theorem total_relation_is_total (n m : Nat) : TotalRelation n m := by
  solution!
    constructor
```

:::::

:::::exercise (rating := 2) (name := "empty_relation") (optional := true)
Define an inductive binary relation `empty_relation` (on numbers)
that never holds.

:::dev "Michael Clarkson (clarksmr)" PotentialImprovement (year := 2020)
this exercise feels unsolvable given what students
already know.  I don't believe we've ever shown them that an
inductive type can have zero constructors, or what the syntax for
that would be.  (That will come when we show them how to define
False in ProofObjects.) Should a hint be added?

BCP 20: Maybe not needed since it's optional anyway? But also,
can't it be done with a inductive definition with nonzero cases but
no base case?

APT 21: Yes, although arguably that is even less obvious.
MRC 3/22: And also something I can't recall we've shown them.

MRC 3/22: `unsolvable ∧ optional → unsolvable`

MTF 6/22: A solution that more than one of my students have submitted
is using a "base" case with a built-in contradiction:
`emp n m : 0 = 1 → empty_relation n m` or
`emp n m : False → empty_relation n m`.
So, I do think that it is solvable given what students know.
:::

```lean
inductive EmptyRelation : Nat → Nat → Prop where
  -- SOLUTION
  -- END SOLUTION
```

```lean
theorem empty_relation_is_empty (n m : Nat) : ¬ EmptyRelation n m := by
  solution!
    intro contra; inversion contra
```
:::::

:::dev PotentialImprovement
A nice exercise...
  - give them a datatype of binary trees
  - ask them to write a "size" function
  - make them write an inductively defined "balanced" property
  - maybe prove something about this property (this might be hard)?

At some point, perhaps we can show them how propositions and data
can get mixed together.  E.g., we can define a type of lists of
numbers less than 10 (where each element carries a proof that it
is less than 10).  Then we can go a step further and parameterize
this definition over 10.  Similarly, we can define balanced binary
trees of height exactly n. (See CoqArt p. 181.)  Show and discuss
the induction principles for all of these.
:::
::::::

# Additional Exercises

:::instructors
The exercises build on `Le`, which is defined in this file,
as well as `List.allb` and `List.filter`, which are defined in Logic.
Other operations, such as `List.length`, `List.append`, `List.reverse`, and `Mem`
are provided by Lean's core library.
:::

:::suppressPreviousHeaderWhenTerse
:::

::::::full
:::::exercise (rating := 3) (name := "nostutter_defn") (manual := true)
Formulating inductive definitions of properties is an important
skill you'll need in this course.  Try to solve this exercise
without any help.

We say that a list "stutters" if it repeats the same element
consecutively.  (This is different from not containing duplicates:
the sequence {lean}`[1, 4, 1]` has two occurrences of the element {lean}`1` but
does not stutter.)  The property `NoStutter l` means that `l` does
not stutter. Formulate an inductive definition for `NoStutter`.

```lean
inductive NoStutter {α : Type} : List α → Prop where
 -- SOLUTION
  | nil : NoStutter []
  | singleton {x : α} : NoStutter (x :: [])
  | cons {x y : α} {l : List α}
      (hneq : x ≠ y) (h : NoStutter (y :: l)) :
      NoStutter (x :: y :: l)
 -- END SOLUTION
```

Make sure each of these tests succeeds, but feel free to change
the suggested proof (in comments) if the given one doesn't work
for you.  Your definition might be different from ours and still
be correct, in which case the examples might need a different
proof.  (You'll notice that the suggested proofs use a number of
tactics we haven't talked about, to make them more robust to
different possible ways of defining {name}`NoStutter`.  You can probably
just uncomment and use them as-is, but you can also prove each
example with more basic tactics.)

```lean
example : NoStutter [3, 1, 4, 1, 5, 6] := by
  suggested!
    constructor; intro contra; contradiction
    constructor; intro contra; contradiction
    constructor; intro contra; contradiction
    constructor; intro contra; contradiction
    constructor; intro contra; contradiction
    constructor

example : NoStutter (@List.nil Nat) := by
  suggested!
    constructor

example :  NoStutter [5] := by
  suggested!
    constructor
```

```lean
example : ¬ (NoStutter [3, 1, 1, 4]) := by
  suggested!
    intro contra
    inversion contra with
    | cons contra =>
      inversion contra with
      | cons _ h _ => contradiction
```

:::grade
`GRADE_MANUAL 3: nostutter`
:::
:::::


:::dev "Yipeng Liu (berberman)" PotentialImprovement
The proofs in the following exercises are a bit awkward to me,
because they require some "internal" `Bool` lemmas in core Lean to simplify the hypotheses.
People would normally run `simp` tactic to access them.
:::

:::::exercise (rating := 4) (name := "filter_challenge") (level := Advanced)
Let's prove that our definition of {name}`filter` from the {ref "Poly"}[Poly]
chapter matches an abstract specification.  Here is the
specification, written out informally in English:

A list `l` is an "in-order merge" of `l₁` and `l₂` if it contains
all the same elements as `l₁` and `l₂`, in the same order as `l₁`
and `l₂`, but possibly interleaved.  For example,

```display
[1, 4, 6, 2, 3]
```

is an in-order merge of

```display
[1, 6, 2]
```

and

```display
[4, 3].
```

Now, suppose we have a type `α`, a function `test : α → Bool`, and a
list `l` of type `List α`.  Suppose further that `l` is an
in-order merge of two lists, `l₁` and `l₂`, such that every item
in `l₁` satisfies `test` and no item in `l₂` satisfies test.  Then
`filter test l = l₁`.

First define what it means for one list to be a merge of two
others.  Do this with an `inductive` relation, not a `def`.

```lean
inductive Merge {α : Type} : List α → List α → List α → Prop where
-- SOLUTION
  | nil : Merge [] [] []
  | left {x : α} {l₁ l₂ l₃ : List α}
      (h : Merge l₁ l₂ l₃) :
      Merge (x :: l₁) l₂ (x :: l₃)
  | right {x : α} {l₁ l₂ l₃ : List α}
      (h : Merge l₁ l₂ l₃) :
      Merge l₁ (x :: l₂) (x :: l₃)
-- END SOLUTION

theorem merge_filter (α : Type) (test : α → Bool) (l l₁ l₂ : List α)
  (h : Merge l₁ l₂ l)
  (h₁ : l₁.allb test)
  (h₂ : l₂.allb (fun x => !test x)) :
  filter test l = l₁ := by
  solution!
    induction h with
    | nil => rfl
    | left h' ih =>
      rw [List.allb_cons, Bool.and_eq_true] at h₁
      obtain ⟨htest, h₁⟩ := h₁
      rw [filter_cons_of_pos htest]
      congr 1; apply ih
      · assumption
      · assumption
    | right h' ih =>
      rw [List.allb_cons, Bool.and_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true] at h₂
      obtain ⟨htest, h₂⟩ := h₂
      rw [filter_cons_of_neg htest]
      congr 1; apply ih
      · assumption
      · assumption
```

:::autogradedHole Merge
:::


:::gradeTheorem 6 merge_filter
:::
:::::

:::::exercise (rating := 5) (name := "filter_challenge_2") (level := Advanced) (optional := true)
A different way to characterize the behavior of {name}`filter` goes like
this: Among all subsequences of `l` with the property that `test`
evaluates to `true` on all their members, `filter test l` is the
longest. Formalize this claim and prove it.

:::solution

```lean
namespace FilterChallenge

open LePlayground

/- Here's a polymorphic version of `Subseq` we've seen above. -/
inductive Subseq {α : Type} : List α → List α → Prop where
  | nil {l : List α} : Subseq [] l
  | take {x : α} {l₁ l₂ : List α}
      (h : Subseq l₁ l₂) :
      Subseq (x :: l₁) (x :: l₂)
  | skip {x : α} {l₁ l₂ : List α}
      (h : Subseq l₁ l₂) :
      Subseq l₁ (x :: l₂)

/- A few lemmas about subseq. -/
namespace Subseq

theorem drop_l {α : Type} {x : α} {l₁ l₂ : List α}
    (h : Subseq (x :: l₁) l₂) : Subseq l₁ l₂ := by
  induction l₂ generalizing l₁ with
  | nil => inversion h
  | cons _ _ ih =>
    inversion h with
    | take hs =>
      constructor; assumption
    | skip hs =>
      constructor; apply ih; assumption

theorem drop {α : Type} {x : α} {l₁ l₂ : List α}
    (h : Subseq (x :: l₁) (x :: l₂)) : Subseq l₁ l₂ := by
  inversion h with
  | take => assumption
  | skip => apply drop_l; assumption

end Subseq

/-- A list is _maximal_ with property `P` if it has the property, and
    every other list with the property is at most as long as it is. -/
def Maximal {α : Type} (maxList : List α) (P : List α → Prop) : Prop :=
  P maxList ∧ ∀ (l : List α), P l → l.length ≤ maxList.length

/-- A "good subsequence" for a given list `l` and a `test` is a
    subsequence of `l` all of whose members evaluate to `true` under
    the `test`. -/
def GoodSubseq {α : Type} (test : α → Bool) (l lsub : List α) :=
  Subseq lsub l ∧ lsub.allb test

/-- Good subsequences can be extended with good elements. -/
theorem GoodSubseq.extend {α : Type} {x : α}
    {l lsub : List α} {test : α → Bool} (hx : test x = true)
    (h : GoodSubseq test l lsub) :
    GoodSubseq test (x :: l) (x :: lsub) := by
  obtain ⟨hsub, hall⟩ := h
  constructor
  · constructor; assumption
  · rw [List.allb_cons, Bool.and_eq_true]
    constructor
    · assumption
    · assumption

/-- If `maxList` is a maximal good subsequence of `x :: l` and `x` is not good,
    then `maxList` is also a maximal good subsequence of `l`. -/
theorem maximal_strengthening {α : Type} {x : α}
    {maxList l : List α} {test : α → Bool} (hx : test x = false)
    (h : Maximal maxList (GoodSubseq test (x :: l))) :
    Maximal maxList (GoodSubseq test l) := by
  obtain ⟨⟨hsub, hall⟩, hlen⟩ := h
  constructor
  constructor
  · inversion hsub with
    | nil => constructor
    | take l₁ hsub =>
      rw [List.allb_cons, Bool.and_eq_true] at hall
      obtain ⟨ht, _⟩ := hall
      rw [hx] at ht; contradiction
    | skip => assumption
  · assumption
  · intro l ⟨hsub', hall'⟩; apply hlen; constructor
    · constructor; assumption
    · assumption

/- Some easy lemmas about filter: its result is a good subsequence of
    the original list. -/

theorem filter_subseq {α : Type} (l : List α) (test : α → Bool) :
    Subseq (filter test l) l := by
  induction l with
  | nil => rw [filter_nil]; constructor
  | cons x xs ih =>
    cases h : (test x)
    · rw [filter_cons_of_neg h]
      constructor; assumption
    · rw [filter_cons_of_pos h]
      constructor; assumption

theorem filter_all {α : Type} (l : List α) (test : α → Bool) :
    (filter test l).allb test := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases h : (test x)
    · rw [filter_cons_of_neg h]; assumption
    · rw [filter_cons_of_pos h, List.allb_cons, Bool.and_eq_true]
      constructor
      · assumption
      · assumption

/- And now for the main theorem: `lsub` is a maximal good subsequence
    of `l` if and only if `filter test l = lsub` -/
theorem filter_spec2 {α : Type} (l lsub : List α) (test : α → Bool) :
    Maximal lsub (GoodSubseq test l) ↔ filter test l = lsub := by
  constructor
  · induction l generalizing lsub with
    | nil =>
      intro ⟨⟨hsub, hall⟩, hlen⟩
      inversion hsub
      rw [filter_nil]
    | cons x xs ih =>
      cases htest : test x with
      | false =>
        rw [filter_cons_of_neg htest]
        · intro hmax; apply ih
          apply maximal_strengthening htest hmax
      | true =>
        intro ⟨⟨hsub, hall⟩, hlen⟩
        /- in this case, `lsub` must begin with `x`, since otherwise it
        wouldn't be maximal. -/
        cases lsub with
        | nil =>
          -- lsub = [] (impossible: contradicts maximality of lsub)
          have contra : [x].length ≤ ([] : List α).length := by
            apply hlen
            constructor
            · constructor; constructor
            · rw [List.allb_cons, List.allb_nil, Bool.and_true]
              assumption
          contradiction
        | cons x' xs' =>
          have heq : x = x' := by -- because of maximality again
            inversion hsub with
            | take hsub => rfl
            | skip hsub =>
              -- contradiction, since x :: x' :: xs' would be longer
              have contra : (x :: x' :: xs').length ≤ (x' :: xs').length := by
                apply hlen; constructor
                · constructor; assumption
                · rw [List.allb_cons, List.allb_cons, Bool.and_eq_true, Bool.and_eq_true]
                  rw [List.allb_cons, Bool.and_eq_true] at hall
                  constructor; assumption; assumption
              rw [List.length_cons, List.length_cons] at contra
              apply le_of_succ_le_succ at contra
              apply le_not_succ_le_self at contra
              contradiction
          subst heq; rw [filter_cons_of_pos htest]
          congr; apply ih; constructor; constructor
          · exact hsub.drop
          · rw [List.allb_cons, Bool.and_eq_true] at hall
            obtain ⟨_, _⟩ := hall; assumption
          · intro l' hgood
            rw [List.length_cons] at hlen
            apply le_of_succ_le_succ
            apply hlen (x :: l')
            exact hgood.extend htest
  · intro hfilter
    constructor; rw [← hfilter]
    constructor
    · apply filter_subseq
    · apply filter_all
    · intro l' ⟨hsub, hall⟩
      induction l generalizing l' lsub with
      | nil =>
        inversion hsub; rw [List.length_nil]
        apply zero_le
      | cons x xs ih =>
        cases htest : test x with
        | false =>
          rw [filter_cons_of_neg htest] at hfilter
          · apply ih _ hfilter _ _ hall
            inversion hsub with
            | nil => constructor
            | take l hsub =>
              rw [List.allb_cons, Bool.and_eq_true] at hall
              obtain ⟨ht, _⟩ := hall
              rw [ht] at htest
              contradiction
            | skip hsub => assumption
        | true =>
          rw [filter_cons_of_pos htest] at hfilter
          rw [← hfilter, List.length_cons]
          inversion hsub with
          | nil => rw [List.length_nil]; apply zero_le
          | take l hsub =>
            rw [List.length_cons]
            apply succ_le_succ
            apply ih _ rfl _ hsub
            rw [List.allb_cons, Bool.and_eq_true] at hall
            obtain ⟨_, h⟩ := hall
            exact h
          | skip hsub =>
            apply Le.step
            exact ih _ rfl _ hsub hall

end FilterChallenge
```
:::
:::::

:::::exercise (rating := 4) (name := "palindromes") (optional := true)
A palindrome is a sequence that reads the same backwards as
forwards.

- Define an inductive proposition `Pal` on `List α` that
  captures what it means to be a palindrome. (Hint: You'll need
  three cases.)

- Prove `pal_append_reverse`, which states that

```display
∀ l, Pal (l ++ l.reverse).
```

- Prove `pal_reverse`, which states that

```display
∀ l, Pal l → l = l.reverse.
```

For extra credit, try proving the same theorems with an alternate
definition with a _single_ constructor of this type:

```display
∀ l, l = l.reverse → Pal l
```

```lean
inductive Pal {α : Type} : List α → Prop where
-- SOLUTION
  | nil : Pal []
  | singleton {x : α} : Pal [x]
  | cons_snoc {x : α} {l : List α} (h : Pal l) : Pal (x :: (l ++ [x]))
-- END SOLUTION
```

```lean
example : Pal ([] : List Nat) := by
  suggested!
    constructor

example : Pal [1] := by
  suggested!
    constructor

example : Pal [1, 2, 1] := by
  suggested!
    apply Pal.cons_snoc (l := [2])
    constructor

example : Pal [1, 2, 3, 2, 1] := by
  suggested!
    apply Pal.cons_snoc (l := [2, 3, 2])
    apply Pal.cons_snoc (l := [3])
    constructor
```

```lean
theorem pal_append_reverse (α : Type) (l : List α) :
    Pal (l ++ l.reverse) := by
  solution!
    induction l with
    | nil => rw [List.reverse_nil, List.append_nil]; constructor
    | cons x xs ih =>
      rw [List.reverse_cons, List.cons_append, ← List.append_assoc]
      constructor; assumption
```

:::dev PotentialImprovement
Note that we're using some standard library stuff here...
We should at least explicitly qualify them...
:::

```lean
theorem pal_reverse {α : Type} {l : List α} (hp : Pal l) : l = l.reverse := by
  solution!
    induction hp with
    | nil => rw [List.reverse_nil]
    | singleton =>
      rw [List.reverse_cons, List.reverse_nil, List.nil_append]
    | cons_snoc h ih =>
      rw [List.reverse_cons, List.reverse_append, ← List.cons_append, ← ih]
      congr
```

:::::

:::::exercise (rating := 4) (name := "NoDup") (level := Advanced) (optional := true) (manual := true)
Use the `∈` property to define a proposition `Disjoint l₁ l₂`,
which should be provable exactly when `l₁` and `l₂` are
lists (with elements of type `α`) that have no elements in
common.

```lean
def Disjoint {α : Type} (l₁ l₂ : List α) : Prop :=
  solution!(∀ {x : α}, x ∈ l₁ → ¬ x ∈ l₂)
```

Next, use `∈` to define an inductive proposition `NoDup l`,
which should be provable exactly when `l` is a list (with
elements of type `α`) where every member is different from every
other.  For example, `NoDup ([1, 2, 3, 4] : List Nat)` and
`NoDup ([] : List Bool)` should be provable, while
`NoDup ([1, 2, 1] : List Nat)` and
`NoDup ([true, true] : List Bool)` should not be.

```lean
inductive NoDup {α : Type} : List α → Prop where
-- SOLUTION
  | nil : NoDup []
  | cons {x : α} {l : List α}
    (hnin : ¬ x ∈ l) (h : NoDup l) : NoDup (x :: l)
-- END SOLUTION
```

Finally, state and prove one or more interesting theorems relating
`Disjoint`, `NoDup` and `++` (list append).

:::solution

Here are some possible answers:

```lean

theorem NoDup.append {α : Type} {l₁ l₂: List α}
    (h₁ : NoDup l₁) (h₂ : NoDup l₂) (hdis : Disjoint l₁ l₂) :
    NoDup (l₁ ++ l₂) := by
  induction l₁ generalizing l₂ with
  | nil => rw [List.nil_append]; assumption
  | cons x xs ih =>
    constructor
    · intro contra
      rw [List.append_eq, List.mem_append] at contra
      cases contra with
      | inl =>
        inversion h₁ with
        | _ hdup hin => apply hin; assumption
      | inr contra =>
        apply hdis _ contra
        rw [List.mem_cons]; left; rfl
    · apply ih _ h₂ _
      · inversion h₁; assumption
      · intros x hin
        apply hdis; rw [List.mem_cons]
        right; assumption

theorem NoDup.isDisjoint {α : Type} {l₁ l₂: List α}
    (h : NoDup (l₁ ++ l₂)) : Disjoint l₁ l₂ := by
  intro x hin contra
  induction l₁ generalizing l₂ x with
  | nil => rw [List.mem_nil_iff] at hin; contradiction
  | cons x xs ih =>
    rw [List.mem_cons] at hin
    inversion h with
    | cons hdup hnin =>
      cases hin with
      | inl hin =>
        subst hin; apply hnin
        rw [List.append_eq, List.mem_append]; right; assumption
      | inr hin => exact ih hdup hin contra

/- We can also show the following results about `NoDup` and `++`
   by themselves -/
theorem NoDup.left {α : Type} {l₁ l₂: List α}
    (hdup : NoDup (l₁ ++ l₂)) : NoDup l₁ := by
  induction l₁ generalizing l₂ with
  | nil => constructor
  | cons x xs ih =>
    inversion hdup with
    | cons hdup' hin =>
      constructor
      · intro contra; apply hin
        rw [List.append_eq, List.mem_append]; left; assumption
      · exact ih hdup'

theorem NoDup.right {α : Type} {l₁ l₂ : List α}
    (h : NoDup (l₁ ++ l₂)) : NoDup l₂ := by
  induction l₁ generalizing l₂ with
  | nil => rw [List.nil_append] at h; assumption
  | cons x xs ih =>
    inversion h
    apply ih; assumption

/- This theorem combines the various lemmas to give a complete
   characterization -/
theorem NoDup.disjoint_app {α : Type} {l₁ l₂ : List α} :
    NoDup (l₁ ++ l₂) ↔
    (NoDup l₁ ∧ NoDup l₂ ∧ Disjoint l₁ l₂) := by
  constructor
  · intro hdup
    constructor; exact left hdup
    constructor; exact right hdup
    exact isDisjoint hdup
  · intro ⟨h₁, ⟨h₂, h₃⟩⟩
    exact append h₁ h₂ h₃
```

:::

:::grade
```
GRADE_MANUAL 6: NoDup
```
:::

:::::

:::::exercise (rating := 5) (name := "pigeonhole_principle") (level := Advanced) (optional := true)
The _pigeonhole principle_ states a basic fact about counting: if
we distribute more than `n` items into `n` pigeonholes, some
pigeonhole must contain at least two items.  As often happens, this
apparently trivial fact about numbers requires non-trivial
machinery to prove, but we now have enough...

First prove an easy and useful lemma.

```lean
theorem List.mem_split {α : Type} {x : α} {l : List α} (hin : x ∈ l) :
    ∃ l₁ l₂, l = l₁ ++ x :: l₂ := by
  solution!
    -- The exact lemma is called `List.append_of_mem` in Lean's core library
    induction l generalizing x with
    | nil => rw [List.mem_nil_iff] at hin; contradiction
    | cons x' xs' ih =>
      rw [List.mem_cons] at hin
      cases hin with
      | inl hin =>
        subst hin
        exists []
        exists xs'
      | inr hin =>
        have ⟨l₁', ⟨l₂', ih⟩⟩ := ih hin
        subst ih
        exists x' :: l₁'
        exists l₂'
```

Now define a property `Repeats` such that `Repeats l` asserts
that `l` contains at least one repeated element.

```lean
inductive Repeats {α : Type} : List α → Prop where
  -- SOLUTION
  | head {x : α} {l : List α} (h : x ∈ l)     : Repeats (x :: l)
  | tail {x : α} {l : List α} (h : Repeats l) : Repeats (x :: l)
-- /SOLUTION
```


:::grade
```
GRADE_MANUAL 2: Repeats
```
:::

Now, here's a way to formalize the pigeonhole principle.  Suppose
list `l₂` represents a list of pigeonhole labels, and list `l₁`
represents the labels assigned to a list of items.  If there are
more items than labels, at least two items must have the same
label -- i.e., list `l₁` must contain repeats.

This proof is much easier if you use the excluded middle
to show that `∈` is decidable, i.e., `∀ x l, (x ∈ l) ∨ ¬ (x ∈ l)`.
Remember the `by_cases` tactic from {ref "Logic"}[Logic]!

:::dev
HIDE: APT21: Apparently, this is really quite hard; even the strongest
students couldn't do it this year.
:::

:::dev "Yipeng Liu (berberman)"
I reworked the proof and felt the list membership reasoning is too distracting.
Maybe move to the Automation chapter for `simp`.
:::

```lean

open LePlayground in

theorem pigeonhole_principle {α : Type} {l₁ l₂ : List α}
    (hin : ∀ x, x ∈ l₁ → x ∈ l₂)
    (hlen : l₂.length < l₁.length) :
    Repeats l₁ := by
  solution!
    induction l₁ generalizing l₂ with
    | nil =>
      rw [List.length_nil] at hlen
      apply lt_not_lt_zero at hlen
      contradiction
    | cons x xs ih =>
      by_cases h : x ∈ xs
      · exact Repeats.head h
      · apply Repeats.tail
        have h₂ : x ∈ l₂ := by
          apply hin; rw [List.mem_cons]; left; rfl
        obtain ⟨l₂a, l₂b, rfl⟩ := List.mem_split h₂
        have hin₂ : ∀ y, y ∈ xs → y ∈ l₂a ++ l₂b := by
          intro y hy
          have hy₂ : y ∈ l₂a ++ x :: l₂b := by
            apply hin
            rw [List.mem_cons]
            right
            exact hy
          rw [List.mem_append] at hy₂
          obtain hya | hy₂ := hy₂
          · rw [List.mem_append]
            left
            exact hya
          · rw [List.mem_cons] at hy₂
            obtain rfl | hyb := hy₂
            · contradiction
            · rw [List.mem_append]
              right
              exact hyb
        have hlen₂ : (l₂a ++ l₂b).length < xs.length := by
          rw [List.length_append, List.length_cons,
              List.length_cons, ← Nat.add_assoc] at hlen
          rw [List.length_append]
          apply le_of_succ_le_succ
          exact hlen
        apply ih hin₂ hlen₂
```

:::dev PotentialImprovement
```
A student came up with

Definition repeats {α} (xs: List α) : Prop :=
  exists x ps qs rs,  xs = ps ++ [x] ++ qs ++ [x] ++ rs.
Should check to see how much harder this makes things.
```
:::
:::::

:::solution
```
/- Here's a clever alternative proof, based heavily on one by Daniel
    Schepler (<dschepler@gmail.com> Coq club mailing list on Wed, 02 Oct
    2013 02:02:12 -0700), that doesn't use decidability of [In], and hence
    doesn't need [excluded_middle]. -/

/- First, some more auxiliary lemmas, some of which are a bit ad hoc. -/

theorem in_repeats: forall {α:Type} (l₁ l₂:List α) (x:α),
  In x (l₁++l₂) →
  repeats (l₁++x::l₂).
Proof.
  intros α l₁. induction l₁ as [|y l1' IHl1'].
  - /- l₁ = [] -/
    intros l₂ x AI. simpl in AI. simpl. apply rep_here. apply AI.
  - /- l₁ = y::l1' -/
    intros l₂ x AI. simpl in AI. simpl. destruct AI as [AI | AI].
    + apply rep_here. apply In_app_iff. right. left.
      rewrite AI. reflexivity.
    + apply rep_later. apply IHl1'. apply AI.
Qed.

theorem rep_insert: forall {α:Type} (l₁ l₂:List α) (x: α),
  repeats (l₁ ++ l₂) → repeats (l₁ ++ x::l₂).
Proof.
  intros α l₁. induction l₁ as [| y l1' IHl1'].
  - /- l₁ = [] -/
    intros l₂ x H. simpl. simpl in H. apply rep_later.  apply H.
  - /- l₁ = y::l1' -/
    intros l₂ x H. simpl. simpl in H. inversion H.
    + /- rep_here -/
      apply rep_here. apply In_app_iff. apply In_app_iff in h₁.
      destruct h₁ as [h₁ | h₁].
      * left. apply h₁.
      * right. right. apply h₁.
    + /- rep_later -/
      apply rep_later. apply IHl1'. apply h₁.
Qed.

theorem repeats_app_comm : forall {α:Type} (l₁ l₂:List α),
  repeats (l₁++l₂) → repeats(l₂++l₁).
Proof.
  intros α l₁. induction l₁ as [|x l1'].
  - /- l₁ = [] -/
    intros l₂ H.  rewrite app_nil_r. simpl in H. apply H.
  - /- l₁ = x::l1' -/
    intros l₂ H. simpl in H. inversion H.
    + /- rep_here -/
      apply in_repeats. apply In_app_iff.
      apply In_app_iff in h₁.
      destruct h₁ as [h₁ | h₁].
      * right. apply h₁.
      * left. apply h₁.
    + /- rep_later -/
      apply IHl1' in h₁. apply rep_insert. apply h₁.
Qed.

/- Now the main lemma: -/

theorem pigeonhole_principle_aux: forall {α:Type} (l₁ l₂ ls: List α),
  (forall x:α, In x l₁ → In x (ls++l₂)) →
  length l₂ < length l₁ → repeats (ls++l₁).
Proof.
  intros α l₁. induction l₁ as [|x l1' IHl1'].
  - /- l₁ = [] -/
    intros l₂ ls AI LT. inversion LT.
  - /- l₁ = x::l1' -/
    intros l₂ ls AI LT.
    assert (In x (ls++l₂)).
    { /- Proof of assertion -/
      apply AI. left. reflexivity. }
    assert (In x ls \/ In x l₂).
    { /- Proof of assertion -/
      apply In_app_iff. apply H. }
    destruct H0.
    + /- In x ls -/
      apply repeats_app_comm. simpl. apply rep_here.
      apply In_app_iff. right. apply H0.
    + /- In x l₂ -/
      apply in_split in H0.
      destruct H0 as [l2a [l2b P]]. rewrite P in *.
      assert (repeats ((x::ls) ++ l1')).
      * /- Proof of assertion -/
        apply (IHl1' (l2a++l2b) (x::ls)).
        { /- re-establish inclusion relation -/
          intros x0 AI'.
          assert (In x0 (ls ++ l2a ++ x::l2b)).
          { /- Proof of assertion -/
            apply AI. right. apply AI'. }
          apply In_app_iff in H0. inversion H0.
            apply In_app_iff.  left. right. apply h₁.
            apply In_app_iff in h₁. inversion h₁.
              apply In_app_iff. right.
                apply In_app_iff. left. apply h₂.
              inversion h₂.
                simpl. left. apply h₃.
                apply In_app_iff. right.
                  apply In_app_iff. right. apply h₃. }
        rewrite app_length in LT.  rewrite app_length.
        simpl in LT. rewrite <- plus_n_Sm in LT.
        unfold lt. unfold lt in LT. apply le_S_n. apply LT.
      * simpl in H0. apply repeats_app_comm. simpl. inversion H0.
        { apply rep_here. apply In_app_iff.
          apply In_app_iff in h₂. inversion h₂.
          - right. apply H4.
          - left. apply H4. }
        apply rep_later. apply repeats_app_comm. apply h₂.
Qed.

theorem stronger_pigeonhole_principle: forall {α:Type} (l₁ l₂ : List α),
  (forall x : α, In x l₁ → In x l₂) →
  length l₂ < length l₁ →
  repeats l₁.
Proof.
  intros α l₁ l₂ AI LT.
  assert (H: l₁ = nil ++ l₁). { reflexivity. }
  rewrite H. apply (pigeonhole_principle_aux l₁ l₂ nil).
  simpl. apply AI. apply LT.
Qed.

/- One key to how this proof works is that at the inductive step,
    when we re-establish the inclusion relation, the contents on the
    list on the right-hand side of the inclusion have not changed at
    all---they are merely re-arranged, so validity of the inclusion is
    trivial (modulo some messy book-keeping). Compare this to the
    equivalent step in the original proof, where we remove [x] from the
    list on the right-hand side of the inclusion; this is only valid when
    we know that [x] is not in the left-hand list [l1'] either---exactly
    the knowledge that we get from decidability of [In], and cannot get
    any other way. -/

/- ------------------------ -/

/- Finally, here is a much more elegant proof due to N. Raghavendra
    <raghu@hri.res.in>, based on Daniel's.  It uses the following
    sequence of observations:

      theorem app_ass :
      forall (α : Type) (l₁ l₂ l₃ : List α),
        (l₁ ++ l₂) ++ l₃ = l₁ ++ l₂ ++ l₃.

      theorem app_length :
      forall (α : Type) (l₁ l₂ : List α),
        length (l₁ ++ l₂) = length l₁ + length l₂.

      theorem In_app_iff_split :
      forall (α : Type) (x : α) (l : List α),
        In x l →
        exists (l₁ l₂ : List α), l = l₁ ++ x :: l₂.

      theorem In_both_impl_repeats_app :
      forall (α : Type) (x : α) (l₁ l₂ : List α),
        In x l₁ → In x l₂ → repeats (l₁ ++ l₂).

      theorem In_app_iff_midswap :
      forall (α : Type) (x : α) (l₁ l₂ l₃ l4 : List α),
        In x (l₁ ++ l₂ ++ l₃ ++ l4) →
        In x (l₁ ++ l₃ ++ l₂ ++ l4).

      theorem pigeonhole_principle_aux :
      forall (α : Type) (l₁ l₂ u : List α),
        (forall x : α, In x l₁ → In x (u ++ l₂)) →
        length l₂ < length l₁ → repeats (u ++ l₁).

      theorem pigeonhole_principle :
      forall (α : Type) (l₁ l₂ : List α),
        (forall x : α, In x l₁ → In x l₂) →
        length l₂ < length l₁ → repeats l₁.
-/

/- HIDE: Some of these are already proved elsewhere. Also, this
  vertical style is hard to read. -/

Module Pigeon.

inductive repeats {α : Type} : List α → Prop :=
  | repeats_1 (x : α) (l : List α)
              (H : In x l) : repeats (x :: l)
  | repeats_2 (x : α) (l : List α)
              (H : repeats l) : repeats (x :: l).

Definition pigeonhole_principle_prop (α : Type) : Prop :=
  forall l₁ l₂ : List α,
    (forall x : α, In x l₁ → In x l₂) →
    length l₂ < length l₁ → repeats l₁.

theorem app_ass :
  forall (α : Type) (l₁ l₂ l₃ : List α),
    (l₁ ++ l₂) ++ l₃ = l₁ ++ l₂ ++ l₃.

Proof.
  intros α l₁ l₂ l₃.
  induction l₁ as [ | h t IH].
  {
    - /- l₁ = nil -/
    reflexivity.
  }
  {
    - /- l₁ = h :: t -/
    simpl.
    rewrite → IH.
    reflexivity.
  }
Qed.

theorem app_length :
  forall (α : Type) (l₁ l₂ : List α),
    length (l₁ ++ l₂) = length l₁ + length l₂.

Proof.
  intros α l₁ l₂.
  induction l₁ as [ | h t IH].
  {
    - /- l₁ = nil -/
    reflexivity.
  }
  {
    - /- l₁ = h :: t -/
    simpl.
    rewrite → IH.
    reflexivity.
  }
Qed.

theorem In_both_impl_repeats_app :
  forall (α : Type) (x : α) (l₁ l₂ : List α),
    In x l₁ → In x l₂ → repeats (l₁ ++ l₂).

Proof.
  intros α x l₁.
  induction l₁ as [ | h₁ t1 IH].
  {
    - /- l₁ = nil -/
    intros l₂ h₁ h₂.
    inversion h₁.
  }
  {
    - /- l₁ = h₁ :: t1 -/
    intros l₂ h₁ h₂. simpl in h₁.
    destruct h₁ as [h₃ | h₃].
    {
      +
      simpl.
      apply repeats_1.
      apply In_app_iff.
      right.
      rewrite h₃.
      apply h₂.
    }
    {
      + /- h₁ = ai_later z u h₃ -/
      simpl.
      apply repeats_2.
      apply IH.
      {
        apply h₃.
      }
      {
        apply h₂.
      }
    }
  }
Qed.

theorem In_app_iff_midswap :
  forall (α : Type) (x : α) (l₁ l₂ l₃ l4 : List α),
    In x (l₁ ++ l₂ ++ l₃ ++ l4) → In x (l₁ ++ l₃ ++ l₂ ++ l4).

Proof.
  intros α x l₁ l₂ l₃ l4 H.
  apply In_app_iff in H.
  destruct H as [h₁ | h₁r].
  {
    - /- In x l₁ -/
    apply In_app_iff.
    left.
    apply h₁.
  }
  {
    - /- In x (l₂ ++ l₃ ++ l4) -/
    apply In_app_iff in h₁r.
    destruct h₁r as [h₂ | h₂r].
    {
      + /- In x l₁ -/
      apply In_app_iff.
      right.
      apply In_app_iff.
      right.
      apply In_app_iff.
      left.
      apply h₂.
    }
    {
      + /- In x (l₃ ++ l4) -/
      apply In_app_iff in h₂r.
      destruct h₂r as [h₃ | h₃r].
      {
        * /- In x l₃ -/
        apply In_app_iff.
        right.
        apply In_app_iff.
        left.
        apply h₃.
      }
      {
        * /- In x l4 -/
        apply In_app_iff.
        right.
        apply In_app_iff.
        right.
        apply In_app_iff.
        right.
        apply h₃r.
      }
    }
  }
Qed.

theorem pigeonhole_principle_aux :
  forall (α : Type) (l₁ l₂ u : List α),
    (forall x : α, In x l₁ → In x (u ++ l₂)) →
    length l₂ < length l₁ → repeats (u ++ l₁).

Proof.
  intros α l₁.
  induction l₁ as [ | h₁ t1 IH].
  {
    - /- l₁ = nil -/
    intros l₂ u h₁ h₂.
    inversion h₂.
  }
  {
    - /- l₁ = h₁ :: t1 -/
    intros l₂ u h₁ h₂.
    assert (h₃ : In h₁ (u ++ l₂)).
    {
      + /- Proof of h₃ -/
      apply h₁.
      left. reflexivity.
    }
    apply In_app_iff in h₃.
    destruct h₃ as [h₃l | h₃r].
    {
      + /- In h₁ u -/
      apply (In_both_impl_repeats_app _ h₁).
      {
        apply h₃l.
      }
      {
        left. reflexivity.
      }
    }
    {
      + /- In h₁ l₂ -/
      apply in_split in h₃r.
      destruct h₃r as [v2 H4].
      destruct H4 as [w2 H5].
      assert (H6 : u ++ h₁ :: t1 = (u ++ [h₁]) ++ t1).
      {
        * /- Proof of H6 -/
        rewrite → app_ass.
        reflexivity.
      }
      rewrite → H6.
      apply (IH (v2 ++ w2)).
      {
        * /- Proof of first condition of IH -/
        intros x H7.
        rewrite → app_ass.
        apply In_app_iff_midswap.
        simpl.
        rewrite <- H5.
        apply h₁.
        right.
        apply H7.
      }
      {
        * /- Proof of second condition of IH -/
        unfold lt.
        assert (H8 : length l₂ = S (length (v2 ++ w2))).
        {
          rewrite → H5.
          rewrite → app_length.
          rewrite → app_length.
          simpl.
          rewrite <- plus_n_Sm.
          reflexivity.
        }
        rewrite <- H8.
        apply Sn_le_Sm__n_le_m.
        unfold lt in h₂.
        simpl in h₂.
        apply h₂.
      }
    }
  }
Qed.

theorem pigeonhole_principle :
  forall α : Type,
    pigeonhole_principle_prop α.

Proof.
  intros α.
  unfold pigeonhole_principle_prop.
  intros l₁ l₂ h₁ h₂.
  assert (H: l₁ = nil ++ l₁). { reflexivity. }
  rewrite H.
  apply (pigeonhole_principle_aux _ _ l₂).
  {
    intros x h₃.
    simpl.
    apply h₁.
    apply h₃.
  }
  {
    apply h₂.
  }
Qed.

End Pigeon.
```
:::
::::::
