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
:::::exercise (rating := 1) (name := "EquivGen") (optional := true) (manual := true)
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
theorem Even.even_inversion (n : Nat) (h : Even n) :
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

theorem le_inversion (n m : Nat) (h : Le n m) :
    (n = m) ∨ (∃ m', m = m' + 1 ∧ Le n m') := by
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
theorem Even.succ_succ_even (n : Nat) (h : Even (n + 2)) : Even n := by
  apply even_inversion at h
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
  intro h; apply Even.even_inversion at h
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
theorem Even.even_add_four {n : Nat} (h : Even (n + 4)) : Even n := by
  solution!
    inversion h with
    | succ_succ h' => apply succ_succ_even; exact h'
```

:::gradeTheorem 1 Even.even_add_four
:::

:::::

:::::exercise (rating := 1) (name := "ev5_nonsense")
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
  | succ_succ _ m' _ _ _ => right; exists m'
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

```lean +error
example (n : Nat) (h : Even n) : Nat.Even n := by
  /- We could try to proceed by case analysis or induction on `n`.  But
      since `Even` is mentioned in a premise, this strategy seems
      unpromising, because (as we've noted before) the induction
      hypothesis will talk about `n-1` (which is _not_ even!).  Thus, it
      seems better to first try `inversion` on the evidence for `Even`.
      Indeed, the first case can be solved trivially. -/
  inversion h with
  | zero => exists 0
  | succ_succ n' h' =>
    /- Unfortunately, the second case is harder.  We need to show
    `∃ n₀, n' + 2 = double n₀`, but the only available assumption is
    `h'`, which states that `Even n'` holds.
    In other words, what we need here is precisely the result we
    are trying to prove, but applied to the smaller evidence `h'`.
    -/
```

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
is of the form `Ev.ev_succ_succ n' h'`, where {lean}`n = n' + 2` and
`h'` is evidence for {lean}`Even n'`. In this case, the inductive hypothesis
says that the property we are trying to prove holds for {lean}`n'`.
::::

Let's try proving that lemma again:

```lean
theorem even_even (n : Nat) (h : Even n) : Nat.Even n := by
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
theorem even_even_iff (n : Nat) : Even n ↔ Nat.Even n := by
  apply Iff.intro
  . intro h; exact even_even _ h
  . intro ⟨k, hk⟩; rw [hk]; exact Even.double k
```

As we will see in later chapters, induction on evidence is a
recurring technique across many areas ─ in particular for
formalizing the semantics of programming languages.

The following exercises provide simpler examples of this
technique, to help you familiarize yourself with it.

:::::exercise (rating := 2) (name := "ev_sum")
```lean
theorem even_add (n m : Nat) (hₙ : Even n) (hₘ : Even m) : Even (n + m) := by
  solution!
    induction hₙ with
    | zero => rw [Nat.zero_add]; exact hₘ
    | succ_succ h' ih =>
      rw [Nat.add_comm, Nat.add_succ, Nat.add_succ, Nat.add_comm]
      apply Even.succ_succ; exact ih
```

:::gradeTheorem 2 even_add
:::
:::::

:::::exercise (rating := 3) (name := "ev_ev__ev") (level := Advanced)
```lean
theorem even_add_even (n m : Nat) (hₙₘ : Even (n + m)) (hₙ : Even n) : Even m := by
  /- Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. -/
  solution!
    induction hₙ generalizing m with
    | zero => rw [Nat.zero_add] at hₙₘ; exact hₙₘ
    | succ_succ h' ih =>
      rw [Nat.add_comm, Nat.add_succ, Nat.add_succ, Nat.add_comm] at hₙₘ
      inversion hₙₘ; apply ih; assumption
```

:::gradeTheorem 3 even_add_even
:::
:::::

:::::exercise (rating := 3) (name := "ev_plus_plus") (optional := true)
This exercise can be completed without induction or case analysis.
But, you will need a clever `have` and some tedious rewriting.
Hint: Is {lean}`(n + m) + (n + k)` even?

```lean
theorem ev_plus_plus (n m k : Nat)
    (hₙₘ : Even (n + m))
    (hₙₚ : Even (n + k)) :
    Even (m + k) := by
  solution!
    apply (even_add_even (n + n))
    . have h : n + n + (m + k) = n + m + (n + k) := by
        rw [Nat.add_assoc, Nat.add_assoc]
        congr 1
        exact Nat.add_left_comm _ _ _
      rw [h]
      apply even_add
      . assumption
      . assumption
    . rw [← Nat.double_add]; exact Even.double n
```

:::gradeTheorem 3 ev_plus_plus
:::
:::::

:::full
Another example of a proposition that can be characterized both recursively and
inductively is the {lean}`List.In` predicate we defined in the {ref "Logic"}[Logic] chapter.
As a reminder, the recursive definition we saw looked like this:
:::

:::terse
Recall the definition of `List.In` from last chapter:
:::

```lean
def In {α : Type} (x : α) (xs : List α) : Prop :=
  match xs with
  | [] => False
  | x' :: xs' => x = x' ∨ In x xs'
```

We can also write this definition inductively like so:

```lean
inductive In_Inductive {α : Type} (x : α) : List α → Prop
  | head {l : List α} : In_Inductive x (x :: l)
  | tail {y : α} {l : List α} (h : In_Inductive x l) : In_Inductive x (y :: l)
```

In fact, this is exactly how Lean defines this proposition,
which it calls {name}`Membership.mem` and which is written {lean}`x ∈ l`.
Its negation {lean}`¬ x ∈ l` is also written as {lean}`x ∉ l`.

A good exercise to test your understanding of induction on
evidence is to prove the equivalence of these definitions:

:::::exercise (rating := 2) (name := "in_mem")
```lean
theorem in_mem {α} (x : α) (l : List α) : List.In x l ↔ x ∈ l := by
  solution!
    constructor
    . intro h; induction l with
      | nil => apply List.In_nil at h; contradiction
      | cons hd tl ih =>
        rw [List.In_cons] at h
        obtain h | h := h
        . subst h; constructor
        . constructor; exact ih h
    . intro h; induction h with
      | head l' => rw [List.In_cons]; left; rfl
      | tail h ih => rw [List.In_cons]; right; assumption
```

:::gradeTheorem 3 in_mem
:::
:::::

The characterizing lemmas for `∈` are called
{name}`List.mem_nil_iff` and {name}`List.mem_cons`.
::::::

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
refines the identity relation ─ i.e., if `R x y` implies {lean}`x = y`.

:::dev
NDS 25: I originally wanted to do this with the empty
relation, defined inductively, but this requires introducing the
surprising behavior of unhabitated types, which I don't think have
been covered (yet?). Maybe they should be?
BCP 25: This one seems good.
:::

```lean
def Diagonal {α : Type} (R : α → α → Prop) := ∀ {x y}, R x y → x = y
```

Now consider the following lemma about diagonal relations:

```lean
theorem closure_of_diagonal_is_diagonal {α} (R : α → α → Prop)
    (hDiag : Diagonal R) :
    Diagonal (ReflTransGen R) := by
  intro x y h
  induction h with
  /- The two first cases go as you'd expect... -/
  | step hr =>
    rw [hDiag hr]
  | refl => rfl
  /- ...  but something interesting happens here: there are two
       induction hypotheses, `ih` and `ih'`! If you think about it, it
       is not that weird: we are in the case `rt_trans`, which has
       two recursive components, `hxy`, relating `x` to `y` and `hyz`,
       relating `y` to `z`. Hence we may want (and will actually need)
       an induction hypothesis for `hxy` and one for `hyz` ─ they are
       called `ihxy` and `ihyz` here. In general, Lean will always
       generate one induction hypothesis per recursive constructor of
       the type being inducted over. -/
  | trans _ _ ihxy ihyz => rw [ihxy, ihyz]
```

:::dev
HIDE: NDS comparing the previous proof to the pen-and-paper version
could be an idea to consider, as the way people tend to write it
on paper differs a bit from the mechanized proof.  BCP 25: Yes.
:::
::::

::::hide
```
    /- LATER: BCP 25: This bit feels potentially confusing and also not
      needed -- people that are paying attention enough to wonder about
      this will notice it when it happens later... -/
    /- Note that having multiple induction hypotheses is not
        specific to evidence: any constructor of any inductive type with
        more than one recursive component will yield as many induction
        hypotheses as it has recursive components. -/
    /- HIDE: NDS we may want to either 1) link to IndPrinciples for such
      examples or 2) add such an example here, even though it is kind of
      out of the topic. -/
```
::::

::::::full
:::::exercise (rating := 4) (name := "ev'_ev") (level := Advanced) (optional := true)
:::instructors
This is pretty hard, unless you know the trick that
the sample proof uses!!  But at least it's marked as
advanced and optional. :-)
:::

In general, there may be multiple ways of defining a
property inductively.  For example, here's a (slightly contrived)
alternative definition for `Ev`:

```lean
inductive Ev' : Nat → Prop where
  | ev'_0 : Ev' 0
  | ev'_2 : Ev' 2
  | ev'_sum {n m : Nat} (h₁ : Ev' n) (h₂ : Ev' m) : Ev' (n + m)
```

Prove that this definition is logically equivalent to the old one.
To streamline the proof, use the technique (from the {ref "Logic"}[Logic]
chapter) of applying theorems to arguments, and note that the same
technique works with constructors of inductively defined
propositions.

```lean
theorem ev'_ev n : Ev' n ↔ Even n := by
  solution!
    apply Iff.intro
    . /- → -/
      intro h; induction h
      . constructor
      . constructor; constructor
      . apply even_add; assumption; assumption
    . /- ← -/
      intro h; induction h with
      | zero => constructor
      | @succ_succ n _ _ =>
        rw [← Nat.add_zero n]
        constructor; assumption; constructor
```

:::gradeTheorem 4 ev'_ev
:::
:::::

We can do similar inductive proofs on the {name}`Perm3` relation,
which we defined earlier as follows:

```lean
namespace Perm3Reminder

inductive Perm3 {α : Type} : List α → List α → Prop where
  | perm3_swap12 {x y z : α} : Perm3 [x, y, z] [y, x, z]
  | perm3_swap23 {x y z : α} : Perm3 [x, y, z] [x, z, y]
  | perm3_trans {l₁ l₂ l₃ : List α}
    (h₁₂ : Perm3 l₁ l₂)
    (h₂₃ : Perm3 l₂ l₃) :
    Perm3 l₁ l₃

end Perm3Reminder

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
      . right; left; assumption
      . left; assumption
      . right; right; left; assumption
      . contradiction
    | swap23 =>
      rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
      obtain h | h | h | h := hIn
      . left; assumption
      . right; right; left; assumption
      . right; left; assumption
      . contradiction
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

:::gradeTheorem 1 NotIn
:::
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
      . contradiction
      . contradiction
      . contradiction
      . contradiction
    apply h4; apply h
    rw [List.mem_cons, List.mem_cons, List.mem_cons]
    right; right; left; rfl
```

:::gradeTheorem 2 Not
:::

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
Just as a single-argument proposition defines a _property_,
a two-argument proposition defines a _relation_.

A proposition parameterized by a number (such as {name}`Even`)
can be thought of as a _property_ — i.e., it defines
a subset of {name}`Nat`, namely those numbers for which the proposition
is provable.  In the same way, a two-argument proposition can be
thought of as a _relation_ — i.e., it defines a set of pairs for
which the proposition is provable.

```lean
namespace Playground
```

Just like properties, relations can be defined inductively.  One
useful example is the "less than or equal to" relation on numbers
that we briefly saw above.

```lean
inductive Le : Nat → Nat → Prop where
  | refl {n : Nat}                : Le n n
  | succ {n m : Nat} (h : Le n m) : Le n (m + 1)
```

(We've written the definition a bit differently this time,
giving explicit names to the arguments to the constructors and
moving them to the left of the colons.)

Proofs of facts about `≤` using the constructors {name}`Nat.le.refl` and
{name}`Nat.le.step` follow the same patterns as proofs about properties, like
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
theorem test_le1 : 3 ≤ 3 := by
  workinclass!
    apply Nat.le.refl

theorem test_le2 : 3 ≤ 6 := by
  workinclass!
    apply Nat.le.step; apply Nat.le.step; apply Nat.le.step; apply Nat.le.refl

theorem test_le3 (h : 2 ≤ 1) : 2 + 2 = 5 := by
  workinclass!
    inversion h with
    | step h' => inversion h'
```

:::slidebreak
:::

The "strictly less than" relation {lean}`n < m` can now be defined
in terms of {lean}`Nat.le`.

```lean
def lt (n m : Nat) : Prop := Nat.le (n + 1) m
```

:::slidebreak
:::

The `≥` operation is defined in terms of `≤`.
Lean provides a theorem {name}`ge_iff_le` allowing us to rewrite between them.

```lean
def ge (m n : Nat) : Prop := Nat.le n m

example (m n : Nat) (h : m ≥ n) : n ≤ m := by
  rw [← ge_iff_le]; assumption

end Playground
```

:::dev
HIDE: PR: Added the following paragraph to try to help reduce
random walks over the following exercises.
:::

From the definition of {name}`Nat.le`, we can sketch the behaviors of
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
theorem zero_le_n (n : Nat) : 0 ≤ n := by
  solution!
    induction n with
    | zero => constructor
    | succ n ih => constructor; exact ih
```

:::gradeTheorem "0.5" zero_le_n
:::

```lean
theorem n_le_m__succ_n_le_succ_m (n m : Nat) (h : n ≤ m) : n + 1 ≤ m + 1 := by
  solution!
    induction h with
    | refl => constructor
    | step h ih =>
      rw [Nat.succ_add]
      constructor; exact ih
```

:::gradeTheorem "0.5" n_le_m__succ_n_le_succ_m
:::

```lean
theorem succ_n_le_succ_m__n_le_m (n m : Nat) (h : n + 1 ≤ m + 1) : n ≤ m := by
  solution!
    inversion h with
    | refl => constructor
    | step h' =>
      apply le_trans _ (n + 1) _
      . constructor; constructor
      . assumption
```

:::gradeTheorem 1 succ_n_le_succ_m__n_le_m
:::

```lean
theorem le_add_l (n m : Nat) : n ≤ n + m := by
  solution!
    induction n with
    | zero => rw [Nat.zero_add]; apply zero_le_n
    | succ n' ih =>
      rw [Nat.succ_add]
      apply n_le_m__succ_n_le_succ_m
      assumption
```

:::gradeTheorem "0.5" le_add_l
:::
:::::

:::::exercise (rating := 2) (name := "plus_le_facts1")
```lean
theorem add_le (n₁ n₂ m : Nat) (h : n₁ + n₂ ≤ m) : n₁ ≤ m ∧ n₂ ≤ m := by
  solution!
    induction h with
    | refl =>
      constructor
      . apply le_add_l
      . rw [Nat.add_comm]; apply le_add_l
    | step =>
      constructor
      . apply le_trans (n := n₁ + n₂)
        . apply le_add_l
        . apply Nat.le.step; assumption
      . apply le_trans (n := n₁ + n₂)
        . rw [Nat.add_comm]; apply le_add_l
        . apply Nat.le.step; assumption
```

:::gradeTheorem 1 add_le
:::

```lean
theorem add_le_cases (n m p q : Nat) (h : n + m ≤ p + q) : n ≤ p ∨ m ≤ q := by
  /- Hint: May be easiest to prove by induction on `n`. -/
  solution!
    induction n generalizing m p q with
    | zero => left; apply zero_le_n
    | succ n' ih =>
      cases p with
      | zero =>
        right; apply add_le at h
        let ⟨_, h⟩ := h
        rw [Nat.zero_add] at h; assumption
      | succ p' =>
        rw [Nat.succ_add, Nat.succ_add] at h
        apply succ_n_le_succ_m__n_le_m at h
        apply ih at h
        cases h with
        | inl => left; apply n_le_m__succ_n_le_succ_m; assumption
        | inr => right; assumption
```

:::gradeTheorem 1 add_le_cases
:::
:::::

:::::exercise (rating := 2) (name := "plus_le_facts2")
```lean
theorem add_le_compat_l (n m p : Nat) (h : n ≤ m) : p + n ≤ p + m := by
  solution!
    induction p with
    | zero =>
      rw [Nat.zero_add, Nat.zero_add]; assumption
    | succ p' ih =>
      rw [Nat.succ_add, Nat.succ_add]
      apply n_le_m__succ_n_le_succ_m
      assumption
```

:::gradeTheorem "0.5" add_le_compat_l
:::

```lean
theorem plus_le_compat_r (n m p : Nat) (h : n ≤ m) : n + p ≤ m + p := by
  solution!
    rw [Nat.add_comm, Nat.add_comm m]
    apply add_le_compat_l
    assumption
```

:::gradeTheorem "0.5" plus_le_compat_r
:::

```lean
theorem le_plus_trans (n m p : Nat) (h : n ≤ m) : n ≤ m + p := by
  solution!
    induction p with
    | zero => rw [Nat.add_zero]; assumption
    | succ p' ih =>
      rw [← Nat.add_assoc]; constructor; assumption
```

:::gradeTheorem 1 le_plus_trans
:::
:::::

:::::exercise (rating := 3) (name := "lt_facts") (optional := true)
```lean
theorem lt_ge_cases (n m : Nat) : n < m ∨ n ≥ m := by
  solution!
    induction n generalizing m with
    | zero =>
      cases m with
      | zero => right; constructor
      | succ _ =>
        left;
        apply n_le_m__succ_n_le_succ_m;
        apply zero_le_n
    | succ n' ih =>
      cases m with
      | zero =>
        rw [ge_iff_le]; right
        apply zero_le_n
      | succ m' =>
        cases ih m' with
        | inl ih =>
          left
          apply n_le_m__succ_n_le_succ_m
          exact ih
        | inr ih =>
          right
          apply n_le_m__succ_n_le_succ_m
          exact ih
```

:::gradeTheorem "1.5" lt_ge_cases
:::

```lean
theorem n_lt_m__n_le_m (n m : Nat) (h : n < m) : n ≤ m := by
  solution!
    apply succ_n_le_succ_m__n_le_m
    constructor; assumption
```

:::gradeTheorem "0.5" n_lt_m__n_le_m
:::

```lean
theorem plus_lt (n₁ n₂ m : Nat) (h : n₁ + n₂ < m) : n₁ < m ∧ n₂ < m := by
  solution!
    constructor
    . apply le_trans (n := (n₁ + n₂) + 1)
      . apply n_le_m__succ_n_le_succ_m
        apply le_add_l
      . exact h
    . apply le_trans (n := (n₂ + n₁) + 1)
      . apply n_le_m__succ_n_le_succ_m
        apply le_add_l
      . rw [Nat.add_comm n₂]; assumption
```

:::gradeTheorem 1 plus_lt
:::
:::::

:::::exercise (rating := 4) (name := "ble_le") (optional := true)
```lean
theorem ble_sound (n m : Nat) (h : Nat.ble n m = true) : n ≤ m := by
  solution!
    induction n generalizing m with
    | zero => apply zero_le_n
    | succ n' ih =>
      cases m with
      | zero =>
        contradiction
      | succ m' =>
        rw [Nat.ble] at h
        apply n_le_m__succ_n_le_succ_m
        apply ih; apply h
```

:::gradeTheorem 2 ble_sound
:::

```lean
theorem ble_complete n m (h : n ≤ m) : Nat.ble n m = true := by
  solution!
    induction n generalizing m with
    | zero => rw [Nat.ble]
    | succ n' ih =>
      cases m with
      | zero => contradiction
      | succ m' =>
        rw [Nat.ble]
        apply succ_n_le_succ_m__n_le_m at h
        apply ih at h
        assumption
```

:::gradeTheorem 2 ble_complete
:::

Hint: The next two can easily be proved without using `induction`.

:::dev PotentialImprovement
AC'21: To me what would be interesting for this last lemma `ble_iff`
would be to show that the proofs of completeness and correctness can
be carried out in a single induction.
:::

```lean
theorem ble_iff (n m : Nat) : Nat.ble n m = true ↔ n ≤ m := by
  solution!
    apply Iff.intro
    . apply ble_sound
    . apply ble_complete
```

:::gradeTheorem 1 ble_iff
:::

```lean
theorem ble_true_trans (n m k : Nat) :
    Nat.ble n m = true →
    Nat.ble m k = true →
    Nat.ble n k = true := by
  solution!
    rw [ble_iff, ble_iff, ble_iff]
    apply le_trans
```

:::gradeTheorem 1 ble_true_trans
:::
:::::

:::dev PotentialImprovement
Another potential exercise:  m ≤ n → n = m + (n - m).
See p. 188 in CoqArt.
:::

:::::exercise (rating := 3) (name := "R_provability") (manual := true)
We can define three-place relations, four-place relations,
etc., in just the same way as binary relations.  For example,
consider the following three-place relation on numbers:

```lean
inductive R : Nat → Nat → Nat → Prop where
  | c1                                               : R  0      0       0
  | c2 {m n k : Nat} (h : R  m       n       k)      : R (m + 1) n      (k + 1)
  | c3 {m n k : Nat} (h : R  m       n       k)      : R  m     (n + 1) (k + 1)
  | c4 {m n k : Nat} (h : R (m + 1) (n + 1) (k + 2)) : R  m      n       k
  | c5 {m n k : Nat} (h : R  m       n       k)      : R  n      m       k
```

:::dev
HIDE: APT 21: Reformatted the above after a student with dyslexia
complained. But the effect is still lost in the HTML.  He also
noted that the kind of question that follows doesn't really require
a high-arity relation.

MRC 3/22: I believe that violates the OCaml Community Guidelines on
indentation.

https://ocaml.org/learn/tutorials/guidelines.html#Bad-indentation-of-pattern-matching-constructs

Whether those are applicable here is a matter of debate. But
torquing the entire textbook into this mode of alignment does not
seem any more desirable to me than torquing an OCaml codebase.

BCP 25: No, but for this specific problem it seems OK. Let's leave
it like this.
:::

- Which of the following propositions are provable?
- `R 1 1 2`
- `R 2 2 6`

- If we dropped constructor `c5` from the definition of `R`,
would the set of provable propositions change?  Briefly (1
sentence) explain your answer.

- If we dropped constructor `c4` from the definition of `R`,
would the set of provable propositions change?  Briefly (1
sentence) explain your answer.

:::solution
- The first proposition is provable and the second is not.
  The proof term for the first is:
  ```display
  (c3 _ _ _ (c2 _ _ _ c1)).
  ```
- Dropping `c5` would not change the set of provable
  propositions. `c4` and `c1` don't interact with `c5`, since
  they're already symmetric in `m` and `n`; `c2` followed by
  `c5` is equivalent to `c3`, and vice versa.

- Dropping `c4` would not change the set of provable
  propositions. This constructor just "undoes" one application
  of `c2` and one application of `c3`. More precisely, the
  only way we can construct evidence for `R (S m) (S n) (S (S o))`
  is by applying `c2` and `c3` (in either order) to evidence for
  `R m n o`, so the latter must already hold. (This can be proved
  by induction, although the proof is surprisingly tedious.)
:::

::::hide
```
    /- Here is such a proof for posterity. -/

    /- inductive R' : Nat → Nat → Nat → Prop where
      | c1' : R' 0 0 0
      | c2' m n o (h : R' m n o) : R' (m + 1) n (o + 1)
      | c3' m n o (h : R' m n o) : R' m (n + 1) (o + 1)

    Ltac inv H := inversion H; subst; clear H.

    theorem c5_redundant: forall m n o, R' m n o → R' n m o.
    Proof.
      intros m n o H.
      induction H.
      - apply c1'.
      - apply c3'; auto.
      - apply c2'; auto.
    Qed.

    theorem c4_redundant: forall m n o, R' (S m) (S n) (S(S o)) → R' m n o.
    Proof.
      /- This one is nastier than one might expect. -/
      assert (Q1: forall m n o, R' (S m) n (S o) → R' m n o).
      { induction n; intros.
        - inv H.  apply h₃.
        - inv H.
          + apply h₃.
          + destruct o.
            * inv h₃.
            * apply c3'. apply IHn. apply h₃.
      }
      assert (Q2: forall m n o, R' m (S n) (S o) → R' m n o).
      { induction m; intros.
        - inv H. apply h₃.
        - inv H.
          + destruct o.
            * inv h₃.
            * apply c2'.  apply IHm. apply h₃.
          + apply h₃.
      }
      intros.
      inv H.
      - apply Q2; apply h₃.
      - apply Q1; apply h₃.
    Qed.

    theorem R_R': forall m n o, R m n o↔  R' m n o.
    Proof.
      split; intros.
      -  induction H.
        + apply c1'.
        + apply c2'; auto.
        + apply c3'; auto.
        + apply c4_redundant; auto.
        + apply c5_redundant; auto.
      - induction H.
        + apply c1.
        + apply c2; auto.
        + apply c3; auto.
    Qed. -/
```
::::

:::grade
`GRADE_MANUAL 3: R_provability`
:::
:::::

:::::exercise (rating := 3) (name := "R_fact") (optional := true)
The relation `R` above actually encodes a familiar function.
Figure out which function; then state and prove this equivalence
in Lean.

```lean
def fR : Nat → Nat → Nat
  := solution!((· + ·))

namespace R

theorem R.equiv_fR m n k : R m n k ↔ fR m n = k := by
  solution!
    unfold fR
    apply Iff.intro
    . intro h; induction h with
      | c1 => rfl
      | c2 _ ih => rw [Nat.succ_add, ih]
      | c3 _ ih => rw [Nat.add_succ, ih]
      | c4 _ ih =>
        rw [Nat.succ_add, Nat.add_succ] at ih
        injections
      | c5 _ ih => rw [Nat.add_comm]; exact ih
    . intro h; subst h
      have R0 : ∀ k, R 0 k k := by
        intro k; induction k with
        | zero => exact c1
        | succ k ih => exact c3 ih
      induction m with
      | zero => rw [Nat.zero_add]; exact R0 n
      | succ m ih => rw [Nat.succ_add]; exact c2 ih
```

:::autogradedHole fR
:::

:::gradeTheorem 3 R.equiv_fR
:::

:::hide
And here's a somewhat nicer version using some automation,
   but we haven't covered that yet...

```display
From Stdlib Require Import Lia.

theorem R_plus: forall m n k, R m n k ↔ m + n = k.
Proof.
  intros m n k; split; intros.
  - induction H; try reflexivity; try lia.
  - generalize dependent n. generalize dependent m.
    induction k as [|k']; intros m n H.
    + destruct m; try inversion H.
      destruct n; try inversion H0.
      apply c1.
    + destruct m as [|m'].
      * destruct n; try inversion H. apply c3.
        apply IHo'. reflexivity.
      * apply c2. apply IHo'. lia.
Qed.
```
:::
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

- Define an inductive proposition `subseq` on {lean}`List Nat` that
  captures what it means to be a subsequence. There are a number
  of correct ways to do this. You should make sure that your
  definition behaves correctly on all the positive and negative
  examples above, but you do not need to prove this formally.

- Prove `subseq_refl` that subsequence is reflexive, that is,
  any list is a subsequence of itself.

- Prove `subseq_app` that for any lists {lean}`l₁`, {lean}`l₂`, and {lean}`l₃`,
  if {lean}`l₁` is a subsequence of {lean}`l₂`, then {lean}`l₁` is also a subsequence
  of {lean}`l₂ ++ l₃`.

- (Harder) Prove `subseq_trans` that subsequence is transitive ─
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
  | sub_nil {l : List Nat} : Subseq [] l
  | sub_take {x : Nat} {l₁ l₂ : List Nat}
    (h : Subseq l₁ l₂) :
    Subseq (x :: l₁) (x :: l₂)
  | sub_skip {x : Nat} {l₁ l₂ : List Nat}
    (h : Subseq l₁ l₂) :
    Subseq l₁ (x :: l₂)
-- END SOLUTION

namespace Subseq

theorem refl (l : List Nat) : Subseq l l := by
  solution!
    induction l with
    | nil => constructor
    | cons hd tl ih =>
      constructor; assumption

theorem app (l₁ l₂ l₃ : List Nat)
    (h : Subseq l₁ l₂) : Subseq l₁ (l₂ ++ l₃) := by
  solution!
    induction h with
    | sub_nil  => constructor
    | sub_take => constructor; assumption
    | sub_skip => constructor; assumption
```

:::autogradedHole Subseq
:::

:::dev
HIDE: AC'21: this exercise should probably be marked as more
challenging.  In particular, it's not necessarily obvious at first
sight that the induction should go on the second hypothesis, and
with `l₁` generalized.  BCP 21: Made it 3 points instead of 2, and
included a hint. CH'23: Made it 4 points, since there are 5 different
choices here and the hint doesn't help with that.
:::

```lean
theorem trans (l₁ l₂ l₃ : List Nat)
    (h₁₂ : Subseq l₁ l₂)
    (h₂₃ : Subseq l₂ l₃) :
    Subseq l₁ l₃ := by
  /- Hint: be careful about what you are doing induction on and which
     other things need to be generalized... -/
  solution!
    induction h₂₃ generalizing l₁ with
    | sub_nil => inversion h₁₂; constructor
    | sub_take _ ih =>
      inversion h₁₂; constructor
      . constructor; apply ih; assumption
      . constructor; apply ih; assumption
    | sub_skip _ ih =>
      constructor; apply ih; assumption

end Subseq
```

:::gradeTheorem 1 Subseq.refl
:::

:::gradeTheorem 2 Subseq.app
:::

:::gradeTheorem 3 Subseq.trans
:::
:::::

:::::exercise (rating := 2) (name := "R_provability2") (optional := true) (manual := true)
Suppose we give Lean the following definition:

```display
inductive R : Nat → List Nat → Prop where
  | c1                                            : R  0      []
  | c2 {n : Nat} {l : List Nat} (h : R  n      l) : R (n + 1) (n :: l)
  | c3 {n : Nat} {l : List Nat} (h : R (n + 1) l) : R  n      l
```

Which of the following propositions are provable?

- `R 2 [1, 0]`
- `R 1 [1, 2, 1, 0]`
- `R 6 [3, 2, 1, 0]`

:::dev "Andrew Tolmach (AndrewTolmach)" PotentialImprovement
```
As in R_provability, above, would be good
to get this formatting into the HTML version.
```
:::

:::solution
The first two are provable, the third is not.

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
:::::

::::::

::::hide
```
    /- Under construction... -/
    /- Definition partition {α : Type} (test : α → Bool) (l : List α) :=
      (filter test l, filter (fun x => negb (test x)) l) .

    /- LATER: Adjust inductive syntax -/
    inductive shuffle (α:Type) : List α → List α → List α → Prop :=
      | shuffle_nil_l : forall (l₂:List α), shuffle _ [] l₂ l₂
      | shuffle_nil_r : forall (l₁:List α), shuffle _ l₁ [] l₁
      | shuffle_cons_l : forall (x:α) (l₁ l₂ l12 : List α),
                          shuffle _ l₁ l₂ l12 →
                          shuffle _ (x::l₁) l₂ (x::l12)
      | shuffle_cons_r : forall (x:α) (l₁ l₂ l12: List α),
                          shuffle _ l₁ l₂ l12 →
                          shuffle _ l₁ (x::l₂) (x::l12).

    Arguments shuffle `α` _ _ _.

    /- HIDE: If they do this proof, they'll see some uses of [fix]... -/
    /- HIDE: M: I don't understand the above remark. This proof, though
      somewhat messy, can be done with everything they've seen so far.
      In any case, I attempt a proof, which is arguably the same as the
      old one. -/

    theorem partition_correct_1 : forall (α:Type) (l l₁ l₂: List α) (test:α → Bool),
      partition test l = (l₁,l₂) →
      shuffle l₁ l₂ l.
    Proof.
      intros α l l₁ l₂ test H. generalize dependent l₂. generalize dependent l₁.
      induction l as [| x l' ].
      - /- l = [] -/
        intros. inversion H. apply shuffle_nil_l.
      - /- l = x :: l' -/
        intros. destruct (test x) eqn:Heqb.
          + /- true = test x -/
            inversion H.
            rewrite Heqb in h₁. rewrite Heqb in h₂. rewrite  Heqb.
            simpl in h₂. simpl.
            apply shuffle_cons_l. apply IHl'. reflexivity.
          + /- false = test x -/
            inversion H.
            rewrite Heqb in h₁. rewrite Heqb in h₂. rewrite Heqb.
            simpl in h₂. simpl.
            apply shuffle_cons_r. apply IHl'. reflexivity.
    Qed.

    /- The old proof is longer (in number of lines), but I cheat.
      And the old proof uses more [destruct]s.
      Thus, the new proof above is better in at least two quantifiable
      ways, but I'm afraid its not entirely clean yet. -/

    /-  intros α l l₁ l₂ test H. generalize dependent l₂.
      generalize dependent l₁.
      induction l as [|x l'].
      - /- l = [] -/
        intros.
        unfold partition in H.
        unfold filter in H.
        inversion H.
        apply shuffle_nil_l.
      - /- l = x::l' -/
        intros.
        unfold partition in H. unfold filter in H.
        remember (test x) as h₁.
        destruct h₁.
          + /- true -/
            simpl in H.
            destruct l₁.
            * /- nil -/
              inversion H.
            * /- cons -/
              inversion H. subst.
              apply shuffle_cons_l.
              apply IHl'.
              unfold partition.
              unfold filter.
              reflexivity.
          + /- false -/
            simpl in H.
            destruct l₂.
            * /- nil -/
              inversion H.
            * /- cons -/
              inversion H. subst.
              apply shuffle_cons_r.
              apply IHl'.
              unfold partition.
              unfold filter.
              reflexivity.
    Qed. -/

    /- LATER: The proof needs to be polished. -/
    /- LATER: Also needs to talk about the two lists respecting the
      partitioning condition.  We'd really like to say all three
      parts of the spec together, but we don't have∧ yet! -/ -/
```
::::

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

:::autogradedHole TotalRelation
:::

:::gradeTheorem 2 total_relation_is_total
:::
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
-- /SOLUTION
```

:::autogradedHole EmptyRelation
:::

```lean
theorem empty_relation_is_empty (n m : Nat) : ¬ EmptyRelation n m := by
  solution!
    intro contra; inversion contra
```

:::gradeTheorem 2 empty_relation_is_empty
:::
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

:::suppressPreviousHeaderWhenTerse
:::

::::::full
:::::exercise (rating := 3) (name := "nostutter_defn")
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
  | nostutter0: NoStutter []
  | nostutter1 {x : α} : NoStutter (x :: [])
  | nostutter2 {x y : α} {l : List α}
    (hneq : x ≠ y) (h : NoStutter (y :: l)) :
    NoStutter (x :: y :: l)
 -- /SOLUTION
```

:::autogradedHole NoStutter
:::

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

:::dev "Arthur Azevedo de Amorim (arthuraa)" PotentialImprovement
The script below seems too fragile, we should probably
change it to make it more robust.
:::

```lean
example : ¬ (NoStutter [3, 1, 1, 4]) := by
  suggested!
    intro contra; inversion contra with
    | nostutter2 _ contra =>
      inversion contra with
      | nostutter2 _ h _ =>
        apply h
        rfl
```

:::grade
`GRADE_MANUAL 3: nostutter`
:::
:::::

:::::exercise (rating := 4) (name := "filter_challenge") (level := Advanced)
Let's prove that our definition of `filter` from the {ref "Poly"}[Poly]
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
inductive Merge {α:Type} : List α → List α → List α → Prop where
-- SOLUTION
  | merge_empty : Merge [] [] []
  | merge_left {x : α} {l₁ l₂ l₃ : List α}
    (h : Merge l₁ l₂ l₃) :
    Merge (x :: l₁) l₂ (x :: l₃)
  | merge_right {x : α} {l₁ l₂ l₃ : List α}
    (h : Merge l₁ l₂ l₃) :
    Merge l₁ (x :: l₂) (x :: l₃)
-- END SOLUTION

theorem merge_filter (α : Type) (test : α → Bool) (l l₁ l₂ : List α)
  (hmerge : Merge l₁ l₂ l)
  (h₁ : List.all l₁ test)
  (h₂ : List.all l₂ (!test ·)) :
  List.filter test l = l₁ := by
  solution!
    induction hmerge with
    | merge_empty => rfl
    | merge_left h' ih =>
      rw [List.all_cons, Bool.and_eq_true] at h₁
      obtain ⟨htest, h₁⟩ := h₁
      rw [List.filter_cons_of_pos htest];
      congr 1; apply ih
      . assumption
      . assumption
    | merge_right h' ih =>
      rw [List.all_cons, Bool.and_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true] at h₂
      obtain ⟨htest, h₂⟩ := h₂
      rw [List.filter_cons_of_neg (ne_true_of_eq_false htest)]
      congr 1; apply ih
      . assumption
      . assumption
```

:::autogradedHole Merge
:::

::::hide
```
 Another possible problem (perhaps for Basics.v): Write a Rocq function
   that generates the list of all in-order merges of two lists... However, the
   following isn't structurally recursive :-(
       Fixpoint all_merges {α : Type} (l₁ l₂ : List α) :=
         match (l₁,l₂) with
         | (l₁,[]) => `l₁`
         | ([],l₂) => `l₂`
         | (x1::rest1,x2::rest2) =>
              (map (fun l => cons x1 l) (all_merges rest1 l₂))
           ++ (map (fun l => cons x2 l) (all_merges l₁ rest2))
         end.
```
::::

:::gradeTheorem 6 merge_filter
:::
:::::

:::::exercise (rating := 5) (name := "filter_challenge_2") (level := Advanced) (optional := true)
A different way to characterize the behavior of `filter` goes like
this: Among all subsequences of `l` with the property that `test`
evaluates to `true` on all their members, `filter test l` is the
longest. Formalize this claim and prove it.

```lean
-- SOLUTION
namespace Sol
/- We reproduce the definition of subseq here, in a module
    so it doesn't conflict. -/

inductive Subseq {α : Type} : List α → List α → Prop where
  | sub_nil {l : List α} : Subseq [] l
  | sub_take {x : α} {l₁ l₂ : List α}
    (h : Subseq l₁ l₂) :
    Subseq (x :: l₁) (x :: l₂)
  | sub_skip {x : α} {l₁ l₂ : List α}
    (h : Subseq l₁ l₂) :
    Subseq l₁ (x :: l₂)

/- A few lemmas about subseq. -/
namespace Subseq

theorem drop_l {α} (x : α) (l₁ l₂ : List α)
    (h : Subseq (x :: l₁) l₂) : Subseq l₁ l₂ := by
  induction l₂ generalizing l₁ with
  | nil => inversion h
  | cons _ _ ih =>
    inversion h with
    | sub_take hs =>
      constructor; assumption
    | sub_skip hs =>
      constructor; apply ih; assumption

theorem drop {α} (x : α) (l₁ l₂ : List α)
    (h : Subseq (x :: l₁) (x :: l₂)) : Subseq l₁ l₂ := by
  inversion h with
  | sub_take => assumption
  | sub_skip => apply drop_l; assumption

end Subseq

/-- A list is _maximal_ with property `P` if it has the property, and
    every other list with the property is at most as long as it is. -/
def Maximal {α : Type} (lmax : List α) (P : List α → Prop) : Prop :=
  P lmax ∧ ∀ l', P l' → l'.length ≤ lmax.length

/-- A "good subsequence" for a given list `l` and a `test` is a
    subsequence of `l` all of whose members evaluate to `true` under
    the `test`. -/
def GoodSubseq {α : Type} (test : α → Bool) (l lsub : List α) :=
  Subseq lsub l ∧ List.all lsub test

/-- Good subsequences can be extended with good elements. -/
theorem good_subseq_extend (α : Type) (x : α)
    (l lsub : List α) (test : α → Bool) (hx : test x) :
    GoodSubseq test l lsub →
    GoodSubseq test (x :: l) (x :: lsub) := by
  intro ⟨hsub, hall⟩; constructor
  . constructor; assumption
  . rw [List.all_cons, Bool.and_eq_true]; constructor
    . assumption
    . assumption

/-- If `lmax` is a maximal good subsequence of `x :: l` and `x` is not good,
    then `lmax` is also a maximal good subsequence of `l`. -/
theorem maximal_strengthening (α : Type) (x : α)
    (lmax l : List α) (test : α → Bool) (hx : !test x) :
    Maximal lmax (GoodSubseq test (x :: l)) →
    Maximal lmax (GoodSubseq test l) := by
  intro ⟨⟨hsub, hall⟩, hlen⟩; constructor; constructor
  . inversion hsub with
    | sub_nil => constructor
    | sub_take l₁ hsub =>
      rw [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨ht, _⟩ := hall
      rw [Bool.not_eq_eq_eq_not, Bool.not_true] at hx
      rw [hx] at ht; contradiction
    | sub_skip => assumption
  . assumption
  . intro l ⟨hsub', hall'⟩; apply hlen; constructor
    . constructor; assumption
    . assumption

/- Some easy lemmas about filter: its result is a good subsequence of
    the original list. -/

theorem filter_subseq (α : Type) (l : List α) (test : α → Bool) :
    Subseq (List.filter test l) l := by
  induction l with
  | nil => rw [List.filter_nil]; constructor
  | cons hd tl ih =>
    cases h : (test hd)
    . rw [List.filter_cons_of_neg (ne_true_of_eq_false h)]; constructor; assumption
    . rw [List.filter_cons_of_pos h]; constructor; assumption

theorem filter_all (α : Type) (l : List α) (test : α → Bool) :
    List.all (List.filter test l) test := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    cases h : (test hd)
    . rw [List.filter_cons_of_neg (ne_true_of_eq_false h)]; assumption
    . rw [List.filter_cons_of_pos h, List.all_cons, Bool.and_eq_true]; constructor
      . assumption
      . assumption

/- And now for the main theorem: `lsub` is a maximal good subsequence
    of `l` if and only if `filter test l = lsub` -/
/- LATER: This could use a lot of cleanup... -/
theorem filter_spec2 (α : Type) (l lsub : List α) (test : α → Bool) :
    Maximal lsub (GoodSubseq test l) ↔ List.filter test l = lsub := by
  apply Iff.intro
  . induction l generalizing lsub with
    | nil =>
      intro ⟨⟨hsub, hall⟩, hlen⟩
      inversion hsub
      rw [List.filter_nil]
    | cons hd tl ih =>
      cases htest : test hd with
      | false =>
        rw [List.filter_cons_of_neg]
        . intro hmax; apply ih
          apply maximal_strengthening _ _ _ _ _ _ hmax
          rw [Bool.not_eq_eq_eq_not, Bool.not_true]
          assumption
        . exact ne_true_of_eq_false htest
      | true =>
        intro ⟨⟨hsub, hall⟩, hlen⟩
        rw [List.filter_cons_of_pos htest]
        /- in this case, lsub must begin with hd, since otherwise it
        wouldn't be maximal. -/
        cases lsub with
        | nil => -- lsub = [] (impossible: contradicts maximality of lsub)
          have contra : [hd].length ≤ ([] : List α).length := by
            apply hlen; constructor
            . constructor; constructor
            . rw [List.all_cons, List.all_nil, Bool.and_true]; assumption
          contradiction
        | cons hd' tl' =>
          have heq : hd = hd' := by -- because of maximality again
            inversion hsub with
            | sub_take hsub => rfl
            | sub_skip hsub =>
            -- contradiction, since hd :: hd' :: tl' would be longer
              have contra : (hd :: hd' :: tl').length ≤ (hd' :: tl').length := by
                apply hlen; constructor
                . constructor; assumption
                . rw [List.all_cons, List.all_cons, Bool.and_eq_true, Bool.and_eq_true]
                  rw [List.all_cons, Bool.and_eq_true] at hall
                  constructor; assumption; assumption
              rw [List.length_cons, List.length_cons, Nat.add_le_add_iff_right] at contra
              apply Nat.not_add_one_le_self at contra
              contradiction
          subst heq; congr; apply ih; constructor; constructor
          . exact hsub.drop hd _ _
          . rw [List.all_cons, Bool.and_eq_true] at hall
            obtain ⟨_, _⟩ := hall; assumption
          . intro l' hgood; rw [List.length_cons] at hlen
            apply succ_n_le_succ_m__n_le_m
            apply hlen (hd :: l')
            exact good_subseq_extend _ _ _ _ _ htest hgood
  . intro hfilter; constructor; rw [← hfilter]; constructor
    . apply filter_subseq
    . apply filter_all
    . intro l' ⟨hsub, hall⟩
      induction l generalizing l' lsub with
      | nil =>
        inversion hsub; rw [List.length_nil]
        apply zero_le_n
      | cons hd tl ih =>
        cases htest : test hd with
        | false =>
          rw [List.filter_cons_of_neg] at hfilter
          . apply ih _ hfilter _ _ hall
            inversion hsub with
            | sub_nil => constructor
            | sub_take l hsub =>
              rw [List.all_cons, Bool.and_eq_true] at hall
              obtain ⟨ht, _⟩ := hall
              rw [ht] at htest
              contradiction
            | sub_skip hsub => assumption
          . exact ne_true_of_eq_false htest
        | true =>
          rw [List.filter_cons_of_pos htest] at hfilter
          rw [← hfilter, List.length_cons]
          inversion hsub with
          | sub_nil => rw [List.length_nil]; apply zero_le_n
          | sub_take l hsub =>
            rw [List.length_cons]; apply n_le_m__succ_n_le_succ_m
            apply ih _ rfl _ hsub
            rw [List.all_cons, Bool.and_eq_true] at hall
            obtain ⟨_, _⟩ := hall
            assumption
          | sub_skip hsub =>
            apply Nat.le_succ_of_le
            exact ih _ rfl _ hsub hall
end Sol
-- END SOLUTION
```
:::::

:::::exercise (rating := 4) (name := "palindromes") (optional := true)
A palindrome is a sequence that reads the same backwards as
forwards.

- Define an inductive proposition `Pal` on `List α` that
  captures what it means to be a palindrome. (Hint: You'll need
  three cases.)

- Prove `pal_app_reverse`, which states that

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

:::dev
```
HIDE: MTF 6/22: It isn't exactly clear why the single constructor approach
"will not work very well".  It seems to work extremely well:

 inductive pal {α : Type} : List α → Prop :=
   | palc : forall l, l = rev l → pal l.

 theorem pal_app_reverse : forall (α:Type) (l : List α),
   pal (l ++ (rev l)).
 Proof.
   intros α l.
   apply palc.
   rewrite rev_app_distr.
   rewrite rev_involutive.
   reflexivity.
 Qed.

 theorem pal_reverse : forall (α:Type) (l: List α) , pal l → l = rev l.
 Proof.
   intros α l H. destruct H. assumption.
 Qed.

 theorem palindrome_converse: forall {α: Type} (l: List α), l = rev l → pal l.
 Proof.
   intros α l H. apply palc. assumption.
 Qed.

   This seems to be yet another example of a property that can be expressed as a
   non-inductive proposition being artificially formulated as an inductive
   proposition.  Are there any other properties of the [palindrome] proposition
   that would be difficult to prove from its specification?

BCP 25: Took away the "will not work very well" wording.
```
:::

```lean
inductive Pal {α : Type} : List α → Prop where
-- SOLUTION
  | pal_nil : Pal []
  | pal_one {x : α} : Pal [x]
  | pal_consnoc {x : α} {l : List α} (h : Pal l) : Pal (x :: (l ++ [x]))
-- END SOLUTION
```

:::autogradedHole Pal
:::

:::dev PotentialImprovement
```
APT21: a student noted that the pal_one case is easy to
miss, since the theorems don't require it! BCP 25: We could fix
that by adding some examples, e.g. [], [1], and [1,1].
```
:::

```lean
theorem pal_app_reverse (α : Type) (l : List α) :
    Pal (l ++ l.reverse) := by
  solution!
    induction l with
    | nil => rw [List.reverse_nil, List.append_nil]; constructor
    | cons hd tl ih =>
      rw [List.reverse_cons, List.cons_append, ← List.append_assoc]
      constructor; assumption
```

:::gradeTheorem 3 pal_app_reverse
:::

:::dev PotentialImprovement
Note that we're using some standard library stuff here...
We should at least explicitly qualify them...
:::

```lean
theorem pal_reverse (α : Type) (l : List α) (hp : Pal l) : l = l.reverse := by
  solution!
    induction hp with
    | pal_nil => rw [List.reverse_nil]
    | pal_one =>
      rw [List.reverse_cons, List.reverse_nil, List.nil_append]
    | pal_consnoc h ih =>
      rw [List.reverse_cons, List.reverse_append, ← List.cons_append, ← ih]
      congr
```

:::gradeTheorem 3 pal_reverse
:::

:::dev "Daniel Sainati (dsainati1)" NOW
This one is super annoying without simp.
I propose we move it to the simp chapter
:::
:::::

:::::exercise (rating := 5) (name := "palindrome_converse") (optional := true)
Again, the converse direction is significantly more difficult, due
to the lack of evidence.  Using your definition of `Pal` from the
previous exercise, prove that

```display
∀ l, l = l.reverse → Pal l.
```

```lean
-- SOLUTION
/- Proving the converse theorem is much harder, because a standard
    induction over the list `l` doesn't work.  The trick to the
    following proof, due to Nathan Collins, is to induct over _half
    the length_ of `l`.  We make heavy use of destruct and inversion
    to clear away the impossible cases. -/

theorem reverse_pal {α : Type} (n : Nat) (l : List α)
    (hlen : l.length / 2 = n) (hrev : l = l.reverse) : Pal l := by
  induction n generalizing l with
  /- (length l) / 2 = 0 || l has length 0 or 1 -/
  | zero =>
    cases l with
    | nil => constructor
    | cons _ l =>
      cases l with
      | nil => constructor
      | cons _ l' =>
        /- impossible : l has length > 1 -/
        rw [List.length_cons, List.length_cons] at hlen
        rw [Nat.div_eq_zero_iff] at hlen
        cases hlen; contradiction; contradiction
  /- (length l) / 2 >= 1  || l has length at least 2 -/
  | succ n ih =>
    cases l with
    | nil => rw [List.length_nil, Nat.zero_div] at hlen; contradiction
    | cons x l =>
      rw [List.length_cons] at hlen
      rw [List.reverse_cons] at hrev
      cases heq : l.reverse with
      | nil =>
        have h : l = [] := by
          cases l; rfl
          simp only [List.reverse_cons, List.append_eq_nil_iff] at heq
          obtain ⟨_, _⟩ := heq; contradiction
        rw [h]; constructor
      | cons y l' =>
        rw [heq] at hrev
        injections hrev heqtl; subst hrev
        rw [heqtl, List.append_eq]
        constructor; apply ih
        . rw [heqtl] at hlen
          rw [List.append_eq, List.length_append, List.length_cons,
            List.length_nil, Nat.zero_add] at hlen
          omega
        . rw [heqtl, List.append_eq, List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.cons_append, List.nil_append] at heq
          injections _ _
          symm
          assumption


  /- And here's another solution due (modulo some fixes by BCP/AAA to
     replace snoc with app) to Michael Schulman. It uses a few tactics
     that we haven't seen yet.

  theorem eqrev_pal_gen (α : Type) : forall (l:List α) (p t:List α),
    l = p ++ t → p = rev p → pal p.
  Proof.
   induction l as [| x l'].
   - /- l = nil -/
     destruct p.
     + /- p = nil -/
       destruct t as [| x t'].
          * /- t = nil -/
            intros; constructor.
          * /- t = cons -/
            intros H; inversion H.
     + /- p = cons -/
       intros t H.
       inversion H.
   - /- l = cons -/
     destruct p as [| y p'].
     + /- p = nil -/
       intros. constructor.
     + /- p = cons -/
       intros t H K.
       inversion H.
       simpl in K.
       destruct (rev p') as [| z p''] eqn:Heqrevp'.
       * /- rev p' = nil -/
         destruct p' as [| w q].
         { /- p' = nil -/ constructor. }
         { /- p' = cons -/
           assert (L : [] = w :: q).
           { rewrite <- rev_involutive. rewrite  Heqrevp'. reflexivity. }
           inversion L. }
       * /- rev p' = cons -/
         assert (M : rev (rev p') = (rev p'') ++ [z]).
         { rewrite Heqrevp'. reflexivity. }
         rewrite rev_involutive in M.
         rewrite M.
         inversion K.
         /- Now we finally get to do -/
         constructor.
         apply (IHl' _ (z :: t)).
         { /- l' = rev p'' ++ z :: t -/
           rewrite h₂. rewrite M. rewrite <- app_assoc. reflexivity. }
         { /- rev p'' = rev (rev p'') -/
           rewrite H4 in Heqrevp'. rewrite rev_app_distr in Heqrevp'.
           inversion Heqrevp'.
           rewrite rev_involutive.
           symmetry. apply H5. } Qed.

  theorem eqrev_pal (α : Type) (l:List α) : (l = rev l) → pal l.
  Proof.
    intros H.
    apply (eqrev_pal_gen _ l l []).
    rewrite app_nil_r. reflexivity.
    apply H.
  Qed.

  /- A final possibility is adding a natural number n and a hypothesis
     "length l ≤ n" and inducting on n.  The following solution by
     Mihir Mehta follows this strategy... -/

  theorem palindrome_converse_lemma_1:
    forall {α: Type} (l: List α), length (rev l) = length l.
  Proof. {
    intros α. induction l.
    { reflexivity. }
    { simpl. rewrite → app_length. rewrite → IHl. simpl.
      rewrite → add_comm. reflexivity. }
  } Qed.

  theorem palindrome_converse_lemma_2:
    forall {α: Type} (n: nat) (l: List α), (length l ≤ n) → l = rev l → pal l.
  Proof. {
    intros α. induction n as [| n'].
    { /- n = 0 -/
      intros [| x l'] h₁ h₂.
      { /- l = [] -/ apply pal_nil. }
      { /- l = x :: l' -/ inversion h₁. }
    }
    { /- n = S n'-/
      intros [| x l'] h₃ H4.
      { /- l = [] -/ apply pal_nil. }
      { /- l = x :: l' -/
        simpl in H4.
        destruct (rev l') as [| x' l''] eqn:H5.
        { /- rev l = [] -/
          rewrite <- (rev_involutive α l'). rewrite → H5. simpl.
          apply pal_one. }
        { /- rev l = x' :: l'' -/
          inversion H4 as [[H6 H7]]. apply pal_consnoc. apply (IHn' l'').
          { /- proving: length l'' ≤ n' -/
            rewrite → H7 in h₃. simpl in h₃.
            rewrite → app_length in h₃. simpl in h₃.
            rewrite → add_comm in h₃. simpl in h₃.
            apply Sn_le_Sm__n_le_m, Sn_le_Sm__n_le_m.
            apply le_S. apply h₃.
          }
          { /- proving l'' = rev l'' -/
            rewrite → H7 in H5. rewrite → rev_app_distr in H5. simpl in H5.
            inversion H5 as [H8]. rewrite → H8, → H8. reflexivity.
          }
        }
      }
    }
  } Qed. -/

theorem palindrome_converse {α : Type} (l : List α) (h : l = l.reverse) : Pal l := by
  exact reverse_pal _ _ rfl h
-- END SOLUTION
```
:::::

:::::exercise (rating := 4) (name := "NoDup") (level := Advanced) (optional := true)
Use the `∈` property to define a proposition `Disjoint l₁ l₂`,
which should be provable exactly when `l₁` and `l₂` are
lists (with elements of type `α`) that have no elements in
common.

```lean
-- SOLUTION
def Disjoint {α : Type} (l₁ l₂ : List α) : Prop :=
  ∀ (x : α), x ∈ l₁ → ¬ x ∈ l₂
-- END SOLUTION
```

Next, use `∈` to define an inductive proposition `NoDup l`,
which should be provable exactly when `l` is a list (with
elements of type `α`) where every member is different from every
other.  For example, `NoDup ([1, 2, 3, 4] : List Nat)` and
`NoDup ([] : List Bool)` should be provable, while
`NoDup ([1, 2, 1] : List Nat)` and
`NoDup ([true, true] : List Bool)` should not be.

```lean
-- SOLUTION
inductive NoDup {α : Type} : List α → Prop where
  | NoDup_nil : NoDup []
  | NoDup_cons {x : α} {l : List α}
    (hnin : ¬ x ∈ l) (h : NoDup l) : NoDup (x :: l)
-- END SOLUTION
```

Finally, state and prove one or more interesting theorems relating
`Disjoint`, `NoDup` and `++` (list append).

```lean
-- SOLUTION
/- Here are some possible answers: -/

theorem NoDup_append (α : Type) (l₁ l₂: List α)
    (h₁ : NoDup l₁) (h₂ : NoDup l₂) (hdis : Disjoint l₁ l₂) :
    NoDup (l₁ ++ l₂) := by
  induction l₁ generalizing l₂ with
  | nil => rw [List.nil_append]; assumption
  | cons hd tl ih =>
    constructor
    . intro contra; rw [List.append_eq, List.mem_append] at contra
      cases contra with
      | inl =>
        inversion h₁ with
        | _ hdup hin => apply hin; assumption
      | inr contra =>
        apply hdis hd _ contra
        rw [List.mem_cons]; left; rfl
    . apply ih _ _ h₂ _
      . inversion h₁; assumption
      . intros x hin
        apply hdis; rw [List.mem_cons]
        right; assumption

theorem NoDup_Disjoint (α : Type) (l₁ l₂: List α)
    (h : NoDup (l₁++l₂)) : Disjoint l₁ l₂ := by
  intro x hin contra
  induction l₁ generalizing l₂ x with
  | nil => rw [List.mem_nil_iff] at hin; contradiction
  | cons hd tl ih =>
    rw [List.mem_cons] at hin
    inversion h with
    | NoDup_cons hdup hnin =>
      cases hin with
      | inl hin =>
        subst hin; apply hnin
        rw [List.append_eq, List.mem_append]; right; assumption
      | inr hin => exact ih _ hdup _ hin contra

/- We can also show the following results about [NoDup] and [++]
   by themselves -/
theorem NoDup_left (α : Type) (l₁ l₂: List α)
    (hdup : NoDup (l₁ ++ l₂)) : NoDup l₁ := by
  induction l₁ generalizing l₂ with
  | nil => constructor
  | cons hd tl ih =>
    inversion hdup with
    | _ hdup' hin =>
      constructor
      . intro contra; apply hin
        rw [List.append_eq, List.mem_append]; left; assumption
      . exact ih _ hdup'

theorem NoDup_right (α : Type) (l₁ l₂ : List α)
    (hdup : NoDup (l₁ ++ l₂)) : NoDup l₂ := by
  induction l₁ generalizing l₂ with
  | nil => rw [List.nil_append] at hdup; assumption
  | cons hd tl ih =>
    inversion hdup
    apply ih; assumption

/- This theorem combines the various lemmas to give a complete
   characterization -/
theorem NoDup_Disjoint_app {α : Type} (l₁ l₂ : List α) :
    NoDup (l₁ ++ l₂) ↔
    (NoDup l₁ ∧ NoDup l₂ ∧ Disjoint l₁ l₂) := by
  apply Iff.intro
  . intro hdup
    constructor; exact NoDup_left _ _ _ hdup
    constructor; exact NoDup_right _ _ _ hdup
    exact NoDup_Disjoint _ _ _ hdup
  . intro ⟨h₁, ⟨h₂, h₃⟩⟩
    exact NoDup_append _ _ _ h₁ h₂ h₃
-- END SOLUTION
```

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
theorem mem_split (α : Type) (x : α) (l : List α) (hin : x ∈ l) :
    ∃ l₁ l₂, l = l₁ ++ x :: l₂ := by
  solution!
    induction l generalizing x with
    | nil => rw [List.mem_nil_iff] at hin; contradiction
    | cons hd tl ih =>
      rw [List.mem_cons] at hin
      cases hin with
      | inl hin => subst hin; exists []; exists tl
      | inr hin =>
        have ⟨l₁', ⟨l₂', ih⟩⟩ := ih x hin
        subst ih
        exists hd :: l₁'; exists l₂'
```
:::gradeTheorem 2 mem_split
:::

Now define a property `Repeats` such that `Repeats l` asserts
that `l` contains at least one repeated element.

```lean
inductive Repeats {α : Type} : List α → Prop where
  -- SOLUTION
  | rep_here  {x : α} {l : List α} (h : x ∈ l)     : Repeats (x :: l)
  | rep_later {x : α} {l : List α} (h : Repeats l) : Repeats (x :: l)
-- /SOLUTION
```

:::autogradedHole Repeats
:::

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

```lean
theorem pigeonhole_principle (α : Type) (l₁ l₂ : List α)
    (hin : ∀ x, x ∈ l₁ → x ∈ l₂)
    (hlen : l₂.length < l₁.length) :
    Repeats l₁ := by
  solution!
    induction l₁ generalizing l₂ with
    | nil =>
      rw [List.length_nil] at hlen
      apply Nat.not_lt_zero at hlen
      contradiction
    | cons x l₁' ih =>
      by_cases h : x ∈ l₁'
      . constructor; assumption
      . apply Repeats.rep_later
        have h₂ : x ∈ l₂ := by
          apply hin; rw [List.mem_cons]; left; rfl
        have ⟨l₂a, ⟨l₂b, heq⟩⟩ := mem_split _ _ _ h₂
        have hin₂ : ∀ x' : α, x' ∈ l₁' -> x' ∈ (l₂a ++ l₂b) := by
          intro x₀ hin₀
          have hneq : x ≠ x₀ := by
            intro heq; subst heq; apply h; assumption
          have h₁ : x₀ ∈ l₂ := by
            apply hin; rw [List.mem_cons]; right; assumption
          rw [heq, List.mem_append] at h₁; rcases h₁ with h₁ | h₁
          . rw [List.mem_append]; left; assumption
          . rw [List.mem_append]; right;
            rw [List.mem_cons] at h₁; rcases h₁ with h₁ | h₁
            . subst h₁; contradiction
            . assumption
        have hlen₂ : (l₂a ++ l₂b).length < l₁'.length := by
          have hlen' : l₂.length = (l₂a ++ l₂b).length + 1 := by
            rw [heq, List.length_append, List.length_append, List.length_cons, Nat.add_assoc]
          rw [hlen', List.length_append, List.length_cons] at hlen
          rw [List.length_append]
          apply succ_n_le_succ_m__n_le_m
          exact hlen
        apply ih (l₂a ++ l₂b) hin₂ hlen₂
    /-.
        destruct (EM (In x l1')) as [H | H].
        + /- In x l1' -/
          apply rep_here. apply H.
        + /- ~ In x l1' -/
          apply rep_later.
          assert (INX: In x l₂).
          {  apply INC. left. reflexivity. }
          destruct (in_split _ _ _ INX) as [l2a [l2b EQ]].
          remember (l2a ++ l2b) as l2' eqn:Heql2'.
          assert (IN2: forall x0 : α, In x0 l1' → In x0 l2').
          { intros x0 AI.
            assert (H0: x <> x0).
            { intros Heq. apply H. rewrite  Heq. apply AI. }
            assert (h₁: In x0 l₂).
            { apply INC. simpl. right. apply AI. }
            rewrite EQ in h₁. apply In_app_iff in h₁.
            rewrite Heql2'. apply In_app_iff.
            simpl in h₁. destruct h₁ as [h₁ | [h₁ | h₁]].
            - left. apply h₁.
            - exfalso. apply H0. apply h₁.
            - right. apply h₁.  }
          assert (LEN2: length l2' < length l1').
          { assert (LS: length l₂ = S(length (l2a ++ l2b))).
            { rewrite EQ.
              rewrite app_length. rewrite app_length. rewrite add_comm.
              simpl. rewrite add_comm. reflexivity. }
            rewrite LS in NR. rewrite <- Heql2' in NR. simpl in NR.
            apply Sn_le_Sm__n_le_m.  apply NR.
          }
          apply (IHl1' l2' IN2 LEN2).
  Qed. -/
```

:::gradeTheorem 6 pigeonhole_principle
:::

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
