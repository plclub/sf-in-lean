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

set_option autoImplicit false

open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "Typeclasses" =>
%%%
htmlSplit := .never
file := "Typeclasses"
%%%


So far we have discussed *parametric polymorphism*, where in Lean we can declare a type variable

```lean
variable (α : Type)
```

without any further information about the details of the type `α`. Here we are able to work
with a type like {InlineLean.lean}`List α`, and can write functions like {name}`List.reverse` or
{name}`List.length` that only operate on the structure of a list independently of its contents.
Along with these we have corresponding proofs like {name}`List.length_reverse` that are similarly
structural in nature.

This is somewhat limiting, as we cannot inspect or non-trivially use any particular `a : α`. What we
might want in some situations rather than `α` being completely generic is to partially specify its
behavior. In Lean, this happens through a form of "ad hoc polymorphism" called *typeclasses*. This
concept originated in the Haskell programming language, and is analogous to features you may be
familiar with in other languages such as traits in Rust or interfaces in Java.

# First Example: Inhabited Types

Suppose we wanted to specify that a type has at least one inhabitant, in other words a non-empty
type. In Lean, we could express this as the typeclass

```lean
class HasOne (α : Type) where
  one : α
```

which explicitly carries an element `one : α` as a witness of non-emptiness. After defining this
typeclass, we can now provide *instances* that show it is satisfied for a particular type. As an
example, we could declare an instance

```lean
instance instHasOneNat : HasOne Nat where
  one := 1
```

which is evidence that {name}`Nat` has some inhabitant. We could do the same thing with integers

```lean
instance instHasOneInt : HasOne Int where
  one := -1
```

Now when you refer to {name}`HasOne.one` in a proof, Lean will use *typeclass inference* to
determine the intended meaning. As an example, you can write

```lean
example : HasOne.one = (1 : Nat) := rfl
example : HasOne.one = (-1 : Int) := rfl
```

and based on the type annotations Lean will infer which of these instances you intended to use.
When in doubt, you can also use the option `pp.all`


```lean
set_option pp.all true in
example : HasOne.one = (1 : Nat) := rfl

set_option pp.all true in
example : HasOne.one = (-1 : Int) := rfl
```

which allows you to see the name of the instance that is being used with {name}`HasOne.one`. We can
also check for the existence of a typeclass instance using the `#synth` command

```lean
#synth HasOne Nat
```

# Proof Carrying Typeclasses

:::dev
I say data to mean "not in `Prop`", is that a Lean-ism that's been explained? --CGH
:::

Notably the above examples enforce no conditions on the data that they carry, and we could provide
any value that we would like for {name}`HasOne.one`. In most languages that support typeclasses it
is not possible to enforce a notion of "lawfulness" as part of the typeclass, and it falls to
the author to ensure that any desired invariants are satisfied. As an example, suppose that we
wanted to express the idea that a type has at least two distinct elements. A first attempt might be

```lean -keep
class HasTwo (α : Type) where
  one : α
  two : α
```

but this does not disallow the case where `one` and `two` are equal. In a proof
assistant however, typeclasses can also carry proofs along with data, so that we can write

```lean
class HasTwo (α : Type) where
  one : α
  two : α
  one_neq_two : one ≠ two
```

which enforces that these are two distinct entries. Declaring instances works in much the same
way, except that now {name}`HasTwo.one_neq_two` requires a proof:

:::dev
I'm not actually sure of the preferred way to prove `1 ≠ 2` at this point in the book -- CGH
:::

```lean
instance : HasTwo Nat where
  one := 1
  two := 2
  one_neq_two := by simp
```

::::exercise (rating := 1) (name := "HasThree")
Following the pattern of {name}`HasOne` and {name}`HasTwo`, define a class `HasThree` that
specifies a type with (at least) three distinct elements.

```lean
class HasThree (α : Type) where
  one : α
  two : α
  three : α
  one_neq_two : one ≠ two
  -- SOLUTION
  one_neq_three : one ≠ three
  two_neq_three : two ≠ three
  -- END SOLUTION
```
::::

::::exercise (rating := 1) (name := "instHasThree")
Provide an instance of {name}`HasThree` for {name}`Nat`.

```lean
instance : HasThree Nat where
  one := 1
  two := 2
  three := 3
  one_neq_two := solution!(by simp)
  one_neq_three := solution!(by simp)
  two_neq_three := solution!(by simp)
```
::::

# Notation Typeclasses

Another use for typeclasses that may be familiar from other languages is to overload a given piece
of syntax. To start, consider the (non-polymorphic) definition

```lean
@[irreducible]
def List.elem_nat (a : Nat) (xs : List Nat) : Bool :=
  match xs with
  | [] => false
  | b :: tl => bif a == b then true else elem_nat a tl

unseal List.elem_nat in
theorem List.elem_nat_nil (a : Nat) : [].elem_nat a = false := rfl

unseal List.elem_nat in
theorem List.elem_nat_cons (a b : Nat) (xs : List Nat) :
    (b :: xs).elem_nat a = bif a == b then true else elem_nat a xs := rfl
```

This function takes a natural number `a` and a list of natural numbers `xs`, then returns a
{name}`Bool` indicating if `a` occurs within `xs`. For example:

```lean
#eval [0, 1].elem_nat 0
#eval [0, 1].elem_nat 1
#eval [0, 1].elem_nat 2
```

If we wanted to construct a polymorphic version of this, how would we proceed? If we try to simply
replace {name}`Nat` with a type variable `α`, we get a somewhat mysterious error

```lean -keep +error
def List.elem_poly {α : Type} (a : α) (xs : List α) : Bool :=
  match xs with
  | [] => false
  | b :: tl => bif a == b then true else elem_poly a tl
```

that mentions a typeclass {name}`BEq`. Perhaps a better question is what exactly the `==` notation
meant in our original {name}`List.elem_nat`. Let's look at a usage of this notation with natural
numbers, but turn off notation:

```lean
/-- info: BEq.beq 1 2 : Bool -/
#guard_msgs in
set_option pp.notation false in
#check 1 == 2
```

This may be a bit surprising, as you may have been expecting to see {name}`Nat.beq`, the function
for boolean equality on natural numbers. What we instead find is that `==` is a notation for the
typeclass {name}`BEq`:

```
class BEq (α : Type u) where
  /-- Boolean equality, notated as `a == b`. -/
  beq : α → α → Bool
```

What is happening in the background when we use the `a == b` notation is that Lean is searching
for an _instance_ of the `BEq` typeclasses that applies for `Nat`. An example of such an instance
would be

```lean
instance (priority := low) : BEq Nat where
  beq := Nat.beq
```

where we are specifying that the usage of `==` for natural numbers should correspond to the
expected `Nat.beq`. So in order to write a function that uses the notation for boolean equality over
a generic type, we need a way to express that there is some instance for {InlineLean.lean}`BEq α`.
This is done using *instance implicits*, where we place a desired typeclass assumption in square
brackets. Our corrected definition is then

```lean
@[irreducible]
def List.elem_poly {α : Type} [BEq α] (a : α) (xs : List α) : Bool :=
  match xs with
  | [] => false
  | b :: tl => bif a == b then true else elem_poly a tl

unseal List.elem_poly in
theorem List.elem_poly_nil [BEq α] (a : α) : [].elem_poly a = false := rfl

unseal List.elem_poly in
theorem List.elem_poly_cons [BEq α] (a b : α) (xs : List α) :
    (b :: xs).elem_poly a = bif a == b then true else elem_poly a xs := rfl
```

where Lean can now infer the usage of `==` is the one that we have provided.

::::exercise (rating := 1) (name := "List.elem_poly_eq_elem_nat")
Prove that {name}`List.elem_poly` agrees with {name}`List.elem_nat` when specialized to
natural numbers.

```lean
theorem List.elem_poly_eq_elem_nat (xs : List Nat) (n : Nat) : xs.elem_poly n = xs.elem_nat n := by
  solution!(
  induction xs with
  | nil =>
    rewrite [List.elem_poly_nil, List.elem_nat_nil]
    rfl
  | cons hd tl ih =>
    rewrite [List.elem_poly_cons, List.elem_nat_cons, ih]
    rfl)
```
::::

# Maps

:::dev
Maps could go here as an example to reinforce this? Or maybe that's too long of an aside? The code
exists (with limited prose) in `Maps.lean` already. --CGH
:::

# Reflection

:::dev
I think this will still exist in previous chapters, just not have the reflection explanations until
here? Since I can't import these yet, just placing here at the top of this section -- CGH
:::

```lean
namespace Nat

@[irreducible]
def isEven : Nat → Bool
| 0 => true
| 1 => false
| n + 2 => isEven n

@[irreducible]
def double : Nat → Nat
| 0 => 0
| n + 1 => double n + 2

section

unseal isEven
unseal double

theorem isEven_zero : isEven 0 = true := rfl
theorem isEven_one : isEven 1 = false := rfl
theorem isEven_succ_succ (n : Nat) : isEven (n + 2) = isEven n := rfl

theorem double_zero : double 0 = 0 := by rfl
theorem double_succ (n : Nat) : double (n + 1) = double n + 2 := rfl

end

def Even (n : Nat) := ∃ m, n = double m

theorem isEven_succ (n : Nat) : isEven (n + 1) = ! isEven n := by
  induction n with
  | zero =>
    rewrite [Nat.zero_add, isEven_zero, isEven_one]
    rfl
  | succ n ih =>
    rewrite [isEven_succ_succ, ih, Bool.not_not]
    rfl
```

We've seen two different ways of expressing logical claims in Lean: with booleans (of type
{name}`Bool`), and with propositions (of type {InlineLean.lean}`Prop`).

Here are the key differences between `Bool` and `Prop`:

:::table +header (align := center)
*
  * ⠀
  * `Bool`
  * `Prop`
*
  * decidable?
  * yes
  * no
*
  * useable with `match`?
  * yes
  * no
*
  * works with {tactic}`rewrite` tactic?
  * no
  * yes
:::

The crucial difference between the two worlds is decidability. Every (closed) Lean expression of
type `Bool` can be simplified in a finite number of steps to either `true` or `false` -- i.e., there
is a terminating mechanical procedure for deciding whether or not it is true.

This means that, for example, the type `Nat → Bool` is inhabited only by functions that, given a
`Nat`, always yield either `true` or `false` in finite time; and this, in turn, means (by a standard
computability argument) that there is no function in `Nat → Bool` that checks whether a given number
is the code of a terminating Turing machine.

By contrast, the type `Prop` includes both decidable and undecidable mathematical propositions; in
particular, the type `Nat → Prop` does contain functions representing properties like
"the nth Turing machine halts." The second row in the table follows directly from this essential
difference. To evaluate a pattern match (or conditional) on a boolean, we need to know whether the
scrutinee evaluates to `true` or `false`; this only works for `Bool`, not `Prop`.

The third row highlights an important practical difference: equality functions like {name}`Nat.beq`
that return a boolean cannot be used directly to justify rewriting with the rewrite tactic;
propositional equality is required for this. Since `Prop` includes both decidable and undecidable
properties, we have two options when we want to formalize a property that happens to be decidable:
we can express it either as a boolean computation or as a function into Prop.

As an example, we can write

```lean
unseal isEven in
example : isEven 42 := rfl
```

or that there exists some `k` such that `42 = double k`.

```lean
unseal double in
example : Even 42 := by exists 21
```

Of course, it would be deeply strange if these two characterizations of evenness did not describe
the same set of natural numbers!

Fortunately, they do! To prove this, we first need two helper lemmas.

```lean
theorem even_double (k : Nat) : isEven (double k) = true := by
  induction k with
  | zero =>
    rewrite [double_zero, isEven_zero]
    rfl
  | succ n ih =>
    rewrite [double_succ, isEven_succ_succ]
    exact ih
```

::::exercise (rating := 3) (name := "isEven_double_exists")

```lean
theorem  isEven_double_exists (n : Nat) :
    ∃ k, n = bif isEven n then double k else double k + 1 := by solution!(
  induction n with
  | zero =>
    exists 0
    rewrite [isEven_zero]
    dsimp only [cond_true]
    symm
    exact double_zero
  | succ n ih =>
    obtain ⟨k, ih⟩ := ih
    rewrite [isEven_succ]
    by_cases h : isEven n
    · exists k
      rewrite [h] at ih ⊢
      subst ih
      rfl
    · exists k + 1
      rewrite [Bool.not_eq_true] at h
      rewrite [h] at ih ⊢
      subst ih
      rewrite [cond_false, Bool.not_false, cond_true, double_succ]
      rfl)
```
::::

Now the main theorem:

```lean
theorem isEven_iff_Even {n : Nat} : isEven n = true ↔ Even n where
  mp h := by
    have ⟨k, hk⟩ := isEven_double_exists n
    rewrite [h, cond_true] at hk
    subst hk
    exists k
  mpr h := by
    obtain ⟨k, hk⟩ := h
    subst hk
    exact even_double k
```

In view of this theorem, we can say that the boolean computation even n is reflected in the truth of
the proposition `∃ k, n = double k`.

 Similarly, to state that two numbers n and m are equal, we can say either
 * that `n == m` returns `true`
 * that `n = m`

 Again, these two notions are equivalent:

:::dev
This proof is from the typeclass version, which makes more sense if maps are included --CGH
:::

 ```lean
 example (n₁ n₂ : Nat) : n₁ == n₂ ↔ n₁ = n₂ := beq_iff_eq
 ```

So what should we do in situations where some claim could be formalized as either a proposition or a boolean computation? Which should we choose?

In general, both can be useful. Which we choose has to do with the _computational_ nature of Lean's
core language, which is designed so that every function it expresses is total, and by default
computable unless we explicit indicate otherwise. As an example, consider
trying to write a function `α → α → Bool` checking for equality on an arbitrary type:

```lean -keep +error
def eq {α : Type} (a₁ a₂ : α) : Bool := if a₁ = a₂ then true else false
```

Lean will complain here that it cannot find an instance of {name}`Decidable`. This typeclass

```lean -keep
class inductive Decidable (p : Prop) where
  /-- Proves that `p` is decidable by supplying a proof of `¬p` -/
  | isFalse (h : Not p) : Decidable p
  /-- Proves that `p` is decidable by supplying a proof of `p` -/
  | isTrue (h : p) : Decidable p
```

is the way that we express in Lean that a given proposition is decidable. This is the generalization
of our observation that {name}`isEven_iff_Even` was reflecting a proof between boolean and
propositional equality. In fact, we can use this theorem to directly construct a {name}`Decidable`
instance

```lean
instance (n : Nat) : Decidable (Even n) := decidable_of_decidable_of_iff isEven_iff_Even
```

Now we are able to complete such proofs by computation using the {tactic}`decide` tactic:

```lean
section
unseal isEven

example : Even 2 := by decide
example : Even 4 := by decide
example : Even 6 := by decide
example : Even 100 := by decide
example : Even 1000 := by decide +kernel
example : ¬ Even 101 := by decide
example : ∀ n < 10, Even (2 * n) := by decide
example : ∀ n < 10, Even (2 * n) ∧ ¬ Even (2 * n + 1) := by decide
end
```

In general, Lean will try to use typeclass synthesis with {name}`Decidable` in order to determine
when it is appropriate to use `Prop` and `Bool` interchangeably. For instance, while our example
`eq` failed above while trying to use propositional equality `=` in the condition of an `if`
statement, we are allowed to write

```lean
def nat_eq (m n : Nat) : Bool := if m = n then true else false
```

Why is this allowed? It is precisely because equality of natural numbers is decidable, and Lean
makes use of this fact. If we print this definition with notation unset, we would find that it
is using {name}`instDecidableEqNat`

```lean
set_option pp.all true in
#print nat_eq
```

which proves that this equality is decidable.

This is only half the story however, as while Lean's core theory enables this computation, Lean is
also often used in applications where we don't care about computability. In particular, it is
possible to write a function a function for arbitrary equality

```lean -keep
open scoped Classical in
noncomputable def eq {α : Type} (a₁ a₂ : α) := if a₁ = a₂ then true else false

set_option pp.all true in
#print eq
```

but we have indicated to Lean using the `noncomputable` keyword and `Classical` namespace
that we are not interested in computation. What is happening in the background is that this allows
typeclass synthesis to find the scoped instance {name}`Classical.propDecidable`, which makes use of
the axiom of choice to provide a proof that all propositions are _classically_ decidable. This
sort of definition is suitable for use with proofs, but is not allowed to be used in conjunction
with computational features of Lean such as the {tactic}`decide` tactic or the `#eval` command.


# TODO

:::dev
Below are some stray examples from IndProp. `Decidable` only carries the proposition and not the
boolean, so one direction of `reflect_iff` is easily translated, but the other is a bit different.
I list some theorems below but you should Loogle and see if that's what you want. Some the the
proofs can be a bit advanced if you follow core, or otherwise a bit circular. -- CGH
:::

```lean
#check decidable_of_bool

example {P : Prop} (b : Bool) (h : b = true ↔ P) : Decidable P := by
  by_cases hb : b
  · apply isTrue
    simp [← h, hb]
  · apply isFalse
    simp [← h, hb]
```

```lean
#check decide_eq_false_iff_not
#check decide_eq_true_iff
```

:::dev
I'm not sure what part of the signature here is important to translate. Is the point the
`Bool`/`Prop` mismatch? -- CGH
:::

```lean
example (a : α) [BEq α] [LawfulBEq α] (xs : List α) (neq : xs.filter (a == ·) ≠ []) : a ∈ xs := by
  sorry
```
