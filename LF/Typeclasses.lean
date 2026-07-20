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
familiar with in other languages such as traits in Rust.

# First Example: Inhabited Types

Suppose we wanted to specify that a type has at least one inhabitant -- i.e.,
that it is not empty. We have previously seen `structure`, which would allow us to express
this as

```lean
structure HasOneStruct (α : Type) where
  one : α
```

As discussed previously, a structure is just an inductive type that comes with a single constructor, in this case {name}`HasOneStruct.mk`, along with a few different syntaxes for convenience:

```lean
def nat_hasOneStruct_mk : HasOneStruct Nat := HasOneStruct.mk 1

def nat_hasOneStruct_brace : HasOneStruct Nat := {one := 1}

def nat_hasOneStruct_where : HasOneStruct Nat where
  one := 1
```

All of these are the same value, a structure of type {InlineLean.lean}`HasOneStruct Nat` that we
can thing of as carrying a piece of data (a term that is not a proposition), the number `1`, as evidence that this type is not empty. We can use this in proofs such as

```lean
theorem nat_hasOneStruct_eq_one : nat_hasOneStruct_mk.one = 1 := rfl
```

to see how this structure provably contains the value that we have placed within it. In Lean, typeclasses work very similarly, and in fact are implemented as structures. The only difference in defining a typeclass is that we instead use the `class` keyword:

```lean
class HasOne (α : Type) where
  one : α
```

While the definition is essentially the same, including the constructor {name}`HasOne.mk`, the usage of typeclasses is different, and what allows us to use them to express ad hoc polymorphism. Instead of using `def` to define inhabitants of this type, we will instead use the `instance` keyword:

:::dev
From GitHub (@chenson2018): Part of the point here is that we don't usually refer to instances
explicitly, even me providing an explicit name is for pedagogy reasons. I'll make it more explicit
in the text that what we're looking for in the infoview is the presence of this instance.
:::

```lean
instance instHasOneNat : HasOne Nat where
  one := 1
```

The definition is exactly the same as above (and any of the alternative syntaxes work as well), but instead of being used as a definition that we pass around, Lean will try to infer its usage through a process called *typeclass synthesis* or *typeclass inference*. To help see this, let's define another instance of `HasOne` for {name}`Int`, the type of integers ... -2, -1, 0, 1, 2, ...

```lean
instance instHasOneInt : HasOne Int where
  one := -1
```

Instead of explicitly referring to a structure like we did in the proof {name}`nat_hasOneStruct_eq_one`, we can instead use {name}`HasOne.one`, and Lean will use typeclass inference to determine the intended meaning. As an example, you can write

```lean
example : HasOne.one = (1 : Nat) := rfl
example : HasOne.one = (-1 : Int) := rfl
```

and based on the type annotations Lean will infer which of these instances you intended to use. So these proofs are equivalent to

```lean
example : instHasOneNat.one = (1 : Nat) := rfl
example : instHasOneInt.one = (-1 : Int) := rfl
```

but without needing to explicitly refer to the instances {name}`instHasOneNat` and {name}`instHasOneInt`. Another way that we can inspect what instance is being using with the constructor of a typeclass is the option `pp.all`. For example looking at

```lean
set_option pp.all true in
example : HasOne.one = (1 : Nat) := rfl

set_option pp.all true in
example : HasOne.one = (-1 : Int) := rfl
```

we can see that {InlineLean.lean}`@HasOne.one Nat instHasOneNat` and {InlineLean.lean}`@HasOne.one Int instHasOneInt` are the respective terms that appear on the right hand side of each equality.

Lean also has a command `#synth` that allows you to search for an instance of a given type. So
the command

```lean
#synth HasOne Nat
```

for instance prints {name}`instHasOneNat`, informing us that this is the instance found that has type {InlineLean.lean}`HasOne Nat`. In general, the assumption is that for typeclasses like {name}`HasOne` that include data, as opposed to solely proofs, that these these instances should be unique to avoid ambiguity.

:::dev
@chenson2018: I don't really want to explain diamonds here, is the above white lie hand-waving okay??
:::

# Proof-Carrying Typeclasses

Notably, the above examples enforce no conditions on the data that they carry, and we could provide
any value that we would like for {name}`HasOne.one`. This could be misleading, for instance if we had instead defined an instance

```lean -keep
instance : HasOne Nat where
  one := 2
```

we might have some counterintuitive proofs based on the name leading us to believe the class contained the element `1`. In most languages that support typeclasses it
is not possible to enforce a notion of "lawfulness" as part of the typeclass, and it falls to
the author to ensure that any desired invariants are satisfied.

As an example, suppose that we
wanted to express the idea that a type has at least two distinct elements. A first attempt might be

```lean -keep
class HasTwoIncomplete (α : Type) where
  one : α
  two : α
```

but this does not disallow the case where `one` and `two` are equal. In a proof
assistant, however, typeclasses can also carry proofs along with data, so we can write

```lean
class HasTwo (α : Type) where
  one : α
  two : α
  one_neq_two : one ≠ two
```

to enforce that these are two distinct entries. Declaring instances works in much the same
way as before, except that now {name}`HasTwo.one_neq_two` requires a proof:

```lean
instance : HasTwo Nat where
  one := 1
  two := 2
  one_neq_two := by intro contra; contradiction
```

::::exercise (rating := 1) (name := "HasThree")
Following the pattern of {name}`HasOne` and {name}`HasTwo`, define a class `HasThree` that
specifies a type with at least three distinct elements.

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
  one_neq_two := solution!(by intro contra; contradiction)
  -- SOLUTION
  one_neq_three := solution!(by intro contra; contradiction)
  two_neq_three := solution!(by intro contra; contradiction)
  -- END SOLUTION
```
::::

# Notation Typeclasses

Another use for typeclasses, which may be familiar from other languages, is to overload a given piece
of syntax. To start, consider the (non-polymorphic) definition

:::dev
BCP: STOPPED READING HERE
:::

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

:::dev
@dsainati - The Verso compilation is not actually removing this from the generated file despite th e
-keep flag. It is, however, stripping the message guard, so this results in an error. Once
we figure out how we are handling these cases, uncomment this.

```lean -keep
/--
error: failed to synthesize instance of type class
  BEq α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def List.elem_poly {α : Type} (a : α) (xs : List α) : Bool :=
  match xs with
  | [] => false
  | b :: tl => bif a == b then true else elem_poly a tl
```
:::

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

Maps (or dictionaries) are ubiquitous data structures both in ordinary programming and in the theory of programming languages; we're going to need them in many places in the coming chapters.

We'll define two flavors of maps: total maps, which include a "default" element to be returned when a key being looked up doesn't exist, and partial maps, which instead return an option to indicate success or failure. Partial maps are defined in terms of total maps, using None as the default element.

## Identifiers

To define maps, we first need a type for the keys that we will use to index into our maps. Instead of using concrete types, we will use a type variables

```lean
universe u v
variable {α : Type u} {β : Type v} [BEq α] [ReflBEq α] [LawfulBEq α]
```

where `α` is the type of our map keys and `β` the corresponding values. Looking at {name}`ReflBEq` and {name}`LawfulBEq`, we see that these typeclasses:

```
/-- `ReflBEq α` says that the `BEq` implementation is reflexive. -/
class ReflBEq (α) [BEq α] : Prop where
  /-- `==` is reflexive, that is, `(a == a) = true`. -/
  protected rfl {a : α} : a == a

/--
A Boolean equality test coincides with propositional equality.

In other words:
 * `a == b` implies `a = b`.
 * `a == a` is true.
-/
class LawfulBEq (α : Type u) [BEq α] : Prop extends ReflBEq α where
  /-- If `a == b` evaluates to `true`, then `a` and `b` are equal in the logic. -/
  eq_of_beq : {a b : α} → a == b → a = b
```

provide the assumption that we have an boolean equality (`==`) on our keys that is reflexive and coincides with proposition equality `=`.

## Total Maps

Our main job in this chapter will be to build a definition of partial maps that is similar in behavior to the one we saw in the Lists chapter, plus accompanying lemmas about its behavior.

This time around, though, we're going to use functions, rather than lists of key-value pairs, to build maps. The advantage of this representation is that it offers a more "extensional" view of maps: two maps that respond to queries in the same way will be represented as exactly the same function, rather than just as "equivalent" list structures. This simplifies proofs that use maps.

We build up to partial maps in two steps. First, we define a type of total maps that return a default value when we look up a key that is not present in the map.

```lean
def TotalMap (α : Type u) (β : Type v) := α → β

namespace TotalMap
```

Intuitively, a total map over an element type `β` is just a function that can be looked up using a corresponding `a : α`.

In order to declare a default value of `β` we will use the {name}`Inhabited` typeclass, which is the standard library's implementation of our {name}`HasOne` example from above:

```lean
variable [Inhabited β]
```

The function `TotalMap.empty` yields an empty total map, given a default element; this map always returns the default element when applied to any string.

```lean
def empty : TotalMap α β := fun _ ↦ default
```

and we'll also declare an instance

```lean
instance : EmptyCollection (TotalMap α β) where
  emptyCollection := TotalMap.empty
```

so that we can use the `∅` notation for this empty map. We'll also declare the instance

```lean
instance : GetElem (TotalMap α β) α β (fun _ _ => True) where
  getElem m a _ := m a

theorem getElem_def (m : TotalMap α β) (a : α) : m[a] = m a :=
  rfl
```

which allows us to use the notation `m[a]` to access elements of a map `m`.

More interesting is the map-updating function, which (as always) takes a map `m`, a key `a`, and a value `b` and returns a new map that takes `a` to `b` and takes every other key to whatever `m` does. The novelty here is that we achieve this effect by wrapping a new function around the old one.

```lean
def update (m : TotalMap α β) (a : α) (b : β) : TotalMap α β :=
  fun a' => bif a == a' then b else m[a']
```

This definition is a nice example of higher-order programming: {name}`update` takes a function `m` and yields a new function `fun x' ↦ ...` that behaves like the desired map.

For example, we can build a map taking {name}`String` to {name}`Bool`, where `"foo"` and `"bar"` are mapped to {name}`true` and every other key is mapped to {name}`false`, like this:

```lean
def example_map :=
  (∅ : TotalMap String Bool)
    |>.update "foo" true
    |>.update "bar" true
```

We'll also introduce a notation for updating maps

```lean
notation a " →ₜ " b " ; " m => TotalMap.update m a b
```

The `examplemap` above can now be defined as follows:

```lean
def examplemap' : TotalMap String Bool := "bar" →ₜ true ; "foo" →ₜ true ; ∅
```

When we use maps in later chapters, we'll need several fundamental facts about how they behave.

Even if you don't work the following exercises, make sure you thoroughly understand the statements of the lemmas!

(Some of the proofs require the functional extensionality axiom, which was discussed in the Logic chapter.)

```lean
theorem update_eq (m : TotalMap α β) (a : α) (b : β) : (a →ₜ b ; m)[a] = b := by
  unfold update
  rewrite [getElem_def, ReflBEq.rfl, cond_true]
  rfl
```

:::dev
exercises here...
:::

## Notation for Concrete Maps

Wouldn't it be nice if we could use a more natural notation for concrete maps like `{ "bar" ↦ true, "foo" ↦ true }`?
To accomplish this we define a simple structure that consists of a key and a value along with `↦` notation for it.

```lean
/--
A key-value pair with `↦` syntax.
-/
@[ext]
structure KVPair (K : Type u) (V : Type v) where
  key : K
  value : V

namespace KVPair
scoped notation k " ↦ " v => KVPair.mk k v
end KVPair

open scoped KVPair
```

Next, we declare `Insert` and `Singleton` instances which control the `{}` notation in lean.

```lean
instance : Insert (KVPair α β) (TotalMap α β) where
  insert kv m := kv.key →ₜ kv.value ; m

instance : Singleton (KVPair α β) (TotalMap α β) where
  singleton kv := insert kv ∅

instance : LawfulSingleton (KVPair α β) (TotalMap α β) where
  insert_empty_eq _ := rfl
```

:::dev
xhalo32: Should we explain why `example : ({ "foo" ↦ true })["foo"]! = true := rfl` doesn't work (the collection that has Insert and GetElem is ambiguous)?
:::

Here are a couple of examples using the new notation:

```lean
example : ({ "bar" ↦ true, "foo" ↦ true }) = "bar" →ₜ true ; "foo" →ₜ true ; ∅ := rfl

example : ({ "foo" ↦ true } : TotalMap String Bool)["foo"]! = true := rfl

example : ({ 1 ↦ 2, 1 ↦ 3 } : TotalMap Nat Nat)[1]! = 2 := rfl
```

## Partial Map

:::dev
rest of section here...
:::

# Reflection

:::dev
I think this will still exist in previous chapters, just not have the reflection explanations until
here? Since I can't import these yet, just placing here at the top of this section -- CGH
Burtonpatel: These definitions of even as boolean computation and Prop should go below, after the table where we explain the difference.
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
:::dev
dsainati12 days ago
We use regular if for the first time here. It is probably necessary to explain at this point what if is and how it differs from bif.

👍
1
berberman1 day ago
Should we clarify the difference between = and ==? Observably if and bif can possibly accept both as the condition because of Coe or DecidableEq instances, which IMO could be confusing.

Probably we can talk a bit about the coercion system in this file as well, since Coe could be an example of typeclasses, so long as if we ignore the outParam thing...

chenson20181 day ago
I definitely intended for this to cover = versus ==. Maps uses LawfulBEq (which says = and == coincide). If that will now appear here it's a good place to give some more detail?

rogerburtonpatel1 day ago
I think right after this part on decidability is good. It's a hefty chunk of information already, so keeping distinct ideas distinct is more likely than not a good call.
:::

:::dev
@dsainati - commenting this out for the same reason as above

```lean -keep +error
def eq {α : Type} (a₁ a₂ : α) : Bool := if a₁ = a₂ then true else false
```
:::

Lean will complain here that it cannot find an instance of {name}`Decidable`. This typeclass

:::dev
@dsainati - commenting this out because the -keep doesn't work during extraction;
this causes Lean to get the two instances (the real one and this one) confused

```lean -keep
class inductive Decidable (p : Prop) where
  /-- Proves that `p` is decidable by supplying a proof of `¬p` -/
  | isFalse (h : Not p) : Decidable p
  /-- Proves that `p` is decidable by supplying a proof of `p` -/
  | isTrue (h : p) : Decidable p
```
:::

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

This is only half the story however: while Lean's core theory enables this computation, Lean is
also often used in applications where we don't care about computability, such as pure mathematics.
In particular, it is possible to write a function for arbitrary equality:

```lean -keep
open scoped Classical in
noncomputable def eq {α : Type} (a₁ a₂ : α) := if a₁ = a₂ then true else false

set_option pp.all true in
#print eq
```

But we have indicated to Lean, using the `noncomputable` keyword and `Classical` namespace
that we are _not_ interested in computation.
What is happening in the background is that this allows
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

:::dev
Burtonpatel: Some more examples would be good. It might be good to start with Nat and then move to the Indprop ones. This is a short chapter, so 5-6 well-chosen, informative exercises could easily fit.
:::
