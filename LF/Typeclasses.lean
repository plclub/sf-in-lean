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
tag := "Typeclasses"
%%%

Chapter {ref "Poly"}[Poly] introduced *parametric polymorphism*, declaring a type variable with no
constraint on it.

:::dev "Michael Hicks (mwhicks1)"
Students will run across universes, though. When looking at List lemmas, for example, they will see things like:
```
List.reverse.{u} {α : Type u} (as : List α) : List α
```
Are we explaining these things somewhere, maybe in Poly ?
:::
:::dev "Benjamin Pierce (bcpierce00)"
Yes, in Poly!
:::


This lets us work with a type like `List α`, writing functions like
{name}`List.reverse` and {name}`List.length` and proofs like {name}`List.length_reverse`, which use
only the list's structure and never inspect any particular `a : α`.

Sometimes, though, we want less freedom: rather than leaving `α` completely generic, we want to
partially specify its behavior. In Lean, this is done through a form of "ad hoc polymorphism" called
*typeclasses*. The concept originated in Haskell and is analogous to features you may know from
other languages, such as traits in Rust.

# Why We Need Typeclasses

Consider the following function, which checks whether a natural number occurs in a list:

```lean
def List.elem_nat (a : Nat) (xs : List Nat) : Bool :=
  match xs with
  | [] => false
  | b :: tl => bif a == b then true else elem_nat a tl

theorem List.elem_nat_nil (a : Nat) : [].elem_nat a = false := rfl

theorem List.elem_nat_cons (a b : Nat) (xs : List Nat) :
    (b :: xs).elem_nat a = bif a == b then true else elem_nat a xs := rfl
```

```lean
#eval [0, 1].elem_nat 0
#eval [0, 1].elem_nat 1
#eval [0, 1].elem_nat 2
```

What if we want this to work for lists of _any_ element type, not just {name}`Nat`? Parametric
polymorphism suggests simply replacing {name}`Nat` with a type variable `α`, but that produces a puzzling
error:

```lean -keep +error (name := elem_poly_error)
def List.elem_poly {α : Type} (a : α) (xs : List α) : Bool :=
  match xs with
  | [] => false
  | b :: tl => bif a == b then true else elem_poly a tl
```

```leanOutput elem_poly_error
failed to synthesize instance of type class
  BEq α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

Lean is trying to use typeclasses to work out how `==` should behave on a value of type `α`.
We'll see exactly why shortly; for now, here's one way to sidestep the problem: have the
caller supply the equality test to use.

```lean
def List.elem_poly_eq {α : Type} (eq : α → α → Bool) (a : α) (xs : List α) : Bool :=
  match xs with
  | [] => false
  | b :: tl => bif eq a b then true else elem_poly_eq eq a tl

#eval [0, 1].elem_poly_eq Nat.beq 0
```

This works, but it's tedious: every caller has to know, and remember to supply, the right equality
function.

Typeclasses automate this — instead of the programmer passing the function
explicitly, Lean searches for one and provides it on its own. We specify something we want
Lean to search for by declaring a `class` with the needed function as a field; a `class` is like
an interface in Java or a trait in Rust. Particular implementations of that class
are called _instance_; each type can have its own instance of a class. For functions that would
use such instances, we specify
the name of the class in a _instance implicit_ on the polymorphic variable that the
instance's function applies to. This directs Lean to rely on the class inside the function, and to
find and fill in the appropriate instance when the function is called.

Here is what this looks like for `List.elem_poly`:
```lean
def List.elem_poly {α : Type} [BEq α] (a : α) (xs : List α) : Bool :=
  match xs with
  | [] => false
  | b :: tl => bif a == b then true else elem_poly a tl

theorem List.elem_poly_nil {α : Type} [BEq α] (a : α) : [].elem_poly a = false := rfl

theorem List.elem_poly_cons {α : Type} [BEq α] (a b : α) (xs : List α) :
    (b :: xs).elem_poly a = bif a == b then true else elem_poly a xs := rfl

#eval [0, 1].elem_poly 0
```
Comparing {name}`List.elem_poly_eq` with {name}`List.elem_poly`, we see three differences.
First, {name}`List.elem_poly_eq` takes an _explicit_ parameter `eq`,
whereas {name}`List.elem_poly` specifies an instance implicit `[BEq α]`. The instance implicit
indicates that an instance of {name}`BEq` must be provided at
call sites for the particular type `α` that is used.
Second, whereas {name}`List.elem_poly_eq` invokes parameter `eq` to test equality,
{name}`List.elem_poly` uses `==` instead. As {ref "Lists"}[Lists] noted when we first used it,
`==` on {name}`Nat` comes from the {name}`BEq` typeclass.
Finally, whereas {lean}`[0, 1].elem_poly_eq Nat.beq 0` passes the equality
function {name}`Nat.beq` explicitly, in {lean}`[0, 1].elem_poly 0` Lean fills it in
automatically based on the type {name}`Nat` of the {name}`List`.

:::dev "xhalo32"
This is technically incorrect, the instance `BEq Nat`, which comes from `DecidableEq`, does not contain `Nat.beq`. You can see in proofs of `List.elem_nat` versus `List.elem_poly_eq` versus `List.elem_poly` and how `Nat.beq` and `==` play different roles.
:::

Going back to the earlier version of {name}`List.elem_poly`, without the instance implicit, we
can now understand the error message: `α` was fully generic
— so the `==` in its body would have needed to work for _every_ type `α`, and no
single {name}`BEq` instance can do that. So Lean's search failed.

Now it is time to dig into the details of what we have seen so far.
We'll see exactly how `[BEq α]` gets filled in below, starting with how
to define a typeclass in the first place.

# Defining Your Own Typeclasses

`BEq` comes from Lean's standard library. Let's define a typeclass of our own, to see the
mechanism — classes, instances, and synthesis — that made `==` resolve automatically above.

Suppose we want a function that returns the first element of a list, defaulting to a
given value if the list is empty. As with {name}`List.elem_poly_eq` above, here is a version
that makes the default value an explicit parameter:

```lean
def List.headOr_ex {α : Type} (defaultValue : α) (xs : List α) : α :=
  match xs with
  | [] => defaultValue
  | hd :: _ => hd

#eval [1, 2, 3].headOr_ex 0
#eval ([] : List Nat).headOr_ex 0
```

This works, but again it's tedious: every caller has to supply an element of `α` to default to, even when there's an obvious choice based on the type of the things in the list, like {lean}`0` for {name}`Nat`.

Getting Lean to fill in `defaultValue` automatically takes two things. One is marking the parameter as
"searchable," rather than something the caller always supplies explicitly. The other is giving Lean
some information about what it should search _for_.

Considering the second problem first: the way to provide this information is to _name_ the data we're
after — the *default value* of a type. In particular, a `structure` (chapter {ref "Lists"}[Lists]) is a
good way to give this information a name; structures can also bundle together more than one
piece of data, which will come in handy later, though we only need a single field here.

To address the first problem, we need to mark this particular structure as one Lean should search
for automatically — not every `structure`-typed argument should be.

Let's build up to what we want in two steps: first the naming, as a plain `structure`; then the marking, by
upgrading it to a `class`. Here's the structure — we'll put it in its own namespace so we can reuse
the name `DefaultValue` for the class version below:

```lean
namespace DefaultValueScratch

structure DefaultValue (α : Type) where
  value : α
```

A value of type {lean}`DefaultValue Nat` picks out a particular {name}`Nat` to serve as the type's default:
it's built the same way any structure is, by supplying a {name}`Nat` for the `value` field:

```lean
def natDefault : DefaultValue Nat where
  value := 0

end DefaultValueScratch
```

Now for the marking: we need to tell Lean that `DefaultValue` is the sort of structure it should
search for automatically, the way it needs to for {name}`List.headOr_ex`'s `defaultValue` argument.
We do this by writing `class` in place of `structure`:

```lean
class DefaultValue (α : Type) where
  value : α
```

We then provide values of this type a bit differently. Instead of `def`, we use `instance`:

```lean
instance instDefaultValueNat : DefaultValue Nat where
  value := 0
```

Lean can now find this instance on its own, via _typeclass synthesis_ (or _typeclass inference_) —
the same process that found {lean}`BEq Nat` earlier. That means we can rewrite {name}`List.headOr_ex`
the same way we rewrote {name}`List.elem_poly_eq` into {name}`List.elem_poly` above, replacing the
explicit `defaultValue` parameter with an instance implicit:

```lean
def List.headOr {α : Type} [DefaultValue α] (xs : List α) : α :=
  match xs with
  | [] => DefaultValue.value
  | hd :: _ => hd

#eval [1, 2, 3].headOr
#eval ([] : List Nat).headOr
```

```lean
example : DefaultValue.value = (0 : Nat) := by rfl
```

Notice that we refer to {name}`DefaultValue.value` alone, with no instance named. Because the
expression equates `DefaultValue.value` with the {name}`Nat` {lean}`0`, Lean selects {name}`instDefaultValueNat`,
the instance for
{lean}`DefaultValue Nat`. We know this because we are able to
prove that {name}`DefaultValue.value` is equal to {lean}`0`.

Let's declare a second instance, for {name}`Int`, the type of integers `... -2, -1, 0, 1, 2, ...`:

```lean
instance instDefaultValueInt : DefaultValue Int where
  value := -1
```

We can also create instances for polymorphic types, like `Option α`, whose default is `none`,
by giving the instance declaration a parameter:

```lean
instance instDefaultValueOption {α : Type} : DefaultValue (Option α) where
  value := none
```

Now, Lean can infer instances for all these types, including inside {name}`List.headOr`:

```lean
example : DefaultValue.value = (0 : Nat) := by rfl
example : DefaultValue.value = (-1 : Int) := by rfl
example : DefaultValue.value = (none : Option Bool) := by rfl
example : DefaultValue.value = (none : Option (List Nat)) := by rfl
example : ([] : List Nat).headOr = 0 := by rfl
example : ([] : List Int).headOr = -1 := by rfl
example : ([] : List (Option Bool)).headOr = none := by rfl
example : ([] : List (Option Bool)).headOr = none := by rfl
```

Synthesis infers instances we could have specified explicitly:

```lean
example : instDefaultValueNat.value = (0 : Nat) := by rfl
example : instDefaultValueInt.value = (-1 : Int) := by rfl
example : instDefaultValueOption.value = (none : Option Nat) := by rfl
```

The option `pp.all` shows which instance Lean picked:

```lean (name := ppAllNat)
set_option pp.all true in
#check (DefaultValue.value : Nat)
```

```leanOutput ppAllNat
@DefaultValue.value Nat instDefaultValueNat : Nat
```

```lean (name := ppAllInt)
set_option pp.all true in
#check (DefaultValue.value : Int)
```

```leanOutput ppAllInt
@DefaultValue.value Int instDefaultValueInt : Int
```

This reveals {name}`instDefaultValueNat` and {name}`instDefaultValueInt` as the instances Lean
picked. The `#synth` command runs the same search directly:

```lean (name := synthDefaultValue)
#synth DefaultValue Nat
```

```leanOutput synthDefaultValue
instDefaultValueNat
```

For a typeclass like {name}`DefaultValue` that carries data — a term, such as the {lean}`1` above,
rather than only proofs (which we will see below) — we expect at most one instance per type, so this search has a unique
answer.

We'll put `DefaultValue`'s standard-library equivalent, {name}`Inhabited`, to work later in this
chapter, when we define maps that need a default value for a generic type. First, though, let's go
back to {name}`List.elem_poly` and see how its `[BEq α]` argument actually gets resolved.

# Using Typeclasses

Let's check what `==` meant for {name}`List.elem_nat`, with notation display turned off:

```lean (name := ppBeq)
set_option pp.notation false in
#check 1 == 2
```

```leanOutput ppBeq
BEq.beq 1 2 : Bool
```

Rather than {name}`Nat.beq`, `==` turns out to be notation for {name}`BEq.beq`, a field of exactly
the kind of typeclass we just learned to define:

```
class BEq (α : Type u) where
  /-- Boolean equality, notated as `a == b`. -/
  beq : α → α → Bool
```

Writing `a == b` makes Lean search for an *instance* of {name}`BEq` for the type of `a` and `b`, the same
way it searched for a {name}`DefaultValue` instance above. For `Nat`, that instance is:

```lean
instance (priority := low) : BEq Nat where
  beq := Nat.beq
```

This is the instance Lean supplies for `[BEq α]` when {name}`List.elem_poly` is called on a
{lean}`List Nat` — no different from Lean choosing {name}`instDefaultValueNat` for
{name}`DefaultValue.value` earlier when it was equated with {lean}`(1 : Nat)`.

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

# Proof-Carrying Typeclasses

The above examples enforce no conditions on the data an instance may carry — any value of the
right type will do. But sometimes enforcing constraints on data is useful. For example,
suppose we want to specify that a type has not just a single element, but two. Here is a first attempt:

```lean -keep
class HasTwoIncomplete (α : Type) where
  one : α
  two : α
```

Unfortunately, this specification isn't precise because it allows `one` and `two` to refer to the
same term. Fortunately, Lean's typeclasses can carry proofs along with data, so we can write the following to enforce that `one` and `two` are distinct.

```lean
class HasTwo (α : Type) where
  one : α
  two : α
  one_neq_two : one ≠ two
```

Declaring instances works in much the same
way as before, except that now the {name}`HasTwo.one_neq_two` field requires a proof:

```lean
instance : HasTwo Nat where
  one := 1
  two := 2
  one_neq_two := by intro contra; contradiction
```

In most languages that support typeclasses (or traits) it is not possible to formally enforce
laws such as `one_neq_two`. Thus it falls to the author to check, informally, that any required invariants are
satisfied, which can lead to bugs.

::::exercise (rating := 1) (name := "HasThree")
Following the pattern of {name}`DefaultValue` and {name}`HasTwo`, define a class `HasThree` that
specifies a type with at least three distinct elements, and give an instance of it for
{name}`Nat`.

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

```lean
namespace Algebra
```

This facility is very powerful, and is used extensively in Lean to define mathematical structures
that carry both operators and laws about how those operators interact. As a simple example,
let's use a typeclass to define a _monoid_, a simple algebraic structure that includes four things:
* an underlying set of data, represented by a type `α`,
* an operator (which we'll write `⊗`, typed \otimes) that combines two elements of type `α` into one,
* a particular element `id` of type `α`, which we call the "identity element", and
* some laws about the interaction of `⊗` and `id`, namely that:
    * `∀ x, id ⊗ x = x = x ⊗ id`, and
    * `∀ x y z, x ⊗ (y ⊗ z) = (x ⊗ y) ⊗ z` (i.e., that `⊗` is associative)

We can express these requirements in the form of a typeclass:

```lean
-- first we define a notation typeclass for our operator ⊗
class OpSet (α : Type) where
  op : α → α → α

infixr:70 " ⊗ " => OpSet.op

class Monoid (α : Type) extends (OpSet α) where
  id : α
  left_id : ∀ (x : α), id ⊗ x = x
  right_id : ∀ (x : α), x ⊗ id = x
  assoc : ∀ (x y z : α), x ⊗ (y ⊗ z) = (x ⊗ y) ⊗ z
```

The `extends` keyword indicates that the {name}`Monoid` typeclass extends the {name}`OpSet` typeclass,
which just defines a set with an operator and some notation for it. The {name}`Monoid` typeclass
"inherits" the fields of {name}`OpSet`, similar to how a class would in an object-oriented language.

As one might expect, the `+` operator over {name}`Nat`s forms a monoid, where `0` is the identity element.
Note that we don't have to define {name}`Nat`'s {name}`OpSet` instance separately, we can define a
single instance that implements both classes.

```lean
instance : Monoid Nat where
  op := Nat.add
  id := 0
  left_id := by lia
  right_id := by lia
  assoc := by lia
```

:::dev "Daniel Sainati @dsainati" PotentialImprovement

Chris notes on GH: we're breaking a rule here about having diamonds on data carrying typeclasses,
something we do explain above. The way this works in Mathlib is that there are additive and m
ultiplicative variants of the classes, e.g. Monoid versus AddMonoid.

This is an isolated problem for now, not sure if/how we want to talk about this.
:::

::::exercise (rating := 1) (name := "NatMonoidMul")
However, multiplication on `Nat`s _also_ forms a monoid. What is its identity element?

```lean
instance : Monoid Nat where
  op := Nat.mul
  id := solution!(1)
  left_id := solution!(by lia)
  right_id := solution!(by lia)
  assoc := solution!(by lia)
```
::::

::::exercise (rating := 1) (name := "ListMonoidAppend")
There are also many monoids over other types. Most usefully in computer science,
lists of any type also form a monoid, with {name}`List.append` as the operator in question:

```lean
instance {α : Type} : Monoid (List α) where
  op := List.append
  id := solution!([])
  left_id := solution!(by simp)
  right_id := solution!(by simp)
  assoc := solution!(by simp)
```
::::

In addition to defining instances of {name}`Monoid`, we can also prove some properties about
monoids in general, just based on the laws defined on the typeclass. One simple theorem
about monoids is that the identity element of a monoid is unique. That is,
if we have two monoids over the same set with the same operator, their identity elements must also
be the same:

:::dev "Daniel Sainati @dsainati1"
I don't know why but the infoview for this proof is extremely confusing. How to set
things up to be clearer?
:::

```lean
theorem id_unique {α : Type} {m₁ m₂ : Monoid α} (h : m₁.op = m₂.op) : m₁.id = m₂.id := by
  rw [←m₁.left_id m₂.id, h, m₂.right_id]
```

A _group_ is a special kind of monoid with an _inverse_ operation `inv`, which has the property that
`∀ x, inv x ⊗ x = id = x ⊗ inv x`. We can extend the definition of a {name}`Monoid` to capture this
new feature:

```lean
class Group (α : Type) extends (Monoid α) where
  inv : α → α
  left_inv : ∀ (x : α), inv x ⊗ x = id
  right_inv: ∀ (x : α), x ⊗ inv x = id
```

Now, the monoids we described earlier are not groups: there is no inverse operation on the
natural numbers such that `∀ x, x + inv x = 0 = inv x + x`, for example. However,
addition does form a group over the integers:

::::exercise (rating := 1) (name := "IntGroupAdd")
```lean
instance : Group Int where
  op := Int.add
  id := solution!(0)
  inv := solution!(Int.neg)
  left_id := solution!(by lia)
  right_id := solution!(by lia)
  assoc := solution!(by lia)
  left_inv := solution!(by lia)
  right_inv := solution!(by lia)
```
::::

The study of groups is called _group theory_ and is a rich area of mathematics. Here, we
will only prove a handful of its simplest results:

:::dev "Daniel Sainati @dsainati1"
This also prints weird.
:::


::::exercise (rating := 1) (name := "InverseUnique")
Two groups defined with the same operation over the same set must have the same inverse as well.

```lean
theorem inv_unique {α : Type} {m₁ m₂ : Group α} (h : m₁.op = m₂.op) : m₁.inv = m₂.inv := by
  solution!
    ext a
    rw [←m₁.right_id (Group.inv a), ←m₁.right_inv a]
    rw [m₁.assoc, h, m₂.left_inv a, m₂.left_id]
```
::::

:::dev "Daniel Sainati @dsainati1"
Taking suggestions for additional simple group theory theorems to prove here.
:::

```lean
end Algebra
```

# Maps

_Maps_ (or "dictionaries") are ubiquitous data structures both in ordinary programming and in the theory of programming languages; we're going to need them in many places in later volumes.

We'll define two flavors of maps: _total maps_, which include a "default" element to be returned when a key being looked up doesn't exist, and _partial maps_, which instead return an option to indicate success or failure. Partial maps are defined in terms of total maps, using {name}`none` as the default element.

## Key and Value Types

To define maps, we first need a type for the keys that we will use to index into our maps and
a type for the values the maps return.
In this section, we'll use the type variable `α` for the type of keys and `β` for values.
In addition to {name}`BEq`, which we have already seen, our key type `α` requires instances of the
{name}`ReflBEq` and {name}`LawfulBEq` typeclasses:

```
/-- `ReflBEq α` says that the `BEq` implementation is reflexive. -/
class ReflBEq (α : Type) [BEq α] : Prop where
  /-- `==` is reflexive, that is, `(a == a) = true`. -/
  protected rfl {a : α} : a == a

/--
A Boolean equality test coincides with propositional equality.

In other words:
 * `a == b` implies `a = b`.
 * `a == a` is true.
-/
class LawfulBEq (α : Type) [BEq α] : Prop extends ReflBEq α where
  /-- If `a == b` evaluates to `true`, then `a` and `b` are equal in the logic. -/
  eq_of_beq : {a b : α} → a == b → a = b
```

These classes refine `BEq`, specifying that (`==`) is reflexive and coincides with
proposition equality `=`.

In general, we place no constraints on the value type `β`.

## Total Maps

The {ref "Lists"}[Lists] chapter introduced a partial map abstraction, `PartialMap`, with a
`find` function for lookup, based on lists of key-value pairs.
Here, we are going to build a map abstraction using functions instead. The advantage of this representation is that it offers a more _extensional_ view of maps, as we saw with functions in the {ref "Logic"}[Logic] chapter: two maps that respond to every query in the same way will be represented as exactly the same function, rather than just as "equivalent" list structures. This simplifies proofs that use maps.

Instead of using functions directly, we encapsulate them inside a `structure` which we call `TotalMap`.
Intuitively, a total map just contains a function `inner` from a key of type `α` to a value of type `β`.

```lean
structure TotalMap (α : Type) (β : Type) where
  inner : α → β

namespace TotalMap
```

In order to declare a default value of `β` we will use the {name}`Inhabited` typeclass, which is the standard library's implementation of our {name}`DefaultValue` example from above:

The function `TotalMap.empty` yields an empty total map, given a default element; this map always returns the default element when applied to any key.

```lean
def empty {α β : Type} [Inhabited β] : TotalMap α β where
  inner := fun _ ↦ default
```

These types and implicit instances are now available automatically to all the definitions in this section.

Just as declaring `BEq`/`DefaultValue` instances above hooked `==` and `DefaultValue.value` up to our types,
we can declare an instance of the standard library's `EmptyCollection` typeclass to associate `∅`
with this empty map.

```lean
instance {α β : Type} [Inhabited β] : EmptyCollection (TotalMap α β) where
  emptyCollection := TotalMap.empty

theorem empty_def {α β : Type} [Inhabited β] : (∅ : TotalMap α β) = { inner := fun _ ↦ default } := by rfl
```

Here, for example, is an empty map that takes `Nat` keys to `Nat` values:

```lean
def emptyNatMap : TotalMap Nat Nat := ∅
```

### Getting Elements

While `TotalMap`s happen to be implemented as functions under the hood,
we would prefer not to expose this
fact in its public interface. Accordingly, we define new operations for querying and
updating mappings. As a first attempt at a query operation, playing the role that `find` played for the {ref "Lists"}[Lists] chapter's
list-based maps, we could define a function
`get` for getting the value associated with a key:

```lean
def get {α β : Type} (m : TotalMap α β) (a : α) := m.inner a

/-- This exposes implementation-specific details of `TotalMap`.
Avoid using this outside the `TotalMap` namespace. -/
theorem get_def {α β : Type} {m : TotalMap α β} {a : α} : m.get a = m.inner a := by rfl

example : emptyNatMap.get 2 = 0 := by rfl
```

Here is an example that uses the API lemmas {name}`empty_def` and {name}`get_def`:

```lean
example {n : Nat} : emptyNatMap.get n = 0 := by
  rewrite [get_def, emptyNatMap, empty_def, Nat.default_eq_zero]
  rfl
```

In the above example, we use {tactic}`rewrite` and {tactic}`rfl` instead of the usual {tactic}`rw`
to highlight something interesting. After the rewrites in this proof,
we end up with a goal that looks like `{ inner := fun x => 0 }.inner n = 0`, which we can solve
with `rfl`. This is because the projection `.inner` on a structure of the form `{ inner := x }`
is definitionally equal to `x`.

{name}`get` is the public API counterpart to {name}`inner` which is an implementation-specific detail of {name}`TotalMap`.
Because {name}`get_def` "peeks" through the abstraction, it should be used sparingly, and only inside the `TotalMap` namespace.

To make element-getting more convenient, let's define notation so we can write
`emptyNatMap[2]` rather than `emptyNatMap.get`. We could notate `get` directly — we'll do
exactly that for `update` below — but here we'll instead make "getting an element" its own
typeclass, `MyGetElem`, and notate it. Doing so means `m[a]` resolves to `MyGetElem.getElem m a` for any
type with a `MyGetElem` instance, not just `TotalMap`.

Using typeclasses to define notation is typical in Lean when the same notation is useful
for many different types.
We have seen the approach already with `==`: writing
`a == b` is notation for {name}`BEq.beq`, resolved by instance search for whatever type `a` and `b` have.
We also just saw overloaded notation for `EmptyCollection` above,
where `∅` is notation for {name}`EmptyCollection.emptyCollection`.
Our typeclass `MyGetElem` is a simpler version of the standard library's {name}`GetElem` typeclass,
which has many instances such as {name}`Array`, {name}`List`, and {name}`Vector`.
We develop it to illustrate the notation-as-typeclass approach.

:::dev "Niklas Halonen (xhalo32)"
A reason I can come up with why we use a notation typeclass (in library code) over a plain notation is that it makes it possible (for a downstream consumer) to write `open scoped MyGetElem` instead of writing `open scoped TotalMap` and `open scoped PartialMap` individually.
This wouldn't be a good sell if `→ₜ` and `→ₚ` are scoped notations, but they're currently global.
:::

```lean
end TotalMap
```

The `MyGetElem` typeclass takes three type parameters: the map implementation,
its keys, and its values.

```lean
class MyGetElem (coll : Type) (idx : Type) (elem : outParam Type) where
  getElem (xs : coll) (i : idx) : elem
```

(Don't worry about the `outParam` qualifier; it is a hint to Lean that helps typeclass inference.)

The appropriate instance of {name}`MyGetElem` for our `TotalMap` is:

```lean
instance {α β : Type} : MyGetElem (TotalMap α β) α β where
  getElem m a := m.get a
```

Now we can associate the bracket syntax with {name}`MyGetElem.getElem`. We've defined custom notation
before — `::` and `[...]` for lists (chapter {ref "Lists"}[Lists], including an `app_unexpander` for
printing `[...]`-notation lists back out), or `+`/`*`/`==` for arithmetic — but always with
`infixl`/`infixr` or `scoped macro`; this is the first time we reach for the more general
`notation`/`macro_rules` forms for getting the `m[a]`
syntax to work.

Don't worry about following the mechanism in detail — the
`macro_rules` and the `app_unexpander` below are minor technicalities. However,
if you do wish to learn more, Chapter 5 and 6 of
[Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/)
contain more detail.

```lean
namespace MyGetElem

scoped macro_rules | `($xs[$i]) => ``(getElem $xs $i)

@[app_unexpander getElem]
def unexpandGetElem : Lean.PrettyPrinter.Unexpander
  | `($_ $xs $i) => `($xs[$i])
  | _ => throw ()
end MyGetElem

open scoped MyGetElem
```

Since the standard library already declares the `x[i]` syntax for {name}`GetElem`,
we only need to define the `macro_rules`, not the `notation` as we have done previously.
It's scoped since we don't want to override the default {name}`GetElem` everywhere, but
only when `open scoped MyGetElem` is in force.

:::dev "Benjamin Pierce (bcpierce00)"
Make sure we've really explained `open scoped` somewhere...
:::

Since we provided a {name}`MyGetElem` instance for {name}`TotalMap`, we can now use the
notation `m[a]` to access elements of a map `m`.

```lean
namespace TotalMap

theorem getElem_def {α  β : Type} (m : TotalMap α β) (a : α) : m[a] = m.get a := by rfl

example : emptyNatMap[1] = default := by rfl

example {n : Nat} : emptyNatMap[n] = 0 := by
  rw [getElem_def, get_def, emptyNatMap, empty_def, Nat.default_eq_zero]
```

We want the public API of {name}`TotalMap` to use the `m[a]` notation instead of `m.get a` so we provide the reverse direction of {name}`getElem_def` as a {tactic}`simp` lemma; the `m[a]` notation is the {name}`TotalMap` API's
{tactic}`simp` normal form.

```lean
@[simp]
theorem get_eq_getElem {α β : Type} (m : TotalMap α β) (a : α) : m.get a = m[a] := by rfl

example {n : Nat} : emptyNatMap.get n = emptyNatMap[n] := by
  simp
```

This design minimizes the need to use {name}`getElem_def` outside concrete examples (which are typically solvable with `rfl` anyways).

### Updating Elements

Now we turn to the `update` function, which takes a map `m`, a key `a`, and a value `b` and returns a new map that takes `a` to `b` and takes every other key to whatever `m` does. We do this by wrapping
a new map function around the old one.

```lean
def update {α β : Type} (m : TotalMap α β) [BEq α] (a : α) (b : β) : TotalMap α β where
  inner := fun a' => bif a == a' then b else m[a']
```

For example, we can build a map taking {name}`String` to {name}`Bool`, where `"foo"` and `"bar"` are mapped to {name}`true` and every other key is mapped to {name}`false`, like this:

```lean
def exampleMap :=
  (∅ : TotalMap String Bool)
    |>.update "foo" true
    |>.update "bar" true
```

Here `|>` is Lean's *pipe* notation: `x |>.f y` means `x.f y`, letting us chain a sequence of
function or method calls left to right without nested parentheses.
:::dev "Benjamin Pierce (bcpierce00)"
Should we introduce this notation earlier?  (Are there good places to use it earlier?)
:::

We also introduce a notation for updating maps — this time, rather than going through a typeclass
and its own `notation`/`macro_rules` machinery as we did for {name}`MyGetElem`, we write a `notation`
that references {name}`TotalMap.update` directly. Unlike indexing, `update` doesn't need to work
generically across container types (there's no standard-library operation like {name}`GetElem` that
we're mirroring here), so the simpler, direct route suffices.

```lean
notation a:55 " →ₜ " b:55 " ; " m:55 => TotalMap.update m a b

/-- This exposes implementation-specific details of `TotalMap`.
Avoid using this outside the `TotalMap` namespace. Prefer `update_apply` if possible. -/
theorem update_def {α β : Type} [BEq α] (m : TotalMap α β) (a : α) (b : β) :
  a →ₜ b ; m = { inner := fun a' => bif a == a' then b else m[a'] } := by rfl

theorem update_apply {α β : Type} [BEq α] (m : TotalMap α β) (a a' : α) (b : β) :
  (a →ₜ b ; m)[a'] = bif a == a' then b else m[a'] := by rfl
```

We can omit the map from the notation when we want it to be empty:

```lean
notation a:55 " →ₜ " b:55 => TotalMap.update ∅ a b
```

The `examplemap` above can now be defined as follows:

```lean
def exampleMap' : TotalMap String Bool := "bar" →ₜ true ; "foo" →ₜ true ; ∅
def exampleMap'' : TotalMap String Bool := "bar" →ₜ true ; "foo" →ₜ true
```

```lean
example : exampleMap = exampleMap' := by rfl
example : exampleMap' = exampleMap'' := by rfl

example : exampleMap'["bar"] = true := by rfl
example : exampleMap'["foo"] = true := by rfl
example : exampleMap'["quux"] = false := by rfl
```

Let's also see a couple of examples of working with updated maps using rewrites:

```lean
example : exampleMap'["bar"] = true := by
  rw [exampleMap', update_apply, BEq.rfl, cond_true]

example : exampleMap'["foo"] = true := by
  rw [exampleMap', update_apply, show ("bar" == "foo") = false by simp, cond_false]
  rw [update_apply, BEq.rfl, cond_true]

example : exampleMap'["quux"] = false := by
  rw [exampleMap', update_apply, show ("bar" == "quux") = false by simp, cond_false]
  rw [update_apply, show ("foo" == "quux") = false by rfl, cond_false]
  rw [empty_def, getElem_def, get_def, Bool.default_bool]
```

When we use maps in later volumes, we'll need several fundamental facts about how they behave.

Even if you don't work the following exercises, make sure you thoroughly understand the statements of the lemmas!

(Some of the proofs require the functional extensionality axiom {name}`funext`, discussed in the {ref "Logic"}[Logic] chapter.)

First, the empty map returns its default element for all keys:

```lean
@[simp]
theorem getElem_empty {α β : Type} [BEq α] [Inhabited β] (a : α) : (∅ : TotalMap α β)[a] = default := by
  rw [empty_def, getElem_def, get_def]
```

Notice that in the example `exampleMap'["quux"] = false` the last rewrite is effectively just {name}`getElem_empty`.

Next, if we update a map `m` at a key `a` with a new value `b` and then look up `a` in the map resulting from the {name}`update`, we get back `b`:

```lean
@[simp]
theorem update_eq {α β : Type} [BEq α] [ReflBEq α] (m : TotalMap α β) (a : α) (b : β) : (a →ₜ b ; m)[a] = b := by
  rw [update_def, getElem_def, get_def]
  dsimp only -- reduces `{ inner := ... }.inner` so that we get a subterm that looks like `a == a`
  rw [BEq.rfl, cond_true]
```

On the other hand, if we update a map `m` at a key `a₁` and then look up a _different_ key `a₂` in the resulting map, we get the same result that `m` would have given:

::::exercise (rating := 2) (name := "update_neq")
```lean
@[simp]
theorem update_neq {α β : Type} [BEq α] [LawfulBEq α] {m : TotalMap α β} {a₁ a₂ : α} (h : a₁ ≠ a₂) (b : β) :
    (a₁ →ₜ b ; m)[a₂] = m[a₂] := by
  solution!
    rw [update_def, getElem_def, get_def]
    dsimp only
    rw [beq_false_of_ne h, cond_false]
```
::::

The two remaining facts are equalities _between maps_, so we first need to say when two maps are equal. Since a total map is implemented as a function, this is effectively the functional extensionality principle ({name}`funext`) from the {ref "Logic"}[Logic] chapter: two maps are equal when they agree at every key. Recording it once, for maps, and tagging it `@[ext]` lets the {tactic}`ext` tactic reduce a goal `m₁ = m₂` to the pointwise one in the proofs below.

The fact that {name}`TotalMap` is a structure complicates things slightly.
We need to use injectivity of its constructor {name}`mk` which Lean automatically provides for us as {name}`mk.injEq`.
It lets us prove `m₁ = m₂` from `m₁.inner = m₂.inner` or vice versa.

```lean
@[ext]
theorem ext {α β : Type} {m₁ m₂ : TotalMap α β} (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := by
  rw [TotalMap.mk.injEq]
  apply funext
  intro x
  specialize h x
  rw [getElem_def, get_def, getElem_def, get_def] at h
  exact h
```

To demonstrate this extensionality principle, let's look at an example:

```lean
example : "bar" →ₜ true ; "foo" →ₜ true = "foo" →ₜ true ; "bar" →ₜ true := by
  ext a
  by_cases h : "bar" = a
  · subst h
    rw [update_eq, update_neq (show "foo" ≠ "bar" by simp), update_eq]
  · simp only [update_apply]
    rw [beq_false_of_ne h]
    simp
```

Given keys `a₁` and `a₂`, the tactic {tactic}`by_cases` `h : a₁ = a₂` splits the proof into the case where they are equal — where `subst h` then replaces one by the other — and the case where they are not, which is what {name}`update_neq` wants. Use it to prove the following theorem, which states that if we update a map to assign key `a` the same value as it already has in `m`, then the result is equal to `m`:

::::exercise (rating := 2) (name := "update_same")
```lean
@[simp]
theorem update_same {α β : Type} [BEq α] [LawfulBEq α] (m : TotalMap α β) (a : α) : (a →ₜ m[a] ; m) = m := by
  solution!
    ext a'
    by_cases h : a = a'
    · subst h
      simp
    · simp [update_neq h]
```
::::

Similarly, if we update a map `m` at a key `a` with a value `b₁` and then update again with the same key `a` and another value `b₂`, the resulting map behaves the same (gives the same result when applied to any key) as the simpler map obtained by performing just the second {name}`update` on `m`:

::::exercise (rating := 2) (name := "update_shadow")
```lean
@[simp]
theorem update_shadow {α β : Type} [BEq α] [LawfulBEq α] (m : TotalMap α β) (a : α) (b₁ b₂ : β) :
    (a →ₜ b₂ ; a →ₜ b₁ ; m) = (a →ₜ b₂ ; m) := by
  solution!
    ext a'
    by_cases h : a = a'
    · subst h
      simp
    · simp [update_neq h]
```
::::

:::dev "mwhicks1" NOW
Two things the Rocq source says here have been dropped.

Rocq frames this case analysis around `destruct (eqb_spec x1 x2)`, which
"simultaneously performs case analysis on the result of `String.eqb x1 x2` and
generates hypotheses about the equality (in the sense of `=`) of `x1` and `x2`"
— the boolean/propositional reflection idiom. The paragraph above replaces that
with `by_cases`/`subst`, which is what the Lean proof uses. But
reflection is what the `Reflection` section *below* is about, so the two
may want to be connected rather than have one silently displace the other.

Rocq then says "With the example in chapter *IndProp* as a template, use
`String.eqb_spec` to prove ...". That cross-reference is dropped, since it is
unclear what the Lean `IndProp` chapter will end up containing. Revisit later.
:::

:::dev "Niklas Halonen (xhalo32)"
Regarding reflection: I have used `show ("bar" == "foo") = false by simp` in some of the above sections which would be good to explain in more detail in the reflection section.
Disclaimer: I don't actually know how Lean proves it under the hood, I just assume it's relevant to reflection.
```lean
example : ("bar" == "foo") = false := by
  simp only [String.reduceBEq]
example : ("bar" == "foo") = false := by
  rfl
example : ("bar" == "foo") = false := by
  decide
```
:::

Similarly, prove one final property of the {name}`update` function: if we update a map `m` at two distinct keys, it doesn't matter in which order we do the updates.

:::dev "mwhicks1" NOW
Rocq says "Similarly, use `String.eqb_spec` to prove ..."; the instruction to use
a specific lemma is dropped here for the same reason as in the note above.
:::

::::exercise (rating := 3) (name := "update_permute")
```lean
theorem update_permute {α β : Type} [BEq α] [LawfulBEq α] {m : TotalMap α β} {a₁ a₂ : α} {b₁ b₂ : β} (h : a₁ ≠ a₂) :
    (a₁ →ₜ b₁ ; a₂ →ₜ b₂ ; m) = (a₂ →ₜ b₂ ; a₁ →ₜ b₁ ; m) := by
  solution!
    ext a'
    by_cases h₁ : a₁ = a'
    · subst h₁
      rw [update_eq, update_neq h.symm, update_eq]
    · rw [update_neq h₁]
      by_cases h₂ : a₂ = a'
      · subst h₂
        rw [update_eq, update_eq]
      · rw [update_neq h₂, update_neq h₂, update_neq h₁]
```

:::gradeTheorem 3 update_permute
:::
::::

:::dev
The Rocq source also has {name}`getElem_empty` (originally `apply_empty`) and {name}`update_eq` as (optional)
exercises; here they are worked examples, since {name}`update_eq` was already
presented that way. Reconsider if this section is rebalanced.
:::

```lean
end TotalMap
```

## Notation for Concrete Maps

Wouldn't it be nice if we could use a more natural notation for concrete maps like `{ "bar" ↦ true, "foo" ↦ true }`?
To accomplish this we define a simple structure that consists of a key and a value along with `↦` notation for it.

```lean
/--
A key-value pair with `↦` syntax.
-/
@[ext]
structure KVPair (K : Type) (V : Type) where
  key : K
  value : V

namespace KVPair
scoped notation k " ↦ " v => KVPair.mk k v
end KVPair

open scoped KVPair
```

Next, we declare `Insert` and `Singleton` instances — the standard-library typeclasses behind the
`{x, y, ...}` and `{x}` collection-literal notation that `List`, `Finset`, and other stdlib
containers already support — so that `TotalMap` can use it too.

```lean
namespace TotalMap

instance {α β : Type} [BEq α] : Insert (KVPair α β) (TotalMap α β) where
  insert kv m := kv.key →ₜ kv.value ; m

instance {α β : Type} [BEq α] [Inhabited β] : Singleton (KVPair α β) (TotalMap α β) where
  singleton kv := insert kv ∅

instance {α β : Type} [BEq α] [Inhabited β] : LawfulSingleton (KVPair α β) (TotalMap α β) where
  insert_empty_eq _ := rfl

end TotalMap
```

Here are a couple of examples using the new notation:

```lean
example : ({ "bar" ↦ true, "foo" ↦ true }) = "bar" →ₜ true ; "foo" →ₜ true ; ∅ := rfl

example : ({ "foo" ↦ true } : TotalMap String Bool)["foo"] = true := rfl

example : ({ 1 ↦ 2, 1 ↦ 3 } : TotalMap Nat Nat)[1] = 2 := rfl
```

The reason we need to explicitly specify the type of the map is that Lean doesn't know what type of collection `{ "foo" ↦ true }` is without type hints, as we can see with `#check`:

```lean (name := foo)
#check { "foo" ↦ true }
```

```leanOutput foo
{"foo" ↦ true} : ?m.4
```

The type shows a `?m.4`, which indicates that Lean can't infer the type.
A type which can't be inferred doesn't have any type classes like `MyGetElem`, so typeclass resolution gets stuck in the following example:

```lean -keep +error
example : ({ "foo" ↦ true })["foo"] = true := rfl
```

## Partial Maps

:::dev "Niklas Halonen (xhalo32)"
We should spend some time discussing differences between the inductive approach in Lists.lean and the approach here.
The inductive approach could be made polymorphic and proven to be equivalent with partial maps (I believe), so the point is not that the maps are extensionally different.
A question (that I don't have an answer to) is then: what makes the new partial map better?
:::

Lastly, we define _partial maps_ on top of total maps. A partial map with elements of type `β` is simply a total map with elements of type `Option β`, whose default element is {name}`none`.

```lean
structure PartialMap (α : Type) (β : Type) where
  /-- The underlying total map. Lean always generates a public projection for a structure
  field, so `inner` is technically accessible, but it isn't part of the intended interface:
  use `PartialMap.toTotal` instead, so there's exactly one sanctioned way to get at it. -/
  inner : TotalMap α (Option β)

/- Note that this definition of `EmptyCollection` doesn't need `β` to have an `Inhabited` instance
   like `TotalMap` did. This is because `Option β` has its own `Inhabited` instance: `none` is a value
   of every `Option` type. -/
instance {α β : Type} : EmptyCollection (PartialMap α β) where
  emptyCollection := { inner := ∅ }

def PartialMap.toTotal  {α β : Type} (m : PartialMap α β) : TotalMap α (Option β) := m.inner

instance  {α β : Type} : MyGetElem (PartialMap α β) α (Option β) where
  getElem m a := m.toTotal[a]

theorem getElem_def  {α β : Type} (m : PartialMap α β) (a : α) : m[a] = m.toTotal[a] := rfl
```

:::dev "Niklas Halonen (xhalo32)" NOW
The following few paragrahps are out-of-date because `TotalMap` is also a structure.
:::

Remember that we discussed earlier with total maps that using accessing the `inner` field
and performing function application application exposes the implementation,
and that's why we introduced a new notation {name}`MyGetElem`?
Here we take extend that concept, and instead of using a `def` for partial maps, like this...

```display
def PartialMap (α : Type) (β : Type) := TotalMap α (Option β)`
```

...we define partial maps as a structure containing a total map.
This more strongly hides the fact that it's a total map.

Now, the type system doesn't consider `PartialMap α β` to be definitionally equal to `TotalMap α (Option β)`,
so the following equality doesn't type check:

```lean -keep +error (name := empty_eq)
example  {α β : Type} : (∅ : PartialMap α β) = (∅ : TotalMap α (Option β)) := by rfl
```

```leanOutput empty_eq
Type mismatch
  ∅
has type
  TotalMap α (Option β)
but is expected to have type
  PartialMap α β
```

Updating a partial map at a key means storing a {name}`some` value there.
To update, we create a new partial map from `a →ₜ some b ; m.toTotal` by wrapping it in angle brackets, i.e. using the anonymous constructor syntax.
This is equivalent to writing `{ inner := a →ₜ some b ; m.toTotal }`.
We also introduce a similar notation for it as for total maps.

```lean
namespace PartialMap

def update  {α β : Type} [BEq α] (m : PartialMap α β) (a : α) (b : β) : PartialMap α β :=
  ⟨a →ₜ some b ; m.toTotal⟩

notation a:55 " →ₚ " b:55 " ; " m:55 => PartialMap.update m a b

notation a:55 " →ₚ " b:55 => PartialMap.update ∅ a b

def examplePmap : PartialMap String Bool := "Church" →ₚ true ; "Turing" →ₚ false
```

Next, we provide some fundamental properties about {name}`toTotal`:

```lean
theorem toTotal_empty {α β : Type} : (∅ : PartialMap α β).toTotal = (∅ : TotalMap α (Option β)) := rfl

theorem toTotal_update{α β : Type} [BEq α] (m : PartialMap α β) (a : α) (b : β) :
    (a →ₚ b ; m).toTotal = a →ₜ some b ; m.toTotal := rfl
```

As an example, here's how we can use these on some concrete maps:

```lean
example : (2 →ₚ 3)[2] = some 3 := by
  rw [getElem_def, toTotal_update, toTotal_empty, TotalMap.getElem_def]
  rfl
```

This also holds by definition (`rfl`), since all the rewrites in the above proof do the computation step-by-step.

```lean
example : (2 →ₚ 3)[2] = some 3 := by rfl
```

Next, we lift all of the basic lemmas about total maps to partial maps.
To do this we should first prove an extensionality lemma about partial maps.
To prove extensionality, we employ injectivity of {name}`PartialMap`'s constructor {name}`mk` using {name}`mk.injEq`.

```lean
theorem toTotal_eq_iff {α β : Type} (m₁ m₂ : PartialMap α β) : m₁.toTotal = m₂.toTotal ↔ m₁ = m₂ := by
  rw [mk.injEq]
  rfl

@[ext]
theorem ext {α β : Type} {m₁ m₂ : PartialMap α β} (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := by
  rw [← toTotal_eq_iff]
  exact TotalMap.ext h
```

Now, let's lift the {name}`TotalMap` lemmas:

```lean
theorem getElem_empty {α β : Type} [BEq α] (a : α) : (∅ : PartialMap α β)[a] = none := by
  rw [getElem_def, toTotal_empty, TotalMap.getElem_empty, Option.default_eq_none]

theorem update_eq {α β : Type} [BEq α] [ReflBEq α] (m : PartialMap α β) (a : α) (b : β) : (a →ₚ b ; m)[a] = some b := by
  rw [getElem_def, toTotal_update, TotalMap.update_eq]

theorem update_neq {α β : Type} [BEq α] [LawfulBEq α] {m : PartialMap α β} {a₁ a₂ : α} (h : a₁ ≠ a₂) (b : β) :
    (a₁ →ₚ b ; m)[a₂] = m[a₂] := by
  dsimp [getElem_def, toTotal_update]
  rw [TotalMap.update_neq h]

theorem update_shadow {α β : Type} [BEq α] [LawfulBEq α] (m : PartialMap α β) (a : α) (b₁ b₂ : β) :
    (a →ₚ b₂ ; a →ₚ b₁ ; m) = (a →ₚ b₂ ; m) := by
  apply ext
  intro x
  dsimp [getElem_def, toTotal_update]
  rw [TotalMap.update_shadow]

theorem update_same {α β : Type} [BEq α] [LawfulBEq α] {m : PartialMap α β} {a : α} {b : β} (h : m[a] = some b) :
    (a →ₚ b ; m) = m := by
  apply ext
  intro x
  dsimp [getElem_def, toTotal_update]
  rw [← h, getElem_def, TotalMap.update_same]

theorem update_permute {α β : Type} [BEq α] [LawfulBEq α] {m : PartialMap α β} {a₁ a₂ : α} {b₁ b₂ : β} (h : a₁ ≠ a₂) :
    (a₁ →ₚ b₁ ; a₂ →ₚ b₂ ; m) = (a₂ →ₚ b₂ ; a₁ →ₚ b₁ ; m) := by
  apply ext
  intro x
  dsimp [getElem_def, toTotal_update]
  rw [TotalMap.update_permute h]
```

And let's add `{}`-notation for partial maps as well.

```lean
instance {α β : Type} [BEq α] : Insert (KVPair α β) (PartialMap α β) where
  insert kv m := kv.key →ₚ kv.value ; m

instance {α β : Type} [BEq α] : Singleton (KVPair α β) (PartialMap α β) where
  singleton kv := insert kv ∅

instance {α β : Type} [BEq α] : LawfulSingleton (KVPair α β) (PartialMap α β) where
  insert_empty_eq _ := rfl

example : { 1 ↦ 2, 2 ↦ 3 } = 1 →ₚ 2 ; 2 →ₚ 3 := rfl
```

One last thing: for partial maps, it's convenient to introduce a notion of map inclusion, stating
that all the entries in one map are also present in another. Lean already has notation for this —
`m₁ ⊆ m₂` — which we get by supplying a {name}`HasSubset` instance.


```lean
def Subset {α β : Type} (m₁ m₂ : PartialMap α β) : Prop :=
  ∀ {a : α} {b : β}, m₁[a] = some b → m₂[a] = some b

instance {α β : Type} : HasSubset (PartialMap α β) where
  Subset := PartialMap.Subset

theorem subset_def {α β : Type} (m₁ m₂ : PartialMap α β) :
    m₁ ⊆ m₂ ↔ (∀ {a : α} {b : β}, m₁[a] = some b → m₂[a] = some b) := .rfl
```

We can then show that map update preserves map inclusion, that is:

```lean
theorem update_subset {α β : Type} [BEq α] [LawfulBEq α] (m₁ m₂ : PartialMap α β) (a : α) (b : β) (h : m₁ ⊆ m₂) :
    (a →ₚ b ; m₁) ⊆ (a →ₚ b ; m₂) := by
  rw [subset_def] at h ⊢
  intro a' b' hb
  by_cases ha : a = a'
  · subst ha
    rw [update_eq] at hb ⊢
    exact hb
  · rw [update_neq ha] at hb ⊢
    exact h hb

end PartialMap
```

This property is quite useful for reasoning about languages with variable binding — e.g., the Simply Typed Lambda Calculus, which we will see in _Type Systems_, where maps are used to keep track of which program variables are defined in a given scope.

:::dev
`namespace TotalMap` is reopened here only because the `Reflection` section below
happens to sit inside it (its `Nat.isEven`/`Nat.double` are really
`TotalMap.Nat.*`, and moving them to the root `Nat` namespace would collide with
`UsingLean`'s `Nat.double`). Drop the reopen when that section is given a home of
its own.
:::

```lean
namespace TotalMap
```

# Reflection

:::dev
I think this will still exist in previous chapters, just not have the reflection explanations until
here? Since I can't import these yet, just placing here at the top of this section — CGH
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
{name}`Bool`), and with propositions (of type {lean}`Prop`).

Here are the key differences between `Bool` and `Prop`:

:::dev "Benjamin Pierce (bcpierce00)"
Check formatting:
:::
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
type `Bool` can be simplified in a finite number of steps to either `true` or `false` — i.e., there
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
theorem isEven_double_exists (n : Nat) :
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

In view of this theorem, we can say that the boolean computation `isEven n` is reflected in the truth of
the proposition `∃ k, n = double k`.

 Similarly, to state that two numbers n and m are equal, we can say either
 * that `n == m` returns `true`, or
 * that `n = m`

 Again, these two notions are equivalent:

:::dev
This proof is from the typeclass version, which makes more sense if maps are included — CGH
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

But we have indicated to Lean, using the `noncomputable` keyword and `Classical` namespace,
that we are _not_ interested in computation.
What is happening in the background is that this allows
typeclass synthesis to find the scoped instance {name}`Classical.propDecidable`, which makes use of
the axiom of choice to provide a proof that all propositions are _classically_ decidable. This
sort of definition is suitable for use with proofs, but is not allowed to be used in conjunction
with computational features of Lean such as the {tactic}`decide` tactic or the `#eval` command.

# TODO

:::dev "Benjamin Pierce (bcpierce00)"
Needs finishing...
:::

:::dev
Below are some stray examples from IndProp. `Decidable` only carries the proposition and not the
boolean, so one direction of `reflect_iff` is easily translated, but the other is a bit different.
I list some theorems below but you should Loogle and see if that's what you want. Some the the
proofs can be a bit advanced if you follow core, or otherwise a bit circular. — CGH
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
`Bool`/`Prop` mismatch? — CGH
:::

```lean
example (a : α) [BEq α] [LawfulBEq α] (xs : List α) (neq : xs.filter (a == ·) ≠ []) : a ∈ xs := by
  sorry
```

:::dev
Burtonpatel: Some more examples would be good. It might be good to start with Nat and then move to the Indprop ones. This is a short chapter, so 5-6 well-chosen, informative exercises could easily fit.
:::
