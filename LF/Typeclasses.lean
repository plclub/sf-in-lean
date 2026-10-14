import SFLMeta

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

:::dev "Mike Hicks (mwhicks1)" PotentialImprovement
Big TODO: Need to make a :::terse version of this lecture. My experience so
far was that "Why We Need Typeclasses", "Defining Your Own Typeclasses", "Using Typeclasses",
"Proof-Carrying Typeclasses" were mostly all useful to present, as is.
We can go much faster through TotalMaps, briefly mentioning a property that uses `ext`.
Then for PartialMaps you can just say it's an Option value type, and then skip past the
rest. Finally, the Decidable section is pretty good as is, with the code examples,
with a little textual glue.
:::

:::dev "Mike Hicks (mwhicks1)" PotentialImprovement
It would be convenient to declare the variables below so that inline prose
throughout this chapter can use `α`, `β`, `defaultValue`, `n`, and `m` without
repeating their type annotations, but the same problem described in the
{ref "Logic"}[Logic] chapter applies: an unused `variable` is silently added
to the local context in basically every proof from here on, even when the
theorem never mentions it. Until we have a way to declare variables visible
only for inline prose (rather than for every `lean` block), we leave this
commented out:

```
-- variable (α β : Type) (defaultValue : α) (n m : Nat)
```
:::

Chapter {ref "Poly"}[Poly] introduced *parametric polymorphism*, declaring a type variable with no
constraint on it.

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
def List.elemNat (n : Nat) (ms : List Nat) : Bool :=
  match ms with
  | [] => false
  | m :: ms' => bif n == m then true else elemNat n ms'

theorem List.elem_nat_nil (n : Nat) : [].elemNat n = false := by rfl

theorem List.elem_nat_cons (n m : Nat) (ms : List Nat) :
    (m :: ms).elemNat n = bif n == m then true else elemNat n ms := by rfl
```

```lean
#eval [0, 1].elemNat 0
#eval [0, 1].elemNat 1
#eval [0, 1].elemNat 2
```

What if we want this to work for lists of _any_ element type, not just {name}`Nat`? Parametric
polymorphism suggests simply replacing {name}`Nat` with a type variable `α`,
but that produces a puzzling error:

```lean -keep +error (name := elem_poly_error)
def List.elemPoly {α : Type} (x : α) (ys : List α) : Bool :=
  match ys with
  | [] => false
  | y :: ys' => bif x == y then true else elemPoly x ys'
```

```leanOutput elem_poly_error
failed to synthesize instance of type class
  BEq α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

Lean is trying to use typeclasses to work out how `==` should behave on a value of type `α`.
We'll see exactly why shortly; for now, here's one way to sidestep the problem:
have the caller supply the equality test to use.

```lean
def List.elemPolyEq {α : Type} (eq : α → α → Bool) (x : α) (ys : List α) : Bool :=
  match ys with
  | [] => false
  | y :: ys' => bif eq x y then true else elemPolyEq eq x ys'

#eval [0, 1].elemPolyEq Nat.beq 0
```

This works, but it's tedious: every caller has to know, and remember to supply, the right equality
function.

Typeclasses automate this — instead of the programmer passing the function
explicitly, Lean searches for one and provides it on its own. We specify something we want
Lean to search for by declaring a `class` with the needed function as a field; a `class` is like
an interface in Java or a trait in Rust. Particular implementations of that class
are called _instances_; each type can have its own instance of a class. For functions that would
use such instances, we specify
the name of the class in an _instance implicit_ on the polymorphic variable that the
instance's function applies to. This directs Lean to rely on the class inside the function, and to
find and fill in the appropriate instance when the function is called.

Here is what this looks like for `List.elemPoly`:

```lean
def List.elemPoly {α : Type} [BEq α] (x : α) (ys : List α) : Bool :=
  match ys with
  | [] => false
  | y :: ys' => bif x == y then true else elemPoly x ys'

theorem List.elemPoly_nil {α : Type} [BEq α] (x : α) : [].elemPoly x = false := by rfl

theorem List.elemPoly_cons {α : Type} [BEq α] (x y : α) (ys : List α) :
    (y :: ys).elemPoly x = bif x == y then true else elemPoly x ys := by rfl

#eval [0, 1].elemPoly 0
```
Comparing {name}`List.elemPolyEq` with {name}`List.elemPoly`, we see three differences.
First, {name}`List.elemPolyEq` takes an _explicit_ parameter `eq`,
whereas {name}`List.elemPoly` specifies an instance implicit `[BEq α]`. The instance implicit
indicates that an instance of {name}`BEq` must be provided at
call sites for the particular type `α` that is used.
Second, whereas {name}`List.elemPolyEq` invokes the parameter `eq` to test equality,
{name}`List.elemPoly` uses `==` instead. As {ref "Lists"}[Lists] noted when we first used it,
`==` on {name}`Nat` comes from the {name}`BEq` typeclass.
Finally, whereas {lean}`[0, 1].elemPolyEq Nat.beq 0` passes the equality
function {name}`Nat.beq` explicitly, in {lean}`[0, 1].elemPoly 0` Lean fills it in
automatically based on the type {name}`Nat` of the {name}`List`.
(It's tempting to assume Lean fills in {name}`Nat.beq` itself here — it doesn't; we'll see exactly
which `BEq` instance it finds, and why, in "Deciding Propositions" later in this chapter.)

Going back to the earlier version of {name}`List.elemPoly`, without the instance implicit, we
can now understand the error message: `α` was fully generic,
so the `==` in its body would have needed to work for _every_ type `α`, and no
single {name}`BEq` instance can do that. So Lean's search failed.

Now it is time to dig into the details of what we have seen so far.
We'll see exactly how `[BEq α]` gets filled in below, starting with how
to define a typeclass in the first place.

# Defining Your Own Typeclasses

{name}`BEq` comes from Lean's standard library. Let's define a typeclass of our own, to see the
mechanism — classes, instances, and synthesis — that made `==` resolve automatically above.

Suppose we want a function that returns the first element of a list, defaulting to a
given value if the list is empty. As with {name}`List.elemPolyEq` above, here is a version
that makes the default value an explicit parameter:

```lean
def List.headOrEx {α : Type} (defaultValue : α) (xs : List α) : α :=
  match xs with
  | [] => defaultValue
  | x :: _ => x

#eval [1, 2, 3].headOrEx 0
#eval ([] : List Nat).headOrEx 0
```

This works, but again it's tedious: every caller has to supply an element of `α` to default to,
even when there's an obvious choice based on the type of the things in the list,
like {lean}`0` for {name}`Nat`.

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
```

Naming the data this way already lets us take a step toward what we want: a version of
{name}`List.headOrEx` can take a `DefaultValue α` argument instead of a raw `α`, with callers
supplying a value like {name}`natDefault` instead of a bare {name}`Nat`:

```lean
def List.headOrEx {α : Type} (defaultValue : DefaultValue α) (xs : List α) : α :=
  match xs with
  | [] => defaultValue.value
  | x :: _ => x

end DefaultValueScratch
```

This is more verbose than before — callers must build a `DefaultValue` value first — but it has
the right shape: all that's left is marking `DefaultValue` as searchable, so Lean can supply this
argument itself. How do we do that?
We need to tell Lean that `DefaultValue` is the sort of structure it should
search for automatically.
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
the same process that found {lean}`BEq Nat` earlier. That means we can rewrite {name}`List.headOrEx`
the same way we rewrote {name}`List.elemPolyEq` into {name}`List.elemPoly` above, replacing the
explicit `defaultValue` parameter with an instance implicit:

```lean
def List.headOr {α : Type} [DefaultValue α] (xs : List α) : α :=
  match xs with
  | [] => DefaultValue.value
  | x :: _ => x

#eval [1, 2, 3].headOr
#eval ([] : List Nat).headOr
```

```lean
example : DefaultValue.value = (0 : Nat) := by rfl
```

Notice that we refer to {name}`DefaultValue.value` alone, with no instance named. Because the
expression equates `DefaultValue.value` with the {name}`Nat` {lean}`0`, Lean selects
{name}`instDefaultValueNat`, the instance for {lean}`DefaultValue Nat`. We know this because we
are able to prove that {name}`DefaultValue.value` is equal to {lean}`0`.

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

For a typeclass like {name}`DefaultValue` that carries data — a term, such as the {lean}`0` above,
rather than only proofs (which we will see below) — we expect at most one instance per type,
so this search has a unique answer.

We'll put {name}`DefaultValue`'s standard-library equivalent, {name}`Inhabited`, to work later in this
chapter, when we define maps that need a default value for a generic type. First, though, let's go
back to {name}`List.elemPoly` and see how its `[BEq α]` argument actually gets resolved.

# Using Typeclasses

Let's check what `==` meant for {name}`List.elemNat`, with notation display turned off:

```lean (name := ppBeq)
set_option pp.notation false in
#check 1 == 2
```

```leanOutput ppBeq
BEq.beq 1 2 : Bool
```

Rather than {name}`Nat.beq`, `==` turns out to be notation for {name}`BEq.beq`, a field of exactly
the kind of typeclass we just learned to define:

```recall
  class BEq (α : Type) where
    beq : α → α → Bool
```

Writing `x == y` makes Lean search for an _instance_ of {name}`BEq` for the type of `x` and `y`, the
same way it searched for a {name}`DefaultValue` instance above. Here is one way to define such an
instance for `Nat`:

```lean
instance (priority := low) instNatbeq : BEq Nat where
  beq := Nat.beq
```

This instance is given low priority so that it doesn't override the standard library's own
`BEq Nat` instance — which, as we'll see later in this chapter, is actually derived from `Nat`'s
decidable equality rather than from {name}`Nat.beq` directly. Declaring it here just illustrates
what a hand-written `BEq` instance looks like, the same way {name}`instDefaultValueNat` illustrated
a hand-written `DefaultValue` instance earlier.

If you prefer a specific instance you can provide it explicitly, by using `@` to make
the instance argument explicit. Here we provide our {name}`instNatbeq` instance specifically.

```lean
#eval @List.elemPoly Nat instNatbeq 1 [1,2,3]
```

::::exercise (rating := 1) (name := "List.elem_poly_eq_elem_nat")
Prove that {name}`List.elemPoly` agrees with {name}`List.elemNat` when specialized to
natural numbers.

```lean
theorem List.elemPoly_eq_elemNat (ms : List Nat) (n : Nat) : ms.elemPoly n = ms.elemNat n := by
  solution!(
  induction ms with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.elemPoly_cons, List.elem_nat_cons, ih])
```
:::gradeTheorem 1 List.elemPoly_eq_elemNat
:::
::::

# Proof-Carrying Typeclasses

The above examples enforce no conditions on the data an instance may carry — any value of the
right type will do. But sometimes enforcing constraints on data is useful. For example,
suppose we want to specify that a type has not just a single element, but two. Here is a first
attempt:

```lean -keep
class HasTwoIncomplete (α : Type) where
  one : α
  two : α
```

Unfortunately, this specification isn't precise because it allows `one` and `two` to refer to the
same term. Fortunately, Lean's typeclasses can carry proofs along with data, so we can write the
following to enforce that `one` and `two` are distinct.

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
  one_neq_two := by lia
```

In most languages that support typeclasses (or traits), it is not possible to formally enforce
laws such as `one_neq_two`. Thus it falls to the author to check, informally, that any required
invariants are satisfied, which can lead to bugs.

::::exercise (rating := 1) (name := "HasThree") (manual := true)
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
  one_neq_three := solution!(by lia)
  two_neq_three := solution!(by lia)
  -- END SOLUTION
```

:::grade
```
GRADE_MANUAL 1: HasThree
```
:::
::::

```lean
namespace Algebra
```

This facility is very powerful, and is used extensively in Lean to define mathematical structures
that carry both operators and laws about how those operators interact. As a simple example,
let's use a typeclass to define a _monoid_, a simple algebraic structure that includes four things:

* an underlying set of data, represented by a type `α`,
* an operator (which we'll write `⊗`, typed `\otimes`) that combines two elements of type `α` into one,
* a particular element `id` of type `α`, which we call the "identity element," and
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
  left_id  (x : α)  : id ⊗ x = x
  right_id (x : α)  : x ⊗ id = x
  assoc (x y z : α) : x ⊗ (y ⊗ z) = (x ⊗ y) ⊗ z
```

The `extends` keyword indicates that the {name}`Monoid` typeclass extends the {name}`OpSet` typeclass,
which just defines a set with an operator and some notation for it. The {name}`Monoid` typeclass
"inherits" the fields of {name}`OpSet`, similar to how a class would in an object-oriented language.

As one might expect, the `+` operator over {name}`Nat`s forms a monoid, where `0` is the identity element.
Note that we don't have to define {name}`Nat`'s {name}`OpSet` instance separately; we can define a
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
something we do explain above. The way this works in Mathlib is that there are additive and
multiplicative variants of the classes, e.g. Monoid versus AddMonoid.

This is an isolated problem for now, not sure if/how we want to talk about this.
:::

::::exercise (rating := 1) (name := "NatMonoidMul") (manual := true)
However, multiplication on `Nat`s _also_ forms a monoid. What is its identity element?

```lean
instance : Monoid Nat where
  op := Nat.mul
  id := solution!(1)
  left_id := solution!(by lia)
  right_id := solution!(by lia)
  assoc := solution!(by lia)
```

:::grade
```
GRADE_MANUAL 1: NatMonoidMul
```
:::
::::

::::exercise (rating := 1) (name := "ListMonoidAppend") (manual := true)
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

:::grade
```
GRADE_MANUAL 1: ListMonoidAppend
```
:::
::::

In addition to defining instances of {name}`Monoid`, we can also prove some properties about
monoids in general, just based on the laws defined on the typeclass. One simple theorem
about monoids is that the identity element of a monoid is unique. That is,
if we have two monoids over the same set with the same operator, their identity elements must also
be the same:

```lean
theorem id_unique {α : Type} {m₁ m₂ : Monoid α} (h : m₁.op = m₂.op) :
  m₁.id = m₂.id := by
    obtain @⟨op₁, id₁, left_id₁, right_id₁, assoc₁⟩ := m₁
    obtain @⟨op₂, id₂, left_id₂, right_id₂, assoc₂⟩ := m₂
    have h' : id₁ = id₂ := by
      -- this introduces a use of m₁'s operator
      rw [← left_id₁ id₂]
      -- we use our hypothesis to rewrite m₁'s operator into m₂'s
      rw [h]
      -- then, we can use m₂'s right id
      rw [right_id₂]
    -- the goal `m₁.id = m₂.id` is equivalent with `id₁ = id₂`
    -- even though it displays `Monoid.id = Monoid.id`
    exact h'
```

In the above proof, we can destructure the monoid instances `m₁` and `m₂` with the `obtain` tactic
we saw in the {ref "Logic"}[Logic] chapter. When we do so, we prepend the `@` symbol to
our tuple so that we can "flatten" the {name}`Monoid` to reveal both its {name}`OpSet` field
`op` and its {name}`Monoid` (only) fields `id`, `left_id`, etc., together.
When stepping through the above proof, if the notation is confusing to you,
remember that you can set `set_option pp.all true` or `set_option pp.explicit true`
to make Lean show you more clearly what is going on.
For example, the goal is displayed as `Monoid.id = Monoid.id` since the instances `m₁` and `m₂` are
implicit arguments to `Monoid.id`. Setting `pp.explicit true` displays the goal as
`@Eq α (@Monoid.id α m₁) (@Monoid.id α m₂)`.

A _group_ is a special kind of monoid with an _inverse_ operation `inv`, which has the property that
`∀ x, inv x ⊗ x = id = x ⊗ inv x`. We can extend the definition of a {name}`Monoid` to capture this
new feature:

```lean
class Group (α : Type) extends (Monoid α) where
  inv : α → α
  left_inv  (x : α) : inv x ⊗ x = id
  right_inv (x : α) : x ⊗ inv x = id
```

Now, the monoids we described earlier are not groups: there is no inverse operation on the
natural numbers such that `∀ x, x + inv x = 0 = inv x + x`, for example. However,
addition does form a group over the integers:

::::exercise (rating := 1) (name := "IntGroupAdd") (manual := true)
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

:::grade
```
GRADE_MANUAL 1: IntGroupAdd
```
:::
::::

In mathematics, the study of groups is called _group theory_. Let's prove a handful of its
simplest results:

::::exercise (rating := 1) (name := "InverseUnique")
Two groups defined with the same operation over the same set must have the same inverse as well.

```lean
theorem inv_unique {α : Type} {g₁ g₂ : Group α} (h : g₁.op = g₂.op) :
  g₁.inv = g₂.inv := by
    solution!
      ext x
      rw [← g₁.right_id (Group.inv x), ← g₁.right_inv x]
      rw [g₁.assoc, h, g₂.left_inv, g₂.left_id]
```
:::gradeTheorem 1 inv_unique
:::
::::

:::dev "Daniel Sainati @dsainati1" PotentialImprovement
Taking suggestions for additional simple group theory theorems to prove here.
:::

::::exercise (rating := 1) (name := "IdentityUnique")
If an element of a monoid satisfies just one of the identity laws
(here, we take the left), then it must be equal to the monoid's identity element.

```lean
theorem Monoid.id_unique_left {α : Type} [Monoid α] (x : α)
    (hₗ : ∀ y, x ⊗ y = y) : x = id := by
  solution!
    rw [← right_id x]
    exact hₗ id
```

:::gradeTheorem 1 Monoid.id_unique_left
:::
::::

:::dev "@ionathanch" PotentialImprovement
To be honest I did not know how to prove this without the lemma
:::

::::exercise (rating := 2) (name := "InverseInverse")
The inverse of the inverse of an element is itself;
we prove this using an intermediate lemma.

```lean
theorem inv_inv' {α : Type} {g : Group α} (x y z : α)
    (h₁ : g.inv x = y) (h₂ : g.inv y = z) : x = z := by
  solution!
    calc x
      _ = g.id ⊗ x          := by rw [g.left_id x]
      _ = (g.inv y ⊗ y) ⊗ x := by rw [g.left_inv y]
      _ = g.inv y ⊗ (y ⊗ x) := by rw [g.assoc]
      _ = z ⊗ (y ⊗ x)       := by rw [h₂]
      _ = z ⊗ (g.inv x ⊗ x) := by rw [h₁]
      _ = z ⊗ g.id          := by rw [g.left_inv]
      _ = z                 := by rw [g.right_id]

theorem inv_inv {α : Type} {g : Group α} (x : α) :
  g.inv (g.inv x) = x := by
    solution!
      symm; apply inv_inv' (y := g.inv x) <;> rfl
```

:::gradeTheorem 1 inv_inv' inv_inv
:::
::::

```lean
end Algebra
```

:::dev "Niklas Halonen (xhalo32)" PotentialImprovement
-- # API and Encapsulation

===
This section is still only the outline below; there is no reader-facing prose yet. It is also not
free-standing: the bullets name exactly the vocabulary the Maps section below uses without ever
defining it — `get` as the "public API counterpart" to `inner`, `toTotal` playing the same role
for `PartialMap`, and the recurring pattern of `*_def` lemmas marked "exposes
implementation-specific details ... avoid using outside the X namespace." Revisit alongside
the Maps section to decide whether to write this section now, using `get`/`inner` and
`toTotal`/`inner` as the worked examples, or leave it as a stub.
===

Here, we should tie back the story from early chapters about characterizing lemmas and definition
unfolding. When unfolding a definition directly without characterizing lemmas, the implementation
details are exposed. When downstream code can depend on implementation details of upstream library
code, it makes it more difficult for the upstream library to evolve.

Explain the following items:
- What is API and how does it relate to typeclasses
- What is encapsulation: public and private API
  - Function definitions and one-field structures are encapsulation boundaries
  - Definitions and structures are usually private, characterizing lemmas are public
  - Constructors of inductives are public
  - Mention `public`, `private` keywords and that we don't use them on the course?
  - One can mostly ignore proof terms due to proof irrelevance

Here is an example where the proof term is blocking a rewrite.
The solution is to simplify it away.

```lean +error
-- set_option pp.proofs true in
example {n m : Nat} {a : Fin n} {b : Fin m} (h₁ : n = m) (h₂ : a.val = b.val) :
    a = ⟨b.val, h₁ ▸ b.isLt⟩ := by
  -- ext
  -- dsimp only
  rw [← h₂]
```
:::

# Maps

_Maps_ (or "dictionaries") are ubiquitous data structures both in ordinary programming and in the
theory of programming languages; we're going to need them in many places in later volumes.

Maps are also where the ideas in this chapter come together in a single, realistic example:
overloaded notation, typeclass-supplied defaults, and proof-carrying instances that guarantee a
data structure behaves the way we expect.

We'll define two flavors of maps: _total maps_, which include a "default" element to be returned
when a key being looked up doesn't exist, and _partial maps_, which instead return an option to
indicate success or failure. Partial maps are defined in terms of total maps, using {name}`none`
as the default element.

## Total Maps

The {ref "Lists"}[Lists] chapter introduced a partial map abstraction, `PartialMap`, with a
`find` function for lookup, based on lists of key-value pairs.
Here, we offer a map abstraction using functions instead.
The advantage of this representation is that it offers a more _extensional_ view of maps,
as we saw with functions in the {ref "Logic"}[Logic] chapter:
two maps that respond to every query in the same way will be represented as exactly the same function.
This simplifies proofs that use maps — we'll see exactly how once we start relating different
updates to each other, below.
We encapsulate them inside a `structure` which we call `TotalMap`.
Intuitively, a total map just contains a function `inner` from a key of type `α` to a value of type `β`.

```lean
structure TotalMap (α : Type) (β : Type) where
  inner : α → β
```

An "empty" {name}`TotalMap` is one that maps every `α` to the same (default) `β`.
We capture this idea using the {name}`Inhabited` typeclass,
which is the standard library's version of the {name}`DefaultValue` class we developed above.
The function `TotalMap.empty` yields an empty total map with the given default element.

```lean
namespace TotalMap

def empty {α β : Type} [Inhabited β] : TotalMap α β where
  inner := fun _ => default
```

Just as declaring {name}`BEq`/{name}`DefaultValue` instances above hooked `==`
and {name}`DefaultValue.value` up to our types, we can declare an instance of the standard
library's {name}`EmptyCollection` typeclass to associate `∅` with this empty map.

```lean
instance {α β : Type} [Inhabited β] : EmptyCollection (TotalMap α β) where
  emptyCollection := TotalMap.empty

theorem empty_def {α β : Type} [Inhabited β] :
    (∅ : TotalMap α β) = { inner := fun _ => default } := by rfl
```

Here, for example, is an empty map that takes `Nat` keys to `Nat` values:

```lean
def emptyNatMap : TotalMap Nat Nat := ∅
```

### Getting Elements

:::instructors
Note that `MyGetElem` has nothing to do with the encapsulation (`inner` vs `get`).
It's simply notation that expands to the public API (`get`).
:::

While {name}`TotalMap`s happen to be implemented as functions under the hood, we would prefer
not to expose this fact in their public interface.
Accordingly, we define a specific function for querying a map,
rather than expecting clients to call a {name}`TotalMap`'s `inner` function directly.
This function `get`, for getting the value associated with a key, plays the role that `find`
played for the {ref "Lists"}[Lists] chapter's list-based maps.

```lean
def get {α β : Type} (m : TotalMap α β) (a : α) := m.inner a

theorem get_def {α β : Type} {m : TotalMap α β} {a : α} :
  m.get a = m.inner a := by rfl

example : emptyNatMap.get 2 = 0 := by rfl
```

Function {name}`get` is the public API counterpart to {name}`inner`, which is an
implementation-specific detail of {name}`TotalMap`.
Because {name}`get_def` "peeks" through the abstraction, it should be used sparingly, and only
inside the `TotalMap` namespace.

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

To make element-getting more convenient, let's define notation so we can write
`emptyNatMap[2]` rather than {lean}`emptyNatMap.get 2`. We could notate {name}`get` directly —
we'll do exactly that for `update` below — but here we'll instead make "getting an element" its own
typeclass, `MyGetElem`, and notate it. Doing so means `m[a]` resolves to `MyGetElem.getElem m a`
for any type with a `MyGetElem` instance, not just `TotalMap`.

Using typeclasses to define notation is typical in Lean when the same notation is useful
for many different types.
We have seen the approach already with `==`: writing
`x == y` is notation for {name}`BEq.beq`, resolved by instance search for whatever type `x` and `y`
have. We also just saw overloaded notation for {name}`EmptyCollection` above,
where `∅` is notation for {name}`EmptyCollection.emptyCollection`.
Our typeclass `MyGetElem` is a simpler version of the standard library's {name}`GetElem` typeclass,
which has many instances such as {name}`Array`, {name}`List`, and {name}`Vector`.
We develop it to illustrate the notation-as-typeclass approach.

```lean
end TotalMap
```

The `MyGetElem` typeclass takes three type parameters: the collection implementation,
its keys, and its values.

```lean
class MyGetElem (coll : Type) (idx : Type) (elem : outParam Type) where
  getElem (xs : coll) (i : idx) : elem
```

(Don't worry about the `outParam` qualifier; it is a hint to Lean that helps typeclass inference.)

The appropriate instance of {name}`MyGetElem` for our {name}`TotalMap` is:

```lean
instance {α β : Type} : MyGetElem (TotalMap α β) α β where
  getElem m a := m.get a
```

Now we can associate the bracket syntax with {name}`MyGetElem.getElem`. We'll do so with the more
general `notation`/`macro_rules` forms, rather than the `infixl`/`infixr`/`scoped macro` forms we've
used for custom notation so far.

::::details "Notation encoding: `MyGetElem` brackets"
We've defined custom notation before — `::` and `[...]` for lists (chapter {ref "Lists"}[Lists],
including an `app_unexpander` for
printing `[...]`-notation lists back out), or `+`/`*`/`==` for arithmetic — but always with
`infixl`/`infixr` or `scoped macro`; this is the first time we reach for the more general
`notation`/`macro_rules` forms for getting the `m[a]` syntax to work. Chapters 5 and 6 of
[Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/)
contain more detail on this mechanism.

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
::::

Since we provided a {name}`MyGetElem` instance for {name}`TotalMap`, we can now use the
notation `m[a]` to access elements of a map `m`.

```lean
namespace TotalMap

theorem getElem_def {α β : Type} (m : TotalMap α β) (a : α) :
  m[a] = m.get a := by rfl

example : emptyNatMap[1] = default := by rfl

example {n : Nat} : emptyNatMap[n] = 0 := by
  rw [getElem_def, get_def, emptyNatMap]
  rw [empty_def, Nat.default_eq_zero]
```

We want the public API of {name}`TotalMap` to use the `m[a]` notation instead of `m.get a`,
so we provide the reverse direction of {name}`getElem_def` as a {tactic}`simp` lemma;
the `m[a]` notation is the {name}`TotalMap` API's {tactic}`simp` normal form.

```lean
@[simp]
theorem get_eq_getElem {α β : Type} (m : TotalMap α β) (a : α) :
  m.get a = m[a] := by rfl

example {n : Nat} : emptyNatMap.get n = emptyNatMap[n] := by
  simp
```

This design minimizes the need to use {name}`getElem_def` outside concrete examples
(which are typically solvable with {tactic}`rfl` anyway).

### Updating Elements

Now we turn to the `update` function, which takes a map `m`, a key `a`, and a value `b`,
and returns a new map that takes `a` to `b` and takes every other key to whatever `m` does.
We do this by wrapping a new map function around the old one.

```lean
def update {α β : Type} (m : TotalMap α β) [BEq α] (a : α) (b : β) :
  TotalMap α β where
    inner := fun a' => bif a == a' then b else m[a']
```

For example, we can build a map taking {name}`String` to {name}`Bool`,
where `"foo"` and `"bar"` are mapped to {name}`true` and every other key is mapped to {name}`false`,
like this:

```lean
def exampleMap :=
  (∅ : TotalMap String Bool)
    |>.update "foo" true
    |>.update "bar" true
```

Here `|>` is Lean's *pipe* notation: `x |>.f y` means `x.f y`, letting us chain a sequence of
function or method calls left to right without nested parentheses.
:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement
Should we introduce this notation earlier?  (Are there good places to use it earlier?)
:::

We also introduce a notation for updating maps — this time, rather than going through a typeclass
and its own `notation`/`macro_rules` machinery as we did for {name}`MyGetElem`, we write a `notation`
that references {name}`TotalMap.update` directly. Unlike indexing, {name}`update` doesn't need to work
generically across container types (there's no standard-library operation like {name}`GetElem` that
we're mirroring here), so the simpler, direct route suffices.

```lean
notation a:55 " →ₜ " b:55 " ; " m:55 => TotalMap.update m a b

theorem update_apply {α β : Type} [BEq α] (m : TotalMap α β)
  (a a' : α) (b : β) : (a →ₜ b ; m)[a'] =
  bif a == a' then b else m[a'] := by rfl
```

We can omit the map from the notation when we want it to be empty:

```lean
notation a:55 " →ₜ " b:55 => TotalMap.update ∅ a b
```

The `exampleMap` above can now be defined as follows:

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
  rw [exampleMap', update_apply, BEq.rfl, Bool.cond_true]

example : exampleMap'["foo"] = true := by
  have h : ("bar" == "foo") = false := by simp
  rw [exampleMap', update_apply, h, Bool.cond_false]
  rw [update_apply, BEq.rfl, Bool.cond_true]

example : exampleMap'["quux"] = false := by
  have h₁ : ("bar" == "quux") = false := by simp
  have h₂ : ("foo" == "quux") = false := by rfl
  rw [exampleMap', update_apply, h₁, Bool.cond_false]
  rw [update_apply, h₂, Bool.cond_false]
  rw [empty_def, getElem_def, get_def, Bool.default_bool]
```

Each `have ... = false by simp`/`by rfl` above goes through because `String`'s {name}`BEq` instance is
ultimately derived from its {name}`DecidableEq` instance — "Deciding Propositions" below explains this
mechanism in full (worked out there for {name}`Nat`, but the connection is general).

## Reasoning About Total Maps

When we use maps in later volumes, we'll need several fundamental properties about how they behave.
Several of these properties depend on {name}`BEq`, which our maps use to compare
keys of type `α`.

```recall
  class ReflBEq (α : Type) [BEq α] : Prop where
    rfl {a : α} : (a == a) = true
```

```recall
  class LawfulBEq (α : Type) [BEq α] : Prop extends ReflBEq α where
    eq_of_beq : {a b : α} → (a == b) = true → a = b
```

These classes refine {name}`BEq`, specifying that `==` is reflexive and coincides with
propositional equality `=`. Neither property is automatic: {name}`BEq`'s only obligation is to
return _some_ `Bool`, with no proof attached, so an arbitrary `BEq` instance could compute
anything at all, whether or not it agrees with `=`. We'll need both facts below: reflexivity to
show that looking up the key you just updated returns the new value, and agreement with `=` to
show that updating one key leaves lookups at every _other_ key unchanged. We'll return to this
distinction between `BEq` and provable equality in "Deciding Propositions" below.

Even if you don't work the following exercises, make sure you thoroughly understand the statements
of the lemmas! Some of the proofs require the extensionality tactic {tactic}`ext`,
discussed in the {ref "Logic"}[Logic] chapter.

Here is our first property, that the empty map returns its default element for all keys:

```lean
@[simp]
theorem getElem_empty {α β : Type} [BEq α] [Inhabited β] (a : α) :
  (∅ : TotalMap α β)[a] = default := by
    rw [empty_def, getElem_def, get_def]
```

Next, if we update a map `m` at a key `a` with a new value `b` and then look up `a` in the map
resulting from the {name}`update`, we get back `b`:

```lean
@[simp]
theorem update_eq {α β : Type} [BEq α] [ReflBEq α] (m : TotalMap α β)
  (a : α) (b : β) : (a →ₜ b ; m)[a] = b := by
    rw [update_apply, BEq.rfl, Bool.cond_true]
```

On the other hand, if we update a map `m` at a key `a₁` and then look up a _different_ key `a₂`
in the resulting map, we get the same result that `m` would have given:

::::exercise (rating := 2) (name := "update_neq")
```lean
@[simp]
theorem update_neq {α β : Type} [BEq α] [LawfulBEq α]
  {m : TotalMap α β} {a₁ a₂ : α} (h : a₁ ≠ a₂) (b : β) :
  (a₁ →ₜ b ; m)[a₂] = m[a₂] := by
  solution!
    rw [update_apply, beq_false_of_ne h, Bool.cond_false]
```
:::gradeTheorem 2 update_neq
:::
::::

The two remaining facts are equalities _between maps_, so we first need to say when two maps are
equal. Since a total map is implemented as a function,
this is effectively the functional extensionality principle ({name}`funext`) from the
{ref "Logic"}[Logic] chapter: two maps are equal when they agree at every key.
Recording it once, for maps, and tagging it `@[ext]` lets the {tactic}`ext` tactic reduce a
goal `m₁ = m₂` to the pointwise one in the proofs below.

The fact that {name}`TotalMap` is a structure complicates things slightly.
We need to use injectivity of its constructor {name}`mk`, which Lean automatically provides
for us as {name}`mk.injEq`. It lets us prove `m₁ = m₂` from `m₁.inner = m₂.inner` or vice versa.

```lean
@[ext]
theorem ext {α β : Type} {m₁ m₂ : TotalMap α β}
  (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := by
    rw [TotalMap.mk.injEq]
    ext a; specialize h a
    rw [getElem_def, get_def, getElem_def, get_def] at h
    exact h
```

This proof amounts to peeling off the {name}`TotalMap` wrapper via
{name}`mk.injEq`, making the goal an equality between the underlying `.inner` functions. Then the inner
{tactic}`ext` call finishes it by invoking {name}`funext` — the standard library's extensionality
principle for _every_ function type, already proved once and for all, with nothing
{name}`TotalMap`-specific left to establish. This is the proof-simplifying payoff of representing
maps as functions.

:::dev "Mike Hicks (mwhicks1)" PotentialImprovement
Claude suggested the following, but I'm not sure I buy it, so leaving it out:

A hand-rolled representation doesn't get this for free. Consider the {ref "Lists"}[Lists] chapter's
list-based `PartialMap`: updating the same key to the same value twice, `update (update empty x 1) x
1`, agrees with a single `update empty x 1` at every key, but the two are _not_ equal as `PartialMap`
values — the shadowed entry is a genuinely different (longer) term, so the obvious extensionality
statement is simply false for that type, not just hard to prove. Getting an analogous `@[ext]`
principle for such a representation would mean changing the type itself — quotienting it by "same
`find` behavior" — not just writing one more lemma.

It's an attempted answer to a prior question from Niklas (xhalo32) about why the functional
approach is better. Not sure!
:::

To demonstrate this extensionality principle, let's look at an example:

```lean
example : "bar" →ₜ true ; "foo" →ₜ true = "foo" →ₜ true ; "bar" →ₜ true := by
  ext a
  by_cases h : "bar" = a
  · subst h
    have h' : "foo" ≠ "bar" := by simp
    rw [update_eq, update_neq h', update_eq]
  · simp only [update_apply]
    rw [beq_false_of_ne h]
    simp
```

Given keys `a₁` and `a₂`, the tactic {tactic}`by_cases` `h : a₁ = a₂`
splits the proof into the case where they are equal
— where `subst h` then replaces one by the other —
and the case where they are not, which is what {name}`update_neq` wants.
Use it to prove the following theorem,
which states that if we update a map to assign key `a` the same value as it already has in `m`,
then the result is equal to `m`:

::::exercise (rating := 2) (name := "update_same")
```lean
@[simp]
theorem update_same {α β : Type} [BEq α] [LawfulBEq α] (m : TotalMap α β)
  (a : α) : (a →ₜ m[a] ; m) = m := by
    solution!
      ext a'
      by_cases h : a = a'
      · subst h
        simp
      · simp [update_neq h]
```
:::gradeTheorem 2 update_same
:::
::::

Similarly, if we update a map `m` at a key `a` with a value `b₁`
and then update again with the same key `a` and another value `b₂`,
the resulting map behaves the same (gives the same result when applied to any key)
as the simpler map obtained by performing just the second {name}`update` on `m`:

::::exercise (rating := 2) (name := "update_shadow") (optional := true)
```lean
@[simp]
theorem update_shadow {α β : Type} [BEq α] [LawfulBEq α] (m : TotalMap α β)
  (a : α) (b₁ b₂ : β) : (a →ₜ b₂ ; a →ₜ b₁ ; m) = (a →ₜ b₂ ; m) := by
  solution!
    ext a'
    by_cases h : a = a'
    · subst h
      simp
    · simp [update_neq h]
```
::::

Now prove one final property of the {name}`update` function:
if we update a map `m` at two distinct keys,
it doesn't matter in which order we do the updates.

::::exercise (rating := 3) (name := "update_permute")
```lean
theorem update_permute {α β : Type} [BEq α] [LawfulBEq α]
  {m : TotalMap α β} {a₁ a₂ : α} {b₁ b₂ : β} (h : a₁ ≠ a₂) :
  (a₁ →ₜ b₁ ; a₂ →ₜ b₂ ; m) = (a₂ →ₜ b₂ ; a₁ →ₜ b₁ ; m) := by
  solution!
    ext a
    by_cases h₁ : a₁ = a
    · subst h₁
      rw [update_eq, update_neq h.symm, update_eq]
    · rw [update_neq h₁]
      by_cases h₂ : a₂ = a
      · subst h₂
        rw [update_eq, update_eq]
      · rw [update_neq h₂, update_neq h₂, update_neq h₁]
```

:::gradeTheorem 3 update_permute
:::
::::

```lean
end TotalMap
```

## Notation for Concrete Maps

Wouldn't it be nice if we could use a more natural notation for concrete maps like
`{ "bar" ↦ true, "foo" ↦ true }`? To accomplish this, we define a simple structure that
consists of a key and a value, along with `↦` notation for it.

```lean
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
  insert_empty_eq _ := by rfl

end TotalMap
```

Here are a couple of examples using the new notation:

```lean
example : ({ "bar" ↦ true, "foo" ↦ true }) = "bar" →ₜ true ; "foo" →ₜ true := by rfl

example : ({ "foo" ↦ true } : TotalMap String Bool)["foo"] = true := by rfl

example : ({ 1 ↦ 2, 1 ↦ 3 } : TotalMap Nat Nat)[1] = 2 := by rfl
```

The reason we need to explicitly specify the type of the map is that
Lean doesn't know what type of collection `{ "foo" ↦ true }` is without type hints,
as we can see with `#check`:

```lean (name := foo)
#check { "foo" ↦ true }
```

```leanOutput foo
{"foo" ↦ true} : ?m.4
```

The type shows a `?m.4`, which indicates that Lean can't infer the type.
A type which can't be inferred doesn't have any type classes like {name}`MyGetElem`,
so typeclass resolution gets stuck in the following example:

```lean -keep +error
example : ({ "foo" ↦ true })["foo"] = true := by rfl
```

## Partial Maps

Lastly, we define _partial maps_ on top of total maps. A partial map with elements of type `β` is
simply a total map with elements of type `Option β`, whose default element is {name}`none`.

```lean
structure PartialMap (α : Type) (β : Type) where
  inner : TotalMap α (Option β)

instance {α β : Type} : EmptyCollection (PartialMap α β) where
  emptyCollection := { inner := ∅ }
```

Note that the definition of {name}`EmptyCollection` doesn't need `β` to have an {name}`Inhabited`
instance like {name}`TotalMap` did. This is because `Option β` has its own {name}`Inhabited`
instance: {lean}`none` is a value of every {name}`Option` type.

Now let's define a {name}`PartialMap`'s operations. We will do so using those of {name}`TotalMap`
via `PartialMap.toTotal`.

```lean
namespace PartialMap

def toTotal {α β : Type} (m : PartialMap α β) : TotalMap α (Option β) := m.inner

theorem toTotal_def {α β : Type} (m : PartialMap α β) : m.toTotal = m.inner := by rfl
```

Note that {name}`toTotal_def` exposes implementation-specific details of `PartialMap`.
So we should aovid using this outside the `PartialMap` namespace. Now we can define the
`getElem` operation.

```lean
instance {α β : Type} : MyGetElem (PartialMap α β) α (Option β) where
  getElem m a := m.toTotal[a]

theorem getElem_def {α β : Type} (m : PartialMap α β) (a : α) : m[a] = m.toTotal[a] := by rfl
```

Here are some examples.

```lean
def emptyNatMap : PartialMap Nat Nat where
  inner := ∅

example : emptyNatMap[1] = default := by rfl

example {n : Nat} : emptyNatMap[n] = none := by
  rw [getElem_def, toTotal_def, emptyNatMap]
  dsimp only
  rw [TotalMap.getElem_def, TotalMap.get_def]
  rw [TotalMap.empty_def, Option.default_eq_none]
```

We again want the public API to use the `m[a]` notation (instead of `m.toTotal[a]`),
so we provide the reverse direction of {name}`getElem_def` as a {tactic}`simp` lemma
to specify that the {tactic}`simp` normal form is `m[a]`.

```lean
@[simp]
theorem toTotal_eq_getElem {α β : Type} (m : PartialMap α β) (a : α) :
    m.toTotal[a] = m[a] := by rfl
```

Now let's turn to the `update` operation.
Updating a partial map at a key means storing a {name}`some` value there.
So we create a new partial map from `a →ₜ some b ; m.toTotal`
by wrapping it in angle brackets, i.e., using the anonymous constructor syntax.
This is equivalent to writing `{ inner := a →ₜ some b ; m.toTotal }`.
We also introduce a similar notation for it as for total maps.

```lean
def update {α β : Type} [BEq α] (m : PartialMap α β) (a : α) (b : β) : PartialMap α β :=
  ⟨a →ₜ some b ; m.toTotal⟩

notation a:55 " →ₚ " b:55 " ; " m:55 => PartialMap.update m a b

notation a:55 " →ₚ " b:55 => PartialMap.update ∅ a b

def examplePmap : PartialMap String Bool := "Church" →ₚ true ; "Turing" →ₚ false
```

Now we can provide some fundamental properties about {name}`toTotal`:

```lean
@[simp]
theorem toTotal_empty {α β : Type} : (∅ : PartialMap α β).toTotal =
  (∅ : TotalMap α (Option β)) := by rfl

@[simp]
theorem toTotal_update {α β : Type} [BEq α] (m : PartialMap α β)
  (a : α) (b : β) : (a →ₚ b ; m).toTotal = a →ₜ some b ; m.toTotal := by rfl
```

As an example, here's how we can use these on some concrete maps:

```lean
example : (2 →ₚ 3)[2] = some 3 := by
  rw [getElem_def, toTotal_update, toTotal_empty, TotalMap.update_eq]
```

This also holds by definition ({tactic}`rfl`),
since all the rewrites in the above proof do the computation step-by-step.

```lean
example : (2 →ₚ 3)[2] = some 3 := by rfl
```

Next, we lift all of the basic lemmas about total maps to partial maps.
To do this, we should first prove an extensionality lemma about partial maps.
To prove extensionality, we employ injectivity of {name}`PartialMap`'s constructor {name}`mk`
using {name}`mk.injEq`.

```lean
theorem toTotal_eq_iff {α β : Type} (m₁ m₂ : PartialMap α β) :
  m₁.toTotal = m₂.toTotal ↔ m₁ = m₂ := by
    rw [mk.injEq]
    rfl

@[ext]
theorem ext {α β : Type} {m₁ m₂ : PartialMap α β}
  (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := by
    rw [← toTotal_eq_iff]
    exact TotalMap.ext h
```

Now, let's lift the {name}`TotalMap` lemmas:

```lean
@[simp]
theorem getElem_empty {α β : Type} [BEq α] (a : α) :
  (∅ : PartialMap α β)[a] = none := by
    rw [getElem_def, toTotal_empty, TotalMap.getElem_empty, Option.default_eq_none]

@[simp]
theorem update_eq {α β : Type} [BEq α] [ReflBEq α]
  (m : PartialMap α β) (a : α) (b : β) : (a →ₚ b ; m)[a] = some b := by
    rw [getElem_def, toTotal_update, TotalMap.update_eq]

@[simp]
theorem update_neq {α β : Type} [BEq α] [LawfulBEq α]
  {m : PartialMap α β} {a₁ a₂ : α} (h : a₁ ≠ a₂) (b : β) :
  (a₁ →ₚ b ; m)[a₂] = m[a₂] := by
    simp only [getElem_def, toTotal_update]
    rw [TotalMap.update_neq h]

theorem update_shadow {α β : Type} [BEq α] [LawfulBEq α]
  (m : PartialMap α β) (a : α) (b₁ b₂ : β) :
  (a →ₚ b₂ ; a →ₚ b₁ ; m) = (a →ₚ b₂ ; m) := by
    apply ext
    intro x
    simp only [getElem_def, toTotal_update]
    rw [TotalMap.update_shadow]

theorem update_same {α β : Type} [BEq α] [LawfulBEq α] {m : PartialMap α β}
  {a : α} {b : β} (h : m[a] = some b) : (a →ₚ b ; m) = m := by
    apply ext
    intro x
    simp only [getElem_def, toTotal_update]
    rw [← h, getElem_def, TotalMap.update_same]

theorem update_permute {α β : Type} [BEq α] [LawfulBEq α]
  {m : PartialMap α β} {a₁ a₂ : α} {b₁ b₂ : β} (h : a₁ ≠ a₂) :
  (a₁ →ₚ b₁ ; a₂ →ₚ b₂ ; m) = (a₂ →ₚ b₂ ; a₁ →ₚ b₁ ; m) := by
    apply ext
    intro x
    simp only [getElem_def, toTotal_update]
    rw [TotalMap.update_permute h]

example : (2 →ₚ 3)[2] = some 3 := by
  simp

example : examplePmap["Post"] = none := by
  rw [examplePmap]
  simp
```

And let's add `{}`-notation for partial maps as well.

```lean
instance {α β : Type} [BEq α] : Insert (KVPair α β) (PartialMap α β) where
  insert kv m := kv.key →ₚ kv.value ; m

instance {α β : Type} [BEq α] : Singleton (KVPair α β) (PartialMap α β) where
  singleton kv := insert kv ∅

instance {α β : Type} [BEq α] : LawfulSingleton (KVPair α β) (PartialMap α β) where
  insert_empty_eq _ := by rfl

example : { 1 ↦ 2, 2 ↦ 3 } = 1 →ₚ 2 ; 2 →ₚ 3 := by rfl
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
    m₁ ⊆ m₂ ↔ (∀ {a : α} {b : β}, m₁[a] = some b → m₂[a] = some b) := by rfl
```

We can then show that map update preserves map inclusion, that is:

```lean
theorem update_subset {α β : Type} [BEq α] [LawfulBEq α] (m₁ m₂ : PartialMap α β) (a : α) (b : β)
    (h : m₁ ⊆ m₂) : (a →ₚ b ; m₁) ⊆ (a →ₚ b ; m₂) := by
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

This property is quite useful for reasoning about languages with variable binding —
e.g., the Simply Typed Lambda Calculus, which we will see in _Type Systems_,
where maps are used to keep track of which program variables are defined in a given scope.

# Deciding Propositions

The {ref "Logic"}[Logic] chapter's "Working with Decidable Properties" section explored the
trade-offs between stating a claim as a boolean (of type {name}`Bool`) and as a proposition (of
type {lean}`Prop`). Here, we tie up a loose end from the start of this chapter, and along the way
formalize _decidability_ itself as a typeclass.

## {name}`Decidable` and Equality

Recall from "Why We Need Typeclasses" that `[0, 1].elemPoly 0`'s `==` is filled in automatically by
Lean, in contrast to `[0, 1].elemPolyEq Nat.beq 0`, which is handed {name}`Nat.beq` explicitly.
It's tempting to assume Lean fills in that very {name}`Nat.beq` function as the required {name}`BEq`
instance — but it doesn't. We can see this by asking Lean to synthesize the instance directly:

```lean (name := synthBEqNat)
#synth BEq Nat
```

```leanOutput synthBEqNat
instBEqOfDecidableEq
```

What is this? Recall that {name}`BEq`'s only field is `beq : α → α → Bool`.
{name}`instBEqOfDecidableEq` builds a `BEq α` instance by setting `beq a b := decide (a = b)`.
What is {name}`decide`? Let's see:
```lean (name := decide_type)
#check @decide
```

```leanOutput decide_type
decide : (p : Prop) → [h : Decidable p] → Bool
```
We can see that {name}`decide` takes a proposition (like `a = b`) and a proof that that
proposition is decidable (i.e., `Decidable (a = b)`), and returns a `Bool` corresponding
to the truth or falsehood of that proposition. What does it mean for a proposition to
be {name}`Decidable`? Here is its definition:

```recall
class inductive Decidable (p : Prop) where
  /-- Proves that `p` is decidable by supplying a proof of `¬ p` -/
  | isFalse (h : Not p) : Decidable p
  /-- Proves that `p` is decidable by supplying a proof of `p` -/
  | isTrue (h : p) : Decidable p
```

In other words, `Decidable p` expresses that a single proposition `p` can be settled one way or the
other, computationally. (But "computationally" is caveated: later we'll see that classical
axioms can manufacture a `Decidable p` instance that doesn't compute, and explain what that means.)
Like {name}`HasTwo`'s `one_neq_two` field earlier in this chapter,
{name}`Decidable.isTrue`/{name}`Decidable.isFalse` are proof-carrying: each one packages a
proof — of `p` or of `¬p` — alongside which case holds. {name}`instBEqOfDecidableEq` references
`DecidableEq α`, which means `∀ a b : α, Decidable (a = b)`, i.e., it's a shorthand for
having one of these proof-carrying values for every equality proposition `a = b` in `α`.

Because `decide (a = b)` genuinely computes whether `a = b` holds, deriving `BEq` from
`DecidableEq` this way also guarantees the result is {name}`LawfulBEq`: the `beq` it
produces is certain to agree with `=`. That guarantee is a fact about _this_ instance, though, not
something {name}`BEq` demands of every instance — as the Maps section noted, `beq`'s only
obligation is to return _some_ `Bool`, with no proof attached, unlike `Decidable`'s constructors,
whose whole point is to carry one. {name}`List.elemPoly`'s `[BEq α]` constraint is therefore the
weakest assumption sufficient for a purely computational membership test: it doesn't require the
caller to have decidable equality, or even a comparison that agrees with `=`, at all.

:::dev "Mike Hicks (mwhicks1)" PotentialImprovement
Worth a sentence on the limits of `DecidableEq` inference: can a synthesized instance ever be
slower than a handwritten `beq`, and are there types for which Lean can't synthesize one at all?
:::

This is also why the chapter's earlier hand-written `BEq Nat` instance — the low-priority one built
directly from {name}`Nat.beq` — is a worse choice, not just a redundant one. `Nat.beq` does happen
to agree with `=`, but nothing tells Lean that automatically: proving that hand-written instance
is {name}`LawfulBEq` would take its own separate induction on `Nat.beq`'s recursive definition.
Deriving `BEq Nat` from `DecidableEq Nat` sidesteps that work entirely — the proof of
agreement is already carried by the `Decidable` instance, as we saw above — which is exactly why
the standard library prefers it.

A {name}`Decidable` instance also allows computation — branching — on the truth/falsehood of a
proposition. You can write `if p then a else b` where `p` is a {lean}`Prop` and `a` and `b` are
expressions of some type `α`. For example, we can write

```lean (name := if_eval_output)
#eval if 2 = 3 then "wrong" else "ok"
```

```leanOutput if_eval_output
"ok"
```

Here, Lean synthesizes a {name}`Decidable` instance for the proposition {lean}`2 = 3` which
`if` (under the covers: {name}`ite`) case-splits on, returning the `then` branch's result
on matching the {lean}`isTrue` case and the `else` branch's result on the {lean}`isFalse` case.
Asking Lean to synthesize the instance for this branched-on proposition shows which one gets used:

```lean (name := synthNatEq)
#synth Decidable (2 = 3)
```

```leanOutput synthNatEq
instDecidableEqNat 2 3
```

What is this? Let's see.

```lean (name := instDecidableEqNat_print)
#print instDecidableEqNat
```

```leanOutput instDecidableEqNat_print
@[instance_reducible] def instDecidableEqNat : DecidableEq Nat :=
Nat.decEq
```

Going one layer deeper ...

```lean (name := decidable_eq_nat_print)
#print Nat.decEq
```

```leanOutput decidable_eq_nat_print
@[reducible] protected def Nat.decEq : (n m : Nat) → Decidable (n = m) :=
fun n m =>
  match h : n.beq m with
  | true => isTrue ⋯
  | false => isFalse ⋯
```

So we have landed back at {name}`Nat.beq`! It computes the result as a {name}`Bool` and then
{name}`Nat.decEq` returns a proof of that computation's result in a {name}`Decidable` instance.
Above, our synthesized {name}`Decidable` instance was for a particular equality, but
it was just an application of {lean}`instDecidableEqNat` to a particular pair of {name}`Nat`s,
so {lean}`instDecidableEqNat` will get used in the general case, too.

```lean
def nat_eq (m n : Nat) : Bool := if m = n then true else false
```

But if we slightly generalize this function, it will fail.

```lean -keep +error (name := generalEqError)
def eq {α : Type} (x y : α) : Bool := if x = y then true else false
```

```leanOutput generalEqError
failed to synthesize instance of type class
  Decidable (x = y)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

Lean cannot synthesize a decidable equality instance for arbitrary types, and gives the same sort
of error we saw at the beginning of this chapter when defining {name}`List.elemPoly`. And the
solution is the same too: Add an instance implicit.

```lean
def eq_dec {α : Type} [DecidableEq α] (x y : α) : Bool :=
  if x = y then true else false
```

Lean provides some automation for proofs of propositions that are {name}`Decidable`, in
the form of the {tactic}`decide` tactic — not to be
confused with the {name}`decide` _function_ from earlier. The function merely computes a `Bool`
from a `Decidable` instance; the tactic instead closes a goal `p` outright, by computing that
`decide p` reduces to `true` and invoking the connection between the two (made precise below):

```lean
example : 3 = 3 := by decide
example : 2 ≠ 3 := by decide
```

The {tactic}`decide` tactic rests on two lemmas relating a `Decidable` instance's underlying
boolean to the proposition it decides: {name}`decide_eq_true_iff` says
`decide p = true ↔ p`, and {name}`decide_eq_false_iff_not` says
`decide p = false ↔ ¬p`. `decide` reduces the goal `p` to computing whether `decide p`
evaluates to `true`, then invokes the first of these.

## {name}`Decidable` Beyond Equality

{name}`instDecidableEqNat` works automatically because Lean's core library derives it for us — but
not every proposition we might want to {tactic}`decide` comes with a ready-made instance.
Sometimes we have to build one ourselves. Let's revisit the {ref "Logic"}[Logic] chapter's "even"
example to see what that looks like: it stated the property as both `Nat.even` (a {name}`Bool`
computation) and `Nat.Even` (a {lean}`Prop`), connected by _reflection_ via `Nat.even_bool_prop`.
We restate the relevant pieces here, in their own namespace (dropping the `Nat.` prefix), so they
don't require that chapter's import:

```lean
namespace Reflection
```

```lean
def even (n : Nat) :=
  match n with
  | 0     => true
  | 1     => false
  | n + 2 => even n

theorem even_zero : even 0 = true := by rfl

theorem even_succ (n : Nat) :
    even (n + 1) = !(even n) := by
  induction n with
  | zero =>
    rfl
  | succ n' ih =>
    rw [even, ih, Bool.not_not]

def double (n : Nat) : Nat :=
  match n with
  | 0    => 0
  | n' + 1 => double n' + 2

theorem double_zero : double 0 = 0 := by rfl

theorem double_succ (n : Nat) : double (n + 1) = double n + 2 := by rfl

def Even x := ∃ n : Nat, x = double n

theorem even_double (k : Nat) : even (double k) = true := by
  induction k with
  | zero =>
    rw [double_zero, even_zero]
  | succ n ih =>
    rw [double_succ, even_succ, even_succ, Bool.not_not]
    exact ih

theorem even_double_exists (n : Nat) :
    ∃ (k : Nat), n = bif even n then double k else double k + 1 := by
  induction n with
  | zero =>
    exists 0
  | succ n ih =>
    obtain ⟨k, ih⟩ := ih
    rewrite [even_succ]
    by_cases h : even n
    · exists k
      rw [h] at ih ⊢
      subst ih
      rfl
    · exists k + 1
      rw [Bool.not_eq_true] at h
      rw [h] at ih ⊢
      subst ih
      rw [Bool.cond_false, Bool.not_false, Bool.cond_true]
      rfl

theorem even_iff_Even {n : Nat} : even n = true ↔ Even n where
  mp h := by
    have ⟨k, hk⟩ := even_double_exists n
    rw [h, Bool.cond_true] at hk
    subst hk
    exists k
  mpr h := by
    obtain ⟨k, hk⟩ := h
    subst hk
    exact even_double k
```

{name}`even_iff_Even` (our copied-in version of `Nat.even_bool_prop` from {ref "Logic"}[Logic])
is the kind of iff-shaped reflection lemma we need: the standard
library's {name}`decidable_of_decidable_of_iff` carries a `Decidable` instance across any `p ↔ q`
— from `Decidable p` to `Decidable q`. Applying it here is all it takes to build a custom
`Decidable (Even n)` instance:

```lean
instance (n : Nat) : Decidable (Even n) :=
  decidable_of_decidable_of_iff even_iff_Even
```

Its type shows exactly what it needs and produces:

```lean (name := checkDdi)
#check @decidable_of_decidable_of_iff
```

```leanOutput checkDdi
@decidable_of_decidable_of_iff : {p q : Prop} → [Decidable p] → (p ↔ q) → Decidable q
```

Given a `Decidable p` instance and a proof `p ↔ q`, it produces a `Decidable q`. Here, `p` is
`even n = true` — already decidable, since equality of {name}`Bool`s always is — and `q` is
`Even n`; {name}`even_iff_Even` supplies the connecting `p ↔ q`. Under the hood, it checks whether
`p` holds (using the `Decidable p` instance it was given) and uses the iff to turn that proof of
`p` or `¬p` into one of `q` or `¬q`, which it then packages with
{name}`Decidable.isTrue`/{name}`Decidable.isFalse`.

Now we can complete such proofs by computation, using the {tactic}`decide` tactic, and
use `Even` in `if` expressions.

```lean
#check if Even 2 then "is even" else "is odd"
def odd (n : Nat) : Bool :=
  if Even n then false else true
example : Even 2 := by decide
example : Even 4 := by decide
example : Even 6 := by decide
example : Even 100 := by decide
example : ¬ Even 101 := by decide
example : ∀ n < 10, Even (2 * n) := by decide
example : ∀ n < 10, Even (2 * n) ∧ ¬ Even (2 * n + 1) := by decide
```

::::dev "Mike Hicks (mwhicks1)" PotentialImprovement

The following seems useful but I don't know where to put it.

The standard library's {name}`decidable_of_bool` builds a `Decidable p` the same general way, but
starting from a {name}`Bool` `b` and a proof `b = true ↔ p`, rather than from an existing
`Decidable` instance: it case-splits on `b` and packages the result with the
{name}`Decidable.isTrue`/{name}`Decidable.isFalse` constructors from the `recall` block above. We
can write that same case split by hand:

```lean
example {p : Prop} (b : Bool) (h : b = true ↔ p) : Decidable p := by
  by_cases hb : b
  · apply isTrue
    simp [← h, hb]
  · apply isFalse
    simp [← h, hb]
```
::::

## {name}`Decidable` and Classical Logic

Computable instances like {name}`instDecidableEqNat` and the one we built for `Even` are only half
the story. Lean is also often used in applications where we don't care about
computability, such as pure mathematics. The {ref "Logic"}[Logic] chapter's "Classical vs.
Constructive Logic" section already showed how `Classical.choice` lets Lean prove `p ∨ ¬ p` for an
_arbitrary_ proposition `p` via {name}`Classical.em`, something no computable procedure could do in
general. The same axiom lets Lean manufacture a `Decidable p` instance for arbitrary `p`, letting us
write a function for arbitrary equality that no decision procedure could actually compute:

```lean -keep (name := eqNoncompPrint)
open scoped Classical in
noncomputable def eq {α : Type} (x y : α) := if x = y then true else false

set_option pp.all true in
#print eq
```

```leanOutput eqNoncompPrint
def Reflection.eq : {α : Type} → (x y : α) → Bool :=
fun {α : Type} (x y : α) => @ite.{1} Bool (@Eq.{1} α x y) (Classical.propDecidable (@Eq.{1} α x y)) Bool.true Bool.false
```

But we have indicated to Lean, using the `noncomputable` keyword and `Classical` namespace,
that we are _not_ interested in computation.
What is happening in the background is that this allows
typeclass synthesis to find the scoped instance {name}`Classical.propDecidable`, which makes use of
the axiom of choice to provide a proof that all propositions are _classically_ decidable. This
sort of definition is suitable for use with proofs, but is not allowed to be used in conjunction
with computational features of Lean such as the {tactic}`decide` tactic or the `#eval` command.

To see this concretely, consider Maps section's {name}`TotalMap.update_same` exercise,
proves that updating a map with the value already stored there changes nothing, for a fully
generic `α` constrained only by `[BEq α] [LawfulBEq α]`. If you use
{tactic}`by_cases` `h : a = a'` in your proof and then do `#print axioms update_same`
you will see `Classical.choice` in the list. If you additionally require `[DecidableEq α]` along
with `[BEq α]` and `[LawfulBEq α]`, though, then you bring a genuine decision
procedure for equality in scope, and {tactic}`by_cases` splits on it directly rather than
falling back to the excluded middle. Try it out!

:::dev PotentialImprovement
This section could use a handful (5-6) of further worked exercises connecting `Decidable` and
`decide` to concrete reasoning tasks — starting with simple `Nat` properties and then moving to
richer examples in the style of the IndProp chapter's `reflect`/`reflect_iff` idiom, which relates
a `Bool` directly to a `Prop` (unlike `Decidable`, which only carries the proposition, not the
original boolean).
:::

```lean
end Reflection
```
