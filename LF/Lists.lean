import SFLMeta

import LF.Induction
import LF.UsingLean

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Lists: Working with Structured Data" =>
%%%
tag := "Lists"
htmlSplit := .never
file := some "Lists"
%%%

:::dev "Daniel Sainati (dsainati1)"
\[BCP: Old comment -- might be out of date?\]
Weird that this file contains the first `inductive` definition students have seen up to this point,
but that definition is also actually a `structure`. Probably need to restructure this.

Unsure if it's a good idea to actually use the built-in `List` definition here, since it's polymorphic,
and we aren't introducing this idea until a later chapter. This also means we don't get the chance
to show students how to actually produce an inductive definition if we're relying on the built-in ones.

We probably need to actually take time to explain what a `@[simp]` annotation on a lemma
means before we introduce it, and I don't think this chapter is the right place to do it anyway.
This is probably a better fit for `Auto.lean`.

Claude picked a bad definition for `nonzeroes`:
```
  match l with
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
```
which makes many of the later proofs hard to do without the full automation of `simp`.
I changed it, but it's worth pointing this out.
:::

:::dev "Konstantinos Kallas (angelhof)"
The `Baz` "how many elements does this type have?" exercise (the last exercise
in the chapter) is a *manual* exercise, and that's a poor fit: a student who
doesn't realize an inductive definition needs a base case will simply fail it and
only see why in the grader comment — and it's easy to wrongly think you have the
right answer and move on without thinking. Better to either add a short section
that explains this directly, or add a hint like the `one_true_baz` / `count_trues`
scaffold ("try to write a value of type `Baz` for which the lemma holds"). Worth
reworking for easier grading.
:::

:::instructors
This file takes about 60 minutes to get through.
Putting it together with Induction.lean makes a reasonable
second week's homework assignment.
:::

:::dev BeforeNextRelease
```
(BCP 9/18) Since the domain type of Maps has changed from
id to string, we should either do the same here (in the partial
maps section) or else comment there that we are making a different
choice.  For the moment, it feels cleaner to avoid importing the
string library, explaining or handwaving string_dec, etc., so I've
added a comment there. BCP 25: I wonder whether we can get away
with just using (... =? ...)%string instead of string_dec.  Would
make it a lot more palatable. I now think this is probably a good
idea. However: At the moment, the Stdlib has String.eqb to compare
strings, but it returns a standard bool, which is not the one we
are using. We'd have to put our booleans inside a module in
Basics.v. That's probably fine. After that, I think we just have to
alias Definition Id := string).
```

This chapter could use another WORKINCLASS or three.
:::

```importBlock
import LF.Induction
import LF.UsingLean
```

::::full
This chapter introduces basic data structures and functions for working with
them. We place all these definitions in the `Lists` namespace to avoid name
clashes with Lean's standard library and with definitions from other chapters.
::::

```lean
namespace Lists
```

:::dev BeforeNextRelease
Note that rewrite laws should sometimes differ from pattern matching now
:::

# Pairs of Numbers

::::full
In an `inductive` type definition, each constructor can take
any number of arguments -- none (as with `true` and `0`),
one (as with `succ`), or more than one (as with `Nibble` and
the following):
::::

::::terse
An inductive definition of pairs of numbers.  It has just
one constructor, taking two arguments:
::::

```lean
inductive NatProd where
  | pair (n1 n2 : Nat)
```

::::full
This declaration can be read: "The one and only way to
construct a pair of numbers is by applying the constructor `pair`
to two arguments of type `Nat`."
::::

```lean
#check (NatProd.pair 3 5)
```

:::slidebreak
:::

Functions for extracting the first and second components of a pair
can then be defined by pattern matching.

```lean
def NatProd.fst (p : NatProd) : Nat :=
  match p with
  | .pair x _ => x

def NatProd.snd (p : NatProd) : Nat :=
  match p with
  | .pair _ y => y
```

Defining these functions with the `NatProd` type name qualifying their name
allows us to use them with `.` notation:

```lean
example : (NatProd.pair 3 5).fst = 3 := by rfl
```

:::slidebreak
:::

::::full
Since pairs will be used heavily in what follows, it will be
convenient to write them with angle bracket notation `⟨x, y⟩`
instead of `NatProd.pair x y`.  This notation is built into Lean and is
called "anonymous constructor syntax".  It is available for any inductive
type with a single constructor, as long as the expected type is declared or
can be inferred from the context.
::::

:::terse
A nicer notation for pairs:
:::

```lean
example : (⟨3, 5⟩ : NatProd).fst = 3 := by rfl
```

The anonymous constructor can be used in both expressions and in pattern matches.

```lean
def fst' (p : NatProd) : Nat :=
  match p with
  | ⟨x, _⟩ => x

def snd' (p : NatProd) : Nat :=
  match p with
  | ⟨_, y⟩ => y

def NatProd.swap (p : NatProd) : NatProd :=
  ⟨snd p, fst p⟩
```

::::full
Note that pattern-matching on a pair (with angle brackets: `⟨x, y⟩`)
is not to be confused with the "multiple pattern" syntax (with no
brackets: `x, y`) that we have seen previously.  The above
examples illustrate pattern matching on a pair with elements `x`
and `y`, whereas, for example, the definition of `sub` in
{ref "Basics"}[Basics] performs pattern matching on the values `n` and `m`:

```lean
def sub (n m : Nat) : Nat :=
  match n, m with
  | 0,        _        => 0
  | .succ _,  0        => n
  | .succ n', .succ m' => sub n' m'
```

The distinction is minor, but it is worth understanding that they
are not the same. For instance, the following definitions are
ill-formed:

```lean +error
-- Can't match on a pair with multiple patterns:
def bad_fst (p : NatProd) : Nat :=
  match p with
  | x, y => x

-- Can't match on multiple values with pair patterns:
def bad_sub (n m : Nat) : Nat :=
  match n, m with
  | ⟨0,        _⟩       => 0
  | ⟨.succ _,  0⟩        => n
  | ⟨.succ n', .succ m'⟩ => sub n' m'
```
::::

:::dev "Daniel Sainati (dsainati1)" NOW
Wrote this, let me know how it reads.
:::

Lean also provides a convenient way to define `inductive` structures like pairs
that have a single constructor but multiple ways to access their data,
using the `structure` keyword. The definition of `NatProd'` below is equivalent
to the `NatProd` definition from earlier, except that Lean automatically
generates the `fst` and `snd` accessors.

```lean
structure NatProd' where
  fst : Nat
  snd : Nat

#check (NatProd'.mk 3 5)
example : (NatProd'.mk 3 5).fst = 3 := by rfl
example : (⟨3, 5⟩ : NatProd').fst = 3 := by rfl
```

:::slidebreak
:::

::::full
A property like `p = ⟨p.fst, p.snd⟩` can be proved by exposing
the structure of the pair, either with `cases` or by destructuring in
`intro`.
::::

::::terse
To expose the structure of a pair, use `cases` (or destructuring).
::::

```lean
theorem surjective_pairing : ∀ p : NatProd,
    p = ⟨p.fst, p.snd⟩ := by
  intro ⟨n, m⟩; rfl

theorem surjective_pairing_cases (p : NatProd) :
    p = ⟨p.fst, p.snd⟩ := by
  cases p; rfl
```

::::full
Notice that, by contrast with the behavior of `cases` on
`Nat`s, where it generates two subgoals, `cases` generates just
one subgoal here.  That's because `NatProd`s can only be
constructed in one way.
::::

::::::full
:::::exercise (rating := 1) (name := "snd_fst_is_swap")
```lean
theorem snd_fst_is_swap (p : NatProd) :
    (⟨p.snd, p.fst⟩ : NatProd) = p.swap := by
  solution!
    cases p; rfl
```
:::::

:::::exercise (rating := 1) (name := "fst_swap_is_snd")
```lean
theorem fst_swap_is_snd (p : NatProd) :
    p.swap.fst = p.snd := by
  solution!
    cases p; rfl
```
:::::

::::::

# Lists of Numbers

::::full
Generalizing the definition of pairs, we can describe the
type of _lists_ of numbers like this: "A list is either the empty
list or else a pair of a number and another list."
::::

:::terse
An inductive definition of _lists_ of numbers:
:::

```lean
inductive NatList : Type where
  | nil
  | cons (n : Nat) (l : NatList)
```

By convention, we place the operations (functions) of an inductive type
inside the namespace implicitly created by that type's definition.

```lean
namespace NatList
```

:::slidebreak
:::

::::full
As with pairs, it is convenient to write lists in familiar
notation.  The following declarations allow us to use `::` as an
infix `cons` operator and square brackets as an "outfix" notation
for constructing lists.
::::

:::terse
Some notation for lists to make our lives easier:
:::

Don't worry too much about what this is doing:

:::dev "Benjamin Pierce (bcpierce00)"
Can we be a little more helpful, or tell them when we are going to tell them, or tell them where to look?
:::

```lean
scoped infixr:65 " :: " => cons
scoped macro (priority := high) "[ " elems:term,* "]" : term => do
  elems.getElems.foldrM (``(cons $(⟨·⟩) $(⟨·⟩))) (← ``(nil))
```

Now these all mean exactly the same thing:

```lean
def mylist1 : NatList := 1 :: (2 :: (3 :: []))
def mylist2 : NatList := 1 :: 2 :: 3 :: []
def mylist3 : NatList := [1, 2, 3]
```

:::terse
Some useful list-manipulation functions...
:::

## Repeat

::::full
First is the `myRepeat` function, which takes a number `n`
and a `count` and returns a list of length `count` in which every element is `n`.
(We use `myRepeat` because `repeat` is a reserved keyword in Lean.)
::::

```lean
def myRepeat (n count : Nat) : NatList :=
  match count with
  | 0 => []
  | count' + 1 => n :: myRepeat n count'
```

Some simple facts about repetition:

```lean
theorem repeat_zero v : myRepeat v 0 = [] := rfl

theorem repeat_succ v count : myRepeat v (count + 1) = v :: myRepeat v count := rfl
```

::::full
The `length` function calculates the length of a list.
::::

```lean
def length (l : NatList) : Nat :=
  match l with
  | [] => 0
  | _ :: t => (length t) + 1
```

Some simple facts about list lengths:

```lean
theorem length_nil : [].length = 0 := rfl

theorem length_cons (n : Nat) (l : NatList) : (n::l).length = l.length + 1 := rfl
```

## Append

::::full
The `app` function appends (concatenates) two lists.
::::

```lean
def app (l1 l2 : NatList) : NatList :=
  match l1 with
  | [] => l2
  | h :: t => h :: app t l2
```

## Type Classes and Overloading

:::dev "Benjamin Pierce (bcpierce00)"
One word, or two?
:::

::::full
In Lean, operators like `++`, `==`, and `+` are not
hardwired to particular types.  Instead, they are defined using
_type classes_ — a mechanism that lets us overload operations
for different types.

For example, `++` is defined via the `HAppend` type class.
Any type that provides an `HAppend` instance gets to use `++`.
Lean's built-in `List` already has such an instance (using
`List.append`), but since we've defined our own `app` function,
we can register it as the `++` operator within our namespace:
::::

```lean
instance : HAppend NatList NatList NatList where
  hAppend := app
```

Now `l1 ++ l2` means `app l1 l2` within `NatList`.

Some simple facts about appending lists:

```lean
theorem nil_append (l : NatList) : [] ++ l = l := rfl

theorem cons_append (n : Nat) (l1 l2 : NatList) : (n::l1) ++ l2 = n :: (l1 ++ l2) := rfl

example : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5] := by rfl
example : ([] : NatList) ++ [4, 5] = [4, 5] := by rfl
example : [1, 2, 3] ++ ([] : NatList) = [1, 2, 3] := by rfl
```

:::dev "One An (meluge)" NOW
Experiment: introduce `BEq.refl` here, at the point where the `BEq` class is named.
:::

:::slidebreak
:::

:::dev "Chris Henson (chenson2018)"
The way that this is written might mislead the student to think it is inherent to BEq, which is not true: this additionally requires the ReflBEq typeclass. How crucial is it to have this early mention of typeclasses? bcpierce00: Hopefully we can postpone it.
:::

::::full
The equality test `==` on `Nat`s is another example: it comes
from the `BEq` ("boolean equality") type class. One small but handy
fact about it, which several proofs below will need, is that `==` is
reflexive:

  `BEq.refl : (a == a) = true`

This is the standard library's version of the `beq_refl` theorem you
proved in {ref "Induction"}[Induction].
::::

::::terse
`==` comes from the `BEq` class;
`BEq.refl : (a == a) = true` is worth knowing by name.
::::

::::full
We'll learn more about type classes as we go.  For now, the
key idea is: a type class is an interface, and an instance is an
implementation of that interface for a particular type.

(For a thorough treatment of type classes, see Chapter 3 of
_Functional Programming in Lean_.)
::::

:::dev "Daniel Sainati (dsainati1)" NOW
Should we replace the above with a forward link to our typeclasses chapter,
once we have one?
:::

### Head and Tail

::::full
The `hd` function returns the first element (the "head") of
the list, while `tl` returns everything but the first element (the
"tail").  Since the empty list has no first element, we pass
a default value to be returned in that case.
::::

```lean
def hd (default : Nat) (l : NatList) : Nat :=
  match l with
  | [] => default
  | h :: _ => h
```

Basic theorems about how `hd` behaves:

```lean
theorem hd_cons h x (t : NatList) : (h :: t).hd x = h := by rfl

theorem hd_nil x : [].hd x = x := by rfl

def tl (l : NatList) : NatList :=
  match l with
  | [] => []
  | _ :: t => t
```

Basic theorems about how `tl` behaves:

```lean
theorem tl_cons h (t : NatList) : (h :: t).tl = t := by rfl

theorem tl_nil : [].tl = [] := by rfl

example : hd 0 [1, 2, 3] = 1 := by rw [hd_cons]
example : hd 0 [] = 0 := by rw [hd_nil]
example : [1, 2, 3].tl = [2, 3] := by rw [tl_cons]
```

::::quiz
What does the following function do?

```lean
def foo (n : Nat) : NatList :=
  match n with
  | 0 => []
  | n' + 1 => (n' + 1) :: foo n'
```
::::

### Exercises

::::::full
:::::exercise (rating := 2) (name := "list_funs")
Complete the definitions of `nonzeros`, `oddmembers`, and
`countoddmembers` below. Have a look at the tests to understand
what these functions should do.

```lean
def nonzeros (l : NatList) : NatList := solution!(
  match l with
  | [] => []
  | h :: t =>
      match h with
      | 0 => nonzeros t
      | _ + 1 => h :: (nonzeros t))

example : nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3] := solution!(by rfl)
```

:::gradeTheorem "0.5" "NatList.test_nonzeros"
:::

The following lemmas should hold about your definition

```lean
theorem nonzeros_cons_zero (t : NatList) :
  nonzeros (0 :: t) = nonzeros t := solution!(by rfl)
theorem nonzeros_nil :
  nonzeros [] = [] := solution!(by rfl)
theorem nonzeros_cons_nonzero h (t : NatList) :
  nonzeros ((h + 1) :: t) = (h + 1) :: nonzeros t := solution!(by rfl)

def oddmembers (l : NatList) : NatList := solution!(
  match l with
  | [] => []
  | h :: t => bif h.odd then h :: oddmembers t else oddmembers t)

theorem oddmembers_nil : oddmembers [] = [] := solution!(by rfl)

theorem oddmembers_cons (h : Nat) (t : NatList) :
    oddmembers (h :: t) = bif odd h then h :: oddmembers t else oddmembers t := solution!(by rfl)

theorem oddmembers_cons_odd (x : Nat) (l : NatList) (h : odd x = true) :
    oddmembers (x :: l) = x :: oddmembers l := by
  solution!
    rw [oddmembers_cons, h, cond_true]

theorem oddmembers_cons_not_odd (x : Nat) (l : NatList) (h : odd x = false) :
    oddmembers (x :: l) = oddmembers l := by
  solution!
    rw [oddmembers_cons, h, cond_false]

example : oddmembers [1, 2] = [1] := by
  rw [oddmembers_cons_odd _ _ rfl]
  rw [oddmembers_cons_not_odd _ _ rfl]
  rw [oddmembers_nil]

theorem test_oddmembers : oddmembers [0, 1, 2, 3, 0] = [1, 3] := by
  solution!
    rw [oddmembers_cons_not_odd _ _ rfl]
    rw [oddmembers_cons_odd _ _ rfl]
    rw [oddmembers_cons_not_odd _ _ rfl]
    rw [oddmembers_cons_odd _ _ rfl]
    rw [oddmembers_cons_not_odd _ _ rfl]
    rw [oddmembers_nil]
```

:::gradeTheorem "0.5" "NatList.test_oddmembers"
:::

For the next problem, `countoddmembers`, we encourage you to implement it using
already-defined functions, rather than recursion.

```lean
def countoddmembers (l : NatList) : Nat := solution!(
  (oddmembers l).length)

theorem countoddmembers_def (l : NatList) : countoddmembers l = (oddmembers l).length := solution!(by rfl)

example : countoddmembers [0, 1, 2, 3, 0] = 2 := by
  rw [countoddmembers_def]
  rw [test_oddmembers]
  rw [length_cons, length_cons, length_nil]

example : countoddmembers [0, 2, 4] = 0 := by
  solution!
    rw [countoddmembers_def]
    rw [oddmembers_cons_not_odd _ _ rfl]
    rw [oddmembers_cons_not_odd _ _ rfl]
    rw [oddmembers_cons_not_odd _ _ rfl]
    rw [oddmembers_nil]
    rw [length_nil]

example : countoddmembers [] = 0 := by
  solution!
    rw [countoddmembers_def, oddmembers_nil, length_nil]
```

:::gradeTheorem "0.5" "NatList.test_countoddmembers2"
:::

:::gradeTheorem "0.5" "NatList.test_countoddmembers3"
:::
:::::

:::::exercise (rating := 3) (name := "alternate") (level := Advanced)
Complete the following definition of `alternate`, which
interleaves two lists into one, alternating between elements taken
from the first list and elements from the second.

Hint: there are natural ways of writing `alternate` that fail to
satisfy Lean's requirement that all recursive definitions be
_structurally recursive_, as mentioned in {ref "Basics"}[Basics].
If you encounter this difficulty,
consider pattern matching against both lists at the same time.
```lean
def alternate (l1 l2 : NatList) : NatList := solution!(
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2)

example : alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6] := solution!(by rfl)
```

:::gradeTheorem 1 "NatList.test_alternate1"
:::

```lean
example : alternate [1] [4, 5, 6] = [1, 4, 5, 6] := solution!(by rfl)
```

:::gradeTheorem 1 "NatList.test_alternate2"
:::

```lean
example : alternate [1, 2, 3] [4] = [1, 4, 2, 3] := solution!(by rfl)
example : alternate ([] : NatList) [20, 30] = [20, 30] := solution!(by rfl)
```

:::gradeTheorem 1 "NatList.test_alternate4"
:::
:::::

::::::

## Bags via Lists

::::full
A `bag` (or `multiset`) is like a set, except that each element
can appear multiple times rather than just once.  One way of
representing a bag of numbers is as a list.  The following definition
introduces a new type, `Bag`, as an abbreviation for `NatList`.

We define `Bag` as it's own new definition, so it needs an "API" so that we can work with it.
Even though it's equal to `NatList`, tactics that operate solely on syntax, like `rw` and `dsimp`, can't see this fact.
Therefore, we need to avoid using `[]` and `::` in `Bag`'s API.
::::


```lean
def Bag := NatList

namespace Bag
```

::::full
We define an "empty bag" and "adding an element to a bag" separately, and express the API using these definitions instead of `[]` and `::`.
The implementation body of the definitions can freely mix these up because, ideally, they are unfolded only in the proofs of their characterizing lemmas.

When working with a new definition encapsulating an inductive type, it's convenient to declare its constructors with a `@[match_pattern]` attribute.
The attribute lets us use the name of the constructor in match arms.
For example, we define the empty bag with the attribute so that the `match` expression in `is_empty` can be written as
```
match s with
| empty => true
| _ => false
```
instead of
```
match s with
| [] => true
| _ => false
```
although the latter style also works.
::::

```lean
@[match_pattern]
def empty : Bag := []

theorem empty_def : empty = [] := rfl

def is_empty (s : Bag) : Bool :=
  match s with
  | empty => true
  | _ => false
```

:::dev "Niklas Halonen (xhalo32)" PotentialImprovement
Do we want to define an induction principle for `Bag` so that it (hopefully) doesn't expose the constructors of `NatList`?
:::

::::::full
:::::exercise (rating := 3) (name := "bag_functions")
Complete the following definitions for the functions `add`, `count`,
`sum`, and `member` and prove the lemmas and examples about them.

```lean
@[match_pattern]
def add (v : Nat) (s : Bag) : Bag := solution!(v :: s)

theorem add_def (v : Nat) (s : Bag) : s.add v = v :: s := solution!(by rfl)

def count (v : Nat) (s : Bag) : Nat := solution!(
  match s with
  | empty => 0
  | add h t => bif v == h then (count v t) + 1 else count v t)
```

These lemmas should hold about your definition.

```lean
theorem count_empty (x : Nat) : count x empty = 0 := solution!(by rfl)

theorem count_add_def (v h : Nat) (s : Bag) :
    count v (add h s) = bif v == h then (count v s) + 1 else count v s := solution!(by rfl)

theorem count_add_same (v₁ v₂ : Nat) (s : Bag) (h : (v₁ == v₂) = true) :
    count v₁ (add v₂ s) = count v₁ s + 1 := by
  solution!
    rw [count_add_def, h, cond_true]

theorem count_add_diff (v₁ v₂ : Nat) (s : Bag) (h : (v₁ == v₂) = false) :
    count v₁ (add v₂ s) = count v₁ s := by
  solution!
    rw [count_add_def, h, cond_false]

example : count 1 (add 1 empty) = 1 := by
  rw [count_add_same _ _ _ rfl]
  rw [count_empty]

example : count 2 ([2, 2]) = 2 := by
  rw [← add_def, count_add_same _ _ _ rfl]
  rw [← add_def, count_add_same _ _ _ rfl]
  rw [← empty_def, count_empty]

example : count 1 (add 1 [1, 4]) = 2 := by
  solution!
    rw [count_add_same _ _ _ rfl]
    rw [← add_def, count_add_same _ _ _ rfl]
    rw [← add_def, count_add_diff _ _ _ rfl]
    rewrite [← empty_def, count_empty]
    rfl

example : count 5 (add 1 [1, 4]) = 0 := by
  solution!
    rw [count_add_diff _ _ _ rfl]
    rw [← add_def, count_add_diff _ _ _ rfl]
    rw [← add_def, count_add_diff _ _ _ rfl]
    rewrite [← empty_def, count_empty]
    rfl
```

:::gradeTheorem "0.5" "Bag.test_count1"
:::

:::gradeTheorem "0.5" "Bag.test_count2"
:::

All these proofs can be completed with `rfl`.

```lean
example : count 1 [1, 2, 3, 1, 4, 1] = 3 := solution!(by rfl)
example : count 6 [1, 2, 3, 1, 4, 1] = 0 := solution!(by rfl)
```

:::gradeTheorem "0.5" "NatList.test_count2"
:::

Multiset `sum` is similar to set `union`: `sum a b` contains all
the elements of `a` and those of `b`.  (Mathematicians usually
define `union` on multisets a little bit differently -- using max
instead of sum -- which is why we don't call this operation
`union`.)

We've deliberately given you a header that does not give explicit
names to the arguments.  Implement `sum` in terms of an
already-defined function, without changing the header.

```lean
def sum : Bag → Bag → Bag := solution!(app)

example : count 1 (sum [1, 2, 3] [1, 4, 1]) = 3 := solution!(by rfl)
```

:::gradeTheorem "0.5" "NatList.test_sum1"
:::

```lean
theorem sum_empty (s : Bag) : sum empty s = s := solution!(rfl)

theorem sum_add (n : Nat) (s₁ s₂ : Bag) : sum (add n s₁) s₂ = add n (sum s₁ s₂) := solution!(rfl)
```

```lean
def member (v : Nat) (s : Bag) : Bool := solution!(
  match s with
  | empty => false
  | add h t => bif v == h then true else member v t)

theorem member_empty (v : Nat) : member v empty = false := solution!(by rfl)

theorem member_add_def (v h : Nat) (t : Bag) :
  member v (add h t) = bif v == h then true else member v t := solution!(by rfl)

theorem member_add_same (v₁ v₂ : Nat) (t : Bag) (h : (v₁ == v₂) = true) :
    member v₁ (add v₂ t) = true := by
  solution!
    rw [member_add_def, h, cond_true]

theorem member_add_diff (v₁ v₂ : Nat) (t : Bag) (h : (v₁ == v₂) = false) :
    member v₁ (add v₂ t) = member v₁ t := by
  solution!
    rw [member_add_def, h, cond_false]

example : member 1 [1] = true := by
  rw [← add_def, member_add_same _ _ _ rfl]

example : member 2 [1] = false := by
  rw [← add_def, member_add_diff _ _ _ rfl]
  apply member_empty

example : member 1 [1, 4, 1] = true := by
  solution!
    rw [← add_def, member_add_same _ _ _ rfl]
```

:::gradeTheorem "0.5" "NatList.test_member1"
:::

```lean
example : member 2 [1, 4, 1] = false := by
  solution!
    rw [← add_def, member_add_diff _ _ _ rfl]
    rw [← add_def, member_add_diff _ _ _ rfl]
    rw [← add_def, member_add_diff _ _ _ rfl]
    apply member_empty
```

:::gradeTheorem "0.5" "NatList.test_member2"
:::
:::::

:::::exercise (rating := 3) (name := "bag_more_functions")
Here are some more `bag` functions for you to practice with.

When `removeOne` is applied to a bag without the number to
remove, it should return the same bag unchanged.  (This exercise
is optional, but students following the advanced track will need
to fill in the definition of `removeOne` for a later
exercise.)

:::dev BeforeNextRelease
BCP 25: At Penn this year, we removed the distinction
between standard and advanced tracks, which made the wording above
confusing. Maybe just make this an exercise for everybody?
:::

```lean
def removeOne (v : Nat) (s : Bag) : Bag := solution!(
  match s with
  | empty => empty
  | add h t => bif v == h then t else add h (removeOne v t))

theorem removeOne_empty (v : Nat) : removeOne v empty = empty := solution!(by rfl)

theorem removeOne_add_def (v h : Nat) (t : Bag) :
  removeOne v (add h t) = bif v == h then t else add h (removeOne v t) := solution!(by rfl)

theorem removeOne_add_same (v₁ v₂ : Nat) (t : Bag) (h : (v₁ == v₂) = true) :
    removeOne v₁ (add v₂ t) = t := by
  solution!
    rw [removeOne_add_def, h, cond_true]

theorem removeOne_add_diff (v₁ v₂ : Nat) (t : Bag) (h : (v₁ == v₂) = false) :
    removeOne v₁ (add v₂ t) = add v₂ (removeOne v₁ t) := by
  solution!
    rw [removeOne_add_def, h, cond_false]
```

```lean
example : count 5 (removeOne 5 [1, 5, 4]) = 0 := by
  rw [← add_def, removeOne_add_diff _ _ _ rfl]
  rw [← add_def, removeOne_add_same _ _ _ rfl]
  rw [count_add_diff _ _ _ rfl]
  rw [← add_def, count_add_diff _ _ _ rfl]
  rw [← empty_def, count_empty]

example : count 4 (removeOne 5 [4, 5, 1, 4]) = 2 := by
  solution!
    rw [← add_def, removeOne_add_diff _ _ _ rfl]
    rw [← add_def, removeOne_add_same _ _ _ rfl]
    rw [count_add_same _ _ _ rfl]
    rw [← add_def, count_add_diff _ _ _ rfl]
    rw [← add_def, count_add_same _ _ _ rfl]
    rw [← empty_def, count_empty]
```

:::gradeTheorem "0.5" "NatList.test_removeOne3"
:::

```lean
example : count 5 (removeOne 5 [1, 5, 5, 4]) = 1 := by
  solution!
    rw [← add_def, removeOne_add_diff _ _ _ rfl]
    rw [← add_def, removeOne_add_same _ _ _ rfl]
    rw [count_add_diff _ _ _ rfl]
    rw [← add_def, count_add_same _ _ _ rfl]
    rw [← add_def, count_add_diff _ _ _ rfl]
    rw [← empty_def, count_empty]
```

:::gradeTheorem "0.5" "NatList.test_removeOne4"
:::


```lean
def removeAll (v : Nat) (s : Bag) : Bag := solution!(
  match s with
  | empty => empty
  | add h t => bif v == h then removeAll v t else add h (removeAll v t))

theorem removeAll_empty (v : Nat) : removeAll v empty = empty := solution!(by rfl)

theorem removeAll_add_def (v h : Nat) (t : Bag) :
  removeAll v (add h t) = bif v == h then removeAll v t else add h (removeAll v t) := solution!(by rfl)

theorem removeAll_add_same (v₁ v₂ : Nat) (t : Bag) (h : (v₁ == v₂) = true) :
    removeAll v₁ (add v₂ t) = removeAll v₁ t := by
  solution!
    rw [removeAll_add_def, h, cond_true]

theorem removeAll_add_diff (v₁ v₂ : Nat) (t : Bag) (h : (v₁ == v₂) = false) :
    removeAll v₁ (add v₂ t) = add v₂ (removeAll v₁ t) := by
  solution!
    rw [removeAll_add_def, h, cond_false]
```

```lean
example : count 5 (removeAll 5 [5, 5]) = 0 := by
  rw [← add_def, removeAll_add_same _ _ _ rfl]
  rw [← add_def, removeAll_add_same _ _ _ rfl]
  rw [← empty_def, removeAll_empty]
  apply count_empty

example : count 5 (removeAll 5 [5, 1]) = 0 := by
  rw [← add_def, removeAll_add_same _ _ _ rfl]
  rw [← add_def, removeAll_add_diff _ _ _ rfl]
  rw [← empty_def, removeAll_empty]
  rw [count_add_diff _ _ _ rfl]
  apply count_empty

example : count 4 (removeAll 5 [4, 5, 4]) = 2 := by
  solution!
    rw [← add_def, removeAll_add_diff _ _ _ rfl]
    rw [← add_def, removeAll_add_same _ _ _ rfl]
    rw [← add_def, removeAll_add_diff _ _ _ rfl]
    rw [← empty_def, removeAll_empty]
    rw [count_add_same _ _ _ rfl]
    rw [count_add_same _ _ _ rfl]
    rw [count_empty]
```

:::gradeTheorem "0.5" "NatList.test_removeAll3"
:::

```lean
example : count 5 (removeAll 5 [2, 5, 5, 5, 1]) = 0 := by
  solution!
    rw [← add_def, removeAll_add_diff _ _ _ rfl]
    rw [← add_def, removeAll_add_same _ _ _ rfl]
    rw [← add_def, removeAll_add_same _ _ _ rfl]
    rw [← add_def, removeAll_add_same _ _ _ rfl]
    rw [← add_def, removeAll_add_diff _ _ _ rfl]
    rw [← empty_def, removeAll_empty]
    rw [count_add_diff _ _ _ rfl]
    rw [count_add_diff _ _ _ rfl]
    rw [count_empty]
```

:::gradeTheorem "0.5" "NatList.test_removeAll4"
:::

```lean
def included (s₁ s₂ : Bag) : Bool := solution!(
  match s₁ with
  | empty => true
  | add h t => member h s₂ && included t (removeOne h s₂))
```

:::dev "Niklas Halonen (xhalo32)" BeforeNextRelease
Do we need to introduce Bool.true_and, Bool.false_and and maybe their mirror versions?
:::

```lean
theorem included_empty (s₂ : Bag) : included empty s₂ = true := solution!(by rfl)

theorem included_add_def (h : Nat) (t s₂ : Bag) :
    included (add h t) s₂ = (member h s₂ && included t (removeOne h s₂)) := solution!(by rfl)

theorem included_add_member (v : Nat) (s₁ s₂ : Bag) (h : member v s₂ = true) :
    included (add v s₁) s₂ = included s₁ (removeOne v s₂) := by
  solution!
    rw [included_add_def, h, Bool.true_and]

theorem included_add_nonmember (v : Nat) (s₁ s₂ : Bag) (h : member v s₂ = false) :
    included (add v s₁) s₂ = false := by
  solution!
    rw [included_add_def, h, Bool.false_and]
```

```lean
example : included [1] [2, 1] = true := by
  rw [← add_def, ← add_def, ← empty_def]
  rw [included_add_member]
  · apply included_empty
  · rw [member_add_diff _ _ _ rfl]
    rw [member_add_same _ _ _ rfl]
```

```lean
example : included [1, 2] [2, 1, 4, 1] = true := by
  solution!
    rw [← add_def, ← add_def, ← add_def, ← add_def, ← add_def, ← add_def, ← empty_def]
    rw [included_add_member]
    · rw [included_add_member]
      · apply included_empty
      · rw [removeOne_add_diff _ _ _ rfl]
        rw [member_add_same _ _ _ rfl]
    · rw [member_add_diff _ _ _ rfl]
      rw [member_add_same _ _ _ rfl]
```

:::gradeTheorem "0.5" "NatList.test_included1"
:::

```lean
example : included [1, 2, 2] [2, 1, 4, 1] = false := by
  solution!
    rw [← add_def, ← add_def, ← add_def, ← add_def, ← add_def, ← add_def, ← add_def, ← empty_def]
    rw [included_add_member]
    · rw [included_add_member]
      · rw [included_add_nonmember]
        rw [removeOne_add_diff _ _ _ rfl]
        rw [removeOne_add_same _ _ _ rfl]
        rw [removeOne_add_same _ _ _ rfl]
        rw [member_add_diff _ _ _ rfl]
        rw [member_add_diff _ _ _ rfl]
        rw [member_empty]
      · rw [removeOne_add_diff _ _ _ rfl]
        rw [member_add_same _ _ _ rfl]
    · rw [member_add_diff _ _ _ rfl]
      rw [member_add_same _ _ _ rfl]
```

:::gradeTheorem "0.5" "NatList.test_included2"
:::
:::::

:::::exercise (rating := 2) (name := "add_inc_count") (manual := true)
Adding a value to a bag should increase the value's count by one.
State this as a theorem and prove it.

```lean
-- SOLUTION
theorem add_inc_count (s : Bag) (v : Nat) :
    count v (add v s) = (count v s) + 1 := by
  rw [count_add_same]
  exact BEq.refl v
-- END SOLUTION
```

:::grade
`GRADE_MANUAL 2: add_inc_count`
:::
:::::

::::::

```lean
end Bag
```

# Reasoning About Lists

::::full
As with numbers, simple facts about list-processing
functions can sometimes be proved entirely by rewriting.
For example, just rewriting the left-hand side of the following equality using the theorem
`nil_append` is enough for this theorem...
::::

::::terse
As with numbers, some proofs about list functions need only
rewriting...
::::

```lean
theorem nil_app (l : NatList) : ([] : NatList) ++ l = l := by rw [nil_append]
```

::::full
...because the `[]` is substituted into the "scrutinee" (the
expression whose value is being "scrutinized" by the match) in the
definition of `app`, allowing the match itself to be simplified.

Also, as with numbers, it is sometimes helpful to perform case
analysis on the possible shapes -- empty or non-empty -- of an
unknown list.
::::

:::slidebreak
:::

:::terse
...and some need case analysis.
:::

```lean
theorem tl_length_pred (l : NatList) :
    l.length.pred = l.tl.length := by
  cases l with
  | nil       => rw [tl_nil, length_nil]; dsimp
  | cons n l' => rw [tl_cons, length_cons]; dsimp
```

::::full
Here, the `nil` case works because we've chosen to define
`tl [] = []`. Notice that the `cons` case introduces two names,
`n` and `l'`, corresponding to the fact that the `cons` constructor
for lists takes two arguments (the head and tail of the list it is
constructing).
::::

Usually, though, interesting theorems about lists require
induction for their proofs.  We'll see how to do this next.

::::full
(Micro-Sermon: As we get deeper into this material, simply
_reading_ proof scripts will not help you very much.  Rather, it
is important to step through the details of each one using Lean and
think about what each step achieves.  Otherwise it is more or less
guaranteed that the exercises will make no sense when you get to
them.  'Nuff said.)
::::

## Induction on Lists

::::full
Proofs by induction over datatypes like `NatList` are a
little less familiar than standard natural number induction, but
the idea is equally simple.  Each `inductive` declaration defines
a set of data values that can be built up using the declared
constructors. For example, a boolean can be either `true` or
`false`; a number can be either `0` or else `succ` applied to another
number; and a list can be either `[]` or else `::` applied to a
number and a list.  Moreover, applications of the declared
constructors to one another are the _only_ possible shapes that
elements of an inductively defined set can have.

This last fact directly gives rise to a way of reasoning about
inductively defined sets: a number is either `0` or else it is `succ`
applied to some _smaller_ number; a list is either `[]` or else
it is `::` applied to some number and some _smaller_ list;
etc.  Thus, if we have in mind some proposition `P` that mentions a
list `l` and we want to argue that `P` holds for _all_ lists, we
can reason as follows:

- First, show that `P` is true of `l` when `l` is `[]`.
- Then show that `P` is true of `l` when `l` is `n :: l'` for
  some number `n` and some smaller list `l'`, assuming that `P`
  is true for `l'`.

Since larger lists can always be broken down into smaller ones,
eventually reaching `[]`, these two arguments together establish
the truth of `P` for all lists `l`.

Here's a concrete example:
::::

::::terse
Lean generates an induction principle for every `inductive`
definition, including lists.  We can use the `induction` tactic on
lists to prove things like the associativity of list-append...
::::

```lean
theorem app_assoc (l1 l2 l3 : NatList) :
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  induction l1 with
  | nil =>
    rw [nil_append, nil_append]
  | cons n l1' ih =>
    rw [cons_append, cons_append, cons_append, ih]
```

:::slidebreak
:::

:::terse
For comparison, here is an informal proof of the same theorem.
:::

:::dev "Benjamin Pierce (bcpierce00)"
What's the best Lean markup for a displayed equation? The markup below is going to get squished into a paragraph with all the rest by default, but IMO it would look better as a separate display. Also: Are we going to consistently write Qed at the end of proofs? We should agree on a convention.
:::

_Theorem_: For all lists `l1`, `l2`, and `l3`,
    `(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)`.

_Proof_: By induction on `l1`.

- First, suppose `l1 = []`.  We must show

```display
([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),
```

  which follows directly from the definition of `app`.

- Next, suppose `l1 = n :: l1'`, with

```display
(l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)
```

(the induction hypothesis). We must show

```display
((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).
```

By the definition of `app`, this follows from

```display
n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),
```

which is immediate from the induction hypothesis.  _Qed_.

### Generalizing Statements

::::full
In some situations, it is necessary to generalize a
statement in order to prove it by induction.  Intuitively, the
reason is that a more general statement also yields a more general
(stronger) inductive hypothesis.
::::

::::terse
Sometimes statements need to be generalized to prove them
by induction:
::::

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (c n : Nat) :
    myRepeat n c ++ myRepeat n c = myRepeat n (c + c) := by
  induction c with
  | zero => rw [repeat_zero, nil_append]
  | succ c' ih =>
    rw [repeat_succ]
    -- Now we seem to be stuck.  The IH only works for c' + c',
    -- but we need c' + 1 + (c' + 1).
    sorry
```

::::full
To get a more general inductive hypothesis, we can generalize:
::::

:::terse
A generalization that gives a stronger inductive hypothesis:
:::

```lean
theorem myRepeat_plus (c1 c2 n : Nat) :
    myRepeat n c1 ++ myRepeat n c2 = myRepeat n (c1 + c2) := by
  induction c1 with
  | zero =>
    rw [repeat_zero, Nat.zero_add, nil_append]
  | succ c1' ih =>
    rw [Nat.succ_add, repeat_succ, repeat_succ, cons_append, ih]
```

### Reversing a List

::::full
For a slightly more involved example of inductive proof over
lists, suppose we use `app` to define a list-reversing function
 `rev`:
::::

:::terse
A more interesting example of induction over lists:
:::

```lean
def rev (l : NatList) : NatList :=
  match l with
  | [] => []
  | h :: t => t.rev ++ [h]

theorem rev_nil : [].rev = [] := by rfl

theorem rev_cons h (t : NatList) : (h :: t).rev = t.rev ++ [h] := by rfl

example : [1, 2, 3].rev = [3, 2, 1] := by rfl

example : ([] : NatList).rev = [] := by rfl
```

::::full
For something a bit more challenging, let's prove that
reversing a list does not change its length.  Our first attempt
gets stuck in the successor case...
::::

:::slidebreak
:::

:::terse
Let's try to prove `length (rev l) = length l`.
:::

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (l : NatList) :
    l.rev.length = l.length := by
  induction l with
  | nil => rw [rev_nil]
  | cons n l' ih =>
    rw [rev_cons]
    -- Now we seem to be stuck: the goal involves `++`,
    -- but we don't have any useful equations
    -- in either the immediate context or in the global
    -- environment!
    sorry
```

::::full
A first attempt to make progress would be to prove exactly
the statement that we are missing at this point.  But this attempt
will fail because the inductive hypothesis is not general enough.
::::

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (l : NatList) n :
    (l.rev ++ [n]).length = .succ l.rev.length := by
  induction l with
  | nil =>
    rw [rev_nil, nil_append, length_cons, length_nil]
  | cons n l' ih =>
    rw [rev_cons]
    -- ih not applicable
    sorry
```

::::full
It turns out that the above lemma is more specific than it
needs to be. We can strengthen the lemma to work not only on reversed
lists but on general lists.
::::

```lean
theorem app_length_succ (l : NatList) (n : Nat) :
    (l ++ [n]).length = l.length + 1 := by
  induction l with
  | nil => rw [nil_append, length_cons]
  | cons m l' ih =>
    rw [cons_append, length_cons, ih, length_cons]
```

:::slidebreak
:::

Now we can prove the main theorem.

```lean
theorem rev_length (l : NatList) :
    l.rev.length = l.length := by
  induction l with
  | nil => rw [rev_nil]
  | cons n l' ih =>
    rw [rev_cons, app_length_succ, ih, length_cons]
```

:::slidebreak
:::

::::full
We can also prove a more general form that gives the
length of any two appended lists.
::::

```lean
theorem app_length (l1 l2 : NatList) :
    (l1 ++ l2).length = l1.length + l2.length := by
  workinclass!
    induction l1 with
    | nil => rw [nil_append, length_nil, Nat.zero_add]
    | cons n l1' ih =>
      rw [cons_append, length_cons, ih, length_cons, Nat.succ_add]
```

:::::terse
::::quiz
To prove the following theorem, which tactics will we need besides
`intro`, `dsimp`, `rw`, and `rfl`?  (A) none,
(B) `cases`, (C) `induction` on `n`, (D) `induction` on `l`, or
(E) can't be done with the tactics we've seen.

```display
theorem foo1 : ∀ n : Nat, ∀ l : NatList,
  myRepeat n 0 = l → l.length = 0
```

:::quizSolution
```
theorem foo1 (n : Nat) (l : NatList) :
    myRepeat n 0 = l → l.length = 0 := by
  intro h
  rw [← h, repeat_zero, length_nil]
```
:::
::::

::::quiz
What about the next one?

```display
theorem foo2 :  ∀ n m : Nat,
  (myRepeat n m).length = m
```

Which tactics do we need besides `intro`, `dsimp`, `rw`, and
`rfl`?  (A) none, (B) `cases`, (C) `induction` on `n`,
(D) `induction` on `m`, or (E) can't be done with the tactics we've
seen.

:::quizSolution
```
theorem foo2 (n m : Nat) :
    (myRepeat n m).length = m := by
  induction m with
  | zero       => rw [repeat_zero, length_nil]
  | succ m' ih => rw [repeat_succ, length_cons, ih]
```
:::
::::

:::::

::::full
For comparison, here are informal proofs of these two theorems:

_Theorem_: For all lists `l1` and `l2`,
   `(l1 ++ l2).length = l1.length + l2.length`.

_Proof_: By induction on `l1`.

- First, suppose `l1 = []`.  We must show

```display
([] ++ l2).length = [].length + l2.length,
```

  which follows directly from the definitions of `length`,
  `++`, and `+`.

- Next, suppose `l1 = n::l1'`, with

```display
(l1' ++ l2).length = l1'.length + l2.length
```

We must show

```display
((n::l1') ++ l2).length = (n::l1').length + l2.length.
```

This follows directly from the definitions of `length` and `++`
together with the induction hypothesis.  _Qed_.

_Theorem_: For all lists `l`,  `l.rev.length = l.length`.

_Proof_: By induction on `l`.

  - First, suppose `l = []`.  We must show

```display
[].rev.length = [].length,
```

  which follows directly from the definitions of `length`
  and `rev`.

- Next, suppose `l = n::l'`, with

```display
l'.rev.length = l'.length
```

We must show

```display
(n :: l').rev.length = (n :: l').length.
```

By the definition of `rev`, this follows from

```display
(l'.rev ++ [n]).length = .succ (l'.length),
```

which, by the previous lemma, is the same as

```display
l'.rev.length + [n].length = .succ (l'.length).
```

This follows directly from the induction hypothesis and the
definition of `length`.  _Qed_.

The style of these proofs is rather longwinded and pedantic.
After reading a couple like this, we might find it easier to
follow proofs that give fewer details (which we can easily work
out in our own minds or on scratch paper if necessary) and just
highlight the non-obvious steps.  In this more compressed style,
the above proof might look like this:

_Theorem_: For all lists `l`, `l.rev.length = l.length`.

_Proof_: First observe, by a straightforward induction on `l`,
 that `(l ++ [n]).length = .succ l.length` for any `l`.  The main
 property then follows by another induction on `l`, using the
 observation together with the induction hypothesis in the case
 where `l = n'::l'`. _Qed_

Which style is preferable in a given situation depends on
the sophistication of the expected audience and how similar the
proof at hand is to ones that they will already be familiar with.
The more pedantic style is a good default for our present purposes
because we're trying to be ultra-clear about the details.
::::

## Search

::::full
We've seen that proofs can make use of other theorems we've
already proved, e.g., using `rw`.  But in order to refer to a
theorem, we need to know its name!

In Lean, the `exact?` tactic will search for a lemma that closes
the current goal.  The `#check` command shows the type of a named
theorem.  You can also use `example` with `exact?` to search for
lemmas matching a particular pattern.

Your IDE likely has its own search functionality too.  In VS Code
with the Lean 4 extension, you can use Ctrl+T to search for
definitions by name.
::::

## List Exercises, Part 1

::::::full
:::::exercise (rating := 3) (name := "list_exercises")
More practice with lists:

```lean
theorem app_nil_r (l : NatList) :
    l ++ ([] : NatList) = l := by
  solution!
    induction l with
    | nil => rw [nil_append]
    | cons n l' ih =>
      rw [cons_append, ih]
```

:::gradeTheorem "0.5" "NatList.app_nil_r"
:::

```lean
theorem rev_app_distr (l1 l2 : NatList) :
   (l1 ++ l2).rev = l2.rev ++ l1.rev := by
  solution!
    induction l1 with
    | nil => rw [nil_append, rev_nil, app_nil_r]
    | cons x l1' ih =>
      rw [cons_append, rev_cons, ih, rev_cons, app_assoc]
```

:::gradeTheorem "0.5" "NatList.rev_app_distr"
:::

An _involution_ is a function that is its own inverse. That is,
applying the function twice yields the original input.

```lean
theorem rev_involutive (l : NatList) :
    l.rev.rev = l := by
  solution!
    induction l with
    | nil => rw [rev_nil, rev_nil]
    | cons n l' ih =>
      rw [rev_cons, rev_app_distr, ih, rev_cons, rev_nil, nil_append, cons_append, nil_append]
```

:::gradeTheorem "0.5" "NatList.rev_involutive"
:::

There is a short solution to the next one.  If you find yourself
getting tangled up, step back and try to look for a simpler way.

```lean
theorem app_assoc4 (l1 l2 l3 l4 : NatList) :
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4 := by
  solution!
    rw [app_assoc, app_assoc]
```

:::gradeTheorem "0.5" "NatList.app_assoc4"
:::

An exercise about your implementation of `nonzeros`:

```lean
theorem nonzeros_app (l1 l2 : NatList) :
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2) := by
  solution!
    induction l1 with
    | nil => rw [nonzeros_nil, nil_app, nil_app]
    | cons n l1' ih =>
      cases n with
      | zero =>
        rw [nonzeros_cons_zero, ←ih, cons_append, nonzeros_cons_zero]
      | succ n' =>
        rw [cons_append, nonzeros_cons_nonzero, nonzeros_cons_nonzero, ih, cons_append]
```

:::gradeTheorem 1 "NatList.nonzeros_app"
:::
:::::

:::::exercise (rating := 2) (name := "eqblist")
:::gradeTheorem 2 "NatList.eqblist_refl"
:::

Fill in the definition of `eqblist`, which compares
lists of numbers for equality.  Prove that `eqblist l l`
yields `true` for every list `l`.

```lean
def eqblist (l1 l2 : NatList) : Bool := solution!(
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => (h1 == h2) && eqblist t1 t2
  | _, _ => false)

theorem eqblist_nil : eqblist [] [] = true := solution!(by rfl)

theorem eqblist_cons_same h t1 t2 : eqblist (h :: t1) (h :: t2) = eqblist t1 t2 := by
  solution!
    dsimp [eqblist]
    rw [BEq.refl, Bool.true_and]

theorem eqblist_cons_diff h1 h2 t1 t2 : (h1 == h2) = false → eqblist (h1 :: t1) (h2 :: t2) = false := by
  solution!
    intro h
    dsimp [eqblist]
    rw [h, Bool.false_and]

example : eqblist [] [] = true := solution!(by rfl)
example : eqblist [1, 2, 3] [1, 2, 3] = true := solution!(by rfl)
example : eqblist [1, 2, 3] [1, 2, 4] = false := solution!(by rfl)

theorem eqblist_refl (l : NatList) :
    eqblist l l = true := by
  solution!
    induction l with
    | nil => rw [eqblist_nil]
    | cons n l' ih =>
      rw [eqblist_cons_same]
      exact ih
```
:::::

::::::

## List Exercises, Part 2

```lean
open Bag
```

:::dev "Niklas Halonen (xhalo32)" PotentialImprovement
Using `rfl` in the following `count_member_nonzero` exercise feels like defeq abuse.
However, `Nat.ble` doesn't seem to have characterizing lemmas:
```
theorem _root_.Nat.ble_zero (m : Nat) : Nat.ble 0 m = true := rfl
theorem _root_.Nat.ble_succ_zero (m : Nat) : Nat.ble (m + 1) 0 = false := rfl
theorem _root_.Nat.ble_succ_succ (m n : Nat) (h : Nat.ble m n = true) : Nat.ble (m + 1) (n + 1) = true := h
theorem count_member_nonzero (s : Bag) :
    Nat.ble 1 (count 1 (add 1 s)) = true := by
  solution!
    rw [count_add_same _ _ _ rfl]
    rw [Nat.ble_succ_succ]
    rw [Nat.ble_zero]
theorem ble_n_Sn (n : Nat) :
    Nat.ble n (n + 1) = true := by
  induction n with
  | zero       =>
    exact Nat.ble_zero _
  | succ n' ih =>
    rw [Nat.ble_succ_succ]
    exact ih
```
:::

::::::full
Here are a couple of little theorems to prove about your
definitions about bags above.

:::::exercise (rating := 1) (name := "count_member_nonzero")
```lean
theorem count_member_nonzero (s : Bag) :
    Nat.ble 1 (count 1 (add 1 s)) = true := by
  solution!
    rw [count_add_same] <;> rfl
```
:::::

The following lemma about `Nat.ble` might help you in the next
exercise (it will also be useful in later chapters).

```lean
theorem ble_n_Sn (n : Nat) :
    Nat.ble n (n + 1) = true := by
  induction n with
  | zero       => rfl
  | succ n' ih => dsimp [Nat.ble]; exact ih
```

Before doing the next exercise, make sure you've filled in the
definition of `removeOne` above.
::::::

::::hide
```
/- LATER: CH: The following exercise is not so simple.  Also the
     shape of the theorem (with a magic constant `0`), and the fact that
     n needs to be destructed seem like big and ugly hacks. The
     hack-free theorem looks like this: -/
/- LATER: BCP 20: We'd need to find a way to get through the first
   lemma's proof without using features they don't know... -/
theorem count_removeOne v s :
    count v (removeOne v s) = (count v s).pred := by
  induction s with
  | nil =>
    rw [← empty_def, removeOne_empty, count_empty]
    rfl
  | cons n l ih =>
  -- XXX they don't know about generalizing or casing on expressions yet !!!
    cases h : v == n with
    | false =>
      rw [← add_def, removeOne_add_diff _ _ _ h, count_add_diff _ _ _ h, ih, count_add_diff _ _ _ h]
    | true =>
      -- they don't yet have tools for this case
      rw [← add_def, removeOne_add_same _ _ _ h, count_add_same _ _ _ h]
      rw [Nat.pred_succ]

theorem ble_pred_n_n n :
    Nat.ble n.pred n = true := by
  induction n with
  | zero => dsimp [Nat.ble]
  | succ n ih =>
    rw [Nat.pred_succ]
    rw [ble_n_Sn]

theorem remove_does_not_increase_count' (s : Bag) (n : Nat) :
    Nat.ble (count n (removeOne n s)) (count n s) = true := by
  induction s with
  | nil =>
    rw [← empty_def, removeOne_empty, count_empty]
    rfl
  | cons n' l ih =>
    rw [count_removeOne, ble_pred_n_n]
```
::::

::::::full
:::::exercise (rating := 3) (name := "remove_does_not_increase_count") (level := Advanced)
```lean
theorem remove_does_not_increase_count (s : Bag) :
    Nat.ble (count 0 (removeOne 0 s)) (count 0 s) = true := by
  solution!
    induction s with
    | nil =>
      rw [← empty_def, removeOne_empty, count_empty]
      rfl
    | cons n s' ih =>
      rw [← add_def]
      cases n with
      | zero =>
        rw [removeOne_add_same _ _ _ rfl, count_add_same _ _ _ rfl, ble_n_Sn]
      | succ n' =>
        rw [removeOne_add_diff _ _ _ rfl, count_add_diff _ _ _ rfl, count_add_diff _ _ _ rfl]
        exact ih
```
:::::

:::::exercise (rating := 3) (name := "bag_count_sum") (manual := true)
Write down an interesting theorem `bag_count_sum` about bags
involving the functions `count` and `sum`, and prove it.
(You may find that the difficulty of the proof depends on how you defined `count`!

:::dev "Andrew Tolmach (AndrewTolmach)" PotentialImprovement
This is the obvious theorem, and everyone came up with
it.  But how hard it is to prove (in terms of Rocq mechanics)
depends critically on how the student defined `count` -- the
solution for which has not been given at this point, and is not so
obvious. BCP 9/16: For the moment, I've just added an explicit
warning to this effect - not sure whether we can do better. (Is
there a hint we could give about how count should have been
defined, to make this easier?  There's no problem giving a hint
here, since they'll already have solved the count exercise once
before getting to this point.) MRC 1/19: The proof uses `cases`
on a term that is not merely an identifier. That usage has not
been introduced yet. APT 21: Added a hint about that. MRC 2/22:
Even if the exercise is optional, it ought to be solvable with
with the material introduced thus far. It is not. I note that BCP
has rejected the proof in the exercise above for `count_removeOne`
because it uses `cases` on a term rather than identifier.
:::

:::dev "Niklas Halonen (xhalo32)" PotentialImprovement
`cases`, `induction`, `if` and `match` all support naming.
One can write `match hv : (v == h) with` instead of `cases hv : (v == h) with`, or even
```
if hv : (v == h) then
  rw [count_add_same _ _ _ hv, count_add_same _ _ _ hv, Nat.succ_add, ← ih]
else
  rw [Bool.not_eq_true] at hv
  rw [count_add_diff _ _ _ hv, count_add_diff _ _ _ hv]
  exact ih
```
in the following exercise.

More information in the reference: <https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=pattern-matching>
:::

```lean
-- SOLUTION
theorem bag_count_sum (s₁ s₂ : Bag) (v : Nat) :
    count v (sum s₁ s₂) = (count v s₁) + (count v s₂) := by
  induction s₁ with
  | nil =>
    rw [← empty_def, sum_empty, count_empty, Nat.zero_add]
  | cons h s1' ih =>
    rw [← add_def, sum_add]
    cases hv : (v == h) with
    | false =>
      rw [count_add_diff _ _ _ hv, count_add_diff _ _ _ hv]
      exact ih
    | true =>
      rw [count_add_same _ _ _ hv, count_add_same _ _ _ hv, Nat.succ_add, ← ih]
-- END SOLUTION
```
:::::

:::::exercise (rating := 3) (name := "involution_injective") (level := Advanced)
Prove that every involution is injective.

Involutions were defined above in `rev_involutive`. An _injective_
function is one-to-one: it maps distinct inputs to distinct
outputs, without any collisions.

```lean
theorem involution_injective (f : Nat → Nat) :
    (∀ n : Nat, n = f (f n)) →
    (∀ n1 n2 : Nat, f n1 = f n2 → n1 = n2) := by
  solution!
    intro hinv n1 n2 heq
    rw [hinv n1, hinv n2, heq]
```
:::::

:::::exercise (rating := 2) (name := "rev_injective") (level := Advanced)
Prove that `rev` is injective. Do not prove this by induction --
that would be hard. Instead, re-use the same proof technique that
you used for `involution_injective`. (But: Don't try to use that
exercise directly as a lemma: the types are not the same!)

```lean
theorem rev_injective (l1 l2 : NatList) :
  l1.rev = l2.rev → l1 = l2 := by
  solution!
    intro heq
    rw [← rev_involutive l1, ← rev_involutive l2, heq]
```
:::::

::::::

# Options

::::full
Suppose we want to write a function that returns the `n`th
element of some list.  If we give it type `NatList → Nat → Nat`,
then we'll have to choose some number to return when the list is
too short...
::::

:::terse
Suppose we'd like a function to retrieve the `n`th element
    of a list.  What to do if the list is too short?
:::

```lean
def nth_bad (l : NatList) (n : Nat) : Nat :=
  match l with
  | [] => 42
  | a :: l' => match n with
    | 0 => a
    | n' + 1 => nth_bad l' n'
```

:::slidebreak
:::

::::full
This solution is not so good: If `nth_bad` returns 42, we
don't know whether that value actually appears in the input or
whether we gave bad arguments.  A better alternative is to change
the return type to include an error value as a possible outcome.
We call this new type `NatOption`.
::::

:::terse
The solution: return a `NatOption`.
:::

```lean
inductive NatOption : Type where
  | some (n : Nat)
  | none
```

::::full
We can then change the above definition of `nth_bad` to
return `none` when the list is too short and `some a` when the
list has enough members and `a` appears at position `n`. We call
this new function `nth_error` to indicate that it may result in an
error.
::::

```lean
def nth_error (l : NatList) (n : Nat) : NatOption :=
  match l with
  | [] => .none
  | a :: l' => match n with
    | 0 => .some a
    | n' + 1 => nth_error l' n'

example : nth_error [4, 5, 6, 7] 0 = .some 4 := by rfl
example : nth_error [4, 5, 6, 7] 3 = .some 7 := by rfl
example : nth_error [4, 5, 6, 7] 9 = .none := by rfl
```

::::full
The function below pulls the `Nat` out of a `NatOption`,
returning a supplied default in the `none` case.
::::

```lean
def option_elim (d : Nat) (o : NatOption) : Nat :=
  match o with
  | .some n => n
  | .none => d

theorem option_elim_none d : option_elim d .none = d := by rfl

theorem option_elim_some d1 d2 : option_elim d1 (.some d2) = d2 := by rfl
```

::::::full
:::::exercise (rating := 2) (name := "hd_error")
Using the same idea, fix the `hd` function from earlier so we
don't have to pass a default element for the `nil` case.

```lean
def hd_error (l : NatList) : NatOption := solution!(
  match l with
  | [] => .none
  | h :: _ => .some h)

example : hd_error ([] : NatList) = .none := solution!(by rfl)
example : hd_error [1] = .some 1 := solution!(by rfl)
example : hd_error [5, 6] = .some 5 := solution!(by rfl)
```

:::gradeTheorem 1 "test_hd_error1"
:::

:::gradeTheorem 1 "test_hd_error2"
:::
:::::

```lean
theorem hd_error_nil : hd_error [] = .none := solution!(by rfl)

theorem hd_error_cons h t : hd_error (h :: t) = .some h := solution!(by rfl)
```

:::::exercise (rating := 1) (name := "option_elim_hd")
:::gradeTheorem 1 "NatList.option_elim_hd"
:::

This exercise relates your new `hd_error` to the old `hd`.

```lean
theorem option_elim_hd (l : NatList) (default : Nat) :
    hd default l = option_elim default (hd_error l) := by
  solution!
    cases l with
    | nil => rw [hd_error_nil, option_elim_none, hd_nil]
    | cons n l' =>
      rw [hd_cons, hd_error_cons, option_elim_some]
```
:::::

::::::

```lean
end NatList
```

::::hide
```
/- SOONER: NDS
   We would like to properly introduce the fact that multiple induction
   hypotheses may be available. We will be experimenting with introducing
   it in \CHAP{IndProp}, but if it turns out to be unsatisfactory, we may want
   to reconsider introducing this concept here. -/
/- Demonstrates the fact that, when a type has multiple
    sub-components (children?"smaller instances"?recursive instances?),
    then one gets one induction hypothesis per component, and that these
    get introduced right after said component (instead of all at the end). -/

inductive BinTree where
| leaf (n: Nat)
| fork (l: BinTree) (r: BinTree)

def mirror(t: BinTree): BinTree :=
  match t with
  | .leaf v => .leaf v
  | .fork l r => .fork (mirror r) (mirror l)

theorem mirror_involutive : ∀ t, t = mirror (mirror t) := by
  intro t
  induction t with
  | leaf => dsimp [mirror]
  | fork l r ihl ihr =>
    dsimp [mirror]
    rw [←ihl, ←ihr]

def size (t: BinTree): Nat :=
  match t with
  | .leaf _ => 1
  | .fork l r => 1 + size l + size r

theorem mirror_size t : size t = size (mirror t) := by
  induction t with
  | leaf => dsimp [size, mirror]
  | fork l r ihl ihr =>
    dsimp [size, mirror]
    rw [←ihl, ←ihr]
    have h: size l + size r = size r + size l := by
      rw [Nat.add_comm]
    rw [Nat.add_assoc, Nat.add_assoc, h]
```
::::

# Partial Maps

As a final illustration of how data structures can be defined in
Lean, here is a simple _partial map_ data type, analogous to the
map or dictionary data structures found in most programming
languages.

First, we define a new type `MyId` to serve as the "keys" of our
partial maps.

```lean
structure MyId where
  val : Nat
```

Internally, a `MyId` is just a number.  Introducing a separate type
by wrapping each `Nat` makes definitions more readable and gives us
flexibility to change representations later if we want to.

:::slidebreak
:::

We'll also need an equality test for `MyId`s:

```lean
def eqb_id (x1 x2 : MyId) : Bool :=
  x1.val == x2.val
```

:::::exercise (rating := 1) (name := "eqb_id_refl")
:::gradeTheorem 1 "eqb_id_refl"
:::

```lean
theorem eqb_id_refl (x : MyId) : eqb_id x x = true := by
  solution!
    dsimp [eqb_id]
    rw [BEq.refl]
```
:::::

:::slidebreak
:::

Now we define the type of partial maps:

```lean
inductive PartialMap : Type where
  | empty : PartialMap
  | record (i : MyId) (v : Nat) (m : PartialMap) : PartialMap
```

::::full
This declaration can be read: "There are two ways to construct a
`PartialMap`: either using the constructor `empty` to represent an
empty partial map, or applying the constructor `record` to
a key, a value, and an existing `PartialMap` to construct a
`PartialMap` with an additional key-to-value mapping."
::::

```lean
namespace PartialMap
```

:::slidebreak
:::

The `update` function overrides the entry for a given key in a
partial map by shadowing it with a new one (or simply adds a new
entry if the given key is not already present).

```lean
def update (d : PartialMap) (x : MyId) (value : Nat) : PartialMap :=
  record x value d
```

::::full
Last, the `find` function searches a `PartialMap` for a given
key.  It returns `none` if the key was not found and `some val` if
the key was associated with `val`. If the same key is mapped to
multiple values, `find` will return the first one it encounters.
::::

:::slidebreak
:::

:::terse
We can define functions on `PartialMap`s by pattern matching.
:::

```lean
def find (x : MyId) (d : PartialMap) : Option Nat :=
  match d with
  | empty => none
  | record y v d' =>
    bif eqb_id x y then some v
    else find x d'
```

::::quiz
Is the following claim true or false?

```lean
theorem quiz1 (d : PartialMap) (x : MyId) (v : Nat) :
    find x (update d x v) = some v := by
  dsimp [update, find]
  rw [eqb_id_refl]
  dsimp
```

(A) True
(B) False
(C) Not sure
::::

::::quiz
Is the following claim true or false?

```lean
theorem quiz2  (d : PartialMap) (x y : MyId) (o : Nat) :
    eqb_id x y = false →
    find x (update d y o) = find x d := by
  intro h
  dsimp [update, find]
  rw [h]
  dsimp
```

(A) True
(B) False
(C) Not sure
::::

::::::full
:::::exercise (rating := 1) (name := "update_eq")
:::gradeTheorem 1 "PartialMap.update_eq"
:::

```lean
theorem update_eq (d : PartialMap) (x : MyId) (v : Nat) :
    find x (update d x v) = some v := by
  solution!
    dsimp [update, find]
    rw [eqb_id_refl]
    dsimp
```
:::::

:::::exercise (rating := 1) (name := "update_neq")
:::gradeTheorem 1 "PartialMap.update_neq"
:::

```lean
theorem update_neq (d : PartialMap) (x y : MyId) (o : Nat) :
    eqb_id x y = false → find x (update d y o) = find x d := by
  solution!
    intro h
    dsimp [update, find]
    rw [h]
    dsimp
```
:::::

::::::

```lean
end PartialMap
```

::::hide
```
-- EX2M? (baz_num_elts)
/- HIDE: I'm not sure the material covered up to here suffices to
  understand that Inductive types must have finite elements and avoid
  the trap of coming up with infinite lists.  HIDE: MRC'20: I have to
  agree with the comments regarding this exercise.  It's unmotivated
  and feels like a trap.  Is there a concept we're trying to get
  across here that's necessary?  I'm proposing the exercise be
  optional.  BCP '20: Looks like someone made it optional. :-) But
  should we just drop it?  IY '20: I agree with the above comments,
  but I sort of appreciate this exercise. It gives a good
  introduction to the concept that some types may not be
  inhabited. Could we just add a hint that Inductive types must have
  finite elements?  BCP 20: That would kind of give away the answer,
  no?  I think leaving it in but leaving it optional is the best
  compromise. MRC 2/22: I don't think the exercise "introduces" the
  concept that types may be uninhabited. Instead it *demands* the
  student invent that notion on their own, which is non-obvious to
  your average OCaml (say) programmer. Also, at this point in the
  file it is a complete non-sequitur. And it has nothing to do with
  lists or other standard data types, as the rest of the file. KK:
  Also this exercise comes out of the blue without any
  motivation/introduction.  BCP 23: OK, I am removing it. -/

-- Consider the following inductive definition:

inductive Baz where
  | baz1 (x : Baz)
  | baz2 (y : Baz) (b : Bool)

/- How _many_ elements does the type `Baz` have? (Explain in words,
   in a comment.) -/

-- SOLUTION
/- None!  In order to create an element of type `Baz`, we would need
      to use one of the two constructors `baz1` and `baz2`; but both of
      these require a `Baz` as an argument.  So this definition cannot
      get off the ground: in order to create a `Baz` we would need to
      already have one. -/
-- /SOLUTION
-- LATER: Rework this exercise for easier grading?

/- LATER: KK: I am not sure whether this point should be made through a
  "manual" exercise like the one below. The students who don't know
  (or notice) that an Inductive definition needs a base case will
  just fail this exercise and will only see the reason in the grader
  comment. It is very easy for a student to falsely think that they
  have the right answer here and just move on without thinking about
  it. I think that it would be better to either add a small section
  that clearly explains this concept, or maybe add a hint similar to
  the one below: -/

/- Hint: Try to write a value of type `Baz` for which the following
     lemma `one_true_baz` holds. -/

def count_trues (x : Baz) : Nat :=
  match x with
  | .baz1 x' => count_trues x'
  | .baz2 x' true => 1 + count_trues x'
  | .baz2 x' _ => count_trues x'

-- theorem one_true_baz : count_trues (your baz here) = 1. --

-- []
```
::::

```lean
end Lists
```
