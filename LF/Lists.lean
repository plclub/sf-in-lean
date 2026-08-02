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
def NatProd.fst' (p : NatProd) : Nat :=
  match p with
  | ⟨x, _⟩ => x

def NatProd.snd' (p : NatProd) : Nat :=
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

```lean +error (name := bad_fst)
-- Can't match on a pair with multiple patterns:
def bad_fst (p : NatProd) : Nat :=
  match p with
  | x, y => x
```

```leanOutput bad_fst
Too many patterns in match alternative: Expected 1, but found 2:
  x, y
```

```lean +error (name := bad_sub)
-- Can't match on multiple values with pair patterns:
def bad_sub (n m : Nat) : Nat :=
  match n, m with
  | ⟨0,        _⟩        => 0
  | ⟨.succ _,  0⟩        => n
  | ⟨.succ n', .succ m'⟩ => sub n' m'
```

```leanOutput bad_sub
Invalid `⟨...⟩` notation: The expected type `Nat` has more than one constructor

Note: This notation can only be used when the expected type is an inductive type with a single constructor
```

::::

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
the structure of the pair, either with {tactic}`cases` or by destructuring in
{tactic}`intro`.
::::

::::terse
To expose the structure of a pair, use {tactic}`cases` (or destructuring).
::::

:::dev "Yipeng Liu (berberman)" PotentialImprovement
Use better examples to show structure destruction.
`surjective_pairing` and `surjective_pairing_cases` can be closed by `rfl`
without destruction because Lean supports projection eta for structures.
:::

```lean
theorem surjective_pairing : ∀ p : NatProd,
    p = ⟨p.fst, p.snd⟩ := by
  intro ⟨n, m⟩; rfl

theorem surjective_pairing_cases (p : NatProd) :
    p = ⟨p.fst, p.snd⟩ := by
  cases p; rfl
```

::::full
Notice that, by contrast with the behavior of {tactic}`cases` on
{name}`Nat`s, where it generates two subgoals, {tactic}`cases` generates just
one subgoal here.  That's because {name}`NatProd`s can only be
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

```lean
scoped infixr:65 " :: " => cons
scoped macro (priority := high) "[" elems:term,* "]" : term => do
  elems.getElems.foldrM (``(cons $(⟨·⟩) $(⟨·⟩))) (← ``(nil))

@[scoped app_unexpander nil]
def unexpandNil : Lean.PrettyPrinter.Unexpander
  | `($_) => `([])

@[scoped app_unexpander cons]
def unexpandCons : Lean.PrettyPrinter.Unexpander
  | `($_ $x []) => `([$x])
  | `($_ $x [$xs,*]) => `([$x, $xs,*])
  | _ => throw ()
```

We first define `::` as right-associative _notation_ for {name}`cons`,
and then define list notation _macro_ with _unexpander_,
allowing us to write `[1, 2]` instead of `1 :: 2 :: []`.

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
theorem repeat_zero {v : Nat} : myRepeat v 0 = [] := rfl

theorem repeat_succ {v count : Nat} : myRepeat v (count + 1) = v :: myRepeat v count := rfl
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

theorem length_cons {n : Nat} {l : NatList} : (n :: l).length = l.length + 1 := rfl
```

## Append

::::full
The `append` function appends (concatenates) two lists.
::::

```lean
def append (l1 l2 : NatList) : NatList :=
  match l1 with
  | [] => l2
  | h :: t => h :: append t l2
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
Any type that provides an {name}`HAppend` instance gets to use `++`.
Lean's built-in `List` already has such an instance (using
{name}`List.append`), but since we've defined our own {name}`append` function,
we can register it as the `++` operator within our namespace:
::::

```lean
instance : HAppend NatList NatList NatList where
  hAppend := append
```

Now `l1 ++ l2` means `append l1 l2` within `NatList`.

Some simple facts about appending lists:

```lean
theorem nil_append (l : NatList) : [] ++ l = l := rfl

theorem cons_append {n : Nat} {l1 l2 : NatList} : (n :: l1) ++ l2 = n :: (l1 ++ l2) := rfl

example : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5] := by rfl
example : [] ++ [4, 5] = [4, 5] := by rfl
example : [1, 2, 3] ++ [] = [1, 2, 3] := by rfl
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
The `head` function returns the first element (the "head") of
the list, while `tail` returns everything but the first element (the
"tail").  Since the empty list has no first element, we pass
a default value to be returned in that case.
::::

```lean
def head (default : Nat) (l : NatList) : Nat :=
  match l with
  | [] => default
  | h :: _ => h
```

Basic theorems about how {name}`head` behaves:

```lean
theorem head_cons {h x : Nat} {t : NatList} : (h :: t).head x = h := by rfl

theorem head_nil {x : Nat} : [].head x = x := by rfl

def tail (l : NatList) : NatList :=
  match l with
  | [] => []
  | _ :: t => t
```

Basic theorems about how {name}`tail` behaves:

```lean
theorem tail_cons {h : Nat} {t : NatList} : (h :: t).tail = t := by rfl

theorem tail_nil : [].tail = [] := by rfl

example : head 0 [1, 2, 3] = 1 := by rw [head_cons]
example : head 0 [] = 0 := by rw [head_nil]
example : [1, 2, 3].tail = [2, 3] := by rw [tail_cons]
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

:::instructors
Each exercise comes with non-graded examples followed by graded tests.
We show how to rewrite with the lemmas explicitly in the first example and the fact that one can just use {tactic}`rfl` in the second (this is only visible in the solution because it would not type-check otherwise).
The point of the graded tests is nearly always to be an {tactic}`rfl` proof that relies on a correctly formulated definition.
The characterizing lemmas are provided (as statements) but not graded.
The student is expected to also use {tactic}`rfl` as it's the easiest, and most idiomatic solution.
:::

::::::full
:::::exercise (rating := 2) (name := "list_funs")
Complete the definitions of `nonZeros`, `oddMembers`, and
`countOddMembers` below. Have a look at the lemmas and examples to understand
what these functions should do.

```lean
def nonZeros (l : NatList) : NatList := solution!(
  match l with
  | [] => []
  | 0 :: t => nonZeros t
  | h :: t => h :: nonZeros t
)
```

The following lemmas should hold about your definition

```lean
theorem nonZeros_cons_zero {t : NatList} :
    nonZeros (0 :: t) = nonZeros t := solution!(by rfl)

theorem nonZeros_nil :
    nonZeros [] = [] := solution!(by rfl)

theorem nonZeros_cons_nonZero {h : Nat} {t : NatList} :
    nonZeros ((h + 1) :: t) = (h + 1) :: nonZeros t := solution!(by rfl)

theorem test_nonZeros : nonZeros [0, 1, 0] = [1] := by
  solution!
    rw [nonZeros_cons_zero]
    rw [nonZeros_cons_nonZero]
    rw [nonZeros_cons_zero]
    rw [nonZeros_nil]
```

:::gradeTheorem "0.5" test_nonZeros
:::

```lean
def oddMembers (l : NatList) : NatList := solution!(
  match l with
  | [] => []
  | h :: t => bif h.odd then h :: oddMembers t else oddMembers t)

theorem oddMembers_nil :
    oddMembers [] = [] := solution!(by rfl)

theorem oddMembers_cons {h : Nat} {t : NatList} :
    oddMembers (h :: t) =
      bif h.odd then h :: oddMembers t else oddMembers t :=
  solution!(by rfl)

theorem oddMembers_cons_odd {x : Nat} {l : NatList}
    (h : x.odd = true) :
    oddMembers (x :: l) = x :: oddMembers l := by
  solution!
    rw [oddMembers_cons, h, cond_true]

theorem oddMembers_cons_not_odd {x : Nat} {l : NatList}
    (h : x.odd = false) :
    oddMembers (x :: l) = oddMembers l := by
  solution!
    rw [oddMembers_cons, h, cond_false]
```

Now, we can prove that {lean}`oddMembers [1, 2]` returns {lean}`[1]` using the lemmas:

```lean
example : oddMembers [1, 2] = [1] := by
  rw [oddMembers_cons_odd]
  · rw [oddMembers_cons_not_odd]
    · rw [oddMembers_nil]
    · rw [Nat.odd_def]
      rw [even_succ, even_succ, even_zero, Bool.not_true, Bool.not_false, Bool.not_true]
  · rw [Nat.odd, even_succ, even_zero, Bool.not_true, Bool.not_false]
```

This gets pretty verbose quite fast, however we can use {tactic}`rfl` to deal with subgoals such as {lean}`Nat.odd 2 = false`:

```lean
example : oddMembers [1, 2] = [1] := by
  rw [oddMembers_cons_odd]
  · rw [oddMembers_cons_not_odd]
    · rw [oddMembers_nil]
    · rfl
  · rfl
```

In fact, as the entire proof is just plain computation, it can be done with a single `rfl`.
This is possible because all of the elements and lists are concrete -- there are no variables involved.

```lean
example : oddMembers [1, 2] = [1] := solution!(by rfl)

theorem test_oddMembers : oddMembers [0, 1, 2, 3, 0] = [1, 3] := solution!(by rfl)
```

:::gradeTheorem "0.5" test_oddMembers
:::

For the next problem, `countOddMembers`, we encourage you to implement it using
already-defined functions, rather than recursion.

```lean
def countOddMembers (l : NatList) : Nat := solution!(
  (oddMembers l).length)

theorem countOddMembers_def (l : NatList) :
    countOddMembers l = (oddMembers l).length := solution!(by rfl)

example : countOddMembers [0, 1, 2, 3, 0] = 2 := by
  rw [countOddMembers_def]
  rw [test_oddMembers]
  rw [length_cons, length_cons, length_nil]

example : countOddMembers [0, 1, 2, 3, 0] = 2 := solution!(by rfl)

theorem test_countOddMembers1 : countOddMembers [0, 2, 4] = 0 := solution!(by rfl)

theorem test_countOddMembers2 : countOddMembers [] = 0 := solution!(by rfl)
```

:::gradeTheorem "0.5" test_countOddMembers1 test_countOddMembers2
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

theorem test_alternate1 :
    alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6] := solution!(by rfl)
```

:::gradeTheorem 1 test_alternate1
:::

```lean
theorem test_alternate2 :
    alternate [1] [4, 5, 6] = [1, 4, 5, 6] := solution!(by rfl)
```

:::gradeTheorem 1 test_alternate2
:::

```lean
theorem test_alternate3 :
    alternate [1, 2, 3] [4] = [1, 4, 2, 3] := solution!(by rfl)

theorem test_alternate4 :
    alternate [] [20, 30] = [20, 30] := solution!(by rfl)
```

:::gradeTheorem 1 test_alternate4
:::
:::::

::::::

## Counting

:::::exercise (rating := 1) (name := "counting")
Define a `count` function for {name}`NatList`s that counts the number of times an element `v` appears in the list.

```lean
def count (v : Nat) (l : NatList) : Nat := solution!(
  match l with
  | [] => 0
  | h :: t => bif v == h then (count v t) + 1 else count v t)
```

Now, prove these lemmas which should hold about your definition.

```lean
theorem count_nil {x : Nat} : count x [] = 0 := solution!(by rfl)

theorem count_cons_def {v h : Nat} {t : NatList} :
    count v (h :: t) = bif v == h then (count v t) + 1 else count v t := solution!(by rfl)

theorem count_cons_same {v₁ v₂ : Nat} {t : NatList} (h : (v₁ == v₂) = true) :
    count v₁ (v₂ :: t) = count v₁ t + 1 := by
  solution!
    rw [count_cons_def, h, cond_true]

theorem count_cons_diff {v₁ v₂ : Nat} {t : NatList} (h : (v₁ == v₂) = false) :
    count v₁ (v₂ :: t) = count v₁ t := by
  solution!
    rw [count_cons_def, h, cond_false]

example : count 1 [1] = 1 := by
  rw [count_cons_same rfl]
  rw [count_nil]

example : count 2 [2, 2] = 2 := solution!(by rfl)

theorem test_count1 : count 1 [1, 1, 4] = 2 := solution!(by rfl)

theorem test_count2 : count 5 [1, 1, 4] = 0 := solution!(by rfl)
```

:::gradeTheorem "0.5" test_count1 test_count2
:::
:::::

Again, all these proofs could be completed with just `rfl`, because the proof is computationally straight-forward -- compute both sides of the equality and check if they are the same.

```lean
example : count 1 [1, 2, 3, 1, 4, 1] = 3 := solution!(by rfl)
example : count 6 [1, 2, 3, 1, 4, 1] = 0 := solution!(by rfl)
```

## Membership

:::::exercise (rating := 1) (name := "membership")

```lean
def member (v : Nat) (l : NatList) : Bool := solution!(
  match l with
  | [] => false
  | h :: t => bif v == h then true else member v t)

theorem member_nil {v : Nat} : member v [] = false := solution!(by rfl)

theorem member_cons_def {v h : Nat} {t : NatList} :
  member v (h :: t) = bif v == h then true else member v t := solution!(by rfl)

theorem member_cons_same {v₁ v₂ : Nat} {t : NatList} (h : (v₁ == v₂) = true) :
    member v₁ (v₂ :: t) = true := by
  solution!
    rw [member_cons_def, h, cond_true]

theorem member_cons_diff {v₁ v₂ : Nat} {t : NatList} (h : (v₁ == v₂) = false) :
    member v₁ (v₂ :: t) = member v₁ t := by
  solution!
    rw [member_cons_def, h, cond_false]

example : member 1 [1] = true := by
  rw [member_cons_same rfl]

example : member 2 [1] = false := solution!(by rfl) -- rfl

theorem test_member1 : member 1 [1, 4, 1] = true := solution!(by rfl)
```

:::gradeTheorem "0.5" test_member1
:::

```lean
theorem test_member2 : member 2 [1, 4, 1] = false := solution!(by rfl)
```

:::gradeTheorem "0.5" test_member2
:::
:::::

## Removing

:::::exercise (rating := 3) (name := "removing")
Here are some more {name}`NatList` functions for you to practice with.

When `removeOne` is applied to a list without the number to
remove, it should return the same list unchanged.  (This exercise
is optional, but students following the advanced track will need
to fill in the definition of `removeOne` for a later
exercise.)

:::dev BeforeNextRelease
BCP 25: At Penn this year, we removed the distinction
between standard and advanced tracks, which made the wording above
confusing. Maybe just make this an exercise for everybody?
:::

```lean
def removeOne (v : Nat) (l : NatList) : NatList := solution!(
  match l with
  | [] => nil
  | h :: t => bif v == h then t else h :: removeOne v t)

theorem removeOne_nil {v : Nat} : removeOne v nil = nil := solution!(by rfl)

theorem removeOne_cons_def {v h : Nat} {t : NatList} :
  removeOne v (h :: t) = bif v == h then t else h :: removeOne v t := solution!(by rfl)

theorem removeOne_cons_same {v₁ v₂ : Nat} {t : NatList} (h : (v₁ == v₂) = true) :
    removeOne v₁ (v₂ :: t) = t := by
  solution!
    rw [removeOne_cons_def, h, cond_true]

theorem removeOne_cons_diff {v₁ v₂ : Nat} {t : NatList} (h : (v₁ == v₂) = false) :
    removeOne v₁ (v₂ :: t) = v₂ :: removeOne v₁ t := by
  solution!
    rw [removeOne_cons_def, h, cond_false]
```

```lean
example : removeOne 5 [1, 5, 4] = [1, 4] := by
  rw [removeOne_cons_diff rfl]
  rw [removeOne_cons_same rfl]

example : count 5 (removeOne 5 [1, 5, 4]) = 0 := solution!(by rfl)

theorem test_removeOne1 : count 4 (removeOne 5 [4, 5, 1, 4]) = 2 := solution!(by rfl)
```

:::gradeTheorem "0.5" test_removeOne1
:::

```lean
theorem test_removeOne2 : count 5 (removeOne 5 [1, 5, 5, 4]) = 1 := solution!(by rfl)
```

:::gradeTheorem "0.5" test_removeOne2
:::


```lean
def removeAll (v : Nat) (l : NatList) : NatList := solution!(
  match l with
  | [] => []
  | h :: t => bif v == h then removeAll v t else h :: removeAll v t)

theorem removeAll_nil {v : Nat} : removeAll v [] = [] := solution!(by rfl)

theorem removeAll_cons_def {v h : Nat} {t : NatList} :
  removeAll v (h :: t) = bif v == h then removeAll v t else h :: removeAll v t := solution!(by rfl)

theorem removeAll_cons_same {v₁ v₂ : Nat} {t : NatList} (h : (v₁ == v₂) = true) :
    removeAll v₁ (v₂ :: t) = removeAll v₁ t := by
  solution!
    rw [removeAll_cons_def, h, cond_true]

theorem removeAll_cons_diff {v₁ v₂ : Nat} {t : NatList} (h : (v₁ == v₂) = false) :
    removeAll v₁ (v₂ :: t) = v₂ :: removeAll v₁ t := by
  solution!
    rw [removeAll_cons_def, h, cond_false]
```

```lean
example : count 5 (removeAll 5 [5, 1]) = 0 := by
  rw [removeAll_cons_same rfl]
  rw [removeAll_cons_diff rfl]
  rw [removeAll_nil]
  rw [count_cons_diff rfl]
  rw [count_nil]

example : count 5 (removeAll 5 [5, 5]) = 0 := solution!(by rfl)

theorem test_removeAll1 : count 4 (removeAll 5 [4, 5, 4]) = 2 := solution!(by rfl)
```

:::gradeTheorem "0.5" test_removeAll1
:::

```lean
theorem test_removeAll2 : count 5 (removeAll 5 [2, 5, 5, 5, 1]) = 0 := solution!(by rfl)
```

:::gradeTheorem "0.5" test_removeAll2
:::

:::::

## Included

:::instructors
The following is also a valid definition because we don't provide `included_cons_def` in the student handout:
```lean
def included (l₁ l₂ : NatList) : Bool :=
  match l₁ with
  | [] => true
  | h :: t => if member h l₂ then included t (removeOne h l₂) else false
```
:::

:::::exercise (rating := 3) (name := "included")
```lean
def included (l₁ l₂ : NatList) : Bool := solution!(
  match l₁ with
  | [] => true
  | h :: t => member h l₂ && included t (removeOne h l₂))
```

:::dev "Niklas Halonen (xhalo32)" BeforeNextRelease
Do we need to introduce Bool.true_and, Bool.false_and and maybe their mirror versions? There's also {name}`NatPlayground.Nat.andb_false` from Induction.lean...
:::

```lean
theorem included_nil {l₂ : NatList} : included nil l₂ = true := solution!(by rfl)
```

:::solution
```lean
theorem included_cons_def {h : Nat} {t l₂ : NatList} :
    included (cons h t) l₂ = (member h l₂ && included t (removeOne h l₂)) := solution!(by rfl)
```
:::

```lean
theorem included_cons_member {v : Nat} {l₁ l₂ : NatList} (h : member v l₂ = true) :
    included (cons v l₁) l₂ = included l₁ (removeOne v l₂) := by
  solution!
    rw [included_cons_def, h, Bool.true_and]

theorem included_cons_nonmember {v : Nat} {l₁ l₂ : NatList} (h : member v l₂ = false) :
    included (cons v l₁) l₂ = false := by
  solution!
    rw [included_cons_def, h, Bool.false_and]
```

```lean
example : included [1] [2, 1] = true := by
  rw [included_cons_member]
  · apply included_nil
  · rw [member_cons_diff rfl]
    rw [member_cons_same rfl]

example : included [1, 1] [2, 1, 4, 1] = true := solution!(by rfl)
```

```lean
theorem test_included1 : included [1, 2] [2, 1, 4, 1] = true := solution!(by rfl)
```

:::gradeTheorem "0.5" test_included1
:::

```lean
theorem test_included2 : included [1, 2, 2] [2, 1, 4, 1] = false := solution!(by rfl)
```

:::gradeTheorem "0.5" test_included2
:::
:::::

:::dev "Niklas Halonen (xhalo32)" BeforeNextRelease
The next exercise is merely a special case of `count_cons_same`.
Is this on purpose?
:::

:::::exercise (rating := 2) (name := "count_cons_inc") (manual := true)
Adding a value to a list should increase the value's count by one.
State this as a theorem and prove it.

:::solution
```lean
theorem count_cons_inc (l : NatList) (v : Nat) :
    count v (v :: l) = (count v l) + 1 := by
  rw [count_cons_same]
  exact BEq.refl v
```
:::

:::grade
`GRADE_MANUAL 2: count_cons_inc`
:::
:::::

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

:::slidebreak
:::

:::terse
...and some need case analysis.
:::

```lean
theorem tail_length_pred (l : NatList) :
    l.length.pred = l.tail.length := by
  cases l with
  | nil       => rw [tail_nil, length_nil]; dsimp
  | cons n l' => rw [tail_cons, length_cons]; dsimp
```

::::full
Here, the {name}`nil` case works because we've chosen to define
{lean}`tail [] = []`. Notice that the {name}`cons` case introduces two names,
`n` and `l'`, corresponding to the fact that the {name}`cons` constructor
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
Proofs by induction over datatypes like {name}`NatList` are a
little less familiar than standard natural number induction, but
the idea is equally simple.  Each `inductive` declaration defines
a set of data values that can be built up using the declared
constructors. For example, a boolean can be either {name}`true` or
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
theorem append_assoc (l1 l2 l3 : NatList) :
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

```display
(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
```

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

```lean -keep +error (name := st)
theorem myRepeat_append {c n : Nat} :
    myRepeat n c ++ myRepeat n c = myRepeat n (c + c) := by
  induction c with
  | zero => rw [repeat_zero, nil_append]
  | succ c' ih =>
    rw [repeat_succ]
    -- Now we seem to be stuck.
    -- The `ih` only works for `c' + c'`,
    -- but we need `c' + 1 + (c' + 1)`.
```

```leanOutput st
unsolved goals
case succ
n c' : Nat
ih : myRepeat n c' ++ myRepeat n c' = myRepeat n (c' + c')
⊢ (n :: myRepeat n c') ++ (n :: myRepeat n c') = myRepeat n (c' + 1 + (c' + 1))
```

::::full
To get a more general inductive hypothesis, we can generalize:
::::

:::terse
A generalization that gives a stronger inductive hypothesis:
:::

```lean
theorem myRepeat_append {c₁ c₂ n : Nat} :
    myRepeat n c₁ ++ myRepeat n c₂ = myRepeat n (c₁ + c₂) := by
  induction c₁ with
  | zero =>
    rw [repeat_zero, Nat.zero_add, nil_append]
  | succ c1' ih =>
    rw [Nat.succ_add, repeat_succ, repeat_succ, cons_append, ih]
```

### Reversing a List

::::full
For a slightly more involved example of inductive proof over
lists, suppose we use `append` to define a list-reversing function `reverse`:
::::

:::terse
A more interesting example of induction over lists:
:::

```lean
def reverse (l : NatList) : NatList :=
  match l with
  | [] => []
  | h :: t => t.reverse ++ [h]

theorem reverse_nil : [].reverse = [] := by rfl

theorem reverse_cons {h : Nat} {t : NatList} : (h :: t).reverse = t.reverse ++ [h] := by rfl

example : [1, 2, 3].reverse = [3, 2, 1] := by rfl

example : [].reverse = [] := by rfl
```

::::full
For something a bit more challenging, let's prove that
reversing a list does not change its length.  Our first attempt
gets stuck in the successor case...
::::

:::slidebreak
:::

:::terse
Let's try to prove {lean}`∀ l : NatList, length (reverse l) = length l`.
:::

```lean +error (name := st2)
example (l : NatList) :
    l.reverse.length = l.length := by
  induction l with
  | nil => rw [reverse_nil]
  | cons n l' ih =>
    rw [reverse_cons]
    -- Now we seem to be stuck: the goal involves `++`,
    -- but we don't have any useful equations
    -- in either the immediate context or in the global
    -- environment!
```

```leanOutput st2
unsolved goals
case cons
n : Nat
l' : NatList
ih : l'.reverse.length = l'.length
⊢ (l'.reverse ++ [n]).length = (n :: l').length
```

::::full
A first attempt to make progress would be to prove exactly
the statement that we are missing at this point.  But this attempt
will fail because the inductive hypothesis is not general enough.
::::

```lean -keep +error (name := st3)
theorem length_append_succ {l : NatList} {n : Nat} :
    (l.reverse ++ [n]).length = l.reverse.length + 1 := by
  induction l with
  | nil =>
    rw [reverse_nil, nil_append, length_cons, length_nil]
  | cons n l' ih =>
    rw [reverse_cons]
    -- `ih` not applicable
```

```leanOutput st3
unsolved goals
case cons
n✝ n : Nat
l' : NatList
ih : (l'.reverse ++ [n✝]).length = l'.reverse.length + 1
⊢ (l'.reverse ++ [n] ++ [n✝]).length = (l'.reverse ++ [n]).length + 1
```

::::full
It turns out that the above lemma is more specific than it
needs to be. We can strengthen the lemma to work not only on reversed
lists but on general lists.
::::

```lean
theorem append_length_succ (l : NatList) (n : Nat) :
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
theorem length_reverse {l : NatList} :
    l.reverse.length = l.length := by
  induction l with
  | nil => rw [reverse_nil]
  | cons n l' ih =>
    rw [reverse_cons, append_length_succ, ih, length_cons]
```

:::slidebreak
:::

::::full
We can also prove a more general form that gives the
length of any two appended lists.
::::

```lean
theorem length_append {l₁ l₂ : NatList} :
    (l₁ ++ l₂).length = l₁.length + l₂.length := by
  workinclass!
    induction l₁ with
    | nil => rw [nil_append, length_nil, Nat.zero_add]
    | cons n l1' ih =>
      rw [cons_append, length_cons, ih, length_cons, Nat.succ_add]
```

:::::terse
::::quiz
To prove the following theorem, which tactics will we need besides
{tactic}`intro`, {tactic}`dsimp`, {tactic}`rw`, and {tactic}`rfl`?

(A) none

(B) {tactic}`cases`

(C) {tactic}`induction` on `n`

(D) {tactic}`induction` on `l`

(E) can't be done with the tactics we've seen.

```display
example (n : Nat) (l : NatList) :
    myRepeat n 0 = l → l.length = 0
```

:::quizSolution
```lean
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
example (n m : Nat) : (myRepeat n m).length = m
```

To prove the following theorem, which tactics will we need besides
{tactic}`intro`, {tactic}`dsimp`, {tactic}`rw`, and {tactic}`rfl`?

(A) none

(B) {tactic}`cases`

(C) {tactic}`induction` on `n`

(D) {tactic}`induction` on `m`

(E) can't be done with the tactics we've seen.


:::quizSolution
```lean
example (n m : Nat) : (myRepeat n m).length = m := by
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

```display
(l1 ++ l2).length = l1.length + l2.length.
```

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

_Theorem_: For all lists `l`,  `l.reverse.length = l.length`.

_Proof_: By induction on `l`.

  - First, suppose `l = []`.  We must show

```display
[].reverse.length = [].length,
```

  which follows directly from the definitions of `length`
  and `reverse`.

- Next, suppose `l = n::l'`, with

```display
l'.reverse.length = l'.length
```

We must show

```display
(n :: l').reverse.length = (n :: l').length.
```

By the definition of `reverse`, this follows from

```display
(l'.reverse ++ [n]).length = l'.length + 1,
```

which, by the previous lemma, is the same as

```display
l'.reverse.length + [n].length = l'.length + 1.
```

This follows directly from the induction hypothesis and the
definition of `length`.  _Qed_.

The style of these proofs is rather longwinded and pedantic.
After reading a couple like this, we might find it easier to
follow proofs that give fewer details (which we can easily work
out in our own minds or on scratch paper if necessary) and just
highlight the non-obvious steps.  In this more compressed style,
the above proof might look like this:

_Theorem_: For all lists `l`, `l.reverse.length = l.length`.

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
theorem append_nil {l : NatList} :
    l ++ [] = l := by
  solution!
    induction l with
    | nil => rw [nil_append]
    | cons n l' ih =>
      rw [cons_append, ih]
```

:::gradeTheorem "0.5" append_nil
:::

```lean
theorem reverse_append {l₁ l₂ : NatList} :
   (l₁ ++ l₂).reverse = l₂.reverse ++ l₁.reverse := by
  solution!
    induction l₁ with
    | nil => rw [nil_append, reverse_nil, append_nil]
    | cons x l1' ih =>
      rw [cons_append, reverse_cons, ih, reverse_cons, append_assoc]
```

:::gradeTheorem "0.5" reverse_append
:::

An _involution_ is a function that is its own inverse. That is,
applying the function twice yields the original input.

```lean
theorem reverse_reverse (l : NatList) :
    l.reverse.reverse = l := by
  solution!
    induction l with
    | nil => rw [reverse_nil, reverse_nil]
    | cons n l' ih =>
      rw [reverse_cons, reverse_append, ih]
      rw [reverse_cons, reverse, nil_append, cons_append, nil_append]
```

:::gradeTheorem "0.5" reverse_reverse
:::

There is a short solution to the next one.  If you find yourself
getting tangled up, step back and try to look for a simpler way.

```lean
theorem append_assoc4 {l1 l2 l3 l4 : NatList} :
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4 := by
  solution!
    rw [append_assoc, append_assoc]
```

:::gradeTheorem "0.5" append_assoc4
:::

An exercise about your implementation of {name}`nonZeros`:

```lean
theorem nonZeros_app (l1 l2 : NatList) :
    nonZeros (l1 ++ l2) = (nonZeros l1) ++ (nonZeros l2) := by
  solution!
    induction l1 with
    | nil => rw [nonZeros_nil, nil_append, nil_append]
    | cons n l1' ih =>
      cases n with
      | zero =>
        rw [nonZeros_cons_zero, ← ih, cons_append, nonZeros_cons_zero]
      | succ n' =>
        rw [cons_append, nonZeros_cons_nonZero, nonZeros_cons_nonZero, ih, cons_append]
```

:::gradeTheorem 1 nonZeros_app
:::
:::::

:::::exercise (rating := 2) (name := "beq")
Fill in the definition of `beq`, which compares
lists of numbers for equality.  Prove that `beq l l`
yields `true` for every list `l`.

```lean
def beq (l1 l2 : NatList) : Bool := solution!(
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => (h1 == h2) && beq t1 t2
  | _, _ => false)

theorem beq_nil : beq [] [] = true := solution!(by rfl)

theorem beq_cons_def {h1 h2 : Nat} {t1 t2 : NatList} : beq (h1 :: t1) (h2 :: t2) = ((h1 == h2) && beq t1 t2) := solution!(by rfl)

theorem beq_cons_same {h1 h2 : Nat} {t1 t2 : NatList} (h : (h1 == h2) = true) :
    beq (h1 :: t1) (h2 :: t2) = beq t1 t2 := by
  solution!
    rw [beq_cons_def, h, Bool.true_and]

theorem beq_cons_diff {h1 h2 : Nat} {t1 t2 : NatList} (h : (h1 == h2) = false) :
    beq (h1 :: t1) (h2 :: t2) = false := by
  solution!
    rw [beq_cons_def, h, Bool.false_and]

example : beq [] [] = true := solution!(by rfl)
example : beq [1, 2, 3] [1, 2, 3] = true := solution!(by rfl)
example : beq [1, 2, 3] [1, 2, 4] = false := by
  solution!
    rw [beq_cons_same rfl]
    rw [beq_cons_same rfl]
    rw [beq_cons_diff rfl]

theorem beq_refl {l : NatList} :
    beq l l = true := by
  solution!
    induction l with
    | nil => rw [beq_nil]
    | cons n l' ih =>
      rw [beq_cons_same BEq.rfl]
      exact ih
```

:::gradeTheorem 2 beq_refl
:::
:::::

::::::

## List Exercises, Part 2

```lean
open NatList
```

:::dev "Niklas Halonen (xhalo32)" PotentialImprovement
Using `rfl` to prove `Nat.ble 1 (count 1 l + 1) = true` in the following `count_member_nonZero` exercise feels like defeq abuse.
However, `Nat.ble` doesn't seem to have characterizing lemmas:
```
theorem _root_.Nat.ble_zero (m : Nat) : Nat.ble 0 m = true := rfl
theorem _root_.Nat.ble_succ_zero (m : Nat) : Nat.ble (m + 1) 0 = false := rfl
theorem _root_.Nat.ble_succ_succ (m n : Nat) (h : Nat.ble m n = true) : Nat.ble (m + 1) (n + 1) = true := h
theorem count_member_nonzero (l : NatList) :
    Nat.ble 1 (count 1 (1 :: l)) = true := by
  solution!
    rw [count_cons_same rfl]
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
definition above.

:::::exercise (rating := 1) (name := "count_member_nonZero")
```lean
theorem count_member_nonZero (l : NatList) :
    Nat.ble 1 (count 1 (1 :: l)) = true := by
  solution!
    rw [count_cons_same] <;> rfl
```
:::::

The following lemma about `Nat.ble` might help you in the next
exercise (it will also be useful in later chapters).

```lean
theorem ble_self_succ (n : Nat) :
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
theorem count_removeOne (v : Nat) (l : NatList) :
    count v (removeOne v l) = (count v l).pred := by
  induction l with
  | nil =>
    rw [removeOne_nil, count_nil]
    rfl
  | cons n l ih =>
  -- XXX they don't know about generalizing or casing on expressions yet !!!
    cases h : v == n with
    | false =>
      rw [removeOne_cons_diff h, count_cons_diff h, ih, count_cons_diff h]
    | true =>
      -- they don't yet have tools for this case
      rw [removeOne_cons_same h, count_cons_same h]
      rw [Nat.pred_succ]

theorem ble_pred_n_n (n : Nat) :
    Nat.ble n.pred n = true := by
  induction n with
  | zero => dsimp [Nat.ble]
  | succ n ih =>
    rw [Nat.pred_succ]
    rw [ble_n_Sn]

theorem remove_does_not_increase_count' (l : NatList) (n : Nat) :
    Nat.ble (count n (removeOne n l)) (count n l) = true := by
  induction l with
  | nil =>
    rw [removeOne_nil, count_nil]
    rfl
  | cons n' l ih =>
    rw [count_removeOne, ble_pred_n_n]
```
::::

::::::full
:::::exercise (rating := 3) (name := "remove_does_not_increase_count") (level := Advanced)
```lean
theorem remove_does_not_increase_count (l : NatList) :
    Nat.ble (count 0 (removeOne 0 l)) (count 0 l) = true := by
  solution!
    induction l with
    | nil =>
      rw [removeOne_nil, count_nil]
      rfl
    | cons n s' ih =>
      cases n with
      | zero =>
        rw [removeOne_cons_same rfl, count_cons_same rfl, ble_self_succ]
      | succ n' =>
        rw [removeOne_cons_diff rfl, count_cons_diff rfl, count_cons_diff rfl]
        exact ih
```
:::::

:::::exercise (rating := 3) (name := "count_app") (manual := true)
Write down an interesting theorem `count_app` about lists
involving the functions `count` and `app`, and prove it.
(You may find that the difficulty of the proof depends on how you defined `count`!)

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
  rw [count_cons_same hv, count_cons_same hv, Nat.succ_cons, ← ih]
else
  rw [Bool.not_eq_true] at hv
  rw [count_cons_diff hv, count_cons_diff hv]
  exact ih
```
in the following exercise.

More information in the reference: <https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=pattern-matching>
:::

:::solution
```lean
theorem count_append (l₁ l₂ : NatList) (v : Nat) :
    count v (l₁ ++ l₂) = (count v l₁) + (count v l₂) := by
  induction l₁ with
  | nil =>
    rw [nil_append, count_nil, Nat.zero_add]
  | cons h s1' ih =>
    rw [cons_append]
    cases hv : (v == h) with
    | false =>
      rw [count_cons_diff hv, count_cons_diff hv]
      exact ih
    | true =>
      rw [count_cons_same hv, count_cons_same hv, Nat.succ_add, ← ih]
```
:::
:::::

:::::exercise (rating := 3) (name := "involutive_injective") (level := Advanced)
Prove that every involution is injective.

Involutions were defined above in {name}`reverse_reverse`. An _injective_
function is one-to-one: it maps distinct inputs to distinct
outputs, without any collisions.

```lean
theorem involutive_injective (f : Nat → Nat) (hInv : ∀ n : Nat, n = f (f n)) :
    (∀ n₁ n₂ : Nat, f n₁ = f n₂ → n₁ = n₂) := by
  solution!
    intro n₁ n₂ h
    rw [hInv n₁, hInv n₂, h]
```
:::::

:::::exercise (rating := 2) (name := "reverse_injective") (level := Advanced)
Prove that {name}`reverse` is injective. Do not prove this by induction —
that would be hard. Instead, re-use the same proof technique that
you used for {name}`involutive_injective`. (But: Don't try to use that
exercise directly as a lemma: the types are not the same!)

```lean
theorem reverse_injective (l₁ l₂ : NatList)
    (h : l₁.reverse = l₂.reverse) : l₁ = l₂ := by
  solution!
    rw [← reverse_reverse l₁, ← reverse_reverse l₂, h]
```
:::::

::::::

# Options

::::full
Suppose we want to write a function that returns the `n`th
element of some list.  If we give it type {lean}`NatList → Nat → Nat`,
then we'll have to choose some number to return when the list is
too short...
::::

:::terse
Suppose we'd like a function to retrieve the `n`th element
    of a list.  What to do if the list is too short?
:::

```lean
def nthBad (l : NatList) (n : Nat) : Nat :=
  match l with
  | [] => 42
  | a :: l' => match n with
    | 0 => a
    | n' + 1 => nthBad l' n'
```

:::slidebreak
:::

::::full
This solution is not so good: If `nthBad` returns 42, we
don't know whether that value actually appears in the input or
whether we gave bad arguments.  A better alternative is to change
the return type to include an error value as a possible outcome.
We call this new type `NatOption`.
::::

:::terse
The solution: return a `NatOption`.
:::

```lean
end NatList
```

```lean
inductive NatOption : Type where
  | some (n : Nat)
  | none
```

```lean
namespace NatList
```

::::full
We can then change the above definition of {name}`nthBad` to
return `none` when the list is too short and `some a` when the
list has enough members and `a` appears at position `n`. We call
this new function `nth?` to indicate that it may result in an
error.
::::

```lean
def nth? (l : NatList) (n : Nat) : NatOption :=
  match l with
  | [] => .none
  | a :: l' => match n with
    | 0 => .some a
    | n' + 1 => nth? l' n'

example : nth? [4, 5, 6, 7] 0 = .some 4 := by rfl
example : nth? [4, 5, 6, 7] 3 = .some 7 := by rfl
example : nth? [4, 5, 6, 7] 9 = .none := by rfl
```

::::full
The function below pulls the {name}`Nat` out of a {name}`NatOption`,
returning a supplied default in the `none` case.
::::

```lean
def NatOption.elim (d : Nat) (o : NatOption) : Nat :=
  match o with
  | .some n => n
  | .none => d

theorem NatOption.elim_none {d : Nat} : elim d .none = d := by rfl

theorem NatOption.elim_some {d₁ d₂ : Nat} : elim d₁ (.some d₂) = d₂ := by rfl
```

::::::full
:::::exercise (rating := 2) (name := "head?")
Using the same idea, fix the {name}`head` function from earlier so we
don't have to pass a default element for the {name}`nil` case.

```lean
def head? (l : NatList) : NatOption := solution!(
  match l with
  | [] => .none
  | h :: _ => .some h)

example : head? [] = .none := solution!(by rfl)
theorem test_head?1 : head? [1] = .some 1 := solution!(by rfl)
theorem test_head?2 : head? [5, 6] = .some 5 := solution!(by rfl)
```

:::gradeTheorem 1 test_head?1 test_head?2
:::
:::::

```lean
theorem head?_nil : head? [] = .none := solution!(by rfl)

theorem head?_cons {h : Nat} {t : NatList} : head? (h :: t) = .some h := solution!(by rfl)
```

:::::exercise (rating := 1) (name := "option_elim_head?")
This exercise relates your new `head?` to the old `head`.

```lean
theorem option_elim_head? (l : NatList) (default : Nat) :
    head default l = NatOption.elim default (head? l) := by
  solution!
    cases l with
    | nil => rw [head?_nil, NatOption.elim_none, head_nil]
    | cons n l' =>
      rw [head_cons, head?_cons, NatOption.elim_some]
```

:::gradeTheorem 1 option_elim_head?
:::
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

Internally, a {name}`MyId` is just a number.  Introducing a separate type
by wrapping each {name}`Nat` makes definitions more readable and gives us
flexibility to change representations later if we want to.

:::slidebreak
:::

We'll also need an equality test for {name}`MyId`s:

```lean
def MyId.beq (x₁ x₂ : MyId) : Bool :=
  x₁.val == x₂.val
```

:::::exercise (rating := 1) (name := "MyId.beq_refl")
```lean
theorem MyId.beq_refl (x : MyId) : MyId.beq x x = true := by
  solution!
    dsimp [beq]
    rw [BEq.refl]
```

:::gradeTheorem 1 MyId.beq_refl
:::
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
Last, the `find` function searches a {name}`PartialMap` for a given
key.  It returns {name}`none` if the key was not found and `some val` if
the key was associated with `val`. If the same key is mapped to
multiple values, `find` will return the first one it encounters.
::::

:::slidebreak
:::

:::terse
We can define functions on `PartialMap`s by pattern matching.
:::

```lean
def find (x : MyId) (d : PartialMap) : NatOption :=
  match d with
  | empty => .none
  | record y v d' =>
    bif MyId.beq x y then .some v
    else find x d'
```

::::quiz
Is the following claim true or false?

```lean
theorem quiz1 (d : PartialMap) (x : MyId) (v : Nat) :
    find x (update d x v) = .some v := by
  dsimp [update, find]
  rw [MyId.beq_refl]
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
    MyId.beq x y = false →
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
```lean
theorem update_eq (d : PartialMap) (x : MyId) (v : Nat) :
    find x (update d x v) = .some v := by
  solution!
    dsimp [update, find]
    rw [MyId.beq_refl]
    dsimp
```

:::gradeTheorem 1 update_eq
:::
:::::

:::::exercise (rating := 1) (name := "update_neq")
```lean
theorem update_neq (d : PartialMap) (x y : MyId) (o : Nat) :
    MyId.beq x y = false → find x (update d y o) = find x d := by
  solution!
    intro h
    dsimp [update, find]
    rw [h]
    dsimp
```

:::gradeTheorem 1 update_neq
:::
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
