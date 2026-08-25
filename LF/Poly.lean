import SFLMeta

import LF.Induction
import LF.UsingLean

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Poly: Polymorphism and Higher-Order Functions" =>
%%%
tag := "Poly"
htmlSplit := .never
file := some "Poly"
%%%

:::ignore
```lean -show
variable (α β γ : Type) (x : α) (y : β)
```
:::

:::instructors
To get through this plus {ref "Tactics"}[Tactics] in two 80-minute
lectures is a bit tight — if that's your plan, don't dawdle on
this chapter.

(This comment may now be misaligned with the flow of lectures in CIS5000 at least, since we've
added significant new material before we get here.)
:::

```importBlock
import LF.Induction
import LF.UsingLean
```

# Polymorphism

::::full
In this chapter we continue our development of basic
concepts of functional programming. The critical new ideas are
_polymorphism_ (abstracting functions over the types of the data
they manipulate) and _higher-order functions_ (treating functions
as data). We begin with polymorphism.
::::

## Polymorphic Lists

::::full
In the last chapter, we worked with lists containing just
numbers. Obviously, interesting programs also need to be able to
manipulate lists with elements from other types — lists of
booleans, lists of lists, etc. We _could_ just define a new
inductive datatype for each of these, for example...
::::

::::terse
Instead of defining new lists for each type, like
this...
::::

```lean
inductive BoolList : Type where
  | nil
  | cons (b : Bool) (l : BoolList)
```

::::full
... but this would quickly become tedious: not only would we
have to make up different constructor names for each datatype, but —
even worse — we would also need to define new versions of all
the list manipulating functions (`length`, `++`, `reverse`,
etc.) and all their properties (`length_reverse`, `append_assoc`, etc.)
for each new definition.
::::

:::slidebreak
:::

::::full
To avoid this repetition, we can make the element type itself an
_argument_ to the definition. Lean calls such definitions
_polymorphic_. Here is a polymorphic list type:
::::

::::terse
... Lean lets us give a _polymorphic_ definition that allows
list elements of any type:
::::

```lean
inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons (x : α) (l : MyList α) : MyList α
```

::::full
This is exactly like the definition of `Natlist` from the
previous chapter, except that the {name}`Nat` argument to the `cons`
constructor has been replaced by an arbitrary type {lean}`α`, a type parameter
{lean}`α` has been added to the header on the first line,
and the occurrences of `Natlist` in the types of the constructors
have been replaced by {lean}`MyList α`. We can now write {lean}`MyList Nat`
instead of a dedicated nat-list type.

What sort of thing is {name}`MyList` itself?  A good way to think about it
is as a _type constructor_ — that is, a function from {lean}`Type`s to
{lean}`Type`s. For any particular type {lean}`α`,
the type {lean}`MyList α` is the inductively defined type of lists whose
elements are of type {lean}`α`.
::::

::::terse
We can now write {lean}`MyList Nat` in place of a specialized
list-of-numbers type.
::::

:::slidebreak
:::

::::terse
What is {name}`MyList` itself?

It is a _type constructor_ — a function from types to types.
::::

:::dev "Yipeng Liu (berberman)"
A trick used below: parenthesizing the declaration makes it a term —
Lean elaborates it and prints its inferred function type,
instead of the declaration signature: `MyList (α : Type) : Type`.
:::

```lean (name := MyList)
#check (MyList)
```

```leanOutput MyList
MyList : Type → Type
```

:::slidebreak
:::

::::full
The {lean}`α` in the definition of {name}`MyList` automatically becomes a
parameter to the constructors `nil` and `cons` — that is, `nil`
and `cons` are now polymorphic constructors. In Lean, the type
parameter is _implicit_ by default: Lean will infer it from context.
For example, {name}`MyList.nil` is the empty list, and Lean figures out
the element type from how it is used.
::::

::::terse
The {lean}`α` in the definition of {name}`MyList` becomes an implicit
parameter to the list constructors `nil` and `cons`.
::::

```lean (name := nil)
#check MyList.nil
```

```leanOutput nil
MyList.nil {α : Type} : MyList α
```

::::full
Similarly, {name}`MyList.cons` adds an element of type {name}`Nat` to a
list of type {lean}`MyList Nat`. Here is an example of forming a list
containing just the natural number {lean}`3`.
::::

```lean (name := cons3)
#check MyList.cons 3 MyList.nil
```

```leanOutput cons3
MyList.cons 3 MyList.nil : MyList Nat
```

::::full
What is the full type of {name}`MyList.nil`? We can read off the
result type {lean}`MyList α` from the definition,
but to state the full type we must also bind {lean}`α`.
Since the type argument to the constructor is implicit,
Lean writes its type as (the equivalent of) {lean}`{α : Type} → MyList α`.
::::

```lean (name := nil)
#check MyList.nil
```

```leanOutput nil
MyList.nil {α : Type} : MyList α
```

::::full
Similarly, the type of {name}`MyList.cons` includes the implicit
type parameter:
::::

```lean (name := cons)
#check MyList.cons
```

```leanOutput cons
MyList.cons {α : Type} (x : α) (l : MyList α) : MyList α
```

::::full
Having to supply a type argument for every single use of a
list constructor would be rather burdensome. Fortunately, the type
argument is implicit, so Lean will normally infer it from context.

We can now go back and make polymorphic versions of all the
list-processing functions that we wrote before. Here is `myRepeat`,
for example:
::::

:::slidebreak
:::

:::terse
We can now define polymorphic versions of the functions
we've already seen...
:::

```lean
def myRepeat (α : Type) (x : α) (count : Nat) : MyList α :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (myRepeat α x count')
```

Some simple facts about {name}`myRepeat`:

```lean
theorem myRepeat_zero (α : Type) (v : α) :
    myRepeat α v 0 = MyList.nil := rfl

theorem myRepeat_succ (α : Type) (v : α) (count : Nat) :
    myRepeat α v (count + 1) = MyList.cons v (myRepeat α v count) := rfl
```

::::full
We can use {name}`myRepeat` by applying it first to a type and then
to an element of this type (and a number):
::::

```lean
example : myRepeat Nat 4 2 = .cons 4 (.cons 4 .nil) := by rfl
```

::::full
To use {name}`myRepeat` to build other kinds of lists, we simply
pass a different type and an element of that type:
::::

```lean
example : myRepeat Bool false 1 = .cons false .nil := by rfl
```

::::quiz
What is the type of `MyList.cons true (MyList.cons 3 MyList.nil)`?

(A) {lean}`MyList Nat`

(B) {lean}`{α : Type} → α → MyList α → MyList α`

(C) {lean}`MyList Bool`

(D) {lean}`MyList (Nat × Bool)`

(E) Ill-typed

:::quizSolution
(E)
:::
::::

::::quiz
What is the type of {name}`myRepeat`?

(A) {lean}`Nat → Nat → MyList Nat`

(B) {lean}`(α : Type) → α → Nat → MyList α`

(C) {lean}`(α : Type) → {β : Type} → α → Nat → MyList β`

(D) Ill-typed

:::quizSolution
(B)
:::
::::

::::quiz
What is the type of `myRepeat 1 2`?

(A) {lean}`MyList Nat`

(B) {lean}`(α : Type) → α → Nat → MyList α`

(C) {lean}`MyList Bool`

(D) Ill-typed

:::quizSolution
(D)
:::
::::

::::full
From now on, we'll use Lean's built-in {name}`List` type and its
associated notation. The built-in {name}`List` is defined just like
our {name}`MyList` above, but with notation {lean}`[]` for {name}`List.nil`,
`::` for {name}`List.cons`, and {lean}`[1, 2, 3]` for list literals.
The `++` operator is list append. The type arguments to the list constructors are implicit.
::::

:::slidebreak
:::

::::terse
From now on we'll use Lean's built-in {lean}`List α` type
with notations {lean}`[]`, `::`, {lean}`[1, 2, 3]`, and `++`.
::::

::::full
Using Lean's built-in list notations, we can now write lists
in the natural way:
::::

```lean
example : List Nat := [1, 2, 3]
```

### Type Annotation Inference

Let's write the definition of {name}`myRepeat` again, but this time we won't specify
the type of the parameter {lean}`α`. Will Lean still accept it?

```lean
def myRepeat' α (x : α) (count : Nat) : List α :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (myRepeat' α x count')
```

Indeed it will. Lean infers that `α` is a type.

```lean (name := myRepeat')
#check myRepeat'
```

```leanOutput myRepeat'
myRepeat'.{u_1} (α : Type u_1) (x : α) (count : Nat) : List α
```

The generated
`u_1` is part of Lean's bookkeeping for treating types more generally.
We will not need to interpret names like this for now —
you can ignore them when they appear in Lean's output unless we explicitly
call attention to them.

::::terse
Lean has used _type inference_ to deduce a type for {lean}`α`.
::::

::::full
Lean was able to use _type inference_ to deduce what the type of {lean}`α`
must be, based on how it is used. Since {lean}`α` is an argument to {name}`List`,
it must be a {lean}`Type`, since {name}`List` expects a {lean}`Type` as its argument.

This facility means we don't always have to write explicit type annotations
everywhere, although explicit type annotations can still be quite useful
as documentation, so we will continue to use them much of the time.
::::

### Type Argument Synthesis

::::full
To use a polymorphic function, we need to pass it one or
more types in addition to its other arguments. For example, the
recursive call in the body of the {name}`myRepeat` function above must
pass along the type {lean}`α`. But since the second argument to
{name}`myRepeat` is an element of {lean}`α`, it seems entirely obvious that the
first argument can only be {lean}`α` — why should we have to write it
explicitly?

Fortunately, Lean permits us to avoid this kind of redundancy. In
place of any type argument we can write a "hole" `_`, which can be
read as "Please try to figure out for yourself what belongs here."
More precisely, when Lean encounters a `_`, it will attempt to
_unify_ all locally available information — the type of the
function being applied, the types of the other arguments, and the
type expected by the context in which the application appears —
to determine what concrete type should replace the `_`.

Using holes, the {name}`myRepeat'` function can be rewritten like this:
::::

::::terse
Supplying every type _argument_ is also boring, but Lean
can usually infer them:
::::

```lean
def myRepeat'' (α : Type) (x : α) (count : Nat) : List α :=
  match count with
  | 0 => []
  | count' + 1 => x :: myRepeat'' _ x count'
```

::::full
Alternatively, we can declare an argument to be implicit
when defining the function itself, by surrounding it in curly
braces instead of parentheses. For example:
::::

::::terse
Alternatively, we can declare arguments implicit by
surrounding them with curly braces instead of parens:
::::

```lean
def myRepeat''' {α : Type} (x : α) (count : Nat) : List α :=
  match count with
  | 0 => []
  | count' + 1 => x :: myRepeat''' x count'
```

::::full
By making the type argument implicit, we no longer need to provide it
to the recursive call to {name}`myRepeat'''`. Indeed, it
would be invalid to provide one, because Lean is not expecting it.
For each implicit parameter, Lean automatically inserts a hidden
hole `_` argument for us, which is then inferred as usual.
::::

### Supplying Type Arguments Explicitly

::::full
One small problem with implicit arguments is that, once in a
while, Lean does not have enough local information to determine
a type argument; in such cases, we need to tell Lean the type
explicitly. For example:
::::

::::terse
In general, it's fine to just let Lean infer all type
arguments. But occasionally this can lead to problems:
::::

This fails because Lean can't figure out the type of the empty list:
`def mynil := []` — error: type not known
We can fix this with an explicit type annotation:

We can use the `@` prefix to supply the type
argument explicitly. The `@` makes all implicit arguments
of a function explicit:

```lean (name := nil2)
#check @List.nil

def myNil' := @List.nil Nat
```

```leanOutput nil2
@List.nil : {α : Type u_1} → List α
```

:::slidebreak
:::

::::quiz
Which type does Lean assign to the following expression?
(The square brackets in this quiz and the following ones are list
brackets.)

```display
[1, 2, 3]
```

(A) {lean}`List Nat`

(B) {lean}`List Bool`

(C) {name}`Bool`

(D) No type can be assigned
::::

:::quizSolution
(A)
:::

::::quiz
What about this one?

```display
[3 + 4] ++ []
```

(A) {lean}`List Nat`

(B) {lean}`List Bool`

(C) {lean}`Bool`

(D) No type can be assigned
::::

:::quizSolution
(A)
:::

::::quiz
What about this one?

```display
(true && false) :: []
```

(A) {lean}`List Nat`

(B) {lean}`List Bool`

(C) {name}`Bool`

(D) No type can be assigned
::::

:::quizSolution
(B)
:::

::::quiz
What about this one?

```display
[1, []]
```

(A) {lean}`List Nat`

(B) {lean}`List (List Nat)`

(C) {lean}`List Bool`

(D) No type can be assigned
::::

:::quizSolution
(D)
:::

::::quiz
What about this one?

```display
[[1], []]
```

(A) {lean}`List Nat`

(B) {lean}`List (List Nat)`

(C) {lean}`List Bool`

(D) No type can be assigned
::::

:::quizSolution
(B)
:::

::::quiz
And what about this one?

```display
[1] :: [[]]
```

(A) {lean}`List Nat`

(B) {lean}`List (List Nat)`

(C) {lean}`List Bool`

(D) No type can be assigned
::::

:::quizSolution
(B)
:::

::::quiz
This one?

```display
@List.nil Bool
```

(A) {lean}`List Nat`

(B) {lean}`List (List Nat)`

(C) {lean}`List Bool`

(D) No type can be assigned
::::

:::quizSolution
(C)
:::

::::::full
:::::exercise (rating := 2) (name := "mumble_grumble") (optional := true) (manual := true)
Consider the following two inductively defined types.

```lean
inductive Mumble : Type where
  | a : Mumble
  | b (x : Mumble) (y : Nat) : Mumble
  | c : Mumble

inductive Grumble (α : Type) : Type where
  | d (m : Mumble) : Grumble α
  | e (x : α) : Grumble α
```

Which of the following are well-typed elements of {lean}`Grumble α` for
some type {lean}`α`?  (Add YES or NO to each line.)
- `Grumble.d (Mumble.b Mumble.a 5)`
- `@Grumble.d Mumble (Mumble.b Mumble.a 5)`
- `@Grumble.d Bool (Mumble.b Mumble.a 5)`
- `@Grumble.e Bool true`
- `@Grumble.e Mumble (Mumble.b Mumble.c 0)`
- `@Grumble.e Bool (Mumble.b Mumble.c 0)`
- `Mumble.c`

:::solution
- YES — {lean}`Grumble.d (Mumble.b Mumble.a 5)`
- YES — {lean}`@Grumble.d Mumble (Mumble.b Mumble.a 5)`
- YES — {lean}`@Grumble.d Bool (Mumble.b Mumble.a 5)`
- YES — {lean}`@Grumble.e Bool true`
- YES — {lean}`@Grumble.e Mumble (Mumble.b Mumble.c 0)`
- NO  — `@Grumble.e Bool (Mumble.b Mumble.c 0)`
- NO  — `Mumble.c`
:::

:::::

::::::

### Exercises

```lean
def List.rev {α : Type} (l : List α) : List α :=
  match l with
  | .nil => .nil
  | .cons h t => rev t ++ (.cons h .nil)

theorem rev_nil {α : Type} : ([] : List α).rev = [] := by rfl

theorem rev_cons {α : Type} {x : α} {l : List α} :
    (x :: l).rev = l.rev ++ [x] := by rfl
```

:::::exercise (rating := 2) (name := "poly_exercises")
Here are a few simple exercises, just like ones in the {ref "Lists"}[Lists] chapter,
for practice with polymorphism. Complete the proofs below.
You will likely find useful the following
characterizing lemmas for {name}`List.append` in Lean standard library:

```lean (name := lemmas_append)
#check List.nil_append
#check List.cons_append
```

```leanOutput lemmas_append
List.cons_append.{u} {α : Type u} {a : α} {as bs : List α} : a :: as ++ bs = a :: (as ++ bs)
```

```leanOutput lemmas_append
List.nil_append.{u} {α : Type u} (as : List α) : [] ++ as = as
```

```lean
theorem append_nil {α : Type} {l : List α} :
    l ++ [] = l := by
  solution!
    induction l with
    | nil => rw [List.nil_append]
    | cons _ _ ih => rw [List.cons_append, ih]

theorem append_assoc {α : Type} {l₁ l₂ l₃ : List α} :
    l₁ ++ l₂ ++ l₃ = l₁ ++ (l₂ ++ l₃) := by
  solution!
    induction l₁ with
    | nil => rw [List.nil_append, List.nil_append]
    | cons _ _ ih =>
      dsimp [List.cons_append]
      rw [ih]

theorem append_length {α : Type} {l₁ l₂ : List α} :
    (l₁ ++ l₂).length = l₁.length + l₂.length := by
  solution!
    induction l₁ with
    | nil =>
      dsimp [List.nil_append, append_nil]
      rw [Nat.zero_add]
    | cons _ _ ih =>
      dsimp [List.cons_append, List.length_cons]
      rw [Nat.succ_add, ih]
```

:::gradeTheorem "0.5" append_nil
:::

:::gradeTheorem 1 append_assoc
:::

:::gradeTheorem "0.5" append_length
:::
:::::

:::::exercise (rating := 2) (name := "more_poly_exercises")
Here are some slightly more interesting ones...

```lean
theorem reverse_append {α : Type} {l₁ l₂ : List α} :
    (l₁ ++ l₂).rev = l₂.rev ++ l₁.rev := by
  solution!
    induction l₁ with
    | nil =>
      dsimp [List.nil_append]
      rw [rev_nil, append_nil]
    | cons _ _ ih =>
      dsimp [List.cons_append]
      rw [rev_cons, rev_cons, ih, append_assoc]

theorem reverse_reverse {α : Type} (l : List α) :
    l.rev.rev = l := by
  solution!
    induction l with
    | nil => rw [rev_nil, rev_nil]
    | cons _ _ ih =>
      rw [rev_cons, reverse_append, ih, rev_cons, rev_nil]
      dsimp [List.nil_append, List.cons_append]
```

:::gradeTheorem 1 reverse_append
:::

:::gradeTheorem 1 reverse_reverse
:::
:::::

## Polymorphic Pairs

Like `inductive`s, `structure`s can also be made polymorphic.
If we generalize the definition `NatProd` of pairs of natural numbers from last chapter,
we get polymorphic pairs, often called _products_:

```lean
structure MyProd (α β : Type) where
  fst : α
  snd : β
```

Lean's built-in product type {name}`Prod` provides a {name}`Prod.mk` constructor,
and {name}`Prod.fst` and {lean}`Prod.snd` functions for accessing the first and
second components of the pair. It also has special syntax for creating products:

```lean (name := pair)
#check (1, true)
#eval (1, true).fst
#eval (1, true).snd
```

```leanOutput pair
(1, true) : Nat × Bool
```

```leanOutput pair
1
```

```leanOutput pair
true
```

You can also use `.1` instead of `.fst` and `.2` instead of `.snd`:

```lean
example : (3, 5).1 = 3 := by rfl
example : (3, 5).2 = 5 := by rfl
```

Lean writes the product type {lean}`Prod α β` as {lean}`α × β`.
In VS Code you can type `\times` or `\x` to enter the `×` symbol.


::::full
It is easy at first to get {lean}`(x, y)` and {lean}`α × β` confused.
Remember that {lean}`(x, y)` is a _value_ built from two other values,
while {lean}`α × β` is a _type_ built from two other types. If {lean}`x` has
type {lean}`α` and {lean}`y` has type {lean}`β`, then {lean}`(x, y)` has type {lean}`α × β`.
::::

::::terse
Be careful not to get {lean}`(x, y)` and {lean}`α × β` confused!
::::

:::slidebreak
:::

::::full
The following function takes two lists and combines them
into a list of pairs.
::::

:::slidebreak
:::

::::terse
What does this function do?
::::

```lean
def zip {α β : Type} (l₁ : List α) (l₂ : List β) : List (α × β) :=
  match l₁, l₂ with
  | [], [] => []
  | _ :: _, [] => []
  | [], _ :: _ => []
  | x :: l₁', y :: l₂' => (x, y) :: zip l₁' l₂'

theorem zip_nil_left {α β : Type} (l₁ : List α) : zip l₁ [] = ([] : List (α × β)) := by
  cases l₁ with
  | nil => rfl
  | cons h t => rfl

theorem zip_nil_right {α β : Type} (l₂ : List β) : zip [] l₂ = ([] : List (α × β)) := by
  cases l₂ <;> rfl

theorem zip_cons_cons {α β : Type} {x : α} {y : β} {l₁ : List α} {l₂ : List β} :
   zip (x :: l₁) (y :: l₂) = (x, y) :: zip l₁ l₂ := by rfl
```

Notice that the simplification lemmas {name}`zip_nil_left` and {name}`zip_nil_right` are not proofs by `rfl`.
The reason is that `l₁` and `l₂` are variables, and matching on a variable usually gets stuck, like we have seen before in {ref "Induction"}[Induction] when proving the `zero_add` theorem.
To overcome this, we destruct the list so that the `match` knows which branch to take during the computation done by the `rfl` tactic.

:::::exercise (rating := 1) (name := "zip_checks") (optional := true) (manual := true)
Try answering the following questions on paper and
checking your answers in Lean:
- What is the type of `zip` (i.e., what does `#check @zip` print?)
- What does
  ```display
  #eval zip [1, 2] [false, false, true, true]
  ```
  print?
:::::

::::full
When working with pairs, we often wish to prove them equal.
When they compute to the same value, we can use `rfl` as usual:

```lean
example : (1 + 2, 5) = (3, 2 + 3) := by
  rfl
```

However, we don't always have concrete values available.
For example, here both pairs are equal, but not definitionally:

```lean +error -keep (name := prodEqComm)
example {n : Nat} : (n + 1, 0) = (1 + n, 0) := by
  rfl
```

```leanOutput prodEqComm
Tactic `rfl` failed: The left-hand side
  (n + 1, 0)
is not definitionally equal to the right-hand side
  (1 + n, 0)

α β γ : Type
x : α
y : β
n : Nat
⊢ (n + 1, 0) = (1 + n, 0)
```

One way to prove this would be to rewrite by {name}`Nat.add_comm` inside the pair:

```lean
example {n : Nat} : (n + 1, 0) = (1 + n, 0) := by
  rw [Nat.add_comm]
```

But this won't always work in general. Let's look at a more involved example.
Remember `surjective_pairing` from {ref "Lists"}[Lists]?
In Lean's standard library, this lemma is called {name}`Prod.eta`,
and we can use it to rewrite `p` into `(p.fst, p.snd)` like this:

```lean
example {n : Nat} {p : Nat × Nat} (hx_fst : p.fst = n + 1) (hx_snd : p.snd = 0) :
    (n + 1, 0) = p := by
  rw [← Prod.eta p]
  rw [hx_fst, hx_snd]
```

However, {name}`Prod.eta` is rarely used directly, since the theorem {name}`Prod.ext`,
the _extensionality principle_ for products, is often easier to work with.
{name}`Prod.ext` splits the proof into two goals:
first, to show that the `fst` elements are equal, and second, to show that the `snd`
elements are equal.
Here's an example:
::::

::::terse
We can use {name}`Prod.ext` to prove equality of pairs by showing equality of their components:
::::

```lean
example {n : Nat} {p : Nat × Nat} (hx_fst : p.fst = n + 1) (hx_snd : p.snd = 0) :
    (n + 1, 0) = p := by
  apply Prod.ext
  · rw [hx_fst]
  · rw [hx_snd]
```

::::exercise (rating := 2) (name := "prod_ext_example")
Now, use {name}`Prod.ext` to prove the following.
Remember that {tactic}`dsimp` simplifies projections like `(a, b).fst` to `a`.

```lean
example {m : Nat} {p : Nat × Nat} (hp_snd : p.snd = 4) (hp_fst : p.fst = m) :
    ((p.fst + 1, 2), (p.fst, 4)) = ((m + 1, p.snd - 2), p) := by
  solution!
    apply Prod.ext
    · dsimp
      apply Prod.ext
      · dsimp
        rw [hp_fst]
      · dsimp
        rw [hp_snd]
    · dsimp
      apply Prod.ext
      · rfl
      · dsimp
        rw [hp_snd]
```
::::

:::::exercise (rating := 3) (name := "unzip") (manual := true)
The function `unzip` goes in the other direction from {name}`zip`: it takes a list of pairs and returns a pair of lists.

Fill in the definition of `unzip` below and write simplification rules that characterize it.
Make sure it that passes the given unit test.
Prove `unzip_test_fst` and `unzip_test_snd` by rewriting with your simplification lemmas instead of using `rfl` directly.

```lean
def unzip {α : Type} {β : Type} (l : List (α × β)) : List α × List β := solution!(
  match l with
  | [] => ([], [])
  | (x, y) :: l' =>
    let (l₁, l₂) := unzip l'
    (x :: l₁, y :: l₂))
```

:::solution
```lean
-- This is a must have. One has to explicitly specify the types of the empty lists, which
-- can be done in two equivalent ways
theorem unzip_nil {α β : Type} : unzip [] = (([], []) : List α × List β) := by rfl
theorem unzip_nil' {α β : Type} : unzip ([] : List (α × β)) = ([], []) := by rfl

-- To characterize the cons branch, we can introduce a single `unzip_cons`...
theorem unzip_cons {α β : Type} {x : α} {y : β} {l : List (α × β)} :
    (unzip ((x, y) :: l)) = (x :: (unzip l).fst, y :: (unzip l).snd) := by rfl

-- ... or introduce lemmas `unzip_cons_fst/snd` which individually give both sides of `unzip_cons`
theorem unzip_cons_fst {α β : Type} {x : α} {y : β} {l : List (α × β)} :
    (unzip ((x, y) :: l)).fst = x :: (unzip l).fst := by rfl

theorem unzip_cons_snd {α β : Type} {x : α} {y : β} {l : List (α × β)} :
    (unzip ((x, y) :: l)).snd = y :: (unzip l).snd := by rfl
```
:::

```lean
theorem unzip_test1 : unzip [(1, false), (2, true)] = ([1, 2], [false, true]) := by
  solution!
    rfl

theorem unzip_test_fst : (unzip [(1, false), (2, true)]).fst = [1, 2] := by
  solution!
    rw [unzip_cons_fst, unzip_cons_fst, unzip_nil]

theorem unzip_test_snd : (unzip [(1, false), (2, true)]).snd = [false, true] := by
  solution!
    · rw [unzip_cons_snd, unzip_cons_snd, unzip_nil]

theorem unzip_test2 : unzip [(1, false), (2, true)] = ([1, 2], [false, true]) := by
  solution!
    exact Prod.ext unzip_test_fst unzip_test_snd
```

:::solution
```lean
-- These are the same tests but with `unzip_cons` instead
theorem unzip_test_fst' : (unzip [(1, false), (2, true)]).fst = [1, 2] := by
  rw [unzip_cons]
  dsimp
  rw [unzip_cons]
  dsimp
  rw [unzip_nil]

theorem unzip_test_snd' : (unzip [(1, false), (2, true)]).snd = [false, true] := by
  rw [unzip_cons]
  dsimp
  rw [unzip_cons]
  dsimp
  rw [unzip_nil]

theorem unzip_test2' : unzip [(1, false), (2, true)] = ([1, 2], [false, true]) := by
  exact Prod.ext unzip_test_fst unzip_test_snd
```
:::
:::::

## Polymorphic Options

::::full
Our last polymorphic type for now is _polymorphic options_.
Lean's standard library provides {lean}`Option α`, with constructors
{name}`none` and {lean}`some`. (We already saw `NatOption` in the {ref "Lists"}[Lists] chapter.)
Let's briefly look at the definition:

```lean
namespace OptionPlayground

inductive Option (α : Type) : Type where
  | none : Option α
  | some (x : α) : Option α

end OptionPlayground
```
::::

:::slidebreak
:::

::::full
We can now rewrite the `nth?` function so that it works
with any type of list.
::::

```lean
def nth? {α : Type} (l : List α) (n : Nat) : Option α :=
  match l with
  | [] => none
  | x :: l' => match n with
    | 0 => some x
    | n' + 1 => nth? l' n'
```

```lean
example : nth? [4, 5, 6, 7] 0 = some 4 := by rfl
example : nth? [[1], [2]] 1 = some [2] := by rfl
example : nth? [true] 2 = none := by rfl
```

::::::full
:::::exercise (rating := 1) (name := "head?_poly") (optional := true)
Complete the definition of a polymorphic version of the
`head?` function from the {ref "Lists"}[last chapter]. Be sure that it
passes the unit tests below.

```lean
def head? {α : Type} (l : List α) : Option α := solution!(
  match l with
  | [] => none
  | x :: _ => some x)

theorem head?_nil {α : Type} : head? ([] : List α) = none := solution!(by rfl)

theorem head?_cons {α : Type} {head : α} {tail : List α} : head? (head :: tail) = some head :=
  solution!(by rfl)

theorem test_head?1 : head? [1, 2] = some 1 := solution!(by rfl)
```

:::gradeTheorem "0.5" test_head?1
:::

```lean
theorem test_head?2 : head? [[1], [2]] = some [1] := solution!(by rfl)
```

:::gradeTheorem "0.5" test_head?2
:::
:::::

::::::

# Functions as Data

::::full
Like most modern programming languages — especially other
"functional" languages, including OCaml, Haskell, Racket, Scala,
Clojure, etc. — Lean treats functions as first-class citizens,
allowing them to be passed as arguments to other functions,
returned as results, stored in data structures, etc.
::::

## Higher-Order Functions

::::full
Functions that manipulate other functions are often called
_higher-order_ functions. Here's a simple one:
::::

::::terse
Functions that take other functions as arguments or return them
as results are called higher-order functions.
::::

```lean
def doIt3Times {α : Type} (f : α → α) (x : α) : α :=
  f (f (f x))
```

::::full
The argument `f` here is itself a function (from {lean}`α` to {lean}`α`);
the body of {name}`doIt3Times` applies `f` three times to some value `x`.
::::

```lean (name := doIt3Times)
#check doIt3Times

example : doIt3Times Nat.minusTwo 9 = 3 := by rfl

example : doIt3Times not true = false := by rfl
```

```leanOutput doIt3Times
doIt3Times {α : Type} (f : α → α) (x : α) : α
```

## Filter

:::instructors
We've tried to be careful with terminology in the rest
of the notes: "(boolean) predicate" for boolean functions and
"property" for propositions indexed by one parameter.
:::

::::full
Here is a more useful higher-order function, taking a list
of {lean}`α`s and a _predicate_ on {lean}`α` (a function from {lean}`α` to {name}`Bool`)
and "filtering" the list to yield a new list containing just
those elements for which the predicate returns {name}`true`.
::::

::::terse
A _higher-order function_ can take another function as an
argument. For example, `filter` takes a test and a list.
::::

```lean
def filter {α : Type} (test : α → Bool) (l : List α) : List α :=
  match l with
  | [] => []
  | x :: l' =>
    bif test x then x :: filter test l'
    else filter test l'
```

::::full
For example, if we apply {name}`filter` to the predicate {name}`Nat.even`
and a list of numbers, it returns a list containing just the
even members.
::::

```lean
example : filter Nat.even [1, 2, 3, 4] = [2, 4] := by rfl
```

:::slidebreak
:::

Here are some further examples and properties of {name}`filter`.

```lean
def isLength1 {α : Type} (l : List α) : Bool :=
  l.length == 1

example : filter isLength1
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

theorem filter_nil {α : Type} {test : α → Bool} : filter test [] = [] := by rfl

theorem filter_cons_of_pos {α : Type} {test : α → Bool} {x : α}
    {l : List α} (h : test x = true) :
    filter test (x :: l) = x :: filter test l := by
  dsimp [filter]
  rw [h]
  dsimp

theorem filter_cons_of_neg {α : Type} {test : α → Bool} {x : α}
    {l : List α} (h : test x = false) :
    filter test (x :: l) = filter test l := by
   dsimp [filter]
   rw [h]
   dsimp
```

::::full
You might have noticed that {name}`filter_cons_of_pos` and {name}`filter_cons_of_neg`
have implicit parameters, such as `head` and `tail`, that do not have type {lean}`Type` like `α` does.
As it turns out, Lean allows _any_ parameter to be implicit, not just those of type {lean}`Type`.
This is a standard Lean convention for lemmas that are likely to be used by {tactic}`rw`
or {tactic}`dsimp` when their values can be inferred by unification.

For example, suppose you were using this theorem to rewrite `filter Nat.even (3 :: rest)`.
Matching that expression against the theorem's left-hand side `filter test (head :: tail)`
establishes that `test = Nat.even`, `head = 3`, `tail = rest`, and
{lean}`α = Nat`. By making these arguments implicit, Lean automatically inserts
a hole `_` for each of them when you apply the theorem, just as with implicit parameters
of type {lean}`Type`, so they can be inferred from the context.

Note that `h : test head` is not implicit, it's explicit. That's because it cannot be
solved by unification, i.e., Lean can't prove that `Nat.even 3 = true` that way.
It's a general proof obligation.

We'll follow the Lean standard convention from now on.
::::

::::terse
Note that `head` and `tail` are implicit too, following a general convention: any
argument an equation's shape determines when applied is made implicit, so using {tactic}`rw`
and {tactic}`simp` lemmas requires no extra `_` arguments.
::::

:::slidebreak
:::

:::dev PotentialImprovement
This material would sink in better if it were made clearer
why map and filter and such were useful in the real world. Talk
about map/reduce, collection-oriented programming, etc. Esp in the
terse version.
:::

::::terse
The {name}`filter` function (especially when combined with some
other functions we'll see later) enables a powerful
_wholemeal_ (or _collection-oriented_) programming style.
::::

::::full
We can use {name}`filter` to give a concise version of the
`countOddMembers` function from the {ref "Lists"}[Lists] chapter.
::::

```lean
def countOddMembers (l : List Nat) : Nat := (filter Nat.odd l).length

example : countOddMembers [1, 0, 3, 1, 4, 5] = 4 := by rfl
example : countOddMembers [0, 2, 4] = 0 := by rfl
example : countOddMembers [] = 0 := by rfl
```

## Anonymous Functions

::::full
It is arguably a little sad, in the example just above, to
be forced to define the function {name}`isLength1` and give it a name
just to be able to pass it as an argument to {name}`filter`, since we
will probably never use it again. Indeed, when using higher-order
functions, we _often_ want to pass as arguments "one-off"
functions that we will never use again; having to give each of
these functions a name would be tedious.

Fortunately, there is a better way. We can construct a function
"on the fly" without declaring it at the top level or giving it a
name. Lean provides two syntaxes for anonymous functions:

- `fun n => n * n` — traditional lambda syntax
- `(· * ·)` — "term with holes" syntax, where `·` marks arguments
::::

::::terse
Functions can be constructed "on the fly" without giving
them names.
::::

```lean
example : doIt3Times (fun n => n * n) 2 = 256 := by rfl
```

::::full
The expression `fun n => n * n` can be read as "the function
that, given a number `n`, yields `n * n`."

Lean also supports a shorter notation using `·` as a placeholder
for the argument:
::::

::::terse
Lean also provides the shorter `·` notation for anonymous
functions.
::::

```lean
example : doIt3Times (· + 1) 0 = 3 := by rfl
```

::::full
Here is the {name}`filter` example, rewritten to use an anonymous
function.
::::

```lean
example : filter (fun l => l.length == 1)
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

example : filter (·.length == 1)
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl
```

::::::full
:::::exercise (rating := 2) (name := "filter_even_gt7")
Use {name}`filter` (instead of a recursive `def`) to write a Lean function
`filterEvenGt7` that takes a list of natural numbers as input
and returns a list of just those that are even and greater than {lean}`7`.

```lean
def filterEvenGt7 (l : List Nat) : List Nat := solution!(
  filter (fun n => n.even && n > 7) l)

theorem test_filterEvenGt7_1 : filterEvenGt7 [1, 2, 6, 9, 10, 3, 12, 8] = [10, 12, 8] := solution!(by rfl)

theorem test_filterEvenGt7_2 : filterEvenGt7 [5, 2, 6, 19, 129] = [] := solution!(by rfl)
```

:::gradeTheorem 1 test_filterEvenGt7_1 test_filterEvenGt7_2
:::
:::::

:::::exercise (rating := 3) (name := "partition")
Use {name}`filter` to write a Lean function `partition` that, given a
type {lean}`α`, a predicate of type {lean}`α → Bool` and a {lean}`List α`, should
return a pair of lists. The first member of the pair is the sublist
of the original list containing the elements that satisfy the test,
and the second is the sublist containing those that fail the test.
The order of elements in the two sublists should be the same as
their order in the original list.

```lean
def partition {α : Type} (test : α → Bool) (l : List α) : List α × List α := solution!(
  (filter test l, filter (!test ·) l))

theorem test_partition1 : partition (· % 2 != 0) [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) := solution!(by rfl)
theorem test_partition2 : partition (fun _ => false) [5, 9, 0] = ([], [5, 9, 0]) := solution!(by rfl)
```

:::gradeTheorem "1.5" test_partition1 test_partition2
:::
:::::

::::::

## Map

::::full
Another handy higher-order function is called `map`.
::::

```lean
def map {α β : Type} (f : α → β) (l : List α) : List β :=
  match l with
  | [] => []
  | head :: tail => f head :: map f tail
```

::::full
It takes a function `f` and a list `l = [n1, n2, n3, ...]`
and returns the list `[f n1, f n2, f n3, ...]`, where `f` has
been applied to each element of `l` in turn. For example:
::::

```lean
example : map (· + 3) [2, 0, 2] = [5, 3, 5] := by rfl
```

::::full
The element types of the input and output lists need not be
the same, since {name}`map` takes _two_ type arguments, {lean}`α` and {lean}`β`; it
can thus be applied to a list of numbers and a function from
numbers to booleans to yield a list of booleans:
::::

```lean
example : map Nat.odd [2, 1, 2, 5] = [false, true, false, true] := by rfl
```

::::full
It can even be applied to a list of numbers and
a function from numbers to _lists_ of booleans to
yield a _list of lists_ of booleans:
::::

```lean
example : map (fun n => [n.even, n.odd]) [2, 1, 2, 5]
  = [[true, false], [false, true], [true, false], [false, true]] := by rfl
```

::::quiz
Recall the definition of {name}`map`:

```recall
def map {α β : Type} (f : α → β) (l : List α) : List β :=
  match l with
  | [] => []
  | head :: tail => f head :: map f tail
```

What is the type of `@map`?

(A) {lean}`{α β : Type} → α → β → List α → List β`

(B) {lean}`α → β → List α → List β`

(C) {lean}`{α β : Type} → (α → β) → List α → List β`

(D) {lean}`{α : Type} → (α → α) → List α → List α`
::::

:::slidebreak
:::

As usual, we define the following simplification rules for {name}`map`:

```lean
theorem map_nil {α : Type} {β : Type} {f : α → β} : map f [] = [] := by rfl

theorem map_cons {α : Type} {β : Type} {f : α → β} {x : α} {l : List α} :
    map f (x :: l) = f x :: map f l := by rfl
```

::::::full
:::::exercise (rating := 3) (name := "map_rev")
Show that {name}`map` and {name}`List.rev` commute. (Hint: You may need to
define an auxiliary lemma.)

```lean
-- SOLUTION
theorem map_append {α β : Type} {f : α → β} {l l' : List α} :
    map f (l ++ l') = map f l ++ map f l' := by
  induction l with
  | nil => rw [map_nil, List.nil_append, List.nil_append]
  | cons _ _ ih => rw [List.cons_append, map_cons, map_cons, ih, List.cons_append]
-- END SOLUTION

theorem map_rev {α : Type} {β : Type} {f : α → β} {l : List α} :
    map f l.rev = (map f l).rev := by
  solution!
    induction l
    case nil =>
     rw [rev_nil, map_nil, rev_nil]
    case cons _ _ ih =>
     rw [rev_cons, map_cons, map_append, rev_cons, ih, map_cons, map_nil]
```

:::gradeTheorem 3 map_rev
:::
:::::

:::::exercise (rating := 2) (name := "flat_map")
The function {name}`map` maps a {lean}`List α` to a {lean}`List β` using a function
of type {lean}`α → β`. We can define a similar function, `flatMap`,
which maps a {lean}`List α` to a {lean}`List β` using a function `f` of type
{lean}`α → List β`. Your definition should work by 'flattening' the
results of `f`, like so:

```display
flatMap (fun n => [n, n + 1, n + 2]) [1, 5, 10]
  = [1, 2, 3, 5, 6, 7, 10, 11, 12]
```

```lean
def flatMap {α β : Type} (f : α → List β) (l : List α) : List β := solution!(
  match l with
  | [] => []
  | h :: t => f h ++ flatMap f t)

theorem test_flatMap : flatMap (fun n => [n, n, n]) [1, 5, 4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4] := solution!(by rfl)
```

:::gradeTheorem 2 test_flatMap
:::
:::::

```lean
theorem flatMap_nil {α : Type} {β : Type} (f : α → List β) : flatMap f [] = [] :=
   solution!(by rfl)

theorem flatMap_cons {α : Type} {β : Type} (f : α → List β) h t :
   flatMap f (h :: t) = f h ++ flatMap f t := solution!(by rfl)
```
::::::

Lists are not the only inductive type for which {name}`map` makes sense.
Here is a {name}`map` for the {name}`Option` type:

```lean
def optionMap {α : Type} {β : Type} (f : α → β) (x? : Option α) : Option β :=
  match x? with
  | none => none
  | some x => some (f x)
```

::::::full
:::::exercise (rating := 2) (name := "implicit_args") (optional := true)
The definitions and uses of {name}`filter` and {name}`map` use implicit
arguments in many places. Replace the curly braces around the
implicit arguments with explicit parentheses, and then fill in
explicit type parameters where necessary and use Lean to check that
you've done so correctly. (This exercise is not to be turned in;
it is probably easiest to do it on a _copy_ of this file that you
can throw away afterwards.)
:::::

::::::

## Fold

::::full
An even more powerful higher-order function is
`fold`. It is the inspiration for the "reduce"
operation that lies at the heart of Google's map/reduce
distributed programming framework.
::::

```lean
def fold {α : Type} {β : Type} (f : α → β → β) (l : List α) (b : β) : β :=
  match l with
  | [] => b
  | a :: l => f a (fold f l b)
```

::::terse
This is the "reduce" in map/reduce...
::::

:::slidebreak
:::

::::full
Intuitively, the behavior of the {name}`fold` operation is to
insert a given binary operator `f` between every pair of elements
in a given list. For example, `fold (· + ·) [1, 2, 3, 4]`
intuitively means `1 + 2 + 3 + 4`. To make this precise, we also
need a "starting element" that serves as the initial second input
to `f`. So, for example,

```display
fold (· + ·) [1, 2, 3, 4] 0
```

yields

```display
1 + (2 + (3 + (4 + 0))).
```
::::

```lean
example : fold (· && ·) [true, true, false, true] true = false := by rfl

example : fold (· * ·) [1, 2, 3, 4] 1 = 24 := by rfl

example : fold (· ++ ·) [[1], [], [2, 3], [4]] [] = [1, 2, 3, 4] := by rfl

example : fold (fun l n => l.length + n) [[1], [], [2, 3, 2], [4]] 0 = 5 := by rfl

theorem fold_nil {α : Type} {β : Type} {f : α → β → β} {b : β} : fold f [] b = b := by rfl

theorem fold_cons {α : Type} {β : Type} {f : α → β → β} {a : α} {l : List α} {b : β} :
    fold f (a :: l) b = f a (fold f l b) := by rfl
```

::::quiz
Here is the definition of `fold` again:

```recall
def fold {α β : Type} (f : α → β → β) (l : List α) (b : β) : β :=
  match l with
  | [] => b
  | a :: l => f a (fold f l b)
```

What is the type of `@fold`?

(A) `{α β : Type} → (α → β → β) → List α → β → β`

(B) `α → β → (α → β → β) → List α → β → β`

(C) `{α β : Type} → α → β → β → List α → β → β`

(D) `α → β → α → β → β → List α → β → β`

:::quizSolution
(A)
:::
::::

::::quiz
What does `fold (· + ·) [1, 2, 3, 4] 0` simplify to?

(A) `[1, 2, 3, 4]`

(B) `0`

(C) `10`

(D) `[3, 7, 0]`

:::quizSolution
(C)
:::
::::

::::::full
:::::exercise (rating := 1) (name := "fold_types_different") (optional := true) (manual := true)
Observe that the type of {name}`fold` is parameterized by _two_ type
variables, {lean}`α` and {lean}`β`, and the parameter `f` is a binary operator
that takes an {lean}`α` and a {lean}`β` and returns a {lean}`β`.
The examples above show one instance where it is useful for {lean}`α`
and {lean}`β` to be different. Can you think of any others?

:::quizSolution
There are many. For example, we could use {name}`fold` to count the
number of {name}`true` elements in a list of booleans. Here {lean}`α` would
be {name}`Bool` and {lean}`β` would be {name}`Nat`.
:::
:::::

::::::

## Functions That Construct Functions

::::full
Most of the higher-order functions we have talked about so
far take functions as arguments. Let's look at some examples that
involve _returning_ functions as the results of other functions.
To begin, here is a function that takes a value `x` (drawn from
some type {lean}`α`) and returns a function from {name}`Nat` to {lean}`α` that
yields {lean}`x` whenever it is called, ignoring its {name}`Nat` argument.
::::

::::terse
Here are two functions that _return_ functions as results.
::::

```lean
def constFun {α : Type} (x : α) : Nat → α :=
  fun _ => x

def fTrue := constFun true

example : fTrue 0 = true := by rfl

example : constFun 5 99 = 5 := by rfl
```

::::full
In fact, the multiple-argument functions we have already
seen are also examples of passing functions as data. To see why,
recall the type of addition:
::::

:::slidebreak
:::

::::terse
A two-argument function in Lean is actually a function that
returns a function!
::::

```lean (name := add)
#check Nat.add
```

```leanOutput add
Nat.add : Nat → Nat → Nat
```

```lean (name := plus3)
def plus3 := Nat.add 3
#check plus3

example : plus3 4 = 7 := by rfl
example : doIt3Times plus3 0 = 9 := by rfl
example : doIt3Times (Nat.add 3) 0 = 9 := by rfl
```

```leanOutput plus3
plus3 : Nat → Nat
```

Similarly, we can write:

```lean (name := fold_plus)
def fold_plus : List Nat → Nat → Nat :=
  fold (· + ·)

#check fold_plus
```

```leanOutput fold_plus
fold_plus : List Nat → Nat → Nat
```

::::full
What's happening here is called _partial application_. In
Lean, the type constructor `→` is right-associative, meaning a
function type like {lean}`α → β → γ` is parsed like {lean}`α → (β → γ)`,
or "a function from {lean}`α` to a function from {lean}`β` to {lean}`γ`."

We can think of {name}`fold` not as a three-argument function, but as a
one-argument function that:

1. Takes an argument `f` of type {lean}`α → β → β`
2. Returns a function of type {lean}`List α → β → β` that "remembers" `f`

When we write `fold (· + ·)`, we're giving {name}`fold` its first argument,
`(· + ·)`, and getting back a specialized function that can sum up
the elements of any list of numbers. This new function still expects
two more arguments: a list and a starting value.
::::

# Additional Exercises

:::suppressPreviousHeaderWhenTerse
:::

::::::full

:::::exercise (rating := 2) (name := "fold_length")
Many common functions on lists can be implemented in terms of
{name}`fold`. For example, here is an alternative definition of {name}`List.length`:

```lean
def foldLength {α : Type} (l : List α) : Nat :=
  fold (fun _ n => n + 1) l 0

example : foldLength [4, 7, 0] = 3 := by rfl
```

Prove the correctness of {name}`foldLength`.

Hint: It may help to use `dsimp [foldLength, fold]` to unfold
the definition.

```lean
theorem fold_length_correct {α : Type} {l : List α} :
    foldLength l = l.length := by
  solution!
    induction l with
    | nil =>
      dsimp only [foldLength]
      rw [fold_nil, List.length_nil]
    | cons _ _ ih =>
      dsimp only [foldLength] at *
      rw [List.length_cons, fold_cons, ih]
```

:::gradeTheorem 2 fold_length_correct
:::
:::::

:::::exercise (rating := 3) (name := "fold_map") (manual := true)
We can also define {name}`map` in terms of {name}`fold`.
Finish `foldMap` below.

```lean
def foldMap {α β : Type} (f : α → β) (l : List α) : List β := solution!(
  fold (fun x l' => f x :: l') l [])
```

Write down a theorem `fold_map_correct` stating that {lean}`foldMap` is
correct, and prove it in Lean.

```lean
-- SOLUTION
theorem fold_map_correct {α : Type} {β : Type} {f : α → β} {l : List α} :
    foldMap f l = map f l := by
  induction l with
  | nil =>
    dsimp only [foldMap]
    rw [fold_nil, map_nil]
  | cons _ _ ih =>
    dsimp only [foldMap] at *
    rw [fold_cons, map_cons, ih]
-- END SOLUTION
```

:::grade
`GRADE_MANUAL 3: fold_map`
:::
:::::

:::::exercise (rating := 2) (name := "currying") (level := Advanced)
The type {lean}`α → β → γ` can be read as describing functions that
take two arguments, one of type {lean}`α` and another of type {lean}`β`, and
return an output of type {lean}`γ`. Recall from our discussion
of partial application that this type is written {lean}`α → (β → γ)`
when fully parenthesized. That is, if we have `f : α → β → γ`,
and we give `f` an input of type {lean}`α`, it will give us as output
a function of type {lean}`β → γ`. If we then give that function an
input of type {lean}`β`, it will return an output of type {lean}`γ`. That
is, every function in Lean takes only one input, but some
functions return a function as output. This is precisely
what enables partial application, as we saw above with {name}`plus3`.

By contrast, functions of type {lean}`α × β → γ` — which when fully
parenthesized is written `(α × β) → γ` — require their single
input to be a pair. Both arguments must be given at once; there
is no possibility of partial application.

It is possible to convert a function between these two types.
Converting from {lean}`α × β → γ` to {lean}`α → β → γ` is called
_currying_, in honor of the logician Haskell Curry. Converting
from {lean}`α → β → γ` to {lean}`α × β → γ` is called _uncurrying_.

We can define currying as follows:

```lean
def prodCurry {α β γ : Type} (f : α × β → γ) (x : α) (y : β) : γ := f (x, y)
```

As an exercise, define its inverse, `prodUncurry`. Then prove
the theorems below to show that the two are really inverses.

```lean
def prodUncurry {α β γ : Type} (f : α → β → γ) (p : α × β) : γ := solution!(
  f p.fst p.snd)
```

As a (trivial) example of the usefulness of currying, we can use it
to shorten one of the examples that we saw above:

```lean
example : map (Nat.add 3) [2, 0, 2] = [5, 3, 5] := by rfl
```

Thought exercise: before looking at the output of the following commands,
can you calculate the types of {name}`prodCurry` and {name}`prodUncurry`?

```lean (name := c_uc)
#check @prodCurry
#check @prodUncurry
```

```leanOutput c_uc
@prodCurry : {α β γ : Type} → (α × β → γ) → α → β → γ
```

```leanOutput c_uc
@prodUncurry : {α β γ : Type} → (α → β → γ) → α × β → γ
```

```lean
theorem uncurry_curry {α β γ : Type} {x : α} {y : β} {f : α → β → γ} :
    prodCurry (prodUncurry f) x y = f x y := by
  solution!
    rfl

theorem curry_uncurry {α β γ : Type} {p : α × β} {f : α × β → γ} :
    prodUncurry (prodCurry f) p = f p := by
  solution!
    rfl
```

:::gradeTheorem 1 uncurry_curry curry_uncurry
:::
:::::

:::::exercise (rating := 2) (name := "nth_error_informal") (level := Advanced) (optional := true) (manual := true)
Recall the definition of the {name}`nth?` function:

```recall
def nth? {α : Type} (l : List α) (n : Nat) : Option α :=
  match l with
  | [] => none
  | x :: l' => match n with
    | 0 => some x
    | n' + 1 => nth? l' n'
```

Write a careful informal proof of the following theorem:

```display
∀ (l : List α) (n : Nat), l.length = n → nth? l n = none
```

Make sure to state the induction hypothesis _explicitly_.

:::solution
Theorem: For all types `α`, lists `l`, and natural numbers `n`,
if `l.length = n` then `nth? l n = none`.

Proof: By induction on `l`. There are two cases to consider:

- If `l = []`, we must show `nth? [] n = none`. This follows
  immediately from the definition of `nth?`.

- Otherwise, `l = x :: l'` for some `x` and `l'`, and the
  induction hypothesis tells us that
  `l'.length = n' → nth? l' n' = none`, for any `n'`.

  Let `n` be the length of `l`. We must show that
  `nth? (x :: l') n = none`.

  But we know that `n = l.length = (x :: l').length = l'.length + 1`.
  So it's enough to show `nth? l' l'.length = none`, which
  follows directly from the induction hypothesis, picking `l'.length`
  for `n'`.
:::

:::grade
`GRADE_MANUAL 2: informal_proof`
:::
:::::

::::::

## Church Numerals (Advanced)

:::suppressPreviousHeaderWhenTerse
:::

::::::full
The following exercises explore an alternative way of defining
natural numbers using the _Church numerals_, which are named after
their inventor, the mathematician Alonzo Church. We can represent
a natural number `n` as a function that takes a function `f` as a
parameter and returns `f` iterated `n` times.

```lean
namespace Church

def CNat := ∀ (α : Type), (α → α) → α → α
```

Let's see how to write some numbers with this notation. Iterating
a function once should be the same as just applying it. Thus:

```lean
def one : CNat :=
  fun (α : Type) (f : α → α) (x : α) => f x
```

Similarly, `two` should apply `f` twice to its argument:

```lean
def two : CNat :=
  fun (α : Type) (f : α → α) (x : α) => f (f x)
```

Defining `zero` is somewhat trickier: how can we "apply a function
zero times"?  The answer is actually simple: just return the
argument untouched.

```lean
def zero : CNat :=
  fun (α : Type) (_ : α → α) (x : α) => x
```

More generally, a number `n` can be written as
`fun α f x => f (f ... (f x) ...)`, with `n` occurrences of `f`.
Let's informally notate that as `fun α f x => f^n x`, with the
convention that `f^0 x` is just `x`. Note how the {name}`doIt3Times`
function we've defined previously is actually just the Church
representation of 3.

```lean
def three : CNat := @doIt3Times
```

So `n α f x` represents "do it `n` times", where `n` is a Church
numeral and "it" means applying `f` starting with `x`.

Another way to think about the Church representation is that
function `f` represents the successor operation on {lean}`α`, and value
`x` represents the zero element of {lean}`α`. We could even rewrite
with those names to make it clearer:

```lean
def zero' : CNat :=
  fun (α : Type) (_ : α → α) (zero : α) => zero
def one' : CNat :=
  fun (α : Type) (succ : α → α) (zero : α) => succ zero
def two' : CNat :=
  fun (α : Type) (succ : α → α) (zero : α) => succ (succ zero)
```

If we passed in `Nat.succ` as `succ` and `0` as `zero`, we'd
even get the Peano naturals as a result:

```lean
example : zero Nat Nat.succ 0 = 0 := by rfl
example : one  Nat Nat.succ 0 = 1 := by rfl
example : two  Nat Nat.succ 0 = 2 := by rfl
```

One very interesting implication of the Church numerals is that we
don't strictly need the natural numbers to be built-in to a
functional programming language, or even to be definable with an
inductive data type. It's possible to represent them purely (if
not efficiently) with functions.

Of course, it's not enough just to "represent" numerals; we need
to be able to do arithmetic with the representation. Show that we
can by completing the definitions of the following functions. Make
sure that the corresponding unit tests pass by proving them with
`rfl`.

:::::exercise (rating := 2) (name := "church_scc") (level := Advanced)
Define a function that computes the successor of a Church numeral.
Given a Church numeral `n`, its successor `scc n` should iterate
its function argument once more than `n`. That is, given
`fun X f x => f^n x` as input, `scc` should produce
`fun X f x => f^(n+1) x` as output.
In other words, do it `n` times, then do it once more.

```lean
def scc (n : CNat) : CNat := solution!(
  fun (α : Type) (f : α → α) (x : α) => f (n α f x))

example : scc zero = one := solution!(by rfl)
theorem scc_2 : scc one = two := solution!(by rfl)
theorem scc_3 : scc two = three := solution!(by rfl)
```

:::gradeTheorem 1 scc_2 scc_3
:::
:::::

:::::exercise (rating := 3) (name := "church_plus") (level := Advanced)
Define a function that computes the addition of two Church
numerals. Given `fun X f x => f^n x` and `fun X f x => f^m x`
as input, `plus` should produce `fun X f x => f^(n + m) x` as
output. In other words, do it `n` times, then do it `m` more times.

Hint: the "zero" argument to a Church numeral need not be just `x`.

```lean
def plus (n m : CNat) : CNat := solution!(
  fun (α : Type) (f : α → α) (x : α) => n α f (m α f x))

theorem plus_1 : plus zero one = one := solution!(by rfl)
theorem plus_2 : plus two three = plus three two := solution!(by rfl)
theorem plus_3 : plus (plus two two) three = plus one (plus three three) := solution!(by rfl)
```

:::gradeTheorem 1 plus_1 plus_2 plus_3
:::
:::::

:::::exercise (rating := 3) (name := "church_mult") (level := Advanced)
Define a function that computes the multiplication of two Church
numerals.

Hint: the "successor" argument to a Church numeral need not be
just `f`.

Warning: Lean will not let you pass {name}`CNat` itself as the type `α`
argument to a Church numeral; you will get a "sort mismatch"
error between {lean}`Type 1` and {lean}`Type 2`. Don't worry too much
about what this means right now, but know that
this is Lean's way of preventing a paradox in
which a type contains itself. So leave the type argument
unchanged.

```lean
def mult (n m : CNat) : CNat := solution!(
  fun (α : Type) (f : α → α) (x : α) => n α (m α f) x)

theorem mult_1 : mult one one = one := solution!(by rfl)
theorem mult_2 : mult zero (plus three three) = zero := solution!(by rfl)
theorem mult_3 : mult two three = plus three three := solution!(by rfl)
```

:::gradeTheorem 1 mult_1 mult_2 mult_3
:::
:::::

:::::exercise (rating := 3) (name := "church_exp") (level := Advanced)
Exponentiation:

Define a function that computes the exponentiation of two Church
numerals.

Hint: the type argument to a Church numeral need not just be {lean}`α`.
Finding the right type can be tricky.

```lean
def exp (n m : CNat) : CNat := solution!(
  fun (α : Type) (f : α → α) (x : α) => m (α → α) (n α) f x)

theorem exp_1 : exp two two = plus two two := solution!(by rfl)
theorem exp_2 : exp three zero = one := solution!(by rfl)
theorem exp_3 : exp three two = plus (mult two (mult two two)) one := solution!(by rfl)
```

:::gradeTheorem 1 exp_1 exp_3 exp_2
:::
:::::

```lean
end Church
```
::::::
