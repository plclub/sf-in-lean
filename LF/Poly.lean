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

:::dev "Daniel Sainati (dsainati1)"
\[BCP: Old comment -- might be out of date?\]
None of the comments at the start of the chapter motivating the polymorphic
definition of lists make sense with the change to use `List Nat` in the previous chapter.

Using the built-in definition of `List.reverse` is dramatically more complicated
than implementing our own reverse function, since it is implemented in terms of an auxiliary
function.

The associativity of `++` in Lean is different than Rocq. In Rocq the definition
of `app_assoc` is `l ++ m ++ n = (l ++ m) ++ n`, but in Lean it's
`l ++ m ++ n = l ++ (m ++ n)`.
:::

:::instructors
To get through this plus Tactics.lean in two 80-minute
lectures is a bit tight -- if that's your plan, don't dawdle on
this chapter.

(This comment may now be misaligned with the flow of lectures in CIS5000 at least, since we've
added significant new material before we get here.)
:::

```importBlock
import LF.Induction
import LF.UsingLean
```

# Polymorphism

:::suppressPreviousHeaderWhenTerse
:::

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
manipulate lists with elements from other types -- lists of
booleans, lists of lists, etc. We _could_ just define a new
inductive datatype for each of these, for example...
::::

::::terse
Instead of defining new lists for each type, like
this...
::::

```lean
inductive BoolList : Type where
  | bool_nil
  | bool_cons (b : Bool) (l : BoolList)
```

::::full
... but this would quickly become tedious: not only would we
have to make up different constructor names for each datatype, but --
even worse -- we would also need to define new versions of all
the list manipulating functions (`length`, `++`, `reverse`,
etc.) and all their properties (`rev_length`, `app_assoc`, etc.)
for each new definition.
::::

:::slidebreak
:::

::::full
To avoid all this repetition, Lean supports _polymorphic_
inductive type definitions. For example, here is a _polymorphic
list_ datatype.
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
previous chapter, except that the `Nat` argument to the `cons`
constructor has been replaced by an arbitrary type `α`, a binding
for `α` has been added to the header on the first line,
and the occurrences of `Natlist` in the types of the constructors
have been replaced by `MyList α`. We can now write `MyList Nat`
instead of a dedicated nat-list type.

What sort of thing is `MyList` itself?  A good way to think about it
is that the definition of `MyList` is a _function_ from `Type`s to
`Type`s. For any particular type `α`,
the type `MyList α` is the inductively defined set of lists whose
elements are of type `α`.
::::

::::terse
We can now write `MyList Nat` in place of a specialized
list-of-numbers type.
::::

:::slidebreak
:::

::::terse
What is `MyList` itself?

It is a _function_ from types to types.
::::

```lean
#check (MyList : Type → Type)
```

:::slidebreak
:::

::::full
The `α` in the definition of `MyList` automatically becomes a
parameter to the constructors `nil` and `cons` -- that is, `nil`
and `cons` are now polymorphic constructors. In Lean, the type
parameter is _implicit_ by default: Lean will infer it from context.
For example, `MyList.nil` is the empty list, and Lean figures out
the element type from how it is used.
::::

::::terse
The `α` in the definition of `MyList` becomes an implicit
parameter to the list constructors `nil` and `cons`.
::::

```lean
#check (MyList.nil : MyList Nat)
```

::::full
Similarly, `MyList.cons` adds an element of type `Nat` to a
list of type `MyList Nat`. Here is an example of forming a list
containing just the natural number 3.
::::

```lean
#check (MyList.cons 3 MyList.nil : MyList Nat)
```

:::dev BeforeNextRelease
Unclear - Reword
:::

::::full
What might the type of `MyList.nil` be?  We can read off the
type `MyList α` from the definition, but this omits the binding for `α`
which is the parameter to `MyList`. `Type -> MyList α` does not
explain the meaning of `α`. `(α : Type) -> List α` comes
closer. For constructors, however, the type argument is implicit; we
don't need to supply it manually.
Lean's notation for this situation is `{α : Type} -> List α`
::::

```lean
#check (@MyList.nil : {α : Type} → MyList α)
```

::::full
Similarly, the type of `MyList.cons` includes the implicit
type parameter:
::::

```lean
#check (@MyList.cons : {α : Type} → α → MyList α → MyList α)
```

:::dev "Daniel Sainati (dsainati1)" NOW
Does this still apply?
:::

:::dev "Jonathan Chan (ionathanch)" NOW
We should never write `forall` in place of `∀`,
but somewhere in `Basics` we ought to tell people
that you can find out how to type a symbol by hovering over it.
:::

::::full
(A side note on notations: In .v files, the "forall"
quantifier is spelled out in letters. In the corresponding HTML
files (and in the way some IDEs show .v files, depending on the
settings of their display controls), `forall` is usually typeset
as the standard mathematical "upside down A," though you'll still
see the spelled-out "forall" in a few places. This is just a
quirk of typesetting -- there is no difference in meaning.)
::::

::::terse
Side note: In .v files, the "forall" quantifier is spelled
out in letters. In the corresponding HTML files, it is usually
typeset as the standard mathematical "upside down A."
::::

:::dev PotentialImprovement
Maybe explain better?  (Maybe NOT using the "forall is a
funny kind of function type" intuition.)
:::

::::full
Having to supply a type argument for every single use of a
list constructor would be rather burdensome; we will soon see ways
 of reducing this annotation burden.

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

Some simple facts about list lengths

```lean
theorem repeat_zero α v : myRepeat α v 0 = MyList.nil := rfl

theorem repeat_succ α v count : myRepeat α v (count + 1) = MyList.cons v (myRepeat α v count) := rfl
```

::::full
As with `nil` and `cons`, we can use `repeat` by applying it
first to a type and then to an element of this type (and a number):
::::

```lean
example : myRepeat Nat 4 2 = .cons 4 (.cons 4 .nil) := by rfl
```

::::full
To use `myRepeat` to build other kinds of lists, we simply
pass an element of the appropriate type:
::::

```lean
example : myRepeat Bool false 1 = .cons false .nil := by rfl
```

::::quiz
What is the type of `MyList.cons true (MyList.cons 3 MyList.nil)`?

(A) `MyList Nat`

(B) `{α : Type} → α → MyList α → MyList α`

(C) `MyList Bool`

(D) `MyList (Nat × Bool)`

(E) Ill-typed
::::

::::quiz
What is the type of `myRepeat`?

(A) `Nat → Nat → MyList Nat`

(B) `{α : Type} → α → Nat → MyList α`

(C) `{α : Type} → {β : Type} → α → Nat → MyList β`

(D) Ill-typed
::::

::::quiz
What is the type of `myRepeat 1 2`?

(A) `MyList Nat`

(B) `{α : Type} → α → Nat → MyList α`

(C) `MyList Bool`

(D) Ill-typed
::::

::::full
From now on, we'll use Lean's built-in `List` type and its
associated notation. The built-in `List` is defined just like
our `MyList` above, but with notation `[]` for `List.nil`,
`::` for `List.cons`, and `[1, 2, 3]` for list literals.
The `++` operator is list append. All type arguments are implicit.
::::

:::slidebreak
:::

::::terse
From now on we'll use Lean's built-in `List α` type
with notations `[]`, `::`, `[1, 2, 3]`, and `++`.
::::

::::full
Using Lean's built-in list notations, we can now write lists
in the natural way:
::::

```lean
def list123 : List Nat := [1, 2, 3]
```

### Type Annotation Inference

:::dev "Daniel Sainati (dsainati1)" NOW
I copied this over mostly verbatim from Poly.v,
but I think the point doesn't work in Lean. The definition of `repeat'`
below doesn't typecheck, I think Lean does less inference than Rocq here.
Should we just delete this?
:::

:::dev "Jonathan Chan (ionathanch)" NOW
Lean can still infer the types of arguments that are used dependently,
so I've adapted the text below to only omit `α`. The question of what Lean infers
as its type is still tricky to present, since `#check repeat'` alone will show
that `α` is universe-polymorphic as well, which I suppose we want to avoid
explaining at this moment?
:::

Let's write the definition of `repeat` again, but this time we won't specify
the type of the parameter `α`. Will Lean still accept it?

```lean
def repeat' α (x : α) (count : Nat) : List α :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (repeat' α x count')
```

Indeed it will. We can see that `α` has the type `Type`, as expected.

```lean
#check (repeat' : ∀ (α : Type), α → Nat → List α)
```

::::terse
Lean has used _type inference_ to deduce a type for `α`.
::::

::::full
Lean was able to use _type inference_ to decude what the type of `α`
must be, based on how it is used. Since `α` is an argument to `List`,
it must be a `Type`, since `List` expects a `Type` as its argument.

This facility means we don't always have to write explicit type annotations
everywhere, although explicit type annotations can still be quite useful
as documentation, so we will continue to use them much of the time.
::::

::::hide
```
(* ###################################################### *)
(** *** Type Annotation Inference *)

(** Let's write the definition of [repeat] again, but this time we
    won't specify the types of any of the arguments. Will Rocq still
    accept it? *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** TERSE: *** *)
(** Indeed it will. Let's see what type Rocq has assigned to [repeat']... *)

Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

(** TERSE: Rocq has used _type inference_ to deduce the proper types
    for [X], [x], and [count]. *)
(** FULL: It has exactly the same type as [repeat]. Rocq was able to
    use _type inference_ to deduce what the types of [X], [x], and
    [count] must be, based on how they are used. For example, since
    [X] is used as an argument to [cons], it must be a [Type], since
    [cons] expects a [Type] as its first argument; matching [count]
    with [0] and [S] means it must be a [nat]; and so on.

    This powerful facility means we don't always have to write
    explicit type annotations everywhere, although explicit type
    annotations can still be quite useful as documentation and sanity
    checks, so we will continue to use them much of the time. *)
(* HIDE: (BCP '19) Deleted, for streamlining: "You should try to find
    a balance in your own code between too many type
    annotations (which can clutter and distract) and too few (which
    can sometimes require readers to perform complex type inference in
    their heads in order to understand your code)."

```
::::

### Type Argument Synthesis

::::full
To use a polymorphic function, we need to pass it one or
more types in addition to its other arguments. For example, the
recursive call in the body of the `myRepeat` function above must
pass along the type `α`. But since the second argument to
`myRepeat` is an element of `α`, it seems entirely obvious that the
first argument can only be `α` -- why should we have to write it
explicitly?

Fortunately, Lean permits us to avoid this kind of redundancy. In
place of any type argument we can write a "hole" `_`, which can be
read as "Please try to figure out for yourself what belongs here."
More precisely, when Lean encounters a `_`, it will attempt to
_unify_ all locally available information -- the type of the
function being applied, the types of the other arguments, and the
type expected by the context in which the application appears --
to determine what concrete type should replace the `_`.

Using holes, the `repeat` function can be written like this:
::::

::::terse
Supplying every type _argument_ is also boring, but Lean
can usually infer them:
::::

```lean
def myRepeat'' (α : Type) (x : α) (count : Nat) : List α :=
  match count with
  | 0        => []
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
  | 0        => []
  | count' + 1 => x :: myRepeat''' x count'
```

::::full
(Note that we didn't even have to provide a type argument to the
recursive call to myRepeat'''. Indeed, it would be invalid to
provide one, because Lean is not expecting it.)
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
`def mynil := []` -- error: type not known
We can fix this with an explicit type annotation:

We can use the `@` prefix to supply the type
argument explicitly. The `@` makes all implicit arguments
of a function explicit:

:::dev "Jonathan Chan (ionathanch)" NOW
Didn't we alredy use this feature back on lines 121/126?
:::

```lean
#check (@List.nil : {α : Type} → List α)

def mynil' := @List.nil Nat
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

(A) `List Nat`

(B) `List Bool`

(C) `Bool`

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

(A) `List Nat`

(B) `List Bool`

(C) `Bool`

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

(A) `List Nat`

(B) `List Bool`

(C) `Bool`

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

(A) `List Nat`

(B) `List (List Nat)`

(C) `List Bool`

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

(A) `List Nat`

(B) `List (List Nat)`

(C) `List Bool`

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

(A) `List Nat`

(B) `List (List Nat)`

(C) `List Bool`

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

(A) `List Nat`

(B) `List (List Nat)`

(C) `List Bool`

(D) No type can be assigned
::::

:::quizSolution
(C)
:::

::::::full
:::::exercise (rating := 2) (name := "mumble_grumble") (manual := true)
Consider the following two inductively defined types.

```lean
namespace MumbleGrumble

inductive Mumble : Type where
  | a : Mumble
  | b (x : Mumble) (y : Nat) : Mumble
  | c : Mumble

inductive Grumble (X: Type) : Type where
  | d (m : Mumble) : Grumble X
  | e (x : X) : Grumble X
```

Which of the following are well-typed elements of `Grumble X` for
some type `X`?  (Add YES or NO to each line.)
  - `Grumble.d (Grumble.b Grumble.a 5)`
  - `@Grumble.d Mumble (Mumble.b Mumble.a 5)`
  - `@Grumble.d Bool (Mumble.b Mumble.a 5)`
  - `@Grumble.e Bool true`
  - `@Grumble.e Mumble (Mumble.b Mumble.c 0)`
  - `@Grumble.e Bool (Mumble.b Mumble.c 0)`
  - `Mumble.c`

:::solution
```
   YES - [Grumble.d (Grumble.b Grumble.a 5)]
YES - [@Grumble.d Mumble (Mumble.b Mumble.a 5)]
YES - [@Grumble.d Bool (Mumble.b Mumble.a 5)]
YES - [@Grumble.e Bool true]
YES - [@Grumble.e Mumble (Mumble.b Mumble.c 0)]
NO  - [@Grumble.e Bool (Mumble.b Mumble.c 0)]
NO  - [Mumble.c]
```
:::

```lean
end MumbleGrumble
```
:::::

::::::

### Exercises

```lean
def List.rev {α:Type} (l:List α) : List α :=
  match l with
  | .nil => .nil
  | .cons h t => rev t ++ (.cons h .nil)

theorem rev_nil α : ([] : List α).rev = [] := by rfl

theorem rev_cons α h (t : List α) : (h :: t).rev = t.rev ++ [h] := by rfl
```

:::::exercise (rating := 2) (name := "poly_exercises")
Here are a few simple exercises, just like ones in the `Lists`
chapter, for practice with polymorphism. Complete the proofs below.
You will likely find useful the following lemmas about append and length
from Lean's standard library:

   `List.nil_append {α} (as : List α) : [] ++ as = as`
   `List.cons_append {α} {a : α} {as bs : List α} : a :: as ++ bs = a :: (as ++ bs)`

:::instructors
(Maybe outdated after the switch to Lean?)
There's a little inconsistency between this definition
and the standard library one: in the library, the type argument is
implicit. :-( I (BCP) have chosen to leave things inconsistent to
avoid having to explain about implicit arguments to theorems, which
wouldn't make sense at this point.
:::

```lean
theorem app_nil_r {α : Type} : ∀ (l : List α),
    l ++ [] = l := by
  solution!
    intro l; induction l
    case nil => rw [List.nil_append]
    case cons h t ih =>
     rw [List.cons_append, ih]

theorem app_assoc {α : Type} : ∀ (l m n : List α),
    l ++ m ++ n = l ++ (m ++ n) := by
  solution!
    intro l m n; induction l
    case nil => rw [List.nil_append, List.nil_append]
    case cons h t ih =>
     dsimp [List.cons_append]
     rw [ih]

theorem app_length {α : Type} : ∀ (l1 l2 : List α),
    (l1 ++ l2).length = l1.length + l2.length := by
  solution!
    intro l1 l2; induction l1
    case nil => dsimp [List.nil_append, app_nil_r]; rw [Nat.zero_add]
    case cons h t ih =>
     dsimp [List.cons_append, List.length_cons]
     rw [Nat.succ_add, ih]
```

:::gradeTheorem "0.5" "app_nil_r"
:::

:::gradeTheorem 1 "app_assoc"
:::

:::gradeTheorem "0.5" "app_length"
:::
:::::

:::::exercise (rating := 2) (name := "more_poly_exercises")
Here are some slightly more interesting ones...

```lean
theorem rev_app_distr {α : Type} : ∀ (l1 l2 : List α),
    (l1 ++ l2).rev = l2.rev ++ l1.rev := by
  solution!
    intro l1 l2; induction l1
    case nil =>
     dsimp [List.nil_append]
     rw [rev_nil, app_nil_r]
    case cons h t ih =>
     dsimp [List.cons_append]
     rw [rev_cons, rev_cons, ih, app_assoc]

theorem rev_involutive {α : Type} : ∀ (l : List α),
    l.rev.rev = l := by
  solution!
    intro l; induction l
    case nil =>
     rw [rev_nil, rev_nil]
    case cons h t ih =>
     rw [rev_cons, rev_app_distr, ih, rev_cons, rev_nil]
     dsimp only [List.nil_append, List.cons_append]
```

:::gradeTheorem 1 "rev_app_distr"
:::

:::gradeTheorem 1 "rev_involutive"
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

Lean's built-in product type `Prod` provides a `Prod.mk` constructor,
and `fst` and `snd` functions for accessing the first and second components
of the pair. It also has special syntax for creating products:

```lean
#check (1, true)  /- (1, true) : Nat × Bool -/
#check (1, true).fst  /- access first component -/
#check (1, true).snd  /- access second component -/
```

You can also use `.1` instead of `.fst` and `.2` instead of `.snd`

```lean
#check (1, true).1  /- access first component -/
#check (1, true).2  /- access second component -/

example : (3, 5).1 = 3 := by rfl
example : (3, 5).2 = 5 := by rfl
```

The notation `α × β` is syntactic sugar for `Prod α β`.

:::dev "Benjamin Pierce (bcpierce00)"
Do we need to tell them how to type it in vscode?  (If yes, then should we be doing this for every notation when it is introduced? (If yes, we should record this decision in the Claude prompt that we use for checking nitpicky regressions like this, creating and documenting it if it doesn't already exist.))
:::

::::full
It is easy at first to get `(x, y)` and `α × β` confused.
Remember that `(x, y)` is a _value_ built from two other values,
while `α × β` is a _type_ built from two other types. If `x` has
type `α` and `y` has type `β`, then `(x, y)` has type `α × β`.
::::

::::terse
Be careful not to get `(x, y)` and `α × β` confused!
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
def zip {α : Type} {β : Type} (lx : List α) (ly : List β) : List (α × β) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: zip tx ty

theorem zip_nil_r α β ly : zip [] ly = ([] : List (α × β)) := by rfl

theorem zip_nil_l α β lx : zip lx [] = ([] : List (α × β)) := by
   cases lx
   . rfl
   . rfl

theorem zip_cons α β lx ly (x : α) (y : β) :
   zip (x :: lx) (y :: ly) = (x, y) :: zip lx ly := by rfl
```

::::::full
:::::exercise (rating := 1) (name := "zip_checks")
Try answering the following questions on paper and
checking your answers in Lean:
- What is the type of `zip` (i.e., what does `#check @zip`
  print?)
- What does

```display
#eval zip [1, 2] [false, false, true, true]
```

print?
:::::

:::::exercise (rating := 2) (name := "split")
The function `unzip` is the right inverse of `zip`: it takes a
list of pairs and returns a pair of lists.

Fill in the definition of `unzip` below. Make sure it passes the
given unit test, and you can prove the simplification lemmas about it

```lean
def unzip {α : Type} {β : Type} (l : List (α × β)) : List α × List β := solution!(
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    let (lx, ly) := unzip t
    (x :: lx, y :: ly))

theorem unzip_nil α β : unzip [] = (([], []) : List α × List β) := solution!(by rfl)

theorem unzip_cons_fst α β l (x : α) (y : β) :
   (unzip ((x, y) :: l)).fst = x :: (unzip l).fst := solution!(by dsimp [unzip])

theorem unzip_cons_snd α β l (x : α) (y : β) :
   (unzip ((x, y) :: l)).snd = y :: (unzip l).snd := solution!(by dsimp [unzip])

example : unzip [(1, false), (2, false)] = ([1, 2], [false, false]) := solution!(by rfl)
```

:::gradeTheorem 1 "split"
:::

:::gradeTheorem 1 "test_split"
:::
:::::

::::::

## Polymorphic Options

:::dev "Benjamin Pierce (bcpierce00)"
Did we literally see `Option Nat` or was it spelled some other way?
:::

::::full
Our last polymorphic type for now is _polymorphic options_.
Lean's standard library provides `Option α`, with constructors
`none` and `some x`. (We already saw `Option Nat` in the
previous chapter.)  Let's briefly look at the definition:

inductive Option (α : Type) : Type where
   | none : Option α
   | some (x : α) : Option α
::::

:::slidebreak
:::

::::full
We can now rewrite the `nthError` function so that it works
with any type of list.
::::

```lean
def nthError {α : Type} (l : List α) (n : Nat) : Option α :=
  match l with
  | [] => none
  | a :: l' => match n with
    | 0 => some a
    | n' + 1 => nthError l' n'
```

test_nth_error1

```lean
example : nthError [4, 5, 6, 7] 0 = some 4 := by rfl
example : nthError [[1], [2]] 1 = some [2] := by rfl
example : nthError [true] 2 = none := by rfl
```

::::::full
:::::exercise (rating := 1) (name := "hd_error_poly")
Complete the definition of a polymorphic version of the
`hd_error` function from the last chapter. Be sure that it
passes the unit tests below.

```lean
def hdError {α : Type} (l : List α) : Option α := solution!(
  match l with
  | [] => none
  | a :: _ => some a)

#check hdError  /- hdError : {α : Type} → List α → Option α -/

theorem hd_error_nil α : hdError ([] : List α) = none := solution!(by rfl)

theorem hd_error_cons α (h : α) t : hdError (h :: t) = some h := solution!(by rfl)

example : hdError [1, 2] = some 1 := solution!(by rfl)
```

:::gradeTheorem "0.5" "test_hd_error1"
:::

test_hd_error2

```lean
example : hdError [[1], [2]] = some [1] := solution!(by rfl)
```

:::gradeTheorem "0.5" "test_hd_error2"
:::
:::::

::::::

# Functions as Data

::::full
Like most modern programming languages -- especially other
"functional" languages, including OCaml, Haskell, Racket, Scala,
Clojure, etc. -- Lean treats functions as first-class citizens,
allowing them to be passed as arguments to other functions,
returned as results, stored in data structures, etc.
::::

:::dev
HIDE: Robert Rand: The terse version could really use words
here. (Or drop the section break and rename this one to
"Higher-Order Functions"
:::

## Higher-Order Functions

::::full
Functions that manipulate other functions are often called
_higher-order_ functions. Here's a simple one:
::::

::::terse
Functions in Lean are _first class_.
::::

```lean
abbrev doit3times {α : Type} (f : α → α) (n : α) : α :=
  f (f (f n))
```

::::full
The argument `f` here is itself a function (from `α` to
`α`); the body of `doit3times` applies `f` three times to some
value `n`.
::::

```lean
#check @doit3times  /- @doit3times : {α : Type} → (α → α) → α → α -/

example : doit3times minustwo 9 = 3 := by rfl

example : doit3times not true = false := by rfl
```

## Filter

:::instructors
We've tried to be careful with terminology in the rest
of the notes: "(boolean) predicate" for boolean functions and
"property" for propositions indexed by one parameter.
:::

::::full
Here is a more useful higher-order function, taking a list
of `α`s and a _predicate_ on `α` (a function from `α` to `Bool`)
and "filtering" the list to yield a new list containing just
those elements for which the predicate returns `true`.
::::

```lean
def filter {α : Type} (test : α → Bool) (l : List α) : List α :=
  match l with
  | [] => []
  | h :: t =>
    bif test h then h :: filter test t
    else filter test t
```

::::full
For example, if we apply `filter` to the predicate `Nat.even`
and a list of numbers, it returns a list containing just the
even members.
::::

```lean
example : filter even [1, 2, 3, 4] = [2, 4] := by rfl
```

:::slidebreak
:::

```lean
abbrev lengthIs1 {α : Type} (l : List α) : Bool :=
  l.length == 1

example : filter lengthIs1
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by dsimp [filter, lengthIs1]

theorem filter_nil {α : Type} {test : α → Bool} : filter test [] = [] := by rfl

theorem filter_cons_success {α : Type} {test : α → Bool} h t :
   test h -> filter test (h :: t) = h :: filter test t := by
   intro htest
   dsimp [filter]
   rw [htest]
   dsimp

theorem filter_cons_fail {α : Type} {test : α → Bool} h t :
   test h = false -> filter test (h :: t) = filter test t := by
   intro htest
   dsimp [filter]
   rw [htest]
   dsimp
```

:::slidebreak
:::

:::dev PotentialImprovement
This material would sink in better if it were made clearer
why map and filter and such were useful in the real world. Talk
about map/reduce, collection-oriented programming, etc. Esp in the
terse version.
:::

::::terse
The `filter` function (especially when combined with some
other functions we'll see later) enables a powerful
_wholemeal_ (or _collection-oriented_) programming style.
::::

::::full
We can use `filter` to give a concise version of the
`countoddmembers` function from the `Lists` chapter.
::::

```lean
abbrev countoddmembers' (l : List Nat) : Nat :=
  (filter odd l).length

example : countoddmembers' [1, 0, 3, 1, 4, 5] = 4 := by rfl
example : countoddmembers' [0, 2, 4] = 0 := by rfl
example : countoddmembers' [] = 0 := by rfl
```

## Anonymous Functions

:::dev
HIDE: Why not show them `fix` here?  It's not that complicated and
it fills out the story. At least as a little optional section.
BAY: I'm not convinced it's "not that complicated" for people who
have never seen much functional programming before. I think adding
a discussion of fix could easily take 20 minutes of class time.
BCP: Yes, this doesn't belong in lecture, probably. But it might
still be useful as an optional section for people to read.
(2013: Now that we've created the idea of "advanced" sections, this
seems like a nice candidate.)
:::

::::full
It is arguably a little sad, in the example just above, to
be forced to define the function `lengthIs1` and give it a name
just to be able to pass it as an argument to `filter`, since we
will probably never use it again. Indeed, when using higher-order
functions, we _often_ want to pass as arguments "one-off"
functions that we will never use again; having to give each of
these functions a name would be tedious.

Fortunately, there is a better way. We can construct a function
"on the fly" without declaring it at the top level or giving it a
name. Lean provides two syntaxes for anonymous functions:

- `fun n => n * n` -- traditional lambda syntax
- `(· * ·)` -- "term with holes" syntax, where `·` marks arguments
::::

::::terse
Functions can be constructed "on the fly" without giving
them names.
::::

```lean
example : doit3times (fun n => n * n) 2 = 256 := by rfl
```

The expression `fun n => n * n` can be read as "the function
that, given a number `n`, yields `n * n`."

Lean also supports a shorter notation using `·` as a placeholder
for the argument:

```lean
example : doit3times (· + 1) 0 = 3 := by rfl
```

::::full
Here is the `filter` example, rewritten to use an anonymous
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
Use `filter` (instead of a recursive `def`) to write a Lean function
`filterEvenGt7` that takes a list of natural numbers as input
and returns a list of just those that are even and greater than 7.

```lean
abbrev filterEvenGt7 (l : List Nat) : List Nat := solution!(
  filter (fun n => even n && n > 7) l)

example : filterEvenGt7 [1, 2, 6, 9, 10, 3, 12, 8] = [10, 12, 8] := solution!(by rfl)

example : filterEvenGt7 [5, 2, 6, 19, 129] = [] := solution!(by rfl)
```

:::gradeTheorem 1 "test_filter_even_gt7_1"
:::

:::gradeTheorem 1 "test_filter_even_gt7_2"
:::
:::::

:::::exercise (rating := 3) (name := "partition")
Use `filter` to write a Lean function `partition` that, given a
type `α`, a predicate of type `α → Bool` and a `List α`, should
return a pair of lists. The first member of the pair is the sublist
of the original list containing the elements that satisfy the test,
and the second is the sublist containing those that fail the test.
The order of elements in the two sublists should be the same as
their order in the original list.

```lean
abbrev partition {α : Type} (test : α → Bool) (l : List α) : List α × List α := solution!(
  (filter test l, filter (!test ·) l))

example : partition (· % 2 != 0) [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) := solution!(by rfl)
example : partition (fun _ => false) [5, 9, 0] = ([], [5, 9, 0]) := solution!(by rfl)
```

:::gradeTheorem 1 "partition"
:::

:::gradeTheorem 1 "test_partition1"
:::

:::gradeTheorem 1 "test_partition2"
:::
:::::

::::::

## Map

::::full
Another handy higher-order function is called `map`.
::::

```lean
def map {α : Type} {β : Type} (f : α → β) (l : List α) : List β :=
  match l with
  | [] => []
  | h :: t => f h :: map f t
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
the same, since `map` takes _two_ type arguments, `α` and `β`; it
can thus be applied to a list of numbers and a function from
numbers to booleans to yield a list of booleans:
::::

```lean
example : map odd [2, 1, 2, 5] = [false, true, false, true] := by rfl
```

::::full
It can even be applied to a list of numbers and
a function from numbers to _lists_ of booleans to
yield a _list of lists_ of booleans:
::::

```lean
example : map (fun n => [even n, odd n]) [2, 1, 2, 5]
  = [[true, false], [false, true], [true, false], [false, true]] := by rfl
```

::::quiz
Recall the definition of `map`:

```display
def map (f : α → β) (l : List α) : List β :=
  match l with
  | [] => []
  | h :: t => f h :: map f t
```

What is the type of `@map`?

(A) `{α β : Type} → α → β → List α → List β`

(B) `α → β → List α → List β`

(C) `{α β : Type} → (α → β) → List α → List β`

(D) `{α : Type} → (α → α) → List α → List α`
::::

:::slidebreak
:::

:::slidebreak
:::

::::full
Exercises
::::

```lean
theorem map_nil {α : Type} {β : Type} (f : α → β) : map f [] = [] := by rfl

theorem map_cons {α : Type} {β : Type} (f : α → β) h t : map f (h :: t) = f h :: map f t := by rfl
```

::::::full
:::::exercise (rating := 3) (name := "map_rev")
Show that `map` and `reverse` commute. (Hint: You may need to
define an auxiliary lemma.)
QUIETSOLUTION

```lean
theorem map_app {α : Type} {β : Type} : ∀ (f : α → β) (l l' : List α),
    map f (l ++ l') = map f l ++ map f l' := by
  intro f l l'
  induction l
  case nil => rw [map_nil, List.nil_append, List.nil_append]
  case cons h t ih =>
   rw [List.cons_append, map_cons, map_cons, ih, List.cons_append]

-- /QUIETSOLUTION

theorem map_rev {α : Type} {β : Type} : ∀ (f : α → β) (l : List α),
    map f l.rev = (map f l).rev := by
  solution!
    intro f l
    induction l
    case nil =>
     rw [rev_nil, map_nil, rev_nil]
    case cons h t ih =>
     rw [rev_cons, map_cons, map_app, rev_cons, ih, map_cons, map_nil]
```

:::gradeTheorem 3 "map_rev"
:::
:::::

:::::exercise (rating := 2) (name := "flat_map")
The function `map` maps a `List α` to a `List β` using a function
of type `α → β`. We can define a similar function, `flatMap`,
which maps a `List α` to a `List β` using a function `f` of type
`α → List β`. Your definition should work by 'flattening' the
results of `f`, like so:

```display
flatMap (fun n => [n, n + 1, n + 2]) [1, 5, 10]
  = [1, 2, 3, 5, 6, 7, 10, 11, 12]
```

```lean
def flatMap {α : Type} {β : Type} (f : α → List β) (l : List α) : List β := solution!(
  match l with
  | [] => []
  | h :: t => f h ++ flatMap f t)

example : flatMap (fun n => [n, n, n]) [1, 5, 4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4] := solution!(by rfl)
```

:::gradeTheorem 1 "flatMap"
:::

:::gradeTheorem 1 "test_flat_map1"
:::
:::::

```lean
theorem flatMap_nil {α : Type} {β : Type} (f : α → List β) : flatMap f [] = [] :=
   solution!(by rfl)

theorem flatMap_cons {α : Type} {β : Type} (f : α → List β) h t :
   flatMap f (h :: t) = f h ++ flatMap f t := solution!(by rfl)
```
::::::

Lists are not the only inductive type for which `map` makes sense.
Here is a `map` for the `Option` type:

```lean
def optionMap {α : Type} {β : Type} (f : α → β) (x? : Option α) : Option β :=
  match x? with
  | none => none
  | some x => some (f x)
```

::::::full
:::::exercise (rating := 2) (name := "implicit_args")
The definitions and uses of `filter` and `map` use implicit
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
  | h :: t => f h (fold f t b)
```

::::terse
This is the "reduce" in map/reduce...
::::

:::slidebreak
:::

::::full
Intuitively, the behavior of the `fold` operation is to
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

theorem fold_nil {α : Type} {β : Type} (f : α → β → β) (b : β) : fold f [] b = b := by rfl

theorem fold_cons {α : Type} {β : Type} (f : α → β → β) h t (b : β) :
   fold f (h :: t) b = f h (fold f t b) := by rfl
```

::::quiz
Here is the definition of `fold` again:

```display
def fold (f : α → β → β) (l : List α) (b : β) : β :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)
```

What is the type of `@fold`?

(A) `{α β : Type} → (α → β → β) → List α → β → β`

(B) `α → β → (α → β → β) → List α → β → β`

(C) `{α β : Type} → α → β → β → List α → β → β`

(D) `α → β → α → β → β → List α → β → β`
::::

::::quiz
What does `fold (· + ·) [1, 2, 3, 4] 0` simplify to?

(A) `[1, 2, 3, 4]`

(B) `0`

(C) `10`

(D) `[3, 7, 0]`
::::

::::::full
:::::exercise (rating := 1) (name := "fold_types_different") (manual := true)
Observe that the type of `fold` is parameterized by _two_ type
variables, `α` and `β`, and the parameter `f` is a binary operator
that takes an `α` and a `β` and returns a `β`. Example
`fold_example4` above shows one instance where it is useful for `α`
and `β` to be different. Can you think of any others?

SOLUTION
There are many. For example, we could use `fold` to count the
number of `true` elements in a list of booleans. Here `α` would
be `Bool` and `β` would be `Nat`.
/SOLUTION
:::::

::::::

## Functions That Construct Functions

::::full
Most of the higher-order functions we have talked about so
far take functions as arguments. Let's look at some examples that
involve _returning_ functions as the results of other functions.
To begin, here is a function that takes a value `x` (drawn from
some type `α`) and returns a function from `Nat` to `α` that
yields `x` whenever it is called, ignoring its `Nat` argument.
::::

::::terse
Here are two functions that _return_ functions as results.
::::

```lean
abbrev constfun {α : Type} (x : α) : Nat → α :=
  fun _ => x

abbrev ftrue := constfun true

example : ftrue 0 = true := by rfl

example : constfun 5 99 = 5 := by rfl
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

```lean
#check (Nat.add : Nat → Nat → Nat)

abbrev plus3 := Nat.add 3
#check (plus3 : Nat → Nat)

example : plus3 4 = 7 := by rfl
example : doit3times plus3 0 = 9 := by rfl
example : doit3times (Nat.add 3) 0 = 9 := by rfl
```

Similarly, we can write:

```lean
abbrev fold_plus : List Nat → Nat → Nat :=
  fold (· + ·)

#check (fold_plus : List Nat → Nat → Nat)
```

::::full
What's happening here is called _partial application_. In
Lean, the type constructor `→` is right-associative, meaning a
function type like `α → β → γ` is parsed like `α → (β → γ)`,
or "a function from `α` to a function from `β` to `γ`."

We can think of `fold` not as a three-argument function, but as a
one-argument function that:

1. Takes an argument `f` of type `α → β → β`
2. Returns a function of type `List α → β → β` that "remembers" `f`

When we write `fold (· + ·)`, we're giving `fold` its first argument,
`(· + ·)`, and getting back a specialized function that can sum up
the elements of any list of numbers. This new function still expects
two more arguments: a list and a starting value.
::::

# Additional Exercises

:::suppressPreviousHeaderWhenTerse
:::

::::::full
```lean
namespace Exercises
```

:::::exercise (rating := 2) (name := "fold_length")
Many common functions on lists can be implemented in terms of
`fold`. For example, here is an alternative definition of `length`:

```lean
abbrev foldLength {α : Type} (l : List α) : Nat :=
  fold (fun _ n => n + 1) l 0

example : foldLength [4, 7, 0] = 3 := by rfl
```

Prove the correctness of `foldLength`.

Hint: It may help to use `dsimp [foldLength, fold]` to unfold
the definition.

```lean
theorem fold_length_correct {α : Type} (l : List α) :
    foldLength l = l.length := by
  solution!
    induction l
    case nil =>
     dsimp only [foldLength]
     rw [fold_nil, List.length_nil]
    case cons h t ih =>
      dsimp only [foldLength] at *
      rw [List.length_cons, fold_cons, ih]
```

:::gradeTheorem 2 "Exercises.fold_length_correct"
:::
:::::

:::::exercise (rating := 3) (name := "fold_map") (manual := true)
We can also define `map` in terms of `fold`. Finish `foldMap`
below.

```lean
abbrev foldMap {α : Type} {β : Type} (f : α → β) (l : List α) : List β := solution!(
  fold (fun x l' => f x :: l') l [])
```

Write down a theorem `fold_map_correct` stating that `foldMap` is
correct, and prove it in Lean.

```lean
-- SOLUTION
/- fold_map_correct -/
theorem fold_map_correct {α : Type} {β : Type} (f : α → β) (l : List α) :
    foldMap f l = map f l := by
  induction l
  case nil => dsimp only [foldMap]; rw [fold_nil, map_nil]
  case cons h t ih =>
    dsimp only [foldMap] at *
    rw [fold_cons, map_cons, ih]
-- END SOLUTION
```

:::grade
`GRADE_MANUAL 3: fold_map`
:::
:::::

:::::exercise (rating := 2) (name := "currying") (level := Advanced)
The type `α → β → γ` can be read as describing functions that
take two arguments, one of type `α` and another of type `β`, and
return an output of type `γ`. Recall from our discussion
of partial application that this type is written `α → (β → γ)`
when fully parenthesized. That is, if we have `f : α → β → γ`,
and we give `f` an input of type `α`, it will give us as output
a function of type `β → γ`. If we then give that function an
input of type `β`, it will return an output of type `γ`. That
is, every function in Lean takes only one input, but some
functions return a function as output. This is precisely
what enables partial application, as we saw above with `plus3`.

By contrast, functions of type `α × β → γ` -- which when fully
parenthesized is written `(α × β) → γ` -- require their single
input to be a pair. Both arguments must be given at once; there
is no possibility of partial application.

It is possible to convert a function between these two types.
Converting from `α × β → γ` to `α → β → γ` is called
_currying_, in honor of the logician Haskell Curry. Converting
from `α → β → γ` to `α × β → γ` is called _uncurrying_.

We can define currying as follows:

```lean
abbrev prodCurry {α β γ : Type} (f : α × β → γ) (x : α) (y : β) : γ := f (x, y)
```

As an exercise, define its inverse, `prodUncurry`. Then prove
the theorems below to show that the two are really inverses.

```lean
abbrev prodUncurry {α β γ : Type} (f : α → β → γ) (p : α × β) : γ := solution!(
  f p.fst p.snd)
```

As a (trivial) example of the usefulness of currying, we can use it
to shorten one of the examples that we saw above:

```lean
example : map (Nat.add 3) [2, 0, 2] = [5, 3, 5] := by rfl
```

Thought exercise: before running the following commands, can you
calculate the types of `prodCurry` and `prodUncurry`?

```lean
#check @prodCurry
#check @prodUncurry
```

:::dev "Benjamin Pierce (bcpierce00)"
This is out of date...

HIDE: Maybe this is a good place to introduce the lack of
functional extensionality? Here, at the latest, the reader may have
started to wonder why the next two theorems, rather than claiming
the equality of functions, claim equalities for their values...
BCP 9/16: On reflection, I think this is not the place. It's an
advanced exercise, so not everybody will see it, and we do come
back to it in detail in a couple chapters.
:::

```lean
theorem uncurry_curry {α β γ : Type} (f : α → β → γ) (x : α) (y : β) :
    prodCurry (prodUncurry f) x y = f x y := by
  solution!
    rfl

theorem curry_uncurry {α β γ : Type} (f : α × β → γ) (p : α × β) :
    prodUncurry (prodCurry f) p = f p := by
  solution!
    rfl
```

:::gradeTheorem 1 "Exercises.uncurry_curry"
:::

:::gradeTheorem 1 "Exercises.curry_uncurry"
:::
:::::

:::dev BeforeNextRelease
This isn't quite the definition given above. (And the one
above is VASTLY easier to work with for the proof!)  We should
really fix this!
:::

:::::exercise (rating := 2) (name := "nth_error_informal") (level := Advanced) (manual := true)
Recall the definition of the `nthError` function:

```display
def nthError (l : List α) (n : Nat) : Option α :=
  match l with
  | [] => none
  | a :: l' => match n with
    | 0 => some a
    | n' + 1 => nthError l' n'
```

Write a careful informal proof of the following theorem:

```display
∀ (l : List α) (n : Nat), l.length = n → nthError l n = none
```

Make sure to state the induction hypothesis _explicitly_.

SOLUTION
Theorem: For all types `α`, lists `l`, and natural numbers `n`,
if `l.length = n` then `nthError l n = none`.

Proof: By induction on `l`. There are two cases to consider:

- If `l = []`, we must show `nthError [] n = none`. This follows
  immediately from the definition of `nthError`.

- Otherwise, `l = x :: l'` for some `x` and `l'`, and the
  induction hypothesis tells us that
  `l'.length = n' → nthError l' n' = none`, for any `n'`.

  Let `n` be the length of `l`. We must show that
  `nthError (x :: l') n = none`.

  But we know that `n = l.length = (x :: l').length = l'.length + 1`.
  So it's enough to show `nthError l' l'.length = none`, which
  follows directly from the induction hypothesis, picking `l'.length`
  for `n'`.
/SOLUTION

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

def CNat := (α : Type) → (α → α) → α → α
```

Let's see how to write some numbers with this notation. Iterating
a function once should be the same as just applying it. Thus:

```lean
def one : CNat :=
  fun (X : Type) (f : X → X) (x : X) => f x
```

Similarly, `two` should apply `f` twice to its argument:

```lean
def two : CNat :=
  fun (X : Type) (f : X → X) (x : X) => f (f x)
```

Defining `zero` is somewhat trickier: how can we "apply a function
zero times"?  The answer is actually simple: just return the
argument untouched.

```lean
def zero : CNat :=
  fun (X : Type) (_ : X → X) (x : X) => x
```

More generally, a number `n` can be written as
`fun X f x => f (f ... (f x) ...)`, with `n` occurrences of `f`.
Let's informally notate that as `fun X f x => f^n x`, with the
convention that `f^0 x` is just `x`. Note how the `doit3times`
function we've defined previously is actually just the Church
representation of 3.

```lean
def three : CNat := @doit3times
```

So `n X f x` represents "do it `n` times", where `n` is a Church
numeral and "it" means applying `f` starting with `x`.

Another way to think about the Church representation is that
function `f` represents the successor operation on `α`, and value
`x` represents the zero element of `α`. We could even rewrite
with those names to make it clearer:

```lean
def zero' : CNat :=
  fun (X : Type) (_ : X → X) (zero : X) => zero
def one' : CNat :=
  fun (X : Type) (succ : X → X) (zero : X) => succ zero
def two' : CNat :=
  fun (X : Type) (succ : X → X) (zero : X) => succ (succ zero)
```

If we passed in `Nat.succ` as `succ` and `0` as `zero`, we'd
even get the Peano naturals as a result:

```lean
example : zero Nat Nat.succ 0 = 0 := by rfl
example : one Nat Nat.succ 0 = 1 := by rfl
example : two Nat Nat.succ 0 = 2 := by rfl
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
  fun (X : Type) (f : X → X) (x : X) => f (n X f x))

example : scc zero = one := solution!(by rfl)
example : scc one = two := solution!(by rfl)
example : scc two = three := solution!(by rfl)
```

:::gradeTheorem 1 "Exercises.Church.scc_2"
:::

:::gradeTheorem 1 "Exercises.Church.scc_3"
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
  fun (X : Type) (f : X → X) (x : X) => n X f (m X f x))

example : plus zero one = one := solution!(by rfl)
example : plus two three = plus three two := solution!(by rfl)
example : plus (plus two two) three = plus one (plus three three) := solution!(by rfl)
```

:::gradeTheorem 1 "Exercises.Church.plus_1"
:::

:::gradeTheorem 1 "Exercises.Church.plus_2"
:::

:::gradeTheorem 1 "Exercises.Church.plus_3"
:::
:::::

:::::exercise (rating := 3) (name := "church_mult") (level := Advanced)
Define a function that computes the multiplication of two Church
numerals.

Hint: the "successor" argument to a Church numeral need not be
just `f`.

Warning: Lean will not let you pass `CNat` itself as the type `X`
 argument to a Church numeral; you will get a "sort mismatch"
 error between `Type 1` and `Type 2`. Don't worry too much
 about what this means right now, but know that
 this is Lean's way of preventing a paradox in
 which a type contains itself. So leave the type argument
 unchanged.

```lean
def mult (n m : CNat) : CNat := solution!(
  fun (X : Type) (f : X → X) (x : X) => n X (m X f) x)

example : mult one one = one := solution!(by rfl)
example : mult zero (plus three three) = zero := solution!(by rfl)
example : mult two three = plus three three := solution!(by rfl)
```

:::gradeTheorem 1 "Exercises.Church.mult_1"
:::

:::gradeTheorem 1 "Exercises.Church.mult_2"
:::

:::gradeTheorem 1 "Exercises.Church.mult_3"
:::
:::::

:::::exercise (rating := 3) (name := "church_exp") (level := Advanced)
Exponentiation:

Define a function that computes the exponentiation of two Church
numerals.

Hint: the type argument to a Church numeral need not just be `α`.
Finding the right type can be tricky.

```lean
def exp (n m : CNat) : CNat := solution!(
  fun (X : Type) (f : X → X) (x : X) => m (X → X) (n X) f x)

example : exp two two = plus two two := solution!(by rfl)
example : exp three zero = one := solution!(by rfl)
example : exp three two = plus (mult two (mult two two)) one := solution!(by rfl)
```

:::gradeTheorem 1 "Exercises.Church.exp_1"
:::

:::gradeTheorem 1 "Exercises.Church.exp_2"
:::

:::gradeTheorem 1 "Exercises.Church.exp_3"
:::
:::::

```lean
end Church
end Exercises
```
::::::
