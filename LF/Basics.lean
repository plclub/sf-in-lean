prelude
import SFLMeta

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Basics: Functional Programming in Lean" =>
%%%
tag := "Basics"
htmlSplit := .never
file := "Basics"
%%%


:::instructors
This file and Induction.lean each take about an hour to
get through in a not-too-rushed fashion (with questions, etc.).

(N.b. This estimate may need to be revised now that the chapter has been converted to Lean! Please edit this note to reflect your own experience teaching it.)

You may want to assign both files together as the homework for the
first week, depending on the level of the class.  Just Basics is
fairly light for many students, but in a mixed class there will
be people that struggle with some of it.

PRESENTATION ADVICE: Working with the .lean file directly in VS Code
is recommended for the first few lectures, so students see exactly
what's in the source file.

If you don't have Lean installed yet:
* Install Lean 4 through the VS Code extension.
* Start a new terminal session to pick up environment changes.
* Run `make`.
* Run `make serve`. Navigate to "http://localhost:8000/lf/student/html/" to start reading.
* Make a copy of "\_out/lf/student/lean" to start solving as if I were a student.
:::

This chapter introduces some of Lean's most essential features for writing functional programs
and proving things about how they behave.

# Introduction
::::full
The _functional style_ of programming is founded on simple
mathematical intuitions: A program is essentially a concrete
means for computing a mathematical function, which just maps
inputs to outputs. (Even programs with side effects like
reading and writing files or network packets can
be presented in this way, using ideas like
_monads_.) This connection between programs and
mathematical functions makes it possible to reason both precisely
and formally about a program's behavior, i.e., to _prove
properties_ about programs.

This functional style is one sense of the word "functional" in
"functional programming." The other sense is
that it emphasizes the use of functions as _first-class_ values —
i.e., values that can be passed as arguments to other functions,
returned as results, included in data structures, etc.
The recognition that functions can be treated as data gives rise to a
host of useful and powerful programming idioms.

Other common features of functional languages include _algebraic
data types_ and _pattern matching_, which make it easy to
construct and manipulate rich data structures, and _polymorphic
types_ supporting abstraction and code reuse.  Lean offers
all of these features, and we will see them often in this book.

The first part of this chapter introduces some key elements of
Lean's functional programming language.  The second part shows
how to use _tactics_ to prove properties about programs.
::::

# Data and Functions

:::terse
In Lean, we can build practically everything from first principles
using _inductive definitions_.
:::

::::full
Lean's set of primitives is extremely small.
For example, instead of providing the usual palette of _atomic
datatypes_ — booleans,
integers, strings, and so on — Lean's standard
library _defines_ them, along with an extensive collection of other common data structures —
lists, hash tables, etc., etc. It does so with a single
powerful and general mechanism: _inductive definitions_.
A type introduced with an inductive definition is called an _inductive type_, and the
word "inductive" hints at the use of mathematical induction
to reason about its values (as we will see in the
{ref "Induction"}[next chapter]).

To demonstrate how inductive definitions work and illustrate their
expressive power, we will start by defining most of the datatypes we
use in this course from scratch, rather than importing
the ones in the standard library. (We will later switch over to the library
versions, to take advantage of all the properties that have already been proved about them.)
::::

## Days of the Week (Enumerated Types)

:::terse
An inductive definition for an _enumerated type_:
:::

::::full
Let's start with a very simple example.  The following declaration tells
Lean to give a name to a set of data values, i.e., to define a _type_.
::::

```lean
inductive Day : Type where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
```

::::full
The new type is called {name}`Day`, and its members are `monday`,
`tuesday`, etc. These are also called the _constructors_
of the {name}`Day` type.
We often call this sort of inductive type an _enumerated type_
since the values belonging to the type are explicitly enumerated in its definition.

Having defined {name}`Day`, we can write Lean functions that operate on
days.
::::

:::slidebreak
:::

:::terse
A function on days:
:::

```lean
def nextWorkingDay (d : Day) : Day :=
  match d with
  | Day.monday    => Day.tuesday
  | Day.tuesday   => Day.wednesday
  | Day.wednesday => Day.thursday
  | Day.thursday  => Day.friday
  | Day.friday    => Day.monday
  | Day.saturday  => Day.monday
  | Day.sunday    => Day.monday
```

::::full
Note that the argument and result types of this function are
explicitly declared on its first line. As in most functional
programming languages, Lean can often figure out these types for
itself when they are not given explicitly — i.e., it can do _type
inference_ — but we'll generally include them to make reading
easier.

The `match` on the second line is Lean's keyword for _pattern matching_, the functional
programming way of examining and making decisions on data. To evaluate
`match d with...`, Lean will examine the structure of `d` to see which
case to execute; if `d` is `Day.monday`, for example, it will
evaluate the first case of the `match` statement; if `d` is
`Day.friday` it will evaluate the fifth case. (There is much more
to say about pattern matching! We'll introduce more of its features
as the need arises.)

You may notice that we _qualified_ `Day`'s constructors when using them,
writing {name}`Day.monday` instead of just `monday`, for example.
Lean places all constructors into a _namespace_ associated with their type,
and generally requires those constructors to be prefixed with their namespace when they are used, though
we will see later that this requirement can sometimes be relaxed.

If you ever need to know the type of _any_ pattern, object, or function,
you can hover over it with your mouse, either in VS Code or in the HTML version of the chapter.
::::

:::slidebreak
:::

:::terse
Evaluation:
:::

::::full
Having defined a function, we should check that it works on some
examples.  There are a few different ways to do this in
Lean.  One is to use the `#eval` command to evaluate a compound
expression involving `nextWorkingDay`.  (Lean's responses are shown
just below.)
::::

:::dev "Benjamin Pierce (bcpierce00)"
There is probably not time to fix this, but the way responses are displayed is confusing.  They
should be marked as responses in some more explicit way.
:::


```lean (name := nextWDay)
#eval nextWorkingDay Day.friday
```

```leanOutput nextWDay
Day.monday
```

```lean (name := nextNextWDay)
#eval nextWorkingDay (nextWorkingDay Day.saturday)
```

```leanOutput nextNextWDay
Day.tuesday
```

We can also record what we _expect_ the result of calling a function to be in the form of a Lean
`example`:

```lean
example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.tuesday := by
  rfl
```
:::dev "Benjamin Pierce (bcpierce00)"
Do we really *have* to follow the Lean convention of putting the `:= by` on the same line
as the theorem statement?  It's awful.,
:::

::::full
This declaration asserts that the second working day after `saturday` is `tuesday`.
Having made the assertion, we can also ask Lean to _verify_ it.
The `by rfl` can be read as "The assertion we've just made can be
proved by observing that both sides of the equality evaluate to
the same term."

Here, {tactic}`rfl` is pronounced "reflexivity," the principle that any value is
equal to itself. After evaluation, both sides of the equality are the same
value, so the assertion is true by reflexivity.
If we had made a different assertion, such as

```lean +error
example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.monday := by rfl
```

then Lean would not be able to verify it and would instead signal an
error.

(The `sf_expect_failure_in` annotation tells Lean that there is intended to be an error in
the following expression and it should not mark the whole file as broken.)
::::

::::terse
The {tactic}`rfl` tactic is used to observe that both sides of an equal sign evaluate to the same value.
::::

## Aside: Using the VS Code Lean Extension

:::suppressPreviousHeaderWhenTerse
:::

::::full
If you have not already done so, this would be an excellent moment
to fire up VS Code with the
[Lean Extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
and load this file, `Basics.lean`,
from the book's Lean sources.
Locate the above example and observe its result in the Lean InfoView panel.

This panel displays the results of commands like `#eval` (click on a particular `#eval` to see),
as well as the current goal state when working on proofs.
The InfoView content always follows your cursor.

You can command-click on a type or variable name to navigate to its definition.
Try this with the mention of `nextWorkingDay` in the above `#eval`.
:::dev "Benjamin Pierce (bcpierce00)"
Is it called command-click on Linux and Windows?
:::

You can also hover over expressions in the source code to see their types.
Try this with mentions of {name}`nextWorkingDay` and `Day.saturday` in the above `#eval`.
If you hover over the `#eval` command itself,
you will see the popup that contains its output (at the top).
Sometimes we show Lean's responses to commands in the text below them; by hovering over
the command you can check against that text.

Experiment with adding your own `#eval` commands to test other inputs.
Lean typechecks the file as you
edit it, so you can see the results of your changes immediately.
::::

## Booleans

::::full
Following the pattern of the days of the week above, we can
define the standard type `Bool` of booleans by enumerating its members `true`
and `false`.
We define our own `MyBool` to teach the concept of building booleans from
scratch. Our definition `MyBool` is equivalent to Lean's built-in {name}`Bool`,
which we'll switch to later.
::::

:::dev "Benjamin Pierce (bcpierce00)"
Why are our custom booleans called `MyBool` but our custom nats are called `Nat`?
:::


::::terse
Another familiar enumerated type; we'll switch to Lean's built-in `Bool` later:
::::

```lean
inductive MyBool : Type where
  | true
  | false
```

:::details
```lean -show
-- This is included to be able to format expressions involving these variables later
variable (b : MyBool) (n m : Nat)
set_option pp.fieldNotation false
```
:::

::::full
The next command opens the namespace associated with the {name}`MyBool` type,
so subsequent definitions will be part of the {name}`MyBool` namespace.
In Lean, functions on a type are typically defined in that type's namespace,
which avoids name clashes with functions of the same name elsewhere (e.g.,
functions on the built-in {name}`Bool` type). We give a full treatment of namespaces below.
::::

::::terse
This command opens the namespace associated with the {name}`MyBool` type:
::::

```lean
namespace MyBool
```

Functions over booleans can be defined in the same way as functions over days of the week.

```lean
def not (b : MyBool) : MyBool :=
  match b with
  | MyBool.true => MyBool.false
  | MyBool.false => MyBool.true
```

:::slidebreak
:::

```lean
def and (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | MyBool.true => b2
  | MyBool.false => MyBool.false

def or (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | MyBool.true => MyBool.true
  | MyBool.false => b2
```

::::full
The `and` and `or` definitions illustrate Lean's syntax for multi-argument
functions.  The corresponding multi-argument function-application syntax is
illustrated by the following tests, which effectively constitute a
complete specification — a truth table — for the `or` function:
::::

:::terse
Note the syntax for defining multi-argument functions (`and` and `or`).
:::

```lean
example : or MyBool.true  MyBool.false = MyBool.true  := by rfl
example : or MyBool.false MyBool.false = MyBool.false := by rfl
example : or MyBool.false MyBool.true  = MyBool.true  := by rfl
example : or MyBool.true  MyBool.true  = MyBool.true  := by rfl
```

Lean also allows us to define symbolic notations for these functions.

```lean
local prefix:40 (priority := high) "!" => not
local infixl:35 (priority := high) " && " => and
local infixl:30 (priority := high) " || " => or
```

```lean
example :
    (MyBool.false || MyBool.false || MyBool.true) = MyBool.true := by rfl

example : (!MyBool.false) = MyBool.true := by rfl
```

::::full
The technical details of how these symbolic notations work are not something you need to understand until quite a bit later in your Lean journey.  We'll mark these details -- and similar material later on -- with `THESE DETAILS CAN BE SKIPPED` comments in `.lean` files and with collapsed text segments in the HTML presentation. Click on the triangle in the HTML if you want to have a peek, or just move on to the following material.

:::details
Lean has a very flexible notation system. Operators like `||` and `&&`
are defined with specified precedence and associativity. For example, the `infixl` directive above states that
`&&` is an infix operator, has precedence 35, and is left-associative, while `||` is also infix and left-associative and has precedence 30. This means that `MyBool.true || MyBool.false && MyBool.false` is parsed as `MyBool.true || (MyBool.false && MyBool.false)`.

Custom notations are defined using the `notation`, `infixl`,
`infixr`, `prefix`, and `postfix` commands, some of which we will see
(again, in skippable sections) later on.
:::
::::

:::slidebreak
:::

::::exercise (rating := 1) (name := "nand")
The {tactic}`sorry` keyword is a placeholder for an incomplete proof or
definition.  We use it in exercises to indicate the parts that we're
leaving for you — i.e., your job is to replace {tactic}`sorry` with real
definitions and proofs.

Remove {tactic}`sorry` below and complete the definition of the
function.  The function should return {name}`MyBool.true` if either or both of
its inputs are {name}`MyBool.false`. Make sure that the `example` assertions
below can be verified by Lean.

```lean
def nand (b1 : MyBool) (b2 : MyBool) : MyBool
  := solution!(match b1 with
  | MyBool.true => not b2
  | MyBool.false => MyBool.true)

theorem nand_test1 : nand MyBool.true  MyBool.false = MyBool.true  := solution!(by rfl)
theorem nand_test2 : nand MyBool.false MyBool.false = MyBool.true  := solution!(by rfl)
theorem nand_test3 : nand MyBool.false MyBool.true  = MyBool.true  := solution!(by rfl)
theorem nand_test4 : nand MyBool.true  MyBool.true  = MyBool.false := solution!(by rfl)
```

:::autogradedHole nand
:::

:::gradeTheorem "0.25" nand_test1 nand_test2 nand_test3 nand_test4
:::

:::dev
TODO: `nand` needs `@[autogradedHole]`
:::
::::

:::::terse
Going forward, most exercises will be omitted from the "terse" version of the notes used
in lecture. The "full" version (used on-line and for homeworks) contains both longer
explanations and all the exercises.
:::::

:::::full
::::exercise (rating := 1) (name := "and3")
Do the same for the `and3` function below. This function should
return `true` when all of its inputs are `true`, and `false`
otherwise.

```lean
def and3 (b1 : MyBool) (b2 : MyBool) (b3 : MyBool) : MyBool
  := solution!(and b1 (and b2 b3))

theorem and3_test1 : and3 MyBool.true  MyBool.true  MyBool.true  = MyBool.true  := solution!(by rfl)
theorem and3_test2 : and3 MyBool.false MyBool.true  MyBool.true  = MyBool.false := solution!(by rfl)
theorem and3_test3 : and3 MyBool.true  MyBool.false MyBool.true  = MyBool.false := solution!(by rfl)
theorem and3_test4 : and3 MyBool.true  MyBool.true  MyBool.false = MyBool.false := solution!(by rfl)
```

:::autogradedHole and3
:::

:::gradeTheorem "0.25" and3_test1 and3_test2 and3_test3 and3_test4
:::
::::
:::::

:::slidebreak
:::

# A First Taste of Proofs

::::full
Now that we've defined some basic functions on booleans, let's see how to
_prove_ some simple properties of those functions. Here is a simple rule
about `&&`:

- for any boolean value {lean}`b`, {lean}`(MyBool.true && b) = b`

This is an example of a _proposition_, a logical claim that we can try to prove.
It says that {lean}`MyBool.true && b` is equal to {lean}`b` for every {name}`MyBool` `b`.

How do we write this proposition in Lean?  Like this:

- `theorem true_and : ∀ (b : MyBool), (MyBool.true && b) = b`
:::dev "Benjamin Pierce (bcpierce00)"
Could it (and the one above) be displayed instead of bulleted?
:::

The keyword `theorem` indicates that we are stating (and eventually proving)
a proposition; the text after the first `:` is the proposition we want to prove.

You'll notice that this proposition looks a lot like the informal one we began with,
with some additional symbols in front.
The `∀` symbol, pronounced "forall",
is a _universal quantifier_: it "quantifies" the variable {lean}`b` that appears
in the proposition. Quantifying a variable with a `∀` means that the proposition
applies to all possible values of its type; we annotate {lean}`b`
with the type {lean}`MyBool` to signify that
the proposition holds for all {lean}`b`s of type {lean}`MyBool`.

Now that we've stated the theorem we'd like to prove, let's see the proof.
::::

::::terse
Let's prove something simple about booleans:
::::

```lean
theorem true_and : ∀ (b : MyBool), (MyBool.true && b) = b := by
  intro b
  rfl
```

::::full
What does this mean?

First the `by` keyword signals
that what follows is a sequence of _tactics_.
The `intro b` and {tactic}`rfl` after the `by`
are examples of tactics. If you hover over a tactic's name, Lean shows
its documentation.

Tactics manipulate the _proof state_, which you can see the in the Lean InfoView panel.
The proof state is divided by the symbol ⊢, pronounced _turnstile_. The part
before it is the _context_, and the part after it is
the _goal_. The context records what we know
at some given point in the proof; the goal is what we are trying to prove
at that point.

Each tactic manipulates the goal, the context, or both, to get things
into a configuration that is closer to being "solved". A tactic can also
_close_ (solve) the current goal, finishing its proof.

Let's walk through the example above with this terminology in mind.
::::

::::terse
And now let's see it in a bit more detail:
::::

```lean
theorem true_and_explained : ∀ (b : MyBool), (MyBool.true && b) = b := by
  /- Move your cursor (click) here to see the initial proof state in
     the InfoView. If you are viewing the book online,
     instead click on the white button after `by`.
     The context (before the ⊢) is empty.
     The goal is `∀ (b : MyBool), (MyBool.true && b) = b`. -/
  intro b
  /- Now click here (or the white button after `intro b`)
     to see the new proof state that results from the
     tactic. Notice how `intro b` has changed the _context_: it now
     contains `b : MyBool`.

    The `intro` tactic is used to name variables quantified by a `∀`.
    Since we are trying to prove a property of all `MyBools`, we
    proceed by introducing an unknown `MyBool` `b` and prove
    the property holds for `b`, regardless of what it is.  Informally,
    this move can be read, "We want to prove <some property> for all
    `MyBool`s `b`. So suppose `b` is some arbitrary `MyBool`...
    <and then go on to prove the property for this particular `b`>..."
    Since `b` was chosen arbitrarily, we've now proved the property
    for all `b`.

    A proof of a theorem beginning with a ∀ will typically start with
    an `intro`.

    As in the `example`s above, we can use the `rfl` tactic,
    which closes goals about equality where both sides are equal to
    one another according to the principle of reflexivity. Now,
    inspecting our goal will show that it is `(MyBool.true && b) = b`,
    which may not appear to be equal to itself. However, the tactic
    _evaluates_ both sides of the equality before comparing them. In
    this case, if we look at the definition of `and`, we can see that,
    when its first argument is `MyBool.true`, the result is its second
    argument. So the two terms `MyBool.true && b` and `b` are in fact
    equal because one evaluates to the other.
  -/
  rfl
  /- The proof is now done! The Lean InfoView tells us there are "No goals". -/
```

::::full
It's also important to point out that, as with languages like Python and Haskell,
Lean is _whitespace-sensitive_. That is, the indentation in proofs is important and changing
it can change the meaning of the proof, usually causing the proof to break. Suppose we had
instead written the following:

```lean +error (name := indent)
theorem true_and_wrong : ∀ (b : MyBool), (MyBool.true && b) = b := by
  intro b
    rfl
```

To see the error message in the Lean file,
change `sf_expect_failure_in` to `sf_expect_failure_in?` temporarily.
You should see the following message.

```leanOutput indent
Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce

b : MyBool
⊢ (true && b) = b
```

Lean complains because the {tactic}`rfl` is not at the same level of indentation as the `{tactic}intro b`,
so it does not recognize these two tactics as being sequential in the way they should be.

In general, sequential tactics applied to the same goal must be on subsequent lines at the same
level of indentation or separated on the same line by a `;` like so:

```lean
theorem true_and' : ∀ (b : MyBool), (MyBool.true && b) = b := by
  intro b; rfl
```
::::

:::::full
::::exercise (rating := 1) (name := "false_or_exercise")
Here's a simple proof for you to try.
Remove {tactic}`sorry` and fill in the proof.

```lean
theorem false_or : ∀ (b : MyBool), (MyBool.false || b) = b := by
  solution!
    intro b
    rfl
```

:::gradeTheorem 1 false_or
:::
::::

While in this book we often use {tactic}`sorry` as a placeholder for you to
replace with an actual proof, in general, {tactic}`sorry` tells Lean that we want to skip trying
to prove a theorem and just accept it as a given.  This can be useful for developing longer proofs.

Be careful, though: every time you say {tactic}`sorry` you are leaving
a door open for total nonsense to enter Lean's safe, formally
checked world!

```lean -keep
theorem really_bad : MyBool.true = MyBool.false := by sorry
```

The facts we've seen so far about booleans are quite simple, so the tactics we need to
prove them are also quite simple. Over the course of this book we are going to
introduce new tactics and proof techniques gradually, enriching the propositions we can prove along the way.

Now that we've seen how to define our own booleans and prove some basic
properties about them, let's switch to Lean's built-in {name}`Bool` type, which has the same structure
but comes with a lot of useful functions and lemmas.
:::::

::::terse
Now we'll switch to Lean's definition of booleans.
::::

```lean
end MyBool
```

## Aside: Unicode in Lean

:::suppressPreviousHeaderWhenTerse
:::

::::full
Note that `∀` and `⊢` are unicode symbols, not a simple ASCII characters. The
Lean Extension for VS Code provides convenient shortcuts for
entering such symbols. Simply type `\` (backslash) followed by the
name of the symbol (the "shortcode"), and the extension will automatically replace it
with the actual symbol. For example, typing `\all` or `\forall` will produce `∀`
and `\->` or `\to` will produce `→`. To find out what backslash sequence
produces a unicode symbol that you can see on the screen, just hover
over it. To see all of the Unicode shortcodes, open the Command Palette
(Ctrl+Shift+P on Windows/Linux or Cmd+Shift+P on macOS), type
"Lean 4: Show Unicode Input Abbreviations", and press Enter.
::::

## Types

::::full
Every expression in Lean has a type describing what sort of value it computes.
The `#check` command asks Lean to print the type of an expression.
::::

::::terse
We can use `#check` to check the type of an expression:
::::

```lean (name := true)
#check Bool.true
```

```leanOutput true
Bool.true : Bool
```

::::full
If the expression after `#check` is followed by a colon and a type,
Lean will verify that the type of the expression
matches the given type and signal an error if not.
::::

```lean (name := true2)
#check (Bool.true : Bool)
#check (Bool.not Bool.true : Bool)
```

```leanOutput true2
true : Bool
```

```leanOutput true2
!true : Bool
```

::::full
Functions like {name}`Bool.not` are themselves ordinary values, just like {name}`Bool.true`
and {name}`Bool.false`.  Their types are called _function types_, and they are
written with arrows.
::::

```lean
#check Bool.not
```

::::full
The type of {name}`Bool.not`, written {lean}`Bool → Bool` and pronounced "`Bool`
arrow `Bool`," can be read, "Given an input of type {name}`Bool`, this
function produces an output of type {name}`Bool`." Similarly, the type of
{name}`Bool.and`, written {lean}`Bool → Bool → Bool`, can be read, "Given two inputs,
each of type {name}`Bool`, this function produces an output of type
{name}`Bool`."
::::

## New Types from Old

::::full
The enumerated types we have seen so far are so-named because
their definitions explicitly enumerate a finite set of
elements: their constructors. Here is a more interesting
inductive type definition, `Color`, where one of the constructors
takes an argument:
::::

:::terse
A more interesting type definition:
:::

```lean
inductive RGB : Type where
  | red
  | green
  | blue

inductive Color : Type where
  | black
  | white
  | primary (p : RGB)
```

:::full
_Constructor expressions_ are formed by applying a constructor
to zero or more other constructors or constructor expressions,
obeying the declared number and types of the constructor arguments.
E.g., these are valid constructor expressions...

- {name}`RGB.red`
- {name}`Bool.true`
- {name}`Color.primary` {name}`RGB.red`

...but these are not:

- `RGB.red Color.primary`
- `Bool.true RGB.red`
- `Color.primary (Color.primary RGB.red)`
:::

:::slidebreak
:::

We can define functions on colors using pattern matching, just as
we did for {name}`Day` and {name}`Bool`.

```lean
def monochrome (c : Color) : Bool :=
  match c with
  | Color.black => Bool.true
  | Color.white => Bool.true
  | Color.primary p => Bool.false
```

:::full
Since the `primary` constructor takes an argument, a pattern
that matches `.primary` should include either a variable, a constant
of appropriate type, or `_`. Lean's convention is to use a `_` (called a
_wildcard_) when the argument to a constructor doesn't matter. In
the definition of `monochrome`, we don't use the argument to `Color.primary`, so
a more idiomatic definition would be:
:::

:::terse
We can use a _wildcard_ pattern `_` to match something we don't care about:
:::

```lean
def monochrome' (c : Color) : Bool :=
  match c with
  | Color.black => Bool.true
  | Color.white => Bool.true
  | Color.primary _ => Bool.false
```

We can use a constant argument to {name}`Color.primary` to match a specific primary color:

```lean
def isRed (c : Color) : Bool :=
  match c with
  | Color.black => Bool.false
  | Color.white => Bool.false
  | Color.primary RGB.red => Bool.true
  | Color.primary _ => Bool.false
```

:::ignore
```lean -show
variable (c : Color) (r : RGB)
```
:::

:::full
The pattern {lean}`Color.primary RGB.red` will match only when {lean}`c` is
{name}`Color.primary` with the argument {name}`RGB.red`. The pattern {lean}`Color.primary _` matches
every {name}`Color.primary` color, but because patterns are checked in
order, the {lean}`Color.primary _` case will never be reached if the color is {name}`RGB.red`.
:::

An alternative way to write the same function would be to explicitly
nest match statements:

```lean
def isRed' (c : Color) : Bool :=
  match c with
  | Color.black => Bool.false
  | Color.white => Bool.false
  | Color.primary r =>
    match r with
    | RGB.red => Bool.true
    | _ => Bool.false
```

This {name}`isRed'` function produces the same result as
{name}`isRed` but illustrates the _use_ of a pattern variable.

:::::full
The {lean}`Color.primary r` pattern stores the {name}`RGB` argument into variable {lean}`r`,
and then pattern matches on that argument to produce the final
result.

::::exercise (rating := 1) (name := "is_weekend")
Define a function that takes a `Day` and returns true if the day is
a weekend, and false otherwise.

Then, fill in right-hand sides of the `example` blocks below.
If you've done both correctly, the blocks will produce no errors
and contain no {tactic}`sorry`.

Hint: You could write this function by pattern matching on
each possible day of the week, or you could try to
come up with a shorter solution...

```lean
def is_weekend (d : Day) : Bool
  := solution!
    (match d with
    | Day.saturday => true
    | Day.sunday => true
    | _ => false
    )

theorem is_weekend_test1 : is_weekend Day.sunday = true := solution!(by rfl)
theorem is_weekend_test2 : is_weekend Day.friday = false := solution!(by rfl)
```

:::autogradedHole is_weekend
:::

:::gradeTheorem "0.5" is_weekend_test1 is_weekend_test2
:::
::::

::::exercise (rating := 1) (name := "isInversion")
Define a function that takes two colors and returns `true` if
the second color is an _inversion_ of the first, and false otherwise.

Inversion is defined by cases:
Black is an inversion of white, and vice versa.
Red is an inversion of blue, and vice versa.
Green is not an inversion of anything.

As before, write the right-hand sides of the `example` blocks
to ensure they pass with no {tactic}`sorry`.

```lean
def isInversion (c1 c2 : Color) : Bool
  := solution!
    (match c1, c2 with
    | Color.black, Color.white => Bool.true
    | Color.white, Color.black => Bool.true
    | Color.primary RGB.red, Color.primary RGB.blue => Bool.true
    | Color.primary RGB.blue, Color.primary RGB.red => Bool.true
    | _, _ => false
    )


theorem isInversion_test1 : isInversion Color.black Color.white = true := solution!(by rfl)
theorem isInversion_test2 : isInversion Color.white Color.black = Bool.true := solution!(by rfl)
theorem isInversion_test3 : isInversion (Color.primary RGB.red) (Color.primary RGB.blue) = Bool.true :=
  solution!(by rfl)
theorem isInversion_test4 : isInversion (Color.primary RGB.green) (Color.primary RGB.red) = Bool.false :=
  solution!(by rfl)
```

:::autogradedHole isInversion
:::

:::gradeTheorem "0.25" isInversion_test1 isInversion_test2 isInversion_test3 isInversion_test4
:::
::::
:::::

## Namespaces

::::full
We have been using Lean's system of _namespaces_ for managing potentially
conflicting names. Now we have seen enough that we can look more closely at
how it works.

When we enclose a collection of declarations in `namespace X ... end X`,
references from outside this collection to names declared within
it are referred to with prefix `X.`, like `X.foo` instead of just `foo`.
In large Lean developments, namespaces are
used to organize definitions and theorems the same way
modules are used in other programming languages.
::::

:::terse
`namespace` declarations create separate namespaces.
:::

```lean (name := ns1)
def myFoo : Bool := true
namespace Playground
def myFoo : RGB := RGB.blue
end Playground

#check myFoo
#check Playground.myFoo
```

```leanOutput ns1
myFoo : Bool
```

```leanOutput ns1
Playground.myFoo : RGB
```

:::full
Namespaces can be re-opened as often as you like to add new definitions and access old ones.
When inside a `namespace`, definitions from that namespace can be referenced
without prefixes.
:::

```lean (name := ns2)
namespace Playground
-- this refers to the `myFoo` we defined in the `Playground` namespace previously
def myBar : RGB := myFoo
end Playground

#check Playground.myBar
```

```leanOutput ns2
Playground.myBar : RGB
```

::::full
When a type is created, a `namespace` with the same name as that type is implicitly created as well;
definitions on that type are available inside that `namespace` without a prefix. In the example
below, we can use the `blue` constructor without qualification because
we are inside the {name}`RGB` `namespace`, which is the same as `blue`'s type.
::::

::::terse
Type definitions implicitly create namespaces.
::::


```lean
namespace RGB
def myBlue : RGB := blue
end RGB
```

Top-level definitions can also be prefixed by a namespace,
which opens the namespace temporarily for the body of the definition.

```lean (name := rgb_1)
--- this works, because the definition is qualified by `RGB.`
def RGB.myOtherBlue : RGB := myBlue

#check RGB.myBlue
#check RGB.myOtherBlue
```

```leanOutput rgb_1
RGB.myBlue : RGB
```

```leanOutput rgb_1
RGB.myOtherBlue : RGB
```

```lean +error (name := rgb_2)
-- this doesn't work; the identifier is undefined
#check myBlue
```

```leanOutput rgb_2
Unknown identifier `myBlue`
```

::::full
Similarly, we could rewrite the definition of `nextWorkingDay`
from above inside the `Day` namespace like so:
::::

```lean
def Day.nextWorkingDay' (d : Day) : Day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
```

:::full
We can also use `open` to bring the definitions of a namespace into
the current scope; after that, we can refer to any of the namespace's
definitions without a prefix.
:::

:::terse
`open` brings definitions from a namespace into scope.
:::

```lean (name := ns_1)
namespace MyNamespace
def myDef : Bool := Bool.true
end MyNamespace

open MyNamespace

#check myDef
```

```leanOutput ns_1
MyNamespace.myDef : Bool
```

If we only want to bring _some_, rather than all, of the definitions
of a namespace into the current scope, we can use the `open (...)` form:

```lean (name := ns_2)
namespace MyOtherNamespace
def myHiddenDef : Bool := Bool.true
def myVisibleDef : Bool := Bool.false
end MyOtherNamespace

open MyOtherNamespace (myVisibleDef)

-- `myVisibleDef` is now usable without qualification:
#check myVisibleDef
```

```leanOutput ns_2
MyOtherNamespace.myVisibleDef : Bool
```

But `myHiddenDef`, which we did not `open`, still needs its full name;
using it unqualified is an error:

```lean +error (name := ns_3)
#check myHiddenDef
```

```leanOutput ns_3
Unknown identifier `myHiddenDef`
```

::::full
In fact, this is exactly what Lean does with the standard {name}`Bool` type by default.
Since it is such an important
part of many proofs and programs, Lean implicitly `open`s many of `Bool`s functions and
constructors. Accordingly, we can use constructors like {name}`true` and {name}`false` and functions
like {name}`not` without qualifying them with {name}`Bool`.
::::

::::terse
Names from the `Bool` `namespace` are `open`ed and thus available without qualification.
::::

```lean (name := tt)
#check Bool.true
#check true
```

```leanOutput tt
Bool.true : Bool
```

```leanOutput tt
Bool.true : Bool
```


::::full
Finally, Lean can often automatically figure out which namespace a qualified name lives in,
saving us the need to explicitly specify it every time we use the name. Instead of
the fully qualified style (e.g., {name}`Day.monday`), we can opt for an implicitly qualified style,
writing just `.monday`.

When we do this, Lean tries to resolve the `.monday` name by seeing what its expected type is
and inferring which namespace it must be from based on that type. If there is only one such
namespace (i.e., if it is unambiguous which constructor we're referring to), then it will
automatically resolve to the expected value.

So, for example, we can also write {name}`nextWorkingDay` as follows, using the shorter
style for both the value being matched upon and the value being returned:
::::

::::terse
Lean can often guess which qualified name we mean if we don't supply it explicitly:
::::

```lean
def nextWorkingDay' (d : Day) : Day :=
  match d with
  | .monday    => .tuesday
  | .tuesday   => .wednesday
  | .wednesday => .thursday
  | .thursday  => .friday
  | .friday    => .monday
  | .saturday  => .monday
  | .sunday    => .monday
```

::::full
In the function above, both the type of `d` and the return type of the function are declared
to be {name}`Day`s. When we use the `.monday` style in the function body, Lean can figure
out that we must mean `Day.monday`. However, in the example below, Lean can't figure out
which version of `.true` we mean, since it could either be {name}`Bool.true` or {name}`MyBool.true`.
In this case, it will raise an error:
::::

::::terse
Here, Lean can't figure out which version of `.true` we mean.
::::

```lean +error (name := am)
#check .true
```

```leanOutput am
Invalid dotted identifier notation: The expected type of `.true` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `true`
  [apply] `MyBool.true`
  [apply] `Lake.Toml.true`
  [apply] `Lean.LBool.true`
  [apply] `Std.Do.ExceptConds.true`
  [apply] `Lean.Meta.Grind.Filter.true`
```

Here, though, because {name}`not` is a function that takes a {name}`Bool` argument, Lean knows that
`.true` must here be a {name}`Bool`:

```lean (name := bt)
#check (Bool.not .true)
```

```leanOutput bt
!true : Bool
```

:::::full

::::exercise (rating := 1) (name := "custom_namespace_checks")
Predict the output of each of the statements below.
Do you think their results would change depending on which namespace
the statements appear in? How?

```
#check .black -- Write your prediction here.
#check Color.black -- Write your prediction here.
#check RGB -- Write your prediction here.
#check Playground.myFoo -- Write your prediction here.
```

Once you have written your predictions, copy the lines from the comment into
an active section of the book to evaluate them.
::::

:::grade
```
GRADE_MANUAL 1: custom_namespace_checks
```
:::
:::::

## Constructors with Multiple Parameters (Tuple Types)

```lean
namespace Playground
```

::::full
A single constructor of an inductive type can have multiple parameters,
not just zero or one. This feature is one way to define _tuple types_ in Lean,
which are like record/struct types but their fields are accessed by their _position_
in patterns rather than by a specific (field) _name_.

As an example, consider representing the four bits in
a nibble (half a byte). We first define a datatype `Bit` that
resembles {name}`Bool` (using the constructors `b1` and `b0` for the two
possible bit values) and then define the datatype `Nibble`, which is
a tuple of four bits.
::::

:::terse
A Nibble is half a byte — four bits.
:::

```lean (name := nb1)
inductive Bit : Type where
  | b1
  | b0

inductive Nibble : Type where
  | bits (x0 x1 x2 x3 : Bit)

#check Nibble.bits .b1 .b0 .b1 .b0
```

```leanOutput nb1
Nibble.bits Bit.b1 Bit.b0 Bit.b1 Bit.b0 : Nibble
```

::::full
The `bits` constructor illustrates a feature of multi-parameter
declarations, both for constructors and for functions: Instead
of writing `(x0 : Bit) (x1 : Bit) ...` we write `(x0 x1 ... : Bit)`
since all of the variables have the same type. We could have done
the same with the function definition {name}`MyBool.or` above, writing
`or (b1 b2 : MyBool)` rather than `or (b1 : MyBool) (b2 : MyBool)`.

The `bits` constructor acts as a wrapper for its contents.
Unwrapping is done by pattern matching, as in the `allZero` function
below, which tests a Nibble to see if all its bits are `b0`.
::::

:::slidebreak
:::

:::terse
We can deconstruct a Nibble by pattern-matching.
:::

```lean
def allZero (nb : Nibble) : Bool :=
  match nb with
  | .bits .b0 .b0 .b0 .b0 => true
  | .bits _   _   _   _   => false

example : allZero (.bits .b1 .b0 .b1 .b0) = false := by rfl
example : allZero (.bits .b0 .b0 .b0 .b0) = true  := by rfl

end Playground
```

### Structures

:::suppressPreviousHeaderWhenTerse
:::

:::full
When defining an inductive type with just one constructor, we can instead use a `structure`:

```lean
structure NibbleStruct : Type where
  x0 : Playground.Bit
  x1 : Playground.Bit
  x2 : Playground.Bit
  x3 : Playground.Bit
```

Rather than construct this as `.bits .b0 .b0 .b0 .b0`, we construct it as:

```lean (name := nbs)
#check NibbleStruct.mk .b0 .b0 .b0 .b0
```

```leanOutput nbs
{ x0 := Playground.Bit.b0, x1 := Playground.Bit.b0, x2 := Playground.Bit.b0, x3 := Playground.Bit.b0 } : NibbleStruct
```

The `.mk` constructor is created for us.
Structures are more commonly constructed by assigning values to their _fields_.
Each field name is paired with its value using `:=`:


```lean
def zeroNibble : NibbleStruct := {
    x0 := .b0
    x1 := .b0
    x2 := .b0
    x3 := .b0
  }
```

Since the result type is declared to be {name}`NibbleStruct`, Lean knows
which structure and fields we mean. Unlike {name}`NibbleStruct.mk`,
this construction syntax doesn't depend on the order of fields.

Now that we have seen how to construct a structure from scratch —
how do we "update" an existing structure, or in other words, construct a new structure
while reusing some old fields?

```lean
def setFirstTwoBits (old : NibbleStruct)
    (newX0 : Playground.Bit)
    (newX1 : Playground.Bit) : NibbleStruct :=
  { old with x0 := newX0, x1 := newX1 }
```

The expression `{ old with ... }` constructs a new {name}`NibbleStruct` whose `x0` and `x1`
have the given value and whose other fields are copied from `old`.
Keep in mind that `old` was not modified — we constructed a new structure
starting from the old one.

```lean
def makeNibbleStruct (x0 x1 x2 x3 : Playground.Bit) : NibbleStruct :=
  { x0, x1, x2, x3 }
```

When a field and the variable supplying its value have the same name,
Lean lets us write just the name.
Thus `{ x0, x1, x2, x3 }` is a shorthand for `{ x0 := x0, x1 := x1, x2 := x2, x3 := x3 }`.
This is called _field abbreviation_.

:::

## Natural Numbers

::::full
We put this portion of the chapter in a namespace so that our definition of
numbers does not interfere with the one from the standard library. Our definition
matches the standard one, which we will use in the rest of the book.
::::

```lean
namespace NatPlayground
```

::::full
All the types we have defined so far — both enumerated types
such as {name}`Day`, {name}`MyBool`, and {name}`Playground.Bit` and tuple types such as
{name}`Playground.Nibble` built from them — are finite. The natural numbers, on
the other hand, are an infinite set, so we'll need to use a
slightly richer form of inductive type declaration to represent
them: _recursive_ inductive types.

While the need for recursion is unequivocal, there are many recursively-defined
representations of numbers to choose from. You are
certainly familiar with decimal notation (base 10), using the digits
0 through 9, for example, to form the number 123. You have likely
also encountered hexadecimal notation (base 16), in which the same
number is represented as 7B, or octal (base 8), where it is 173, or
binary (base 2), where it is 1111011. Using an enumerated type to
represent digits, we could use any of these as our representation of
natural numbers.

There are circumstances in which each of these choices is useful.
The binary representation is valuable in computer hardware because
the digits can be represented with just two distinct voltage levels,
resulting in simple circuitry.

Here we choose an even simpler _unary_ (base 1) representation, for
the sake of streamlining proofs. As a Lean datatype, it uses two
constructors. The `zero` constructor represents the number zero. The
`succ` constructor can be applied to the representation of the
natural number {lean}`n`, yielding the representation of {lean}`n + 1`, where
`succ` stands for "successor." The number {lean}`n` is then represented by
`n` applications of `succ` to `zero`.

Here is the complete datatype definition:
::::

:::terse
For simplicity in proofs, we choose a _unary_ representation of natural numbers.
:::

```lean
inductive Nat : Type where
  | zero
  | succ (n : Nat)
```

:::full
With a little Lean magic, we can also arrange that
ordinary numerals such as 0, 1, and 2 will be interpreted as values of our new {name}`Nat` type
whenever this is sensible in context.
The technical details are not important.
:::

:::details "Library Nat to SFL Nat coercion"
```lean
def ofNat : _root_.Nat → Nat
  | .zero => .zero
  | .succ n => .succ (ofNat n)

instance (n : _root_.Nat) : OfNat Nat n := ⟨ofNat n⟩
attribute [pp_nodot] Nat.succ
```
:::

:::full
We'll define some shorthands for numbers, putting them in the `Nat` namespace
so we don't need to use `.` notation everywhere.
:::

:::terse
Eventually we'll swap to Lean's definition of natural numbers, which is very similar to this.
:::

```lean
namespace Nat

def one   : Nat := succ zero
def two   : Nat := succ one
def three : Nat := succ two
def four  : Nat := succ three
```

We can also write functions on {name}`Nat`.

```lean
def pred (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ n' => n'

def minusTwo (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ (zero) => zero
  | succ (succ n') => n'

#eval minusTwo four
```

::::full
Look the types of {name}`succ`, {name}`pred`, and {name}`minusTwo`:

```lean (name := nat1)
#check (succ)
#check (pred)
#check (minusTwo)
```

```leanOutput nat1
succ : Nat → Nat
```

```leanOutput nat1
pred : Nat → Nat
```

```leanOutput nat1
minusTwo : Nat → Nat
```

These are all things that can be applied to a number to yield a
number. However, there is a fundamental difference between
{name}`succ` and the other two: functions like {name}`pred` and
{name}`minusTwo` are defined by giving _computation rules_ — e.g.,
the definition of {name}`pred` says that {lean}`pred (succ (succ zero))`
can be simplified to {lean}`succ zero` — while the definition of
{name}`succ` has no such behavior attached. Although it is like a
function in the sense that it can be applied to an argument, it does
not _do_ anything at all! It is just the way we write down numbers.
::::

:::slidebreak
:::

::::full
We can also define _recursive functions_: functions that call themselves
repeatedly down to a base case. Recursion is the essence of repeated
computation in functional programming; in this course, we will make
extensive use of recursive functions.

We first define a simple recursive function, `even`, then a slightly
more sophisticated recursive function `add`.
::::

:::terse
Here are some recursive functions on natural numbers:
:::

```lean
def even (n : Nat) : Bool :=
  match n with
  | zero => true
  | succ (zero) => false
  | succ (succ n') => even n'

example : even one = false := by rfl
example : even four = true := by rfl
```

:::slidebreak
:::

We could define `odd` by a similar recursive declaration, but
here is a simpler way:

```lean
def odd (n : Nat) : Bool :=
  not (even n)

example : odd one = true := by rfl
example : odd four = false := by rfl
```

:::slidebreak
:::

This function takes multiple parameters, recursing on the second:

```lean
def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m')
```

```lean (name :=  three_1)
#eval add one two -- succ (succ (succ zero)) -- aka, three!
```

```leanOutput three_1
NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.zero)))
```

We can also define infix notation for our {name}`add` functions.

```lean
scoped infixl:65 " + " => add
```

```lean (name := three_2)
#eval one + two -- succ (succ (succ zero)) -- aka, three again.
```

```leanOutput three_2
NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.zero)))
```

# Proof by Rewriting

## Proving properties about functions in Lean

::::full
Being recursive on a {name}`Nat` and returning {name}`Nat` as well,
{name}`add` is the first example of a more sophisticated class of functions.
In this chapter and beyond, we will _prove_ properties
about recursive functions like `add` over inductive datatypes
like {name}`Nat`, using _simplification rules_, also known as _characterizing lemmas_, about their behavior.

Here is a simplification rule about {name}`add`:

- {lean}`n + zero = n`

In Lean, this rule looks like this:
::::

::::terse
We can prove properties of recursive functions like {name}`add`:
::::

```lean
theorem add_zero : ∀ n : Nat, n + zero = n := by
  intro n
  rfl
```

```lean (name := add_zero)
#check add_zero
```

```leanOutput add_zero
NatPlayground.Nat.add_zero (n : Nat) : n + zero = n
```

Using our simplification rule {name}`add_zero`, we can carry out a simple proof
about natural numbers.

```lean
theorem add_zero_zero : ∀ n : Nat, n + zero + zero = n := by
  intro n
  rewrite [add_zero]
  rewrite [add_zero]
  rfl
```
::::full
We'll walk through this proof in the next section.
::::

## Proof state and tactics

:::suppressPreviousHeaderWhenTerse
:::

::::full
The {tactic}`rewrite` tactic in the proof of {name}`add_zero_zero` is used
to transform the goal of the proof according to an equality.
The {name}`add_zero` in brackets is an _argument_ to the {tactic}`rewrite` tactic.

Let's walk through the theorem again in detail.
::::

::::terse
Here is the previous proof in more detail:
::::

```lean
theorem add_zero_zero_explained : ∀  n : Nat, n + zero + zero = n := by
  intro n
  /- After introducing `n`, our goal is `n + zero + zero = n`.
     What can we do to simplify this expression? If you hover
     your cursor over the `add_zero` in the rewrite below, you
     can see its type: `n + zero = n`. So, we can use that
     rewrite rule to transform an appearance of `n + zero`
     in the goal to `n`. -/
  rewrite [add_zero]
  /- Now click here to see the new proof state that results
     from the tactic. Notice how `n + zero + zero` changes to
     `n + zero` in the goal. -/
  rewrite [add_zero]
  /- Again the goal changes, from `n + zero` to `n`. Now the
     proof state is an equality with both sides equal, so it
     can be closed by the tactic `rfl`. -/
  rfl
  /- The proof is now done! The Lean InfoView tells us there are
     "No goals". -/
```

Give this proof a try (it's similar):

```lean
theorem add_zero_zero_zero : ∀ n : Nat, n + zero + zero + zero = n := by
  workinclass!
    intro n
    rewrite [add_zero]
    rewrite [add_zero]
    rewrite [add_zero]
    rfl
```

## The {tactic}`rewrite` tactic

:::suppressPreviousHeaderWhenTerse
:::

::::full
The {tactic}`rewrite` tactic tells Lean to rewrite (part of) a goal or
hypothesis based on a rule (or rules), given in square brackets.
For example, given the rule {name}`add_zero`,
which states that {lean}`n + zero` is equal to {lean}`n` for any {lean}`n`, we can replace
any {lean}`n + zero` in our proof with {lean}`n` via `rewrite [add_zero]`.
::::

## The {tactic}`rfl` tactic

:::suppressPreviousHeaderWhenTerse
:::

::::full
The {tactic}`rfl` tactic closes a goal of the shape `a = a`, for any `a`. It
checks that both sides of the equality are _definitionally equal_ —
that is, that they reduce to the same term. (So, in particular, a
term is always definitionally equal to itself.)
::::

::::terse
The {tactic}`rfl` closes a goal that looks like `a = a`, reducing both sides of the equality in
the process.
::::

## A New {lean}`add` Rule

::::full
Here is another fundamental rule about addition:

{lean}`n + (succ m) = succ (n + m)`.

This is the rule we need to push {name}`succ` around.

Here it is in Lean:
::::

::::terse
Here's another rule we can use for {name}`add`:
::::

```lean
theorem add_succ : ∀ n m : Nat, n + (succ m) = succ (n + m) := by
  intro n m
  rfl
```

Now, let's use {name}`add_succ` in a proof:

```lean
theorem add_one (n : Nat) : n + (succ zero) = succ n + zero := by
  rewrite [add_succ]
  rewrite [add_zero]
  rewrite [add_zero]
  rfl
```

::::full
We recommend stepping through these proofs in VS Code —
that is, moving past each tactic with your cursor to see how it
changes the proof state and hovering over each argument to {tactic}`rewrite` to see its type.
::::

## Irreducibility, Rewriting, and Proof Engineering

::::full
Lean, like any other programming language, has conventions and best practices
for writing good software. Lean takes inspiration from object-oriented programming
in favoring the use of _encapsulation_. In OOP, it is considered poor style to expose
the fields of an object in its interface; instead, those fields should only be
accessible by an object's methods (like getters and setters).
Doing so hides the object's definition, so that, if its fields or implementation
ever change, the interface it exposes to the outside world remains the same.
In simple examples such conventions may seem trivial or even silly; in complex codebases,
it is the only way to maintain crucial invariants that prevent a system from becoming unmaintainable.

The same principle applies to programs and proofs in Lean.
In idiomatic Lean, it is considered poor style to _unfold_ — that is, "peek
through" — definitions by using {tactic}`rfl` to implicitly simplify expressions
that aren't syntactically identical. If you take a look at the proofs of
{name}`add_zero` and {name}`add_succ` above, you will notice this is exactly what we did
when we used the {tactic}`rfl` tactic.
:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement
Readers might wonder why there isn't a tactic that's just like `rfl` but insists on syntactic identity, if that's what is considered good style...
:::


Fortunately, the foundational theorems {name}`add_zero` and {name}`add_succ` provide a
characterization of the behavior of {name}`add` that makes using {tactic}`rfl` to simplify
expressions unnecessary; instead, we can rewrite by these theorems anywhere we want to describe
how {name}`add` evaluates.
In real-world Lean developments, the style of writing proofs using
simplification rules is both standard and expected.

For the next few chapters, we mark definitions with `attribute [irreducible]` to prevent this peeking,
also called *definitional equality abuse* (*defeq abuse*, for short).
We place this attribute after the proofs of {name}`add_zero` and {name}`add_succ`,
and can then rewrite by these theorems anywhere we want to describe
how {name}`add` evaluates.
We use `attribute [irreducible]` for now to enforce the style of
using simplification rules, so that it is natural to you moving forward.
We will relax this discipline in later chapters.
::::

::::terse
After proving the theorems that characterize a definition,
we mark the definition `irreducible` to require rewriting by them instead
of using {tactic}`rfl`.
::::

```lean
attribute [irreducible] add
```

These simplification rules also follow a particular pattern. Let's look again at the
definition of {name}`add`, without the `+` notation for maximum clarity:

```lean
namespace AddPlayground

def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m')

theorem add_zero : ∀ (n : Nat), add n zero = n := by
  intro n
  rfl

theorem add_succ : ∀ (n m : Nat), add n (succ m) = succ (add n m) := by
  intro n m
  rfl

end AddPlayground
```

::::full
Each of {name}`add_zero` and {name}`add_succ` correspond to one branch of the `match`
statement defining {name}`add` and describe how the evaluation of {name}`add` proceeds
in that case. The {name}`add_zero` theorem describes how {lean}`add n zero` evaluates,
while {name}`add_succ` describes (symbolically) how {lean}`add n (succ m)` evaluates.

These are instances of a general pattern: each definition
operating over enumerated types like {name}`Nat`, {name}`Bool`, {name}`Day`, or {name}`Color`
needs a simplification rule for each branch of control flow through
the function.

So, for example, we need two simplification rules for the definition of `pred`:
::::

::::terse
Each branch of a definition's control flow gets one simplification rule. Here are the two for
{name}`pred`:
::::

```lean
theorem pred_zero : pred zero = zero := by rfl
theorem pred_succ n : pred (succ n) = n := by rfl
```

Now that we have defined and proved {name}`pred`'s simplification rules,
we can mark it `irreducible`, to enforce rewriting by these lemmas.

```lean
attribute [irreducible] pred
```

Similarly, for each of the three branches of the definition of {name}`even`,
we need one simplification rule:

```lean
theorem even_zero : even zero = true := rfl
theorem even_one : even (succ zero) = false := rfl
theorem even_succ_succ n : even (succ (succ n)) = even n := rfl

attribute [irreducible] even odd
```

::::full
In the remainder of this textbook, we will pair definitions
with simplification rules. After proving these rules,
instead of using {tactic}`rfl` to peek through the definitions, we will {tactic}`rewrite`
using the rules.

Eventually, we will introduce a way to _automatically_ apply these simplification rules.
Real-world Lean developments use automation extensively, and you will learn to do so
gradually throughout this book.
For the moment it is important that you work through these early concepts
by hand, without automation.
By the time the more powerful tools are introduced,
you will have the foundational understanding to use them with precision and skill.
::::

::::terse
From here on, we pair each definition with its simplification rules and rewrite by those rules
rather than {tactic}`rfl`-ing through the definition.
::::

## Working with Numerals

We know from our definitions above that {name}`one` is just {lean}`succ zero`,
{name}`two` is {lean}`succ one`, and so on. We can write rules for these equalities too:

```lean
theorem one_eq_succ_zero : one = succ zero := by rfl
theorem two_eq_succ_one : two = succ one := by rfl
theorem three_eq_succ_two : three = succ two := by rfl
theorem four_eq_succ_three : four = succ three := by rfl
```

:::::full
We can rewrite with these rules to expand numerals into their definitions,
which allows us to use our {name}`add` rules.
Here's an example of how to start a proof this way.

::::exercise (rating := 1) (name := "mul_simpl_rules")

Finish the proof using the {name}`add` rules:

```lean
theorem one_plus_one_eq_two : one + one = two := by
  rewrite [one_eq_succ_zero]
  solution!
    rewrite [add_succ]
    rewrite [add_zero]
    rfl
```

Try the same for {lean}`two + two = four`.

```lean
theorem two_plus_two_eq_four : two + two = four := by
  solution!
    rewrite [four_eq_succ_three, three_eq_succ_two,
             two_eq_succ_one, one_eq_succ_zero]
    rewrite [add_succ, add_succ, add_zero]
    rfl
```

:::gradeTheorem "0.5" one_plus_one_eq_two two_plus_two_eq_four
:::
::::
:::::

### Multiplication

::::full
Now that we know how addition is defined, we can use it to define multiplication:
::::

:::slidebreak
:::

```lean
def mul (n m : Nat) : Nat :=
  match m with
  | zero => zero
  | succ m' => (mul n m') + n

scoped infixl:70 " * " => mul
```

::::exercise (rating := 1) (name := "mul_simpl_rules")
Multiplication, like any function we will prove properties about,
also has simplification rules.

Remove {tactic}`sorry` and prove the simplification rules for {name}`mul` below.
You will likely find the proofs of the simplification rules for {name}`add`
to be helpful as a model.

:::dev
@rogerburtonpatel: it would be nice if we could get the
theorem _statements_ inside a `solution!` block as well.
:::

```lean
theorem mul_zero : ∀ n : Nat, n * zero = zero := by
  solution!
    intro n
    rfl

theorem mul_succ : ∀ n m : Nat, n * (succ m) = (n * m) + n := by
  solution!
    intro n m
    rfl

attribute [irreducible] mul
```

:::gradeTheorem "0.5" mul_zero mul_succ
:::
::::

Prove this theorem using rewriting with the simplification rules.

```lean
theorem zero_add_one : (zero + one : Nat) = one := by
  rewrite [one_eq_succ_zero]
  workinclass!
    rewrite [add_succ, add_zero]
    rfl
```

:::::full
Notice how {tactic}`rewrite`
can take any number of arguments. You can rewrite with all of the
simplification rules at once, for example.

After each rewrite, check the proof state by placing the cursor immediately
after a rule to see how the goal is changing. This happens naturally
as you write the proof, which makes it convenient to use {tactic}`rewrite` blocks
with multiple rules.

::::exercise (rating := 2) (name := "test_mul_add")
```lean
theorem one_add_one : (one + one : Nat) = two := by
  rewrite [one_eq_succ_zero]
  solution!
    rewrite [add_succ, add_zero]
    rfl

theorem zero_mul_two : (zero * two : Nat) = zero := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  solution!
    rewrite [mul_succ, mul_succ, mul_zero]
    rewrite [add_zero, add_zero]
    rfl

theorem one_mul_two : (one * two : Nat) = two := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  solution!
    rewrite [mul_succ, mul_succ, mul_zero]
    rewrite [add_succ, add_zero, add_succ, add_zero]
    rfl

theorem two_mul_two : (two * two : Nat) = four := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  solution!
    rewrite [mul_succ, mul_succ, mul_zero]
    rewrite [add_succ, add_succ, add_zero]
    rewrite [add_succ, add_succ, add_zero]
    rfl
```

:::gradeTheorem "0.5" one_add_one zero_mul_two one_mul_two two_mul_two
:::
::::
:::::

:::slidebreak
:::

### Equality and Ordering

::::full
When we say that Lean relies on almost nothing that's truly built-in, we really mean it: even
testing equality is not a primitive operation, but an ordinary function that we could re-implement
ourselves as users.
::::

Here is a function `beq` that tests natural numbers for
equality, yielding a boolean.

```lean
def beq (n m : Nat) : Bool :=
  match n with
  | zero => match m with
            | zero => true
            | succ _ => false
  | succ n' => match m with
               | zero => false
               | succ m' => beq n' m'
```

We could also write this by pattern matching on both `n` and `m` at the same time:

```lean
def beq' (n m : Nat) : Bool :=
  match n, m with
  | zero, zero => true
  | zero, succ _ => false
  | succ _, zero => false
  | succ n', succ m' => beq n' m'
```

The definitions of `beq` and `beq'` are equivalent.

:::slidebreak
:::

Similarly, the `ble` function tests whether its first argument is
less than or equal to its second argument, yielding a boolean.

```lean
def ble (n m : Nat) : Bool :=
  match n with
  | zero => true
  | succ n' =>
      match m with
      | zero => false
      | succ m' => ble n' m'

theorem zero_ble (n : Nat) : ble zero n = true := by rfl
theorem succ_ble_zero (n : Nat) : ble (succ n) zero = false := by rfl
theorem succ_ble_succ (n m : Nat) : ble (succ n) (succ m) = ble n m := by rfl

example : ble two two = true  := by rfl
example : ble two four = true := by rfl
example : ble four two = false := by rfl

```

:::::full
::::exercise (rating := 1) (name := "blt")
Define a less-than function in terms of {name}`ble`.

```lean
def blt (n m : Nat) : Bool := solution!(ble (succ n) m)

example : blt two two = false := solution!(by rfl)
example : blt two four = true  := solution!(by rfl)
theorem blt_test3 : blt four two = false := solution!(by rfl)

attribute [irreducible] blt ble
```

:::autogradedHole blt
:::

:::gradeTheorem 1 blt_test3
:::
::::
:::::

:::slidebreak
:::

We'll be using {name}`beq` a lot, so let's give it an infix notation.

```lean
scoped infixl:30 " == " => beq
```

::::full
We now have seen two symbols that both look like equality: `=`
and `==`.  We'll have much more to say about their differences and
similarities later. For now, notice that
`x = y` is a logical _claim_ — a "proposition" — that we can try to
prove, while `x == y` is a boolean _expression_ whose value (either
{name}`true` or {name}`false`) Lean can compute.
::::

::::terse
Note that `==` and `=` are different; the former means {name}`beq` whereas the latter is a logical
claim. Here are our simplification rules.
::::

::::full
We can also now define the simplification rules for {name}`beq` with our new notation,
one for each of the four cases of control flow through the function.
::::

```lean
theorem zero_beq_zero : (zero == zero) = true := by rfl
theorem zero_beq_succ (n : Nat) : (zero == (succ n)) = false := by rfl
theorem succ_beq_zero (n : Nat) : ((succ n) == zero) = false := by rfl
theorem succ_beq_succ (n m : Nat) : ((succ n) == (succ m)) = (n == m) := by rfl

attribute [irreducible] beq
```

::::full
Aside: Our naming convention
for simplification rules encodes their meaning.
For `add_zero` and `add_succ`, notice that the `zero` and
`succ` come after the `add`; this is because they depend on `add`'s _second_ argument
and do not care about its first.
:::dev "Benjamin Pierce (bcpierce00)"
So they would be called `zero_add` and `succ_add` if they depended on the first argument?? This explanation isn't making complete sense to me...
:::
Also, in the `beq` rules above, we write `zero_beq_zero` and `zero_beq_succ`
because the rules apply to both the first and second arguments of `beq`. We put
`beq` between the arguments because it usually written in infix.
There are no strict style conventions for naming theorems like this in Lean, but many developers
follow this approach.
:::dev "Benjamin Pierce (bcpierce00)"
We haven't really articulated an "approach" -- just given a couple of miscellaneous examples...
TO DO: Let's move this to UsingLean and broaden it.
:::
::::

## General Proofs about Natural Numbers

:::terse
A (slightly) more interesting theorem:
:::


::::full
We now begin to make claims about _general_ natural numbers.

We begin by making a universal claim about all numbers {lean}`n` and {lean}`m` that are
equal to each other ({lean}`n = m`). The arrow symbol is pronounced "implies."
Enter it with `\to` or `\->` or `\r`.

The {tactic}`intro` tactic moves the universally quantified variables and the
hypothesis into the context, giving them names.  The goal is now to prove
{lean}`n + n = m + m` under the assumption `h : n = m`.

The tactic that tells Lean to perform replacement is one we have seen
before: {tactic}`rewrite`. It can take a hypothesis from the context as an argument,
just like it can take a previously proved theorem.  In this case, we want to
rewrite with the hypothesis `h`, which says that {lean}`n` and {lean}`m` are equal, so
that we can replace {lean}`n` with {lean}`m` in the goal.

After the rewrite, the goal is {lean}`m + m = m + m`, which can be closed by
{tactic}`rfl`.
::::

```lean
theorem add_id_example : ∀ n m : Nat,
    n = m → n + n = m + m := by
  intro n m
  intro h
  rewrite [h]
  rfl
```

:::::full
::::exercise (rating := 1) (name := "add_id_exercise")

Remove {tactic}`sorry` and fill in the proof.

```lean
theorem add_id_exercise : ∀ n m o : Nat,
    n = m → m = o → n + m = m + o := by
  solution!
    intro n m o h1 h2
    rewrite [h1, h2]
    rfl
```

:::gradeTheorem 1 add_id_exercise
:::
::::
:::::

:::slidebreak
:::

### Displaying Theorem Statements

The `#check` command can also be used to examine the statements of
previously declared lemmas and theorems.

```lean (name := mul_l)
#check mul_zero
#check mul_succ
```

```leanOutput mul_l
NatPlayground.Nat.mul_zero (n : Nat) : n * zero = zero
```

```leanOutput mul_l
NatPlayground.Nat.mul_succ (n m : Nat) : n * succ m = n * m + n
```


::::full
Note that you may see a slight discrepancy in the output:
`#check` shows the theorem differently from the way it was introduced earlier.

First, Lean may print the theorem's fully qualified name {name}`NatPlayground.Nat.mul_zero`.
The qualification identifies the namespace containing the theorem, though
the shorter name {name}`mul_zero` is usually sufficient when Lean can determine
which declaration we mean.

Second, Lean displays the theorem's arguments before the colon `mul_zero (n : Nat) : n * zero = zero`.
Writing arguments as binders before the colon is called _declaration-header style_.
The same statement can be written using an explicit universal quantifier, as we have seen before:

```display
mul_zero : ∀ (n : Nat), n * zero = zero
```

Writing statements in declaration-header style shortens proofs because Lean
automatically adds declared variables to the context, rather than requiring
them to be added with {tactic}`intro`.
The declaration-header style is conventional in Lean, and we will generally use it from now on.
::::

::::terse
Lean displays universally quantified variables as binders before the colon, which is
the preferred _declaration-header style_ in Lean.
::::

:::slidebreak
:::

# Proof by Case Analysis

::::full
Of course, not everything can be proved by simple calculation and
rewriting: In general, the presence of unknown, hypothetical values
(arbitrary numbers, booleans, etc.) can block a proof.
::::

:::terse
Sometimes simple calculation and rewriting are not enough...
:::


```lean +error
example (n : Nat) : (succ zero + n == zero) = false := by
  /-
    We can't rewrite by any lemmas here: `add`'s definition matches on its
    *second* argument, and here that argument is the unknown `n`!
  -/
```

::::full
The tactic that tells Lean to consider separate cases is called {tactic}`cases`.
::::

:::terse
We can use `cases` to perform case analysis:
:::

```lean
theorem add_one_neb_zero (n : Nat) : (succ zero + n == zero) = false := by
  cases n with
  | zero =>
    rewrite [add_zero, succ_beq_zero]
    rfl
  | succ n' =>
    rewrite [add_succ, succ_beq_zero]
    rfl
```

::::full
The {tactic}`cases` tactic generates _two_ subgoals, which we must
prove, separately, in order to get Lean to accept the theorem.
The generated subgoals are tagged by the names of the constructors.
`| zero =>` and `| succ n' =>` select which subgoal to work on next
and introduce variable names.
Note also that when we enter a subcase, we increase the level of indentation at which we are working
by two spaces.

The {tactic}`cases` tactic can be used with any inductively defined
datatype. For example, we use it next to prove that boolean
negation is involutive (that is, that negation is its own inverse).
::::

:::slidebreak
:::

:::terse
Another example, using booleans:
:::

```lean
theorem not_involutive (b : Bool) : (!!b) = b := by
  cases b with
  | false =>
    rewrite [Bool.not_false, Bool.not_true]
    rfl
  | true =>
    rewrite [Bool.not_true, Bool.not_false]
    rfl
```

::::full
The proof above uses some rewrite rules that we didn't
prove previously. These come from Lean's standard library, in particular
from the section about booleans.
In the {ref "UsingLean"}[UsingLean] chapter we will discuss how to search through the standard library
for theorems like these. For now, note that, if you hover over the name of these theorems
in VS Code, the Lean extension will show you what the theorem proves.
::::

::::terse
Some of the above proofs use standard library lemmas; later on we will discuss how to search for
those yourself.
::::

:::slidebreak
:::

We can also have nested case analysis:

```lean
theorem and_commutative (b c : Bool) :
    (b && c) = (c && b) := by
  cases b with
  | true =>
    cases c with
    | true =>
      rewrite [Bool.and_self]
      rfl
    | false =>
      rewrite [Bool.and_false, Bool.and_true]
      rfl
  | false =>
    cases c with
    | true =>
      rewrite [Bool.and_true, Bool.and_false]
      rfl
    | false =>
      rewrite [Bool.and_self]
      rfl

theorem and3_exchange (b c d : Bool) :
    ((b && c) && d) = ((b && d) && c) := by
  cases b with
  | false =>
    cases c with
    | true =>
      cases d with
      | false =>
        rewrite [Bool.and_true, Bool.and_self]
        rfl
      | true =>
        rewrite [Bool.and_true]
        rfl
    | false =>
      cases d with
      | false =>
        rewrite [Bool.and_self]
        rfl
      | true =>
        rewrite [Bool.and_self, Bool.and_true]
        rfl
  | true =>
    cases c with
    | true =>
      cases d with
      | false =>
        rewrite [Bool.and_self, Bool.and_false, Bool.and_true]
        rfl
      | true =>
        rewrite [Bool.and_self]
        rfl
    | false =>
      cases d with
      | false =>
        rewrite [Bool.and_false]
        rfl
      | true =>
        rewrite [Bool.and_false, Bool.and_true, Bool.and_self]
        rfl
```

As you can see, proofs by cases can become very verbose.
We will introduce some tactics for writing shorter proofs
by case analysis in the {ref "Tactics"}[Tactics] chapter.

## New Tactics: `rewrite ... at` and {tactic}`exact`

:::suppressPreviousHeaderWhenTerse
:::

::::full
Some new tactics will be useful for the exercises ahead.

The `rewrite ... at` tactic can be used to rewrite in a hypothesis instead of the
goal. For example, if `hp : p` is in the context and we have a rule `r : p = q`,
then `rewrite [r] at hp` changes the hypothesis to `hp : q`.

The {tactic}`exact` tactic closes a goal by providing the exact proof of the goal.  For
example, if `hp : p` is in the context and the goal is `p`, then `exact hp`
closes the goal. You can also transform `hp` slightly when using `exact`, and we will
explain how when we get to an example that needs it.
::::

::::terse
You will need the `rewrite ... at` and {tactic}`exact` tactics to complete some exercises.
::::

:::::full
::::exercise (rating := 2) (name := "or_false_true")
Prove the following claim.

Tip: the rewrite rule to simplify `(b || false)` is called {name}`Bool.or_false`.

```lean
theorem or_false_true (b : Bool) (h: (b || false) = true) :
  b = true := by
  solution!
    rewrite [Bool.or_false] at h
    exact h
```

:::gradeTheorem 2 or_false_true
:::
::::

::::exercise (rating := 1) (name := "zero_neb_add_one")
```lean
theorem zero_neb_add_one (n : Nat) :
  (zero == (succ zero + n)) = false := by
  solution!
    cases n with
    | zero => rewrite [add_zero, zero_beq_succ]; rfl
    | succ n' => rewrite [add_succ, zero_beq_succ]; rfl
```

:::gradeTheorem 1 zero_neb_add_one
:::
::::
:::::

## Structural Recursion (Optional)

:::suppressPreviousHeaderWhenTerse
:::

:::::full
Here is a copy of the definition of `even`:

```lean
def even' (n : Nat) : Bool :=
  match n with
  | zero => true
  | succ (zero) => false
  | succ (succ n') => even' n'
```

When Lean checks this definition, it verifies that the recursion
terminates.  Specifically, it checks that one of the parameters
is _structurally decreasing_ — each recursive call made in the body of the
definition is made on an argument that is smaller than the original input.
In {name}`even'` example above, the argument to the recursive call to {name}`even'` is the variable `n'`.
Because of our pattern match, we know that `n` is equal to `succ (succ n')`, and therefore
that `n'` is smaller than `n`. This makes `n'` an acceptable argument to {name}`even'` for Lean's
termination checker, and so this recursive definition is accepted.

This requirement is a fundamental feature of Lean's design: In
particular, it guarantees that every function that can be defined
in Lean will terminate on all inputs.  However, because Lean's
termination analysis is not always able to figure things out
automatically, it is sometimes necessary to provide hints or
write functions in slightly different ways.

::::exercise (rating := 2) (name := "decreasing") (optional := true) (manual := true)
To get a concrete sense of how termination checking works in Lean,
find a way to write a sensible recursive definition (of a simple
function on numbers, say) that does actually terminate on all inputs,
but that Lean will reject because it cannot automatically prove
termination.

:::solution

```lean +error
def factorial_bad (n : Nat) : Nat :=
  match n with
  | zero => (succ zero)
  | succ _ => n * factorial_bad (pred n)
```

This fails because Lean can't see that `pred n` is structurally smaller.
:::
::::
:::::

## Binary Numerals

:::suppressPreviousHeaderWhenTerse
:::

:::::full
::::exercise (rating := 3) (name := "binary")
We can generalize our unary representation of natural numbers to
the more efficient binary representation by treating a binary
number as a sequence of constructors `b0` and `b1` (representing 0s
and 1s), terminated by a `z`.

For example:

```
decimal                binary   unary
      0                     z   zero
      1                  b1 z   succ zero
      2             b0 (b1 z)   succ (succ zero)
      3             b1 (b1 z)   succ (succ (succ zero))
      4        b0 (b0 (b1 z))   succ (succ (succ (succ zero)))
      5        b1 (b0 (b1 z))   succ (succ (succ (succ (succ zero))))
      6        b0 (b1 (b1 z))   succ (succ (succ (succ (succ (succ zero)))))
      7        b1 (b1 (b1 z))   succ (succ (succ (succ (succ (succ (succ zero))))))
      8   b0 (b0 (b0 (b1 z)))   succ (succ (succ (succ (succ (succ (succ (succ zero)))))))
```

Note that the low-order bit is on the left and the high-order bit
is on the right — the opposite of the way binary numbers are
usually written.  This choice makes them easier to manipulate.

(Comprehension check: What unary numeral does `b0 z` represent?)

```lean
inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)

attribute [pp_nodot] Bin.b1 Bin.b0

def incr (m : Bin) : Bin
  := solution!(match m with
  | .z => .b1 .z
  | .b0 m' => .b1 m'
  | .b1 m' => .b0 (incr m'))

def binToNat (m : Bin) : Nat
  := solution!(match m with
  | .z => zero
  | .b0 m' => binToNat m' * two
  | .b1 m' => binToNat m' * two + one)

theorem incr_test1 : incr (.b1 .z) = .b0 (.b1 .z) := solution!(by rfl)
theorem incr_test2 : incr (.b0 (.b1 .z)) = .b1 (.b1 .z) := solution!(by rfl)
theorem incr_test3 : incr (.b1 (.b1 .z)) = .b0 (.b0 (.b1 .z)) := solution!(by rfl)

theorem incr_z : incr .z = .b1 .z := solution!(by rfl)
theorem incr_b0 (m : Bin) : incr (.b0 m) = .b1 m := solution!(by rfl)
theorem incr_b1 (m : Bin) : incr (.b1 m) = .b0 (incr m) := solution!(by rfl)

theorem binToNat_z : binToNat .z = zero := solution!(by rfl)
theorem binToNat_b0 (m : Bin) : binToNat (.b0 m) = binToNat m * two := solution!(by rfl)
theorem binToNat_b1 (m : Bin) : binToNat (.b1 m) = binToNat m * two + one := solution!(by rfl)
```

:::autogradedHole incr binToNat
:::

You may find your previous proofs of {name}`zero_add_one`, {name}`one_add_one`, {name}`zero_mul_two`,
{name}`one_mul_two`, and {name}`two_mul_two` useful here.

```lean
example : binToNat (.b0 (.b1 .z)) = two := solution!(by
  rewrite [binToNat_b0, binToNat_b1, binToNat_z]
  rewrite [zero_mul_two, zero_add_one, one_mul_two]
  rfl
)
theorem binToNat_test1 : binToNat (incr (.b1 .z)) = add one (binToNat (.b1 .z)) := solution!(by
    rewrite [binToNat_b1, binToNat_z, incr_b1, binToNat_b0, incr_z, binToNat_b1, binToNat_z]
    rewrite [zero_mul_two, zero_add_one, one_mul_two, one_add_one]
    rfl
)
theorem binToNat_test2 : binToNat (incr (incr (.b1 .z))) = add two (binToNat (.b1 .z)) := solution!(by
  rewrite [binToNat_b1, binToNat_z, incr_b1, incr_b0, binToNat_b1, incr_z, binToNat_b1, binToNat_z]
  rewrite [zero_mul_two, zero_add_one, one_mul_two]
  rfl
)
theorem binToNat_test3 : binToNat (.b0 (.b0 (.b1 .z))) = four := solution!(by
  rewrite [binToNat_b0, binToNat_b0, binToNat_b1, binToNat_z]
  rewrite [zero_mul_two, zero_add_one, one_mul_two, two_mul_two]
  rfl
)

attribute [irreducible] incr binToNat
```

:::gradeTheorem "0.5" incr_test1 incr_test2 incr_test3 binToNat_test1 binToNat_test2 binToNat_test3
:::
::::
:::::

```lean
end Nat
```

# More Exercises

:::suppressPreviousHeaderWhenTerse
:::

## Warmups

:::suppressPreviousHeaderWhenTerse
:::

:::::full
::::exercise (rating := 1) (name := "identity_fn_applied_twice")
You now have a small but rather powerful suite of tactics at your disposal.
As a warmup for the last section of the chapter, use the tactics you have
learned so far to prove the following theorem about boolean functions.

Hint: You can use {tactic}`rewrite` with _any_ hypothesis that has an `=` in it
as long as the types line up.

```lean
theorem identity_fn_applied_twice (f : Bool → Bool) :
    (∀ x : Bool, f x = x) →
    ∀ b : Bool, f (f b) = b := by
  solution!
    intro h b
    rewrite [h, h]
    rfl
```

:::gradeTheorem 1 identity_fn_applied_twice
:::
::::

::::exercise (rating := 1) (name := "negation_fn_applied_twice") (manual := true)
Now state and prove a theorem `negation_fn_applied_twice` similar
to the previous one but where the hypothesis says that the
function `f` has the property that `f x = !x`.

```lean
-- SOLUTION
theorem negation_fn_applied_twice (f : Bool → Bool) :
    (∀ x : Bool, f x = !x) →
    ∀ b : Bool, f (f b) = b := by
  intro h b
  rewrite [h, h]
  cases b with
  | true => rewrite [Bool.not_true, Bool.not_false]; rfl
  | false => rewrite [Bool.not_false, Bool.not_true]; rfl
-- END SOLUTION
```

:::grade
```
GRADE_MANUAL 1: negation_fn_applied_twice
```
:::
::::

::::exercise (rating := 3) (name := "and_eq_or") (optional := true)
Prove the following theorem.

```lean
theorem and_eq_or (b c : Bool) : (b && c) = (b || c) → b = c := by
  solution!
    intro h
    cases c with
    | true =>
      /-
        h : (true && c) = true || c, i.e., h : c = true
      -/
      rewrite [Bool.and_true, Bool.or_true] at h
      rewrite [h]
      rfl
    | false =>
      /-
        h : (false && c) = false || c, i.e., h : false = c
      -/
      rewrite [Bool.and_false, Bool.or_false] at h
      rewrite [h]
      rfl
```

:::gradeTheorem 3 and_eq_or
:::
::::
:::::

## Airport Exercise

:::suppressPreviousHeaderWhenTerse
:::

:::::full
:::dev "Yipeng Liu (berberman)" BeforeNextRelease
Add grading attributes.
:::

Now that we have learned some basic features of Lean, let's close the chapter
with an exercise that brings them together.

In this exercise, we will model part of a database
storing information about travelers passing through an airport.
The database contains one entry per traveler, recording
information about where the traveler is in the airport process and the contents of their
current carry-on bag.

We will implement several operations on these entries, state intended
properties of the database's
behavior, and prove that the implementation satisfies them.


```lean
namespace Airport
```

For simplicity, a carry-on bag either contains a prohibited item,
such as a liquid that exceeds the allowed limit,
causing it to fail inspection, or contains only ordinary items.

```lean
inductive BagContent : Type where
  | prohibited
  | ordinary
```

After a traveler checks in, the database also records the result of
the most recent security screening of their carry-on bag.

```lean
inductive ScreeningStatus : Type where
  | notScreened
  | cleared
  | blocked
```

Next, we define the possible stages of the airport process a traveler can inhabit:
- they have not yet purchased a ticket;
- they have a ticket but have not yet checked in;
- they have checked in, in which case the
  database also stores the screening status of their carry-on bag.

We can represent these possible database entries directly with an inductive type.
```lean
inductive Traveler : Type where
  | noTicket  (bagContent : BagContent)
  | ticketed  (bagContent : BagContent)
  | checkedIn (bagContent : BagContent) (screeningStatus : ScreeningStatus)
```

Buying a ticket changes a traveler with no ticket into a ticketed traveler.
If the traveler already has a ticket or has already checked in, nothing changes.

::::exercise (rating := 1) (name := "buyTicket")
```lean
def buyTicket (t : Traveler) : Traveler := solution!(
  match t with
  | .noTicket bagContent => .ticketed bagContent
  | _ => t
)
theorem buyTicket_test1 : buyTicket (.noTicket .ordinary) = .ticketed .ordinary := solution!(by rfl)
theorem buyTicket_test2 : buyTicket (.checkedIn .prohibited .blocked) = .checkedIn .prohibited .blocked := solution!(by rfl)
```
:::autogradedHole buyTicket
:::
:::gradeTheorem "0.5" buyTicket_test1 buyTicket_test2
:::
::::

Here are the simplification rules for {name}`buyTicket`:

```lean
theorem buyTicket_noTicket (bagContent : BagContent) :
    buyTicket (.noTicket bagContent) = .ticketed bagContent := solution!(by rfl)

theorem buyTicket_ticketed (bagContent : BagContent) :
    buyTicket (.ticketed bagContent) = .ticketed bagContent := solution!(by rfl)

theorem buyTicket_checkedIn (bagContent : BagContent)
    (screeningStatus : ScreeningStatus) :
    buyTicket (.checkedIn bagContent screeningStatus) = .checkedIn bagContent screeningStatus := solution!(by rfl)

attribute [irreducible] buyTicket
```

The first property we will prove about our system is that
purchasing a ticket is an _idempotent_ operation
(i.e., performing it twice has the same effect as performing it once).

::::exercise (rating := 2) (name := "buy_ticket_idempotent")
```lean
theorem buyTicket_idempotent (t : Traveler) :
    buyTicket (buyTicket t) = buyTicket t := by
  solution!
    cases t with
    | noTicket =>
        rewrite [buyTicket_noTicket]
        rewrite [buyTicket_ticketed]
        rfl
    | ticketed =>
        rewrite [buyTicket_ticketed]
        rewrite [buyTicket_ticketed]
        rfl
    | checkedIn =>
        rewrite [buyTicket_checkedIn]
        rewrite [buyTicket_checkedIn]
        rfl
```
:::gradeTheorem 2 buyTicket_idempotent
:::
::::

A traveler can check in only after buying a ticket.
Checking in records that their carry-on bag still needs to be inspected.
Calling `checkIn` before buying a ticket or after already checking in does nothing.

::::exercise (rating := 1) (name := "checkIn")

```lean
def checkIn (t : Traveler) : Traveler := solution!(
  match t with
  | .ticketed bagContent => .checkedIn bagContent .notScreened
  | _ => t
)

theorem checkIn_test1 : checkIn (.noTicket .ordinary) = .noTicket .ordinary := solution!(by rfl)
theorem checkIn_test2 : checkIn (.ticketed .prohibited) = .checkedIn .prohibited .notScreened := solution!(by rfl)
theorem checkIn_test3 : checkIn (.checkedIn .ordinary .cleared) = .checkedIn .ordinary .cleared := solution!(by rfl)
```
:::autogradedHole checkIn
:::
:::gradeTheorem "1/3" checkIn_test1 checkIn_test2 checkIn_test3
:::
::::

Again, we record one rewrite rule for each case:

```lean
theorem checkIn_noTicket (bagContent : BagContent) :
    checkIn (.noTicket bagContent) = .noTicket bagContent := solution!(by rfl)

theorem checkIn_ticketed (bagContent : BagContent) :
    checkIn (.ticketed bagContent) = .checkedIn bagContent .notScreened := solution!(by rfl)

theorem checkIn_checkedIn (bagContent : BagContent)
    (screeningStatus : ScreeningStatus) :
    checkIn (.checkedIn bagContent screeningStatus) = .checkedIn bagContent screeningStatus := solution!(by rfl)

attribute [irreducible] checkIn
```

A traveler who does not yet have a ticket can buy one and then check in.
After this, the traveler is checked in and their carry-on ba bag needs to be screened.

::::exercise (rating := 1) (name := "buy_ticket_then_check_in")
```lean
theorem buyTicket_then_checkIn (bagContent : BagContent) :
    checkIn (buyTicket (.noTicket bagContent)) = .checkedIn bagContent .notScreened := by
  solution!
    rewrite [buyTicket_noTicket]
    rewrite [checkIn_ticketed]
    rfl
```
:::gradeTheorem 1 buyTicket_then_checkIn
:::
::::

Carry-on inspection happens only after check-in.
A bag containing only ordinary items is cleared,
while a bag containing a prohibited item is blocked.
If the traveler has not checked in, `inspectBag` does nothing.

::::exercise (rating := 1) (name := "inspectBag")
Define `inspectBag`.

```lean
def inspectBag (t : Traveler) : Traveler := solution!(
  match t with
  | .checkedIn .ordinary _ => .checkedIn .ordinary .cleared
  | .checkedIn .prohibited _ => .checkedIn .prohibited .blocked
  | _ => t
)

theorem inspectBag_test1 : inspectBag (.ticketed .prohibited) = .ticketed .prohibited := solution!(by rfl)
theorem inspectBag_test2 : inspectBag (.checkedIn .ordinary .notScreened) = .checkedIn .ordinary .cleared := solution!(by rfl)
theorem inspectBag_test3 : inspectBag (.checkedIn .prohibited .notScreened) = .checkedIn .prohibited .blocked := solution!(by rfl)
```
:::autogradedHole inspectBag
:::
:::gradeTheorem "1/3" inspectBag_test1 inspectBag_test2 inspectBag_test3
:::
::::

Again, we record one characterization lemma for each case.

```lean
theorem inspectBag_noTicket (bagContent : BagContent) :
    inspectBag (.noTicket bagContent) = .noTicket bagContent := solution!(by rfl)

theorem inspectBag_ticketed (bagContent : BagContent) :
    inspectBag (.ticketed bagContent) = .ticketed bagContent := solution!(by rfl)

theorem inspectBag_ordinary (screeningStatus : ScreeningStatus) :
    inspectBag (.checkedIn .ordinary screeningStatus) = .checkedIn .ordinary .cleared := solution!(by rfl)

theorem inspectBag_prohibited (screeningStatus : ScreeningStatus) :
    inspectBag (.checkedIn .prohibited screeningStatus) = .checkedIn .prohibited .blocked := solution!(by rfl)

attribute [irreducible] inspectBag
```

::::exercise (rating := 2) (name := "inspect_bag_idempotent")
Show that inspecting same unchanged carry-on bag twice has the same effect as inspecting it once.

```lean
theorem inspectBag_idempotent (t : Traveler) : inspectBag (inspectBag t) = inspectBag t := by
  solution!
    cases t with
    | noTicket bagContent =>
      rewrite [inspectBag_noTicket]
      rewrite [inspectBag_noTicket]
      rfl
    | ticketed bagContent =>
      rewrite [inspectBag_ticketed]
      rewrite [inspectBag_ticketed]
      rfl
    | checkedIn bagContent screeningStatus =>
      cases bagContent with
      | prohibited =>
        rewrite [inspectBag_prohibited]
        rewrite [inspectBag_prohibited]
        rfl
      | ordinary =>
        rewrite [inspectBag_ordinary]
        rewrite [inspectBag_ordinary]
        rfl
```
:::gradeTheorem 2 inspectBag_idempotent
:::
::::

A traveler may leave the screened area and return with a different carry-on bag.
Since the previous screening result applied to the old bag,
a new carry-on must be screened again before the traveler can re-enter.

::::exercise (rating := 1) (name := "changeBag")
Define `changeBag`.
```lean
def changeBag (newContent : BagContent) (t : Traveler) : Traveler := solution!(
  match t with
  | .checkedIn _ _ => .checkedIn newContent .notScreened
  | .ticketed _ => .ticketed newContent
  | .noTicket _ => .noTicket newContent
)

theorem changeBag_test1 : changeBag .prohibited (.ticketed .ordinary) = .ticketed .prohibited := solution!(by rfl)
theorem changeBag_test2 : changeBag .prohibited (.checkedIn .ordinary .cleared) = .checkedIn .prohibited .notScreened := solution!(by rfl)
```
:::autogradedHole changeBag
:::
:::gradeTheorem "0.5" changeBag_test1 changeBag_test2
:::
::::

As before, we record the behavior of each case as a rewrite rule.

```lean
theorem changeBag_noTicket (newContent oldContent : BagContent) :
    changeBag newContent (.noTicket oldContent) = .noTicket newContent := solution!(by rfl)

theorem changeBag_ticketed (newContent oldContent : BagContent) :
    changeBag newContent (.ticketed oldContent) = .ticketed newContent := solution!(by rfl)

theorem changeBag_checkedIn (newContent oldContent : BagContent)
    (screeningStatus : ScreeningStatus) :
    changeBag newContent (.checkedIn oldContent screeningStatus) =
    .checkedIn newContent .notScreened := solution!(by rfl)

attribute [irreducible] changeBag
```

It is easy to see that replacing a bag after it has been inspected resets its screening status.
In other words, {name}`inspectBag` and {name}`changeBag` do not, in general, commute:
the order in which the two operations are performed can affect the result.

However, if the traveler has not checked in, {name}`inspectBag` does nothing,
so changing and inspecting the carry-on can be performed in either order.
There are two such cases: the traveler may not yet have a ticket,
or may have a ticket but not yet be checked in.

::::exercise (rating := 2) (name := "inspect_changeBag_commute")
```lean
theorem inspectBag_changeBag_comm_noTicket
    (oldContent newContent : BagContent) :
    inspectBag (changeBag newContent (.noTicket oldContent)) =
    changeBag newContent (inspectBag (.noTicket oldContent)) := by
  solution!
    rewrite [changeBag_noTicket]
    rewrite [inspectBag_noTicket]
    rewrite [inspectBag_noTicket]
    rewrite [changeBag_noTicket]
    rfl

theorem inspectBag_changeBag_comm_ticketed
    (oldContent newContent : BagContent) :
    inspectBag (changeBag newContent (.ticketed oldContent)) =
    changeBag newContent (inspectBag (.ticketed oldContent)) := by
  solution!
    rewrite [changeBag_ticketed]
    rewrite [inspectBag_ticketed]
    rewrite [inspectBag_ticketed]
    rewrite [changeBag_ticketed]
    rfl
```
:::gradeTheorem 1 inspectBag_changeBag_comm_noTicket inspectBag_changeBag_comm_ticketed
:::
::::

```lean
end Airport
```
:::::
