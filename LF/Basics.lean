prelude
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

open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "Basics: Functional Programming in Lean" =>
%%%
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
:::

::::full
The _functional style_ of programming is founded on simple, everyday
mathematical intuitions: If a program has no side effects, then --
ignoring efficiency -- all we need to understand about it is how it
maps inputs to outputs. That is, we can think of it as just a
concrete method for computing a mathematical function. This direct
connection between programs and simple mathematical objects supports
both formal correctness proofs and sound informal reasoning about
program behavior. This is one sense of the word "functional" in
"functional programming."

The other sense in which functional programming is "functional" is
that it emphasizes the use of functions as _first-class_ values --
i.e., values that can be passed as arguments to other functions,
returned as results, included in data structures, etc.  The
recognition that functions can be treated as data gives rise to a
host of useful and powerful programming idioms.

Other common features of functional languages include _algebraic
data types_ and _pattern matching_, which make it easy to
construct and manipulate rich data structures, and _polymorphic
types_ supporting abstraction and code reuse.  Lean offers
all of these features.

The first half of this chapter introduces some key elements of
Lean's functional programming language.  The second half introduces
some basic _tactics_ that can be used to prove properties of
programs.
::::

# Data and Functions

## Enumerated Types

:::terse
In Lean, we can
build practically
everything from first principles...
:::

::::full
One notable thing about Lean is that its set of built-in features is
_extremely_ small.  For example, instead of the usual palette of atomic
data types (booleans, integers, strings, etc.), Lean offers a powerful
mechanism for defining new data types from scratch, with all these
familiar types as instances.

Naturally, Lean also comes with an extensive standard library
providing definitions of booleans, numbers, and many common data
structures like lists and hash tables.  But there is nothing magic
or primitive about these library definitions.  To illustrate this
fact, we will explicitly recapitulate most of the definitions we
need in this course, rather than just referring
to the standard library. However, we take care to harmonize
those definitions with the ones in the standard library, as well
as to gradually introduce the actual library definitions a little later in the course.
By the time you are finished, you will have a good grasp
of how the Lean standard library is organized and how to efficiently
navigate it.
::::

## Days of the Week

:::terse
A datatype definition:
:::

::::full
To see how the datatype definition mechanism works, let's
start with a very simple example.  The following declaration tells
Lean that we are defining a set of data values -- a _type_.
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
The new type is called `Day`, and its members are `monday`,
`tuesday`, etc. These members are also called the _constructors_
of the `Day` type, since they can be use to construct elements of that type.

Having defined `Day`, we can write Lean functions that operate on
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
Note that the argument and return types of this function are
explicitly declared on the first line.  Like most functional
programming languages, Lean can often figure out these types for
itself when they are not given explicitly -- i.e., it can do _type
inference_ -- but we'll generally include them to make reading
easier.

The `match` keyword is Lean's keyword for _pattern matching_: the functional
programming way of examining and making decisions on data. When evaluating
`match d with...`, Lean will examine the structure of `d` to see which
case to execute; if `d` is `Day.monday`, for example, it will
evaluate the first case of the `match` statement; if `d` is
`Day.friday` it will evaluate the fifth case. (There is much more
to say about pattern matching -- we'll introduce more of its features
as the need arises.)

You may notice that we qualified all the constructors before using them,
writing `Day.monday` instead of just `monday`, for example. You may
wonder if this is necessary.

Lean places all constructors into a "namespace" associated with their type,
and requires uses of those constructors to be prefixed with their namespace.
We will see in a little bit how to enter a namespace and avoid this requirement,
but for now, if we wish to be a bit more concise, we can use just a `.`,
like `.monday`, that signals that we're qualifying a name
without having to type too much. A more concise (but equivalent) definition
of `nextWorkingDay` is given below.

:::dev
BCP: I *still* find this quite tangled.  We say Lean requires all uses of constructors to be prefixed with their namespace, but then, right after, we suggest exactly not doing this!  (And I am still confused, myself, about identifiers like `true` and `false`, which seem not to need to be prefixed, even though they come from their own namespace.)
:::

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

When full qualification is not necessary to disambiguate, we will
prefer the shorter syntax with just the `.`.

If you ever need to know the type of *any* pattern, object, or function,
you can hover over it with your mouse in any editor that supports Lean,
like VS Code or the web version we provide.

:::dev
RAB: I'm resolving the discussion for now. The `.pattern` syntax shows
up in the Lean suggestions, in the documentation, and (less importantly)
in our examples pervasively after this point, and we need to introduce it early.
I think we should ask for feedback from people who aren't writing the book on
this part and on others; I feel our curse of knowledge is leading to a lot of
focus on something that may not be that important.

BCP: I respectfully disagree that it's not important -- that is, the concept
doesn't seem all that important, but not confusing readers is important, and right now I think we are doing that.  We need *some* consistent story.

Old conversation, for reference:
MWH - it seems that the full explanation comes later? I'm still not sure I get
what's being said here. I think it's maybe worth being systematic, right here,
if it seems to slow you down.
DHS - I worry that explaining namespaces right here is too soon. This is essentially
the very first thing we explain in the whole textbook, and going directly in to the
details of how namespaces work immediately seems like a lot. Does it seem appropriate
to say "names have to be qualified" here and then explain namespaces later?
MWH - This is a key concept as the current comment explains. I'm a little inclined to
put it all here. But I'm good with whatever for now. We can always change it later.
:::
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
in comments.)
::::

```lean
#eval nextWorkingDay .friday
```

```lean
#eval nextWorkingDay (nextWorkingDay .saturday)
```

::::full
If you have a computer handy, this would be an excellent moment
to fire up VS Code with the Lean extension or the Lean web interface
and try it for yourself.  Load this file, `Basics.lean`,
from the book's Lean sources, find the above example, and observe
the result in the Lean InfoView panel.

:::dev
DHS: Where are we showing responses in comments? I don't see them.
RAB: Why did we remove the comments?
Per GitHub discussion, MWH agrees - this is unresolved.
BCP: Don't understand the state of play here...
:::
::::

## Aside: Using the VS Code Lean Extension

::::full
In VS Code, development of Lean code is supported by the Lean Extension,
which provides an interactive "InfoView" panel that displays the results
of commands like `#eval` and `#check`, as well as the current goal state
when working on proofs. You can hover over expressions in the source code
to see their types, and you can click on the results in the InfoView
to navigate to their definitions. This makes it easier to understand
how your code is being interpreted by Lean and to debug any issues that
arise.

The InfoView always follows your cursor, and Lean typechecks the file as you
edit it, so you can see the results of your changes immediately. You can also
use the InfoView to explore the definitions of functions and types that
you're using, which can be very helpful for understanding how they work.

If you haven't already, either install the Lean Extension in VS Code and open the
`Basics.lean` file or open `Basics.lean` on the interactive Lean web client
to see the InfoView in action. Try hovering over the `nextWorkingDay` function
and the `Day` type to see their definitions, and experiment with adding your own
`#eval` commands to test other inputs.

For `#eval` and other commands, we show Lean's responses in comments; if you
hover over the `#eval` commands above, you will see the popup that contains
the output should match what's in the comment below. Experiment with adding
your own `#eval` commands to test other inputs.

::::

Continuing with our simple type and function, we can record what we _expect_
the result of calling a function to be in the form of a Lean `example`:

```lean
example : nextWorkingDay (nextWorkingDay .saturday) = .tuesday := by
  rfl
```

::::full
This declaration asserts that the second working day after `saturday` is `tuesday`.
Having made the assertion, we can also ask Lean to _verify_ it.
The `by rfl` can be read as "The assertion we've just made can be
proved by observing that both sides of the equality evaluate to
the same thing."

`rfl` stands for "reflexivity," which is the principle that any value is
equal to itself. After evaluation, both sides of the equality are the same
value, so the assertion is true by reflexivity.  If we had made a different
assertion, such as `example : nextWorkingDay (nextWorkingDay .saturday) =
.monday`, then Lean would not be able to verify it and would instead signal an
error. Try it out!

We can also ask Lean to _compile_ our definitions to efficient
native code.

Lean compiles to C, which is then compiled to machine code by a
standard C compiler.  This facility is very useful, since it gives
us a path from proved-correct algorithms written in Lean to
efficient executables. We'll come back to this topic in later
chapters.
::::

:::dev
RAB: Is Lean compiling to C its "killer app," or is it the fact that it is an
executable programming language (unlike Gallina)? We should get a Lean pro's
take on what to say here.
:::

## Booleans

::::full
Following the pattern of the days of the week above, we can
define the standard type `Bool` of booleans, with members `true`
and `false`.
::::

:::terse
Another familiar enumerated type:
:::

We define our own `MyBool` to teach the concept of building from
scratch; later we'll switch to Lean's built-in `Bool`.
We use a different name to make explicit that this is not the same
type as Lean's built-in, but their definitions are equivalent.

```lean
inductive MyBool : Type where
  | true
  | false
```

The next command opens a new namespace so that our definitions don't
clash with ones from the standard library. We'll discuss it in more
detail below.

```lean
namespace MyBool
```

::::full
Functions over booleans can be defined in the same way as above
::::

```lean
def notb (b : MyBool) : MyBool :=
  match b with
  | .true =>  .false
  | .false => .true
```

:::slidebreak
:::

```lean
def andb (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | .true => b2
  | .false => .false

def orb (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | .true => .true
  | .false => b2
```

::::full
The last two definitions illustrate Lean's syntax for multi-argument
functions.  The corresponding multi-argument _application_ syntax is
illustrated by the following tests, which effectively constitute a
complete specification -- a truth table -- for the `orb` function:
::::

:::terse
Note the syntax for defining multi-argument functions (`andb` and `orb`).
:::


```lean
example : orb .true  .false = .true  := by rfl
example : orb .false .false = .false := by rfl
example : orb .false .true  = .true  := by rfl
example : orb .true  .true  = .true  := by rfl
```

We can define new symbolic notations for existing definitions.
Because Lean already defines the same notations for the built-in `Bool`,
we restrict ours locally to a namespace. Don't worry for now about
how the notation is defined.

```lean
namespace MyBool_notations
local prefix:40 (priority := high) "!" => notb
local infixl:35 (priority := high) " && " => andb
local infixl:30 (priority := high) " || " => orb
```

```lean
example : (.false || .false || .true) = .true := by rfl

example : (!.false) = .true := by rfl
end MyBool_notations
```

:::slidebreak
:::

::::exercise (rating := 1) (name := "nandb")
The `sorry` keyword is a placeholder for an incomplete proof or
definition.  We use it in exercises to indicate the parts that we're
leaving for you -- i.e., your job is to replace `sorry` with real
definitions and proofs.

Remove `sorry` below and complete the definition of the following
function.  The function should return `.true` if either or both of
its inputs are `.false`. Make sure that the `example` assertions
below can be verified by Lean.

```lean
def nandb (b1 : MyBool) (b2 : MyBool) : MyBool
  := solution!(match b1 with
  | .true => notb b2
  | .false => .true)

example : nandb .true  .false  = .true  := solution!(by rfl)
example : nandb .false .false =  .true  := solution!(by rfl)
example : nandb .false .true  =  .true  := solution!(by rfl)
example : nandb .true  .true   = .false := solution!(by rfl)
```

:::grade
```
GRADE_THEOREM 1: nandb_test4
```
:::
::::

::::exercise (rating := 1) (name := "andb3")
Do the same for the `andb3` function below. This function should
return `true` when all of its inputs are `true`, and `false`
otherwise.

```lean
def andb3 (b1 : MyBool) (b2 : MyBool) (b3 : MyBool) : MyBool
  := solution!(andb b1 (andb b2 b3))

example : andb3 .true .true .true  = .true  := solution!(by rfl)
example : andb3 .false .true .true = .false := solution!(by rfl)
example : andb3 .true .false .true = .false := solution!(by rfl)
example : andb3 .true .true .false = .false := solution!(by rfl)
```

:::grade
```
GRADE_THEOREM 1: andb3_test4
```
:::
::::

:::slidebreak
:::

::::full
Now that we've seen how to define our own booleans, let's switch
to Lean's built-in `Bool` type, which has the same structure
but comes with a lot of useful functions and lemmas.
::::

```lean
end MyBool
```

## Types

Every expression in Lean has a type describing what sort of thing it computes.
The `#check` command asks Lean to print the type of an expression.

```lean
#check true
```

If the thing after `#check` is followed by a colon and a type,
Lean will verify that the type of the expression
matches the given type and signal an error if not.

```lean
#check (true : Bool)
#check (not true : Bool)
```

Functions like `not` are themselves data values, just like `true`
and `false`.  Their types are called _function types_, and they are
written with arrows.

```lean
#check not
```

::::full
The type of `not`, written `Bool → Bool` and pronounced "`Bool`
arrow `Bool`," can be read, "Given an input of type `Bool`, this
function produces an output of type `Bool`." Similarly, the type of
`and`, written `Bool → Bool → Bool`, can be read, "Given two inputs,
each of type `Bool`, this function produces an output of type
`Bool`."
::::

### Aside: Unicode in Lean

::::full
Note that → is a unicode symbol, not a simple ASCII character. The
Lean Extension for VS Code provides convenient shortcuts for
entering such symbols. Simply type `\` (backslash) followed by the
name of the symbol, and the extension will automatically replace it
with the actual symbol. For example, typing `\->` or `\to` will produce
→, and `\lambda` will produce λ. To find out what backslash sequence
produces a unicode symbol that you can see on the screen, just hover
over it.
::::

## New Types from Old

::::full
The types we have defined so far are simple examples of "enumerated
types": their definitions explicitly enumerate a finite set of
elements, called _constructors_.  Here is a more interesting type
definition, `Color`, where one of the constructors takes an
argument:
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

An `inductive` definition does two things:

- It introduces a set of new _constructors_. E.g., {name}`RGB.red`,
  {name}`Color.primary`, {name}`true`, {name}`false`, {name}`Day.monday`,
  etc. are constructors.

- It groups them into a new named type, like `Bool`, `RGB`, or
  `Color`.

_Constructor expressions_ are formed by applying a constructor
to zero or more other constructors or constructor expressions,
obeying the declared number and types of the constructor arguments.
E.g., these are valid constructor expressions...

- {name}`RGB.red`
- {name}`true`
- {name}`Color.primary` {name}`RGB.red`

...but these are not:

- {name}`RGB.red` `Color.primary`
- {name}`true` {name}`RGB.red`
- {name}`Color.primary` `(.primary .red)`

  Note that we don't need to qualify `true` as `Bool.true`.
  Lean recognizes `Bool` as one of the types whose constructors
  are usable without qualification by default.

:::dev
BCP: "One of the types..." is mysterious.  What are these types?  Have we been told about them already?
:::

:::slidebreak
:::

We can define functions on colors using pattern matching, just as
we did for `Day` and `Bool`.

```lean
def monochrome (c : Color) : Bool :=
  match c with
  | .black => true
  | .white => true
  | .primary p => false
```

Since the `primary` constructor takes an argument, a pattern
that matches `.primary` should include either a variable, a constant
of appropriate type, or `_`. Lean's convention is to use a `_` (called a
_wildcard_) when the argument to a constructor doesn't matter. In
the definition of `monochrome`, we don't use the argument to `.primary`, so
a more idiomatic definition would be:

```lean
def monochrome' (c : Color) : Bool :=
  match c with
  | .black => true
  | .white => true
  | .primary _ => false
```

We can use a constant argument to `.primary` to match a specific primary color:

```lean
def isRed (c : Color) : Bool :=
  match c with
  | .black => false
  | .white => false
  | .primary .red => true
  | .primary _ => false
```

The pattern `.primary .red` will match only when `c` is
`.primary` with the argument `.red`. Patterns are checked in
order, so the subsequent pattern `.primary _` here means "the
constructor `primary` applied to any `RGB` constructor except
`red`."

An alternative way to write the same function would be to explicitly
nest match statements:

```lean
def isRed' (c : Color) : Bool :=
  match c with
  | .black => false
  | .white => false
  | .primary r =>
    match r with
    | .red => true
    | _ => false
```

This function produces the same result as the old
`isRed` but illustrates the use of a pattern matching variable: the
`.primary r` pattern stores the `RGB` argument into variable `r`,
and then pattern matches on that argument to produce the final
result.

::::exercise (rating := 1) (name := "is_weekend")
Define a function that takes a day and returns true if the day is
a weekend, and false otherwise.

Hint: You could do this by pattern matching on each possible day of the week,
or you could try to come up with a shorter solution...

```lean
@[irreducible]
def is_weekend (d : Day) : Bool
  := solution!
    (match d with
    | .saturday => true
    | .sunday => true
    | _ => false
    )

unseal is_weekend
example : is_weekend .sunday = true := solution!(by rfl)
example : is_weekend .friday = false := solution!(by rfl)
seal is_weekend
```
:::dev
RAB, to NH: 1/2 new exercises to grade. Thanks!
:::

:::grade
```
GRADE_THEOREM 1: is_inversion
```
:::
::::

::::exercise (rating := 1) (name := "is_inversion")
Define a function that takes two colors and returns `true` if
the second color is an _inversion_ of the first, and false otherwise.

Inversion is defined by cases:
Black is an inversion of white, and vice versa.
Red is an inversion of blue, and vice versa.
Green is not an inversion of anything.

```lean
@[irreducible]
def is_inversion (c1 c2 : Color) : Bool
  := solution!
    (match c1, c2 with
    | .black, .white => true
    | .white, .black => true
    | .primary .red, .primary .blue => true
    | .primary .blue, .primary .red => true
    | _, _ => false
    )

unseal is_inversion
example : is_inversion .black .white = true := solution!(by rfl)
example : is_inversion .white .black = true := solution!(by rfl)
example : is_inversion (.primary .red) (.primary .blue) = true := solution!(by rfl)
example : is_inversion (.primary .green) (.primary .red) = false := solution!(by rfl)
seal is_inversion
```
:::dev
RAB, to NH: 2/2 new exercise to grade
:::

:::grade
```
GRADE_THEOREM 1: is_inversion
```
:::
::::

## Namespaces

::::full
Lean provides a _namespace system_ to aid in organizing large
developments. If we enclose a collection of declarations in
`namespace X ... end X`, then, in the rest of the file after the
`end`, these definitions will be referred to by names like `X.foo`
instead of just `foo`. In this book, we will use this feature to
limit the scope of definitions so that we are free to reuse names
from the standard library so we can redefine them and learn about
how they work. In large Lean developments, namespaces are
used to organize definitions and theorems the same way
modules are used in other programming languages.
::::

:::terse
`namespace` declarations create separate namespaces.
:::

```lean
def myFoo : Bool := true
namespace Playground
def myFoo : RGB := RGB.blue
end Playground

#check myFoo             -- Bool
#check Playground.myFoo  -- RGB
```

::::exercise(rating:=0) (name := "custom_namespace_checks")
Predict the output of each of these statements below.
Do you think their results will change depending on which `namespace`
they are in? How?

#check .black -- Write your prediction here.
#check Color.black -- Write your prediction here.
#check RGB -- Write your prediction here.
#check NatPlayground.myFoo -- Write your prediction here.

Once you have written your predictions, copy the lines from the comment into
an active section of the book to evaluate them.
::::

:::dev
RAB: This seems like a reasonable exercise; I'm not quite sure if/how we should grade it?
BCP: Not all exercises need to be graded.  (In Rocq we had a notation for manually graded exercises. An optional and manually graded exercise would serve for this.)
:::

::::full
When inside a `namespace` region, definitions from the same
namespace can be referenced without prefixes. When a `namespace`
shares the same name as a type, definitions on that type are
available inside the `namespace` without a prefix. In the example
below, we can use the `blue` constructor without a `.` because
we are inside the `RGB` `namespace`, which is the same as `blue`'s type.
::::

```lean
namespace RGB
def myBlue : RGB := blue
end RGB
```

::::full
Top-level definitions can also be prefixed by a namespace to put
them in the namespace "from the outside," without having to open and
close it.
::::

```lean
--- this works, because the definition is qualified by `RGB.`
def RGB.myOtherBlue : RGB := myBlue

#check RGB.myBlue      -- RGB
#check RGB.myOtherBlue -- RGB
```

#check myBlue -- unknown identifier

::::full
When we do this, definitions inside that namespace are available without
qualification. So, for example, we could write the definition of `nextWorkingDay''`
earlier inside the `Day` namespace like so:
::::

```lean
def Day.nextWorkingDay'' (d : Day) : Day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
```

::::full
We can also use `open` to bring the definitions of a namespace into
the current scope; after that, we can refer to any of the namespace's
definitions without a prefix.
::::

```lean
namespace MyNamespace
def myDef : Bool := true
end MyNamespace

open MyNamespace

#check myDef -- Bool
```

## Constructors with Multiple Parameters

```lean
namespace Playground
```

::::full
A single constructor with multiple parameters can be used to create
a tuple type. As an example, consider representing the four bits in
a nibble (half a byte). We first define a datatype `Bit` that
resembles `Bool` (using the constructors `b1` and `b0` for the two
possible bit values) and then define the datatype `Nibble`, which is
a tuple of four bits.
::::

:::terse
A Nibble is half a byte -- four bits.
:::

```lean
inductive Bit : Type where
  | b1
  | b0

inductive Nibble : Type where
  | bits (x0 x1 x2 x3 : Bit)

#check (.bits .b1 .b0 .b1 .b0 : Nibble)
```

::::full
Note: The `bits` constructor illustrates a feature of multi-parameter
declarations, both for constructors and for functions: Instead
of writing `(x0 : Bit) (x1 : Bit) ...` we write `(x0 x1 ... : Bit)`
since all of the variables have the same type. We could have done
the same with the function definition `orb` above, writing
`orb (b1 b2 : MyBool)` rather than `orb (b1 : MyBool) (b2 : MyBool)`.

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

## Natural Numbers

::::full
We put this portion of the chapter in a namespace so that our own definition of
numbers does not interfere with the one from the standard library.
In the remainder of the book, we'll use the standard library's.
::::


```lean
namespace NatPlayground
```

::::full
All the types we have defined so far -- both "enumerated types"
such as `Day`, `Bool`, and `Bit` and tuple types such as
`Nibble` built from them -- are finite. The natural numbers, on
the other hand, are an infinite set, so we'll need to use a
slightly richer form of type declaration to represent them.

There are many representations of numbers to choose from. You are
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
natural number `n`, yielding the representation of `n+1`, where
`succ` stands for "successor." The number `n` is then represented by
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

Naturally, Lean has its own definition of natural numbers,
with some slightly fancy features for reasoning and
notation. As we are just beginning to reason about natural numbers,
we use our own definition here and introduce the Lean one in a later chapter.

We'll define some shorthands for numbers, `open`ing the `Nat` namespace
so we don't need to use `.` notation everywhere.

```lean
namespace Nat

def one   : Nat := succ zero
def two   : Nat := succ one
def three : Nat := succ two
def four  : Nat := succ three
```

We can also write functions on `Nat`.

```lean
@[irreducible]
def pred (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ n' => n'

@[irreducible]
def minustwo (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ (zero) => zero
  | succ (succ n') => n'

#eval minustwo four
```

::::full
You may wonder what the `@[irreducible]` means in the definitions above,
or the `seal` and `unseal` that we use in the examples below.
Hold onto this question; we will explain shortly.
::::

::::full

Look the types of `succ`, `pred`, and `minustwo`:

```lean
#check succ  -- Nat → Nat
#check Nat.pred  -- Nat → Nat
#check minustwo  -- Nat → Nat
```

These are all things that can be applied to a number to yield a
number. However, there is a fundamental difference between
`Nat.succ` and the other two: functions like `Nat.pred` and
`Nat.minustwo` are defined by giving _computation rules_ -- e.g.,
the definition of `Nat.pred` says that `Nat.pred (succ (succ zero))`
can be simplified to `succ zero` -- while the definition of
`Nat.succ` has no such behavior attached. Although it is like a
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
Recursive functions:
:::

```lean
@[irreducible]
def even (n : Nat) : Bool :=
  match n with
  | zero => true
  | succ (zero) => false
  | succ (succ n') => even n'

unseal even
example : even one = false  := by rfl
example : even four = true := by rfl
seal even
```

:::slidebreak
:::

We could define `odd` by a similar recursive declaration, but
here is a simpler way:

```lean
@[irreducible]
def odd (n : Nat) : Bool :=
  not (even n)

unseal odd even
example : odd one = true  := by rfl
example : odd four = false := by rfl
seal odd even
```

:::slidebreak
:::

:::terse
A multi-parameter recursive function.
:::

```lean
@[irreducible]
def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m')
```

```lean
#eval add one two -- succ (succ (succ zero)) -- aka, three!
```

::::full
We can also define infix notation for our `add` functions.
Don't worry too much about how this is defined; we will return to it
in more detail later.
::::
```lean
scoped infixl:65 " + " => add
```
```lean
#eval one + two -- succ (succ (succ zero)) -- aka, three again.
```

# Proof by Rewriting

## Proving properties about functions in Lean

::::full
Being recursive, `add` is our first example of a more sophisticated
class of functions. In this chapter and beyond, we will _prove_
properties about recursive functions like `add` over inductive
datatypes like `Nat` using _simplification rules_ about their
behavior.

Here is a simple rule about `add`:

- `n + zero = n`

In Lean, this rule looks like this:
::::

```lean
unseal add in
theorem add_zero : ∀ n : Nat, n + zero = n := by
  intro n
  rfl
```

:::dev
BCP: The flow here is rough
  - need to explain ∀ in the statement (and `theorem` and `add_zero`)
  - need to explain "by", "intro n", and "rfl" in the proof
  - what about `unseal`? if we really need it, it has to be explained!
  - the comment below will need to change a bit
  - We should also comment, as soon as it's relevant, on the binder
    form vs. the ∀ form for introducing variables.  Why do we use
    the ∀ form here?  Could we switch to the binder form?
RAB: We desperately need a way for this not to be the introduction to proof.
Explaining it away with "don't worry" feels painful. Can we hide the definition,
or do _something_ to make sure we're not having to explain ∀ , intro, by, etc.
here?
:::

::::full
```lean
#check add_zero
```

:::dev
BCP: We will probably want to remove the "NatPlayground" stuff from
all these comments when we fix the printing.
RAB: Yes! Someone please let us know how!
:::

We can then use the `add_zero` rule to carry out a simple proof
about natural numbers!

```lean
theorem add_zero_zero : ∀ n : Nat, n + zero + zero = n := by
  intro n
  rewrite [add_zero]
  rewrite [add_zero]
  rfl

-- Let's walk through this proof.
```
::::

## Proof state and tactics

::::full
Commands like `intro n`, `rewrite`, `rfl`, etc. are called
_tactics_. The `add_zero` in brackets is an _argument_ to the
`rewrite` tactic.

Hovering with the cursor over each line of the proof, we can see the
_proof state_ in the Lean InfoView panel.

The proof state is divided into the _context_, before the ⊢,
and the _goal_, after the ⊢. The context records what we know
at each point in the proof;the goal is what we are trying to prove
at each point.

A tactic manipulates both the goal and the context to get the goal
into a shape that is closer to the one we want. A tactic can also
_close_ (solve) the current goal which finishes its proof.

Let's walk through the example above with this terminology in mind.

```lean
theorem add_zero_zero_explained : ∀  n : Nat, (n + zero) + zero = n := by
  /- Move your cursor (click) here to see the initial proof state in
     the InfoView. The context (before the ⊢) is empty.
     The goal is `∀ (n : Nat), (n + zero) + zero = n`. -/
  intro n
  /- Now click here to see the new proof state that results from the
     tactic. Notice how `intro n` has changed the _context_: it now
     contains `n : Nat`.

    The `intro` tactic is used to name variables _quantified_ by a
    ∀ (pronounced "forall", typed \all or \forall.) Since we are
    trying to prove a property of all natural numbers, we
    proceed by introducing an unknown natural number `n` and prove
    the property holds for `n`.  Informally, this move can be read,
    "We want to prove <some property> for all numbers `n`. So suppose
    `n` is some arbitrary number... <and then go on to prove the
    property for this particular `n`>..." Since `n` was chosen
    arbitrarily, we've now proved the property for all `n`.

    A proof of a theorem beginning with a ∀ will typically start with
    an `intro`.
  -/
  rewrite [add_zero]
  /- Now click here to see the new proof state that results from the tactic.
     Notice how `(n + zero) + zero` changes to `n + zero` in the goal. -/
  rewrite [add_zero]
  /- Again the goal changes, from `n + zero` to `n`. Now the proof state
     is an equality with both sides equal, so it can be closed by the
     tactic `rfl`. -/
  rfl
  /- The proof is now done! The Lean InfoView tells us there are "No goals". -/

/-! Here's a simple proof for you to try. -/

theorem add_zero_zero_zero : ∀ n : Nat, n + zero + zero + zero = n := by
  solution!
    intro n
    rewrite [add_zero]
    rewrite [add_zero]
    rewrite [add_zero]
    rfl
```
::::

## The `rewrite` tactic

::::full
  As we saw above, the tactic that tells Lean to rewrite (part of) a goal or
  hypothesis based on a rule is called `rewrite`. Given the rule `add_zero`,
  which states that `n + zero` is equal to `n` for any `n`, we can replace
  any `n + zero` in our proof with `n` via `rewrite [add_zero]`.

  The `rewrite` tactic takes its argument(s) in square brackets.
::::

## The `rfl` tactic

::::full
 The `rfl` tactic closes a goal of the shape `a = a`, for any `a`. It
 checks that both sides of the equality are _definitionally equal_ --
 that is, that they reduce to the same thing. (So, in particular, a
 term is always definitionally equal to itself.)
::::

## A New `add` Rule

::::full
   Here is another fundamental rule about addition:

   `n + (succ m) = succ (n + m)`.

   This is the rule we need to push `succ` around.

Here it is in Lean:

```lean
unseal add in
theorem add_succ : ∀ n m : Nat, n + (succ m) = succ (n + m) := by
  intro n m
  rfl
```

And here it is in a proof:

```lean
theorem add_one (n : Nat) : n + (succ zero) = succ (n + zero) + zero := by
  rewrite [add_succ]
  rewrite [add_zero]  /- notice how this handles an addition on both sides -/
  rewrite [add_zero]
  rfl
```

Again, we recommend stepping through these proofs in VS Code --
   that is, moving past each tactic with your cursor to see how it
   changes the proof state.
::::

## Irreducibility, Rewriting, and Proof Engineering

::::full
The definitions and proofs above use a few somewhat mysterious conventions:
we write `@[irreducible]` above some of our definitions, and we
write `unseal` before some of our proofs and `seal` after them.
These are not things you will usually see in real Lean developments;
however, we use them i this book to enforce a particular convention
to help you build good Lean habits.

Lean, like any other programming language, has conventions and best practices
for writing good software. You are probably familiar with object oriented programming,
for example, in which it is considered good practice not to access the
fields of an object directly, but instead to use getter and setter methods.
This helps to encapsulate the object's definition, so that, if its fields or implementation
change, the interface it exposes to the outside world remains the same.

The same principle applies to definitions proofs in Lean.
In idiomatic Lean, it is considered poor style to "peek" through
definitions by using `rfl` to implicitly simplify expressions
that aren't syntactically identical. If you take a look at the proofs of
`add_zero` and `add_succ` above, you will notice this is exactly what we did
when we used the `rfl` tactic.

In this text, to enforce idiomatic style, we mark
definitions with `@[irreducible]` to prevent this peeking,
also called *definitional equality abuse* (*defeq abuse*, for short).
The `unseal` we wrote before the proof of `add_zero` temporarily
allows this, but only in that proof. We allow unsealing the definition
for `add_zero` and `add_succ`, but then expect that from this point on,
these foundational theorems should provide a characterization of the behavior
of `add` that makes further unsealing unnecessary. Instead,
we can rewrite by these theorems anywhere we want to describe how `add`
evaluates. The motivation for this strict discipline is both readability
and performance; unfolding definitions can have negative effects as libraries scale.

:::dev
BCP: We start by saying that what we're going to here is not what real lean developments do, but then
explain why what we're doing in a way that makes it sound like it is (or should be) standard. And we
never say what is the style that we *don't* do (but that standard Lean practice does).
RAB: This will (hopefully) be addressed by our decision on hiding these
definitions. Even if not, it seems odd to discuss how to write this section
before we make that choice.
:::

These two theorems also follow a particular pattern. Let's look again at the
definition of `add`:

```lean
namespace AddPlayground
/- repeating the definition here for ease of reference:
def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m') -/

unseal add in
theorem add_zero : forall (n : Nat), n + zero = n := by
  intro n
  rfl

unseal add in
theorem add_succ : forall (n m : Nat), n + (succ m) = succ (n + m) := by
  intro n m
  rfl

end AddPlayground
```

Each of `add_zero` and `add_succ` correspond to one branch of the `match`
statement defining `add` and describe how the evaluation of `add` proceeds
in that case. The `add_zero` theorem describes how `n + zero` evaluates,
while `add_succ` describes (symbolically) how `n + succ m` evaluates.
Because these theorems describe how to simplify more complex expressions
involving `add`, we call them _simplification lemmas_ for `add`.

These are instances of a general pattern: each definition
 operating over enumerated types like `Nat`, `Bool`, `Day`, or `Color`
needs a simplification lemma for each branch of control flow through
the function.

So, for example, we need two simplification lemmas for the definition of `pred`:

```lean
unseal Nat.pred in
theorem pred_zero : Nat.pred zero = zero := by rfl

unseal Nat.pred in
theorem pred_succ n : Nat.pred (succ n) = n := by rfl
```

Similarly, for each of the three branches of the definition of `even`,
we need one simplification lemma:

```lean
unseal even
theorem even_zero : even zero = true := rfl
theorem even_one : even (succ zero) = false := rfl
theorem even_succ_succ n : even (succ (succ n)) = even n := rfl
seal even
```

In the remainder of this textbook, we will pair definitions
with their simplification lemmas. After proving these lemmas, instead of using `rfl`
to peek through the definitions, we will prefer rewriting
by the lemmas, using `@[irreducible]` to enforce this policy,
and only `unseal`ing the definition in the proofs of those lemmas themselves.
::::

## Working with Numerals

:::dev
BCP: The following lemmas are also needed by the TERSE version,
so I am un-fulling them for now.
But indeed the whole discussion here needs both TERSE and FULL versions.
Or probably some of it should turn into an exercise?
RAB: This will be part of our discussion on presenting laws.
:::

We know from our definitions above that `one` is just `succ zero`,
`two` is `succ one`, and so on. We can write rules for these equalities too:

```lean
theorem one_eq_succ_zero : one = succ zero := by rfl
theorem two_eq_succ_one : two = succ one := by rfl
theorem three_eq_succ_two : three = succ two := by rfl
theorem four_eq_succ_three : four = succ three := by rfl
```

We can rewrite with these rules to expand numerals into their definitions,
   which allows us to use our `add` rules.
Here's an example of how to start a proof this way.
Finish the proof using the `add` rules:

:::dev
BCP: Should this be marked / formatted as an exercise or at least a WORKINCLASS?
RAB: Let's decide once we choose how to present the laws.
     My intuition is yes.
:::

```lean
theorem one_plus_one_eq_two : (one + one : Nat) = two := by
  rewrite [one_eq_succ_zero]
  solution!
    rewrite [add_succ]
    rewrite [add_zero]
    rfl
```

Try the same for `two + two = four`.

```lean
theorem two_plus_two_eq_four : two + two = four := by
  solution!
    rewrite [four_eq_succ_three, three_eq_succ_two,
             two_eq_succ_one, one_eq_succ_zero]
    rewrite [add_succ, add_succ, add_zero]
    rfl
```

::::full
Now that we know how addition is defined, we can use it to define multiplication:
::::

:::slidebreak
:::

```lean
@[irreducible]
def mul (n m : Nat) : Nat :=
  match m with
  | zero => zero
  | succ m' => (mul n m') + n

scoped infixl:70 " * " => mul
```

Multiplication, like any function we will prove properties about,
   also has simplification rules.

```lean
unseal mul in
theorem mul_zero : ∀ n : Nat, n * zero = zero := by
  intro n
  rfl

unseal mul add in
theorem mul_succ : ∀ n m : Nat, n * (succ m) = (n * m) + n := by
  intro n m
  rfl
```

:::dev
BCP: Again, this should be an exercise.
RAB: Agreed if we're keeping these visible; putting off
     small decision until large decision is made.
:::

Prove this property. (We have given you the first line.) Notice how `rewrite`
   can take any number of arguments. You can use this rewrite with all of the
   numeral rules at once, for example.

   After each rewrite, check the proof state by placing the cursor immediately
   after a rule to see how the goal is changing. This happens naturally
   as you write the proof, which makes it convenient to use `rewrite` blocks
   with multiple rules.

```lean
theorem test_mult1 : (two * two : Nat) = four := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  solution!
    rewrite [mul_succ, mul_succ, mul_zero]
    rewrite [add_succ, add_succ, add_zero]
    rewrite [add_succ, add_succ, add_zero]
    rfl
```

:::slidebreak
:::

We can pattern-match two values at the same time:

:::slidebreak
:::

When we say that Lean comes with almost nothing built-in, we really
mean it: even testing equality is a user-defined operation!

Here is a function `beq` that tests natural numbers for
equality, yielding a boolean.

```lean
@[irreducible]
def beq (n m : Nat) : Bool :=
  match n with
  | zero => match m with
            | zero => true
            | succ _ => false
  | succ n' => match m with
               | zero => false
               | succ m' => beq n' m'
```

:::slidebreak
:::

:::dev
TODO: We need to make a decision about `==`.
Either we give decidable equality early, or we use this `==` thing.
RAB: This is the other thing we need to decide on together.
:::

Similarly, the `leb` function tests whether its first argument is
less than or equal to its second argument, yielding a boolean.

```lean
@[irreducible]
def leb (n m : Nat) : Bool :=
  match n with
  | zero => true
  | succ n' =>
      match m with
      | zero => false
      | succ m' => leb n' m'

unseal leb
theorem zero_leb (n : Nat) : leb zero n = true := by rfl
theorem succ_leb_zero (n : Nat) : leb (succ n) zero = false := by rfl
theorem succ_leb_succ (n m : Nat) : leb (succ n) (succ m) = leb n m := by rfl

example : leb two two = true  := by rfl
example : leb two four = true  := by rfl
example : leb four two = false := by rfl
seal leb
```

We'll be using `leb` a lot, so let's give it an infix notation too.

```lean
scoped infixl:55 " <? " => leb
```

:::slidebreak
:::

We'll be using `beq` a lot, so let's give it an infix notation.

```lean
scoped infixl:30 " == " => beq
```

::::full
We can also now define the simplification lemmas for `beq` with this new notation,
one for each of the four cases of control flow through the function.
::::

```lean
unseal beq
theorem zero_zero_beq_true : (zero == zero) = true := by rfl
theorem zero_succ_beq_false (n : Nat) : (zero == (succ n)) = false := by rfl
theorem succ_zero_beq_false (n : Nat) : ((succ n) == zero) = false := by rfl
theorem succ_succ_beq (n m : Nat) : ((succ n) == (succ m)) = (n == m) := by rfl
seal beq
```

::::full
We now have two symbols that both look like equality: `=`
and `==`.  We'll have much more to say about their differences and
similarities later. For now, the main thing to notice is that
`x = y` is a logical _claim_ -- a "proposition" -- that we can try to
prove, while `x == y` is a boolean _expression_ whose value (either
`true` or `false`) we can compute.
::::

::::exercise (rating := 1) (name := "ltb")
Define a less-than function in terms of `leb`.

```lean
@[irreducible]
def ltb (n m : Nat) : Bool
  := solution!(leb (succ n) m)

unseal ltb leb
example : ltb two two = false := solution!(by rfl)
example : ltb two four = true  := solution!(by rfl)
example : ltb four two = false := solution!(by rfl)
seal ltb leb
```

:::grade
```
GRADE_THEOREM 1: ltb_test3
```
:::
::::

# General Proofs about Natural Numbers

:::terse
A (slightly) more interesting theorem:
:::


::::full
We now begin to make claims about _general_ natural numbers.

We begin by making a universal claim about all numbers `n` and `m` that are
equal to each other (`n = m`). The arrow symbol is pronounced "implies."
Enter it with `\to` or `\->` or `\r`.

The `intro` tactic moves the universally quantified variables and the
hypothesis into the context, giving them names.  The goal is now to prove
`n + n = m + m` under the assumption `h : n = m`.

The tactic that tells Lean to perform replacement is one we have seen
before: `rewrite`. It can take a hypothesis from the context as an argument,
just like it can take a previously proved theorem.  In this case, we want to
rewrite with the hypothesis `h`, which says that `n` and `m` are equal, so
that we can replace `n` with `m` in the goal.

After the rewrite, the goal is `m + m = m + m`, which can be closed by
`rfl`.
::::

```lean
theorem add_id_example : ∀ n m : Nat,
    n = m → n + n = m + m := by
  intro n m
  intro h
  rewrite [h]
  rfl
```

:::terse
We make a general claim about natural numbers and prove it
:::

::::exercise (rating := 1) (name := "add_id_exercise")
Remove `sorry` and fill in the proof.

```lean
theorem add_id_exercise : ∀ n m o : Nat,
    n = m → m = o → n + m = m + o := by
  solution!
    intro n m o h1 h2
    rewrite [h1, h2]
    rfl
```

:::grade
```
GRADE_THEOREM 1: add_id_exercise
```
:::
::::

::::full
The `sorry` here tells Lean that we want to skip trying
to prove this theorem and just accept it as a given.  This is
often useful for developing longer proofs.

Be careful, though: every time you say `sorry` you are leaving
a door open for total nonsense to enter Lean's safe, formally
checked world!
::::

```lean -keep
theorem really_bad : one = two := by sorry
```

:::slidebreak
:::

The `#check` command can also be used to examine the statements of
previously declared lemmas and theorems.

```lean
#check mul_zero  -- ∀ (n : Nat), n * 0 = 0
#check mul_succ  -- ∀ (n m : Nat), n * Nat.succ m = n + n * m
```

## Type Annotations (Optional)

:::dev
BCP: I don't think we should mark sections "Optional" in the middle of chapters.  People will
read them anyway, so it's just confusing -- and a temptation to write less clearly.
:::

::::full
Note that you may see a slight discrepancy in the output:
#check might show
`NatPlayground.Nat.mul_zero (n : Nat) : n * zero = zero`.
Qualification, like `mul_zero` to `NatPlayground.Nat.mul_zero`, can happen
automatically when printing a type in Lean.

Another simple but important-to-note automatic display feature is _indexing_:
`mul_zero : ∀ (n : Nat), n * zero = zero` may display as
`mul_zero  (n : Nat) : n * zero = zero`.

Note how the (n : Nat) has moved _before_ the colon and has lost the ∀.
The two definitions are equivalent for our purposes right now, and you will
find both in the Lean ecosystem.
::::

:::slidebreak
:::

We can use the `rewrite` tactic with a previously proved theorem
instead of a hypothesis from the context.

```lean
theorem add_mul_zero : ∀ p q : Nat,
    (p * zero) + (q * zero) = zero := by
  intro p q
  rewrite [mul_zero, mul_zero, add_zero]
  rfl
```

# Proof by Case Analysis

::::full
Of course, not everything can be proved by simple calculation and
rewriting: In general, the presence of unknown, hypothetical values
(arbitrary numbers, booleans, etc.) can block proof.
::::

:::terse
Sometimes simple calculation and rewriting are not enough...
:::

:::instructors
We use `#guard_msgs` in a number of places in the SFL
source files to help deter bit-rot, and you are encouraged to add
your own instances.  It doesn't need to be explained to students
because it gets stripped out when verso files are translated to
.lean and .html.
:::

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs(warning) in
example : ∀ n : Nat,
    (succ n == zero) = false := by
  intro n
  /-
    We can't rewrite by any lemmas here because `n` is unknown!
  -/
  sorry
```

::::full
The tactic that tells Lean to consider separate cases is called
`cases`.
::::

:::terse
We can use `cases` to perform case analysis:
:::

```lean
theorem add_one_neb_zero : ∀ n : Nat,
    (succ n == zero) = false := by
  intro n
  cases n
  case zero =>
    rewrite [succ_zero_beq_false]
    rfl
  case succ n' =>
    rewrite [succ_zero_beq_false]
    rfl
```

::::full
The `cases` tactic generates _two_ subgoals, which we must
prove, separately, in order to get Lean to accept the theorem.

The generated subgoals are tagged by the names of the constructors.
`case zero =>` and `case succ n' =>` select which subgoal to work on next
and introduce variable names.

The `cases` tactic can be used with any inductively defined
datatype.  For example, we use it next to prove that boolean
negation is involutive (that is, that negation is its own inverse).
::::

:::slidebreak
:::

:::terse
Another example, using booleans:
:::

```lean
theorem notb_involutive : ∀ b : Bool, (!!b) = b := by
  intro b
  cases b
  case false =>
    rewrite [Bool.not_false, Bool.not_true]
    rfl
  case true =>
    rewrite [Bool.not_true, Bool.not_false]
    rfl
```

:::slidebreak
:::

:::terse
We can have nested case analysis:
:::

```lean
theorem andb_commutative : ∀ b c : Bool,
    (b && c) = (c && b) := by
  intro b c
  cases b
  case true =>
    cases c
    case true =>
      rewrite [Bool.and_self]
      rfl
    case false =>
      rewrite [Bool.and_false, Bool.and_true]
      rfl
  case false =>
    cases c
    case true =>
      rewrite [Bool.and_true, Bool.and_false]
      rfl
    case false =>
      rewrite [Bool.and_self]
      rfl

theorem andb3_exchange : ∀ b c d : Bool,
    ((b && c) && d) = ((b && d) && c) := by
  intro b c d
  cases b
  case false =>
    cases c
    case true =>
      cases d
      case false =>
        rewrite [Bool.and_true, Bool.and_self]
        rfl
      case true =>
        rewrite [Bool.and_true]
        rfl
    case false =>
      cases d
      case false =>
        rewrite [Bool.and_self]
        rfl
      case true =>
        rewrite [Bool.and_self, Bool.and_true]
        rfl
  case true =>
    cases c
    case true =>
      cases d
      case false =>
        rewrite [Bool.and_self, Bool.and_false, Bool.and_true]
        rfl
      case true =>
        rewrite [Bool.and_self]
        rfl
    case false =>
      cases d
      case false =>
        rewrite [Bool.and_false]
        rfl
      case true =>
        rewrite [Bool.and_false, Bool.and_true, Bool.and_self]
        rfl
```

As you can see, proofs by cases can become very verbose.
  We will introduce some tactics for writing shorter proofs
  by case analysis in `Tactics.lean`.

## New Tactics: `rewrite ... at` and `exact`

Some new tactics will be useful for the exercises ahead.

The `rewrite` tactic can be used to rewrite in a hypothesis instead of the
goal. For example, if `h : P` is in the context and we have a rule `P = Q`,
then `rewrite [P = Q] at h` changes the hypothesis to `h : Q`.

The `exact` tactic closes a goal by providing the exact proof of the goal.  For
example, if `h : P` is in the context and the goal is `P`, then `exact h`
closes the goal.  You can also transform `h` slightly, but we will
explain how when we get to an example where we need to.

::::exercise (rating := 2) (name := "orb_false_true")
Prove the following claim.

Tip: the rewrite rule to simplify `(b || false)` is called `Bool.or_false`.

```lean
theorem orb_false_true : ∀ b : Bool,
    (b || false) = true → b = true := by
  solution!
    intro b h
    rewrite [Bool.or_false] at h
    exact h
```

:::grade
```
GRADE_THEOREM 2: orb_false_true
```
:::
::::

::::exercise (rating := 1) (name := "zero_nbeq_add_1")
```lean
theorem zero_neb_add_one : ∀ n : Nat,
  (zero == succ n) = false := by
  solution!
    intro n; cases n
    case zero => rewrite [zero_succ_beq_false]; rfl
    case succ n' => rewrite [zero_succ_beq_false]; rfl
```

:::grade
```
GRADE_THEOREM 1: zero_nbeq_add_1
```
:::
::::

## More on Notation (Optional)

::::full
Lean has a very flexible notation system.  Operators like `+` and `*`
are defined with specified precedence and associativity.  For example,
`+` has precedence 65 and is left-associative, while `*` has
precedence 70 and is also left-associative.  This means that `1+2*3*4`
is parsed as `1+((2*3)*4)`.

You can define custom notation using the `notation`, `infixl`,
`infixr`, `prefix`, and `postfix` commands.

Lean handles notation scoping through namespaces and _type classes_.
The numeric literal `3` can be interpreted as `Nat`, `Int`, `Float`, etc.,
depending on the expected type, thanks to Lean's `OfNat` type class.
We explain type classes in full in Typeclasses chapter,
found in `Typeclasses.lean`.

::::

## Structural Recursion (Optional)

::::full
Here is a copy of the definition of addition:

```lean
def add' (n : Nat) (m : Nat) : Nat :=
  match n with
  | zero => m
  | succ n' => succ (add' n' m)
```

When Lean checks this definition, it verifies that the recursion
terminates.  Specifically, it checks that one of the parameters
is _structurally decreasing_.  This implies that all calls to
`add'` will eventually terminate.

This requirement is a fundamental feature of Lean's design: In
particular, it guarantees that every function that can be defined
in Lean will terminate on all inputs.  However, because Lean's
termination analysis is not always able to figure things out
automatically, it is sometimes necessary to provide hints or
write functions in slightly different ways.
::::

::::exercise (rating := 2) (name := "decreasing")
To get a concrete sense of this, find a way to write a sensible
recursive definition (of a simple function on numbers, say) that
does actually terminate on all inputs, but that Lean will reject
because it cannot automatically prove termination.

:::solution
```
def factorial_bad (n : Nat) : Nat :=
  if n == 0 then 1
  else n * factorial_bad (n - 1)
This fails because Lean can't see that `n - 1` is structurally smaller.
```
:::
::::

## Binary Numerals

::::exercise (rating := 3) (name := "binary")
We can generalize our unary representation of natural numbers to
the more efficient binary representation by treating a binary
number as a sequence of constructors `b0` and `b1` (representing 0s
and 1s), terminated by a `z`.

For example:

| decimal |            binary     |                                                unary         |
|:-------:| ---------------------:| ------------------------------------------------------------:|
|    0    | `               z   ` | `                                               zero       ` |
|    1    | `            b1 z   ` | `                                          succ zero       ` |
|    2    | `        b0 (b1 z)  ` | `                                    succ (succ zero)      ` |
|    3    | `        b1 (b1 z)  ` | `                              succ (succ (succ zero))     ` |
|    4    | `    b0 (b0 (b1 z)) ` | `                        succ (succ (succ (succ zero)))    ` |
|    5    | `    b1 (b0 (b1 z)) ` | `                  succ (succ (succ (succ (succ zero))))   ` |
|    6    | `    b0 (b1 (b1 z)) ` | `            succ (succ (succ (succ (succ (succ zero)))))  ` |
|    7    | `    b1 (b1 (b1 z)) ` | `      succ (succ (succ (succ (succ (succ (succ zero)))))) ` |
|    8    | `b0 (b0 (b0 (b1 z)))` | `succ (succ (succ (succ (succ (succ (succ (succ zero)))))))` |

Note that the low-order bit is on the left and the high-order bit
is on the right -- the opposite of the way binary numbers are
usually written.  This choice makes them easier to manipulate.

(Comprehension check: What unary numeral does `b0 z` represent?)

```lean
inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)

@[irreducible]
def incr (m : Bin) : Bin
  := solution!(match m with
  | .z => .b1 .z
  | .b0 m' => .b1 m'
  | .b1 m' => .b0 (incr m'))

@[irreducible]
def binToNat (m : Bin) : Nat
  := solution!(match m with
  | .z => zero
  | .b0 m' => binToNat m' * two
  | .b1 m' => binToNat m' * two + one)

unseal incr
example : incr (.b1 .z) = .b0 (.b1 .z) := solution!(by rfl)
example : incr (.b0 (.b1 .z)) = .b1 (.b1 .z) := solution!(by rfl)
example : incr (.b1 (.b1 .z)) = .b0 (.b0 (.b1 .z)) := solution!(by rfl)

theorem incr_z : incr .z = .b1 .z := solution!(by rfl)
theorem incr_b0 m : incr (.b0 m) = .b1 m := solution!(by rfl)
theorem incr_b1 m : incr (.b1 m) = .b0 (incr m) := solution!(by rfl)
seal incr

unseal binToNat
theorem binToNat_z : binToNat .z = zero := solution!(by rfl)
theorem binToNat_b0 m : binToNat (.b0 m) = binToNat m * two := solution!(by rfl)
theorem binToNat_b1 m : binToNat (.b1 m) = binToNat m * two + one := solution!(by rfl)
seal binToNat
```

```lean
unseal Nat.mul Nat.add incr binToNat
example : binToNat (.b0 (.b1 .z)) = two := solution!(by rfl)
example : binToNat (incr (.b1 .z)) = add one (binToNat (.b1 .z)) := solution!(by rfl)
example : binToNat (incr (incr (.b1 .z))) = add two (binToNat (.b1 .z)) := solution!(by rfl)
example : binToNat (.b0 (.b0 (.b1 .z))) = four := solution!(by rfl)
seal Nat.mul Nat.add incr binToNat
```

:::grade
```
GRADE_THEOREM 0.5: incr_test1
```
:::

:::grade
```
GRADE_THEOREM 0.5: incr_test2
```
:::

:::grade
```
GRADE_THEOREM 0.5: incr_test3
```
:::

:::grade
```
GRADE_THEOREM 0.5: binToNat_test1
```
:::

:::grade
```
GRADE_THEOREM 0.5: binToNat_test2
```
:::

:::grade
```
GRADE_THEOREM 0.5: binToNat_test3
```
:::
::::

```lean
end Nat
```

# More Exercises

## Warmups

::::exercise (rating := 1) (name := "identity_fn_applied_twice")
You now have a small, but powerful, suite of tactics at your disposal.
As a warmup for the last section of the chapter, use the tactics you have
learned so far to prove the following theorem about boolean functions.

Hint: You can use `rewrite` with _any_ hypothesis that has an `=` in it
as long as the types line up.

```lean
theorem identity_fn_applied_twice : ∀ f : Bool → Bool,
    (∀ x : Bool, f x = x) → ∀ b : Bool, f (f b) = b := by
  solution!
    intro f h b
    rewrite [h, h]
    rfl
```

:::grade
```
GRADE_THEOREM 1: identity_fn_applied_twice
```
:::
::::

::::exercise (rating := 1) (name := "negation_fn_applied_twice")
Now state and prove a theorem `negation_fn_applied_twice` similar
to the previous one but where the hypothesis says that the
function `f` has the property that `f x = !x`.

```lean
-- SOLUTION
theorem negation_fn_applied_twice : ∀ f : Bool → Bool,
    (∀ x : Bool, f x = !x) → ∀ b : Bool, f (f b) = b := by
  intro f h b
  rewrite [h, h]
  cases b
  case true => rewrite [Bool.not_true, Bool.not_false]; rfl
  case false => rewrite [Bool.not_false, Bool.not_true]; rfl
-- END SOLUTION
```

:::grade
```
GRADE_MANUAL 1: negation_fn_applied_twice
```
:::
::::

::::exercise (rating := 3) (name := "andb_eq_orb")
Prove the following theorem.

```lean
theorem andb_eq_orb : ∀ b c : Bool, (b && c) = (b || c) → b = c := by
  solution!
    intro b c h
    cases c
    case true =>
      /-
        h : true && c = true || c, i.e., h : c = true
      -/
      rewrite [Bool.and_true, Bool.or_true] at h
      rewrite [h]
      rfl
    case false =>
      /-
        h : false && c = false || c, i.e., h : false = c
      -/
      rewrite [Bool.and_false, Bool.or_false] at h
      rewrite [h]
      rfl
```

:::grade
```
GRADE_THEOREM 3: andb_eq_orb
```
:::
::::

## Course Late Policies, Formalized

::::full
Suppose that a course has a grading policy based on late days,
where a student's final letter grade is lowered if they submit too
many homework assignments late.
::::

```lean
namespace LateDays
open scoped NatPlayground.Nat

-- Numeric literals (`9`, `17`, `21`) for our unary `Nat`.
@[reducible] def ofNat : _root_.Nat → Nat
  | .zero => .zero
  | .succ n => .succ (ofNat n)

instance (n : _root_.Nat) : OfNat Nat n := ⟨ofNat n⟩
```

::::full
First, we introduce a datatype for modeling the "letter" component
of a grade.
::::

```lean
inductive Letter : Type where
  | A | B | C | D | F
```

::::full
Then we define the modifiers -- a `natural` `A` is just a "plain"
grade of `A`.
::::

```lean
inductive Modifier : Type where
  | plus | natural | minus
```

::::full
A full `Grade`, then, is just a `Letter` and a `Modifier`.
In Lean, a combination of several values is called a _structure_.  The `structure`
keyword is used to define a new structure type.
::::

```lean
structure Grade where
  letter : Letter
  modifier : Modifier
```

::::full
We will want to be able to say when one grade is "better" than
another.  In other words, we need a way to compare two grades.  As
with natural numbers, we could define `bool`-valued functions
`grade_eqb`, `grade_ltb`, etc., and that would work fine.
However, we can also define a slightly more informative type for
comparing two values, as shown below.  This datatype has three
constructors that can be used to indicate whether two values are
"equal", "less than", or "greater than" one another.
::::

```lean
inductive Comparison : Type where
  | eq   -- "equal"
  | lt   -- "less than"
  | gt   -- "greater than"
```

::::full
Since we're in a namespace, we can open the relevant types to
avoid having to write `Letter.A`, etc.
::::

```lean
open Letter Modifier Comparison
```

::::full
Using pattern matching, it is not difficult to define the
comparison operation for two letters `l1` and `l2` (see below).
This definition uses a feature of `match` patterns: we can match
against _two_ values simultaneously by separating them and the
corresponding patterns with comma `,`.
This is simply a convenient abbreviation for nested pattern
matching.
::::

```lean
def letterComparison (l1 l2 : Letter) : Comparison :=
  match l1, l2 with
  | A, A => eq
  | A, _ => gt
  | B, A => lt
  | B, B => eq
  | B, _ => gt
  | C, A => lt
  | C, B => lt
  | C, C => eq
  | C, _ => gt
  | D, F => gt
  | D, D => eq
  | D, _ => lt
  | F, F => eq
  | F, _ => lt

example : letterComparison B A = lt := by rfl
example : letterComparison D D = eq := by rfl
example : letterComparison B F = gt := by rfl
```

::::exercise (rating := 1) (name := "letter_comparison")
```lean
theorem letterComparison_Eq : ∀ l : Letter,
    letterComparison l l = eq := by
  solution!
    intro l; cases l <;> rfl
```

:::grade
```
GRADE_THEOREM 1: letterComparison_Eq
```
:::
::::

```lean
def modifierComparison (m1 m2 : Modifier) : Comparison :=
  match m1, m2 with
  | plus, plus => eq
  | plus, _ => gt
  | natural, plus => lt
  | natural, natural => eq
  | natural, _ => gt
  | minus, minus => eq
  | minus, _ => lt
```

::::exercise (rating := 2) (name := "grade_comparison")
Here, we will need to access the fields of the `Grade` structure.
The field names are `letter` and `modifier`, so for a grade `g`,
we can write `g.letter` and `g.modifier` to access these fields.

```lean
def gradeComparison (g1 g2 : Grade) : Comparison
  := solution!(match letterComparison g1.letter g2.letter with
  | lt => lt
  | eq => modifierComparison g1.modifier g2.modifier
  | gt => gt)

example : gradeComparison ⟨A, minus⟩ ⟨B, plus⟩ = gt := solution!(by rfl)
example : gradeComparison ⟨A, minus⟩ ⟨A, plus⟩ = lt := solution!(by rfl)
example : gradeComparison ⟨F, plus⟩ ⟨F, plus⟩ = eq := solution!(by rfl)
example : gradeComparison ⟨B, minus⟩ ⟨C, plus⟩ = gt := solution!(by rfl)
```

:::grade
```
GRADE_THEOREM 0.5: gradeComparison_test1
```
:::

:::grade
```
GRADE_THEOREM 0.5: gradeComparison_test2
```
:::

:::grade
```
GRADE_THEOREM 0.5: gradeComparison_test3
```
:::

:::grade
```
GRADE_THEOREM 0.5: gradeComparison_test4
```
:::
::::

```lean
def lowerLetter (l : Letter) : Letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F  -- Can't go lower than F!
```

::::full
This theorem is not provable because of the edge case of `F`!

```
theorem lowerLetter_lowers_bad : ∀ (l : Letter),
  letterComparison (lowerLetter l) l = lt := by ...
```
::::

```lean
theorem lowerLetter_F_is_F : lowerLetter F = F := by rfl
```

::::exercise (rating := 2) (name := "lower_letter_lowers")
```lean
theorem lowerLetter_lowers : ∀ l : Letter,
    letterComparison F l = lt →
    letterComparison (lowerLetter l) l = lt := by
  solution!
    intro l h
    cases l with
    | A => rfl
    | B => rfl
    | C => rfl
    | D => rfl
    | F => exact h
```

:::grade
```
GRADE_THEOREM 2: lowerLetter_lowers
```
:::
::::

::::exercise (rating := 2) (name := "lower_grade")
In addition to the dot notation for accessing structure fields, we can also
use pattern matching to access these fields.
For example, if `g` is a grade, then we can write
`match g with ⟨l, m⟩ => ...` to access the letter and modifier components
of `g` as `l` and `m`, respectively.
Note: The angle brackets `⟨` and `⟩` are typed as `\<` and `\>`.

```lean
def lowerGrade (g : Grade) : Grade
  := solution!(match g with
  | ⟨l, plus⟩ => ⟨l, natural⟩
  | ⟨l, natural⟩ => ⟨l, minus⟩
  | ⟨F, minus⟩ => ⟨F, minus⟩
  | ⟨l, minus⟩ => ⟨lowerLetter l, plus⟩)

example : lowerGrade ⟨A, plus⟩ = ⟨A, natural⟩ := solution!(by rfl)
example : lowerGrade ⟨A, natural⟩ = ⟨A, minus⟩ := solution!(by rfl)
example : lowerGrade ⟨A, minus⟩ = ⟨B, plus⟩ := solution!(by rfl)
example : lowerGrade ⟨B, plus⟩ = ⟨B, natural⟩ := solution!(by rfl)
example : lowerGrade ⟨F, natural⟩ = ⟨F, minus⟩ := solution!(by rfl)
example : lowerGrade (lowerGrade ⟨B, minus⟩) = ⟨C, natural⟩ := solution!(by rfl)
example : lowerGrade (lowerGrade (lowerGrade ⟨B, minus⟩)) = ⟨C, minus⟩ := solution!(by rfl)

theorem lowerGrade_F_Minus : lowerGrade ⟨F, minus⟩ = ⟨F, minus⟩ := solution!(by rfl)
```

:::grade
```
GRADE_THEOREM 0.25: lowerGrade_A_Plus
```
:::

:::grade
```
GRADE_THEOREM 0.25: lowerGrade_F_Minus
```
:::
::::

::::exercise (rating := 3) (name := "lower_grade_lowers")
:::dev
For our solution we use:

- Working on multiple match cases with `| _ ... | _ => ...`;
- Working on all remaining goals with `all_goals`.
- These are not expected of students at this point.
:::

```lean
theorem lowerGrade_lowers : ∀ g : Grade,
    gradeComparison ⟨F, minus⟩ g = lt →
    gradeComparison (lowerGrade g) g = lt := by
  solution!
    intro g h
    match g with
    | ⟨l, plus⟩ =>
      rw [lowerGrade, gradeComparison]
      rewrite [letterComparison_Eq]
      rw [modifierComparison]
    | ⟨l, natural⟩ =>
      rw [lowerGrade, gradeComparison]
      rewrite [letterComparison_Eq]
      rw [modifierComparison]
      intro x
      contradiction
    | ⟨l, minus⟩ =>
      cases l
      case F => rewrite [lowerGrade_F_Minus]; exact h
      all_goals rfl
```

:::dev
RAB: in removing `dsimp` from these proofs, I found
that you might need the `contradiction` tactic here instead,
or some other reasoning that's not accomplishable
with the tactics we've introduced so far. Can you make this
proof work with only `rw`, `rfl`, `exact`, etc?
:::

:::grade
```
GRADE_THEOREM 3: lowerGrade_lowers
```
:::
::::

```lean
def applyLatePolicy (lateDays : NatPlayground.Nat) (g : Grade) : Grade :=
  if lateDays <? 9 then g
  else if lateDays <? 17 then lowerGrade g
  else if lateDays <? 21 then lowerGrade (lowerGrade g)
  else lowerGrade (lowerGrade (lowerGrade g))

theorem applyLatePolicy_unfold : ∀ (lateDays : NatPlayground.Nat) (g : Grade),
    applyLatePolicy lateDays g
    =
    (if lateDays <? 9 then g
     else if lateDays <? 17 then lowerGrade g
     else if lateDays <? 21 then lowerGrade (lowerGrade g)
     else lowerGrade (lowerGrade (lowerGrade g))) := by
  intro _ _; rfl
```

::::exercise (rating := 2) (name := "no_penalty_for_mostly_on_time")
```lean
theorem no_penalty_for_mostly_on_time : ∀ (lateDays : NatPlayground.Nat) (g : Grade),
    (lateDays <? 9 = true) →
    applyLatePolicy lateDays g = g := by
  solution!
    intro lateDays g h
    rw [applyLatePolicy]
    rewrite [h]; rfl
```

:::grade
```
GRADE_THEOREM 2: no_penalty_for_mostly_on_time
```
:::
::::

::::exercise (rating := 2) (name := "grade_lowered_once")
```lean
theorem grade_lowered_once : ∀ (lateDays : NatPlayground.Nat) (g : Grade),
    (lateDays <? 9 = false) →
    (lateDays <? 17 = true) →
    applyLatePolicy lateDays g = lowerGrade g := by
  solution!
    intro lateDays g h9 h17
    rw [applyLatePolicy]
    rewrite [h9, h17]; rfl
```

:::grade
```
GRADE_THEOREM 2: grade_lowered_once
```
:::
::::

```lean
end LateDays
```
:::dev
RAB: If we are to have this exercise, we must either
make the functions irreducible or teach about
`rw` of a reducible definition.
We also have to figure out how to make lowerGrade\_lowers
go through without `dsimp` or `contradiction`. To discuss.
:::
