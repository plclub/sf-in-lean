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
(BCP: Actually, in 2025 this file alone took me two full hours.)
(BCP: This estimate may need to be revised now that we are in Lean!)

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
In Lean, we can build practically everything from first principles...
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
need in this course, rather than just referring to the standard
library. However, we will take care to harmonize those definitions
with the ones in the standard library, so that, by the time you are
finished the course, you will have a good grasp of how the standard
library is organized.
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
wonder if this is necessary. Lean doesn't allow patterns like `monday`, to avoid
name shadowing, because being explicit about names is _especially_
important to avoid confusion and headaches when writing proofs.
If we wish to be a bit more concise, we can use a syntax with just a `.`,
like `.monday`, that lets us know we're qualifying a name
without having to type too much. A more concise (but equivalent) definition
of `nextWorkingDay` is given below.

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

:::dev
BCP: I'm persistently confused by this explanation.  We start out saying that
being explicit is very important, but then we say that the shorter syntax
is fine.  I feel like this is an instance where trying not to overwhelm readers
with too much detail is actually leading to more confusion.  Maybe we should
just explain what's going on.
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
(We show Lean's responses in comments; if you have a computer
handy, this would be an excellent moment to fire up VS Code with
the Lean extension and try it for yourself.  Load this file,
`Basics.lean`, from the book's Lean sources, find the above
example, and observe the result in the Lean InfoView panel.)

:::dev
DHS: Where are we showing responses in comments? I don't see thems
:::
::::

## Aside: Using the VS Code Lean Extension

::::full
In VS Code, development of Lean code is supported by
the Lean Extension, which provides an interactive "InfoView" panel that
displays the results of commands like `#eval` and `#check`, as well as the
current goal state when working on proofs. You can hover over expressions in
the source code to see their types, and you can click on the results in the
InfoView to navigate to their definitions. This makes it easier to understand
how your code is being interpreted by Lean and to debug any issues that
arise.

The InfoView always follows your cursor, and Lean typechecks the file as you
edit it, so you can see the results of your changes immediately. You can also
use the InfoView to explore the definitions of functions and types that
you're using, which can be very helpful for understanding how they work.

If you haven't already, install the Lean Extension in VS Code and open the
`Basics.lean` file to see the InfoView in action. Try hovering over the
`nextWorkingDay` function and the `Day` type to see their definitions, and
experiment with adding your own `#eval` commands to test other inputs.

For `#eval` and other commands, we show Lean's responses in comments; if you
hover over the `#eval` commands above, you will see the popup that contains
the output should match what's in the comment below. Experiment with adding
your own `#eval` commands to test other inputs.

:::dev
RAB: There's a question of where exactly to put this.
:::
::::

Continuing with our simple type and function, we can record what we _expect_
the result of calling a function to be in the form of a Lean `example`:

```lean
example : nextWorkingDay (nextWorkingDay .saturday) = .tuesday := by
  rfl
```

:::dev
BCP: Can we add some line breaks to that?  What is idiomatic?
:::

::::full
This declaration asserts
that the second working day after `saturday` is `tuesday`.
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
The next command opens a new namespace so that our definitions don't
clash with ones from the standard library. We'll discuss it in more
detail below.

```lean
namespace MyBool
```

:::dev
BCP: Why call it MyBool instead of just Bool?  (Or, conversely, why call the constructors
true and false instead of mytrue, myfalse, mynotb, etc.?)
:::

```lean
inductive MyBool : Type where
  | true
  | false
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

:::dev
HG: This feels like too little discussion of FP function calling for a non-FP
person, and too much for anyone who knows FP. I propose we skip this.
:::

```lean
example : orb .true  .false = .true  := by rfl
example : orb .false .false = .false := by rfl
example : orb .false .true  = .true  := by rfl
example : orb .true  .true  = .true  := by rfl
```

We can define new symbolic notations for existing definitions.
Because Lean already defines the same notations for the built-in `Bool`,
we restrict ours locally to a _section_. Don't worry for now about
how the notation is defined.

```lean
section
local prefix:40 (priority := high) "!" => notb
local infixl:35 (priority := high) " && " => andb
local infixl:30 (priority := high) " || " => orb
```

:::dev
BCP: Why spaces some places but not others?
:::

```lean
example : (.false || .false || .true) = .true := by rfl

example : (!.false) = .true := by rfl
end
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

:::dev
RAB: From this point, there are about 450 lines of comments before
the next exercise. This is the same as in Rocq, but do we want
to keep this pattern?
:::

:::dev
BCP: Ideally no!
:::

:::dev
TODO (Claude): Concretely: even trivial drop-in exercises would keep
hands on keyboards through this stretch -- e.g., "define `isWeekend`",
"write a `Color` inverter", "add your own `#check` and predict the
output".  The namespaces/sections material in particular is reference
content that could become an exercise-light aside.
:::

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

:::dev
HG: Again, maybe too basic for our audience.
BCP: I think here I might diusagree...?
DHS: This is almost exactly the text from the Rocq book. Are we aiming
these at different audiences?
:::

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

- It introduces a set of new _constructors_. E.g., `.red`,
  `.primary`, `true`, `false`, `.monday`, etc. are constructors.

- It groups them into a new named type, like `Bool`, `RGB`, or
  `Color`.

_Constructor expressions_ are formed by applying a constructor
to zero or more other constructors or constructor expressions,
obeying the declared number and types of the constructor arguments.
E.g., these are valid constructor expressions...

- `.red`
- `true`
- `.primary .red`

...but these are not:

- `.red .primary`
- `true .red`
- `.primary (.primary .red)`

:::dev
BCP: Why do all of the constructors have namespaces except true and false?
:::

:::dev
TODO (Claude): The bullet above draws attention to this inconsistency
without resolving it, which is risky for beginners.  Either explain
(`Bool`'s constructors are exported to the root namespace) or drop
the remark.
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

## Namespaces and Sections


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
--- this works, because the definnition is qualified by `RGB.`
def RGB.myOtherBlue : RGB := myBlue

#check RGB.myBlue      -- RGB
#check RGB.myOtherBlue -- RGB
```

#check myBlue -- unknown identifier

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

## Constructors with Multiple Arguments

```lean
namespace Playground
```

::::full
A single constructor with multiple parameters can be used to create
a tuple type. As an example, consider representing the four bits in
a nibble (half a byte). We first define a datatype `Bit` that
resembles `Bool` (using the constructors `b1` and `b0` for the two
possible bit values) and then define the datatype `Nibble`, which is
essentially a tuple of four bits.
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
Note: The `bits` constructor illustrates a feature of multi-argument
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

:::dev
HG: I wonder how we should prioritize `#eval e` vs. `example e = e' := rfl`.
They both feel like they have value.
DHS: I prefer `example` for when the result actually matters (as in the above case),
since this means we don't have to worry about keeping comments in sync.
BCP: Not sure I understood Chris's comment above, but I thought he might
be saying that these comment will be auto-generated by the `example` statements...?
:::

## Natural Numbers

::::full
We put this section in a namespace so that our own definition of
numbers does not interfere with the one from the standard library.
In the remainder of the book, we'll use the standard library's.
::::

:::dev
BCP: Is "section" used in a technical sense in that paragraph? Why
do we need both namespaces and sections (particularly in this first
chapter)?
:::

```lean
namespace NatPlayground
```

::::full
All the types we have defined so far -- both "enumerated
types" such as `Day`, `Bool`, and `Bit` and tuple types such as
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

:::dev
TODO (Claude): The instructor advice at the top says to work
directly in this .lean file, but the "hidden" scaffolding (this
attribute, the OfNat instance, `unseal`, `@[irreducible]`,
the BEq instance) is fully visible to anyone reading
the source, and far beyond a beginner's reach.
BCP: Same question
as Claude here: Do we really need this?  If so, how / where do we
explain it?
:::

```lean
attribute [pp_nodot] Nat.succ

namespace Nat
open Nat

@[reducible]
def ofNat (x : _root_.Nat) : Nat :=
  match x with
  | .zero => zero
  | .succ b => succ (ofNat b)

instance instOfNat {n : _root_.Nat} : OfNat Nat n where
  ofNat := ofNat n

theorem zero_eq_0 : zero = 0 := rfl
```

With this definition, 0 is represented by `zero`, 1 by `succ zero`, 2 by `succ
(succ zero)`, and so on.

We use some machinery in the background to allow us to write `0`, `1`, `2`,
etc. instead of `zero`, `succ zero`, etc., for our custom definition of `Nat`.
This is just syntactic sugar, and the two forms are interchangeable.

:::dev
BCP: Can we be more explicit about the machinery?
DHS: I propose we just cut this entirely? If we are working
with our own handrolled definition, it's okay not to have notation IMO.
:::

:::dev
BCP: What are these RULES comments for?
RULES
:::

```lean
theorem one_eq_succ_zero : 1 = succ 0 := rfl
-- RULES
theorem two_eq_succ_one : 2 = succ 1 := rfl
-- RULES
theorem three_eq_succ_two : 3 = succ 2 := rfl
-- RULES
theorem four_eq_succ_three : 4 = succ 3 := rfl

example : succ (succ (succ (succ zero))) = 4 := by rfl
```

Naturally, Lean has its own definition of natural numbers.

:::dev
BCP: We already said that, no?
:::

```lean
  #check Nat
  /- ==> NatPlayground.Nat : Type -/ /- ← this is our `Nat`... -/
  #check _root_.Nat
  /- ==> _root_.Nat : Type -/ /- ← ...this is Lean's `Nat`. -/
```

Lean's `Nat` comes with some powerful built-in features for reasoning and
notation.

As we are just beginning to reason about natural numbers, we use our own
definition here and introduce the Lean one in a later chapter.

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

#eval minustwo 4
```

::::full
You may wonder what the `@[irreducible]` means in the definitions above,
or the `seal` and `unseal` that we use in the examples below.
Hold onto this question; we will explain shortly.
::::

:::dev
TODO:
Lean user question: how to get (succ (succ zero)) rather than
NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.zero))
:::

:::dev
BCP: Yes!
:::

:::dev
BCP: Missing transition
:::

::::full
```lean
#check Nat.succ  -- Nat → Nat
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
example : even 1 = false  := by rfl
example : even 4 = true := by rfl
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
example : odd 1 = true  := by rfl
example : odd 4 = false := by rfl
seal odd even
```

:::slidebreak
:::

:::terse
A multi-argument recursive function.
:::

```lean
@[irreducible]
def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m')

--- Don't worry about this for now
instance instAdd : Add Nat where add := add
```

:::dev
BCP STOPPED HERE
:::

# Proof by Rewriting

## Proving properties about functions in Lean

::::full
Being recursive, `add` is our first example of a more sophisticated
class of functions. In this chapter and beyond, we will _prove_
properties about recursive functions like `add` over inductive
datatypes like `Nat` using _simplification rules_ about their
behavior.

Here is a simple rule about `add`:

- `n + 0 = n`

In Lean, this rule looks like this:
::::

:::dev
BCP: Why does the Info View say "Goals accomplished!" right at the
beginning of the proof?  Can we comment on this?
:::

```lean
unseal add in
theorem add_zero : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl
```

::::full
```lean
#check add_zero
```

:::dev
BCP: We will probably want to remove the "NatPlayground" stuff from
all these comments when we fix the printing.
:::

We can then use the `add_zero` rule to carry out a simple proof
about natural numbers!

```lean
theorem add_zero_zero (n : Nat) : n + 0 + 0 = n := by
  rewrite [add_zero]
  rewrite [add_zero]
  rfl

-- Let's walk through this proof.
```
::::

## Proof state and tactics

::::full
The "proof commands" -- `rewrite`, `rfl`, etc. -- are called
_tactics_. The `add_zero` in brackets is an _argument_ to the
`rewrite` tactic.

Hovering with the cursor over each line of the proof, we can see the
_proof state_ in the Lean InfoView panel.

The proof state is divided into the _context_, before the ⊢,
and the _goal_, after the ⊢. The context is what we know at each point, while
the goal is what we are trying to prove.

A tactic manipulates both the goal and the context to get the goal
into a shape that is closer to the one we want. A tactic can also
_close_ (solve) the current goal which finishes its proof.

Let's walk through the example above with this terminology in mind.

```lean
theorem add_zero_zero_explained (n : Nat) : n + 0 + 0 = n := by
  /- Move your cursor (click) here to see the initial proof state in
     the InfoView. The context is `n : Nat`. The goal is `n + 0 + 0 =
     n`. -/
  rewrite [add_zero]
  /- Now click here to see the new proof state that results from the tactic.
     Notice how `n + 0 + 0` changes to `n + 0` in the goal. -/
  rewrite [add_zero]
  /- Again the goal changes, from `n + 0` to `n`. Now the proof state
     is an equality with both sides equal, so it can be closed by the
     tactic `rfl`. -/
  rfl
  /- The proof is now done! The Lean InfoView tells us there are "No Goals". -/

/-! Here's a simple proof for you to try. -/

theorem add_zero_zero_zero (n : Nat) : n + 0 + 0 + 0 = n := by
  solution!
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
  which states that `n + 0` is equal to `n` for any `n`, we can replace any `n
  + 0` in our proof with `n` via `rewrite [add_zero]`.

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
theorem add_succ : ∀ n m : Nat, n + succ m = succ (n + m) := by
  intro n m
  rfl
```

And here it is in a proof:

```lean
theorem add_succ_zero (n : Nat) : n + succ 0 = succ (n + 0 + 0) := by
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
The definitions and proofs above use a rather mysterious convention:
we write `@[irreducible]` above some of our definitions, and we
write `unseal` before some of our proofs and `seal` after them.
This is not something you will usually see in real Lean developments;
rather, we use them throughout this book to enforce a particular convention
to help you build good Lean habits.

Lean, like any other programming language, has conventions and best practices
for writing good software. You may be familiar with object oriented programming,
for example, in which it is considered good practice not to access the
fields of objects directly, and instead to use getter and setter methods.
This helps to encapsulate the object's definition, so if its fields or implementation
change, the interface it exposes to the outside world remains the same.

The same principle applies to definitions (and proofs about them) in Lean.
In idiomatic Lean, it is considered poor style to "peek" through
definitions and rely on `rfl` to implicitly simplify expressions
that aren't actually equal. If you take a look at the proofs of
`add_zero` and `add_succ` above, you will notice this is exactly what we did
when we used the `rfl` tactic.

In this text, to enforce idiomatic style, we mark
definitions with `@[irreducible]` to prevent this peeking.
The `unseal` we wrote before the proof of `add_zero` temporarily
allows this, but only in that proof. We have to
allow it there, since there is no other way to prove the goal.
However, except for `add_zero` and `add_succ`, we never need
to unseal `add` anywhere else. Instead, we can rewrite
with those theorems anywhere we want to describe how `add` evaluates.

These two theorems also follow a particular pattern. Let's look again at the
definition of `add`:

```lean
namespace AddPlayground

@[irreducible]
def add' (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m')

unseal add in
theorem add_zero' : forall (n : Nat), n + 0 = n := by
  intro n
  rfl

unseal add in
theorem add_succ' : forall (n m : Nat), n + succ m = succ (n + m) := by
  intro n m
  rfl

end AddPlayground
```

Each of `add_zero` and `add_succ` correspond to one branch of the `match`
statement defining `add`, and describe how the evaluation of `add` proceeds
in that case. The `add_zero` theorem describes how `n + 0` evaluates,
while `add_succ` describes (symbolically) how `n + succ m` evaluates.
Because these theorems describe how to simplify more complex expressions
involving `add`, we call them `add`'s _simplification lemmas_.

These are an instance of a general pattern: each definition
of operating over enumerated types like `Nat`s or `Bool`s or `Day`s or `Color`s
will need a simplification lemma for each branch of control flow through
the function.

So, for example, we need two simplification lemmas for the definition of `pred`:

```lean
unseal pred in
theorem pred_zero : pred 0 = 0 := by rfl

unseal pred in
theorem pred_succ n : pred (succ n) = n := by rfl
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
with their simplification lemmas. Then, instead of using `rfl`
to peek through the definitions, we will prefer rewriting
by those lemmas, using `@[irreducible]` to enforce this policy,
and only `unseal`ing the definition in the proofs of those lemmas themselves.
::::

## Working with Numerals

::::full
   We know from above that `1` is just `succ 0`, `2` is `succ 1`, and so on.
   We have rules for these equalities, as well:

:::dev
BCP: We have them because we stated them above, but maybe the
reader wasn't sure why we did that.  I'm a little confused what
point we're making just here.
:::

```lean
#check one_eq_succ_zero /- ==> one_eq_succ_zero : 1 = succ 0 -/
#check two_eq_succ_one /- ==> two_eq_succ_one : 2 = succ 1 -/
#check three_eq_succ_two /- ==> three_eq_succ_two : 3 = succ 2 -/
```

We can rewrite with these rules to expand numerals into their definitions,
   which allows us to use our `add` rules.
::::

Here's an example of how to start a proof this way.
   Finish the proof using the `add` rules.

:::dev
BCP: Should this be marked / formatted as an exercise?
:::

```lean
theorem one_plus_one_eq_two : (1 + 1 : Nat) = 2 := by
  rewrite [one_eq_succ_zero]
  solution!
    rewrite [add_succ]
    rewrite [add_zero]
    rfl
```

Try the same for `2 + 2 = 4`.

```lean
theorem two_plus_two_eq_four : (2 + 2 : Nat) = 4 := by
  solution!
    rewrite [four_eq_succ_three, three_eq_succ_two,
             two_eq_succ_one, one_eq_succ_zero]
    rewrite [add_succ, add_succ, add_zero]
    rfl
```

::::full
By default, `rewrite` rewrites left-to-right. To rewrite from right
to left, use `rewrite [← h]`, where `←` is typed as `\l` or `\<-`.

:::dev
BCP: We should make this point wherever we rewrite to the left for
the first time. It's out of place here.
:::
::::

::::full
Now that we know how addition is defined, we can use it to define
multiplication:
::::

:::slidebreak
:::

```lean
@[irreducible]
def mul (n m : Nat) : Nat :=
  match m with
  | zero => zero
  | succ m' => add (mul n m') n

instance instMul : Mul Nat where mul := mul
```

Multiplication, like any function we will prove properties about,
   also has simplification rules.

```lean
unseal mul in
theorem mul_zero : ∀ n : Nat, n * 0 = 0 := by
  intro n
  rfl

unseal mul add in
theorem mul_succ : ∀ n m : Nat, n * succ m = n * m + n := by
  intro n m
  rfl
```

Prove this property. We have given you the first line. Notice how `rewrite`
   can take any number of arguments. You can use this rewrite with all of the
   numeral rules at once, for example.

   After each rewrite, check the proof state by placing the cursor immediately
   after a rule to see how the goal is changing. This happens naturally
   as you write the proof, which makes it convenient to use `rewrite` blocks
   with multiple rules.

```lean
theorem test_mult1 : (3 * 3 : Nat) = 9 := by
  rewrite [three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
  solution!
    rewrite [mul_succ, mul_succ, mul_succ, mul_zero]
    rewrite [add_succ, add_succ, add_succ, add_zero]
    rewrite [add_succ, add_succ, add_succ, add_zero]
    rewrite [add_succ, add_succ, add_succ, add_zero]
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

example : leb 2 2 = true  := by rfl
example : leb 2 4 = true  := by rfl
example : leb 4 2 = false := by rfl
seal leb
```

:::slidebreak
:::

We'll be using these (especially `beq`) a lot, so let's give
them infix notations. Don't worry too much about how these are defined.

:::dev
JC: Lean's stdlib has `==` notation for `beq`,
but not for `Nat.ble`...
:::

:::dev
BCP: Readers may wonder what "instance" is...
:::

```lean
instance : BEq Nat where
  beq := beq

infix:65 "≤?" => leb

unseal leb in
example : 4 ≤? 2 = false := by rfl
```

::::full
We can also now define `beq`'s simplification lemmas with this new notation,
one for each of the four cases of control flow through the function.

```lean
unseal beq
theorem zero_zero_beq_true : (0 == 0) = true := by rfl
theorem zero_succ_beq_false (n : Nat) : (0 == (succ n)) = false := by rfl
theorem succ_zero_beq_false (n : Nat) : ((succ n) == 0) = false := by rfl
theorem succ_succ_beq (n m : Nat) : ((succ n) == (succ m)) = (n == m) := by rfl
seal beq
```
::::

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

infix:65 "<?" => ltb

unseal ltb leb
example : 2 <? 2 = false := solution!(by rfl)
example : 2 <? 4 = true  := solution!(by rfl)
example : 4 <? 2 = false := solution!(by rfl)
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

:::dev
TODO (Claude): The file mixes two binder styles without comment:
`theorem foo (n : Nat) : ...` (no `intro` needed, e.g. `add_zero_zero`)
vs. `theorem foo : ∀ n : Nat, ...` plus `intro` (here).  "When do I
need `intro`?" is one of a beginner's first hard questions; one
explicit paragraph reconciling the two styles would prevent
cargo-culting.
:::

::::full
We now begin to make claims about _general_ natural numbers.

We begin by making a universal claim about all numbers `n` and `m` that are
equal to each other (`n = m`). The arrow symbol is pronounced "implies."
Type it with `\to` or `\->` or `\r`.

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

:::dev
BCP: I find the indentation / linebreaking choices here kind of
ugly. Are they standard, or can we make a better convention?
:::

```lean
theorem add_id_example : ∀ n m : Nat,
    n = m →
    n + n = m + m := by
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
The `sorry` keyword tells Lean that we want to skip trying
to prove this theorem and just accept it as a given.  This is
often useful for developing longer proofs.

Be careful, though: every time you say `sorry` you are leaving
a door open for total nonsense to enter Lean's safe, formally
checked world!

:::dev
TODO (Claude): `sorry` was already explained before the nandb
exercise, and this second explanation arrives *after* add_id_exercise
told the student to remove a `sorry`.  Keep one explanation, placed
before its first use, and cover both roles there (exercise placeholder
/ temporarily accepting a claim).
:::
::::

:::slidebreak
:::

The `#check` command can also be used to examine the statements of
previously declared lemmas and theorems.

:::dev
TODO: how to get these to show `∀ (n : Nat)` instead of `mul_zero (n : Nat)`
:::

:::dev
BCP: Or maybe we need to explain that they mean the same thing?  I
think we are a bit inconsistent, ourselves, in the way we write
things.
:::

```lean
#check mul_zero  -- ∀ (n : Nat), n * 0 = 0
#check mul_succ  -- ∀ (n m : Nat), n * Nat.succ m = n + n * m
```

:::slidebreak
:::

We can use the `rewrite` tactic with a previously proved theorem
instead of a hypothesis from the context.

```lean
theorem add_mul_zero : ∀ p q : Nat,
    (p * 0) + (q * 0) = 0 := by
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
source files to help deter bitrot, and you are encouraged to add
your own instances.  It doesn't need to be explained to students
because it gets stripped out when verso files are translated to
.lean and .html.

:::
:::dev
HG: We should be using `guard_msgs` anywhere we leave a sorry.
BCP: Yes, and there's already a part of a note about this someplace.  Merge with this.
:::

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs(warning) in
example : ∀ n : Nat,
    (succ n == 0) = false := by
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
    (succ n == 0) = false := by
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

:::dev
DHS: All these `Bool` examples are in the old style, where we simplify
through `rfl` instead of rewriting by simplification lemmas. Do we want
to go ahead and change all of this? If we do, we need to also add in
an explanation of how to find the appropriate rewrite lemmas in the standard library,
which is probably a new lesson in and of itself.
:::

```lean
theorem notb_involutive : ∀ b : Bool,
    (!!b) = b := by
  intro b
  cases b
  case true => rfl
  case false => rfl
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
    case true => rfl
    case false => rfl
  case false =>
    cases c
    case true => rfl
    case false => rfl

theorem andb3_exchange : ∀ b c d : Bool,
    ((b && c) && d) = ((b && d) && c) := by
  intro b c d
  cases b
  case false =>
    cases c
    case true =>
      cases d
      case false => rfl
      case true => rfl
    case false =>
      cases d
      case false => rfl
      case true => rfl
  case true =>
    cases c
    case true =>
      cases d
      case false => rfl
      case true => rfl
    case false =>
      cases d
      case false => rfl
      case true => rfl
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
  (0 == Nat.succ n) = false := by
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

Lean handles notation scoping through namespaces and _type classes_
rather than notation scopes.  The numeric literal `3` can be
interpreted as `Nat`, `Int`, `Float`, etc., depending on the
expected type, thanks to Lean's `OfNat` type class. We explain type
classes in full in a later chapter.

:::dev
TODO: which chapter?
:::

:::dev
BCP: What is "notation scopes"?  Can this explanation be streamlined?
:::
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
terminates.  Specifically, it checks that one of the arguments
is _structurally decreasing_.  This implies that all calls to
`add'` will eventually terminate.

This requirement is a fundamental feature of Lean's design: In
particular, it guarantees that every function that can be defined
in Lean will terminate on all inputs.  However, because Lean's
termination analysis is not always able to figure things out
automatically, it is sometimes necessary to provide hints or
write functions in slightly different ways.

Lean also supports more flexible termination proofs using
`termination_by` and `decreasing_by` clauses, as well as `partial`
functions that are not required to terminate.

:::dev
BCP: That last paragraph will be opaque to many readers.
DHS: Let's just drop it, IMO
:::
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

```lean
end Nat
```

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
  | .z => 0
  | .b0 m' => binToNat m' * 2
  | .b1 m' => binToNat m' * 2 + 1)

unseal incr
example : incr (.b1 .z) = .b0 (.b1 .z) := solution!(by rfl)
example : incr (.b0 (.b1 .z)) = .b1 (.b1 .z) := solution!(by rfl)
example : incr (.b1 (.b1 .z)) = .b0 (.b0 (.b1 .z)) := solution!(by rfl)

theorem incr_z : incr .z = .b1 .z := solution!(by rfl)
theorem incr_b0 m : incr (.b0 m) = .b1 m := solution!(by rfl)
theorem incr_b1 m : incr (.b1 m) = .b0 (incr m) := solution!(by rfl)
seal incr

unseal binToNat
theorem binToNat_z : binToNat .z = 0 := solution!(by rfl)
theorem binToNat_b0 m : binToNat (.b0 m) = binToNat m * 2 := solution!(by rfl)
theorem binToNat_b1 m : binToNat (.b1 m) = binToNat m * 2 + 1 := solution!(by rfl)
seal binToNat
```

```lean
unseal Nat.mul Nat.add incr binToNat
example : binToNat (.b0 (.b1 .z)) = 2 := solution!(by rfl)
example : binToNat (incr (.b1 .z)) = 1 + binToNat (.b1 .z) := solution!(by rfl)
example : binToNat (incr (incr (.b1 .z))) = 2 + binToNat (.b1 .z) := solution!(by rfl)
example : binToNat (.b0 (.b0 (.b0 (.b1 .z)))) = 8 := solution!(by rfl)
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

:::dev
TODO: Give more intro to these two theorems on booleans.
:::

```lean
end NatPlayground
```

# More Exercises

## Warmups

::::exercise (rating := 1) (name := "identity_fn_applied_twice")
Use the tactics you have learned so far to prove the following
theorem about boolean functions.

:::dev
TODO (Claude): This exercise quietly requires rewriting with a
*universally quantified* hypothesis -- a real conceptual jump from
rewriting with `h : n = m` that deserves a sentence of preparation.
:::

```lean
theorem identity_fn_applied_twice : ∀ f : Bool → Bool,
    (∀ x : Bool, f x = x) →
    ∀ b : Bool, f (f b) = b := by
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
    (∀ x : Bool, f x = !x) →
    ∀ b : Bool, f (f b) = b := by
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

:::dev
BCP: The indentation here is even more problematic... Is this a
systematic problem with the way the file was translated?
:::

```lean
theorem andb_eq_orb : ∀ b c : Bool,
    (b && c) = (b || c) →
  b = c := by
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
