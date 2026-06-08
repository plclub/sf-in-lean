import VersoManual
import VersoManual.InlineLean
import Illuminate
import LF.Meta.Bnf
import LF.Meta.Ignore
import LF.Meta.Save
import LF.Meta.Comment
import LF.Meta.Exercise

open Verso.Genre Manual
--open Illuminate.Diagram
open LF.Meta
open LF

/-
INSTRUCTORS: This file and Induction.lean each take about an hour to
   get through in a not-too-rushed fashion (with questions, etc.).
   (BCP: Actually, in 2025 this file alone took me two full hours.)

   You may want to assign both files together as the homework for the
   first week, depending on the level of the class.  Just Basics is
   fairly light for many students, but in a mixed class there will
   be people that struggle with some of it.

   PRESENTATION ADVICE: Working with the .lean file directly in VS Code
   is recommended for the first few lectures, so students see exactly
   what's in the source file.
-/

open InlineLean hiding lean

#doc (Manual) "Basics: Functional Programming in Lean" =>
%%%
htmlSplit := .never
file := "Basics"
%%%

# Introduction

The _functional style_ of programming is founded on simple,
everyday mathematical intuitions: If a procedure or method has no
side effects, then (ignoring efficiency) all we need to understand
about it is how it maps inputs to outputs -- that is, we can think
of it as just a concrete method for computing a mathematical
function.  This is one sense of the word "functional" in
"functional programming."  The direct connection between programs
and simple mathematical objects supports both formal correctness
proofs and sound informal reasoning about program behavior.

The other sense in which functional programming is "functional" is
that it emphasizes the use of functions as _first-class_ values --
i.e., values that can be passed as arguments to other functions,
returned as results, included in data structures, etc.  The
recognition that functions can be treated as data gives rise to a
host of useful and powerful programming idioms.

Other common features of functional languages include _algebraic
data types_ and _pattern matching_, which make it easy to
construct and manipulate rich data structures, and _polymorphic
type systems_ supporting abstraction and code reuse.  Lean offers
all of these features.

The first half of this chapter introduces some key elements of
Lean's functional programming language.  The second half introduces
some basic _tactics_ that can be used to prove properties of
programs.

# Data and Functions

## Enumerated Types

One notable thing about Lean is that its set of built-in features is
_extremely_ small.  For example, instead of the usual palette of atomic
data types (booleans, integers, strings, etc.), Lean offers a powerful
mechanism for defining new data types from scratch, with all these
familiar types as instances.

Naturally, Lean also comes with an extensive standard library providing
definitions of booleans, numbers, and many common data structures like lists
and hash tables.  But there is nothing magic or primitive about these library
definitions.  To illustrate this, in this course we will explicitly
recapitulate almost all the definitions we need, rather than getting them
from the standard library.

We take great care to match those definitions with the ones in the standard
library, so that by the time you are finished with this course, you will
already have a strong understanding of how the Lean standard library works.

:::dev
RAB ADDITION ^ (last paragraph above)
:::

## Days of the Week

To see how the datatype definition mechanism works, let's
start with a very simple example.  The following declaration tells
Lean that we are defining a set of data values -- a _type_.

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

The new type is called {name}`Day`, and its members are {name}`Day.monday`,
{name}`Day.tuesday`, etc.

Having defined {name}`Day`, we can write functions that operate on days.

```lean
def Day.nextWorkingDay (d : Day) : Day :=
  match d with
  | .monday    => .tuesday
  | .tuesday   => .wednesday
  | .wednesday => .thursday
  | .thursday  => .friday
  | .friday    => .monday
  | .saturday  => .monday
  | .sunday    => .monday
```

Note that the argument and return types of this function are
explicitly declared on the first line.  Like most functional
programming languages, Lean can often figure out these types for
itself when they are not given explicitly - i.e., it can do _type
inference_ -- but we'll generally include them to make reading
easier.

:::dev
RAB ADDITION (further edited by CGH)
:::

You may also notice the unique pattern matching syntax- for
example, in `.monday`. The `.` - is syntactic sugar for {name}`Day.monday`, and
exists to save the programmer the time of typing out the full qualified name.
You may wonder why the language doesn't just expose a pattern like `monday`
without the dot, like OCaml does. This is to avoid name shadowing, because
being explicit about names is _especially_ important to avoid confusion and
headaches when writing proofs. The `.` syntax is a compromise that lets us
know we're qualifying a name without having to type too much. If this syntax
is ever ambiguous, Lean will provide an error message listing any names that
might have been intended. For now we'll write

```lean
open Day
```

so that we can write these without the full namespace.

Having defined a function, we can check that it works on
some examples.  There are actually three different ways to do
examples in Lean.  First, we can use the `#eval` command to
evaluate a compound expression involving `nextWorkingDay`.

:::dev
  CGH: these `#eval` are supposed to show up in the HTML I thought, some missing config
:::

```lean
#eval nextWorkingDay friday
```

```lean
#eval nextWorkingDay (nextWorkingDay saturday)
```
Second, we can record what we _expect_ the result to be in the
form of a Lean `example`:

```lean
open Day in
example : nextWorkingDay (nextWorkingDay saturday) = tuesday := by
  rfl
```

:::dev
RAB/CGH: this should go somewhere, but maybe is awkward here

(We show Lean's responses in comments; if you have a computer
handy, this would be an excellent moment to fire up VS Code with
the Lean extension and try it for yourself.  Load this file,
`Basics.lean`, from the book's Lean sources, find the above
example, and observe the result in the Lean Infoview panel.)

Aside: Using the Lean Extension

In VS Code, development of Lean code is supported by
the Lean Extension, which provides an interactive "infoview" panel that
displays the results of commands like `#eval` and `#check`, as well as the
current goal state when working on proofs. You can hover over expressions in
the source code to see their types, and you can click on the results in the
infoview to navigate to their definitions. This makes it easier to understand
how your code is being interpreted by Lean and to debug any issues that
arise.

The infoview always follows your cursor, and Lean typechecks the file as you
edit it, so you can see the results of your changes immediately. You can also
use the infoview to explore the definitions of functions and types that
you're using, which can be very helpful for understanding how they work.

If you haven't already, install the Lean Extension in VS Code and open the
`Basics.lean` file to see the infoview in action. Try hovering over the
`nextWorkingDay` function and the `Day` type to see their definitions, and
experiment with adding your own `#eval` commands to test other inputs.
:::

This command makes an assertion that the second working day after {name}`saturday` is {name}`tuesday`).
Having made the assertion, we can also ask Lean to _verify_ it.
The `by rfl` can be read as "The assertion we've just made can be
proved by observing that both sides of the equality evaluate to
the same thing."

{tactic}`rfl` stands for "reflexivity," which is the principle that any value is
equal to itself. After evaluation, both sides of the equality are the same
value, so the assertion is true by reflexivity.  If we had made a different
assertion, such as `nextWorkingDay (nextWorkingDay saturday) = monday`
then Lean would not be able to verify it, and would signal an
error. Try it out!

Third, we can ask Lean to _compile_ our definitions to efficient
native code.  Lean compiles to C, which is then compiled to machine
code by a standard C compiler.  This facility is very useful, since
it gives us a path from proved-correct algorithms written in Lean to
efficient executables.

Indeed, this is one of the main uses for which Lean was developed.
We'll come back to this topic in later chapters.

## Booleans

Following the pattern of the days of the week above, we can
define the standard type {name}`Bool` of booleans, with members {name}`true`
and {name}`false`.

We define our own `MyBool` to teach the concept of building from
scratch; later we'll switch to Lean's built-in {name}`Bool`.

```lean
inductive MyBool : Type where
  | true
  | false
```
Functions over booleans can be defined in the same way as above:

```lean
namespace MyBool

def notb (b : MyBool) : MyBool :=
  match b with
  | true => false
  | false => true

def andb (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | true => b2
  | false => false

def orb (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | true => true
  | false => b2

end MyBool

open MyBool
```
(Although we are rolling our own booleans here for the sake
of building up everything from scratch, Lean does, of course,
provide a default implementation of the booleans, together with a
multitude of useful functions and lemmas.)

The last two of these illustrate Lean's syntax for
multi-argument function definitions.  The corresponding
multi-argument _application_ syntax is illustrated by the
following "unit tests," which constitute a complete specification
- a truth table - for the {name}`orb` function:

```lean
example : orb true  false = .true  := by rfl
example : orb false false = .false := by rfl
example : orb false true  = .true  := by rfl
example : orb true  true  = .true  := by rfl
```

We can define new symbolic notations for existing definitions.
Because Lean already defines these for the built-in {name}`Bool`,
we restrict ours locally to a section.

```lean
section

local prefix:40 (priority := high) "!" => notb
local infixl:35 (priority := high) " && " => andb
local infixl:30 (priority := high) " || " => orb

example : (.false || .false || .true) = .true := by rfl

example : (! .false) = .true := by rfl
```

The {tactic}`sorry` keyword can be used as a placeholder for an
incomplete proof or definition.  We use it in exercises to indicate
the parts that we're leaving for you - i.e., your job is to replace
{tactic}`sorry` with real definitions and proofs.

:::dev
CGH TODO: change `exercise` so you don't need multiple blocks like this
:::

:::exercise (rating := 1) (name := "nandb")
Remove {tactic}`sorry` below and complete the definition of the
following function; then make sure that the `example` assertions
below can each be verified by Lean.  The function should return
`true` if either or both of its inputs are `false`.
```lean
def nandb (b1 : MyBool) (b2 : MyBool) : MyBool := solution!(
  match b1 with
  | .true => notb b2
  | .false => true)

```
```lean
example : nandb true  false = .true  := solution!(by rfl)
```
```lean
example : nandb false false = .true  := solution!(by rfl)
```
```lean
example : nandb false true  = .true  := solution!(by rfl)
```
```lean
example : nandb true  true  = .false := solution!(by rfl)
```
:::


:::exercise (rating := 1) (name := "andb3")
```lean
def andb3 (b1 : MyBool) (b2 : MyBool) (b3 : MyBool) : MyBool := solution!(
  andb b1 (andb b2 b3)
  )
```
```lean
example : andb3 true  true  true  = .true  := solution!(by rfl)
```
```lean
example : andb3 false true  true = .false := solution!(by rfl)
```
```lean
example : andb3 true  false true = .false := solution!(by rfl)
```
```lean
example : andb3 true  true  false = .false := solution!(by rfl)
```
:::

Now that we've seen how to define our own booleans, we can switch back to
Lean's built-in {name}`Bool` type, which has the same structure but also includes
a lot of useful functions and lemmas.  We can even define functions to
convert between our {name}`MyBool` and Lean's {name}`Bool`.

```lean
def myBoolToBool (b : MyBool) : Bool :=
  match b with
  | .true => true
  | .false => false
```
With the full power of Lean's {name}`Bool` at our disposal, we can also write this
more concisely using the `bif ... then ... else` syntax, which is a
convenient way to write simple conditional expressions.

:::dev
CGH: not sure how to hide the section closing
:::

```lean
def boolToMyBool (b : Bool) : MyBool :=
  bif b then true else false

end
```

:::dev
RAB: From this point, there are about 450 lines of comments before
the next exercise. This is the same as in Rocq, but do we want
to keep this pattern?
:::

## Types

Every expression in Lean has a type describing what sort of
thing it computes.  The `#check` command asks Lean to print the type
of an expression.

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

Functions like {name}`not` itself are also data values, just like
`true` and `false`.  Their types are called _function types_, and
they are written with arrows.

```lean
#check not
```
The type of {name}`not`, written `Bool → Bool` and pronounced
"`Bool` arrow `Bool`," can be read, "Given an input of type
`Bool`, this function produces an output of type `Bool`."
Similarly, the type of `and`, written `Bool → Bool → Bool`, can
be read, "Given two inputs, each of type `Bool`, this function
produces an output of type `Bool`."

You may notice that → is a unicode character, not a simple ASCII string. This
is a common convention in Lean, and the Lean Extension provides convenient
shortcuts for entering these characters. Simply typing \ (backslash) followed
by the name of the character, and the extension will automatically replace it
with the correct symbol. For example, typing \-> or \to will produce →, and
\lambda will produce λ. This allows you to write more concise and readable
code without having to remember complex keyboard shortcuts.

## New Types from Old

The types we have defined so far are examples of simple
"enumerated types": their definitions explicitly enumerate a
finite set of elements, called _constructors_.  Here is a more
interesting type definition, `Color`, where one of the
constructors takes an argument:

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

Let's look at this in a little more detail. An `inductive` definition does two things:

- It introduces a set of new _constructors_. E.g., `RGB.red`,
  `Color.primary`, `true`, `false`, `Day.monday`, etc. are constructors.

- It groups them into a new named type, like `Bool`, `RGB`, or
  `Color`.

_Constructor expressions_ are formed by applying a constructor
to zero or more other constructors or constructor expressions,
obeying the declared number and types of the constructor arguments.

E.g., these are valid constructor expressions...

    - `RGB.red`
    - `true`
    - `Color.primary RGB.red`
    - etc.

but these are not:

    - `RGB.red Color.primary`
    - `true RGB.red`
    - `Color.primary (Color.primary RGB.red)`
    - etc.

We can define functions on colors using pattern matching just as
we did for `Day` and `Bool`.

```lean
def monochrome (c : Color) : Bool :=
  match c with
  | .black => true
  | .white => true
  | .primary _ => false
```

Since the `primary` constructor takes an argument, a pattern
matching `primary` should include either a variable, as we just
did (note that we can choose its name freely), or a constant of
appropriate type (as below).

```lean
def isRed (c : Color) : Bool :=
  match c with
  | .black => false
  | .white => false
  | .primary .red => true
  | .primary _ => false
```

The pattern `Color.primary _` here is shorthand for "the constructor
`primary` applied to any `RGB` constructor except `red`."

:::dev
CGH: this section is currently somewhat out of order since we mention namespaces above
:::

## Namespaces and Sections

  Lean provides a _namespace system_ to aid in organizing large
  developments.  If we enclose a collection of declarations in
  `namespace X ... end X`, then, in the remainder of the file
  after the `end`, these definitions are referred to by names like
  `X.foo` instead of just `foo`.  We will use this feature to limit
  the scope of definitions, so that we are free to reuse names.

```lean
namespace Playground
def myFoo : RGB := RGB.blue
end Playground

def myFoo : Bool := true

#check Playground.myFoo  -- RGB
#check myFoo             -- Bool
```

  Inside of a namespace, all previous definitions from that namespace are
  available, and can be referred to without prefixing.
  Definitions can also be prefixed by a namespace to put it in the namespace
  without having to open and close the namespace.

```lean
namespace RGB
def myBlue : RGB := blue
end RGB

def RGB.myOtherBlue : RGB := myBlue

#check RGB.myBlue      -- RGB
#check RGB.myOtherBlue -- RGB
```

  We can also use `open` to bring the definitions of a namespace into scope.
  This makes it convenient to refer to all of those definitions without
  a prefix. Original definitions of the same name can then be referred to
  by the special prefix `_root_`.
  Lean also provides _sections_, which delimit the scope of `open`ing
  namespaces and `local` notations within `section ... end`.
  We already saw `prefix` and `infix` notations for MyBool;
  there are also `postfix` notations.

```lean
section
open Playground
local postfix:40 "′" => Color.primary

#check myFoo        -- RGB
#check _root_.myFoo -- Bool
#check RGB.blue′    -- Color
end

#check myFoo         -- Bool

-- fails to parse:
-- #check RGB.blue′
```
## Tuples

```lean
namespace TuplePlayground
```

  A single constructor with multiple parameters can be used
  to create a tuple type. As an example, consider representing
  the four bits in a nybble (half a byte). We first define
  a datatype `Bit` that resembles `Bool` (using the
  constructors `b1` and `b0` for the two possible bit values)
  and then define the datatype `Nybble`, which is essentially
  a tuple of four bits.

:::dev
RAB: Is this called a Nybble, not a Nibble? Whatever the Penn systems course
calls it, we should follow suite, I guess.
:::

```lean
inductive Bit : Type where
  | b1
  | b0

inductive Nybble : Type where
  | bits (x0 x1 x2 x3 : Bit)

#check (.bits .b1 .b0 .b1 .b0 : Nybble)
```

  The `bits` constructor acts as a wrapper for its contents.
  Unwrapping can be done by pattern-matching, as in the `allZero`
  function below, which tests a nybble to see if all its bits are
  `b0`.

```lean
def allZero (nb : Nybble) : Bool :=
  match nb with
  | .bits .b0 .b0 .b0 .b0 => true
  | .bits _   _   _   _   => false
```

(The underscore `_` here is a _wildcard pattern_, which avoids inventing variable names that will not be used.)

```lean
#eval allZero (.bits .b1 .b0 .b1 .b0)
#eval allZero (.bits .b0 .b0 .b0 .b0)
```
```lean
end TuplePlayground
```

## Numbers

# Proof by Simplification

# Proof by Rewriting

# Proof by Case Analysis

## More on Notation (Optional)

## Structural Recursion (Optional)

# More Exercises

## Warmups

## Course Late Policies, Formalized

  Suppose that a course has a grading policy based on late days,
  where a student's final letter grade is lowered if they submit too
  many homework assignments late.

```lean
namespace LateDays
```

  First, we inroduce a datatype for modeling the "letter" component
  of a grade.

```lean
inductive Letter : Type where
  | A | B | C | D | F
```

  Then we define the modifiers -- a `natural` `a` is just a "plain"
  grade of `a`.

```lean
inductive Modifier : Type where
  | plus | natural | minus
```

  A full `Grade`, then, is just a `letter` and a `modifier`.
  In Lean, a combination of several values is called a _structure_.  The `structure`
  keyword is used to define a new structure type.

```lean
structure Grade where
  letter : Letter
  modifier : Modifier
```

  We will want to be able to say when one grade is "better" than
  another.  In other words, we need a way to compare two grades.  As
  with natural numbers, we could define `bool`-valued functions
  `grade_eqb`, `grade_ltb`, etc., and that would work fine.
  However, we can also define a slightly more informative type for
  comparing two values, as shown below.  This datatype has three
  constructors that can be used to indicate whether two values are
  "equal", "less than", or "greater than" one another.

```lean
inductive Comparison : Type where
  | eq   -- "equal"
  | lt   -- "less than"
  | gt   -- "greater than"
```

  Since we're in a namespace, we can open the relevant types to
  avoid having to write `Letter.A`, etc.

```lean
open Letter Modifier Comparison
```

  Using pattern matching, it is not difficult to define the
  comparison operation for two letters `l1` and `l2` (see below).
  This definition uses a feature of `match` patterns: we can match
  against _two_ values simultaneously by separating them and the
  corresponding patterns with comma `,`.
  This is simply a convenient abbreviation for nested pattern
  matching.

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

:::exercise (name := "letter_comparison") (rating := 1)
```lean
theorem letterComparison_Eq :
    ∀ l : Letter, letterComparison l l = eq := by solution!(
  intro l
  cases l <;> rfl
  )
```
:::

We can follow the same strategy to define the comparison operation for two grade modifiers.
We consider them to be ordered as `plus > natural > minus`.

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

:::exercise (name := "grade_comparison") (rating := 2)
  Here, we will need to access the fields of the `Grade` structure.
  The field names are `letter` and `modifier`, so for a grade `g`,
  we can write `g.letter` and `g.modifier` to access these fields.

```lean
def gradeComparison (g1 g2 : Grade) : Comparison := solution!(
  match letterComparison g1.letter g2.letter with
  | lt => lt
  | eq => modifierComparison g1.modifier g2.modifier
  | gt => gt
  )
```
```lean
example : gradeComparison ⟨A, minus⟩ ⟨B, plus⟩ = gt := solution!(by rfl)
```
```lean
example : gradeComparison ⟨A, minus⟩ ⟨A, plus⟩ = lt := solution!(by rfl)
```
```lean
example : gradeComparison ⟨F, plus⟩ ⟨F, plus⟩ = eq := solution!(by rfl)
```
```lean
example : gradeComparison ⟨B, minus⟩ ⟨C, plus⟩ = gt := solution!(by rfl)
```
:::

Now that we have a definition of grades and how they compare to one another, let us implement a late-penalty fuction.

First, we define what it means to lower the letter component of a grade. Since F is already the lowest grade possible, we just leave it alone.

```lean
def lowerLetter (l : Letter) : Letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F  -- Can't go lower than F!
```

Our formalization can already help us understand some corner cases of the grading policy.
For example, we might expect that if we use the `lowerLetter` function its result will actually be lower,
as claimed in the following theorem. But this theorem is not provable! (Do you see why?)

```lean
  theorem lowerLetter_lowers_bad : ∀ (l : Letter),
    letterComparison (lowerLetter l) l = lt := sorry
```

This theorem is not provable because of the edge case of F!

```lean
theorem lowerLetter_F_is_F : lowerLetter F = F := by rfl
```
:::dev
CGH: I got tired of porting at this point!
:::

```lean
end LateDays
```

## Binary Numerals

We can generalize our unary representation of natural numbers to
the more efficient binary representation by treating a binary
number as a sequence of constructors `b0` and `b1` (representing 0s
and 1s), terminated by a `z`.

For example:

:::table +header (align := right)
*
  * decimal
  * binary
  * unary
*
  * 0
  * `z`
  * `zero`
*
  * 1
  * `b1 z`
  * `succ zero`
*
  * 2
  * `b1 z`
  * `succ (succ zero)`
*
  * 3
  * `b1 (b1 z)`
  * `succ (succ (succ zero))`
*
  * 4
  * `b0 (b0 (b1 z))`
  * `succ (succ (succ (succ zero)))`
*
  * 5
  * `b1 (b0 (b1 z))`
  * `succ (succ (succ (succ (succ zero))))`
*
  * 6
  * `b0 (b1 (b1 z))`
  * `succ (succ (succ (succ (succ (succ zero)))))`
*
  * 7
  * `b1 (b1 (b1 z))`
  * `succ (succ (succ (succ (succ (succ (succ zero))))))`
*
  * 8
  * `b0 (b0 (b0 (b1 z)))`
  * `succ (succ (succ (succ (succ (succ (succ (succ zero)))))))`
:::

Note that the low-order bit is on the left and the high-order bit
is on the right - the opposite of the way binary numbers are
usually written.  This choice makes them easier to manipulate.

(Comprehension check: What unary numeral does `b0 z` represent?)

:::exercise (name := "binary") (rating := 3)
Complete the definitions below of an increment function incr for binary numbers, and a function
`binToNat` to convert binary numbers to unary numbers.
```lean
inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)
```

```lean
def incr (m : Bin) : Bin := solution!(
  match m with
  | .z => .b1 .z
  | .b0 m' => .b1 m'
  | .b1 m' => .b0 (incr m')
  )
```

```lean
def binToNat (m : Bin) : Nat := solution!(
  match m with
  | .z => 0
  | .b0 m' => binToNat m' * 2
  | .b1 m' => binToNat m' * 2 + 1
  )
```

```lean
example : incr (.b1 .z) = .b0 (.b1 .z) := solution!(by rfl)
```
```lean
example : incr (.b0 (.b1 .z)) = .b1 (.b1 .z) := solution!(by rfl)
```
```lean
example : incr (.b1 (.b1 .z)) = .b0 (.b0 (.b1 .z)) := solution!(by rfl)
```
```lean
example : binToNat (.b0 (.b1 .z)) = 2 := solution!(by rfl)
```
```lean
example : binToNat (incr (.b1 .z)) = 1 + binToNat (.b1 .z) := solution!(by rfl)
```
```lean
example : binToNat (incr (incr (.b1 .z))) = 2 + binToNat (.b1 .z) := solution!(by rfl)
```
```lean
example : binToNat (.b0 (.b0 (.b0 (.b1 .z)))) = 8 := solution!(by rfl)

```
:::
