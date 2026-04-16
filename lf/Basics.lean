-- Basics: Functional Programming in Lean

-- INSTRUCTORS: This file and Induction.lean each take about an hour to
--    get through in a not-too-rushed fashion (with questions, etc.).
--    (BCP: Actually, in 2025 this file alone took me two full hours.)
--
--    You may want to assign both files together as the homework for the
--    first week, depending on the level of the class.  Just Basics is
--    fairly light for many students, but in a mixed class there will
--    be people that struggle with some of it.
--
--    PRESENTATION ADVICE: Working with the .lean file directly in VS Code
--    is recommended for the first few lectures, so students see exactly
--    what's in the source file.

-- HIDEFROMHTML
-- FULL
-- REMINDER:
--
--          #####################################################
--          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
--          #####################################################
--
--   (See the [Preface] for why.)
-- /FULL
-- /HIDEFROMHTML

-- ######################################################################
-- # Introduction

-- FULL
-- The _functional style_ of programming is founded on simple,
-- everyday mathematical intuitions: If a procedure or method has no
-- side effects, then (ignoring efficiency) all we need to understand
-- about it is how it maps inputs to outputs -- that is, we can think
-- of it as just a concrete method for computing a mathematical
-- function.  This is one sense of the word "functional" in
-- "functional programming."  The direct connection between programs
-- and simple mathematical objects supports both formal correctness
-- proofs and sound informal reasoning about program behavior.
--
-- The other sense in which functional programming is "functional" is
-- that it emphasizes the use of functions as _first-class_ values --
-- i.e., values that can be passed as arguments to other functions,
-- returned as results, included in data structures, etc.  The
-- recognition that functions can be treated as data gives rise to a
-- host of useful and powerful programming idioms.
--
-- Other common features of functional languages include _algebraic
-- data types_ and _pattern matching_, which make it easy to
-- construct and manipulate rich data structures, and _polymorphic
-- type systems_ supporting abstraction and code reuse.  Lean offers
-- all of these features.
--
-- The first half of this chapter introduces some key elements of
-- Lean's functional programming language.  The second half introduces
-- some basic _tactics_ that can be used to prove properties of
-- programs.
-- /FULL

-- ######################################################################
-- # Data and Functions

-- ## Enumerated Types

-- TERSE: In Lean, we can build practically everything from first principles...
--     FULL One notable thing about Lean is that its set of built-in features is
--     _extremely_ small.  For example, instead of the usual palette of atomic
--     data types (booleans, integers, strings, etc.), Lean offers a powerful
--     mechanism for defining new data types from scratch, with all these
--     familiar types as instances.
--
-- Naturally, Lean also comes with an extensive standard library providing
-- definitions of booleans, numbers, and many common data structures like lists
-- and hash tables.  But there is nothing magic or primitive about these library
-- definitions.  To illustrate this, in this course we will explicitly
-- recapitulate almost all the definitions we need, rather than getting them
-- from the standard library.
-- RAB ADDITION:
-- We take great care to match those definitions with the ones in the standard
-- library, so that by the time you are finished with this course, you will
-- already have a strong understanding of how the Lean standard library works.
-- /FULL

-- ######################################################################
-- ## Days of the Week

-- TERSE: A datatype definition:

-- FULL
-- To see how the datatype definition mechanism works, let's
-- start with a very simple example.  The following declaration tells
-- Lean that we are defining a set of data values -- a _type_.
-- /FULL

inductive Day : Type where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

-- FULL
-- The new type is called `Day`, and its members are `monday`,
-- `tuesday`, etc.
--
-- Having defined `Day`, we can write functions that operate on days.
-- /FULL
-- TERSE: ***
-- TERSE: A function on days:

def nextWorkingDay (d : Day) : Day :=
  match d with
  | .monday    => .tuesday
  | .tuesday   => .wednesday
  | .wednesday => .thursday
  | .thursday  => .friday
  | .friday    => .monday
  | .saturday  => .monday
  | .sunday    => .monday

-- FULL
-- Note that the argument and return types of this function are
-- explicitly declared on the first line.  Like most functional
-- programming languages, Lean can often figure out these types for
-- itself when they are not given explicitly -- i.e., it can do _type
-- inference_ -- but we'll generally include them to make reading
-- easier.

-- RAB ADDITION
-- You may also notice the unique pattern matching syntax- for
-- example, in "`.monday`". The `.` - is syntactic sugar for `Day.monday`, and
-- exists to save the programmer the time of typing out the full qualified name.
-- You may wonder why the language doesn't just expose a pattern like `monday`
-- without the dot, like OCaml does. This is to avoid name shadowing, because
-- being explicit about names is _especially_ important to avoid confusion and
-- headaches when writing proofs. The `.` syntax is a compromise that lets us
-- know we're qualifying a name without having to type too much.

-- /FULL

-- TERSE: ***
-- TERSE: Evaluation:
-- FULL
-- Having defined a function, we can check that it works on
-- some examples.  There are actually three different ways to do
-- examples in Lean.  First, we can use the `#eval` command to
-- evaluate a compound expression involving `nextWorkingDay`.
-- /FULL

#eval nextWorkingDay Day.friday
-- ==> Day.monday

#eval nextWorkingDay (nextWorkingDay Day.saturday)
-- ==> Day.tuesday

-- FULL
-- (We show Lean's responses in comments; if you have a computer
-- handy, this would be an excellent moment to fire up VS Code with
-- the Lean extension and try it for yourself.  Load this file,
-- `Basics.lean`, from the book's Lean sources, find the above
-- example, and observe the result in the Lean Infoview panel.)

-- RAB ADDITION

-- Using the Lean Extension

-- In VSCode, development of Lean code is supported by
-- the Lean Extension, which provides an interactive "infoview" panel that
-- displays the results of commands like `#eval` and `#check`, as well as the
-- current goal state when working on proofs. You can hover over expressions in
-- the source code to see their types, and you can click on the results in the
-- infoview to navigate to their definitions. This makes it easier to understand
-- how your code is being interpreted by Lean and to debug any issues that
-- arise.

-- The infoview always follows your cursor, and Lean typechecks the file as you
-- edit it, so you can see the results of your changes immediately. You can also
-- use the infoview to explore the definitions of functions and types that
-- you're using, which can be very helpful for understanding how they work.

-- If you haven't already, install the Lean Extension in VSCode and open the
-- `Basics.lean` file to see the infoview in action. Try hovering over the
-- `nextWorkingDay` function and the `Day` type to see their definitions, and
-- experiment with adding your own `#eval` commands to test other inputs.

-- NOTE: There's a question of where exactly to put this.

-- /FULL

-- Second, we can record what we _expect_ the result to be in the
-- form of a Lean "example":

-- test_next_working_day
example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.tuesday := by
  rfl

-- FULL
-- This declaration does two things: it makes an assertion
-- (that the second working day after `saturday` is `tuesday`), and it
-- gives the assertion a name that can be used to refer to it later.
-- Having made the assertion, we can also ask Lean to _verify_ it.
-- The `by rfl` can be read as "The assertion we've just made can be
-- proved by observing that both sides of the equality evaluate to
-- the same thing."

-- `rfl` stands for "reflexivity," which is the principle that any value is
-- equal to itself. After evaluation, both sides of the equality are the same
-- value, so the assertion is true by reflexivity.  If we had made a different
-- assertion, such as `example : nextWorkingDay (nextWorkingDay Day.saturday) =
-- Day.monday`, then Lean would not be able to verify it, and would signal an
-- error. Try it out!

-- /FULL

-- Third, we can ask Lean to _compile_ our definitions to efficient
-- native code.  Lean compiles to C, which is then compiled to machine
-- code by a standard C compiler.  This facility is very useful, since
-- it gives us a path from proved-correct algorithms written in Lean to
-- efficient executables.
--
-- Indeed, this is one of the main uses for which Lean was developed.
-- We'll come back to this topic in later chapters.

-- ######################################################################
-- ## Booleans

-- FULL
-- Following the pattern of the days of the week above, we can
-- define the standard type `Bool` of booleans, with members `true`
-- and `false`.
-- /FULL
-- TERSE: Another familiar enumerated type:

-- We define our own `MyBool` to teach the concept of building from
-- scratch; later we'll switch to Lean's built-in `Bool`.

/- JC: Can we just gloss over what `section` is doing here,
  or do we need to explain it? -/

-- RAB: No need, I think.
section

inductive MyBool : Type where
  | true
  | false
open MyBool

-- TERSE: Booleans are also available in Lean's standard library, but
--     in this course we'll define everything from scratch, just to see
--     how it's done.
-- TERSE: ***
-- FULL
-- Functions over booleans can be defined in the same way as above:
-- /FULL

def notb (b : MyBool) : MyBool :=
  match b with
  | .true => false
  | .false => true

-- TERSE: ***

def andb (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | .true => b2
  | .false => false

def orb (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | .true => true
  | .false => b2

-- FULL
-- (Although we are rolling our own booleans here for the sake
-- of building up everything from scratch, Lean does, of course,
-- provide a default implementation of the booleans, together with a
-- multitude of useful functions and lemmas.)
-- /FULL

-- FULL
-- The last two of these illustrate Lean's syntax for
-- multi-argument function definitions.  The corresponding
-- multi-argument _application_ syntax is illustrated by the
-- following "unit tests," which constitute a complete specification
-- -- a truth table -- for the `orb` function:
-- /FULL
-- TERSE: Note the syntax for defining multi-argument
--     functions (`andb` and `orb`).
-- TERSE: ***

-- test_orb1
example : orb .true  .false = .true  := by rfl
-- test_orb2
example : orb .false .false = .false := by rfl
-- test_orb3
example : orb .false .true  = .true  := by rfl
-- test_orb4
example : orb .true  .true  = .true  := by rfl

-- We can define new symbolic notations for existing definitions.
-- Because Lean already defines these for the built-in `Bool`,
-- we restrict ours locally to a section.

section
local prefix:40 (priority := high) "!" => notb
local infixl:35 (priority := high) " && " => andb
local infixl:30 (priority := high) " || " => orb

-- test_orb5
example : (.false || .false || .true) = .true := by rfl

-- test_orb6
example : (! .false) = .true := by rfl
end

-- TERSE: ***
-- EX1 (nandb)
-- FULL
-- The `sorry` keyword can be used as a placeholder for an
-- incomplete proof or definition.  We use it in exercises to indicate
-- the parts that we're leaving for you -- i.e., your job is to replace
-- `sorry` with real definitions and proofs.
--
-- Remove `sorry` below and complete the definition of the
-- following function; then make sure that the `example` assertions
-- below can each be verified by Lean.  The function should return
-- `true` if either or both of its inputs are `false`.
-- /FULL

def nandb (b1 : MyBool) (b2 : MyBool) : MyBool
  -- ADMITDEF
  := match b1 with
  | .true => notb b2
  | .false => true
  -- /ADMITDEF

-- test_nandb1
example : nandb .true .false  = .true  := by rfl  -- ADMITTED
-- test_nandb2
example : nandb .false .false = .true  := by rfl  -- ADMITTED
-- test_nandb3
example : nandb .false .true  = .true  := by rfl  -- ADMITTED
-- test_nandb4
example : nandb .true .true   = .false := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: nandb_test4
-- []

-- FULL
-- EX1 (andb3)
-- Do the same for the `andb3` function below. This function should
-- return `true` when all of its inputs are `true`, and `false`
-- otherwise.

def andb3 (b1 : MyBool) (b2 : MyBool) (b3 : MyBool) : MyBool
  -- ADMITDEF
  := andb b1 (andb b2 b3)
  -- /ADMITDEF

-- test_andb31
example : andb3 .true .true .true  = .true  := by rfl  -- ADMITTED
-- test_andb32
example : andb3 .false .true .true = .false := by rfl  -- ADMITTED
-- test_andb33
example : andb3 .true .false .true = .false := by rfl  -- ADMITTED
-- test_andb34
example : andb3 .true .true .false = .false := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: andb3_test4
-- []
-- /FULL

/- JC: Now would be a good time to explicitly say we're switching
  back to Lean's Bool, which conveniently has `bif ... then ... else`
  syntax that we can then use. -/

  -- RADDTION

-- TERSE: ***
-- FULL
-- Now that we've seen how to define our own booleans, we can switch back to
-- Lean's built-in `Bool` type, which has the same structure but also includes
-- a lot of useful functions and lemmas.  We can even define functions to
-- convert between our `MyBool` and Lean's `Bool`.

def myBoolToBool (b : MyBool) : Bool :=
  match b with
  | .true => true
  | .false => false

-- With the full power of Lean's `Bool` at our disposal, we can also write this
-- more concisely using the `bif ... then ... else` syntax, which is a
-- convenient way to write simple conditional expressions.

def boolToMyBool (b : Bool) : MyBool :=
  bif b then true else false

end

-- RAB: From this point, there are about 450 lines of comments before
-- the next exercise. This is the same as in Rocq, but do we want
-- to keep this pattern?

-- ######################################################################
-- ## Types

-- Every expression in Lean has a type describing what sort of
-- thing it computes.  The `#check` command asks Lean to print the type
-- of an expression.

#check true
-- ===> true : Bool

-- If the thing after `#check` is followed by a colon and a type,
-- Lean will verify that the type of the expression
-- matches the given type and signal an error if not.

#check (true : Bool)
#check (not true : Bool)

-- Functions like `not` itself are also data values, just like
-- `true` and `false`.  Their types are called _function types_, and
-- they are written with arrows.

#check not
-- ===> not : Bool → Bool

-- FULL
-- The type of `not`, written `Bool → Bool` and pronounced
-- "`Bool` arrow `Bool`," can be read, "Given an input of type
-- `Bool`, this function produces an output of type `Bool`."
-- Similarly, the type of `and`, written `Bool → Bool → Bool`, can
-- be read, "Given two inputs, each of type `Bool`, this function
-- produces an output of type `Bool`."

-- RAB ADDITION

-- You may notice that → is a unicode character, not a simple ASCII string. This
-- is a common convention in Lean, and the Lean Extension provides convenient
-- shortcuts for entering these characters. Simply typing \ (backslash) followed
-- by the name of the character, and the extension will automatically replace it
-- with the correct symbol. For example, typing \-> or \to will produce →, and
-- \lambda will produce λ. This allows you to write more concise and readable
-- code without having to remember complex keyboard shortcuts.

-- /FULL


-- ######################################################################
-- ## New Types from Old

-- FULL
-- The types we have defined so far are examples of simple
-- "enumerated types": their definitions explicitly enumerate a
-- finite set of elements, called _constructors_.  Here is a more
-- interesting type definition, `Color`, where one of the
-- constructors takes an argument:
-- /FULL
-- TERSE: A more interesting type definition:

inductive RGB : Type where
  | red
  | green
  | blue

inductive Color : Type where
  | black
  | white
  | primary (p : RGB)

-- Let's look at this in a little more detail.
--
-- An `inductive` definition does two things:
--
-- - It introduces a set of new _constructors_. E.g., `RGB.red`,
--   `Color.primary`, `true`, `false`, `Day.monday`, etc. are constructors.
--
-- - It groups them into a new named type, like `Bool`, `RGB`, or
--   `Color`.
--
-- _Constructor expressions_ are formed by applying a constructor
-- to zero or more other constructors or constructor expressions,
-- obeying the declared number and types of the constructor arguments.
-- E.g., these are valid constructor expressions...
--     - `RGB.red`
--     - `true`
--     - `Color.primary RGB.red`
--     - etc.
-- ...but these are not:
--     - `RGB.red Color.primary`
--     - `true RGB.red`
--     - `Color.primary (Color.primary RGB.red)`
--     - etc.

-- TERSE: ***

-- We can define functions on colors using pattern matching just as
-- we did for `Day` and `Bool`.

def monochrome (c : Color) : Bool :=
  match c with
  | .black => true
  | .white => true
  | .primary _ => false

-- Since the `primary` constructor takes an argument, a pattern
-- matching `primary` should include either a variable, as we just
-- did (note that we can choose its name freely), or a constant of
-- appropriate type (as below).

def isRed (c : Color) : Bool :=
  match c with
  | .black => false
  | .white => false
  | .primary .red => true
  | .primary _ => false

-- The pattern `Color.primary _` here is shorthand for "the constructor
-- `primary` applied to any `RGB` constructor except `red`."

-- ######################################################################
-- ## Namespaces and Sections

/- JC: I edited a lot of the contents and comments in just this section,
  I hope it makes sense. -/

-- FULL
-- Lean provides a _namespace system_ to aid in organizing large
-- developments.  If we enclose a collection of declarations in
-- `namespace X ... end X`, then, in the remainder of the file
-- after the `end`, these definitions are referred to by names like
-- `X.foo` instead of just `foo`.  We will use this feature to limit
-- the scope of definitions, so that we are free to reuse names.
-- /FULL
-- TERSE: `namespace` declarations create separate namespaces.

namespace Playground
def myFoo : RGB := RGB.blue
end Playground

def myFoo : Bool := true

#check Playground.myFoo  -- RGB
#check myFoo             -- Bool

-- FULL
-- Inside of a namespace, all previous definitions from that namespace are
-- available, and can be referred to without prefixing.
-- Definitions can also be prefixed by a namespace to put it in the namespace
-- without having to open and close the namespace.
-- /FULL

namespace RGB
def myBlue : RGB := blue
end RGB

def RGB.myOtherBlue : RGB := myBlue

-- #check myBlue -- unknown identifier
#check RGB.myBlue      -- RGB
#check RGB.myOtherBlue -- RGB

-- FULL
-- We can also use `open` to bring the definitions of a namespace into scope.
-- This makes it convenient to refer to all of those definitions without
-- a prefix. Original definitions of the same name can then be referred to
-- by the special prefix `_root_`.
-- Lean also provides _sections_, which delimit the scope of `open`ing
-- namespaces and `local` notations within `section ... end`.
-- We already saw `prefix` and `infix` notations for MyBool;
-- there are also `postfix` notations.
-- /FULL
-- TERSE: `section` declarations delimit the scope of `open` and `local`.

section
open Playground
local postfix:40 "′" => Color.primary

#check myFoo        -- RGB
#check _root_.myFoo -- Bool
#check RGB.blue′    -- Color
end

#check myFoo         -- Bool
-- #check RGB.blue′  -- fails to parse

-- ######################################################################
-- ## Tuples

namespace TuplePlayground

-- FULL
-- A single constructor with multiple parameters can be used
-- to create a tuple type. As an example, consider representing
-- the four bits in a nybble (half a byte). We first define
-- a datatype `Bit` that resembles `Bool` (using the
-- constructors `b1` and `b0` for the two possible bit values)
-- and then define the datatype `Nybble`, which is essentially
-- a tuple of four bits.

-- RAB: Is this called a Nybble, not a Nibble? Whatever the Penn systems course
-- calls it, we should follow suite, I guess.

-- /FULL

-- TERSE: A nybble is half a byte -- four bits.

inductive Bit : Type where
  | b1
  | b0

inductive Nybble : Type where
  | bits (x0 x1 x2 x3 : Bit)

#check (.bits .b1 .b0 .b1 .b0 : Nybble)

-- FULL
-- The `bits` constructor acts as a wrapper for its contents.
-- Unwrapping can be done by pattern-matching, as in the `allZero`
-- function below, which tests a nybble to see if all its bits are
-- `b0`.
-- /FULL

-- TERSE: ***
-- TERSE: We can deconstruct a nybble by pattern-matching.

def allZero (nb : Nybble) : Bool :=
  match nb with
  | .bits .b0 .b0 .b0 .b0 => true
  | .bits _   _   _   _   => false

-- (The underscore `_` here is a _wildcard pattern_, which avoids
-- inventing variable names that will not be used.)

#eval allZero (.bits .b1 .b0 .b1 .b0)
-- ===> false
#eval allZero (.bits .b0 .b0 .b0 .b0)
-- ===> true

end TuplePlayground

-- ######################################################################
-- ## Numbers

-- FULL
-- We put this section in a namespace so that our own definition of
-- natural numbers does not interfere with the one from the
-- standard library.  In the rest of the book, we'll want to use
-- the standard library's.
-- /FULL

namespace NatPlayground

-- FULL
-- All the types we have defined so far -- both "enumerated
-- types" such as `Day`, `Bool`, and `Bit` and tuple types such as
-- `Nybble` built from them -- are finite.  The natural numbers, on
-- the other hand, are an infinite set, so we'll need to use a
-- slightly richer form of type declaration to represent them.

-- RAB: I moved over the notes from the Rocq book here, as I find they
-- very nicely motivate unary for someone who has not seen it before.

-- There are many representations of numbers to choose from. You are
-- certainly familiar with decimal notation (base 10), using the
-- digits 0 through 9, for example, to form the number 123. You may
-- very likely also have encountered hexadecimal notation (base 16),
-- in which the same number is represented as 7B, or octal (base 8),
-- where it is 173, or binary (base 2), where it is 1111011. Using an
-- enumerated type to represent digits, we could use any of these as
-- our representation natural numbers. Indeed, there are
-- circumstances where each of these choices would be useful.

-- The binary representation is valuable in computer hardware because
-- the digits can be represented with just two distinct voltage
-- levels, resulting in simple circuitry. Analogously, we wish here
-- to choose a representation that makes _proofs_ simpler.

-- In fact, there is a representation of numbers that is even simpler
-- than binary, namely unary (base 1), in which only a single digit
-- is used -- as our forebears might have done to count days by
-- making scratches on the walls of their caves. To represent unary
-- numbers with a Lean datatype, we use two constructors. The
-- [zero] constructor represents zero. The [succ] constructor can be
--applied to the representation of the natural number [n], yielding
-- the representation of [n+1], where [succ] stands for "successor."
--  Here is the complete datatype definition: *)

-- /FULL

-- TERSE: For simplicity in proofs, we choose unary representation.

inductive Nat : Type where
  | zero
  | succ (n : Nat)

-- With this definition, 0 is represented by `zero`, 1 by `succ zero`,
-- 2 by `succ (succ zero)`, and so on.

-- TERSE: ***
-- Critical point: this just defines a _representation_ of
-- numbers -- a unary notation for writing them down.

inductive OtherNat : Type where
  | stop
  | tick (foo : OtherNat)

-- This is the same _representation_ of numbers as `Nat`, but with different
-- (sillier!) constructor names.

-- The _interpretation_ of these representations arises from how we use them to
-- compute.

def pred (n : Nat) : Nat :=
  match n with
  | .zero => .zero
  | .succ n' => n'

end NatPlayground

-- TERSE: ***

-- Because natural numbers are such a pervasive kind of data,
-- Lean provides built-in support for them: ordinary decimal
-- numerals can be used as a shorthand, and Lean's `Nat` type uses
-- the constructors `Nat.zero` and `Nat.succ`.

-- RAB: Hovering over succ points out that "Using Nat.succ n should usually be
-- avoided in favor of n + 1, which is the simp normal form." How quickly should
-- we break away from succ style and go straight to n + 1 style? More broadly,
-- how much do we want to adhere to conventions like simp normal form? In my
-- view, following standard Lean style wherever possible is a good thing to be
-- doing, in no small part because proof view displays terms in Lean style, e.g. (n +
-- 1) instead of .succ n.

example : .succ (.succ (.succ (.succ .zero))) = 4 := by rfl

def minustwo (n : Nat) : Nat :=
  match n with
  | 0                => 0
  | 1                => 0
  | .succ (.succ n') => n'

#eval minustwo 4
-- ===> 2

-- FULL
#check Nat.succ  -- Nat → Nat
#check Nat.pred  -- Nat → Nat
#check minustwo  -- Nat → Nat

-- These are all things that can be applied to a number to yield a
-- number.  However, there is a fundamental difference between `Nat.succ`
-- and the other two: functions like `Nat.pred` and `minustwo` are
-- defined by giving _computation rules_ -- e.g., the definition of
-- `Nat.pred` says that `Nat.pred 2` can be simplified to `1` -- while the
-- definition of `Nat.succ` has no such behavior attached.  Although it is
-- _like_ a function in the sense that it can be applied to an
-- argument, it does not _do_ anything at all!  It is just a way of
-- writing down numbers.
-- /FULL

-- TERSE: ***
-- TERSE: Recursive functions:

def even (n : Nat) : Bool :=
  match n with
  | 0                => true
  | 1                => false
  | .succ (.succ n') => even n'

-- TERSE: ***
-- We could define `odd` by a similar recursive declaration, but
-- here is a simpler way:

def odd (n : Nat) : Bool :=
  not (even n)

-- test_odd1
example : odd 1 = true  := by rfl
-- test_odd2
example : odd 4 = false := by rfl

-- TERSE: ***
-- TERSE: A multi-argument recursive function.

-- Note: Lean's built-in `Nat.add` recurses on the _second_ argument,
-- so we follow the same convention here.  This means `n + 0` reduces
-- by definition, but `0 + n` does not (the reverse of Rocq).

def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | 0 => n
  | .succ m' => .succ (add n m')

-- FULL
-- Adding three to two gives us five (whew!):
-- /FULL

#eval add 3 2
-- ===> 5

-- FULL
-- The steps of simplification that Lean performs here can be
-- visualized as follows:
--
--      `add 3 2`
--   i.e. `add (succ (succ (succ 0))) (succ (succ 0))`
--    ==> `succ (add (succ (succ (succ 0))) (succ 0))`
--          by the second clause of the `match`
--    ==> `succ (succ (add (succ (succ (succ 0))) 0))`
--          by the second clause of the `match`
--    ==> `succ (succ (succ (add (succ 0))))`
--          by the first clause of the `match`
--   i.e. `5`
-- /FULL

-- TERSE: ***

/- JC: Add some text here about how we're using Lean's `add`,
  not our own `add`, because it provides the `+` notation for `Nat`
  that would be problematic (vague?) to override.
  But overriding the rest of the notation is fine though. -/

def mul (n m : Nat) : Nat :=
  match m with
  | 0 => 0
  | .succ m' => n + (mul n m')

-- test_mult1
example : mul 3 3 = 9 := by rfl

-- TERSE: ***
-- We can pattern-match two values at the same time:

def sub (n m : Nat) : Nat :=
  match n, m with
  | 0,        _        => 0
  | .succ _,  0        => n
  | .succ n', .succ m' => sub n' m'

-- Now that we've seen how natural numbers are built from `Nat.zero`
-- and `Nat.succ`, we can take advantage of Lean's notation: the
-- pattern `n + 1` is syntactic sugar for `Nat.succ n`, `n + 2` is
-- syntactic sugar for `Nat.succ (Nat.succ n)`, and so on.
-- We'll use this more concise style from now on.

-- FULL
def pow (base power : Nat) : Nat :=
  match power with
  | 0 => 1
  | p + 1 => mul base (pow base p)

-- EX1 (factorial)
-- Recall the standard mathematical factorial function:
--        factorial(0)  =  1
--        factorial(n)  =  n * factorial(n-1)     (if n>0)
-- Translate this into Lean.

def factorial (n : Nat) : Nat
  -- ADMITDEF
  := match n with
  | 0 => 1
  | n' + 1 => n * factorial n'
  -- /ADMITDEF

-- test_factorial1
example : factorial 3 = 6         := by rfl  -- ADMITTED
-- test_factorial2
example : factorial 5 = 10 * 12   := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: factorial_test2
-- []
-- /FULL

-- TERSE: ***
-- Lean already provides `+`, `-`, `*` for `Nat`, so we don't need to
-- define our own notation.

/- JC: Overriding the `+` is an immense headache for technical reasons,
  so we leave that alone, since our definition is the same anyway.
  In contrast, our `sub` and `mul` definitions _are_ slightly different,
  so we _do_ want to override the notation instances for them. -/

instance instSub : Sub Nat where sub := sub
instance instMul : Mul Nat where mul := mul
instance instPow : Pow Nat Nat where pow := pow

/- JC: In the infoview, hover over the operators
  to check out their associativity --
  `+`, `-`, and `*` all left-associative,
  but `^` is right-associative. -/

#check (0 + 1 + 1 : Nat)
#check (4 - 3 - 2 : Nat)
#check (2 * 3 * 4 : Nat)
#check (1 ^ 2 ^ 2 : Nat)

-- TERSE: ***
-- When we say that Lean comes with almost nothing built-in, we really
-- mean it: even testing equality is a user-defined operation!
--
-- Here is a function `beq` that tests natural numbers for
-- equality, yielding a boolean.

def beq (n m : Nat) : Bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | _ + 1 => false
  | n' + 1 => match m with
              | 0 => false
              | m' + 1 => beq n' m'

-- TERSE: ***
-- Similarly, the `leb` function tests whether its first argument is
-- less than or equal to its second argument, yielding a boolean.

def leb (n m : Nat) : Bool :=
  match n with
  | 0 => true
  | n' + 1 =>
      match m with
      | 0 => false
      | m' + 1 => leb n' m'

-- test_leb1
example : leb 2 2 = true  := by rfl
-- test_leb2
example : leb 2 4 = true  := by rfl
-- test_leb3
example : leb 4 2 = false := by rfl

-- TERSE: ***
-- We'll be using these (especially `beq`) a lot, so let's give
-- them infix notations.

/- JC: Lean's stdlib has `==` notation for `beq`,
  but not for `Nat.ble`... -/

instance : BEq Nat where
  beq := beq

infix:65 "<=?" => leb

-- test_leb3'
example : 4 <=? 2 = false := by rfl

-- FULL
-- We now have two symbols that both look like equality: `=`
-- and `=?`.  We'll have much more to say about their differences and
-- similarities later. For now, the main thing to notice is that
-- `x = y` is a logical _claim_ -- a "proposition" -- that we can try to
-- prove, while `x =? y` is a boolean _expression_ whose value (either
-- `true` or `false`) we can compute.
-- /FULL

-- FULL
-- EX1 (ltb)
-- Define a less-than function in terms of `leb`.

def ltb (n m : Nat) : Bool
  -- ADMITDEF
  := leb (n + 1) m
  -- /ADMITDEF

infix:65 "<?" => ltb

-- test_ltb1
example : 2 <? 2 = false := by rfl  -- ADMITTED
-- test_ltb2
example : 2 <? 4 = true  := by rfl  -- ADMITTED
-- test_ltb3
example : 4 <? 2 = false := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: ltb_test3
-- []
-- /FULL

-- ######################################################################
-- # Proof by Simplification

-- FULL
-- Now that we've looked at a few datatypes and functions,
-- let's turn to stating and proving properties of their behavior.
--
-- Actually, we've already started doing this: each `example` in the
-- previous sections made a precise claim about the behavior of some
-- function on some particular inputs.  The proofs of these claims
-- were always the same: use `rfl` to check that both sides of the
-- equation evaluate to identical values.
-- /FULL

-- TERSE: A specific fact about natural numbers:
-- plus_1_1
example : 1 + 1 = 2 := by rfl

-- TERSE: Another specific fact about natural numbers:
-- JC: Keep the name for this one, it gets used later.
theorem add_zero_one : 1 = 0 + 1 := by rfl

-- FULL
-- The same sort of "proof by simplification" can also be used to
-- establish more interesting properties.  For example, the
-- fact that `0` is a "neutral element" for `+` on the left can be
-- proved just by observing that `0 + n` reduces to `n` no matter
-- what `n` is.
-- /FULL

-- TERSE: A general property of natural numbers:

-- Note: Because Lean's addition recurses on the second argument,
-- `n + 0` reduces to `n` by definition.  (In Rocq, it is `0 + n`
-- that reduces by definition, because Rocq's addition recurses on
-- the first argument.)

theorem add_zero : ∀ n : Nat, n + 0 = n := by
  intro n; rfl

-- FULL
-- The keywords `intro` and `rfl` are examples of _tactics_.
-- A tactic is a command that is used between `by` and the end of the
-- proof to guide the process of checking some claim we are making.
-- The semicolon `;` separates multiple steps of tactics;
-- they can also be separated by putting them on separate lines.
-- We will see several more tactics in the rest of this chapter and
-- many more in future chapters.
-- /FULL

-- TERSE: ***

theorem add_succ : ∀ n m : Nat, n + (m + 1) = (n + m) + 1 := by
  intro n m; rfl

theorem mul_zero : ∀ n : Nat, n * 0 = 0 := by
  intro n; rfl

theorem mul_succ : ∀ n m : Nat, n * (m + 1) = n + n * m := by
  intro n m; rfl

/- JC: Dumping the rest of the properties here.
  They're needed because the notations prevent reducing from left to right
  by just `dsimp [sub]` or `dsimp [pow]`.
  I don't think these properties are actually used by us,
  so maybe they can just be exercises. -/

#check Nat.sub_zero

theorem sub_zero n : 0 - n = 0 := by rfl
theorem succ_sub_zero n : (n + 1) - 0 = n + 1 := by rfl
theorem succ_sub_succ n m : (n + 1) - (m + 1) = n - m := by rfl

theorem pow_zero n : n ^ 0 = 1 := by rfl
theorem pow_succ (n m : Nat) : n ^ (m + 1) = n * (n ^ m) := by rfl

/- JC: And another one, which we _do_ use later. -/

theorem beq_succ : ∀ n m : Nat, (n + 1 == m + 1) = (n == m) := by
  intro n m; rfl

-- ######################################################################
-- # Proof by Rewriting

-- TERSE: A (slightly) more interesting theorem:

theorem plus_id_example : ∀ n m : Nat,
    n = m →
    n + n = m + m := by
  -- FULL
  -- Instead of making a universal claim about all numbers `n` and `m`,
  -- this talks about a more specialized property that only holds when
  -- `n = m`.  The arrow symbol is pronounced "implies."
  --
  -- The tactic that tells Lean to perform replacement is called `rewrite`.
  -- /FULL
  intro n m
  intro h
  rewrite [h]
  rfl

-- TERSE: The `intro` tactic names the hypotheses as they are moved
--     to the context.  The `rewrite` tactic rewrites using an equality.
-- FULL
-- By default, `rewrite` rewrites left-to-right. To rewrite from right
-- to left, use `rewrite [← h]`, where `←` is typed as `\l` or `\<-`.
-- Because the pattern `rewrite [h]; rfl` is so common, Lean provides
-- `rw [h]` as shorthand.
-- /FULL

-- FULL
-- EX1 (plus_id_exercise)
-- Remove `sorry` and fill in the proof.

theorem plus_id_exercise : ∀ n m o : Nat,
    n = m → m = o → n + m = m + o := by
  -- ADMITTED
  intro n m o h1 h2
  rw [h1, h2]
  -- /ADMITTED
-- GRADE_THEOREM 1: plus_id_exercise
-- []
-- /FULL

-- FULL
-- The `sorry` keyword tells Lean that we want to skip trying
-- to prove this theorem and just accept it as a given.  This is
-- often useful for developing longer proofs.
--
-- Be careful, though: every time you say `sorry` you are leaving
-- a door open for total nonsense to enter Lean's safe, formally
-- checked world!
-- /FULL

-- TERSE: ***

-- The `#check` command can also be used to examine the statements of
-- previously declared lemmas and theorems.

#check mul_zero  -- ∀ (n : Nat), n * 0 = 0
#check mul_succ  -- ∀ (n m : Nat), n * Nat.succ m = n + n * m

-- TERSE: ***
-- We can use the `rw` tactic with a previously proved theorem
-- instead of a hypothesis from the context.

theorem add_mul_zero : ∀ p q : Nat,
    (p * 0) + (q * 0) = 0 := by
  intro p q
  rw [mul_zero, mul_zero, add_zero]

-- FULL
-- EX1 (mult_n_1)
theorem mul_one : ∀ p : Nat,
    p * 1 = p := by
  -- ADMITTED
  intro p
  rw [add_zero_one, mul_succ, mul_zero, add_zero]
  -- /ADMITTED
-- GRADE_THEOREM 1: mult_n_1
-- []
-- /FULL

theorem mul_two : ∀ p : Nat,
    p * 2 = p + p := by
  intro p
  rw [mul_succ, mul_succ, mul_zero, add_zero]

-- ######################################################################
-- # Proof by Case Analysis

-- FULL
-- Of course, not everything can be proved by simple
-- calculation and rewriting: In general, unknown, hypothetical
-- values (arbitrary numbers, booleans, lists, etc.) can block
-- simplification.
-- /FULL

-- TERSE: Sometimes simple calculation and rewriting are not enough...
example : ∀ n : Nat,
    (n + 1 == 0) = false := by
  intro n
  -- `rfl` doesn't work here because `n` is unknown
  sorry

-- FULL
-- The tactic that tells Lean to consider separate cases is called
-- `cases`.
-- /FULL

-- TERSE: We can use `cases` to perform case analysis:

theorem add_one_neb_zero : ∀ n : Nat,
    (n + 1 == 0) = false := by
  intro n
  cases n
  case zero => rfl
  case succ n' => rfl

-- FULL
-- The `cases` tactic generates _two_ subgoals, which we must then
-- prove, separately, in order to get Lean to accept the theorem.
--
-- The generated subgoals are tagged by the names of the constructors.
-- `case zero =>` and `case succ n' =>` select which subgoal to work on next
-- and introduce variable names.
--
-- The `cases` tactic can be used with any inductively defined
-- datatype.  For example, we use it next to prove that boolean
-- negation is involutive -- i.e., that negation is its own inverse.
-- /FULL

-- TERSE: ***
-- TERSE: Another example, using booleans:

theorem notb_involutive : ∀ b : Bool,
    (!!b) = b := by
  intro b
  cases b
  case true => rfl
  case false => rfl

-- TERSE: ***
-- TERSE: We can have nested case analysis:

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

-- FULL

-- If there are no constructor arguments that need names, we can use
-- `<;>` to apply the same tactic to all generated goals:
theorem andb3_exchange : ∀ b c d : Bool,
    ((b && c) && d) = ((b && d) && c) := by
  intro b c d
  cases b
  case true =>
    cases c
    case true => cases d <;> rfl -- case on `d`, then `rfl` all generated subgoals.
    case false => cases d <;> rfl
  case false =>
    cases c
    case true => cases d <;> rfl
    case false => cases d <;> rfl
-- /FULL

-- ** New Tactics: `dsimp`, `exact`, and `contradiction`
--
-- Some more tactics will be useful for the exercises ahead.
--
-- The `dsimp` tactic ("definitionally simplify") applies known facts
-- and definitions to simplify the goal.  You can give it hints in
-- square brackets: `dsimp [f]` tells it to unfold the definition
-- of `f`.  You can also simplify a hypothesis `h` in the context
-- by writing `dsimp [...] at h`. `dsimp` will also close goals by
-- `rfl` when possible.
--
-- The `exact` tactic closes a goal by providing an exact proof
-- term.  For example, if `h : P` is in the context and the goal
-- is `P`, then `exact h` closes the goal.  You can also
-- transform `h` slightly — for instance, `exact h.symm` uses
-- the symmetry of equality.

/- JC: I think this example should be rewritten to avoid `contradiction`,
  which gets discussed in detail in the Tactics chapter.
  I've added `orb_false_true` as a suggestion. -/

-- The `contradiction` closes a goal by looking for contradictory
-- assumptions in the context. For instance, if `h : 0 = 1` is in the
-- context, then `contradiction` closes the current goal, since such
-- a hypothesis is impossible.

-- FULL
-- EX2 (andb_true_elim2)
-- Prove the following claim.

theorem andb_true_elim2 : ∀ b c : Bool,
    (b && c) = true → c = true := by
  -- ADMITTED
  intro b c h
  cases b
  case true =>
    -- h : true && c = true, which simplifies to h : c = true
    dsimp [Bool.and] at h
    exact h
  case false =>
    -- h : false && c = true, which simplifies to h : false = true
    dsimp [Bool.and] at h
    contradiction
  -- /ADMITTED
-- GRADE_THEOREM 2: andb_true_elim2
-- []
-- /FULL

-- FULL
-- EX3 (orb_false_true)
-- Prove the following claim.

theorem orb_false_true : ∀ b : Bool,
    (false || b) = true → b = true := by
  -- ADMITTED
  intro b h
  dsimp [Bool.or] at h
  exact h
  -- /ADMITTED
-- GRADE_THEOREM 2: orb_false_true
-- []
-- /FULL

-- TERSE: ***
-- Again, we use <;> to apply `rfl` to the subgoals generated by `cases n`:
theorem add_one_neb_zero' : ∀ n : Nat,
    (n + 1 == 0) = false := by
  intro n; cases n <;> rfl

theorem andb_commutative'' : ∀ b c : Bool,
    (b && c) = (c && b) := by
  intro b c; cases b <;> cases c <;> rfl

-- FULL
-- EX1 (zero_nbeq_plus_1)
theorem zero_neb_add_one : ∀ n : Nat,
  (0 == n + 1) = false := by
  -- ADMITTED
  intro n; cases n <;> rfl
  -- /ADMITTED
-- GRADE_THEOREM 1: zero_nbeq_plus_1
-- []
-- /FULL

-- FULL
-- ######################################################################
-- ## More on Notation (Optional)

-- Lean has a very flexible notation system.  Operators like `+` and `*`
-- are defined with specified precedence and associativity.  For example,
-- `+` has precedence 65 and is left-associative, while `*` has
-- precedence 70 and is also left-associative.  This means that `1+2*3*4`
-- is parsed as `1+((2*3)*4)`.
--
-- You can define custom notation using the `notation`, `infixl`,
-- `infixr`, `prefix`, and `postfix` commands.
--
-- Unlike Rocq, Lean handles notation scoping through namespaces and
-- type classes rather than notation scopes.  The numeric literal `3`
-- can be interpreted as `Nat`, `Int`, `Float`, etc., depending on the
-- expected type, thanks to Lean's `OfNat` type class.
-- /FULL

-- FULL
-- ######################################################################
-- ## Structural Recursion (Optional)

-- Here is a copy of the definition of addition:

def plus' (n : Nat) (m : Nat) : Nat :=
  match n with
  | 0 => m
  | n' + 1 => (plus' n' m) + 1

-- When Lean checks this definition, it verifies that the recursion
-- terminates.  Specifically, it checks that one of the arguments
-- is _structurally decreasing_.  This implies that all calls to
-- `plus'` will eventually terminate.
--
-- This requirement is a fundamental feature of Lean's design: In
-- particular, it guarantees that every function that can be defined
-- in Lean will terminate on all inputs.  However, because Lean's
-- termination analysis is not always able to figure things out
-- automatically, it is sometimes necessary to provide hints or
-- write functions in slightly different ways.
--
-- Lean also supports more flexible termination proofs using
-- `termination_by` and `decreasing_by` clauses, as well as `partial`
-- functions that are not required to terminate.

-- EX2? (decreasing)
-- To get a concrete sense of this, find a way to write a sensible
-- recursive definition (of a simple function on numbers, say) that
-- _does_ terminate on all inputs, but that Lean will reject because
-- it cannot automatically prove termination.

-- SOLUTION
-- def factorial_bad (n : Nat) : Nat :=
--   if n == 0 then 1
--   else n * factorial_bad (n - 1)
-- This fails because Lean can't see that `n - 1` is structurally smaller.
-- /SOLUTION
-- []
-- /FULL

-- FULL
-- ######################################################################
-- # More Exercises

-- ## Warmups

-- EX1 (identity_fn_applied_twice)
-- Use the tactics you have learned so far to prove the following
-- theorem about boolean functions.

theorem identity_fn_applied_twice : ∀ f : Bool → Bool,
    (∀ x : Bool, f x = x) →
    ∀ b : Bool, f (f b) = b := by
  -- ADMITTED
  intro f h b
  rw [h, h]
  -- /ADMITTED
-- GRADE_THEOREM 1: identity_fn_applied_twice
-- []

-- EX1 (negation_fn_applied_twice)
-- Now state and prove a theorem `negation_fn_applied_twice` similar
-- to the previous one but where the hypothesis says that the
-- function `f` has the property that `f x = !x`.

-- SOLUTION
theorem negation_fn_applied_twice : ∀ f : Bool → Bool,
    (∀ x : Bool, f x = !x) →
    ∀ b : Bool, f (f b) = b := by
  intro f h b
  rewrite [h, h]
  cases b <;> rfl
-- /SOLUTION

-- GRADE_MANUAL 1: negation_fn_applied_twice
-- []

-- EX3? (andb_eq_orb)
-- Prove the following theorem.

theorem andb_eq_orb : ∀ b c : Bool,
    (b && c) = (b || c) →
  b = c := by
  -- ADMITTED
  intro b c h
  cases b
  case true =>
    -- h : true && c = true || c, i.e., h : c = true
    dsimp [Bool.and, Bool.or] at h
    rw [h]
  case false =>
    -- h : false && c = false || c, i.e., h : false = c
    dsimp [Bool.and, Bool.or] at h
    rw [h]
  -- /ADMITTED
-- GRADE_THEOREM 3: andb_eq_orb
-- []

-- /FULL

-- FULL
-- ######################################################################
-- ## Course Late Policies, Formalized

-- Suppose that a course has a grading policy based on late days,
-- where a student's final letter grade is lowered if they submit too
-- many homework assignments late.

namespace LateDays

-- First, we inroduce a datatype for modeling the "letter" component
-- of a grade.
inductive Letter : Type where
  | A | B | C | D | F

-- Then we define the modifiers -- a `natural` `a` is just a "plain"
-- grade of `a`.
inductive Modifier : Type where
  | plus | natural | minus

-- A full `Grade`, then, is just a `letter` and a `modifier`.
-- JC: Explain what a `structure` is.
structure Grade where
  letter : Letter
  modifier : Modifier

-- We will want to be able to say when one grade is "better" than
-- another.  In other words, we need a way to compare two grades.  As
-- with natural numbers, we could define `bool`-valued functions
-- `grade_eqb`, `grade_ltb`, etc., and that would work fine.
-- However, we can also define a slightly more informative type for
-- comparing two values, as shown below.  This datatype has three
-- constructors that can be used to indicate whether two values are
-- "equal", "less than", or "greater than" one another.
inductive Comparison : Type where
  | eq   -- "equal"
  | lt   -- "less than"
  | gt   -- "greater than"

-- TODO: Explain what this is doing
open Letter Modifier Comparison

-- Using pattern matching, it is not difficult to define the
-- comparison operation for two letters `l1` and `l2` (see below).
-- This definition uses a feature of `match` patterns: we can match
-- against _two_ values simultaneously by separating them and the
-- corresponding patterns with comma `,`.
-- This is simply a convenient abbreviation for nested pattern
-- matching.
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

-- EX1 (letter_comparison)
theorem letterComparison_Eq : ∀ l : Letter,
    letterComparison l l = eq := by
  -- ADMITTED
  intro l; cases l <;> rfl
  -- /ADMITTED
-- GRADE_THEOREM 1: letterComparison_Eq
-- []

def modifierComparison (m1 m2 : Modifier) : Comparison :=
  match m1, m2 with
  | plus, plus => eq
  | plus, _ => gt
  | natural, plus => lt
  | natural, natural => eq
  | natural, _ => gt
  | minus, minus => eq
  | minus, _ => lt

-- EX2 (grade_comparison)
-- JC: Explain structure projections at this point.
def gradeComparison (g1 g2 : Grade) : Comparison
  -- ADMITDEF
  := match letterComparison g1.letter g2.letter with
  | lt => lt
  | eq => modifierComparison g1.modifier g2.modifier
  | gt => gt
  -- /ADMITDEF

-- test_grade_comparison1
example : gradeComparison ⟨A, minus⟩ ⟨B, plus⟩ = gt := by rfl  -- ADMITTED
-- test_grade_comparison2
example : gradeComparison ⟨A, minus⟩ ⟨A, plus⟩ = lt := by rfl  -- ADMITTED
-- test_grade_comparison3
example : gradeComparison ⟨F, plus⟩ ⟨F, plus⟩ = eq := by rfl  -- ADMITTED
-- test_grade_comparison4
example : gradeComparison ⟨B, minus⟩ ⟨C, plus⟩ = gt := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: gradeComparison_test1
-- GRADE_THEOREM 0.5: gradeComparison_test2
-- GRADE_THEOREM 0.5: gradeComparison_test3
-- GRADE_THEOREM 0.5: gradeComparison_test4
-- []

def lowerLetter (l : Letter) : Letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F  -- Can't go lower than F!

-- This theorem is not provable because of the edge case of F!
-- theorem lowerLetter_lowers_bad : ∀ (l : Letter),
--   letterComparison (lowerLetter l) l = lt := by ...

theorem lowerLetter_F_is_F : lowerLetter F = F := by rfl

-- EX2 (lower_letter_lowers)
theorem lowerLetter_lowers : ∀ l : Letter,
    letterComparison F l = lt →
    letterComparison (lowerLetter l) l = lt := by
  -- ADMITTED
  intro l h
  cases l with
  | A => rfl
  | B => rfl
  | C => rfl
  | D => rfl
  | F => exact h
  -- /ADMITTED
-- GRADE_THEOREM 2: lowerLetter_lowers
-- []

-- EX2 (lower_grade)
-- JC: Explain constructor brackets `⟨` `⟩` at this point.
def lowerGrade (g : Grade) : Grade
  -- ADMITDEF
  := match g with
  | ⟨l, plus⟩ => ⟨l, natural⟩
  | ⟨l, natural⟩ => ⟨l, minus⟩
  | ⟨F, minus⟩ => ⟨F, minus⟩
  | ⟨l, minus⟩ => ⟨lowerLetter l, plus⟩
  -- /ADMITDEF

-- lower_grade_A_Plus
example : lowerGrade ⟨A, plus⟩ = ⟨A, natural⟩ := by rfl  -- ADMITTED
-- lower_grade_A_Natural
example : lowerGrade ⟨A, natural⟩ = ⟨A, minus⟩ := by rfl  -- ADMITTED
-- lower_grade_A_Minus
example : lowerGrade ⟨A, minus⟩ = ⟨B, plus⟩ := by rfl  -- ADMITTED
-- lower_grade_B_Plus
example : lowerGrade ⟨B, plus⟩ = ⟨B, natural⟩ := by rfl  -- ADMITTED
-- lower_grade_F_Natural
example : lowerGrade ⟨F, natural⟩ = ⟨F, minus⟩ := by rfl  -- ADMITTED
-- lower_grade_twice
example : lowerGrade (lowerGrade ⟨B, minus⟩) = ⟨C, natural⟩ := by rfl  -- ADMITTED
-- lower_grade_thrice
example : lowerGrade (lowerGrade (lowerGrade ⟨B, minus⟩)) = ⟨C, minus⟩ := by rfl  -- ADMITTED

theorem lowerGrade_F_Minus : lowerGrade ⟨F, minus⟩ = ⟨F, minus⟩ := by rfl  -- ADMITTED

-- GRADE_THEOREM 0.25: lowerGrade_A_Plus
-- ...
-- GRADE_THEOREM 0.25: lowerGrade_F_Minus
-- []

-- EX3 (lower_grade_lowers)
/- JC: Some things to introduce before we get here:
  * Working on multiple match cases with `| _ ... | _ => ...`;
  * Working on all remaining goals with `all_goals`. -/
theorem lowerGrade_lowers : ∀ g : Grade,
    gradeComparison ⟨F, minus⟩ g = lt →
    gradeComparison (lowerGrade g) g = lt := by
  -- ADMITTED
  intro g h
  match g with
  | ⟨l, plus⟩
  | ⟨l, natural⟩ =>
    dsimp [lowerGrade, gradeComparison]
    rewrite [letterComparison_Eq]
    dsimp [modifierComparison]
  | ⟨l, minus⟩ =>
    cases l
    case F => rewrite [lowerGrade_F_Minus]; exact h
    all_goals rfl
  -- /ADMITTED
-- GRADE_THEOREM 3: lowerGrade_lowers
-- []

def applyLatePolicy (lateDays : Nat) (g : Grade) : Grade :=
  if lateDays <? 9 then g
  else if lateDays <? 17 then lowerGrade g
  else if lateDays <? 21 then lowerGrade (lowerGrade g)
  else lowerGrade (lowerGrade (lowerGrade g))

theorem applyLatePolicy_unfold : ∀ (lateDays : Nat) (g : Grade),
    applyLatePolicy lateDays g
    =
    (if lateDays <? 9 then g
     else if lateDays <? 17 then lowerGrade g
     else if lateDays <? 21 then lowerGrade (lowerGrade g)
     else lowerGrade (lowerGrade (lowerGrade g))) := by
  intro _ _; rfl

-- EX2 (no_penalty_for_mostly_on_time)
theorem no_penalty_for_mostly_on_time : ∀ (lateDays : Nat) (g : Grade),
    (lateDays <? 9 = true) →
    applyLatePolicy lateDays g = g := by
  -- ADMITTED
  intro lateDays g h
  dsimp [applyLatePolicy]
  rewrite [h]; rfl
  -- /ADMITTED
-- GRADE_THEOREM 2: no_penalty_for_mostly_on_time
-- []

-- EX2 (grade_lowered_once)
theorem grade_lowered_once : ∀ (lateDays : Nat) (g : Grade),
    (lateDays <? 9 = false) →
    (lateDays <? 17 = true) →
    applyLatePolicy lateDays g = lowerGrade g := by
  -- ADMITTED
  intro lateDays g h9 h17
  dsimp [applyLatePolicy]
  rewrite [h9, h17]; rfl
  -- /ADMITTED
-- GRADE_THEOREM 2: grade_lowered_once
-- []

end LateDays

-- ######################################################################
-- ## Binary Numerals

-- EX3 (binary)
-- We can generalize our unary representation of natural numbers to
-- the more efficient binary representation by treating a binary
-- number as a sequence of constructors `b0` and `b1` (representing 0s
-- and 1s), terminated by a `z`.
--
-- For example:
--     decimal       binary                    unary
--        0              z                        0
--        1           b1 z                        1
--        2       b0 (b1 z)                       2
--        3       b1 (b1 z)                       3
--        4   b0 (b0 (b1 z))                      4
--        5   b1 (b0 (b1 z))                      5
--        6   b0 (b1 (b1 z))                      6
--        7   b1 (b1 (b1 z))                      7
--        8  b0 (b0 (b0 (b1 z)))                  8
--
-- Note that the low-order bit is on the left and the high-order bit
-- is on the right -- the opposite of the way binary numbers are
-- usually written.  This choice makes them easier to manipulate.
--
-- (Comprehension check: What unary numeral does `b0 z` represent?)

inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)

def incr (m : Bin) : Bin
  -- ADMITDEF
  := match m with
  | .z => .b1 .z
  | .b0 m' => .b1 m'
  | .b1 m' => .b0 (incr m')
  -- /ADMITDEF

def binToNat (m : Bin) : Nat
  -- ADMITDEF
  := match m with
  | .z => 0
  | .b0 m' => binToNat m' * 2
  | .b1 m' => binToNat m' * 2 + 1
  -- /ADMITDEF

-- test_bin_incr1
example : incr (.b1 .z) = .b0 (.b1 .z) := by rfl  -- ADMITTED
-- test_bin_incr2
example : incr (.b0 (.b1 .z)) = .b1 (.b1 .z) := by rfl  -- ADMITTED
-- test_bin_incr3
example : incr (.b1 (.b1 .z)) = .b0 (.b0 (.b1 .z)) := by rfl  -- ADMITTED
-- test_bin_incr4
example : binToNat (.b0 (.b1 .z)) = 2 := by rfl  -- ADMITTED
-- test_bin_incr5
example : binToNat (incr (.b1 .z)) = 1 + binToNat (.b1 .z) := by rfl  -- ADMITTED
-- test_bin_incr6
example : binToNat (incr (incr (.b1 .z))) = 2 + binToNat (.b1 .z) := by rfl  -- ADMITTED
-- test_bin_incr7
example : binToNat (.b0 (.b0 (.b0 (.b1 .z)))) = 8 := by rfl  -- ADMITTED

-- GRADE_THEOREM 0.5: incr_test1
-- GRADE_THEOREM 0.5: incr_test2
-- GRADE_THEOREM 0.5: incr_test3
-- GRADE_THEOREM 0.5: binToNat_test1
-- GRADE_THEOREM 0.5: binToNat_test2
-- GRADE_THEOREM 0.5: binToNat_test3
-- []

-- /FULL
