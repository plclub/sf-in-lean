/-

  Basics: Functional Programming in Lean
-/

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
/-
  REMINDER:

           #####################################################
           ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
           #####################################################

    (See the [Preface] for why.)
-/
-- /FULL
-- /HIDEFROMHTML

/-
  ######################################################################
  # Introduction
-/

-- FULL
/-
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
-/
-- /FULL

/-
  ######################################################################
  # Data and Functions
-/

/- ## Enumerated Types -/

-- TERSE: /- In Lean, we can build practically everything from first principles... -/
-- FULL
/-
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
-/

-- /FULL

/-
  ######################################################################
  ## Days of the Week
-/

-- TERSE: /- A datatype definition: -/

-- FULL
/-
  To see how the datatype definition mechanism works, let's
  start with a very simple example.  The following declaration tells
  Lean that we are defining a set of data values -- a _type_.
-/
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
/-
  The new type is called `Day`, and its members are `monday`,
  `tuesday`, etc.

  Having defined `Day`, we can write functions that operate on days.
-/
-- /FULL
-- TERSE: /- *** -/
-- TERSE: /- A function on days: -/

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

/-
  Note that the argument and return types of this function are
  explicitly declared on the first line.  Like most functional
  programming languages, Lean can often figure out these types for
  itself when they are not given explicitly -- i.e., it can do _type
  inference_ -- but we'll generally include them to make reading
  easier.
-/

/-
  The `match` keyword is Lean's keyword for _pattern matching_: the functional
  programming way of examining and making decisions on data. We assume some
  familiarity with basic pattern matching in this book.
-/


/- You may also notice the unique pattern matching syntax- for
  example, in "`.monday`". The `.` - is syntactic sugar for `Day.monday`, and
  exists to save the programmer the time of typing out the full qualified name.
  You may wonder why the language doesn't just expose a pattern like `monday`
  without the dot, like OCaml does. This is to avoid name shadowing, because
  being explicit about names is especially important to avoid confusion and
  headaches when writing proofs. The `.` syntax is a compromise that lets us
  know we're qualifying a name without having to type too much.
-/

-- /FULL

-- TERSE: /- *** -/
-- TERSE: /- Evaluation: -/
-- FULL
/-
  Having defined a function, we can check that it works on
  some examples. There are actually three different ways to do
  examples in Lean. First, we can use the `#eval` command to
  evaluate a compound expression involving `nextWorkingDay`.
-/
-- /FULL


#eval nextWorkingDay Day.friday
/- ==> Day.monday -/

#eval nextWorkingDay (nextWorkingDay Day.saturday)
/- ==> Day.tuesday -/

-- FULL

/-
  ### Aside: Using the Lean Extension
-/

/-
  In VSCode, development of Lean code is supported by the Lean Extension, which
  provides an interactive "InfoView" panel that displays the results of commands
  like `#eval` and `#check`, as well as the current goal state when working on
  proofs. You can hover over expressions in the source code to see their types,
  and you can click on the results in the InfoView to navigate to their
  definitions. This makes it easier to understand how your code is being
  interpreted by Lean and to debug any issues that arise.

  The InfoView always follows your cursor, and Lean typechecks the file as you
  edit it, so you can see the results of your changes immediately. You can also
  use the InfoView to explore the definitions of functions and types that you're
  using, which can be very helpful for understanding how they work.

  If you haven't already, install the Lean Extension in VSCode and open the
  `Basics.lean` file to see the InfoView in action. Try hovering over the
  `nextWorkingDay` function and the `Day` type to see their definitions.
  For `#eval` and other commands, we show Lean's responses in comments; if you
  hover over the `#eval` commands above, you will see the popup that contains
  the output should match what's in the comment below. Experiment with adding
  your own `#eval` commands to test other inputs.

-/


-- /FULL

/-
  Continuing with our simple type and function, we can record what we _expect_
  the result of calling a function to be in the form of a Lean `example`:
-/

/- test_next_working_day -/
example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.tuesday := by
  rfl

-- FULL
/-
  This declaration does two things: it makes an assertion
  (that the second working day after `saturday` is `tuesday`), and it
  gives the assertion a name for later reference.
  Having made the assertion, we can also ask Lean to _verify_ it.
  The `by rfl` can be read as "The assertion we've just made can be
  proved by observing that both sides of the equality evaluate to
  the same thing."
-/

/-
  `rfl` stands for "reflexivity," which is the principle that any value is
  equal to itself. After evaluation, both sides of the equality are the same
  value, so the assertion is true by reflexivity.  If we had made a different
  assertion, such as `example : nextWorkingDay (nextWorkingDay Day.saturday) =
  Day.monday`, then Lean would not be able to verify it, and would signal an
  error. Try it out!
-/

-- /FULL

/- ###################################################################### -/
/- ## Booleans -/

-- FULL
/-
  Following the pattern of the days of the week above, we can
  define the standard type `Bool` of booleans, with members `true`
  and `false`.
-/
-- /FULL
-- TERSE: /- Another familiar enumerated type: -/

/-
  We define our own `MyBool` to teach the concept of building from
  scratch; later we'll switch to Lean's built-in `Bool`.
-/

section MyBool

inductive MyBool : Type where
  | true
  | false
open MyBool

-- FULL
/-
  Functions over booleans can be defined in the same way as above
-/
-- /FULL

def notb (b : MyBool) : MyBool :=
  match b with
  | .true =>  .false
  | .false => .true

def andb (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | .true => b2
  | .false => .false

def orb (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | .true => .true
  | .false => b2

-- FULL
/-
  The last two of these illustrate Lean's syntax for
  multi-argument function definitions. The corresponding
  multi-argument _application_ syntax is illustrated by the
  following "unit tests," which constitute a complete specification
  -- a truth table -- for the `orb` function:
-/
-- /FULL

-- TERSE: Note the syntax for defining multi-argument functions (`andb` and `orb`).

/- test_orb1 -/
example : orb .true  .false = .true  := by rfl
/- test_orb2 -/
example : orb .false .false = .false := by rfl
/- test_orb3 -/
example : orb .false .true  = .true  := by rfl
/- test_orb4 -/
example : orb .true  .true  = .true  := by rfl

/-
  We can define new symbolic notations for existing definitions.
  Because Lean already defines the same notations for the built-in `Bool`,
  we restrict ours locally to a _section_.
-/

section
local prefix:40 (priority := high) "!" => notb
local infixl:35 (priority := high) " && " => andb
local infixl:30 (priority := high) " || " => orb

/- test_orb5 -/
example : (.false || .false || .true) = .true := by rfl

/- test_orb6 -/
example : (! .false) = .true := by rfl
end

-- TERSE: /- *** -/
-- EX1 (nandb)
-- FULL
/-
  The `sorry` keyword can be used as a placeholder for an
  incomplete proof or definition. We use it in exercises to indicate
  the parts that we're leaving for you -- i.e., your job is to replace
  `sorry` with real definitions and proofs.

  Remove `sorry` below and complete the definition of the
  following function; then make sure that the `example` assertions
  below can each be verified by Lean. The function should return
  `true` if either or both of its inputs are `false`.
-/
-- /FULL

def nandb (b1 : MyBool) (b2 : MyBool) : MyBool
  -- ADMITDEF
  := match b1 with
  | .true => notb b2
  | .false => true
  -- /ADMITDEF

/- test_nandb1 -/
example : nandb .true .false  = .true  := by rfl  -- ADMITTED
/- test_nandb2 -/
example : nandb .false .false = .true  := by rfl  -- ADMITTED
/- test_nandb3 -/
example : nandb .false .true  = .true  := by rfl  -- ADMITTED
/- test_nandb4 -/
example : nandb .true .true   = .false := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: nandb_test4
-- []

-- FULL
-- EX1 (andb3)
/-
  Do the same for the `andb3` function below. This function should
  return `true` when all of its inputs are `true`, and `false`
  otherwise.
-/

def andb3 (b1 : MyBool) (b2 : MyBool) (b3 : MyBool) : MyBool
  -- ADMITDEF
  := andb b1 (andb b2 b3)
  -- /ADMITDEF

/- test_andb31 -/
example : andb3 .true .true .true  = .true  := by rfl  -- ADMITTED
/- test_andb32 -/
example : andb3 .false .true .true = .false := by rfl  -- ADMITTED
/- test_andb33 -/
example : andb3 .true .false .true = .false := by rfl  -- ADMITTED
/- test_andb34 -/
example : andb3 .true .true .false = .false := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: andb3_test4
-- []
-- /FULL


-- TERSE: /- *** -/
-- FULL
/-
  Lean's built-in `Bool` type has the same structure as our `MyBool` but also
  includes a lot of useful functions and lemmas. We can even define a function
  to convert between our `MyBool` and Lean's `Bool`.
-/

def myBoolToBool (b : MyBool) : Bool :=
  match b with
  | .true => true
  | .false => false

/-
  Note how we don't have to use the `.`, because we have specified the type
  of `true` by declaring the return type of `myBoolToBool` to be `Bool`.
  Lean's type inference algorithm fills in the gap.
-/

/-
  With the full power of Lean's `Bool` at our disposal, we can also write this
  function more concisely using the `bif ... then ... else` syntax, which is a
  convenient way to write simple conditional expressions.
-/

def boolToMyBool (b : Bool) : MyBool :=
  bif b then true else false
-- /FULL

end MyBool


/- ###################################################################### -/
/- ## Types -/

/-
  Every expression in Lean has a type describing what sort of
  thing it computes. The `#check` command asks Lean to print the type
  of an expression.
-/

#check true
/- ===> true : Bool -/

/-
  If the thing after `#check` is followed by a colon and a type,
  Lean will verify that the type of the expression
  matches the given type and signal an error if not.
-/

#check (true : Bool)
#check (not true : Bool)

/-
  Functions like `not` itself are also data values, just like
  `true` and `false`.  Their types are called _function types_, and
  they are written with arrows.
-/

#check not
/- ===> not : Bool → Bool -/

-- FULL
/-
  The type of `not`, written `Bool → Bool` and pronounced
  "`Bool` arrow `Bool`," can be read, "Given an input of type
  `Bool`, this function produces an output of type `Bool`."
  Similarly, the type of `and`, written `Bool → Bool → Bool`, can
  be read, "Given two inputs, each of type `Bool`, this function
  produces an output of type `Bool`."
-/

/-
  ### Aside: Unicode in Lean
  You may notice that → is a unicode character, not a simple ASCII string. This
  is a common convention in Lean, and the Lean Extension provides convenient
  shortcuts for entering these characters. Simply typing \ (backslash) followed
  by the name of the character, and the extension will automatically replace it
  with the correct symbol. For example, typing \-> or \to will produce →, and
  \lambda will produce λ. This allows you to write more concise and readable
  code without having to remember complex keyboard shortcuts.
-/

-- /FULL


/-
  ######################################################################
  ## New Types from Old
-/

-- FULL
/-
  The types we have defined so far are examples of simple
  "enumerated types": their definitions explicitly enumerate a
  finite set of elements, called _constructors_.  Here is a more
  interesting type definition, `Color`, where one of the
  constructors takes an argument:
-/
-- /FULL
-- TERSE: /- A more interesting type definition: -/

inductive RGB : Type where
  | red
  | green
  | blue

inductive Color : Type where
  | black
  | white
  | primary (p : RGB)

/-
  An `inductive` definition does two things:

  - It introduces a set of new _constructors_. E.g., `RGB.red`,
    `Color.primary`, `true`, `false`, `Day.monday`, etc. are constructors.

  - It groups them into a new named type, like `Bool`, `RGB`, or
    `Color`.

  _Constructor expressions_ are formed by applying a constructor
  to zero or more other constructors or constructor expressions,
  obeying the declared number and types of the constructor arguments.
  E.g., these are valid constructor expressions...
      - `RGB.red`
      - `MyBool.true`
      - `true` -- Lean's builtin Boolean type- no `.` needed
      - `Color.primary RGB.red`
      - etc.
  ...but these are not:
      - `RGB.red Color.primary`
      - `true RGB.red`
      - `Color.primary (Color.primary RGB.red)`
      - etc.
-/

-- TERSE: /- *** -/

/-
  We can define functions on colors using pattern matching just as
  we did for `Day` and `Bool`.
-/

def monochrome (c : Color) : Bool :=
  match c with
  | .black => true
  | .white => true
  | .primary _ => false

/-
  Since the `primary` constructor takes an argument, a pattern
  matching `primary` should include either a variable, a constant
  of appropriate type, or `_`. The last, as used in the above
  example, means that the constructor argument is being ignored.
  Examples below illustrate the other two cases.
-/

def isRed (c : Color) : Bool :=
  match c with
  | .black => false
  | .white => false
  | .primary .red => true
  | .primary _ => false

/-
  The pattern `.primary red` will match only when `c` is `Color.primary`
  with the argument `RGB.red`. Patterns are checked in order, so
  the subsequent pattern `.primary _` here means "the constructor
  `primary` applied to any `RGB` constructor except `red`."
-/

def isRed' (c : Color) : Bool :=
  match c with
  | .black => false
  | .white => false
  | .primary r =>
    match r with
    | .red => true
    | _ => false

/-
  The `isRed'` function produces the same result as `isRed` but illustrates
  the use of a pattern matching variable: the `.primary r` pattern
  stores the `RGB` argument into variable `r`, and then pattern matches on
  that argument to produce the final result.
-/

/-
  ######################################################################
  ## Namespaces and Sections
-/

-- FULL
/-
  Lean provides a _namespace system_ to aid in organizing large
  developments. If we enclose a collection of declarations in
  `namespace X ... end X`, then, in the remainder of the file
  after the `end`, these definitions are referred to by names like
  `X.foo` instead of just `foo`. We will use this feature to limit
  the scope of definitions, so that we are free to reuse names.
-/
-- /FULL
-- TERSE: /- `namespace` declarations create separate namespaces. -/

namespace Playground
def myFoo : RGB := RGB.blue
end Playground

def myFoo : Bool := true

#check Playground.myFoo  -- RGB
#check myFoo             -- Bool

-- FULL
/-
  Inside of a namespace, all previous definitions from that namespace are
  available, and can be referenced without prefixes.
  Definitions can also be prefixed by a namespace to put them in the namespace
  without having to open and close the namespace.
-/
-- /FULL

namespace RGB
def myBlue : RGB := blue
end RGB

def RGB.myOtherBlue : RGB := myBlue

/-
  #check myBlue -- unknown identifier
-/
#check RGB.myBlue      -- RGB
#check RGB.myOtherBlue -- RGB

-- FULL
/-
  We can also use `open` to bring the definitions of a namespace into scope.
  This means that we can refer to all of the namespace's definitions without
  a prefix. Definitions of the same name declared prior to the `open`
  can be referred to by the special prefix `_root_`.
  Lean also provides _sections_, which delimit the scope of `open`ing
  namespaces and `local` notations within `section ... end`.
  We already saw `prefix` and `infix` notations for MyBool;
  there are also `postfix` notations.
-/
-- /FULL
-- TERSE: /- `section` declarations delimit the scope of `open` and `local`. -/

section
open Playground
local postfix:40 "′" => Color.primary

#check myFoo        -- RGB
#check _root_.myFoo -- Bool
#check RGB.blue′    -- Color
end

#check myFoo         -- Bool
/-
  #check RGB.blue′  -- fails to parse
-/

/-
  ######################################################################
  ## Tuples
-/

namespace TuplePlayground

-- FULL
/-
  A single constructor with multiple parameters can be used
  to create a tuple type. As an example, consider representing
  the four bits in a nybble (half a byte). We first define
  a datatype `Bit` that resembles `Bool` (using the
  constructors `b1` and `b0` for the two possible bit values)
  and then define the datatype `Nybble`, which is essentially
  a tuple of four bits.
-/

-- RAB: Is this called a Nybble, not a Nibble? Whatever the Penn systems course
-- calls it, we should follow suite, I guess.

-- /FULL

-- TERSE: /- A nybble is half a byte -- four bits. -/

inductive Bit : Type where
  | b1
  | b0

inductive Nybble : Type where
  | bits (x0 x1 x2 x3 : Bit)

#check (.bits .b1 .b0 .b1 .b0 : Nybble)

-- FULL
/-
  Note: The `bits` constructor illustrates a feature of multi-argument
  declarations, both for constructors and for functions: Instead
  of writing `(x0 : Bit) (x1 : Bit) ...` we write `(x0 x1 ... : Bit)`
  since all of the variables have the same type. We could have done
  the same with the function definition `orb` above, writing
  `orb (b1 b2 : MyBool)` rather than `orb (b1 : MyBool) (b2 : MyBool)`
-/

/-
  The `bits` constructor acts as a wrapper for its contents.
  Unwrapping can be done by pattern-matching, as in the `allZero`
  function below, which tests a nybble to see if all its bits are
  `b0`.
-/
-- /FULL

-- TERSE: /- *** -/
-- TERSE: /- We can deconstruct a nybble by pattern-matching. -/

def allZero (nb : Nybble) : Bool :=
  match nb with
  | .bits .b0 .b0 .b0 .b0 => true
  | .bits _   _   _   _   => false

#eval allZero (.bits .b1 .b0 .b1 .b0)
/- ===> false -/
#eval allZero (.bits .b0 .b0 .b0 .b0)
/- ===> true -/

end TuplePlayground

/-
  ######################################################################
  ## Numbers
-/

-- FULL
/-
  We put this section in a namespace so that our own definition of
  numbers does not interfere with the one from the standard library.
  In the rest of the book, we'll use the standard library's.
-/
-- /FULL

namespace NatPlayground

-- FULL
/-
  All the types we have defined so far -- both "enumerated
  types" such as `Day`, `Bool`, and `Bit` and tuple types such as
  `Nybble` built from them -- are finite. The natural numbers, on
  the other hand, are an infinite set, so we'll need to use a
  slightly richer form of type declaration to represent them.
-/

/-
  There are many representations of numbers to choose from. You are
  certainly familiar with decimal notation (base 10), using the
  digits 0 through 9, for example, to form the number 123. You may
  also have encountered hexadecimal notation (base 16),
  in which the same number is represented as 7B, or octal (base 8),
  where it is 173, or binary (base 2), where it is 1111011. Using an
  enumerated type to represent digits, we could use any of these as
  our representation natural numbers.
-/

/-
  There are circumstances where each of these choices would
  be useful. The binary representation is valuable in computer hardware
  because the digits can be represented with just two distinct voltage
  levels, resulting in simple circuitry. Here we choose a _unary_
  (base 1) representation that is even simpler than binary, makes proofs
  simpler. In this representation, only a single digit
  is used. As a Lean datatype, we use two constructors. The
  [zero] constructor represents zero. The [succ] constructor can be
  applied to the representation of the natural number [n], yielding
  the representation of [n+1], where [succ] stands for "successor."
  Here is the complete datatype definition:
-/

-- /FULL

-- TERSE: /- For simplicity in proofs, we choose unary representation. -/

inductive Nat : Type where
  | zero
  | succ (n : Nat)

-- ASSUME THIS IS HIDDEN
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
-- END ASSUME

/-
  With this definition, 0 is represented by `zero`, 1 by `succ zero`, 2 by `succ
  (succ zero)`, and so on.

  We use some machinery in the background to allow us to write `0`, `1`, `2`,
  etc. instead of `zero`, `succ zero`, etc., for our custom definition of `Nat`.
  This is just syntactic sugar, and the two forms are interchangeable.
-/

-- RULES
theorem one_eq_succ_zero : 1 = succ 0 := rfl
-- RULES
theorem two_eq_succ_one : 2 = succ 1 := rfl
-- RULES
theorem three_eq_succ_two : 3 = succ 2 := rfl
-- RULES
theorem four_eq_succ_three : 4 = succ 3 := rfl

example : succ (succ (succ (succ zero))) = 4 := by rfl

/-
  Naturally, Lean has its own definition of natural numbers.
-/

  #check Nat
  /- ==> NatPlayground.Nat : Type -/ /- ← this is our `Nat`... -/
  #check _root_.Nat
  /- ==> _root_.Nat : Type -/ /- ← ...this is Lean's `Nat`. -/

/-
  Lean's [Nat] comes with powerful built-in reasoning and notation.
  As we are just beginning to reason about natural numbers, we use our own
  simple definition, and introduce the Lean one shortly after.
-/


/-
  We can also write computations functions on `Nat`.
-/

def pred (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ n' => n'

def minustwo (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ (zero) => zero
  | succ (succ n') => n'

#eval minustwo 4
/- ===> succ (succ zero) -/

-- TODO:
-- Lean user question: how to get (succ (succ zero)) rather than
-- NatPlayground.Nat.succ (NatPlayground.Nat.succ (NatPlayground.Nat.zero))

-- FULL
#check Nat.succ  -- Nat → Nat
#check Nat.pred  -- Nat → Nat
#check minustwo  -- Nat → Nat

/-
  These are all things that can be applied to a number to yield a
  number. However, there is a fundamental difference between `Nat.succ`
  and the other two: functions like `Nat.pred` and `Nat.minustwo` are
  defined by giving _computation rules_ -- e.g., the definition of
  `Nat.pred` says that `Nat.pred (succ (succ zero))` can be simplified to
  `succ zero` -- while the definition of `Nat.succ` has no such behavior attached.
  Although it is _like_ a function in the sense that it can be applied to an
  argument, it does not _do_ anything at all!  It is just a way of
  writing down numbers.
-/
-- /FULL

-- TERSE: /- *** -/
-- TERSE: /- Recursive functions: -/

def even (n : Nat) : Bool :=
  match n with
  | zero => true
  | succ (zero) => false
  | succ (succ n') => even n'

-- TERSE: /- *** -/
/-
  We could define `odd` by a similar recursive declaration, but
  here is a simpler way:
-/

def odd (n : Nat) : Bool :=
  not (even n)

/- test_odd1 -/
example : odd 1 = true  := by rfl
/- test_odd2 -/
example : odd 4 = false := by rfl

-- TERSE: /- *** -/
-- TERSE: /- A multi-argument recursive function. -/


@[irreducible]
def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m')

instance instAdd : Add Nat where add := add

-- FULL

/-
  ######################################################################
  # Proof by Rewriting

  ### Proving properties about functions in Lean

  Being recursive, `add` is our first of a more sophisticated class of
  functions. In this chapter and onwards, we will _prove_ properties about
  recursive functions and inductive data, like `add` and `Nat`, using
  _simplification rules_ about their behavior.

  Here is a simple rule about `add`, called `add_zero`:

  `add_zero (n : Nat) : n + 0 = n`

  We can see it is a real rule in lean:
-/
-- ASSUME THIS IS HIDDEN
unseal add in
theorem add_zero : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl
unseal add in
theorem add_succ : ∀ n m : Nat, n + succ m = succ (n + m) := by
  intro n m
  rfl
-- END ASSUME

#check add_zero
/- ==> NatPlayground.Nat.add_zero (n : Nat) : n + 0 = n -/

/- And we can use it for a simple proof about natural numbers! -/

theorem add_zero_zero (n : Nat) : n + 0 + 0 = n := by
  rewrite [add_zero]
  rewrite [add_zero]
  rfl

/-
  # Proof state and tactics
  There are several parts to a proof in Lean.
   Each "command" of the proof- `rewrite`, `rfl` is called a **tactic**.
   (The `add_zero` in brackets is an _argument_ to a tactic.)


    Hovering with the cursor over each line of the proof,
    we see the **proof state** in the Lean InfoView panel.

    The **proof state** is divided into the **context**, before the ⊢,
    and the **goal**, after the ⊢. The **context** is what we know, and
    the **goal** is what we are trying to prove.

    A **tactic** manipulates the **proof state** (or **context**) to
    get the goal into a closer shape to the one we want. Once we have
    a proof state that a tactic can _close_ (solve), we invoke that
    tactic, which finishes the proof.

    Let's walk through the example above with our terminology.
-/

  theorem add_zero_zero_explained (n : Nat) : n + 0 + 0 = n := by
  /- Move your cursor (click) here to see the initial proof state in the InfoView.
    Our context is `n : Nat`.
    Our goal is `n + 0 + 0 = n`. -/
    rewrite [add_zero]
    /- Now click here to see the new proof state, after the tactic.
      This tactic above is the `rewrite` tactic, with an argument `add_zero`.
      Notice how it changed the goal by changing `n + 0` to `n`. -/
    rewrite [add_zero]
     /-  Again, we change the goal state by changing `n + 0` to `n`.
      Now the proof state is an equality with both sides equal,
      so it can be closed by the tactic `rfl`. -/
    rfl
    /- The proof is now done! The Lean InfoView tells us there are "No Goals". -/

  /- We'll give you a simple proof to try.
    Try completing this proof of `add_zero_zero_zero`, following the model above.
   -/

theorem add_zero_zero_zero (n : Nat) : n + 0 + 0 + 0 = n := by
  -- ADMITTED
  rewrite [add_zero]
  rewrite [add_zero]
  rewrite [add_zero]
  rfl
  -- /ADMITTED

/-

 ## The `rewrite` tactic

   As we saw above, the tactic that tells Lean to rewrite (part of) a goal or
   hypothesis based on a rule is called `rewrite`. Given our rule `add_zero`,
   which states that `n + 0` is equal to `n` for any `n`, we can replace any `n
   + 0` in our proof with `n` via `rewrite [add_zero]`.

  `rewrite` always takes its argument(s) in square brackets: `[]`.

  ## The `rfl` tactic

  `rfl` closes a goal of the shape `a = a`, for any `a`.
  `rfl` checks that both sides of the equality are _definitionally equal_- that
  is, they reduce to the same thing.
  A term is always _definitionally equal_ to itself.
-/

  /- ## A New `add` Rule

    We introduce the other fundamental rule about `add`:

    `add_succ (n m : Nat) : n + (succ m) = succ (n + m)`.

    This is the rule we use to push `succ` around.
  -/


 /- Again, we see that it is a usable rule in Lean: -/

  #check add_succ
  /- ==> add_succ (n m : Nat) : n + succ m = succ (n + m) -/

  /- And we can write a proof with it: -/

  theorem add_succ_zero (n : Nat) : n + succ 0 = succ (n + 0 + 0) := by
    rewrite [add_succ]
    rewrite [add_zero]  /- notice how this handles an `n + 0` on both sides -/
    rewrite [add_zero]
    rfl

  /- Make sure you're "stepping through" the proofs- that is, moving past each
     tactic with your cursor to see how each tactic is manipulating the proof
     state. You will write more and more of the proofs by yourself as we go
     along, so learning how the tactics work now is worthwhile!
  -/

  /- ## Working with Numerals

    We know from above that `1` is just `succ 0`, `2` is `succ 1`, and so on.
    We have rules for these equalities, as well:
  -/

  #check one_eq_succ_zero /- ==> one_eq_succ_zero : 1 = succ 0 -/
  #check two_eq_succ_one /- ==> two_eq_succ_one : 2 = succ 1 -/
  #check three_eq_succ_two /- ==> three_eq_succ_two : 3 = succ 2 -/

  /- We can rewrite with these rules to expand numerals into their definitions,
     which allows us to use our `add` rules. -/

-- /FULL

/- We give an example of how to start a proof this way.
  Finish the proof using the `add` rules.
 -/
theorem one_plus_one_eq_two : (1 + 1 : Nat) = 2 := by
  rewrite [one_eq_succ_zero]
  -- ADMITTED
  rewrite [add_succ]
  rewrite [add_zero]
  rfl
  -- /ADMITTED

-- /FULL

  /- Try the same for `2 + 2 = 4`. -/

theorem two_plus_two_eq_four : (2 + 2 : Nat) = 4 := by
  -- ADMITTED
  rewrite [four_eq_succ_three, three_eq_succ_two,
           two_eq_succ_one, one_eq_succ_zero]
  rewrite [add_succ, add_succ, add_zero]
  rfl
  -- /ADMITTED

-- FULL
/-
  By default, `rewrite` rewrites left-to-right. To rewrite from right
  to left, use `rewrite [← h]`, where `←` is typed as `\l` or `\<-`.
-/
-- /FULL

-- FULL
/-
  Now that we know how addition is defined, we can use
  it to define multiplication:
-/
-- /FULL

-- TERSE: /- *** -/
@[irreducible]
def mul (n m : Nat) : Nat :=
  match m with
  | zero => zero
  | succ m' => add (mul n m') n

instance instMul : Mul Nat where mul := mul

/- Multiplication, like almost any function we will prove properties about,
   also has simplification rules. -/

-- ASSUME THIS IS HIDDEN
unseal mul in
theorem mul_zero : ∀ n : Nat, n * 0 = 0 := by
  intro n
  rfl

unseal mul add in
theorem mul_succ : ∀ n m : Nat, n * succ m = n * m + n := by
  intro n m
  rfl
-- END ASSUME

/- Prove this property. We have given you the first line. Notice how `rewrite`
   can take any number of arguments. You can use this rewrite with all of the
   numeral rules at once, for example.

   After each rewrite, check the proof state by placing the cursor immediately
   after a rule to see how the goal is changing. This happens naturally
   as you write the proof, which makes it convenient to use `rewrite` blocks
   with multiple rules.
 -/
/- test_mult1 -/
theorem test_mult1 : (3 * 3 : Nat) = 9 := by
  rewrite [three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
  -- ADMITTED
  rewrite [mul_succ, mul_succ, mul_succ, mul_zero]
  rewrite [add_succ, add_succ, add_succ, add_zero]
  rewrite [add_succ, add_succ, add_succ, add_zero]
  rewrite [add_succ, add_succ, add_succ, add_zero]
  rfl

-- /ADMITTED

-- TERSE: /- *** -/


/-
  We can pattern-match two values at the same time:
-/

-- TERSE: /- *** -/
/-
  When we say that Lean comes with almost nothing built-in, we really
  mean it: even testing equality is a user-defined operation!

  Here is a function `beq` that tests natural numbers for
  equality, yielding a boolean.
-/

def beq (n m : Nat) : Bool :=
  match n with
  | zero => match m with
            | zero => true
            | succ _ => false
  | succ n' => match m with
               | zero => false
               | succ m' => beq n' m'

-- TERSE: /- *** -/

-- We need to make a decision about `==`.
-- Either we give decidable equality early, or we use this `==` thing.

/-
  Similarly, the `leb` function tests whether its first argument is
  less than or equal to its second argument, yielding a boolean.
-/

def leb (n m : Nat) : Bool :=
  match n with
  | zero => true
  | succ n' =>
      match m with
      | zero => false
      | succ m' => leb n' m'
/- test_leb1 -/
example : leb 2 2 = true  := by rfl
/- test_leb2 -/
example : leb 2 4 = true  := by rfl
/- test_leb3 -/
example : leb 4 2 = false := by rfl

-- TERSE: /- *** -/
/-
  We'll be using these (especially `beq`) a lot, so let's give
  them infix notations.
-/

-- JC: Lean's stdlib has `==` notation for `beq`,
-- but not for `Nat.ble`...

instance : BEq Nat where
  beq := beq

infix:65 "<=?" => leb

/-
  test_leb3'
-/
example : 4 <=? 2 = false := by rfl

-- FULL
/-
  We now have two symbols that both look like equality: `=`
  and `=?`.  We'll have much more to say about their differences and
  similarities later. For now, the main thing to notice is that
  `x = y` is a logical _claim_ -- a "proposition" -- that we can try to
  prove, while `x =? y` is a boolean _expression_ whose value (either
  `true` or `false`) we can compute.
-/
-- /FULL

-- FULL
-- EX1 (ltb)
/-
  Define a less-than function in terms of `leb`.
-/

def ltb (n m : Nat) : Bool
  -- ADMITDEF
  := leb (succ n) m
  -- /ADMITDEF

infix:65 "<?" => ltb

/- test_ltb1 -/
example : 2 <? 2 = false := by rfl  -- ADMITTED
/- test_ltb2 -/
example : 2 <? 4 = true  := by rfl  -- ADMITTED
/- test_ltb3 -/
example : 4 <? 2 = false := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: ltb_test3
-- []
-- /FULL

/- We can use our new functions to show an important property of
   natural numbers: -/

/- We can use our new functions to show an important property of
   natural numbers: -/

theorem beq_succ : ∀ n m : Nat, (succ n == succ m) = (n == m) := by
  intro n m; rfl


/-
  ######################################################################
  # General Proofs about Natural Numbers
  # General Proofs about Natural Numbers
-/

-- TERSE: /- A (slightly) more interesting theorem: -/

theorem add_id_example : ∀ n m : Nat,
    n = m →
    n + n = m + m := by
  -- FULL
  /-

    We now begin to make claims about _general_ natural numbers.

    We begin by making a universal claim about all numbers `n` and `m` that are
    equal to each other (`n = m`). The arrow symbol is pronounced "implies."
    Type it with "\to" or "\->" or "\r".

     The `intro` tactic moves the universally quantified variables and the
     hypothesis into the context, giving them names.  The goal is now to prove
     `n + n = m + m` under the assumption `h : n = m`.

    We now begin to make claims about _general_ natural numbers.

    We begin by making a universal claim about all numbers `n` and `m` that are
    equal to each other (`n = m`). The arrow symbol is pronounced "implies."
    Type it with "\to" or "\->" or "\r".

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
    The tactic that tells Lean to perform replacement is one we have seen
    before: `rewrite`. It can take a hypothesis from the context as an argument,
    just like it can take a previously proved theorem.  In this case, we want to
    rewrite with the hypothesis `h`, which says that `n` and `m` are equal, so
    that we can replace `n` with `m` in the goal.

     After the rewrite, the goal is `m + m = m + m`, which can be closed by
     `rfl`.
  -/
  -- /FULL
  intro n m
  intro h
  rewrite [h]
  rfl

-- TERSE:
      /- We make a general claim about natural numbers, and prove
        it by rewriting with the hypothesis. -/
-- TERSE:
      /- We make a general claim about natural numbers, and prove
        it by rewriting with the hypothesis. -/

-- FULL
-- EX1 (add_id_exercise)
-- EX1 (add_id_exercise)
/-
  Remove `sorry` and fill in the proof.
-/

theorem add_id_exercise : ∀ n m o : Nat,
    n = m → m = o → n + m = m + o := by
  -- ADMITTED
  intro n m o h1 h2
  rewrite [h1, h2]
  rfl
  -- /ADMITTED
-- GRADE_THEOREM 1: add_id_exercise
-- GRADE_THEOREM 1: add_id_exercise
-- []
-- /FULL

-- FULL
/-
  The `sorry` keyword tells Lean that we want to skip trying
  to prove this theorem and just accept it as a given.  This is
  often useful for developing longer proofs.

  Be careful, though: every time you say `sorry` you are leaving
  a door open for total nonsense to enter Lean's safe, formally
  checked world!
-/
-- /FULL

-- TERSE: /- *** -/

/-
  The `#check` command can also be used to examine the statements of
  previously declared lemmas and theorems.
-/

/- TODO: how to get these to show `∀ (n : Nat)` instead of `mul_zero (n : Nat)` -/
/- TODO: how to get these to show `∀ (n : Nat)` instead of `mul_zero (n : Nat)` -/
#check mul_zero  -- ∀ (n : Nat), n * 0 = 0
#check mul_succ  -- ∀ (n m : Nat), n * Nat.succ m = n + n * m

-- TERSE: /- *** -/
/-
  We can use the `rewrite` tactic with a previously proved theorem
  instead of a hypothesis from the context.
-/

theorem add_mul_zero : ∀ p q : Nat,
    (p * 0) + (q * 0) = 0 := by
  intro p q
  rewrite [mul_zero, mul_zero, add_zero]
  rfl

/-
  ######################################################################
  # Proof by Case Analysis
-/

-- FULL
/-
  Of course, not everything can be proved by simple
  calculation and rewriting: In general, unknown, hypothetical
  values (arbitrary numbers, booleans, lists, etc.) can block
  simplification.
-/
-- /FULL

-- TERSE: /- Sometimes simple calculation and rewriting are not enough... -/
example : ∀ n : Nat,
    (succ n == 0) = false := by
  intro n
  /-
    `rfl` doesn't work here because `n` is unknown
  -/
  sorry

-- FULL
/-
  The tactic that tells Lean to consider separate cases is called
  `cases`.
-/
-- /FULL

-- TERSE: /- We can use `cases` to perform case analysis: -/

theorem add_one_neb_zero : ∀ n : Nat,
    (succ n == 0) = false := by
  intro n
  cases n
  case zero => rfl
  case succ n' => rfl

  -- FULL
/-
  The `cases` tactic generates _two_ subgoals, which we must then
  prove, separately, in order to get Lean to accept the theorem.

  The generated subgoals are tagged by the names of the constructors.
  `case zero =>` and `case succ n' =>` select which subgoal to work on next
  and introduce variable names.

  The `cases` tactic can be used with any inductively defined
  datatype.  For example, we use it next to prove that boolean
  negation is involutive -- i.e., that negation is its own inverse.
-/
-- /FULL

-- TERSE: /- *** -/
-- TERSE: /- Another example, using booleans: -/

theorem notb_involutive : ∀ b : Bool,
    (!!b) = b := by
  intro b
  cases b
  case true => rfl
  case false => rfl

-- TERSE: /- *** -/
-- TERSE: /- We can have nested case analysis: -/

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

/- As you can see, proofs by cases can become very verbose.
  We will introduce some tactics for writing shorter proofs
  by case analysis in `Tactics.lean`. -/

/-
  ** New Tactics: `rewrite ... at` and `exact`.

  Some new tactics will be useful for the exercises ahead.

  The `rewrite` tactic can be used to rewrite in a hypothesis instead of the
  goal. For example, if `h : P` is in the context and we have a rule `P = Q`,
  then `rewrite [P = Q] at h` changes the hypothesis to `h : Q`.

  The `exact` tactic closes a goal by providing an exact proof term.  For
  example, if `h : P` is in the context and the goal is `P`, then `exact h`
  closes the goal.  You can also transform `h` slightly — for instance, `exact
  h.symm` uses the symmetry of equality.
-/


-- EX2 (orb_false_true)
/-
  Prove the following claim.
  /- Tip: the rewrite rule to simplifiy (b || false)
     is `Bool.or_false` -/
-/

theorem orb_false_true : ∀ b : Bool,
    (b || false) = true → b = true := by
  -- ADMITTED
  intro b h
  rewrite [Bool.or_false] at h
  exact h
  -- /ADMITTED
-- GRADE_THEOREM 2: orb_false_true
-- []
-- /FULL

-- FULL
-- EX1 (zero_nbeq_add_1)
theorem zero_neb_add_one : ∀ n : Nat,
  (0 == Nat.succ n) = false := by
  -- ADMITTED
  intro n; cases n
  case zero => rfl
  case succ n' => rfl
  -- /ADMITTED
-- GRADE_THEOREM 1: zero_nbeq_add_1
-- []
-- /FULL


-- FULL
/-
  ######################################################################
  ## More on Notation (Optional)
-/

/-
  Lean has a very flexible notation system.  Operators like `+` and `*`
  are defined with specified precedence and associativity.  For example,
  `+` has precedence 65 and is left-associative, while `*` has
  precedence 70 and is also left-associative.  This means that `1+2*3*4`
  is parsed as `1+((2*3)*4)`.

  You can define custom notation using the `notation`, `infixl`,
  `infixr`, `prefix`, and `postfix` commands.

  Lean handles notation scoping through namespaces and
 _type classes_ rather than notation scopes.  The numeric literal `3`
 _type classes_ rather than notation scopes.  The numeric literal `3`
  can be interpreted as `Nat`, `Int`, `Float`, etc., depending on the
  expected type, thanks to Lean's `OfNat` type class. We explain type classes
  in full in a later chapter.
  /- TODO: which chapter? -/
  expected type, thanks to Lean's `OfNat` type class. We explain type classes
  in full in a later chapter.
  /- TODO: which chapter? -/
-/
-- /FULL

-- FULL
/-
  ######################################################################
  ## Structural Recursion (Optional)
-/

/-
  Here is a copy of the definition of addition:
-/

def add' (n : Nat) (m : Nat) : Nat :=
  match n with
  | zero => m
  | succ n' => succ (add' n' m)

/-
  When Lean checks this definition, it verifies that the recursion
  terminates.  Specifically, it checks that one of the arguments
  is _structurally decreasing_.  This implies that all calls to
  `add'` will eventually terminate.
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
-/

-- EX2? (decreasing)
/-
  To get a concrete sense of this, find a way to write a sensible
  recursive definition (of a simple function on numbers, say) that
  _does_ terminate on all inputs, but that Lean will reject because
  it cannot automatically prove termination.
-/

--  SOLUTION
/-
  def factorial_bad (n : Nat) : Nat :=
    if n == 0 then 1
    else n * factorial_bad (n - 1)
  This fails because Lean can't see that `n - 1` is structurally smaller.

-/
-- /SOLUTION
-- []
-- /FULL

end Nat

/-
  ######################################################################
  ## Binary Numerals
-/

-- EX3 (binary)
/-
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
-/

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

/- test_bin_incr1 -/
example : incr (.b1 .z) = .b0 (.b1 .z) := by rfl  -- ADMITTED
/- test_bin_incr2 -/
example : incr (.b0 (.b1 .z)) = .b1 (.b1 .z) := by rfl  -- ADMITTED
/- test_bin_incr3 -/
example : incr (.b1 (.b1 .z)) = .b0 (.b0 (.b1 .z)) := by rfl  -- ADMITTED
/- test_bin_incr4 -/
unseal Nat.mul Nat.add in
example : binToNat (.b0 (.b1 .z)) = 2 := by rfl  -- ADMITTED
/- test_bin_incr5 -/
unseal Nat.mul Nat.add in
example : binToNat (incr (.b1 .z)) = 1 + binToNat (.b1 .z) := by rfl  -- ADMITTED
/- test_bin_incr6 -/
unseal Nat.mul Nat.add in
example : binToNat (incr (incr (.b1 .z))) = 2 + binToNat (.b1 .z) := by rfl  -- ADMITTED
/- test_bin_incr7 -/
unseal Nat.mul Nat.add in
example : binToNat (.b0 (.b0 (.b0 (.b1 .z)))) = 8 := by rfl  -- ADMITTED

-- GRADE_THEOREM 0.5: incr_test1
-- GRADE_THEOREM 0.5: incr_test2
-- GRADE_THEOREM 0.5: incr_test3
-- GRADE_THEOREM 0.5: binToNat_test1
-- GRADE_THEOREM 0.5: binToNat_test2
-- GRADE_THEOREM 0.5: binToNat_test3
-- []

/- TODO: Give more intro to these two theorems on booleans. -/

-- FULL

end NatPlayground


-- FULL
/-
  ######################################################################
  # More Exercises
-/

/- ## Warmups -/

-- EX1 (identity_fn_applied_twice)
/-
  Use the tactics you have learned so far to prove the following
  theorem about boolean functions.
-/

theorem identity_fn_applied_twice : ∀ f : Bool → Bool,
    (∀ x : Bool, f x = x) →
    ∀ b : Bool, f (f b) = b := by
  -- ADMITTED
  intro f h b
  rewrite [h, h]
  rfl
  -- /ADMITTED
-- GRADE_THEOREM 1: identity_fn_applied_twice
-- []

-- EX1 (negation_fn_applied_twice)
/-
  Now state and prove a theorem `negation_fn_applied_twice` similar
  to the previous one but where the hypothesis says that the
  function `f` has the property that `f x = !x`.
-/

-- SOLUTION
theorem negation_fn_applied_twice : ∀ f : Bool → Bool,
    (∀ x : Bool, f x = !x) →
    ∀ b : Bool, f (f b) = b := by
  intro f h b
  rewrite [h, h]
  cases b <;> rfl
--  /SOLUTION

--  GRADE_MANUAL 1: negation_fn_applied_twice
-- []

-- EX3? (andb_eq_orb)
/-
  Prove the following theorem.
-/

theorem andb_eq_orb : ∀ b c : Bool,
    (b && c) = (b || c) →
  b = c := by
  -- ADMITTED
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
  -- /ADMITTED
-- GRADE_THEOREM 3: andb_eq_orb
-- []

-- /FULL
