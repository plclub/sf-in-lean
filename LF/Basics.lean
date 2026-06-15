/-
  Basics: Functional Programming in Lean
-/

-- INSTRUCTORS: This file and Induction.lean each take about an hour to
--    get through in a not-too-rushed fashion (with questions, etc.).
--    (BCP: Actually, in 2025 this file alone took me two full hours.)
--    (BCP: This estimate may need to be revised now that we are in Lean!)
--
--    You may want to assign both files together as the homework for the
--    first week, depending on the level of the class.  Just Basics is
--    fairly light for many students, but in a mixed class there will
--    be people that struggle with some of it.
--
--    PRESENTATION ADVICE: Working with the .lean file directly in VS Code
--    is recommended for the first few lectures, so students see exactly
--    what's in the source file.


-- FULL
/-
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

  Having defined `Day`, we can write Lean functions that operate on
  days.
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
-- TODO (Claude): "We assume some familiarity with basic pattern matching"
-- contradicts the chapter's premise that readers may be new to functional
-- programming (see also MWH's comment below).  The Rocq original walks
-- through `match` as a new concept; consider restoring a gentle explanation
-- and dropping the OCaml/Haskell references, which assume exactly the
-- background the chapter says it doesn't.


/-
  The `.` in `.monday` is an abbreviation for `Day.`, to avoid typing
  out the full qualified name `Day.monday`. You may wonder why Lean
  doesn't allow patterns like `monday` without the dot, as other
  functional languages like OCaml and Haskell do. This is to avoid
  name shadowing, because being explicit about names is _especially_
  important to avoid confusion and headaches when writing proofs. The
  `.` syntax is a compromise that lets us know we're qualifying a name
  without having to type too much.
-/
-- BCP: That last paragraph doesn't really explain it!  Why do we need
-- to / is it better / helpful to know when we are qualifying names?
-- Also, wouldn't it be pedagogically better to write it out first
-- without the abbreviation and then introduce the shorter form?

-- /FULL

-- TERSE: /- *** -/
-- TERSE: /- Evaluation: -/
-- FULL
/- MWH: The text that follows seems to assume the reader knows what pattern matching
  is, calling attention only to the syntax. It also seems to assume the reader
  knows what OCaml is. But the premise of this section seems to be that readers
  do not know what functional programming is -- we are explaining it to them.
  Seems like a gap. Was it in the original?
-/
/-
  Having defined a function, we should check that it works on some
  examples.  There are actually three different ways to do this in
  Lean.  First, we can use the `#eval` command to evaluate a compound
  expression involving `nextWorkingDay`.  (Lean's responses are shown
  in comments.)
-/
-- BCP: Are these comments auto-verified?
-- TODO (Claude): They are not, and some have drifted from what Lean
-- actually prints (see `#eval minustwo 4` below).  Consider `#guard_msgs`
-- to machine-check the response comments so they can't rot.
-- /FULL


#eval nextWorkingDay Day.friday
/- ==> Day.monday -/

-- BCP: Can we write `nextWorkingDay .friday`?  If so, why didn't we?
-- If not, why not?
-- TODO (Claude): Related: the definition above uses the short form
-- `.monday` while this #eval uses the long form `Day.friday`, with no
-- stated rule for when each is used.  Suggest: use fully qualified names
-- first, introduce the `.` abbreviation explicitly as a convenience (as
-- BCP's comment above proposes), then stick to one convention.

#eval nextWorkingDay (nextWorkingDay Day.saturday)
/- ==> Day.tuesday -/

-- FULL
/-
  (We show Lean's responses in comments; if you have a computer
  handy, this would be an excellent moment to fire up VS Code with
  the Lean extension and try it for yourself.  Load this file,
  `Basics.lean`, from the book's Lean sources, find the above
  example, and observe the result in the Lean InfoView panel.)
-/

/-
  ## Aside: Using the VS Code Lean Extension
-/

/-
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

-/

-- RAB: There's a question of where exactly to put this.

-- /FULL

/-
  Continuing with our simple type and function, we can record what we _expect_
  the result of calling a function to be in the form of a Lean `example`:
-/

/- test_next_working_day -/
example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.tuesday := by
  rfl
-- BCP: Can we add some line breaks to that?  What is idiomatic?

-- FULL
/-
  This declaration does two things: it makes an assertion
  (that the second working day after `saturday` is `tuesday`), and it
  gives the assertion a name that we can use to refer to it later.

  Having made the assertion, we can also ask Lean to _verify_ it.
  The `by rfl` can be read as "The assertion we've just made can be
  proved by observing that both sides of the equality evaluate to
  the same thing."
-/
-- TODO (Claude): "gives the assertion a name that we can use to refer to
-- it later" is false in Lean: `example` is anonymous (the name survives
-- only in the `/- test_next_working_day -/` comment).  This is leftover
-- Rocq text.  Either use named `theorem`s for these tests or fix the prose.

/-
  `rfl` stands for "reflexivity," which is the principle that any value is
  equal to itself. After evaluation, both sides of the equality are the same
  value, so the assertion is true by reflexivity.  If we had made a different
  assertion, such as `example : nextWorkingDay (nextWorkingDay Day.saturday) =
  Day.monday`, then Lean would not be able to verify it, and would signal an
  error. Try it out!
-/
-- /FULL

-- TODO (Claude): The promise of "three different ways" (above) is broken:
-- the `example` mechanism is never labeled as the second way, and this
-- third way (compilation) is described but never demonstrated.  Either
-- demonstrate it (even a one-line `lake` mention) or reduce the
-- enumeration to two.
/-
  Third, we can ask Lean to _compile_ our definitions to efficient
  native code.

  Lean compiles to C, which is then compiled to machine code by a
  standard C compiler.  This facility is very useful, since it gives
  us a path from proved-correct algorithms written in Lean to
  efficient executables. We'll come back to this topic in later
  chapters.
-/

-- FULL
/- ###################################################################### -/
/- ## Running Lean -/
-- TODO (Claude): This section is nearly verbatim the same as RAB's
-- "Aside: Using the Lean Extension" above, and the parenthetical before
-- that repeats it a third time.  Keep one copy; the spot right after the
-- first #eval (RAB's location) seems best, since that is the first moment
-- the reader has a reason to look at the InfoView.

/-
   You may already be reading this chapter inside VS Code, but if not
   -- and if you have a computer handy -- this would be an excellent
   moment to fire up VS Code with the Lean extension and try it for
   yourself.  Load this file, `Basics.lean`, from the book's Lean
   sources, find the above examples, and observe the results in the
   Lean Infoview panel.

   In VS Code, development of Lean code is supported by the Lean
   Extension, which provides an interactive "infoview" panel that
   displays the results of commands like `#eval` and `#check`, as well
   as the current goal state when working on proofs. You can hover
   over expressions in `lean` files to see their types, and you can
   click on items in the infoview to navigate to their definitions.
   This makes it easier to understand how your code is being
   interpreted by Lean and fix any issues that arise.

   The infoview always follows your cursor, and Lean typechecks the
   file as you edit it, so you can see the results of your changes
   immediately. You can also use the infoview to explore the
   definitions of functions and types that you're using, which can be
   very helpful for understanding how they work.

   If you haven't already, install the Lean Extension in VS Code and
   open the `Basics.lean` file to see the infoview in action. Try
   hovering over the `nextWorkingDay` function and the `Day` type to
   see their definitions, and experiment with adding your own `#eval`
   commands to test other inputs.
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
-- TODO (Claude): The rationale for the `My` prefix is split across two
-- half-paragraphs here.  Suggest one explicit sentence: "we name it
-- `MyBool` only to avoid clashing with the built-in `Bool`; everything
-- else is identical."  (Keeping the constructors named `true`/`false`
-- seems right, per the harmonize-with-stdlib promise -- cf. BCP's
-- question below.)

/-
  The next command opens a new namespace so that our definitions don't
  clash with ones from the standard library. We'll discuss it in more
  detail below.
-/
-- TODO (Claude): "opens a new namespace" is incorrect: Lean sections do
-- not namespace declarations -- `notb`, `andb`, etc. land at root scope
-- and avoid clashes only because their names differ.  The correct
-- section/namespace distinction is taught later in this very file, so a
-- careful reader will notice the contradiction.  Fix the prose (or
-- actually use `namespace`).
section MyBool

-- BCP: Why call it MyBool instead of just Bool?  (Or, conversely, why call the constructors
-- true and false instead of mytrue, myfalse, mynotb, etc.?)
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

-- TERSE: /- *** -/

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
  The last two definitions illustrate Lean's syntax for multi-argument
  functions.  The corresponding multi-argument _application_ syntax is
  illustrated by the following tests, which effectively constitute a
  complete specification -- a truth table -- for the `orb` function:
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
-- BCP: We are already inside a section, no?
-- TODO (Claude): The notation declarations below expose precedence
-- numbers and `(priority := high)` with zero commentary, ~1200 lines
-- before notation is actually discussed.  Either tell the reader to
-- ignore the numbers for now or hide these lines.

section
local prefix:40 (priority := high) "!" => notb
local infixl:35 (priority := high) " && " => andb
local infixl:30 (priority := high) " || " => orb
-- BCP: Why spaces some places but not others?

/- test_orb5 -/
example : (.false || .false || .true) = .true := by rfl

/- test_orb6 -/
example : (! .false) = .true := by rfl
end

-- TERSE: /- *** -/
-- EX1 (nandb)
-- FULL
/-
  The `sorry` keyword is a placeholder for an incomplete proof or
  definition.  We use it in exercises to indicate the parts that we're
  leaving for you -- i.e., your job is to replace `sorry` with real
  definitions and proofs.

  Remove `sorry` below and complete the definition of the following
  function.  The function should return `true` if either or both of
  its inputs are `false`. Make sure that the `example` assertions
  below can be verified by Lean.
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
  Now that we've seen how to define our own booleans, let's switch
  back to Lean's built-in `Bool` type, which has the same structure
  but comes with a lot of useful functions and lemmas.  We can even
  define functions to convert between our `MyBool` and Lean's `Bool`.
-/
-- BCP: Do we really want to do this, rather than just leaving MyBool
-- completely behind?

def myBoolToBool (b : MyBool) : Bool :=
  match b with
  | .true => true
  | .false => false

/-
  Note how we don't have to use the `.`, because we have specified the type
  of `true` by declaring the return type of `myBoolToBool` to be `Bool`.
  Lean's type inference algorithm fills in the gap.
-/
-- BCP: Why can't type inference fill in the .??

/-
  With the full power of Lean's `Bool` at our disposal, we can also write this
  function more concisely using the `bif ... then ... else` syntax, which is a
  convenient way to write simple conditional expressions.
-/
-- TODO (Claude): `bif` deserves one sentence of explanation: beginners
-- will naturally write `if` next time and hit a `Decidable` error they
-- cannot interpret.  Explain why `bif` here (boolean-valued condition
-- vs. propositional `if`), or avoid the construct this early.

def boolToMyBool (b : Bool) : MyBool :=
  bif b then true else false
-- /FULL

end MyBool

-- RAB: From this point, there are about 450 lines of comments before
-- the next exercise. This is the same as in Rocq, but do we want
-- to keep this pattern?
-- BCP: Ideally no!
-- TODO (Claude): Concretely: even trivial drop-in exercises would keep
-- hands on keyboards through this stretch -- e.g., "define `isWeekend`",
-- "write a `Color` inverter", "add your own `#check` and predict the
-- output".  The namespaces/sections material in particular is reference
-- content that could become an exercise-light aside.

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
  Functions like `not` are themselves data values, just like `true`
  and `false`.  Their types are called _function types_, and they are
  written with arrows.
-/

#check not
/- ===> not : Bool → Bool -/

-- FULL
/-
  The type of `not`, written `Bool → Bool` and pronounced "`Bool`
  arrow `Bool`," can be read, "Given an input of type `Bool`, this
  function produces an output of type `Bool`." Similarly, the type of
  `and`, written `Bool → Bool → Bool`, can be read, "Given two inputs,
  each of type `Bool`, this function produces an output of type
  `Bool`." -/

/- ### Aside: Unicode in Lean -/

/-
  Note that → is a unicode symbol, not a simple ASCII character. The
  Lean Extension for VS Code provides convenient shortcuts for
  entering such symbols. Simply type `\` (backslash) followed by the
  name of the symbol, and the extension will automatically replace it
  with the actual symbol. For example, typing `\->` or `\to` will produce
  →, and `\lambda` will produce λ. To find out what backslash sequence
  produces a unicode symbol that you can see on the screen, just hover
  over it.
-/
-- /FULL

/-
  ######################################################################
  ## New Types from Old
-/

-- FULL
/-
  The types we have defined so far are simple examples of "enumerated
  types": their definitions explicitly enumerate a finite set of
  elements, called _constructors_.  Here is a more interesting type
  definition, `Color`, where one of the constructors takes an
  argument:
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
  - `true` (Lean's builtin Boolean type -- no `.` needed)
  - `Color.primary RGB.red`

  ...but these are not:

  - `RGB.red Color.primary`
  - `true RGB.red`
  - `Color.primary (Color.primary RGB.red)`
-/
-- BCP: Why do all of the constructors have namespaces except true and false?
-- TODO (Claude): The bullet above draws attention to this inconsistency
-- without resolving it, which is risky for beginners.  Either explain
-- (`Bool`'s constructors are exported to the root namespace) or drop
-- the remark.

-- TERSE: /- *** -/

/-
  We can define functions on colors using pattern matching, just as
  we did for `Day` and `Bool`.
-/

def monochrome (c : Color) : Bool :=
  match c with
  | .black => true
  | .white => true
  | .primary _ => false

/-
  Since the `primary` constructor takes an argument, a pattern
  that matches `primary` should include either a variable, a constant
  of appropriate type, or `_`. The last, as used in the above
  example, means that the constructor argument is being ignored.
  Examples below illustrate the other two cases.
-/
-- BCP: We didn't use a variable -- we used an underscore!  We should
-- explain this in two steps: first with an explicit name, then with
-- an underscore.

def isRed (c : Color) : Bool :=
  match c with
  | .black => false
  | .white => false
  | .primary .red => true
  | .primary _ => false

/-
  The pattern `.primary red` will match only when `c` is
  `Color.primary` with the argument `RGB.red`. Patterns are checked in
  order, so the subsequent pattern `.primary _` here means "the
  constructor `primary` applied to any `RGB` constructor except
  `red`."
-/
-- TODO (Claude): Typo above: "The pattern `.primary red`" is missing the
-- dot on `red` (the code says `.primary .red`).  Since dot-notation rules
-- are exactly what beginners are absorbing here, this will actively
-- confuse.

def isRed' (c : Color) : Bool :=
  match c with
  | .black => false
  | .white => false
  | .primary r =>
    match r with
    | .red => true
    | _ => false

/-
  The new `isRed'` function produces the same result as the old
  `isRed` but illustrates the use of a pattern matching variable: the
  `.primary r` pattern stores the `RGB` argument into variable `r`,
  and then pattern matches on that argument to produce the final
  result.
-/

/-
  ######################################################################
  ## Namespaces and Sections
-/

-- JC: I edited a lot of the contents and comments in just this section,
-- I hope it makes sense.

-- FULL
/-
  Lean provides a _namespace system_ to aid in organizing large
  developments. If we enclose a collection of declarations in
  `namespace X ... end X`, then, in the rest of the file after the
  `end`, these definitions will be referred to by names like `X.foo`
  instead of just `foo`. We will use this feature to limit the scope
  of definitions so that we are free to reuse names (in particular,
  names from the standard library).
-/
-- BCP: This doesn't explain why we *want* to reuse names freely?
-- /FULL
-- TERSE: /- `namespace` declarations create separate namespaces. -/

def myFoo : Bool := true
namespace Playground
def myFoo : RGB := RGB.blue
end Playground

#check myFoo             -- Bool
#check Playground.myFoo  -- RGB

-- FULL
/-
  When inside a `namespace` region, definitions from the same
  namespace can be referenced without prefixes.

  Top-level definitions can also be prefixed by a namespace to put
  them in the namespace "from the outside," without having to open and
  close it.
-/
-- /FULL

namespace RGB
-- BCP: RGB was declared as an inductive type, and it's used here in
-- both senses. Is this intentional?
def myBlue : RGB := blue
end RGB

def RGB.myOtherBlue : RGB := myBlue

/-
  #check myBlue -- unknown identifier
-/
-- BCP: Huh? We just used `myBlue` as a top-level id, didn't we?  So
-- why is it unknown?
#check RGB.myBlue      -- RGB
#check RGB.myOtherBlue -- RGB

-- FULL
/-
  We can also use `open` to bring the definitions of a namespace into
  the current scope; after that, we can refer to any of the namespace's
  definitions without a prefix.

  Definitions of the same name declared prior to the `open` can be
  referred to by the special prefix `_root_`. Lean also provides
  _sections_, which delimit the scope of `open`ing namespaces and
  `local` notations within `section ... end`. We already saw `prefix`
  and `infix` notations for MyBool; there are also `postfix`
  notations.
-/
-- BCP: That goes by *waaay* too fast!
-- BCP: Is the `_root_` thing something that readers actually need to know?
-- /FULL
-- TERSE: /- `section` declarations delimit the scope of `open` and `local`. -/

section
open Playground
local postfix:40 "′" => Color.primary
-- BCP: Not convinced we need to teach people about `postfix` and
-- suchlike in this chapter (or anyplace, really, but I will object
-- less to it if we do it later).

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
  ## Constructors with Multiple Arguments
-/

namespace Playground

-- FULL
/-
  A single constructor with multiple parameters can be used to create
  a tuple type. As an example, consider representing the four bits in
  a nibble (half a byte). We first define a datatype `Bit` that
  resembles `Bool` (using the constructors `b1` and `b0` for the two
  possible bit values) and then define the datatype `Nibble`, which is
  essentially a tuple of four bits.
-/
-- /FULL

-- TERSE: /- A nibble is half a byte -- four bits. -/

inductive Bit : Type where
  | b1
  | b0

inductive Nibble : Type where
  | bits (x0 x1 x2 x3 : Bit)

#check (.bits .b1 .b0 .b1 .b0 : Nibble)

-- FULL
/-
  Note: The `bits` constructor illustrates a feature of multi-argument
  declarations, both for constructors and for functions: Instead
  of writing `(x0 : Bit) (x1 : Bit) ...` we write `(x0 x1 ... : Bit)`
  since all of the variables have the same type. We could have done
  the same with the function definition `orb` above, writing
  `orb (b1 b2 : MyBool)` rather than `orb (b1 : MyBool) (b2 : MyBool)`.
-/

/-
  The `bits` constructor acts as a wrapper for its contents.
  Unwrapping is done by pattern matching, as in the `allZero` function
  below, which tests a nibble to see if all its bits are `b0`.
-/
-- /FULL

-- TERSE: /- *** -/
-- TERSE: /- We can deconstruct a nibble by pattern-matching. -/

def allZero (nb : Nibble) : Bool :=
  match nb with
  | .bits .b0 .b0 .b0 .b0 => true
  | .bits _   _   _   _   => false

#eval allZero (.bits .b1 .b0 .b1 .b0)
/- ===> false -/
#eval allZero (.bits .b0 .b0 .b0 .b0)
/- ===> true -/

end Playground

/-
  ######################################################################
  ## Natural Numbers
-/

-- FULL
/-
  We put this section in a namespace so that our own definition of
  numbers does not interfere with the one from the standard library.
  In the remainder of the book, we'll use the standard library's.
-/
-- /FULL

-- BCP: Is "section" used in a technical sense in that paragraph? Why
-- do we need both namespaces and sections (particularly in this first
-- chapter)?

namespace NatPlayground

-- FULL
/-
  All the types we have defined so far -- both "enumerated
  types" such as `Day`, `Bool`, and `Bit` and tuple types such as
  `Nibble` built from them -- are finite. The natural numbers, on
  the other hand, are an infinite set, so we'll need to use a
  slightly richer form of type declaration to represent them.
-/

/-
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
-/

-- /FULL

-- TERSE: For simplicity in proofs, we choose a _unary_
-- representation.

inductive Nat : Type where
  | zero
  | succ (n : Nat)

-- TODO (Claude): The instructor advice at the top says to work
-- directly in this .lean file, but the "hidden" scaffolding (this
-- attribute, the OfNat instance, `unseal`, `@[irreducible]`,
-- the BEq instance) is fully visible to anyone reading
-- the source, and far beyond a beginner's reach. BCP: Same question
-- as Claude here: Do we really need this?  If so, how / where do we
-- explain it?
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

/-
  With this definition, 0 is represented by `zero`, 1 by `succ zero`, 2 by `succ
  (succ zero)`, and so on.

  We use some machinery in the background to allow us to write `0`, `1`, `2`,
  etc. instead of `zero`, `succ zero`, etc., for our custom definition of `Nat`.
  This is just syntactic sugar, and the two forms are interchangeable.
-/
-- BCP: Can we be more explicit about the machinery?

-- BCP: What are these RULES comments for?
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
-- BCP: We already said that, no?

  #check Nat
  /- ==> NatPlayground.Nat : Type -/ /- ← this is our `Nat`... -/
  #check _root_.Nat
  /- ==> _root_.Nat : Type -/ /- ← ...this is Lean's `Nat`. -/

/-
  Lean's `Nat` comes with some powerful built-in features for reasoning and
  notation.

  As we are just beginning to reason about natural numbers, we use our own
  definition here and introduce the Lean one in a later chapter.
-/

/-
  We can also write functions on `Nat`.
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
-- BCP: Yes!

-- BCP: Missing transition

-- FULL
#check Nat.succ  -- Nat → Nat
#check Nat.pred  -- Nat → Nat
#check minustwo  -- Nat → Nat

/-
  These are all things that can be applied to a number to yield a
  number. However, there is a fundamental difference between
  `Nat.succ` and the other two: functions like `Nat.pred` and
  `Nat.minustwo` are defined by giving _computation rules_ -- e.g.,
  the definition of `Nat.pred` says that `Nat.pred (succ (succ zero))`
  can be simplified to `succ zero` -- while the definition of
  `Nat.succ` has no such behavior attached. Although it is like a
  function in the sense that it can be applied to an argument, it does
  not _do_ anything at all! It is just the way we write down numbers.
-/
-- /FULL

-- TERSE: /- *** -/
-- TERSE: /- Recursive functions: -/

def even (n : Nat) : Bool :=
  match n with
  | zero => true
  | succ (zero) => false
  | succ (succ n') => even n'

theorem even_zero : even zero = true := rfl
theorem even_one : even (succ zero) = false := rfl
theorem even_succ_succ n : even (succ (succ n)) = even n := rfl

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

-- TODO (Claude): The sealing strategy needs to be acknowledged in the
-- text.  `add` and `mul` are irreducible (so `rfl` won't prove
-- `1 + 1 = 2`, usefully forcing rewrite practice), but `even`, `beq`,
-- and `leb` are not, so `rfl` blasts right through `leb 2 2 = true`.
-- A beginner will inevitably ask why `rfl` works on some computations
-- and not others -- and stock Lean *will* prove `1 + 1 = 2` by `rfl`.
-- One honest paragraph ("we have deliberately sealed `add` so you must
-- practice rewriting; real Lean computes it") would defuse this.
@[irreducible]
def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m')

instance instAdd : Add Nat where add := add

-- BCP STOPPED HERE

-- FULL
/-
  ######################################################################
  # Proof by Rewriting

  ## Proving properties about functions in Lean

  Being recursive, `add` is our first example of a more sophisticated
  class of functions. In this chapter and beyond, we will _prove_
  properties about recursive functions like `add` over inductive
  datatypes like `Nat` using _simplification rules_ about their
  behavior.

  Here is a simple rule about `add`:

  - `n + 0 = n`

  In Lean, this rule looks like this:
-/
-- /FULL
-- BCP: Why does the Info View say "Goals accomplished!" right at the
-- beginning of the proof?  Can we comment on this?
unseal add in
theorem add_zero : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl
-- FULL

#check add_zero
/- ==> NatPlayground.Nat.add_zero (n : Nat) : n + 0 = n -/
-- BCP: We will probably want to remove the "NatPlayground" stuff from
-- all these comments when we fix the printing.

/-
   We can then use the `add_zero` rule to carry out a simple proof
   about natural numbers!
-/

theorem add_zero_zero (n : Nat) : n + 0 + 0 = n := by
  rewrite [add_zero]
  rewrite [add_zero]
  rfl

-- Let's walk through this proof.

-- BCP: We need a consistent convention about **boldface** vs _italic_
-- for emphasis.
/-
  ## Proof state and tactics

  The "proof commands" -- `rewrite`, `rfl`, etc. -- are called
  **tactics**. The `add_zero` in brackets is an _argument_ to the
  `rewrite` tactic.

  Hovering with the cursor over each line of the proof, we can see the
  **proof state** in the Lean InfoView panel.

  The proof state is divided into the **context**, before the ⊢,
  and the **goal**, after the ⊢. The context is what we know at each point, while
  the goal is what we are trying to prove.

  A tactic manipulates both the goal and the context to get the goal
  into a shape that is closer to the one we want. A tactic can also
  _close_ (solve) the current goal which finishes its proof.

  Let's walk through the example above with this terminology in mind.
-/

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
  -- ADMITTED
  rewrite [add_zero]
  rewrite [add_zero]
  rewrite [add_zero]
  rfl
  -- /ADMITTED

/-
 ## The `rewrite` tactic

   As we saw above, the tactic that tells Lean to rewrite (part of) a goal or
   hypothesis based on a rule is called `rewrite`. Given the rule `add_zero`,
   which states that `n + 0` is equal to `n` for any `n`, we can replace any `n
   + 0` in our proof with `n` via `rewrite [add_zero]`.

   The `rewrite` tactic takes its argument(s) in square brackets.

  ## The `rfl` tactic

  The `rfl` tactic closes a goal of the shape `a = a`, for any `a`. It
  checks that both sides of the equality are _definitionally equal_ --
  that is, that they reduce to the same thing. (So, in particular, a
  term is always definitionally equal to itself.)
-/

/- ## A New `add` Rule

   Here is another fundamental rule about addition:

   `n + (succ m) = succ (n + m)`.

   This is the rule we need to push `succ` around.
-/

/- Here it is in Lean: -/
unseal add in
theorem add_succ : ∀ n m : Nat, n + succ m = succ (n + m) := by
  intro n m
  rfl

-- BCP: Maybe we don't need this?
#check add_succ
/- ==> add_succ (n m : Nat) : n + succ m = succ (n + m) -/

/- And here it is in a proof: -/

theorem add_succ_zero (n : Nat) : n + succ 0 = succ (n + 0 + 0) := by
  rewrite [add_succ]
  rewrite [add_zero]  /- notice how this handles an addition on both sides -/
  rewrite [add_zero]
  rfl

/- Again, we recommend stepping through these proofs in VS Code --
   that is, moving past each tactic with your cursor to see how it
   changes the proof state.
-/

/- ## Working with Numerals

   We know from above that `1` is just `succ 0`, `2` is `succ 1`, and so on.
   We have rules for these equalities, as well:
-/

-- BCP: We have them because we stated them above, but maybe the
-- reader wasn't sure why we did that.  I'm a little confused what
-- point we're making just here.
#check one_eq_succ_zero /- ==> one_eq_succ_zero : 1 = succ 0 -/
#check two_eq_succ_one /- ==> two_eq_succ_one : 2 = succ 1 -/
#check three_eq_succ_two /- ==> three_eq_succ_two : 3 = succ 2 -/

/- We can rewrite with these rules to expand numerals into their definitions,
   which allows us to use our `add` rules. -/

-- /FULL

/- Here's an example of how to start a proof this way.
   Finish the proof using the `add` rules.
 -/
 -- BCP: Should this be marked / formatted as an exercise?
theorem one_plus_one_eq_two : (1 + 1 : Nat) = 2 := by
  rewrite [one_eq_succ_zero]
  -- ADMITTED
  rewrite [add_succ]
  rewrite [add_zero]
  rfl
  -- /ADMITTED

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
-- BCP: We should make this point wherever we rewrite to the left for
-- the first time. It's out of place here.
-- /FULL

-- FULL
/-
  Now that we know how addition is defined, we can use it to define
  multiplication:
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
-- BCP: Why almost?

unseal mul in
theorem mul_zero : ∀ n : Nat, n * 0 = 0 := by
  intro n
  rfl

unseal mul add in
theorem mul_succ : ∀ n m : Nat, n * succ m = n * m + n := by
  intro n m
  rfl

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

-- TODO: We need to make a decision about `==`.
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

theorem zero_leb (n : Nat) : leb zero n = true := by rfl
theorem succ_leb_zero (n : Nat) : leb (succ n) zero = false := by rfl
theorem succ_leb_succ (n m : Nat) : leb (succ n) (succ m) = leb n m := by rfl

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

-- BCP: Readers may wonder what "instance" is...
instance : BEq Nat where
  beq := beq

infix:65 "≤?" => leb

/-
  test_leb3'
-/
example : 4 ≤? 2 = false := by rfl

-- FULL
-- TODO (Claude): `=?` does not exist in this file -- we defined `==`
-- (via BEq), `≤?`, and `<?`.  Rocq residue.  Since `=` vs `==` is one of
-- the most important distinctions in the chapter, this paragraph must
-- use the actual notation.
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

-- TODO (Claude): The theorem is billed as "an important property" but
-- is never motivated or used in this chapter -- it reads as an
-- orphan.
theorem beq_succ : ∀ n m : Nat, (succ n == succ m) = (n == m) := by
  intro n m
  rfl

/-
  ######################################################################
  # General Proofs about Natural Numbers
-/

-- TERSE: /- A (slightly) more interesting theorem: -/

-- TODO (Claude): The file mixes two binder styles without comment:
-- `theorem foo (n : Nat) : ...` (no `intro` needed, e.g. `add_zero_zero`)
-- vs. `theorem foo : ∀ n : Nat, ...` plus `intro` (here).  "When do I
-- need `intro`?" is one of a beginner's first hard questions; one
-- explicit paragraph reconciling the two styles would prevent
-- cargo-culting.
-- FULL
/-
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
-/
-- /FULL

-- BCP: I find the indentation / linebreaking choices here kind of
-- ugly. Are they standard, or can we make a better convention?
theorem add_id_example : ∀ n m : Nat,
    n = m →
    n + n = m + m := by
  intro n m
  intro h
  rewrite [h]
  rfl

-- TERSE: We make a general claim about natural numbers and prove it
-- by rewriting with the hypothesis.

-- FULL
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
-- TODO (Claude): `sorry` was already explained before the nandb
-- exercise, and this second explanation arrives *after* add_id_exercise
-- told the student to remove a `sorry`.  Keep one explanation, placed
-- before its first use, and cover both roles there (exercise placeholder
-- / temporarily accepting a claim).
-- /FULL

-- TERSE: /- *** -/

/-
  The `#check` command can also be used to examine the statements of
  previously declared lemmas and theorems.
-/

/- TODO: how to get these to show `∀ (n : Nat)` instead of `mul_zero (n : Nat)` -/
-- BCP: Or maybe we need to explain that they mean the same thing?  I
-- think we are a bit inconsistent, ourselves, in the way we write
-- things.
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
  Of course, not everything can be proved by simple calculation and
  rewriting: In general, the presence of unknown, hypothetical values
  (arbitrary numbers, booleans, etc.) can block simplification.
-/
-- /FULL
-- TERSE: Sometimes simple calculation and rewriting are not enough...

-- INSTRUCTORS: We use `#guard_msgs` in a number of places in the SFL
-- source files to help deter bitrot, and you are encouraged to add
-- your own instances.  It doesn't need to be explained to students
-- because it gets stripped out when verso files are translated to
-- .lean and .html.

/-- warning: declaration uses `sorry` -/
#guard_msgs(warning) in
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
  The `cases` tactic generates _two_ subgoals, which we must
  prove, separately, in order to get Lean to accept the theorem.

  The generated subgoals are tagged by the names of the constructors.
  `case zero =>` and `case succ n' =>` select which subgoal to work on next
  and introduce variable names.

  The `cases` tactic can be used with any inductively defined
  datatype.  For example, we use it next to prove that boolean
  negation is involutive (that is, that negation is its own inverse).
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
  ## New Tactics: `rewrite ... at` and `exact`

  Some new tactics will be useful for the exercises ahead.

  The `rewrite` tactic can be used to rewrite in a hypothesis instead of the
  goal. For example, if `h : P` is in the context and we have a rule `P = Q`,
  then `rewrite [P = Q] at h` changes the hypothesis to `h : Q`.

  The `exact` tactic closes a goal by providing an exact proof term.  For
  example, if `h : P` is in the context and the goal is `P`, then `exact h`
  closes the goal.  You can also transform `h` slightly — for instance, `exact
  h.symm` uses the symmetry of equality.
-/
-- BCP: What is "proof term"?
-- BCP: What is "h.symm"??  The explanation there is way too fast.

-- FULL
-- EX2 (orb_false_true)
/-
  Prove the following claim.

  Tip: the rewrite rule to simplify `(b || false)` is called `Bool.or_false`.
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

  Lean handles notation scoping through namespaces and _type classes_
  rather than notation scopes.  The numeric literal `3` can be
  interpreted as `Nat`, `Int`, `Float`, etc., depending on the
  expected type, thanks to Lean's `OfNat` type class. We explain type
  classes in full in a later chapter.
-/
/- TODO: which chapter? -/
-- BCP: What is "notation scopes"?  Can this explanation be streamlined?
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
-- BCP: That last paragraph will be opaque to many readers.

-- EX2? (decreasing)
/-
  To get a concrete sense of this, find a way to write a sensible
  recursive definition (of a simple function on numbers, say) that
  does actually terminate on all inputs, but that Lean will reject
  because it cannot automatically prove termination.
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
-- TODO (Claude): The `unseal Nat.mul Nat.add in` incantations below sit
-- directly on tests students must read and extend; a student who writes
-- their own test will see it mysteriously fail without the unseal.
-- Needs either an explanation or a way to hide it.
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
-- TODO (Claude): This exercise quietly requires rewriting with a
-- *universally quantified* hypothesis -- a real conceptual jump from
-- rewriting with `h : n = m` that deserves a sentence of preparation.

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
  cases b
  case true => rfl
  case false => rfl
--  /SOLUTION

--  GRADE_MANUAL 1: negation_fn_applied_twice
-- []

-- EX3? (andb_eq_orb)
/-
  Prove the following theorem.
-/

-- BCP: The indentation here is even more problematic... Is this a
-- systematic problem with the way the file was translated?
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
