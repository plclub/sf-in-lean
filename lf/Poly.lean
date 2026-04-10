-- Poly: Polymorphism and Higher-Order Functions

-- INSTRUCTORS: To get through this plus Tactics.lean in two 80-minute
--    lectures is a bit tight -- if that's your plan, don't dawdle on
--    this chapter.

-- HIDEFROMHTML
-- FULL
-- Final reminder: Please do not put solutions to the exercises in
--    publicly accessible places.  Thank you!!

-- /FULL
-- /HIDEFROMHTML
-- TERSE: HIDEFROMHTML
import Induction
-- TERSE: /HIDEFROMHTML

-- HIDEFROMADVANCED
-- FULL
-- ######################################################################
-- * Polymorphism

-- In this chapter we continue our development of basic
-- concepts of functional programming.  The critical new ideas are
-- _polymorphism_ (abstracting functions over the types of the data
-- they manipulate) and _higher-order functions_ (treating functions
-- as data).  We begin with polymorphism.

-- /FULL
-- ######################################################################
-- ** Polymorphic Lists

-- FULL: In the last chapter, we worked with lists containing just
-- numbers.  Obviously, interesting programs also need to be able to
-- manipulate lists with elements from other types -- lists of
-- booleans, lists of lists, etc.  We _could_ just define a new
-- inductive datatype for each of these, for example...

-- TERSE: Instead of defining new lists for each type, like
--     this...

inductive BoolList : Type where
  | bool_nil
  | bool_cons (b : Bool) (l : BoolList)

-- FULL: ... but this would quickly become tedious: not only would we
-- have to make up different constructor names for each datatype, but --
-- even worse -- we would also need to define new versions of all
-- the list manipulating functions (`List.length`, `++`, `List.reverse`,
-- etc.) and all their properties (`rev_length`, `app_assoc`, etc.)
-- for each new definition.

-- TERSE: ***

-- FULL: To avoid all this repetition, Lean supports _polymorphic_
-- inductive type definitions.  For example, here is a _polymorphic
-- list_ datatype.
-- /HIDEFROMADVANCED
-- TERSE: ...Lean lets us give a _polymorphic_ definition that allows
-- list elements of any type:

namespace Playground

inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons (x : α) (l : MyList α) : MyList α

-- FULL: This is exactly like the definition of `List Nat` from the
-- previous chapter, except that the `Nat` argument to the `cons`
-- constructor has been replaced by an arbitrary type `α`, a binding
-- for `α` has been added to the header on the first line,
-- and the occurrences of `List Nat` in the types of the constructors
-- have been replaced by `MyList α`.  We can now write `MyList Nat`
-- instead of a dedicated nat-list type.
--
-- What sort of thing is `MyList` itself?  A good way to think about it
-- is that the definition of `MyList` is a _function_ from `Type`s to
-- `Type`s.  For any particular type `α`,
-- the type `MyList α` is the inductively defined set of lists whose
-- elements are of type `α`.
-- TERSE: We can now write `MyList Nat` in place of a dedicated
-- nat-list type.

-- TERSE: ***

-- TERSE: What is `MyList` itself?
--
-- It is a _function_ from types to types.

#check MyList -- MyList : Type → Type

-- TERSE: ***

-- FULL: The `α` in the definition of `MyList` automatically becomes a
-- parameter to the constructors `nil` and `cons` -- that is, `nil`
-- and `cons` are now polymorphic constructors.  In Lean, the type
-- parameter is _implicit_ by default: Lean will infer it from context.
-- For example, `MyList.nil` is the empty list, and Lean figures out
-- the element type from how it is used.

-- TERSE: The `α` in the definition of `MyList` becomes an implicit
-- parameter to the list constructors `nil` and `cons`.

#check (MyList.nil : MyList Nat)

-- FULL: Similarly, `MyList.cons` adds an element of type `Nat` to a
-- list of type `MyList Nat`.  Here is an example of forming a list
-- containing just the natural number 3.

#check (MyList.cons 3 MyList.nil : MyList Nat)

-- FULL: What might the type of `MyList.nil` be?  We can read off the
-- type `MyList α` from the definition, but what is `α`?  In Lean,
-- the type parameter is implicit (written in curly braces `{α : Type}`),
-- so `MyList.nil` has type `MyList α` for any `α`.  Lean's notation
-- for this is `{α : Type} → MyList α`, which is displayed as
-- `MyList ?α` with `?α` as a metavariable to be inferred.

#check @MyList.nil  -- @MyList.nil : {α : Type} → MyList α

-- FULL: Similarly, the type of `MyList.cons` includes the implicit
-- type parameter:

#check @MyList.cons  -- @MyList.cons : {α : Type} → α → MyList α → MyList α

-- HIDEFROMADVANCED
-- FULL: Having to supply a type argument for every single use of a
-- list constructor would be rather burdensome.  Lean avoids this by
-- making the type parameter implicit: it is automatically inferred
-- from context.

-- FULL: We can now go back and make polymorphic versions of all the
-- list-processing functions that we wrote before.  Here is `myRepeat`,
-- for example:

-- /HIDEFROMADVANCED
-- TERSE: ***
-- TERSE: We can now define polymorphic versions of the functions
--     we've already seen...

def myRepeat {α : Type} (x : α) (count : Nat) : MyList α :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (myRepeat x count')

-- FULL: Unlike Rocq, we don't need to pass the type explicitly to
-- `myRepeat` -- Lean infers it from the type of `x`.  The type parameter
-- `α` is implicit here because Lean uses _auto-bound implicit_
-- variables: any free variable in a definition's type signature is
-- automatically bound as an implicit argument.

-- HIDEFROMADVANCED

-- test_repeat1
example : myRepeat 4 2 = .cons 4 (.cons 4 .nil) := by rfl

-- FULL: To use `myRepeat` to build other kinds of lists, we simply
-- pass an element of the appropriate type:

-- test_repeat2
example : myRepeat false 1 = .cons false .nil := by rfl

-- QUIZ
-- What is the type of `MyList.cons true (MyList.cons 3 MyList.nil)`?
--
-- (A) `MyList Nat`
--
-- (B) `{α : Type} → α → MyList α → MyList α`
--
-- (C) `MyList Bool`
--
-- (D) `MyList (Nat × Bool)`
--
-- (E) Ill-typed
-- /QUIZ

-- QUIZ
-- What is the type of `myRepeat`?
--
-- (A) `Nat → Nat → MyList Nat`
--
-- (B) `{α : Type} → α → Nat → MyList α`
--
-- (C) `{α : Type} → {β : Type} → α → Nat → MyList β`
--
-- (D) Ill-typed
-- /QUIZ

-- QUIZ
-- What is the type of `myRepeat 1 2`?
--
-- (A) `MyList Nat`
--
-- (B) `{α : Type} → α → Nat → MyList α`
--
-- (C) `MyList Bool`
--
-- (D) Ill-typed
-- /QUIZ

-- /HIDEFROMADVANCED

end Playground

-- FULL
-- ** Implicit Arguments in Lean
--
-- In Lean, there are several ways to declare implicit arguments:
--
-- - **Curly braces `{α : Type}`**: The argument is implicit and Lean
--   will try to infer it from context.  If it can't, you'll get an
--   error.
--
-- - **Auto-bound implicits**: Any free type variable in a signature
--   is automatically treated as implicit.  So writing
--   `def myRepeat (x : α) (count : Nat) : List α` is equivalent to
--   `def myRepeat {α : Type} (x : α) (count : Nat) : List α`.
--
-- - **The `@` prefix**: You can use `@f` to make all implicit
--   arguments of `f` explicit.  For example, `@List.nil Nat` is the
--   empty list of natural numbers.
--
-- This is Lean's analogue of Rocq's `Arguments` directive and `_`
-- holes.  In practice, Lean's implicit arguments are more convenient
-- because they are the default -- you rarely need to supply type
-- arguments explicitly.
-- /FULL

-- FULL: From now on, we'll use Lean's built-in `List` type and its
-- associated notation.  The built-in `List` is defined just like
-- our `MyList` above, but with notation `[]` for `List.nil`,
-- `::` for `List.cons`, and `[1, 2, 3]` for list literals.
-- The `++` operator is list append.  All type arguments are implicit.

-- TERSE: *** From now on we'll use Lean's built-in `List α` type
-- with notation `[]`, `::`, `[1, 2, 3]`, and `++`.

-- FULL
-- ** Supplying Type Arguments Explicitly
--
-- One small problem with implicit arguments is that, once in a
-- while, Lean does not have enough local information to determine
-- a type argument; in such cases, we need to tell Lean the type
-- explicitly.  For example:
-- TERSE: In general, it's fine to just let Lean infer all type
-- arguments.  But occasionally this can lead to problems:

-- This fails because Lean can't figure out the type of the empty list:
-- `def mynil := []` -- error: type not known
-- We can fix this with an explicit type annotation:

def mynil : List Nat := []

-- Alternatively, we can use the `@` prefix to supply the type
-- argument explicitly.  The `@` makes all implicit arguments
-- of a function explicit:

#check @List.nil  -- @List.nil : {α : Type u_1} → List α

def mynil' := @List.nil Nat

-- TERSE: ***

-- FULL: Using Lean's built-in list notation, we can now write lists
-- in the natural way:
-- TERSE: Using Lean's notation, we can write lists naturally:

def list123 : List Nat := [1, 2, 3]

-- HIDEFROMADVANCED
-- TERSE: HIDEFROMHTML

-- TERSE
-- QUIZ
-- Which type does Lean assign to the following expression?
-- HIDEFROMHTML
-- (The square brackets in this quiz and the following ones are list
-- brackets.)
-- /HIDEFROMHTML
--
--     [1, 2, 3]
--
-- (A) `List Nat`
--
-- (B) `List Bool`
--
-- (C) `Bool`
--
-- (D) No type can be assigned
-- /QUIZ
-- INSTRUCTORS: (A)

-- QUIZ
-- What about this one?
--
--     [3 + 4] ++ []
--
-- (A) `List Nat`
--
-- (B) `List Bool`
--
-- (C) `Bool`
--
-- (D) No type can be assigned
-- /QUIZ
-- INSTRUCTORS: (A)

-- QUIZ
-- What about this one?
--
--     (true && false) :: []
--
-- (A) `List Nat`
--
-- (B) `List Bool`
--
-- (C) `Bool`
--
-- (D) No type can be assigned
-- /QUIZ
-- INSTRUCTORS: (B)

-- QUIZ
-- What about this one?
--
--     [1, []]
--
-- (A) `List Nat`
--
-- (B) `List (List Nat)`
--
-- (C) `List Bool`
--
-- (D) No type can be assigned
-- /QUIZ
-- INSTRUCTORS: (D)

-- QUIZ
-- What about this one?
--
--     [[1], []]
--
-- (A) `List Nat`
--
-- (B) `List (List Nat)`
--
-- (C) `List Bool`
--
-- (D) No type can be assigned
-- /QUIZ
-- INSTRUCTORS: (B)

-- QUIZ
-- And what about this one?
--
--     [1] :: [[]]
--
-- (A) `List Nat`
--
-- (B) `List (List Nat)`
--
-- (C) `List Bool`
--
-- (D) No type can be assigned
-- /QUIZ
-- INSTRUCTORS: (B)

-- QUIZ
-- This one?
--
--     @List.nil Bool
--
-- (A) `List Nat`
--
-- (B) `List (List Nat)`
--
-- (C) `List Bool`
--
-- (D) No type can be assigned
-- /QUIZ
-- INSTRUCTORS: (C)

-- /TERSE

-- TERSE: /HIDEFROMHTML

-- *** Exercises

-- TERSE: HIDEFROMHTML

-- EX2 (poly_exercises)
-- Here are a few simple exercises, just like ones in the `Lists`
-- chapter, for practice with polymorphism.  Complete the proofs below.

def rev {α:Type} (l:List α) : List α :=
  match l with
  | .nil => .nil
  | .cons h t => rev t ++ (.cons h .nil)

-- app_nil_r
theorem app_nil_r {α : Type} : ∀ (l : List α),
  l ++ [] = l := by
  -- ADMITTED
  intro l; induction l
  . case nil => rfl
  . case cons h t ih => dsimp; rw [ih]
-- /ADMITTED

-- app_assoc
theorem app_assoc {α : Type} : ∀ (l m n : List α),
  l ++ m ++ n = l ++ (m ++ n) := by
  -- ADMITTED
  intro l m n; induction l
  . case nil => rfl
  . case cons h t ih => dsimp; rw [ih]
-- /ADMITTED

-- app_length
theorem app_length {α : Type} : ∀ (l1 l2 : List α),
  (l1 ++ l2).length = l1.length + l2.length := by
  -- ADMITTED
  intro l1 l2; induction l1
  . case nil => dsimp; rw [zero_add]
  . case cons h t ih => dsimp; rw [succ_add, ih]
-- /ADMITTED
-- GRADE_THEOREM 0.5: app_nil_r
-- GRADE_THEOREM 1: app_assoc
-- GRADE_THEOREM 0.5: app_length
-- []

-- EX2 (more_poly_exercises)
-- Here are some slightly more interesting ones...

-- rev_app_distr
theorem rev_app_distr {α : Type} : ∀ (l1 l2 : List α),
  rev (l1 ++ l2) = rev l2 ++ rev l1 := by
  -- ADMITTED
  intro l1 l2; induction l1
  . case nil => dsimp [rev]; rw [app_nil_r]
  . case cons h t ih => dsimp [rev]; rw [ih]; rw [app_assoc]
-- /ADMITTED

-- rev_involutive
theorem rev_involutive {α : Type} : ∀ (l : List α),
  rev (rev l) = l := by
  -- ADMITTED
  intro l; induction l
  . case nil => rfl
  . case cons h t ih =>
      dsimp [rev]
      rw [rev_app_distr, ih]
      dsimp [rev]
-- /ADMITTED
-- GRADE_THEOREM 1: rev_app_distr
-- GRADE_THEOREM 1: rev_involutive
-- []
-- /HIDEFROMADVANCED
-- HIDEFROMADVANCED
-- TERSE: /HIDEFROMHTML
-- /HIDEFROMADVANCED

-- ######################################################################
-- ** Polymorphic Pairs

-- FULL: Following the same pattern, the definition for pairs of
-- numbers that we gave in the last chapter can be generalized to
-- _polymorphic pairs_, often called _products_.  Lean's standard
-- library provides `Prod α β` (written `α × β`) with constructor
-- `Prod.mk` (written `(a, b)`).

-- TERSE: Similarly, Lean provides polymorphic pairs `α × β`...

-- FULL: Let's briefly look at what the built-in product type provides:

#check (1, true)        -- (1, true) : Nat × Bool
#check (1, true).1      -- access first component
#check (1, true).2      -- access second component

-- HIDEFROMADVANCED
-- FULL: The notation `α × β` is syntactic sugar for `Prod α β`.
-- Values are constructed with `(a, b)` or `Prod.mk a b`.  The
-- projections are `.1` (or `.fst`) and `.2` (or `.snd`).
-- /HIDEFROMADVANCED

-- TERSE: Be careful not to get `(x, y)` and `α × β` confused!
-- TERSE: ***

-- FULL: The first and second projection functions look like this in
-- Lean:

-- These are already provided as `Prod.fst` and `Prod.snd`, or
-- equivalently `.1` and `.2`.  For illustration:

-- fst_example
example : (3, 5).1 = 3 := by rfl
-- snd_example
example : (3, 5).2 = 5 := by rfl

-- FULL: The following function takes two lists and combines them
-- into a list of pairs.  In other functional languages, it is often
-- called `zip`; Lean calls it `List.zip`.
-- TERSE: ***
-- TERSE: What does this function do?

def combine {α : Type} {β : Type} (lx : List α) (ly : List β) : List (α × β) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: combine tx ty

-- FULL
-- EX1M? (combine_checks)
-- Try answering the following questions on paper and
-- checking your answers in Lean:
-- - What is the type of `combine` (i.e., what does `#check @combine`
--   print?)
-- - What does
--       #eval combine [1, 2] [false, false, true, true]
--   print?
-- []

-- EX2! (split)
-- The function `split` is the right inverse of `combine`: it takes a
-- list of pairs and returns a pair of lists.  In many functional
-- languages, it is called `unzip`.
--
-- Fill in the definition of `split` below.  Make sure it passes the
-- given unit test.

def split {α : Type} {β : Type} (l : List (α × β)) : List α × List β :=
  -- ADMITDEF
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    let (lx, ly) := split t
    (x :: lx, y :: ly)
  -- /ADMITDEF

-- test_split
example : split [(1, false), (2, false)] = ([1, 2], [false, false]) := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: split
-- GRADE_THEOREM 1: test_split
-- []
-- /FULL

-- ######################################################################
-- ** Polymorphic Options

-- FULL: Our last polymorphic type for now is _polymorphic options_.
-- Lean's standard library provides `Option α`, with constructors
-- `none` and `some x`.  (We already saw `Option Nat` in the
-- previous chapter.)  Let's briefly look at the definition inside a
-- playground:

namespace OptionPlayground

inductive MyOption (α : Type) : Type where
  | none : MyOption α
  | some (x : α) : MyOption α

end OptionPlayground

-- TERSE: ***
-- FULL: We can now rewrite the `nth_error` function so that it works
-- with any type of list.  Lean calls this `List.get?`:

def nthError {α : Type} (l : List α) (n : Nat) : Option α :=
  match l with
  | [] => none
  | a :: l' => match n with
    | 0 => some a
    | n' + 1 => nthError l' n'

-- HIDEFROMADVANCED
-- test_nth_error1
example : nthError [4, 5, 6, 7] 0 = some 4 := by rfl
-- test_nth_error2
example : nthError [[1], [2]] 1 = some [2] := by rfl
-- test_nth_error3
example : nthError [true] 2 = none := by rfl

-- /HIDEFROMADVANCED
-- FULL
-- EX1? (hd_error_poly)
-- Complete the definition of a polymorphic version of the
-- `hd_error` function from the last chapter. Be sure that it
-- passes the unit tests below.

def hdError {α : Type} (l : List α) : Option α :=
  -- ADMITDEF
  match l with
  | [] => none
  | a :: _ => some a
  -- /ADMITDEF

-- Once again, to force the implicit arguments to be explicit,
-- we can use `@` before the name of the function.

#check @hdError  -- @hdError : {α : Type} → List α → Option α

-- test_hd_error1
example : hdError [1, 2] = some 1 := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: test_hd_error1
-- test_hd_error2
example : hdError [[1], [2]] = some [1] := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: test_hd_error2
-- []
-- /FULL

-- ######################################################################
-- * Functions as Data

-- HIDEFROMADVANCED
-- FULL: Like most modern programming languages -- especially other
-- "functional" languages, including OCaml, Haskell, Racket, Scala,
-- Clojure, etc. -- Lean treats functions as first-class citizens,
-- allowing them to be passed as arguments to other functions,
-- returned as results, stored in data structures, etc.

-- /HIDEFROMADVANCED

-- ######################################################################
-- ** Higher-Order Functions

-- HIDEFROMADVANCED
-- FULL: Functions that manipulate other functions are often called
-- _higher-order_ functions.  Here's a simple one:
-- TERSE: Functions in Lean are _first class_.

def doit3times {α : Type} (f : α → α) (n : α) : α :=
  f (f (f n))

-- FULL: The argument `f` here is itself a function (from `α` to
-- `α`); the body of `doit3times` applies `f` three times to some
-- value `n`.

#check @doit3times  -- @doit3times : {α : Type} → (α → α) → α → α

-- test_doit3times
example : doit3times (· - 2) 9 = 3 := by rfl

-- test_doit3times'
example : doit3times (!·) true = false := by rfl

-- ######################################################################
-- ** Filter

-- /HIDEFROMADVANCED
-- FULL: Here is a more useful higher-order function, taking a list
-- of `α`s and a _predicate_ on `α` (a function from `α` to `Bool`)
-- and "filtering" the list to yield a new list containing just
-- those elements for which the predicate returns `true`.

def filter {α : Type} (test : α → Bool) (l : List α) : List α :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: filter test t
    else filter test t

-- FULL: For example, if we apply `filter` to the predicate `Nat.even`
-- and a list of numbers, it returns a list containing just the
-- even members.

-- HIDEFROMADVANCED
-- (We use `Nat.even` from Lean's standard library, which tests
-- whether a number is even.)

-- test_filter1
example : filter (·% 2 == 0) [1, 2, 3, 4] = [2, 4] := by rfl

-- TERSE: ***
def lengthIs1 {α : Type} (l : List α) : Bool :=
  l.length == 1

-- test_filter2
example : filter lengthIs1
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

-- TERSE: ***
-- FULL: We can use `filter` to give a concise version of the
-- `countoddmembers` function from the Lists chapter.

def countoddmembers' (l : List Nat) : Nat :=
  (filter (· % 2 != 0) l).length

-- test_countoddmembers'1
example : countoddmembers' [1, 0, 3, 1, 4, 5] = 4 := by rfl
-- test_countoddmembers'2
example : countoddmembers' [0, 2, 4] = 0 := by rfl
-- test_countoddmembers'3
example : countoddmembers' [] = 0 := by rfl

-- /HIDEFROMADVANCED

-- ######################################################################
-- ** Anonymous Functions

-- FULL: It is arguably a little sad, in the example just above, to
-- be forced to define the function `lengthIs1` and give it a name
-- just to be able to pass it as an argument to `filter`, since we
-- will probably never use it again.  Indeed, when using higher-order
-- functions, we _often_ want to pass as arguments "one-off"
-- functions that we will never use again; having to give each of
-- these functions a name would be tedious.
--
-- Fortunately, there is a better way.  We can construct a function
-- "on the fly" without declaring it at the top level or giving it a
-- name.  Lean provides two syntaxes for anonymous functions:
--
-- - `fun n => n * n` -- traditional lambda syntax
-- - `(· * ·)` -- "term with holes" syntax, where `·` marks arguments
-- TERSE: Functions can be constructed "on the fly" without giving
-- them names.
-- HIDEFROMADVANCED

-- test_anon_fun'
example : doit3times (fun n => n * n) 2 = 256 := by rfl

-- The expression `fun n => n * n` can be read as "the function
-- that, given a number `n`, yields `n * n`."
--
-- Lean also supports a shorter notation using `·` as a placeholder
-- for the argument:

-- test_anon_fun''
example : doit3times (· + 1) 0 = 3 := by rfl

-- /HIDEFROMADVANCED
-- FULL: Here is the `filter` example, rewritten to use an anonymous
-- function.

-- test_filter2'
example : filter (fun l => l.length == 1)
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

-- FULL
-- EX2 (filter_even_gt7)
-- Use `filter` (instead of a recursive `def`) to write a Lean function
-- `filterEvenGt7` that takes a list of natural numbers as input
-- and returns a list of just those that are even and greater than 7.

def filterEvenGt7 (l : List Nat) : List Nat :=
  -- ADMITDEF
  filter (fun n => n % 2 == 0 && n > 7) l
  -- /ADMITDEF

-- test_filter_even_gt7_1
example : filterEvenGt7 [1, 2, 6, 9, 10, 3, 12, 8] = [10, 12, 8] := by rfl  -- ADMITTED

-- test_filter_even_gt7_2
example : filterEvenGt7 [5, 2, 6, 19, 129] = [] := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: test_filter_even_gt7_1
-- GRADE_THEOREM 1: test_filter_even_gt7_2
-- []

-- EX3 (partition)
-- Use `filter` to write a Lean function `partition` that, given a
-- type `α`, a predicate of type `α → Bool` and a `List α`, should
-- return a pair of lists.  The first member of the pair is the sublist
-- of the original list containing the elements that satisfy the test,
-- and the second is the sublist containing those that fail the test.
-- The order of elements in the two sublists should be the same as
-- their order in the original list.

def partition {α : Type} (test : α → Bool) (l : List α) : List α × List α :=
  -- ADMITDEF
  (filter test l, filter (fun x => !test x) l)
  -- /ADMITDEF

-- test_partition1
example : partition (· % 2 != 0) [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) := by rfl  -- ADMITTED
-- test_partition2
example : partition (fun _ => false) [5, 9, 0] = ([], [5, 9, 0]) := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: partition
-- GRADE_THEOREM 1: test_partition1
-- GRADE_THEOREM 1: test_partition2
-- []
-- /FULL

-- ######################################################################
-- ** Map

-- FULL: Another handy higher-order function is called `map`.

def map {α : Type} {β : Type} (f : α → β) (l : List α) : List β :=
  match l with
  | [] => []
  | h :: t => f h :: map f t

-- FULL: It takes a function `f` and a list `l = [n1, n2, n3, ...]`
-- and returns the list `[f n1, f n2, f n3, ...]`, where `f` has
-- been applied to each element of `l` in turn.  For example:

-- test_map1
example : map (· + 3) [2, 0, 2] = [5, 3, 5] := by rfl

-- HIDEFROMADVANCED
-- FULL: The element types of the input and output lists need not be
-- the same, since `map` takes _two_ type arguments, `α` and `β`; it
-- can thus be applied to a list of numbers and a function from
-- numbers to booleans to yield a list of booleans:

-- test_map2
example : map (· % 2 != 0) [2, 1, 2, 5] = [false, true, false, true] := by rfl

-- FULL: It can even be applied to a list of numbers and
-- a function from numbers to _lists_ of booleans to
-- yield a _list of lists_ of booleans:

-- test_map3
example : map (fun n => [n % 2 == 0, n % 2 != 0]) [2, 1, 2, 5]
  = [[true, false], [false, true], [true, false], [false, true]] := by rfl

-- TERSE
-- QUIZ
-- Recall the definition of `map`:
--
--     def map (f : α → β) (l : List α) : List β :=
--       match l with
--       | [] => []
--       | h :: t => f h :: map f t
--
-- What is the type of `@map`?
--
-- (A) `{α β : Type} → α → β → List α → List β`
--
-- (B) `α → β → List α → List β`
--
-- (C) `{α β : Type} → (α → β) → List α → List β`
--
-- (D) `{α : Type} → (α → α) → List α → List α`
-- /QUIZ

-- /TERSE

-- TERSE: ***
-- FULL: *** Exercises

-- FULL
-- EX3 (map_rev)
-- Show that `map` and `reverse` commute.  (Hint: You may need to
-- define an auxiliary lemma.)
-- QUIETSOLUTION

theorem map_app {α : Type} {β : Type} : ∀ (f : α → β) (l l' : List α),
  map f (l ++ l') = map f l ++ map f l' := by
  intro f l l'
  induction l
  . case nil => rfl
  . case cons h t ih => dsimp [map]; rw [ih]

-- /QUIETSOLUTION

-- map_rev
theorem map_rev {α : Type} {β : Type} : ∀ (f : α → β) (l : List α),
  map f (rev l) = rev (map f l) := by
  -- ADMITTED
  intro f l
  induction l
  . case nil => rfl
  . case cons h t ih => dsimp [map, rev]; rw [map_app, ih]; dsimp [map]
-- /ADMITTED
-- GRADE_THEOREM 3: map_rev
-- []

-- EX2! (flat_map)
-- The function `map` maps a `List α` to a `List β` using a function
-- of type `α → β`.  We can define a similar function, `flatMap`,
-- which maps a `List α` to a `List β` using a function `f` of type
-- `α → List β`.  Your definition should work by 'flattening' the
-- results of `f`, like so:
--
--     flatMap (fun n => [n, n + 1, n + 2]) [1, 5, 10]
--       = [1, 2, 3, 5, 6, 7, 10, 11, 12]

def flatMap {α : Type} {β : Type} (f : α → List β) (l : List α) : List β :=
  -- ADMITDEF
  match l with
  | [] => []
  | h :: t => f h ++ flatMap f t
  -- /ADMITDEF

-- test_flat_map1
example : flatMap (fun n => [n, n, n]) [1, 5, 4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4] := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: flatMap
-- GRADE_THEOREM 1: test_flat_map1
-- []
-- /FULL
-- HIDEFROMADVANCED

-- Lists are not the only inductive type for which `map` makes sense.
-- Here is a `map` for the `Option` type:

def optionMap {α : Type} {β : Type} (f : α → β) (xo : Option α) : Option β :=
  match xo with
  | none => none
  | some x => some (f x)

-- /HIDEFROMADVANCED
-- FULL
-- EX2? (implicit_args)
-- The definitions and uses of `filter` and `map` use implicit
-- arguments in many places.  Replace the curly braces around the
-- implicit arguments with explicit parentheses, and then fill in
-- explicit type parameters where necessary and use Lean to check that
-- you've done so correctly.  (This exercise is not to be turned in;
-- it is probably easiest to do it on a _copy_ of this file that you
-- can throw away afterwards.)
-- []
-- /FULL
-- /HIDEFROMADVANCED

-- ######################################################################
-- ** Fold

-- FULL: An even more powerful higher-order function is called
-- `fold`.  This function is the inspiration for the "reduce"
-- operation that lies at the heart of Google's map/reduce
-- distributed programming framework.

def fold {α : Type} {β : Type} (f : α → β → β) (l : List α) (b : β) : β :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)

-- TERSE: This is the "reduce" in map/reduce...

-- HIDEFROMADVANCED
-- TERSE: ***

-- FULL: Intuitively, the behavior of the `fold` operation is to
-- insert a given binary operator `f` between every pair of elements
-- in a given list.  For example, `fold (· + ·) [1, 2, 3, 4]`
-- intuitively means `1 + 2 + 3 + 4`.  To make this precise, we also
-- need a "starting element" that serves as the initial second input
-- to `f`.  So, for example,
--
--     fold (· + ·) [1, 2, 3, 4] 0
--
-- yields
--
--     1 + (2 + (3 + (4 + 0))).

-- fold_example1
example : fold (· && ·) [true, true, false, true] true = false := by rfl

-- fold_example2
example : fold (· * ·) [1, 2, 3, 4] 1 = 24 := by rfl

-- fold_example3
example : fold (· ++ ·) [[1], [], [2, 3], [4]] [] = [1, 2, 3, 4] := by rfl

-- fold_example4
example : fold (fun l n => l.length + n) [[1], [], [2, 3, 2], [4]] 0 = 5 := by rfl

-- TERSE
-- QUIZ
-- Here is the definition of `fold` again:
--
--     def fold (f : α → β → β) (l : List α) (b : β) : β :=
--       match l with
--       | [] => b
--       | h :: t => f h (fold f t b)
--
-- What is the type of `@fold`?
--
-- (A) `{α β : Type} → (α → β → β) → List α → β → β`
--
-- (B) `α → β → (α → β → β) → List α → β → β`
--
-- (C) `{α β : Type} → α → β → β → List α → β → β`
--
-- (D) `α → β → α → β → β → List α → β → β`
-- /QUIZ

-- QUIZ
-- What does `fold (· + ·) [1, 2, 3, 4] 0` simplify to?
--
-- (A) `[1, 2, 3, 4]`
--
-- (B) `0`
--
-- (C) `10`
--
-- (D) `[3, 7, 0]`
-- /QUIZ
-- /TERSE
-- /HIDEFROMADVANCED

-- FULL
-- EX1M? (fold_types_different)
-- Observe that the type of `fold` is parameterized by _two_ type
-- variables, `α` and `β`, and the parameter `f` is a binary operator
-- that takes an `α` and a `β` and returns a `β`.  Example
-- `fold_example4` above shows one instance where it is useful for `α`
-- and `β` to be different. Can you think of any others?

-- SOLUTION
-- There are many.  For example, we could use `fold` to count the
-- number of `true` elements in a list of booleans.  Here `α` would
-- be `Bool` and `β` would be `Nat`.
-- /SOLUTION
-- []
-- /FULL

-- HIDEFROMADVANCED
-- ######################################################################
-- ** Functions That Construct Functions

-- FULL: Most of the higher-order functions we have talked about so
-- far take functions as arguments.  Let's look at some examples that
-- involve _returning_ functions as the results of other functions.
-- To begin, here is a function that takes a value `x` (drawn from
-- some type `α`) and returns a function from `Nat` to `α` that
-- yields `x` whenever it is called, ignoring its `Nat` argument.
-- TERSE: Here are two functions that _return_ functions as results.

def constfun {α : Type} (x : α) : Nat → α :=
  fun _ => x

def ftrue := constfun true

-- constfun_example1
example : ftrue 0 = true := by rfl

-- constfun_example2
example : constfun 5 99 = 5 := by rfl

-- FULL: In fact, the multiple-argument functions we have already
-- seen are also examples of passing functions as data.  To see why,
-- recall the type of addition:
-- TERSE: ***
-- TERSE: A two-argument function in Lean is actually a function that
-- returns a function!

#check (Nat.add : Nat → Nat → Nat)

def plus3 := Nat.add 3
#check (plus3 : Nat → Nat)

-- test_plus3
example : plus3 4 = 7 := by rfl
-- test_plus3'
example : doit3times plus3 0 = 9 := by rfl
-- test_plus3''
example : doit3times (Nat.add 3) 0 = 9 := by rfl

-- Similarly, we can write:
def fold_plus : List Nat → Nat → Nat :=
  fold (· + ·)

#check (fold_plus : List Nat → Nat → Nat)

-- FULL: What's happening here is called _partial application_.  In
-- Lean, the type constructor `→` is right-associative, meaning a
-- function type like `α → β → γ` is parsed like `α → (β → γ)`,
-- or "a function from `α` to a function from `β` to `γ`."
--
-- We can think of `fold` not as a three-argument function, but as a
-- one-argument function that:
--
-- 1. Takes an argument `f` of type `α → β → β`
-- 2. Returns a function of type `List α → β → β` that "remembers" `f`
--
-- When we write `fold (· + ·)`, we're giving `fold` its first argument,
-- `(· + ·)`, and getting back a specialized function that can sum up
-- the elements of any list of numbers. This new function still expects
-- two more arguments: a list and a starting value.

-- FULL
-- ######################################################################
-- * Additional Exercises

namespace Exercises

-- EX2 (fold_length)
-- Many common functions on lists can be implemented in terms of
-- `fold`.  For example, here is an alternative definition of `length`:

def foldLength {α : Type} (l : List α) : Nat :=
  fold (fun _ n => n + 1) l 0

-- test_fold_length1
example : foldLength [4, 7, 0] = 3 := by rfl

-- Prove the correctness of `foldLength`.
--
-- Hint: It may help to use `simp [foldLength, fold]` to unfold
-- the definition.

-- fold_length_correct
theorem fold_length_correct {α : Type} : ∀ (l : List α),
  foldLength l = l.length := by
  -- ADMITTED
  intro l; induction l
  . case nil => rfl
  . case cons h t ih =>
      dsimp [foldLength, fold] at *
      rw [ih]
-- /ADMITTED
-- GRADE_THEOREM 2: Exercises.fold_length_correct
-- []

-- EX3M (fold_map)
-- We can also define `map` in terms of `fold`.  Finish `foldMap`
-- below.

def foldMap {α : Type} {β : Type} (f : α → β) (l : List α) : List β :=
  -- ADMITDEF
  fold (fun x l' => f x :: l') l []
  -- /ADMITDEF

-- Write down a theorem `fold_map_correct` stating that `foldMap` is
-- correct, and prove it in Lean.

-- SOLUTION
-- fold_map_correct
theorem fold_map_correct {α : Type} {β : Type} : ∀ (f : α → β) (l : List α),
  foldMap f l = map f l := by
  intro f l; induction l
  . case nil => rfl
  . case cons h t ih =>
      dsimp [foldMap, fold, map] at *
      rw [ih]
-- /SOLUTION

-- GRADE_MANUAL 3: fold_map
-- []

-- EX2A (currying)
-- The type `α → β → γ` can be read as describing functions that
-- take two arguments, one of type `α` and another of type `β`, and
-- return an output of type `γ`. Recall from our discussion
-- of partial application that this type is written `α → (β → γ)`
-- when fully parenthesized.  That is, if we have `f : α → β → γ`,
-- and we give `f` an input of type `α`, it will give us as output
-- a function of type `β → γ`.  If we then give that function an
-- input of type `β`, it will return an output of type `γ`. That
-- is, every function in Lean takes only one input, but some
-- functions return a function as output. This is precisely
-- what enables partial application, as we saw above with `plus3`.
--
-- By contrast, functions of type `α × β → γ` -- which when fully
-- parenthesized is written `(α × β) → γ` -- require their single
-- input to be a pair.  Both arguments must be given at once; there
-- is no possibility of partial application.
--
-- It is possible to convert a function between these two types.
-- Converting from `α × β → γ` to `α → β → γ` is called
-- _currying_, in honor of the logician Haskell Curry.  Converting
-- from `α → β → γ` to `α × β → γ` is called _uncurrying_.

-- We can define currying as follows:

def prodCurry {α : Type} {β : Type} {γ : Type} (f : α × β → γ) (x : α) (y : β) : γ := f (x, y)

-- As an exercise, define its inverse, `prodUncurry`.  Then prove
-- the theorems below to show that the two are really inverses.

def prodUncurry {α : Type} {β : Type} {γ : Type} (f : α → β → γ) (p : α × β) : γ :=
  -- ADMITDEF
  f p.1 p.2
  -- /ADMITDEF

-- As a (trivial) example of the usefulness of currying, we can use it
-- to shorten one of the examples that we saw above:

-- test_map1'
example : map (Nat.add 3) [2, 0, 2] = [5, 3, 5] := by rfl

-- Thought exercise: before running the following commands, can you
-- calculate the types of `prodCurry` and `prodUncurry`?

#check @prodCurry
#check @prodUncurry

-- uncurry_curry
theorem uncurry_curry {α : Type} {β : Type} {γ : Type} : ∀ (f : α → β → γ) (x : α) (y : β),
  prodCurry (prodUncurry f) x y = f x y := by
  -- ADMITTED
  intro f x y; rfl
-- /ADMITTED

-- curry_uncurry
theorem curry_uncurry {α : Type} {β : Type} {γ : Type} : ∀ (f : α × β → γ) (p : α × β),
  prodUncurry (prodCurry f) p = f p := by
  -- ADMITTED
  intro f ⟨x, y⟩; rfl
-- /ADMITTED
-- GRADE_THEOREM 1: Exercises.uncurry_curry
-- GRADE_THEOREM 1: Exercises.curry_uncurry
-- []

-- EX2AM? (nth_error_informal)
-- Recall the definition of the `nthError` function:
--
--     def nthError (l : List α) (n : Nat) : Option α :=
--       match l with
--       | [] => none
--       | a :: l' => match n with
--         | 0 => some a
--         | n' + 1 => nthError l' n'
--
-- Write a careful informal proof of the following theorem:
--
--     ∀ (l : List α) (n : Nat), l.length = n → nthError l n = none
--
-- Make sure to state the induction hypothesis _explicitly_.

-- SOLUTION
-- Theorem: For all types `α`, lists `l`, and natural numbers `n`,
-- if `l.length = n` then `nthError l n = none`.
--
-- Proof: By induction on `l`. There are two cases to consider:
--
-- - If `l = []`, we must show `nthError [] n = none`.  This follows
--   immediately from the definition of `nthError`.
--
-- - Otherwise, `l = x :: l'` for some `x` and `l'`, and the
--   induction hypothesis tells us that
--   `l'.length = n' → nthError l' n' = none`, for any `n'`.
--
--   Let `n` be the length of `l`.  We must show that
--   `nthError (x :: l') n = none`.
--
--   But we know that `n = l.length = (x :: l').length = l'.length + 1`.
--   So it's enough to show `nthError l' l'.length = none`, which
--   follows directly from the induction hypothesis, picking `l'.length`
--   for `n'`.
-- /SOLUTION

-- GRADE_MANUAL 2: informal_proof
-- []

-- ** Church Numerals (Advanced)

-- The following exercises explore an alternative way of defining
-- natural numbers using the _Church numerals_, which are named after
-- their inventor, the mathematician Alonzo Church.  We can represent
-- a natural number `n` as a function that takes a function `f` as a
-- parameter and returns `f` iterated `n` times.

namespace Church

def CNat := (α : Type) → (α → α) → α → α

-- Let's see how to write some numbers with this notation. Iterating
-- a function once should be the same as just applying it.  Thus:

def one : CNat :=
  fun (X : Type) (f : X → X) (x : X) => f x

-- Similarly, `two` should apply `f` twice to its argument:

def two : CNat :=
  fun (X : Type) (f : X → X) (x : X) => f (f x)

-- Defining `zero` is somewhat trickier: how can we "apply a function
-- zero times"?  The answer is actually simple: just return the
-- argument untouched.

def zero : CNat :=
  fun (X : Type) (_f : X → X) (x : X) => x

-- More generally, a number `n` can be written as
-- `fun X f x => f (f ... (f x) ...)`, with `n` occurrences of `f`.
-- Let's informally notate that as `fun X f x => f^n x`, with the
-- convention that `f^0 x` is just `x`. Note how the `doit3times`
-- function we've defined previously is actually just the Church
-- representation of 3.

def three : CNat := @doit3times

-- So `n X f x` represents "do it `n` times", where `n` is a Church
-- numeral and "it" means applying `f` starting with `x`.
--
-- Another way to think about the Church representation is that
-- function `f` represents the successor operation on `α`, and value
-- `x` represents the zero element of `α`.  We could even rewrite
-- with those names to make it clearer:

def zero' : CNat :=
  fun (X : Type) (_succ : X → X) (zero : X) => zero
def one' : CNat :=
  fun (X : Type) (succ : X → X) (zero : X) => succ zero
def two' : CNat :=
  fun (X : Type) (succ : X → X) (zero : X) => succ (succ zero)

-- If we passed in `Nat.succ` as `succ` and `0` as `zero`, we'd
-- even get the Peano naturals as a result:

-- zero_church_peano
example : zero Nat Nat.succ 0 = 0 := by rfl
-- one_church_peano
example : one Nat Nat.succ 0 = 1 := by rfl
-- two_church_peano
example : two Nat Nat.succ 0 = 2 := by rfl

-- One very interesting implication of the Church numerals is that we
-- don't strictly need the natural numbers to be built-in to a
-- functional programming language, or even to be definable with an
-- inductive data type. It's possible to represent them purely (if
-- not efficiently) with functions.
--
-- Of course, it's not enough just to "represent" numerals; we need
-- to be able to do arithmetic with the representation. Show that we
-- can by completing the definitions of the following functions. Make
-- sure that the corresponding unit tests pass by proving them with
-- `rfl`.

-- EX2A (church_scc)

-- Define a function that computes the successor of a Church numeral.
-- Given a Church numeral `n`, its successor `scc n` should iterate
-- its function argument once more than `n`. That is, given
-- `fun X f x => f^n x` as input, `scc` should produce
-- `fun X f x => f^(n+1) x` as output.
-- In other words, do it `n` times, then do it once more.

def scc (n : CNat) : CNat :=
  -- ADMITDEF
  fun (X : Type) (f : X → X) (x : X) => f (n X f x)
  -- /ADMITDEF

-- scc_1
example : scc zero = one := by rfl  -- ADMITTED
-- scc_2
example : scc one = two := by rfl  -- ADMITTED
-- scc_3
example : scc two = three := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: Exercises.Church.scc_2
-- GRADE_THEOREM 1: Exercises.Church.scc_3
-- []

-- EX3A (church_plus)

-- Define a function that computes the addition of two Church
-- numerals.  Given `fun X f x => f^n x` and `fun X f x => f^m x`
-- as input, `plus` should produce `fun X f x => f^(n + m) x` as
-- output.  In other words, do it `n` times, then do it `m` more times.
--
-- Hint: the "zero" argument to a Church numeral need not be just `x`.

def plus (n m : CNat) : CNat :=
  -- ADMITDEF
  fun (X : Type) (f : X → X) (x : X) => n X f (m X f x)
  -- /ADMITDEF

-- plus_1
example : plus zero one = one := by rfl  -- ADMITTED
-- plus_2
example : plus two three = plus three two := by rfl  -- ADMITTED
-- plus_3
example : plus (plus two two) three = plus one (plus three three) := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: Exercises.Church.plus_1
-- GRADE_THEOREM 1: Exercises.Church.plus_2
-- GRADE_THEOREM 1: Exercises.Church.plus_3
-- []

-- EX3A (church_mult)

-- Define a function that computes the multiplication of two Church
-- numerals.
--
-- Hint: the "successor" argument to a Church numeral need not be
-- just `f`.

def mult (n m : CNat) : CNat :=
  -- ADMITDEF
  fun (X : Type) (f : X → X) (x : X) => n X (m X f) x
  -- /ADMITDEF

-- mult_1
example : mult one one = one := by rfl  -- ADMITTED
-- mult_2
example : mult zero (plus three three) = zero := by rfl  -- ADMITTED
-- mult_3
example : mult two three = plus three three := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: Exercises.Church.mult_1
-- GRADE_THEOREM 1: Exercises.Church.mult_2
-- GRADE_THEOREM 1: Exercises.Church.mult_3
-- []

-- EX3A (church_exp)

-- Exponentiation:

-- Define a function that computes the exponentiation of two Church
-- numerals.
--
-- Hint: the type argument to a Church numeral need not just be `α`.
-- Finding the right type can be tricky.

def exp (n m : CNat) : CNat :=
  -- ADMITDEF
  fun (X : Type) (f : X → X) (x : X) => m (X → X) (n X) f x
  -- /ADMITDEF

-- exp_1
example : exp two two = plus two two := by rfl  -- ADMITTED
-- exp_2
example : exp three zero = one := by rfl  -- ADMITTED
-- exp_3
example : exp three two = plus (mult two (mult two two)) one := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: Exercises.Church.exp_1
-- GRADE_THEOREM 1: Exercises.Church.exp_2
-- GRADE_THEOREM 1: Exercises.Church.exp_3
-- []

end Church
end Exercises

-- /HIDEFROMADVANCED
-- /FULL
