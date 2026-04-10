/- Lists: Working with Structured Data -/

/- INSTRUCTORS: This file takes about 60 minutes to get through.
   Putting it together with Induction.lean makes a reasonable
   second week's homework assignment. -/

/- SOONER: (BCP 9/18) Since the domain type in Maps.v has changed from
   id to string, we should either do the same here (in the partial
   maps section) or else comment there that we are making a different
   choice.  For the moment, it feels cleaner to avoid importing the
   string library, explaining or handwaving string_dec, etc., so I've
   added a comment there. BCP 25: I wonder whether we can get away
   with just using (... =? ...)%string instead of string_dec.  Would
   make it a lot more palatable. I now think this is probably a good
   idea. However: At the moment, the Stdlib has String.eqb to compare
   strings, but it returns a standard bool, which is not the one we
   are using. We'd have to put our booleans inside a module in
   Basics.v. That's probably fine. After that, I think we just have to
   alias Definition Id := string). -/

/- SOONER: This chapter could use another WORKINCLASS or three. -/

/- HIDEFROMHTML
   FULL
   REMINDER:

          #####################################################
          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
          #####################################################

   (See the [Preface] for why.)
   /FULL
   /HIDEFROMHTML
-/

import Induction
namespace NatList

#check ([] ++ [])

-- ######################################################################
-- * Pairs of Numbers

/- FULL: In an `inductive` type definition, each constructor can take
   any number of arguments -- none (as with `true` and `0`),
   one (as with `succ`), or more than one (as with `Nybble` and
   the following): -/
/- TERSE: An inductive definition of pairs of numbers.  It has just
   one constructor, taking two arguments: -/

inductive NatProd where
  | pair (n1 n2 : Nat)

/- FULL: This declaration can be read: "The one and only way to
    construct a pair of numbers is by applying the constructor [pair]
    to two arguments of type [Nat]." -/

-- HIDEFROMADVANCED
#check (NatProd.pair 3 5)

-- TERSE:
-- /HIDEFROMADVANCED
/- Functions for extracting the first and second components of a pair
    can then be defined by pattern matching. -/

def NatProd.fst (p : NatProd) : Nat :=
  match p with
  | .pair x _ => x

def NatProd.snd (p : NatProd) : Nat :=
  match p with
  | .pair _ y => y

/- Defining these functions with the `NatProd` type name qualifying their name
   allows us to use them with `.` notation: -/

-- HIDEFROMADVANCED
example : (NatProd.pair 3 5).fst = 3 := by rfl
-- /HIDEFROMADVANCED

-- TERSE: ***

-- FULL: Since pairs will be used heavily in what follows, it will be
-- convenient to write them with angle bracket notation `⟨x, y⟩`
-- instead of `NatProd.pair x y`. Lean's anonymous constructor
-- syntax works when the expected type is known.
-- TERSE: A nicer notation for pairs:

example : (⟨3, 5⟩ : NatProd).fst = 3 := by rfl

-- The anonymous constructor can be used in both expressions and in pattern matches.
def fst' (p : NatProd) : Nat :=
  match p with
  | ⟨x,_⟩ => x

def snd' (p : NatProd) : Nat :=
  match p with
  | ⟨_,y⟩=> y

def NatProd.swap (p : NatProd) : NatProd :=
  ⟨snd p, fst p⟩

/- FULL
  Note that pattern-matching on a pair (with parentheses: [(x, y)])
  is not to be confused with the "multiple pattern" syntax (with no
  parentheses: [x, y]) that we have seen previously.  The above
  examples illustrate pattern matching on a pair with elements [x]
  and [y], whereas, for example, the definition of [sub] in
  \CHAP{Basics} performs pattern matching on the values [n] and [m]:
[[
    def sub (n m : Nat) : Nat :=
      match n, m with
      | 0,        _        => 0
      | .succ _,  0        => n
      | .succ n', .succ m' => sub n' m'
]]
    The distinction is minor, but it is worth understanding that they
    are not the same. For instance, the following definitions are
    ill-formed:
[[
      -- Can't match on a pair with multiple patterns:
      def bad_fst (p : NatProd) : Nat :=
        match p with
        | x, y => x

      -- Can't match on multiple values with pair patterns:
      def bad_sub (n m : Nat) : Nat :=
        match n, m with
        | ⟨0,        _⟩       => 0
        | ⟨.succ _,  0⟩        => n
        | ⟨.succ n', .succ m'⟩ => sub n' m'
]]
/FULL -/

/- TODO (DHS): Wrote this, let me know how it reads. -/
/- Lean also provides a convenient way to define `inductive` structures like pairs
   that have a single constructor but multiple ways to access their data,
   using the `structure` keyword. The definition of `NatProd'` below is equivalent
   to the `NatProd` definition from earlier, except that Lean automatically
   generates the `fst` and `snd` accessors. -/

structure NatProd' where
  fst : Nat
  snd : Nat

#check (NatProd'.mk 3 5)
example : (NatProd'.mk 3 5).fst = 3 := by rfl
example : (⟨3, 5⟩ : NatProd').fst = 3 := by rfl

/-
  TODO (DHS): None of this applies to Lean I believe,
  the Rocq example that doesn't work actually works just fine in Lean.
  Okay to just cut these next two entirely?

/- TERSE: ***
   If we state properties of pairs in a slightly peculiar way, we can
   sometimes complete their proofs with just reflexivity and its
   built-in simplification: -/

-- surjective_pairing'
theorem surjective_pairing' : ∀ n m : Nat,
  (⟨n, m⟩ : NatProd) = ⟨fst (⟨n, m⟩ : NatProd), snd (⟨n, m⟩ : NatProd)⟩ := by
  intro n m; rfl

-- TERSE: ***
-- But just `rfl` is not enough if we state the lemma in a more
-- natural way:

-- surjective_pairing_stuck
example : ∀ (p : NatProd),
    p = ⟨fst p, snd p⟩ := by
  intro p; rfl -/

-- TERSE: ***
/- FULL: If we want to expose the structure of a pair,
   we can do this with `cases` or by destructuring in `intro`. -/
/- TERSE: Solution: use `cases` (or destructuring). -/

-- surjective_pairing
theorem surjective_pairing : ∀ p : NatProd,
    p = ⟨p.fst, p.snd⟩ := by
  intro ⟨n, m⟩; rfl

theorem surjective_pairing_cases : ∀ p : NatProd,
    p = ⟨p.fst, p.snd⟩ := by
  intro p; cases p; rfl

/- FULL: Notice that, by contrast with the behavior of `cases` on
   `Nat`s, where it generates two subgoals, `cases` generates just
   one subgoal here.  That's because `NatProd`s can only be
   constructed in one way. -/

-- FULL
-- EX1 (snd_fst_is_swap)
-- snd_fst_is_swap
theorem snd_fst_is_swap : ∀ p : NatProd,
    (⟨p.snd, p.fst⟩ : NatProd) = p.swap := by
  -- ADMITTED
  intro ⟨n, m⟩; rfl
-- /ADMITTED
-- []

-- EX1? (fst_swap_is_snd)
-- fst_swap_is_snd
theorem fst_swap_is_snd : ∀ p : NatProd,
    p.swap.fst = p.snd := by
  -- ADMITTED
  intro ⟨n, m⟩; rfl
-- /ADMITTED
-- []
-- /FULL

-- ######################################################################
-- * Lists of Numbers

/- FULL: Generalizing the definition of pairs, we can describe the
   type of _lists_ of numbers like this: "A list is either the empty
   list or else a pair of a number and another list." -/

-- TERSE: An inductive definition of _lists_ of numbers:

inductive NatList : Type where
  | nil
  | cons (n : Nat) (l : NatList)

-- TERSE: ***
/-  FULL: As with pairs, it is convenient to write lists in familiar
    notation.  The following declarations allow us to use [::] as an
    infix [cons] operator and square brackets as an "outfix" notation
    for constructing lists. -/
-- TERSE: Some notation for lists to make our lives easier:

-- Don't worry too much about what this is doing
scoped infixr:65 (priority := high) " :: " => NatList.cons

syntax "%[" withoutPosition(term,*,? " | " term) "]" : term
macro_rules
  | `([ $elems,* ]) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Lean.TSyntax `term) : Lean.MacroM Lean.Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← ``(NatList.cons $(⟨elems.elemsAndSeps.get!Internal i⟩) $result))
    let size := elems.elemsAndSeps.size
    if size < 64 then
      expandListLit size (size % 2 == 0) (← ``(NatList.nil))
    else
      `(%[ $elems,* | NatList.nil ])


-- Now these all mean exactly the same thing:
def mylist1 : NatList := 1 :: (2 :: (3 :: []))
def mylist2 : NatList := 1 :: 2 :: 3 :: []
def mylist3 : NatList := [1, 2, 3]

/- We put our function definitions in a namespace, so we can
   define our own versions of standard list functions for practice. -/

-- TERSE: Some useful list-manipulation functions...

-- *** Repeat

/- FULL: First is the `myRepeat` function, which takes a number `n`
   and a `count` and returns a list of length `count` in which every element is `n`.
   (We use `myRepeat` because `repeat` is a reserved keyword in Lean.) -/

def myRepeat (n count : Nat) : NatList :=
  match count with
  | 0 => []
  | count' + 1 => n :: myRepeat n count'

-- Length

-- FULL: The `length` function calculates the length of a list.

def NatList.length (l : NatList) : Nat :=
  match l with
  | [] => 0
  | _ :: t => (length t) + 1

-- *** Append

-- FULL: The `app` function appends (concatenates) two lists.

def NatList.app (l1 l2 : NatList) : NatList :=
  match l1 with
  | [] => l2
  | h :: t => h :: app t l2

-- *** Type Classes and Overloading

/- FULL: In Lean, operators like `++`, `==`, and `+` are not
   hardwired to particular types.  Instead, they are defined using
   _type classes_ — a mechanism that lets us overload operations
   for different types.

   For example, `++` is defined via the `HAppend` type class.
   Any type that provides an `HAppend` instance gets to use `++`.
   Lean's built-in `List` already has such an instance (using
   `List.append`), but since we've defined our own `app` function,
   we can register it as the `++` operator within our namespace: -/

instance : HAppend NatList NatList NatList where
  hAppend := NatList.app

-- Now `l1 ++ l2` means `app l1 l2` within `NatList`.

-- test_app1
example : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5] := by rfl
-- test_app2
example : ([] : NatList) ++ [4, 5] = [4, 5] := by rfl
-- test_app3
example : [1, 2, 3] ++ ([] : NatList) = [1, 2, 3] := by rfl

/- FULL: We'll learn more about type classes as we go.  For now, the
   key idea is: a type class is an interface, and an instance is an
   implementation of that interface for a particular type.

  (For a thorough treatment of type classes, see Chapter 3 of
   _Functional Programming in Lean_.) -/

-- Some simple facts about appending lists
theorem nil_append (l : NatList) : [] ++ l = l := rfl
theorem cons_append (n : Nat) (l1 l2 : NatList) : (n::l1) ++ l2 = n::(l1 ++ l2) := rfl

-- *** Head and Tail

/- FULL: The `hd` function returns the first element (the "head") of
   the list, while `tl` returns everything but the first element (the
   "tail").  Since the empty list has no first element, we pass
   a default value to be returned in that case. -/

def NatList.hd (default : Nat) (l : NatList) : Nat :=
  match l with
  | [] => default
  | h :: _ => h

def NatList.tl (l : NatList) : NatList :=
  match l with
  | [] => []
  | _ :: t => t

-- test_hd1
example : NatList.hd 0 [1, 2, 3] = 1 := by rfl
-- test_hd2
example : NatList.hd 0 [] = 0 := by rfl
-- test_tl
example : [1, 2, 3].tl = [2, 3] := by rfl

-- QUIZ
-- What does the following function do?

def foo (n : Nat) : NatList :=
  match n with
  | 0 => []
  | n' + 1 => (n' + 1) :: foo n'
-- /QUIZ

-- FULL
-- *** Exercises

-- EX2! (list_funs)
-- Complete the definitions of `nonzeros`, `oddmembers`, and
-- `countoddmembers` below. Have a look at the tests to understand
-- what these functions should do.

def nonzeros (l : NatList) : NatList :=
  -- ADMITDEF
  match l with
  | [] => []
  | h :: t =>
      match h with
      | 0 => nonzeros t
      | _ + 1 => h :: (nonzeros t)
  -- /ADMITDEF

-- test_nonzeros
example : nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3] := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_nonzeros

def oddmembers (l : NatList) : NatList :=
  -- ADMITDEF
  match l with
  | [] => []
  | h :: t => if odd h then h :: oddmembers t else oddmembers t
  -- /ADMITDEF

-- test_oddmembers
example : oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3] := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_oddmembers

-- For the next problem, `countoddmembers`, we encourage you to implement it using
-- already-defined functions, rather than recursion.

def countoddmembers (l : NatList) : Nat :=
  -- ADMITDEF
  (oddmembers l).length
  -- /ADMITDEF

-- test_countoddmembers1
example : countoddmembers [1, 0, 3, 1, 4, 5] = 4 := by rfl  -- ADMITTED
-- test_countoddmembers2
example : countoddmembers [0, 2, 4] = 0 := by rfl  -- ADMITTED
-- test_countoddmembers3
example : countoddmembers [] = 0 := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_countoddmembers2
-- GRADE_THEOREM 0.5: NatList.test_countoddmembers3
-- []

-- EX3A (alternate)
/- Complete the following definition of `alternate`, which
  interleaves two lists into one, alternating between elements taken
  from the first list and elements from the second.

  Hint: there are natural ways of writing `alternate` that fail to
  satisfy Lean's requirement that all recursive definitions be
  _structurally recursive_, as mentioned in `"Basics"`.
  If you encounter this difficulty,
  consider pattern matching against both lists at the same time. -/

def alternate (l1 l2 : NatList) : NatList :=
  -- ADMITDEF
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
  -- /ADMITDEF

-- test_alternate1
example : alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6] := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: NatList.test_alternate1
-- test_alternate2
example : alternate [1] [4, 5, 6] = [1, 4, 5, 6] := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: NatList.test_alternate2
-- test_alternate3
example : alternate [1, 2, 3] [4] = [1, 4, 2, 3] := by rfl  -- ADMITTED
-- test_alternate4
example : alternate ([] : NatList) [20, 30] = [20, 30] := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: NatList.test_alternate4
-- []

-- ######################################################################
-- *** Bags via Lists

namespace Bag

/- A `bag` (or `multiset`) is like a set, except that each element
   can appear multiple times rather than just once.  One way of
   representing a bag of numbers is as a list. -/

abbrev Bag := NatList

-- EX3! (bag_functions)
/- Complete the following definitions for the functions `count`,
   `sum`, `add`, and `member` for bags. -/

def count (v : Nat) (s : Bag) : Nat :=
  -- ADMITDEF
  match s with
  | [] => 0
  | h :: t => if h == v then (count v t) + 1 else count v t
  -- /ADMITDEF

-- All these proofs can be completed with `rfl`.

-- test_count1
example : count 1 [1, 2, 3, 1, 4, 1] = 3 := by rfl  -- ADMITTED
-- test_count2
example : count 6 [1, 2, 3, 1, 4, 1] = 0 := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_count2

/- Multiset `sum` is similar to set `union`: `sum a b` contains all
   the elements of `a` and those of `b`.  (Mathematicians usually
   define [union] on multisets a little bit differently -- using max
   instead of sum -- which is why we don't call this operation
   [union].)

   We've deliberately given you a header that does not give explicit
   names to the arguments.  Implement [sum] in terms of an
   already-defined function, without changing the header. -/

def sum : Bag → Bag → Bag :=
  -- ADMITDEF
  NatList.app
  -- /ADMITDEF

-- test_sum1
example : count 1 (sum [1, 2, 3] [1, 4, 1]) = 3 := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_sum1

def add (v : Nat) (s : Bag) : Bag :=
  -- ADMITDEF
  v :: s
  -- /ADMITDEF

-- test_add1
example : count 1 (add 1 [1, 4, 1]) = 3 := by rfl  -- ADMITTED
-- test_add2
example : count 5 (add 1 [1, 4, 1]) = 0 := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_add1
-- GRADE_THEOREM 0.5: NatList.test_add2

def member (v : Nat) (s : Bag) : Bool :=
  -- ADMITDEF
  match s with
  | [] => false
  | h :: t => if v == h then true else member v t
  -- /ADMITDEF

-- test_member1
example : member 1 [1, 4, 1] = true := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_member1

-- test_member2
example : member 2 [1, 4, 1] = false := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_member2
-- []

-- EX3? (bag_more_functions)
-- Here are some more `bag` functions for you to practice with.

/- When `remove_one` is applied to a bag without the number to
    remove, it should return the same bag unchanged.  (This exercise
    is optional, but students following the advanced track will need
    to fill in the definition of `remove_one` for a later
    exercise.) -/
/- SOONER: BCP 25: At Penn this year, we removed the distinction
   between standard and advanced tracks, which made the wording above
   confusing. Maybe just make this an exercise for everybody? -/

def remove_one (v : Nat) (s : Bag) : Bag :=
  -- ADMITDEF
  match s with
  | [] => []
  | h :: t => if h == v then t else h :: remove_one v t
  -- /ADMITDEF

-- test_remove_one1
example : count 5 (remove_one 5 [2, 1, 5, 4, 1]) = 0 := by rfl  -- ADMITTED
-- test_remove_one2
example : count 5 (remove_one 5 [2, 1, 4, 1]) = 0 := by rfl  -- ADMITTED
-- test_remove_one3
example : count 4 (remove_one 5 [2, 1, 4, 5, 1, 4]) = 2 := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_remove_one3
-- test_remove_one4
example : count 5 (remove_one 5 [2, 1, 5, 4, 5, 1, 4]) = 1 := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_remove_one4

def remove_all (v : Nat) (s : Bag) : Bag :=
  -- ADMITDEF
  match s with
  | [] => []
  | h :: t => if h == v then remove_all v t else h :: remove_all v t
  -- /ADMITDEF

-- test_remove_all1
example : count 5 (remove_all 5 [2, 1, 5, 4, 1]) = 0 := by rfl  -- ADMITTED
-- test_remove_all2
example : count 5 (remove_all 5 [2, 1, 4, 1]) = 0 := by rfl  -- ADMITTED
-- test_remove_all3
example : count 4 (remove_all 5 [2, 1, 4, 5, 1, 4]) = 2 := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_remove_all3
-- test_remove_all4
example : count 5 (remove_all 5 [2, 1, 5, 4, 5, 1, 4, 5, 1, 4]) = 0 := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_remove_all4

def included (s1 s2 : Bag) : Bool :=
  -- ADMITDEF
  match s1 with
  | [] => true
  | h :: t => member h s2 && included t (remove_one h s2)
  -- /ADMITDEF

-- test_included1
example : included [1, 2] [2, 1, 4, 1] = true := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_included1
-- test_included2
example : included [1, 2, 2] [2, 1, 4, 1] = false := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_included2
-- []

-- EX2M? (add_inc_count)
-- Adding a value to a bag should increase the value's count by one.
-- State this as a theorem and prove it.
-- QUIETSOLUTION
theorem add_inc_count : ∀ (s : Bag) (v : Nat),
    count v (add v s) = (count v s) + 1 := by
  intro s v
  simp [add, count, eqb_refl]
-- /QUIETSOLUTION
-- GRADE_MANUAL 2: add_inc_count
-- []

end Bag

-- /FULL
-- ######################################################################
-- Reasoning About Lists

/- FULL: As with numbers, simple facts about list-processing
   functions can sometimes be proved entirely by simplification.
   For example, just `rfl` is enough for this theorem... -/
/- TERSE: As with numbers, some proofs about list functions need only
   simplification... -/

theorem nil_app : ∀ (l : NatList), ([] : NatList) ++ l = l := by
  intro l
  rfl

/- FULL: ...because the `[]` is substituted into the "scrutinee" (the
   expression whose value is being "scrutinized" by the match) in the
   definition of `app`, allowing the match itself to be simplified. -/

/- FULL: Also, as with numbers, it is sometimes helpful to perform case
   analysis on the possible shapes -- empty or non-empty -- of an
   unknown list. -/
-- TERSE: ***
-- TERSE: ...and some need case analysis.

theorem tl_length_pred : ∀ l : NatList,
    l.length.pred = l.tl.length := by
  intro l
  cases l
  . case nil => rfl
  . case cons n l' => rfl

-- FULL: Here, the `nil` case works because we've chosen to define
-- `tl [] = []`. Notice that the `cons` case introduces two names,
-- `n` and `l'`, corresponding to the fact that the `cons` constructor
-- for lists takes two arguments (the head and tail of the list it is
-- constructing).

-- Usually, though, interesting theorems about lists require
-- induction for their proofs.  We'll see how to do this next.

-- FULL
/- (Micro-Sermon: As we get deeper into this material, simply
  _reading_ proof scripts will not help you very much.  Rather, it
  is important to step through the details of each one using Lean and
  think about what each step achieves.  Otherwise it is more or less
  guaranteed that the exercises will make no sense when you get to
  them.  'Nuff said.)
  /FULL
-/

-- ######################################################################
-- ** Induction on Lists

/-
  FULL: Proofs by induction over datatypes like `NatList` are a
  little less familiar than standard natural number induction, but
  the idea is equally simple.  Each `inductive` declaration defines
  a set of data values that can be built up using the declared
  constructors. For example, a boolean can be either `true` or
  `false`; a number can be either `0` or else `succ` applied to another
  number; and a list can be either `[]` or else `::` applied to a
  number and a list.  Moreover, applications of the declared
  constructors to one another are the _only_ possible shapes that
  elements of an inductively defined set can have.

  This last fact directly gives rise to a way of reasoning about
  inductively defined sets: a number is either `0` or else it is `succ`
  applied to some _smaller_ number; a list is either `[]` or else
  it is `::` applied to some number and some _smaller_ list;
  etc.  Thus, if we have in mind some proposition `P` that mentions a
  list `l` and we want to argue that `P` holds for _all_ lists, we
  can reason as follows:

    - First, show that `P` is true of `l` when `l` is `[]`.

    - Then show that `P` is true of `l` when `l` is `n :: l'` for
      some number `n` and some smaller list `l'`, assuming that `P`
      is true for `l'`.

  Since larger lists can always be broken down into smaller ones,
  eventually reaching `[]`, these two arguments together establish
  the truth of `P` for all lists `l`.

  Here's a concrete example:
-/

/- TERSE: Lean generates an induction principle for every `inductive`
   definition, including lists.  We can use the `induction` tactic on
   lists to prove things like the associativity of list-append... -/

theorem app_assoc : ∀ l1 l2 l3 : NatList,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  intro l1 l2 l3
  induction l1
  . case nil => rfl
  . case cons n l1' ih =>
    rw [cons_append, cons_append, cons_append, ih]

-- TERSE: ***
-- TERSE: For comparison, here is an informal proof of the same theorem.

/-
 _Theorem_: For all lists `l1`, `l2`, and `l3`,
     `(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)`.

 _Proof_: By induction on `l1`.

 - First, suppose `l1 = []`.  We must show
       `([] ++ l2) ++ l3 = [] ++ (l2 ++ l3)`,
   which follows directly from the definition of `app`.

 - Next, suppose `l1 = n :: l1'`, with
       `(l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)`
   (the induction hypothesis). We must show
       `((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3)`.
   By the definition of `app`, this follows from
       `n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3))`,
   which is immediate from the induction hypothesis.  _Qed_. -/

-- Generalizing Statements

/- FULL: In some situations, it is necessary to generalize a
 statement in order to prove it by induction.  Intuitively, the
 reason is that a more general statement also yields a more general
 (stronger) inductive hypothesis. -/
/- TERSE: Sometimes statements need to be generalized to prove them
 by induction: -/

-- myRepeat_double_firsttry
example : ∀ c n : Nat,
    myRepeat n c ++ myRepeat n c = myRepeat n (add c c) := by
  intro c
  induction c
  . case zero => intro n; rfl
  . case succ c' ih =>
    intro n
    -- Now we seem to be stuck.  The IH only works for c' + c',
    -- but we need c' + (c' + 1).
    sorry

-- FULL: To get a more general inductive hypothesis, we can generalize:
-- TERSE: A generalization that gives a stronger inductive hypothesis:

theorem myRepeat_plus : ∀ c1 c2 n : Nat,
    myRepeat n c1 ++ myRepeat n c2 = myRepeat n (c1 + c2) := by
  intro c1 c2 n
  induction c1
  . case zero =>
    dsimp [myRepeat]
    rw [zero_add]; rfl
  . case succ c1' ih =>
    dsimp [myRepeat]
    rw [succ_add, cons_append, ih]
    dsimp [myRepeat]

-- *** Reversing a List

/- FULL: For a slightly more involved example of inductive proof over
  lists, suppose we use `app` to define a list-reversing function
   `rev`: -/
-- TERSE: A more interesting example of induction over lists:

def NatList.rev (l : NatList) : NatList :=
  match l with
  | [] => []
  | h :: t => rev t ++ [h]

-- test_rev1
example : [1, 2, 3].rev = [3, 2, 1] := by rfl
-- test_rev2
example : ([] : NatList).rev = [] := by rfl

-- FULL: For something a bit more challenging, let's prove that
-- reversing a list does not change its length.  Our first attempt
-- gets stuck in the successor case...
-- TERSE: ***
-- TERSE: Let's try to prove `length (rev l) = length l`.

-- rev_length_firsttry
example : ∀ l : NatList,
    l.rev.length = l.length := by
  intro l
  induction l
  . case nil => rfl
  . case cons n l' ih =>
    dsimp [NatList.rev]
    -- Now we seem to be stuck: the goal involves `++`, but we
    -- but we don't have any useful equations
    -- in either the immediate context or in the global
    -- environment!
    sorry

/- FULL: A first attempt to make progress would be to prove exactly
    the statement that we are missing at this point.  But this attempt
    will fail because the inductive hypothesis is not general enough. -/
-- app_rev_length_S_firsttry
example : ∀ (l : NatList) n,
  (l.rev ++ [n]).length = .succ l.rev.length := by

  intro l n
  induction l
  . case nil =>
      dsimp [NatList.rev, NatList.length]
      rw [nil_app]
      dsimp [NatList.length]
  . case cons n l' ih =>
      dsimp [NatList.rev, NatList.length]
      -- ih not applicable
      sorry

/- FULL: It turns out that the above lemma is more specific than it
   needs to be. We can strengthen the lemma to work not only on reversed
   lists but on general lists. -/
theorem app_length_succ : ∀ (l : NatList) (n : Nat),
  (l ++ [n]).length = l.length + 1 := by
  intro l n
  induction l
  . case nil => rfl
  . case cons m l' ih =>
    rw [cons_append]
    dsimp [NatList.length]
    rw [ih]

-- TERSE: ***
-- Now we can prove the main theorem.

theorem rev_length : ∀ l : NatList,
    l.rev.length = l.length := by
  intro l
  induction l
  . case nil => rfl
  . case cons n l' ih =>
    dsimp [NatList.rev, NatList.length]
    rw [app_length_succ, ih]

-- TERSE: ***
-- FULL: We can also prove a more general form that gives the
-- length of any two appended lists.

-- app_length
theorem app_length : ∀ l1 l2 : List Nat,
  (l1 ++ l2).length = l1.length + l2.length := by
  -- WORKINCLASS
  intro l1 l2
  induction l1
  . case nil => dsimp; rw [zero_add]
  . case cons n l1' ih => dsimp; rw [ih, succ_add]
-- /WORKINCLASS

-- HIDEFROMADVANCED
-- TERSE
-- QUIZ
/- To prove the following theorem, which tactics will we need besides
    `intro`, `dsimp`, `rw`, and `rfl`?  (A) none,
    (B) `cases`, (C) `induction` on `n`, (D) `induction` on `l`, or
    (E) can't be done with the tactics we've seen.

      theorem foo1 : forall n:Nat, forall l:NatList,
        myRepeat n 0 = l -> l.length = 0 -/

-- HIDE
theorem foo1 : forall n : Nat, forall l : NatList,
    myRepeat n 0 = l -> l.length = 0 := by
  intro n l H
  rw [←H]
  rfl
-- /HIDE
-- /QUIZ

-- QUIZ --
/- What about the next one?

      theorem foo2 :  forall n m : Nat,
        (myRepeat n m).length = m

    Which tactics do we need besides [intro], [dsimp], [rw], and
    [rfl]?  (A) none, (B) [cases], (C) [induction on n],
    (D) [induction on m], or (E) can't be done with the tactics we've
    seen.
-/

-- HIDE
theorem foo2 :  forall n m : Nat,
        (myRepeat n m).length = m := by
  intro n m
  induction m
  . case zero => rfl
  . case succ m' ih =>
      dsimp [NatList.length, myRepeat] at *
      rw [ih]
-- /HIDE
-- /QUIZ

-- FULL --
/- For comparison, here are informal proofs of these two theorems:

    _Theorem_: For all lists [l1] and [l2],
       [(l1 ++ l2).length = l1.length + l2.length].

    _Proof_: By induction on [l1].

    - First, suppose [l1 = []].  We must show
[[
        ([] ++ l2).length = [].length + l2.length,
]]
      which follows directly from the definitions of [length],
      [++], and [add].

    - Next, suppose [l1 = n::l1'], with
[[
        (l1' ++ l2).length = l1'.length + l2.length
]]
      We must show
[[
       ((n::l1') ++ l2).length = (n::l1').length + l2.length.
]]
      This follows directly from the definitions of [length] and [++]
      together with the induction hypothesis. [] *)

(** _Theorem_: For all lists [l],  l.rev.length = l.length

    _Proof_: By induction on [l].

      - First, suppose [l = []].  We must show
[[
          [].rev.length = [].length
]]
        which follows directly from the definitions of [length]
        and [rev].

      - Next, suppose [l = n::l'], with
[[
          l'.rev.length = l'.length
]]
        We must show
[[
          (n :: l').rev.length = (n :: l').length
]]
        By the definition of [rev], this follows from
[[
          (l'.rev ++ [n]).length = .succ (l'.length)
]]
        which, by the previous lemma, is the same as
[[
          l'.rev.length + [n].length = .succ (l'.length)
]]
        This follows directly from the induction hypothesis and the
        definition of [length]. [] -/

/- The style of these proofs is rather longwinded and pedantic.
    After reading a couple like this, we might find it easier to
    follow proofs that give fewer details (which we can easily work
    out in our own minds or on scratch paper if necessary) and just
    highlight the non-obvious steps.  In this more compressed style,
    the above proof might look like this: -/

/- _Theorem_: For all lists [l], [l.rev.length = l.length].

    _Proof_: First observe, by a straightforward induction on [l],
     that [(l ++ [n].length = .succ l.length] for any [l].  The main
     property then follows by another induction on [l], using the
     observation together with the induction hypothesis in the case
     where [l = n'::l']. _Qed_ -/

/- Which style is preferable in a given situation depends on
    the sophistication of the expected audience and how similar the
    proof at hand is to ones that they will already be familiar with.
    The more pedantic style is a good default for our present purposes
    because we're trying to be ultra-clear about the details. -/
-- /FULL

-- FULL
-- ######################################################################
-- ** Search

-- We've seen that proofs can make use of other theorems we've
-- already proved, e.g., using `rw`.  But in order to refer to a
-- theorem, we need to know its name!
--
-- In Lean, the `exact?` tactic will search for a lemma that closes
-- the current goal.  The `#check` command shows the type of a named
-- theorem.  You can also use `example` with `exact?` to search for
-- lemmas matching a particular pattern.
--
-- Your IDE likely has its own search functionality too.  In VS Code
-- with the Lean 4 extension, you can use Ctrl+T to search for
-- definitions by name.
-- /FULL

-- FULL
-- ######################################################################
-- ** List Exercises, Part 1

-- EX3 (list_exercises)
-- More practice with lists:

theorem app_nil_r : ∀ l : NatList,
    l ++ ([] : NatList) = l := by
  -- ADMITTED
  intro l
  induction l
  . case nil => rfl
  . case cons n l' ih =>
    rw [cons_append, ih]
-- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.app_nil_r

theorem rev_app_distr : ∀ l1 l2 : NatList,
   (l1 ++ l2).rev = l2.rev ++ l1.rev := by
  -- ADMITTED
  intro l1 l2
  induction l1
  . case nil =>
      dsimp [NatList.rev]
      rw [app_nil_r, nil_app]
  . case cons x l1' ih =>
      rw [cons_append]
      dsimp [NatList.rev]
      rw [ih, app_assoc]
-- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.rev_app_distr

-- An _involution_ is a function that is its own inverse. That is,
-- applying the function twice yields the original input.
theorem rev_involutive : ∀ l : NatList,
    l.rev.rev = l := by
  -- ADMITTED
  intro l
  induction l
  . case nil => rfl
  . case cons n l' ih =>
      dsimp [NatList.rev]
      rw [rev_app_distr, ih]
      rfl
-- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.rev_involutive

-- There is a short solution to the next one.  If you find yourself
-- getting tangled up, step back and try to look for a simpler way.

theorem app_assoc4 : ∀ l1 l2 l3 l4 : NatList,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4 := by
  -- ADMITTED
  intro l1 l2 l3 l4
  rw [app_assoc, app_assoc]
-- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.app_assoc4

-- An exercise about your implementation of `nonzeros`:

-- nonzeros_app
theorem nonzeros_app : ∀ l1 l2 : NatList,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2) := by
  -- ADMITTED
  intro l1 l2
  induction l1
  . case nil => rfl
  . case cons n l1' ih =>
    cases n
    . case zero => dsimp [nonzeros, cons_append]; rw [ih]
    . case succ n' => dsimp [nonzeros, cons_append]; rw [ih]


-- /ADMITTED
-- GRADE_THEOREM 1: NatList.nonzeros_app
-- []

-- EX2 (eqblist)
-- GRADE_THEOREM 2: NatList.eqblist_refl
-- Fill in the definition of `eqblist`, which compares
-- lists of numbers for equality.  Prove that `eqblist l l`
-- yields `true` for every list `l`.

def eqblist (l1 l2 : NatList) : Bool :=
  -- ADMITDEF
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => (h1 == h2) && eqblist t1 t2
  | _, _ => false
  -- /ADMITDEF

-- test_eqblist1
example : eqblist [] [] = true := by rfl  -- ADMITTED
-- test_eqblist2
example : eqblist [1, 2, 3] [1, 2, 3] = true := by rfl  -- ADMITTED
-- test_eqblist3
example : eqblist [1, 2, 3] [1, 2, 4] = false := by rfl  -- ADMITTED

-- eqblist_refl
theorem eqblist_refl : ∀ l : NatList,
    eqblist l l = true := by
  -- ADMITTED
  intro l
  induction l
  . case nil => rfl
  . case cons n l' ih =>
    dsimp [eqblist, ih]
    rw [eqb_refl, ih]
    rfl
-- /ADMITTED
-- []

-- FULL: ** Deriving Type Class Instances
--
-- Writing `eqblist` by hand was instructive, but tedious.  In fact,
-- Lean can generate boolean equality functions automatically for any
-- inductively defined type using the `deriving` mechanism.
--
-- Writing `deriving BEq` after a type definition asks Lean to
-- generate a `BEq` instance — exactly the kind of recursive equality
-- function you just wrote.  For example, if we had defined our own
-- list type:
--
--     inductive MyList where
--       | nil
--       | cons (hd : Nat) (tl : MyList)
--       deriving BEq
--
-- then `==` would automatically work on `MyList` values.  Since we're
-- using Lean's built-in `List Nat`, which already derives `BEq`, we
-- get `==` for free.  (We'll see more uses of `deriving` in later
-- chapters.)
-- /FULL

-- ######################################################################
-- ** List Exercises, Part 2

open Bag

-- Here are a couple of little theorems to prove about your
-- definitions about bags above.

-- EX1 (count_member_nonzero)
-- count_member_nonzero
theorem count_member_nonzero : ∀ s : Bag,
    Nat.ble 1 (count 1 (1 :: s)) = true := by
  -- ADMITTED
  intro s; rfl
-- /ADMITTED
-- []

-- The following lemma about `Nat.ble` might help you in the next
-- exercise (it will also be useful in later chapters).

theorem leb_n_Sn : ∀ n : Nat,
    Nat.ble n (n + 1) = true := by
  intro n
  induction n
  . case zero => rfl
  . case succ n' ih => dsimp [Nat.ble]; exact ih

-- Before doing the next exercise, make sure you've filled in the
-- definition of `remove_one` above.
-- EX3A (remove_does_not_increase_count)

theorem remove_does_not_increase_count : ∀ s : Bag,
    Nat.ble (count 0 (remove_one 0 s)) (count 0 s) = true := by
  -- ADMITTED
  intro s
  induction s
  . case nil => rfl
  . case cons n s' ih =>
    cases n
    . case zero =>
      dsimp [remove_one, count]
      apply leb_n_Sn
    . case succ n' =>
      dsimp [remove_one, count, ih]; exact ih
-- /ADMITTED
-- []

-- EX3M? (bag_count_sum)
-- Write down an interesting theorem `bag_count_sum` about bags
-- involving the functions `count` and `sum`, and prove it.
-- (You may find that the difficulty of the proof depends on how you defined `count`!
-- SOLUTION
theorem bag_count_sum : ∀ (s1 s2 : Bag) (v : Nat),
    count v (sum s1 s2) = (count v s1) + (count v s2) := by
  intro s1 s2 v
  unfold sum
  induction s1
  . case nil =>
    dsimp [NatList.app, count]
    rw [zero_add]
  . case cons h s1' ih =>
    dsimp [NatList.app, count]
    cases (h == v)
    . case false =>
      dsimp [succ_add]; exact ih
    . case true =>
      dsimp
      rw [succ_add, ←ih]
-- /SOLUTION
-- []

-- EX3A (involution_injective)
-- Prove that every involution is injective.
--
-- Involutions were defined above in `rev_involutive`. An _injective_
-- function is one-to-one: it maps distinct inputs to distinct
-- outputs, without any collisions.

theorem involution_injective : ∀ f : Nat → Nat,
    (∀ n : Nat, n = f (f n)) →
    (∀ n1 n2 : Nat, f n1 = f n2 → n1 = n2) := by
  -- ADMITTED
  intro f hinv n1 n2 heq
  rw [hinv n1, hinv n2, heq]
-- /ADMITTED
-- []

-- EX2A (rev_injective)
-- Prove that `rev` is injective. Do not prove this by induction --
-- that would be hard. Instead, re-use the same proof technique that
-- you used for `involution_injective`. (But: Don't try to use that
-- exercise directly as a lemma: the types are not the same!)

theorem rev_injective : ∀ l1 l2 : NatList,
  l1.rev = l2.rev → l1 = l2 := by
  -- ADMITTED
  intro l1 l2 heq
  rw [← rev_involutive l1, ← rev_involutive l2, heq]
-- /ADMITTED
-- []

-- /FULL
-- ######################################################################
-- * Options

-- FULL: Suppose we want to write a function that returns the `n`th
-- element of some list.  If we give it type `NatList → Nat → Nat`,
-- then we'll have to choose some number to return when the list is
-- too short...
-- TERSE: Suppose we'd like a function to retrieve the `n`th element
--     of a list.  What to do if the list is too short?

def nth_bad (l : NatList) (n : Nat) : Nat :=
  match l with
  | [] => 42
  | a :: l' => match n with
    | 0 => a
    | n' + 1 => nth_bad l' n'

-- TERSE: ***
-- FULL: This solution is not so good: If `nth_bad` returns 42, we
-- don't know whether that value actually appears in the input or
-- whether we gave bad arguments.  A better alternative is to change
-- the return type to include an error value as a possible outcome.
-- We call this new type `NatOption`.

-- TERSE: The solution: return an `NatOption`.

inductive NatOption : Type where
  | some (n : Nat)
  | none


/- FULL: We can then change the above definition of [nth_bad] to
    return [none] when the list is too short and [some a] when the
    list has enough members and [a] appears at position [n]. We call
    this new function [nth_error] to indicate that it may result in an
    error. -/

def nth_error (l : NatList) (n : Nat) : NatOption :=
  match l with
  | [] => .none
  | a :: l' => match n with
    | 0 => .some a
    | n' + 1 => nth_error l' n'

-- test_nth_error1
example : nth_error [4, 5, 6, 7] 0 = .some 4 := by rfl
-- test_nth_error2
example : nth_error [4, 5, 6, 7] 3 = .some 7 := by rfl
-- test_nth_error3
example : nth_error [4, 5, 6, 7] 9 = .none := by rfl

-- FULL

-- The function below pulls the `Nat` out of an `NatOption`,
-- returning a supplied default in the `none` case.

def option_elim (d : Nat) (o : NatOption) : Nat :=
  match o with
  | .some n => n
  | .none => d

-- EX2 (hd_error)
-- Using the same idea, fix the `hd` function from earlier so we
-- don't have to pass a default element for the `nil` case.

def hd_error (l : NatList) : NatOption :=
  -- ADMITDEF
  match l with
  | [] => .none
  | h :: _ => .some h
  -- /ADMITDEF

-- test_hd_error1
example : hd_error ([] : NatList) = .none := by rfl  -- ADMITTED
-- test_hd_error2
example : hd_error [1] = .some 1 := by rfl  -- ADMITTED
-- test_hd_error3
example : hd_error [5, 6] = .some 5 := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: test_hd_error1
-- GRADE_THEOREM 1: test_hd_error2
-- []

-- EX1? (option_elim_hd)
-- GRADE_THEOREM 1: NatList.option_elim_hd
-- This exercise relates your new `hd_error` to the old `hd`.

-- option_elim_hd
theorem option_elim_hd : ∀ (l : NatList) (default : Nat),
    NatList.hd default l = option_elim default (hd_error l) := by
  -- ADMITTED
  intro l default
  cases l
  . case nil => rfl
  . case cons n l' => rfl
-- /ADMITTED
-- []

-- /FULL
end NatList

-- HIDE
/- SOONER: NDS
   We would like to properly introduce the fact that multiple induction
   hypotheses may be available. We will be experimenting with introducing
   it in [IndProp.v], but if it turns out to be unsatisfactory, we may want
   to reconsider introducing this concept here. -/
/--/ Demonstrates the fact that, when a type has multiple
    sub-components (children?"smaller instances"?recursive instances?),
    then one gets one induction hypothesis per component, and that these
    get introduced right after said component (instead of all at the end). -/

inductive BinTree where
| leaf (n: Nat)
| fork (l: BinTree) (r: BinTree)

def mirror(t: BinTree): BinTree :=
  match t with
  | .leaf v => .leaf v
  | .fork l r => .fork (mirror r) (mirror l)

theorem mirror_involutive: forall t, t = mirror (mirror t) := by
  intro t
  induction t
  case leaf => dsimp [mirror]
  case fork l r ihl ihr =>
    dsimp [mirror]
    rw [←ihl, ←ihr]

def size (t: BinTree): Nat :=
  match t with
  | .leaf _ => 1
  | .fork l r => 1 + size l + size r

theorem mirror_size: forall t, size t = size (mirror t) := by
  intro t
  induction t
  case leaf => dsimp [size, mirror]
  case fork l r ihl ihr =>
    dsimp [size, mirror]
    rw [←ihl, ←ihr]
    have h: size l + size r = size r + size l := by
      rw [Nat.add_comm]
    rw [Nat.add_assoc, Nat.add_assoc, h]

-- /HIDE

-- ######################################################################
-- * Partial Maps

-- As a final illustration of how data structures can be defined in
-- Lean, here is a simple _partial map_ data type, analogous to the
-- map or dictionary data structures found in most programming
-- languages.

-- First, we define a new type `MyId` to serve as the "keys" of our
-- partial maps.

structure MyId where
  val : Nat

-- Internally, a `MyId` is just a number.  Introducing a separate type
-- by wrapping each `Nat` makes definitions more readable and gives us
-- flexibility to change representations later if we want to.

-- TERSE: ***
-- We'll also need an equality test for `MyId`s:

def eqb_id (x1 x2 : MyId) : Bool :=
  beq x1.val x2.val

-- EX1 (eqb_id_refl)
-- GRADE_THEOREM 1: eqb_id_refl
-- eqb_id_refl
theorem eqb_id_refl : ∀ x : MyId, eqb_id x x = true := by
  -- ADMITTED
  intro ⟨n⟩
  dsimp [eqb_id]
  apply eqb_refl
-- /ADMITTED
-- []

-- TERSE: ***
-- Now we define the type of partial maps:

namespace PartialMap

open NatList

inductive PartialMap : Type where
  | empty : PartialMap
  | record (i : MyId) (v : Nat) (m : PartialMap) : PartialMap

open PartialMap

-- FULL
-- This declaration can be read: "There are two ways to construct a
-- `PartialMap`: either using the constructor `empty` to represent an
-- empty partial map, or applying the constructor `record` to
-- a key, a value, and an existing `PartialMap` to construct a
-- `PartialMap` with an additional key-to-value mapping."
-- /FULL

-- TERSE: ***
-- The `update` function overrides the entry for a given key in a
-- partial map by shadowing it with a new one (or simply adds a new
-- entry if the given key is not already present).

def update (d : PartialMap) (x : MyId) (value : Nat) : PartialMap :=
  record x value d

-- FULL
-- Last, the `find` function searches a `PartialMap` for a given
-- key.  It returns `none` if the key was not found and `some val` if
-- the key was associated with `val`. If the same key is mapped to
-- multiple values, `find` will return the first one it encounters.
-- /FULL
-- TERSE: ***
-- TERSE: We can define functions on `PartialMap`s by pattern matching.

def find (x : MyId) (d : PartialMap) : Option Nat :=
  match d with
  | empty => none
  | record y v d' =>
    if eqb_id x y then some v
    else find x d'

-- QUIZ
-- Is the following claim true or false?

-- quiz1
theorem quiz1 : ∀ (d : PartialMap) (x : MyId) (v : Nat),
    find x (update d x v) = some v := by
  intro d x v
  dsimp [update, find]
  rw [eqb_id_refl]
  dsimp

-- (A) True
-- (B) False
-- (C) Not sure
-- /QUIZ

-- QUIZ
-- Is the following claim true or false?

-- quiz2
theorem quiz2 : ∀ (d : PartialMap) (x y : MyId) (o : Nat),
    eqb_id x y = false →
    find x (update d y o) = find x d := by
  intro d x y o h
  dsimp [update, find]
  rw [h]
  dsimp

-- (A) True
-- (B) False
-- (C) Not sure
-- /QUIZ

-- FULL
-- EX1 (update_eq)
-- GRADE_THEOREM 1: PartialMap.update_eq
-- update_eq
theorem update_eq : ∀ (d : PartialMap) (x : MyId) (v : Nat),
    find x (update d x v) = some v := by
  -- ADMITTED
  intro d x v
  dsimp [update, find]
  rw [eqb_id_refl]
  dsimp
-- /ADMITTED
-- []

-- EX1 (update_neq)
-- GRADE_THEOREM 1: PartialMap.update_neq
-- update_neq
theorem update_neq : ∀ (d : PartialMap) (x y : MyId) (o : Nat),
    eqb_id x y = false → find x (update d y o) = find x d := by
  -- ADMITTED
  intro d x y o h
  dsimp [update, find]
  rw [h]
  dsimp
-- /ADMITTED
-- []
-- /FULL

end PartialMap
