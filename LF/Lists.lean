-- Note that rewrite laws should sometimes differ from pattern matching now

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

import LF.Induction
import LF.UsingLean
namespace NatList

#check ([] ++ [])

-- ######################################################################
-- # Pairs of Numbers

/- FULL: In an `inductive` type definition, each constructor can take
   any number of arguments -- none (as with `true` and `0`),
   one (as with `succ`), or more than one (as with `Nibble` and
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
-- instead of `NatProd.pair x y`.  This notation is built into Lean, and is called
-- "anonymous constructor syntax".  It is available for any inductive type with a single constructor,
-- as long the expected type is declared or can be inferred from the context.
-- TERSE: A nicer notation for pairs:

example : (⟨3, 5⟩ : NatProd).fst = 3 := by rfl

-- The anonymous constructor can be used in both expressions and in pattern matches.
def fst' (p : NatProd) : Nat :=
  match p with
  | ⟨x, _⟩ => x

def snd' (p : NatProd) : Nat :=
  match p with
  | ⟨_, y⟩ => y

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

theorem surjective_pairing_cases (p : NatProd) :
    p = ⟨p.fst, p.snd⟩ := by
  cases p; rfl

/- FULL: Notice that, by contrast with the behavior of `cases` on
   `Nat`s, where it generates two subgoals, `cases` generates just
   one subgoal here.  That's because `NatProd`s can only be
   constructed in one way. -/

-- FULL
-- EX1 (snd_fst_is_swap)
-- snd_fst_is_swap
theorem snd_fst_is_swap (p : NatProd) :
    (⟨p.snd, p.fst⟩ : NatProd) = p.swap := by
  -- ADMITTED
  cases p; rfl
-- /ADMITTED
-- []

-- EX1? (fst_swap_is_snd)
-- fst_swap_is_snd
theorem fst_swap_is_snd (p : NatProd) :
    p.swap.fst = p.snd := by
  -- ADMITTED
  cases p; rfl
-- /ADMITTED
-- []
-- /FULL

-- ######################################################################
-- # Lists of Numbers

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
scoped infixr:65 " :: " => NatList.cons
macro (priority := high) "[ " elems:term,* "]" : term => do
  elems.getElems.foldrM (``(NatList.cons $(⟨·⟩) $(⟨·⟩))) (← ``(NatList.nil))

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

@[irreducible]
def NatList.myRepeat (n count : Nat) : NatList :=
  match count with
  | 0 => []
  | count' + 1 => n :: myRepeat n count'

-- Some simple facts about repetition
unseal NatList.myRepeat in
theorem repeat_zero v : NatList.myRepeat v 0 = [] := rfl

unseal NatList.myRepeat in
theorem repeat_succ v count : NatList.myRepeat v (count + 1) = v :: NatList.myRepeat v count := rfl

-- Length

-- FULL: The `length` function calculates the length of a list.

@[irreducible]
def NatList.length (l : NatList) : Nat :=
  match l with
  | [] => 0
  | _ :: t => (length t) + 1

-- Some simple facts about list lengths
unseal NatList.length in
theorem nil_length : [].length = 0 := rfl

unseal NatList.length in
theorem cons_length (n : Nat) (l : NatList) : (n::l).length = l.length + 1 := rfl

-- *** Append

-- FULL: The `app` function appends (concatenates) two lists.
@[irreducible]
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

-- Some simple facts about appending lists
unseal NatList.app in
theorem nil_append (l : NatList) : [] ++ l = l := rfl

unseal NatList.app in
theorem cons_append (n : Nat) (l1 l2 : NatList) : (n::l1) ++ l2 = n :: (l1 ++ l2) := rfl

-- test_app1
unseal NatList.app
example : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5] := by rfl
-- test_app2
example : ([] : NatList) ++ [4, 5] = [4, 5] := by rfl
-- test_app3
example : [1, 2, 3] ++ ([] : NatList) = [1, 2, 3] := by rfl
seal NatList.app
/- FULL: We'll learn more about type classes as we go.  For now, the
   key idea is: a type class is an interface, and an instance is an
   implementation of that interface for a particular type.

  (For a thorough treatment of type classes, see Chapter 3 of
   _Functional Programming in Lean_.) -/
/- TODO (DHS) : Should we replace the above with a forward link to our typeclasses chapter,
  once we have one? -/

-- *** Head and Tail

/- FULL: The `hd` function returns the first element (the "head") of
   the list, while `tl` returns everything but the first element (the
   "tail").  Since the empty list has no first element, we pass
   a default value to be returned in that case. -/
@[irreducible]
def NatList.hd (default : Nat) (l : NatList) : Nat :=
  match l with
  | [] => default
  | h :: _ => h

-- Basic theorems about how `hd` behaves:
unseal NatList.hd in
theorem hd_cons h x (t : NatList) : (h :: t).hd x = h := by rfl
unseal NatList.hd in
theorem hd_nil x : [].hd x = x := by rfl

@[irreducible]
def NatList.tl (l : NatList) : NatList :=
  match l with
  | [] => []
  | _ :: t => t

-- Basic theorems about how `tl` behaves:
unseal NatList.tl in
theorem tl_cons h (t : NatList) : (h :: t).tl = t := by rfl
unseal NatList.tl in
theorem tl_nil : [].tl = [] := by rfl

-- test_hd1
example : NatList.hd 0 [1, 2, 3] = 1 := by rw [hd_cons]
-- test_hd2
example : NatList.hd 0 [] = 0 := by rw [hd_nil]
-- test_tl
example : [1, 2, 3].tl = [2, 3] := by rw [tl_cons]

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

@[irreducible]
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
unseal nonzeros in
example : nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3] := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_nonzeros

-- the following lemmas should hold about your definition
unseal nonzeros
theorem nonzeros_cons_zero (t : NatList) :
  nonzeros (0 :: t) = nonzeros t := by rfl -- ADMITTED
theorem nonzeros_nil :
  nonzeros [] = [] := by rfl -- ADMITTED
theorem nonzeros_cons_nonzero h (t : NatList) :
  nonzeros ((h + 1) :: t) = (h + 1) :: nonzeros t := by rfl -- ADMITTED
seal nonzeros

@[irreducible]
def oddmembers (l : NatList) : NatList :=
  -- ADMITDEF
  match l with
  | [] => []
  | h :: t => bif odd h then h :: oddmembers t else oddmembers t
  -- /ADMITDEF

-- test_oddmembers
unseal oddmembers in
example : oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3] := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_oddmembers

-- For the next problem, `countoddmembers`, we encourage you to implement it using
-- already-defined functions, rather than recursion.
abbrev countoddmembers (l : NatList) : Nat :=
  -- ADMITDEF
  (oddmembers l).length
  -- /ADMITDEF

-- test_countoddmembers1
unseal oddmembers NatList.length
example : countoddmembers [1, 0, 3, 1, 4, 5] = 4 := by rfl  -- ADMITTED
-- test_countoddmembers2
example : countoddmembers [0, 2, 4] = 0 := by rfl  -- ADMITTED
-- test_countoddmembers3
example : countoddmembers [] = 0 := by rfl  -- ADMITTED
seal oddmembers NatList.length
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
@[irreducible]
def alternate (l1 l2 : NatList) : NatList :=
  -- ADMITDEF
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
  -- /ADMITDEF

unseal alternate
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
seal alternate
-- GRADE_THEOREM 1: NatList.test_alternate4
-- []

-- ######################################################################
-- ## Bags via Lists

namespace Bag

/- A `bag` (or `multiset`) is like a set, except that each element
   can appear multiple times rather than just once.  One way of
   representing a bag of numbers is as a list.  The following definition introduces a new name,
   `Bag`, as an abbreviation for `NatList`. -/

abbrev Bag := NatList

-- EX3! (bag_functions)
/- Complete the following definitions for the functions `count`,
   `sum`, `add`, and `member` for bags. -/

@[irreducible]
def count (v : Nat) (s : Bag) : Nat :=
  -- ADMITDEF
  match s with
  | [] => 0
  | h :: t => bif h == v then (count v t) + 1 else count v t
  -- /ADMITDEF

-- These lemmas should hold about your definition
unseal count in
theorem count_nil x  : count x [] = 0 := by rfl -- ADMITTED

unseal count in
theorem count_cons_same x y l : (y == x) = true → count x (y :: l) = count x l + 1 := by
  -- ADMITTED
  intro h
  dsimp [count]
  rw [h]
  dsimp
  -- /ADMITTED

unseal count in
theorem count_cons_diff x y l : (y == x) = false → count x (y :: l) = count x l := by
  -- ADMITTED
  intro h
  dsimp [count]
  rw [h]
  dsimp
  -- /ADMITTED

-- All these proofs can be completed with `rfl`.

-- test_count1
unseal count
example : count 1 [1, 2, 3, 1, 4, 1] = 3 := by rfl  -- ADMITTED
-- test_count2
example : count 6 [1, 2, 3, 1, 4, 1] = 0 := by rfl  -- ADMITTED
seal count
-- GRADE_THEOREM 0.5: NatList.test_count2

/- Multiset `sum` is similar to set `union`: `sum a b` contains all
   the elements of `a` and those of `b`.  (Mathematicians usually
   define [union] on multisets a little bit differently -- using max
   instead of sum -- which is why we don't call this operation
   [union].)

   We've deliberately given you a header that does not give explicit
   names to the arguments.  Implement [sum] in terms of an
   already-defined function, without changing the header. -/

abbrev sum : Bag → Bag → Bag :=
  -- ADMITDEF
  NatList.app
  -- /ADMITDEF

-- test_sum1
unseal count in
unseal NatList.app in
example : count 1 (sum [1, 2, 3] [1, 4, 1]) = 3 := by rfl -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_sum1

unseal NatList.app in
theorem nil_sum (l : NatList) : sum [] l = l := rfl

unseal NatList.app in
theorem cons_sum (n : Nat) (l1 l2 : Bag) : sum (n::l1) l2 = n :: (sum l1 l2) := rfl

abbrev add (v : Nat) (s : Bag) : Bag :=
  -- ADMITDEF
  v :: s
  -- /ADMITDEF

-- test_add1
example : count 1 (add 1 [1, 4, 1]) = 3 := by
  -- ADMITTED
  dsimp [add]
  rw [count_cons_same, count_cons_same, count_cons_diff, count_cons_same, count_nil]
  dsimp; dsimp; dsimp; dsimp
  -- /ADMITTED
-- test_add2
example : count 5 (add 1 [1, 4, 1]) = 0 := by
  -- ADMITTED
  dsimp [add]
  rw [count_cons_diff, count_cons_diff, count_cons_diff, count_cons_diff, count_nil]
  dsimp; dsimp; dsimp; dsimp
  -- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_add1
-- GRADE_THEOREM 0.5: NatList.test_add2

@[irreducible]
def member (v : Nat) (s : Bag) : Bool :=
  -- ADMITDEF
  match s with
  | [] => false
  | h :: t => bif v == h then true else member v t
  -- /ADMITDEF

-- test_member1
unseal member in
example : member 1 [1, 4, 1] = true := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_member1

-- test_member2
unseal member in
example : member 2 [1, 4, 1] = false := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_member2
-- []

unseal member in
theorem member_nil v : member v [] = false := by rfl -- ADMITTED

unseal member in
theorem member_add_same v t : member v (add v t) = true := by
  -- ADMITTED
  dsimp [add, member]
  -- TODO (DHS): rw? doesn't suggest this one for some reason. Why?
  -- We may need to teach students about this theorem explicitly, perhaps in UsingLean
  rw [BEq.refl]
  dsimp
  -- /ADMITTED

unseal member in
theorem member_add_diff v1 v2 t : (v1 == v2) = false -> member v1 (add v2 t) = member v1 t := by
  -- ADMITTED
  intro h
  dsimp [add, member]
  rw [h]
  dsimp
  -- /ADMITTED

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

@[irreducible]
def remove_one (v : Nat) (s : Bag) : Bag :=
  -- ADMITDEF
  match s with
  | [] => []
  | h :: t => bif h == v then t else h :: remove_one v t
  -- /ADMITDEF

-- test_remove_one1
unseal count
unseal remove_one
example : count 5 (remove_one 5 [2, 1, 5, 4, 1]) = 0 := by rfl  -- ADMITTED
-- test_remove_one2
example : count 5 (remove_one 5 [2, 1, 4, 1]) = 0 := by rfl  -- ADMITTED
-- test_remove_one3
example : count 4 (remove_one 5 [2, 1, 4, 5, 1, 4]) = 2 := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_remove_one3
-- test_remove_one4
example : count 5 (remove_one 5 [2, 1, 5, 4, 5, 1, 4]) = 1 := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_remove_one4
seal count
seal remove_one

unseal remove_one in
theorem remove_one_nil v : remove_one v [] = [] := by rfl -- ADMITTED

unseal remove_one in
theorem remove_one_add_same v1 v2 t : (v2 == v1) = true -> remove_one v1 (add v2 t) = t := by
  -- ADMITTED
  intro h
  dsimp [remove_one]
  rw [h]
  dsimp
  -- /ADMITTED

unseal remove_one in
theorem remove_one_add_diff v1 v2 t : (v2 == v1) = false -> remove_one v1 (add v2 t) = add v2 (remove_one v1 t) := by
  -- ADMITTED
  intro h
  dsimp [remove_one]
  rw [h]
  dsimp
  -- /ADMITTED

@[irreducible]
def remove_all (v : Nat) (s : Bag) : Bag :=
  -- ADMITDEF
  match s with
  | [] => []
  | h :: t => bif h == v then remove_all v t else h :: remove_all v t
  -- /ADMITDEF

unseal count
unseal remove_all
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
seal count
seal remove_all

unseal remove_all in
theorem remove_all_nil v : remove_all v [] = [] := by rfl -- ADMITTED

unseal remove_all in
theorem remove_all_add_same v t : remove_all v (add v t) = remove_all v t := by
  -- ADMITTED
  dsimp [add, remove_all]
  rw [BEq.refl]
  dsimp
  -- /ADMITTED

unseal remove_all in
theorem remove_all_add_diff v1 v2 t : (v2 == v1) = false -> remove_all v1 (add v2 t) = add v2 (remove_all v1 t) := by
  -- ADMITTED
  intro h
  dsimp [add, remove_all]
  rw [h]
  dsimp
  -- /ADMITTED

@[irreducible]
def included (s1 s2 : Bag) : Bool :=
  -- ADMITDEF
  match s1 with
  | [] => true
  | h :: t => member h s2 && included t (remove_one h s2)
  -- /ADMITDEF

-- test_included1
unseal included
unseal member
unseal remove_one
example : included [1, 2] [2, 1, 4, 1] = true := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_included1
-- test_included2
example : included [1, 2, 2] [2, 1, 4, 1] = false := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_included2
-- []
seal included
seal member
seal remove_one

unseal included in
theorem included_nil s : included [] s = true := by rfl -- ADMITTED

unseal included in
theorem included_add_member v s1 s2 : member v s2 = true -> included (add v s1) s2 = included s1 (remove_one v s2) := by
  -- ADMITTED
  intro h
  dsimp [add, included]
  rw [h]
  rfl
  -- /ADMITTED

unseal included in
theorem included_add_nonmember v s1 s2 : member v s2 = false -> included (add v s1) s2 = false := by
  -- ADMITTED
  intro h
  dsimp [add, included]
  rw [h]
  rfl
  -- /ADMITTED

-- EX2M? (add_inc_count)
-- Adding a value to a bag should increase the value's count by one.
-- State this as a theorem and prove it.
-- QUIETSOLUTION
theorem add_inc_count (s : Bag) (v : Nat) :
    count v (add v s) = (count v s) + 1 := by
  dsimp [add]
  rw [count_cons_same]
  exact (BEq.refl v)
-- /QUIETSOLUTION
-- GRADE_MANUAL 2: add_inc_count
-- []

end Bag

-- /FULL
-- ######################################################################
-- # Reasoning About Lists

/- FULL: As with numbers, simple facts about list-processing
   functions can sometimes be proved entirely by simplification.
   For example, just `rfl` is enough for this theorem... -/
/- TERSE: As with numbers, some proofs about list functions need only
   simplification... -/
/- TODO (KH): The above comment is wrong, since we use `rw` here.
   Should we put unseal + rfl? Or change the comments? I am a bit confused because this file
   uses `unseal` and `dsimp` extensively.
   -/

theorem nil_app (l : NatList) : ([] : NatList) ++ l = l := by rw [NatList.nil_append]

/- FULL: ...because the `[]` is substituted into the "scrutinee" (the
   expression whose value is being "scrutinized" by the match) in the
   definition of `app`, allowing the match itself to be simplified. -/

/- FULL: Also, as with numbers, it is sometimes helpful to perform case
   analysis on the possible shapes -- empty or non-empty -- of an
   unknown list. -/
-- TERSE: ***
-- TERSE: ...and some need case analysis.

theorem tl_length_pred (l : NatList) :
    l.length.pred = l.tl.length := by
  cases l
  case nil => rw [tl_nil, nil_length]; dsimp
  case cons n l' => rw [tl_cons, cons_length]; dsimp

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
-- ## Induction on Lists

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

  * First, show that `P` is true of `l` when `l` is `[]`.
  * Then show that `P` is true of `l` when `l` is `n :: l'` for
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

theorem app_assoc (l1 l2 l3 : NatList) :
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  induction l1
  case nil =>
    rw [nil_append, nil_append]
  case cons n l1' ih =>
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
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (c n : Nat) :
    NatList.myRepeat n c ++ NatList.myRepeat n c = NatList.myRepeat n (c + c) := by
  induction c
  case zero => rw [repeat_zero, nil_append]
  case succ c' ih =>
    rw [repeat_succ]
    -- Now we seem to be stuck.  The IH only works for c' + c',
    -- but we need c' + 1 + (c' + 1).
    sorry

-- FULL: To get a more general inductive hypothesis, we can generalize:
-- TERSE: A generalization that gives a stronger inductive hypothesis:

theorem myRepeat_plus (c1 c2 n : Nat) :
    NatList.myRepeat n c1 ++ NatList.myRepeat n c2 = NatList.myRepeat n (c1 + c2) := by
  induction c1
  case zero =>
    rw [repeat_zero, Nat.zero_add, nil_append]
  case succ c1' ih =>
    rw [Nat.succ_add, repeat_succ, repeat_succ, cons_append, ih]

-- *** Reversing a List

/- FULL: For a slightly more involved example of inductive proof over
  lists, suppose we use `app` to define a list-reversing function
   `rev`: -/
-- TERSE: A more interesting example of induction over lists:

@[irreducible]
def NatList.rev (l : NatList) : NatList :=
  match l with
  | [] => []
  | h :: t => t.rev ++ [h]

unseal NatList.rev in
theorem rev_nil : [].rev = [] := by rfl

unseal NatList.rev in
theorem rev_cons h (t : NatList) : (h :: t).rev = t.rev ++ [h] := by rfl

-- test_rev1
unseal NatList.rev in
unseal NatList.app in
example : [1, 2, 3].rev = [3, 2, 1] := by rfl
-- test_rev2
unseal NatList.rev in
example : ([] : NatList).rev = [] := by rfl



-- FULL: For something a bit more challenging, let's prove that
-- reversing a list does not change its length.  Our first attempt
-- gets stuck in the successor case...
-- TERSE: ***
-- TERSE: Let's try to prove `length (rev l) = length l`.

-- rev_length_firsttry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (l : NatList) :
    l.rev.length = l.length := by
  induction l
  case nil => rw [rev_nil]
  case cons n l' ih =>
    rw [rev_cons]
    -- Now we seem to be stuck: the goal involves `++`, but we
    -- but we don't have any useful equations
    -- in either the immediate context or in the global
    -- environment!
    sorry

/- FULL: A first attempt to make progress would be to prove exactly
    the statement that we are missing at this point.  But this attempt
    will fail because the inductive hypothesis is not general enough. -/
-- app_rev_length_S_firsttry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (l : NatList) n :
    (l.rev ++ [n]).length = .succ l.rev.length := by
  induction l
  case nil =>
    rw [rev_nil, nil_append, cons_length, nil_length]
  case cons n l' ih =>
    rw [rev_cons]
    -- ih not applicable
    sorry

/- FULL: It turns out that the above lemma is more specific than it
   needs to be. We can strengthen the lemma to work not only on reversed
   lists but on general lists. -/
theorem app_length_succ (l : NatList) (n : Nat) :
    (l ++ [n]).length = l.length + 1 := by
  induction l
  case nil => rw [nil_append, cons_length]
  case cons m l' ih =>
    rw [cons_append, cons_length, ih, cons_length]

-- TERSE: ***
-- Now we can prove the main theorem.

theorem rev_length (l : NatList) :
    l.rev.length = l.length := by
  induction l
  case nil => rw [rev_nil]
  case cons n l' ih =>
    rw [rev_cons, app_length_succ, ih, cons_length]

-- TERSE: ***
-- FULL: We can also prove a more general form that gives the
-- length of any two appended lists.

-- app_length
theorem app_length (l1 l2 : NatList) :
    (l1 ++ l2).length = l1.length + l2.length := by
  -- WORKINCLASS
  induction l1
  case nil => rw [nil_append, nil_length, Nat.zero_add]
  case cons n l1' ih =>
    rw [cons_append, cons_length, ih, cons_length, Nat.succ_add]
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
theorem foo1 (n : Nat) (l : NatList) :
    NatList.myRepeat n 0 = l -> l.length = 0 := by
  intro h
  rewrite [←h, repeat_zero, nil_length]
  rfl
-- /HIDE
-- /QUIZ

-- QUIZ --
/- What about the next one?

      theorem foo2 :  forall n m : Nat,
        (NatList.myRepeat n m).length = m

    Which tactics do we need besides [intro], [dsimp], [rewrite], and
    [rfl]?  (A) none, (B) [cases], (C) [induction on n],
    (D) [induction on m], or (E) can't be done with the tactics we've
    seen.
-/

-- HIDE
theorem foo2 (n m : Nat) :
    (NatList.myRepeat n m).length = m := by
  induction m
  case zero => rewrite [repeat_zero, nil_length]; rfl
  case succ m' ih =>
    rewrite [repeat_succ, cons_length, ih]; rfl
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
-- ## Search

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
-- ## List Exercises, Part 1

-- EX3 (list_exercises)
-- More practice with lists:

theorem app_nil_r (l : NatList) :
    l ++ ([] : NatList) = l := by
  -- ADMITTED
  induction l
  case nil => rw [nil_append]
  case cons n l' ih =>
    rw [cons_append, ih]
-- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.app_nil_r

theorem rev_app_distr (l1 l2 : NatList) :
   (l1 ++ l2).rev = l2.rev ++ l1.rev := by
  -- ADMITTED
  induction l1
  case nil => rw [nil_append, rev_nil, app_nil_r]
  case cons x l1' ih =>
    rw [ cons_append, rev_cons, ih, rev_cons, app_assoc]
-- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.rev_app_distr

-- An _involution_ is a function that is its own inverse. That is,
-- applying the function twice yields the original input.
theorem rev_involutive (l : NatList) :
    l.rev.rev = l := by
  -- ADMITTED
  induction l
  case nil => rw [rev_nil, rev_nil]
  case cons n l' ih =>
    rw [rev_cons, rev_app_distr, ih, rev_cons, rev_nil, nil_append, cons_append, nil_append]
-- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.rev_involutive

-- There is a short solution to the next one.  If you find yourself
-- getting tangled up, step back and try to look for a simpler way.

theorem app_assoc4 (l1 l2 l3 l4 : NatList) :
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4 := by
  -- ADMITTED
  rw [app_assoc, app_assoc]
-- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.app_assoc4

-- An exercise about your implementation of `nonzeros`:

-- nonzeros_app
theorem nonzeros_app (l1 l2 : NatList) :
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2) := by
  -- ADMITTED
  induction l1
  case nil => rw [nonzeros_nil, nil_app, nil_app]
  case cons n l1' ih =>
    cases n
    case zero =>
      rw [nonzeros_cons_zero, ←ih, cons_append, nonzeros_cons_zero]
    case succ n' =>
      rw [cons_append, nonzeros_cons_nonzero, nonzeros_cons_nonzero, ih, cons_append]


-- /ADMITTED
-- GRADE_THEOREM 1: NatList.nonzeros_app
-- []

-- EX2 (eqblist)
-- GRADE_THEOREM 2: NatList.eqblist_refl
-- Fill in the definition of `eqblist`, which compares
-- lists of numbers for equality.  Prove that `eqblist l l`
-- yields `true` for every list `l`.

@[irreducible]
def eqblist (l1 l2 : NatList) : Bool :=
  -- ADMITDEF
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => (h1 == h2) && eqblist t1 t2
  | _, _ => false
  -- /ADMITDEF

unseal eqblist in
theorem eqblist_nil : eqblist [] [] = true := by rfl

unseal eqblist in
theorem eqblist_cons_same h t1 t2 : eqblist (h :: t1) (h :: t2) = eqblist t1 t2 := by
  dsimp [eqblist]
  rw [BEq.refl, Bool.true_and]

unseal eqblist in
theorem eqblist_cons_diff h1 h2 t1 t2 : (h1 == h2) = false -> eqblist (h1 :: t1) (h2 :: t2) = false := by
  intro h
  dsimp [eqblist]
  rw [h, Bool.false_and]

-- test_eqblist1
unseal eqblist
example : eqblist [] [] = true := by rfl  -- ADMITTED
-- test_eqblist2
example : eqblist [1, 2, 3] [1, 2, 3] = true := by rfl  -- ADMITTED
-- test_eqblist3
example : eqblist [1, 2, 3] [1, 2, 4] = false := by rfl  -- ADMITTED
seal eqblist

-- eqblist_refl
theorem eqblist_refl (l : NatList) :
    eqblist l l = true := by
  -- ADMITTED
  induction l
  case nil => rw [eqblist_nil]
  case cons n l' ih =>
    rw [eqblist_cons_same]
    exact ih
-- /ADMITTED
-- []

-- ######################################################################
-- ## List Exercises, Part 2

open Bag

-- Here are a couple of little theorems to prove about your
-- definitions about bags above.

-- EX1 (count_member_nonzero)
-- count_member_nonzero
theorem count_member_nonzero (s : Bag) :
    Nat.ble 1 (count 1 (1 :: s)) = true := by
  -- ADMITTED
  rw [count_cons_same]
  rfl; rfl
-- /ADMITTED
-- []

-- The following lemma about `Nat.ble` might help you in the next
-- exercise (it will also be useful in later chapters).

theorem leb_n_Sn (n : Nat) :
    Nat.ble n (n + 1) = true := by
  induction n
  case zero => rfl
  case succ n' ih => dsimp [Nat.ble]; exact ih

-- Before doing the next exercise, make sure you've filled in the
-- definition of `remove_one` above.

-- HIDE
/- LATER: CH: The following exercise is not so simple.  Also the
     shape of the theorem (with a magic constant [0]), and the fact that
     n needs to be destructed seem like big and ugly hacks. The
     hack-free theorem looks like this: -/
/- LATER: BCP 20: We'd need to find a way to get through the first
   lemma's proof without using features they don't know... -/
theorem count_remove_one v s :
  count v (remove_one v s) = (count v s).pred := by
  induction s
  case nil => rw [remove_one_nil, count_nil]; rfl
  case cons n l ih =>
  -- XXX they don't know about generalizing or casing on expressions yet !!!
    cases h : n == v
    case false =>
      rw [remove_one_add_diff, count_cons_diff, ih, count_cons_diff]
      exact h; exact h; exact h
    case true =>
      -- they don't yet have tools for this case
      rw [remove_one_add_same, count_cons_same]
      dsimp; exact h; exact h

theorem leb_pred_n_n n :
    Nat.ble n.pred n = true := by
  induction n
  case zero => dsimp [Nat.ble]
  case succ n ih =>
    dsimp
    rw [leb_n_Sn]

theorem remove_does_not_increase_count' (s : Bag) (n : Nat) :
    Nat.ble (count n (remove_one n s)) (count n s) = true := by
  induction s
  case nil => rw [remove_one_nil, count_nil]; rfl
  case cons n' l ih =>
    rw [count_remove_one, leb_pred_n_n]
-- /HIDE

-- EX3A (remove_does_not_increase_count)

theorem remove_does_not_increase_count (s : Bag) :
    Nat.ble (count 0 (remove_one 0 s)) (count 0 s) = true := by
  -- ADMITTED
  induction s
  case nil => rw [remove_one_nil, count_nil]; rfl
  case cons n s' ih =>
    cases n
    case zero =>
      rw [remove_one_add_same, count_cons_same]
      rw [leb_n_Sn]; rfl; rfl
    case succ n' =>
      rw [remove_one_add_diff, count_cons_diff, count_cons_diff]
      exact ih; rfl; rfl; rfl
-- /ADMITTED
-- []

-- EX3M? (bag_count_sum)
-- Write down an interesting theorem `bag_count_sum` about bags
-- involving the functions `count` and `sum`, and prove it.
-- (You may find that the difficulty of the proof depends on how you defined `count`!

/- LATER: APT: This is the obvious theorem, and everyone came up with
   it.  But how hard it is to prove (in terms of Rocq mechanics)
   depends critically on how the student defined [count] -- the
   solution for which has not been given at this point, and is not so
   obvious. BCP 9/16: For the moment, I've just added an explicit
   warning to this effect - not sure whether we can do better. (Is
   there a hint we could give about how count should have been
   defined, to make this easier?  There's no problem giving a hint
   here, since they'll already have solved the count exercise once
   before getting to this point.) MRC 1/19: The proof uses [destruct]
   on a term that is not merely an identifier. That usage has not
   been introduced yet. APT 21: Added a hint about that. MRC 2/22:
   Even if the exercise is optional, it ought to be solvable with
   with the material introduced thus far. It is not. I note that BCP
   has rejected the proof in the exercise above for [count_remove_one]
   because it [destruct]s on a term rather than identifier. -/
-- SOLUTION
theorem bag_count_sum (s1 s2 : Bag) (v : Nat) :
    count v (sum s1 s2) = (count v s1) + (count v s2) := by
  induction s1
  case nil =>
    rw [nil_sum, count_nil, Nat.zero_add]
  case cons h s1' ih =>
    rw [cons_sum,]
    cases hv : (h == v)
    case false =>
      rw [count_cons_diff, count_cons_diff]
      exact ih; exact hv; exact hv
    case true =>
      rw [count_cons_same, count_cons_same, Nat.succ_add, ←ih]
      exact hv; exact hv
-- /SOLUTION
-- []

-- EX3A (involution_injective)
-- Prove that every involution is injective.
--
-- Involutions were defined above in `rev_involutive`. An _injective_
-- function is one-to-one: it maps distinct inputs to distinct
-- outputs, without any collisions.

theorem involution_injective (f : Nat → Nat) :
    (∀ n : Nat, n = f (f n)) →
    (∀ n1 n2 : Nat, f n1 = f n2 → n1 = n2) := by
  -- ADMITTED
  intro hinv n1 n2 heq
  rw [hinv n1, hinv n2, heq]
-- /ADMITTED
-- []

-- EX2A (rev_injective)
-- Prove that `rev` is injective. Do not prove this by induction --
-- that would be hard. Instead, re-use the same proof technique that
-- you used for `involution_injective`. (But: Don't try to use that
-- exercise directly as a lemma: the types are not the same!)

theorem rev_injective (l1 l2 : NatList) :
  l1.rev = l2.rev → l1 = l2 := by
  -- ADMITTED
  intro heq
  rw [← rev_involutive l1, ← rev_involutive l2, heq]
-- /ADMITTED
-- []

-- /FULL
-- ######################################################################
-- # Options

-- FULL: Suppose we want to write a function that returns the `n`th
-- element of some list.  If we give it type `NatList → Nat → Nat`,
-- then we'll have to choose some number to return when the list is
-- too short...
-- TERSE: Suppose we'd like a function to retrieve the `n`th element
--     of a list.  What to do if the list is too short?

@[irreducible]
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

@[irreducible]
def nth_error (l : NatList) (n : Nat) : NatOption :=
  match l with
  | [] => .none
  | a :: l' => match n with
    | 0 => .some a
    | n' + 1 => nth_error l' n'

-- test_nth_error1
unseal nth_error
example : nth_error [4, 5, 6, 7] 0 = .some 4 := by rfl
-- test_nth_error2
example : nth_error [4, 5, 6, 7] 3 = .some 7 := by rfl
-- test_nth_error3
example : nth_error [4, 5, 6, 7] 9 = .none := by rfl
seal nth_error

-- FULL

-- The function below pulls the `Nat` out of an `NatOption`,
-- returning a supplied default in the `none` case.

@[irreducible]
def option_elim (d : Nat) (o : NatOption) : Nat :=
  match o with
  | .some n => n
  | .none => d

unseal option_elim in
theorem option_elim_none d : option_elim d .none = d := by rfl

unseal option_elim in
theorem option_elim_some d1 d2 : option_elim d1 (.some d2) = d2 := by rfl

-- EX2 (hd_error)
-- Using the same idea, fix the `hd` function from earlier so we
-- don't have to pass a default element for the `nil` case.

@[irreducible]
def hd_error (l : NatList) : NatOption :=
  -- ADMITDEF
  match l with
  | [] => .none
  | h :: _ => .some h
  -- /ADMITDEF

-- test_hd_error1
unseal hd_error
example : hd_error ([] : NatList) = .none := by rfl  -- ADMITTED
-- test_hd_error2
example : hd_error [1] = .some 1 := by rfl  -- ADMITTED
-- test_hd_error3
example : hd_error [5, 6] = .some 5 := by rfl  -- ADMITTED
seal hd_error
-- GRADE_THEOREM 1: test_hd_error1
-- GRADE_THEOREM 1: test_hd_error2
-- []

unseal hd_error in
theorem hd_error_nil : hd_error [] = .none := by rfl -- ADMITTED

unseal hd_error in
theorem hd_error_cons h t : hd_error (h :: t) = .some h := by rfl -- ADMITTED


-- EX1? (option_elim_hd)
-- GRADE_THEOREM 1: NatList.option_elim_hd
-- This exercise relates your new `hd_error` to the old `hd`.

-- option_elim_hd
theorem option_elim_hd (l : NatList) (default : Nat) :
    NatList.hd default l = option_elim default (hd_error l) := by
  -- ADMITTED
  cases l
  case nil => rw [hd_error_nil, option_elim_none, hd_nil]
  case cons n l' =>
    rw [hd_cons, hd_error_cons, option_elim_some]
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

theorem mirror_size t : size t = size (mirror t) := by
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
-- # Partial Maps

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
  x1.val == x2.val

-- EX1 (eqb_id_refl)
-- GRADE_THEOREM 1: eqb_id_refl
-- eqb_id_refl
theorem eqb_id_refl (x : MyId) : eqb_id x x = true := by
  -- ADMITTED
  dsimp [eqb_id]
  rw [BEq.refl]
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
theorem quiz1 (d : PartialMap) (x : MyId) (v : Nat) :
    find x (update d x v) = some v := by
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
theorem quiz2  (d : PartialMap) (x y : MyId) (o : Nat) :
    eqb_id x y = false →
    find x (update d y o) = find x d := by
  intro h
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
theorem update_eq (d : PartialMap) (x : MyId) (v : Nat) :
    find x (update d x v) = some v := by
  -- ADMITTED
  dsimp [update, find]
  rw [eqb_id_refl]
  dsimp
-- /ADMITTED
-- []

-- EX1 (update_neq)
-- GRADE_THEOREM 1: PartialMap.update_neq
-- update_neq
theorem update_neq (d : PartialMap) (x y : MyId) (o : Nat) :
    eqb_id x y = false → find x (update d y o) = find x d := by
  -- ADMITTED
  intro h
  dsimp [update, find]
  rw [h]
  dsimp
-- /ADMITTED
-- []
-- /FULL

end PartialMap

-- HIDE
-- EX2M? (baz_num_elts)
/- HIDE: I'm not sure the material covered up to here suffices to
  understand that Inductive types must have finite elements and avoid
  the trap of coming up with infinite lists.  HIDE: MRC'20: I have to
  agree with the comments regarding this exercise.  It's unmotivated
  and feels like a trap.  Is there a concept we're trying to get
  across here that's necessary?  I'm proposing the exercise be
  optional.  BCP '20: Looks like someone made it optional. :-) But
  should we just drop it?  IY '20: I agree with the above comments,
  but I sort of appreciate this exercise. It gives a good
  introduction to the concept that some types may not be
  inhabited. Could we just add a hint that Inductive types must have
  finite elements?  BCP 20: That would kind of give away the answer,
  no?  I think leaving it in but leaving it optional is the best
  compromise. MRC 2/22: I don't think the exercise "introduces" the
  concept that types may be uninhabited. Instead it *demands* the
  student invent that notion on their own, which is non-obvious to
  your average OCaml (say) programmer. Also, at this point in the
  file it is a complete non-sequitur. And it has nothing to do with
  lists or other standard data types, as the rest of the file. KK:
  Also this exercise comes out of the blue without any
  motivation/introduction.  BCP 23: OK, I am removing it. -/

-- Consider the following inductive definition:

inductive Baz where
  | baz1 (x : Baz)
  | baz2 (y : Baz) (b : Bool)

/- How _many_ elements does the type [baz] have? (Explain in words,
   in a comment.) -/

-- SOLUTION
/- None!  In order to create an element of type [baz], we would need
      to use one of the two constructors [Baz1] and [Baz2]; but both of
      these require a [baz] as an argument.  So this definition cannot
      get off the ground: in order to create a [baz] we would need to
      already have one. -/
-- /SOLUTION
-- LATER: Rework this exercise for easier grading?

/- LATER: KK: I am not sure whether this point should be made through a
  "manual" exercise like the one below. The students who don't know
  (or notice) that an Inductive definition needs a base case will
  just fail this exercise and will only see the reason in the grader
  comment. It is very easy for a student to falsely think that they
  have the right answer here and just move on without thinking about
  it. I think that it would be better to either add a small section
  that clearly explains this concept, or maybe add a hint similar to
  the one below: -/

/- Hint: Try to write a value of type baz for which the following
     lemma [one_true_baz] holds. -/

def count_trues (x : Baz) : Nat :=
  match x with
  | .baz1 x' => count_trues x'
  | .baz2 x' true => 1 + count_trues x'
  | .baz2 x' _ => count_trues x'

-- theorem one_true_baz : count_trues (your baz here) = 1. --

-- []
-- /HIDE
