-- Lists: Working with Structured Data

-- INSTRUCTORS: This file takes about 60 minutes to get through.
--    Putting it together with Induction.lean makes a reasonable
--    second week's homework assignment.

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

import lf.Induction

-- ######################################################################
-- * Pairs of Numbers

-- FULL: In an `inductive` type definition, each constructor can take
-- any number of arguments -- none (as with `true` and `Nat.zero`),
-- one (as with `Nat.succ`), or more than one (as with `Nybble` and
-- the following):
-- TERSE: An inductive definition of pairs of numbers.  It has just
--     one constructor, taking two arguments:

structure NatProd where
  fst : Nat
  snd : Nat

-- FULL: This declaration can be read: "The one and only way to
-- construct a pair of numbers is by giving two arguments of type
-- `Nat`."

-- FULL: Lean's `structure` command automatically generates accessor
-- functions `NatProd.fst` and `NatProd.snd` for the fields.

#check (NatProd.mk 3 5)

-- TERSE: ***

example : (NatProd.mk 3 5).fst = 3 := by rfl

-- TERSE: ***

-- FULL: Since pairs will be used heavily in what follows, it will be
-- convenient to write them with angle bracket notation `⟨x, y⟩`
-- instead of `NatProd.mk x y`. Lean's anonymous constructor
-- syntax works when the expected type is known.
-- TERSE: A nicer notation for pairs:

example : (⟨3, 5⟩ : NatProd).fst = 3 := by rfl

-- The anonymous constructor can be used in pattern matches too.

def NatProd.swap (p : NatProd) : NatProd :=
  ⟨p.snd, p.fst⟩

-- TERSE: ***
-- If we state properties of pairs in a slightly peculiar way, we can
-- sometimes complete their proofs with just reflexivity and its
-- built-in simplification:

-- surjective_pairing'
theorem surjective_pairing' : ∀ (n m : Nat),
  (⟨n, m⟩ : NatProd) = ⟨(⟨n, m⟩ : NatProd).fst, (⟨n, m⟩ : NatProd).snd⟩ := by
  intro n m; rfl

-- TERSE: ***
-- But just `rfl` is not enough if we state the lemma in a more
-- natural way:

-- surjective_pairing_stuck
theorem surjective_pairing_stuck : ∀ (p : NatProd),
  p = ⟨p.fst, p.snd⟩ := by
  intro p
  -- `rfl` doesn't work here!
  sorry

-- TERSE: ***
-- FULL: Instead, we need to expose the structure of `p` so that
-- the accessor functions can compute.  We can do this with `cases`
-- (or by destructuring in `intro`).
-- TERSE: Solution: use `cases` (or destructuring).

-- surjective_pairing
theorem surjective_pairing : ∀ (p : NatProd),
  p = ⟨p.fst, p.snd⟩ := by
  intro ⟨n, m⟩; rfl

-- FULL: Notice that, by contrast with the behavior of `cases` on
-- `Nat`s, where it generates two subgoals, `cases` generates just
-- one subgoal here.  That's because `NatProd`s can only be
-- constructed in one way.

-- FULL
-- EX1 (snd_fst_is_swap)
-- snd_fst_is_swap
theorem snd_fst_is_swap : ∀ (p : NatProd),
  (⟨p.snd, p.fst⟩ : NatProd) = p.swap := by
  -- ADMITTED
  intro ⟨n, m⟩; rfl
-- /ADMITTED
-- []

-- EX1? (fst_swap_is_snd)
-- fst_swap_is_snd
theorem fst_swap_is_snd : ∀ (p : NatProd),
  p.swap.fst = p.snd := by
  -- ADMITTED
  intro ⟨n, m⟩; rfl
-- /ADMITTED
-- []
-- /FULL

-- ######################################################################
-- * Lists of Numbers

-- FULL: Generalizing the definition of pairs, we can describe the
-- type of _lists_ of numbers like this: "A list is either the empty
-- list or else a pair of a number and another list."
--
-- Lean's standard library provides a polymorphic `List` type with
-- exactly this structure:
--
--     inductive List (α : Type) where
--       | nil : List α
--       | cons (head : α) (tail : List α) : List α
--
-- We write `List Nat` for lists of natural numbers.  The notation
-- `[]` means `List.nil` and `::` means `List.cons`.  Lean also
-- provides bracket notation: `[1, 2, 3]` means `1 :: 2 :: 3 :: []`.

-- TERSE: We use Lean's built-in `List Nat` type:

-- For example, here is a three-element list:

def mylist : List Nat := [1, 2, 3]

-- Now these all mean exactly the same thing:
def mylist1 : List Nat := 1 :: (2 :: (3 :: []))
def mylist2 : List Nat := 1 :: 2 :: 3 :: []
def mylist3 : List Nat := [1, 2, 3]

-- We put our function definitions in a namespace, so we can
-- define our own versions of standard list functions for practice.

namespace NatList

-- TERSE: Some useful list-manipulation functions...

-- *** Repeat

-- FULL: First is the `myRepeat` function, which takes a number `n`
-- and a `count` and returns a list of length `count` in which every
-- element is `n`.
-- (We use `myRepeat` because `repeat` is a reserved keyword in Lean.)

def myRepeat (n count : Nat) : List Nat :=
  match count with
  | 0 => []
  | count' + 1 => n :: myRepeat n count'

-- *** Length

-- FULL: The `length` function calculates the length of a list.

def length (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | _ :: t => (length t) + 1

@[simp] theorem length_nil : length ([] : List Nat) = 0 := rfl
@[simp] theorem length_cons (h : Nat) (t : List Nat) : length (h :: t) = (length t) + 1 := rfl

-- *** Append

-- FULL: The `app` function appends (concatenates) two lists.

def app (l1 l2 : List Nat) : List Nat :=
  match l1 with
  | [] => l2
  | h :: t => h :: app t l2

-- *** Type Classes and Overloading

-- FULL: In Lean, operators like `++`, `==`, and `+` are not
-- hardwired to particular types.  Instead, they are defined using
-- _type classes_ — a mechanism that lets us overload operations
-- for different types.
--
-- For example, `++` is defined via the `HAppend` type class.
-- Any type that provides an `HAppend` instance gets to use `++`.
-- Lean's built-in `List` already has such an instance (using
-- `List.append`), but since we've defined our own `app` function,
-- we can register it as the `++` operator within our namespace:

instance : HAppend (List Nat) (List Nat) (List Nat) where
  hAppend := app

-- Now `l1 ++ l2` means `app l1 l2` within `NatList`.

-- These simp lemmas tell the simplifier how `++` computes on lists.
-- They follow directly from the definition of `app`.
@[simp] theorem app_nil_l (l : List Nat) : ([] : List Nat) ++ l = l := rfl
@[simp] theorem app_cons_l (h : Nat) (t l : List Nat) : (h :: t) ++ l = h :: (t ++ l) := rfl

-- test_app1
example : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5] := by rfl
-- test_app2
example : ([] : List Nat) ++ [4, 5] = [4, 5] := by rfl
-- test_app3
example : [1, 2, 3] ++ ([] : List Nat) = [1, 2, 3] := by rfl

-- FULL: We'll learn more about type classes as we go.  For now, the
-- key idea is: a type class is an interface, and an instance is an
-- implementation of that interface for a particular type.  The
-- `@[simp]` attribute tells Lean's simplifier how to unfold `++`
-- back to `app` when proving theorems.
--
-- (For a thorough treatment of type classes, see Chapter 3 of
-- _Functional Programming in Lean_.)

-- *** Head and Tail

-- FULL: The `hd` function returns the first element (the "head") of
-- the list, while `tl` returns everything but the first element (the
-- "tail").  Since the empty list has no first element, we pass
-- a default value to be returned in that case.

def hd (default : Nat) (l : List Nat) : Nat :=
  match l with
  | [] => default
  | h :: _ => h

def tl (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | _ :: t => t

-- test_hd1
example : hd 0 [1, 2, 3] = 1 := by rfl
-- test_hd2
example : hd 0 [] = 0 := by rfl
-- test_tl
example : tl [1, 2, 3] = [2, 3] := by rfl

-- QUIZ
-- What does the following function do?

def foo (n : Nat) : List Nat :=
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

def nonzeros (l : List Nat) : List Nat :=
  -- ADMITDEF
  match l with
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
  -- /ADMITDEF

-- test_nonzeros
example : nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3] := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_nonzeros

def oddmembers (l : List Nat) : List Nat :=
  -- ADMITDEF
  match l with
  | [] => []
  | h :: t => if odd h then h :: oddmembers t else oddmembers t
  -- /ADMITDEF

-- test_oddmembers
example : oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3] := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: NatList.test_oddmembers

-- For the next problem, `countoddmembers`, we're giving you a header
-- that uses `def` instead of a recursive definition.  The point is to
-- encourage you to implement it using already-defined functions.

def countoddmembers (l : List Nat) : Nat :=
  -- ADMITDEF
  length (oddmembers l)
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
-- Complete the following definition of `alternate`, which
-- interleaves two lists into one, alternating between elements taken
-- from the first list and elements from the second.
--
-- Hint: there are natural ways of writing `alternate` that fail to
-- satisfy Lean's requirement that all recursive definitions be
-- _structurally recursive_.  If you encounter this difficulty,
-- consider pattern matching against both lists at the same time.

def alternate (l1 l2 : List Nat) : List Nat :=
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
example : alternate ([] : List Nat) [20, 30] = [20, 30] := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: NatList.test_alternate4
-- []

-- ######################################################################
-- *** Bags via Lists

-- A `bag` (or `multiset`) is like a set, except that each element
-- can appear multiple times rather than just once.  One way of
-- representing a bag of numbers is as a list.

abbrev Bag := List Nat

-- EX3! (bag_functions)
-- Complete the following definitions for the functions `count`,
-- `sum`, `add`, and `member` for bags.

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

-- Multiset `sum` is similar to set `union`: `sum a b` contains all
-- the elements of `a` and those of `b`.

def sum : Bag → Bag → Bag :=
  -- ADMITDEF
  app
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

-- When `remove_one` is applied to a bag without the number to
-- remove, it should return the same bag unchanged.

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
theorem add_inc_count :
  ∀ (s : Bag) (v : Nat),
  count v (add v s) = (count v s) + 1 := by
  intro s v
  simp [add, count]
-- /QUIETSOLUTION
-- GRADE_MANUAL 2: add_inc_count
-- []

-- /FULL
-- ######################################################################
-- * Reasoning About Lists

-- FULL: As with numbers, simple facts about list-processing
-- functions can sometimes be proved entirely by simplification.
-- TERSE: As with numbers, some proofs about list functions need only
--     simplification...

theorem nil_app : ∀ l : List Nat,
  ([] : List Nat) ++ l = l := by
  intro l; rfl

-- FULL: ...because the `[]` is substituted into the "scrutinee" (the
-- expression whose value is being "scrutinized" by the match) in the
-- definition of `app`, allowing the match itself to be simplified.

-- FULL: Also, as with numbers, it is sometimes helpful to perform case
-- analysis on the possible shapes -- empty or non-empty -- of an
-- unknown list.
-- TERSE: ***
-- TERSE: ...and some need case analysis.

theorem tl_length_pred : ∀ l : List Nat,
  Nat.pred (length l) = length (tl l) := by
  intro l
  cases l with
  | nil => rfl
  | cons n l' => rfl

-- FULL: Here, the `nil` case works because we've chosen to define
-- `tl [] = []`. Notice that the `cons` case introduces two names,
-- `n` and `l'`, corresponding to the fact that the `cons` constructor
-- for lists takes two arguments (the head and tail of the list it is
-- constructing).

-- Usually, though, interesting theorems about lists require
-- induction for their proofs.  We'll see how to do this next.

-- FULL
-- (Micro-Sermon: As we get deeper into this material, simply
-- _reading_ proof scripts will not help you very much.  Rather, it
-- is important to step through the details of each one using Lean and
-- think about what each step achieves.  Otherwise it is more or less
-- guaranteed that the exercises will make no sense when you get to
-- them.  'Nuff said.)
-- /FULL

-- ######################################################################
-- ** Induction on Lists

-- FULL: Proofs by induction over datatypes like `List Nat` are a
-- little less familiar than standard natural number induction, but
-- the idea is equally simple.  Each `inductive` declaration defines
-- a set of data values that can be built up using the declared
-- constructors.  If we have in mind some proposition `P` that
-- mentions a list `l` and we want to argue that `P` holds for _all_
-- lists, we can reason as follows:
--
--   - First, show that `P` is true of `l` when `l` is `[]`.
--
--   - Then show that `P` is true of `l` when `l` is `n :: l'` for
--     some number `n` and some smaller list `l'`, assuming that `P`
--     is true for `l'`.
--
-- Here's a concrete example:

-- TERSE: Lean generates an induction principle for every `inductive`
-- definition, including lists.  We can use the `induction` tactic on
-- lists to prove things like the associativity of list-append...

theorem app_assoc : ∀ l1 l2 l3 : List Nat,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  intro l1 l2 l3
  induction l1 with
  | nil => rfl
  | cons n l1' ih =>
    simp [ih]

-- TERSE: ***
-- TERSE: For comparison, here is an informal proof of the same theorem.

-- _Theorem_: For all lists `l1`, `l2`, and `l3`,
--     `(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)`.
--
-- _Proof_: By induction on `l1`.
--
-- - First, suppose `l1 = []`.  We must show
--       `([] ++ l2) ++ l3 = [] ++ (l2 ++ l3)`,
--   which follows directly from the definition of `app`.
--
-- - Next, suppose `l1 = n :: l1'`, with
--       `(l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)`
--   (the induction hypothesis). We must show
--       `((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3)`.
--   By the definition of `app`, this follows from
--       `n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3))`,
--   which is immediate from the induction hypothesis.  _Qed_.

-- *** Generalizing Statements

-- FULL: In some situations, it is necessary to generalize a
-- statement in order to prove it by induction.  Intuitively, the
-- reason is that a more general statement also yields a more general
-- (stronger) inductive hypothesis.
-- TERSE: Sometimes statements need to be generalized to prove them
-- by induction:

-- myRepeat_double_firsttry
theorem myRepeat_double_firsttry : ∀ (c n : Nat),
  myRepeat n c ++ myRepeat n c = myRepeat n (c + c) := by
  intro c
  induction c with
  | zero => intro n; rfl
  | succ c' ih =>
    intro n
    simp [myRepeat]
    -- Now we seem to be stuck.  The IH only works for c' + c',
    -- but we need c' + (c' + 1).
    sorry

-- FULL: To get a more general inductive hypothesis, we can generalize:
-- TERSE: A generalization that gives a stronger inductive hypothesis:

theorem myRepeat_plus : ∀ (c1 c2 n : Nat),
  myRepeat n c1 ++ myRepeat n c2 = myRepeat n (c1 + c2) := by
  intro c1 c2 n
  induction c1 with
  | zero => simp [myRepeat]
  | succ c1' ih =>
    simp [myRepeat, Nat.succ_add, ih]

-- *** Reversing a List

-- FULL: For a slightly more involved example of inductive proof over
-- lists, suppose we use `app` to define a list-reversing function
-- `rev`:
-- TERSE: A more interesting example of induction over lists:

def rev (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => rev t ++ [h]

@[simp] theorem rev_nil : rev ([] : List Nat) = [] := rfl
@[simp] theorem rev_cons (h : Nat) (t : List Nat) : rev (h :: t) = rev t ++ [h] := rfl

-- test_rev1
example : rev [1, 2, 3] = [3, 2, 1] := by rfl
-- test_rev2
example : rev ([] : List Nat) = [] := by rfl

-- FULL: For something a bit more challenging, let's prove that
-- reversing a list does not change its length.  Our first attempt
-- gets stuck in the successor case...
-- TERSE: ***
-- TERSE: Let's try to prove `length (rev l) = length l`.

-- rev_length_firsttry
theorem rev_length_firsttry : ∀ l : List Nat,
  length (rev l) = length l := by
  intro l
  induction l with
  | nil => rfl
  | cons n l' ih =>
    simp [rev]
    -- Now we seem to be stuck: the goal involves `++`, but we
    -- don't have the right lemma yet.
    sorry

-- A useful lemma: appending a single element increases length by one.

theorem app_length_succ : ∀ (l : List Nat) (n : Nat),
  length (l ++ [n]) = (length l) + 1 := by
  intro l n
  induction l with
  | nil => rfl
  | cons m l' ih =>
    simp [length, ih]

-- TERSE: ***
-- Now we can prove the main theorem.

theorem rev_length : ∀ l : List Nat,
  length (rev l) = length l := by
  intro l
  induction l with
  | nil => rfl
  | cons n l' ih =>
    simp [rev, app_length_succ, ih, length]

-- TERSE: ***
-- FULL: We can also prove a more general form that gives the
-- length of any two appended lists.

-- app_length
theorem app_length : ∀ l1 l2 : List Nat,
  length (l1 ++ l2) = (length l1) + (length l2) := by
  -- WORKINCLASS
  intro l1 l2
  induction l1 with
  | nil => simp
  | cons n l1' ih =>
    simp [app_cons_l, length_cons, ih, Nat.succ_add]
-- /WORKINCLASS

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

theorem app_nil_r : ∀ l : List Nat,
  l ++ ([] : List Nat) = l := by
  -- ADMITTED
  intro l
  induction l with
  | nil => rfl
  | cons n l' ih => simp [ih]
-- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.app_nil_r

theorem rev_app_distr : ∀ l1 l2 : List Nat,
  rev (l1 ++ l2) = rev l2 ++ rev l1 := by
  -- ADMITTED
  intro l1 l2
  induction l1 with
  | nil => simp [rev, app_nil_r]
  | cons x l1' ih => simp [rev, ih, app_assoc]
-- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.rev_app_distr

-- An _involution_ is a function that is its own inverse. That is,
-- applying the function twice yields the original input.
theorem rev_involutive : ∀ l : List Nat,
  rev (rev l) = l := by
  -- ADMITTED
  intro l
  induction l with
  | nil => rfl
  | cons n l' ih => simp [rev, rev_app_distr, ih]
-- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.rev_involutive

-- There is a short solution to the next one.  If you find yourself
-- getting tangled up, step back and try to look for a simpler way.

theorem app_assoc4 : ∀ l1 l2 l3 l4 : List Nat,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4 := by
  -- ADMITTED
  intro l1 l2 l3 l4
  rw [app_assoc, app_assoc]
-- /ADMITTED
-- GRADE_THEOREM 0.5: NatList.app_assoc4

-- An exercise about your implementation of `nonzeros`:

-- nonzeros_app
theorem nonzeros_app : ∀ l1 l2 : List Nat,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2) := by
  -- ADMITTED
  intro l1 l2
  induction l1 with
  | nil => rfl
  | cons n l1' ih =>
    cases n with
    | zero => simp [nonzeros, ih]
    | succ n' => simp [nonzeros, ih]
-- /ADMITTED
-- GRADE_THEOREM 1: NatList.nonzeros_app
-- []

-- EX2 (eqblist)
-- GRADE_THEOREM 2: NatList.eqblist_refl
-- Fill in the definition of `eqblist`, which compares
-- lists of numbers for equality.  Prove that `eqblist l l`
-- yields `true` for every list `l`.

def eqblist (l1 l2 : List Nat) : Bool :=
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
theorem eqblist_refl : ∀ l : List Nat,
  eqblist l l = true := by
  -- ADMITTED
  intro l
  induction l with
  | nil => rfl
  | cons n l' ih => simp [eqblist, ih]
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

-- Here are a couple of little theorems to prove about your
-- definitions about bags above.

-- EX1 (count_member_nonzero)
-- count_member_nonzero
theorem count_member_nonzero : ∀ (s : Bag),
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
  induction n with
  | zero => rfl
  | succ n' ih => simp [Nat.ble, ih]

-- Before doing the next exercise, make sure you've filled in the
-- definition of `remove_one` above.
-- EX3A (remove_does_not_increase_count)

theorem remove_does_not_increase_count : ∀ (s : Bag),
  Nat.ble (count 0 (remove_one 0 s)) (count 0 s) = true := by
  -- ADMITTED
  intro s
  induction s with
  | nil => rfl
  | cons n s' ih =>
    cases n with
    | zero => simp [remove_one, count, leb_n_Sn]
    | succ n' => simp [remove_one, count, ih]
-- /ADMITTED
-- []

-- EX3M? (bag_count_sum)
-- Write down an interesting theorem `bag_count_sum` about bags
-- involving the functions `count` and `sum`, and prove it.
-- SOLUTION
theorem bag_count_sum : ∀ (s1 s2 : Bag) (v : Nat),
  count v (sum s1 s2) = count v s1 + count v s2 := by
  intro s1 s2 v
  induction s1 with
  | nil => simp [sum, app, count]
  | cons h s1' ih =>
    simp only [sum, app, count]
    cases (h == v) with
    | true => simp [Nat.succ_add]; exact ih
    | false => exact ih
-- /SOLUTION
-- []

-- EX3A (involution_injective)
-- Prove that every involution is injective.
--
-- Involutions were defined above in `rev_involutive`. An _injective_
-- function is one-to-one: it maps distinct inputs to distinct
-- outputs, without any collisions.

theorem involution_injective : ∀ (f : Nat → Nat),
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

theorem rev_injective : ∀ (l1 l2 : List Nat),
  rev l1 = rev l2 → l1 = l2 := by
  -- ADMITTED
  intro l1 l2 heq
  rw [← rev_involutive l1, ← rev_involutive l2, heq]
-- /ADMITTED
-- []

-- /FULL
-- ######################################################################
-- * Options

-- FULL: Suppose we want to write a function that returns the `n`th
-- element of some list.  If we give it type `List Nat → Nat → Nat`,
-- then we'll have to choose some number to return when the list is
-- too short...
-- TERSE: Suppose we'd like a function to retrieve the `n`th element
--     of a list.  What to do if the list is too short?

def nth_bad (l : List Nat) (n : Nat) : Nat :=
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
--
-- Lean's standard library provides `Option α` for this purpose:
--
--     inductive Option (α : Type) where
--       | none : Option α
--       | some (val : α) : Option α
--
-- We use `Option Nat` to represent "maybe a Nat".

-- TERSE: The solution: return an `Option Nat`.

def nth_error (l : List Nat) (n : Nat) : Option Nat :=
  match l with
  | [] => none
  | a :: l' => match n with
    | 0 => some a
    | n' + 1 => nth_error l' n'

-- test_nth_error1
example : nth_error [4, 5, 6, 7] 0 = some 4 := by rfl
-- test_nth_error2
example : nth_error [4, 5, 6, 7] 3 = some 7 := by rfl
-- test_nth_error3
example : nth_error [4, 5, 6, 7] 9 = none := by rfl

-- FULL

-- The function below pulls the `Nat` out of an `Option Nat`,
-- returning a supplied default in the `none` case.

def option_elim (d : Nat) (o : Option Nat) : Nat :=
  match o with
  | some n => n
  | none => d

-- EX2 (hd_error)
-- Using the same idea, fix the `hd` function from earlier so we
-- don't have to pass a default element for the `nil` case.

def hd_error (l : List Nat) : Option Nat :=
  -- ADMITDEF
  match l with
  | [] => none
  | h :: _ => some h
  -- /ADMITDEF

-- test_hd_error1
example : hd_error ([] : List Nat) = none := by rfl  -- ADMITTED
-- test_hd_error2
example : hd_error [1] = some 1 := by rfl  -- ADMITTED
-- test_hd_error3
example : hd_error [5, 6] = some 5 := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: test_hd_error1
-- GRADE_THEOREM 1: test_hd_error2
-- []

-- EX1? (option_elim_hd)
-- GRADE_THEOREM 1: NatList.option_elim_hd
-- This exercise relates your new `hd_error` to the old `hd`.

-- option_elim_hd
theorem option_elim_hd : ∀ (l : List Nat) (default : Nat),
  hd default l = option_elim default (hd_error l) := by
  -- ADMITTED
  intro l default
  cases l with
  | nil => rfl
  | cons n l' => rfl
-- /ADMITTED
-- []

-- /FULL
end NatList

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
  x1.val == x2.val

-- EX1 (eqb_id_refl)
-- GRADE_THEOREM 1: eqb_id_refl
-- eqb_id_refl
theorem eqb_id_refl : ∀ x : MyId, eqb_id x x = true := by
  -- ADMITTED
  intro ⟨n⟩
  simp [eqb_id]
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
  simp [update, find, eqb_id_refl]

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
  simp [update, find, h]

-- (A) True
-- (B) False
-- (C) Not sure
-- /QUIZ

-- FULL
-- EX1 (update_eq)
-- GRADE_THEOREM 1: PartialMap.update_eq
-- update_eq
theorem update_eq :
  ∀ (d : PartialMap) (x : MyId) (v : Nat),
    find x (update d x v) = some v := by
  -- ADMITTED
  intro d x v
  simp [update, find, eqb_id_refl]
-- /ADMITTED
-- []

-- EX1 (update_neq)
-- GRADE_THEOREM 1: PartialMap.update_neq
-- update_neq
theorem update_neq :
  ∀ (d : PartialMap) (x y : MyId) (o : Nat),
    eqb_id x y = false → find x (update d y o) = find x d := by
  -- ADMITTED
  intro d x y o h
  simp [update, find, h]
-- /ADMITTED
-- []
-- /FULL

end PartialMap
