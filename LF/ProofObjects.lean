-- ProofObjects: The Curry-Howard Correspondence

-- TERSE: HIDEFROMHTML
import LF.IndProp
-- /HIDEFROMHTML

-- "Algorithms are the computational content of proofs."
--     (Robert Harper)

-- FULL: We have seen that Lean has mechanisms both for _programming_,
-- using inductive data types like `Nat` or `List` and functions over
-- these types, and for _proving_ properties of these programs, using
-- inductive propositions (like `Ev`), implication, universal
-- quantification, and the like.  So far, we have mostly treated
-- these mechanisms as if they were quite separate, and for many
-- purposes this is a good way to think.  But we have also seen hints
-- that Lean's programming and proving facilities are closely related.
-- For example, the keyword `inductive` is used to declare both data
-- types and propositions, and `→` is used both to describe the type
-- of functions on data and logical implication.  This is not just a
-- syntactic accident!  In fact, programs and proofs in Lean are
-- _the same thing_.  In this chapter we will study this connection
-- in more detail.
--
-- In Lean, the Curry-Howard correspondence is even more visible than
-- in Rocq.  There is no separate "proof mode" -- tactics are just one
-- way of constructing terms.  Every proof is a term, and every term
-- of a `Prop` type is a proof.  We have already been exploiting this
-- throughout the book.
--
-- We have already seen the fundamental idea: provability in Lean is
-- always witnessed by _evidence_.  When we construct the proof of a
-- basic proposition, we are actually building a tree of evidence,
-- which can be thought of as a concrete data structure.
--
-- If the proposition is an implication like `A → B`, then its proof
-- is an evidence _transformer_: a recipe for converting evidence for
-- A into evidence for B.  So at a fundamental level, proofs are
-- simply programs that manipulate evidence.

-- Question: If evidence is data, what are propositions themselves?
--
-- Answer: They are types!

-- TERSE: ***
-- Look again at the formal definition of the `Ev` property.

-- (Recall from IndProp:)
--
--   inductive Ev : Nat → Prop where
--     | ev_0                        : Ev 0
--     | ev_SS (n : Nat) (H : Ev n)  : Ev (n + 2)

-- We can pronounce the ":" here as either "has type" or "is a proof
-- of."  For example, the second line in the definition of `Ev`
-- declares that `Ev.ev_0 : Ev 0`.  Instead of "`Ev.ev_0` has type
-- `Ev 0`," we can say that "`Ev.ev_0` is a proof of `Ev 0`."

-- TERSE: ***

-- This pun between types and propositions -- between `:` as "has type"
-- and `:` as "is a proof of" or "is evidence for" -- is called the
-- _Curry-Howard correspondence_.  It proposes a deep connection
-- between the world of logic and the world of computation:
--
--                  propositions  ~  types
--                  proofs        ~  programs
--
-- See Wadler 2015 for a brief history and modern exposition.

-- TERSE: ***
-- Many useful insights follow from this connection.  To begin with,
-- it gives us a natural interpretation of the type of the `Ev.ev_SS`
-- constructor:

-- The type of `Ev.ev_SS` says that it is a _function_ (better: a
-- data _constructor_) taking two arguments (one number `n` plus
-- evidence for `Ev n`) and returning evidence that `n + 2` is even.

#check @Ev.ev_SS
-- Ev.ev_SS : (n : Nat) → Ev n → Ev (n + 2)

-- This can be read "`Ev.ev_SS` is a constructor that takes two
-- arguments -- a number `n` and evidence for the proposition `Ev n`
-- -- and yields evidence for the proposition `Ev (n + 2)`."

-- TERSE: ***
-- Now let's look again at a proof involving `Ev`.

-- (These were already proved in IndProp, so we work in a namespace.)
namespace ProofObjects

-- ev_4_tactic
theorem ev_4_tactic : Ev 4 := by
  apply Ev.ev_SS; apply Ev.ev_SS; apply Ev.ev_0

-- Just as with ordinary data values and functions, we can use the
-- `#print` command to see the _proof object_ that results from this
-- proof script.

#print ev_4_tactic
-- ev_4_tactic = Ev.ev_SS 2 (Ev.ev_SS 0 Ev.ev_0)

-- TERSE: ***
-- Indeed, we can also write down this proof object directly,
-- with no need for a proof script at all:

#check (Ev.ev_SS 2 (Ev.ev_SS 0 Ev.ev_0) : Ev 4)

-- FULL: The expression `Ev.ev_SS 2 (Ev.ev_SS 0 Ev.ev_0)` instantiates
-- the parameterized constructor `Ev.ev_SS` with the specific arguments
-- `2` and `0` plus the corresponding proof objects for its premises
-- `Ev 2` and `Ev 0`.  Alternatively, we can think of `Ev.ev_SS` as a
-- primitive "evidence constructor" that, when applied to a particular
-- number, wants to be further applied to evidence that this number
-- is even; its type,
--
--       (n : Nat) → Ev n → Ev (n + 2)
--
-- expresses this functionality, in the same way that the polymorphic
-- type `{α : Type} → List α` expresses the fact that the constructor
-- `[]` can be thought of as a function from types to empty lists
-- with elements of that type.

-- FULL: Similarly, as we've seen, we can directly apply proof terms
-- using `exact`:

-- ev_4_exact
theorem ev_4_exact : Ev 4 := by
  exact (Ev.ev_SS 2 (Ev.ev_SS 0 Ev.ev_0))

-- ######################################################
-- * Proof Scripts

-- FULL: The _proof objects_ we've been discussing lie at the core of how
-- Lean operates.  When Lean is following a proof script, what is
-- happening internally is that it is gradually constructing a proof
-- object -- a term whose type is the proposition being proved.  The
-- tactics between `by` and the end of the block tell it how to build
-- up a term of the required type.

-- TERSE: When we write a proof using tactics, what we are doing is
-- instructing Lean to build a proof object under the hood.

-- In Lean, this is especially transparent: you can freely mix tactic
-- mode and term mode.  A `by` block is just another way of writing
-- a term.

-- ev_4_tactic'
theorem ev_4_tactic' : Ev 4 := by
  -- At this point Lean needs a term of type `Ev 4`.
  apply Ev.ev_SS
  -- Now Lean needs a term of type `Ev 2`.
  apply Ev.ev_SS
  -- Now Lean needs a term of type `Ev 0`.
  apply Ev.ev_0
  -- Done: the proof object is `Ev.ev_SS 2 (Ev.ev_SS 0 Ev.ev_0)`.

-- TERSE: ***
-- Tactic proofs are convenient, but they are not essential in Lean:
-- in principle, we can always just construct the required evidence
-- by hand. Then we can use `def` (rather than `theorem`) to
-- introduce a global name for this evidence.

-- ev_4_term
def ev_4_term : Ev 4 :=
  Ev.ev_SS 2 (Ev.ev_SS 0 Ev.ev_0)

-- FULL: All these different ways of building the proof lead to exactly the
-- same evidence being saved in the global environment.

#print ev_4_tactic
#print ev_4_exact
#print ev_4_tactic'
#print ev_4_term

-- FULL:
-- EX2 (eight_is_even)
-- Give a tactic proof and a proof object showing that `Ev 8`.

-- ev_8
theorem ev_8 : Ev 8 := by
  -- ADMITTED
  apply Ev.ev_SS; apply Ev.ev_SS; apply Ev.ev_SS; apply Ev.ev_SS
  exact Ev.ev_0
  -- /ADMITTED

-- ev_8'
-- ADMITDEF
def ev_8' : Ev 8 :=
  Ev.ev_SS 6 (Ev.ev_SS 4 (Ev.ev_SS 2 (Ev.ev_SS 0 Ev.ev_0)))
-- /ADMITDEF
-- GRADE_THEOREM 1: ev_8
-- GRADE_THEOREM 1: ev_8'

-- ######################################################
-- * Quantifiers, Implications, Functions

-- In Lean's computational universe (where data structures and
-- programs live), there are two sorts of values that have arrows in
-- their types: _constructors_ introduced by `inductive`ly defined
-- data types, and _functions_.
--
-- Similarly, in Lean's logical universe (where we carry out proofs),
-- there are two ways of giving evidence for an implication:
-- constructors introduced by `inductive`ly defined propositions,
-- and... functions!

-- TERSE: ***
-- For example, consider this statement:

-- ev_plus4_tactic
theorem ev_plus4_tactic : ∀ (n : Nat), Ev n → Ev (4 + n) := by
  intro n H
  have h : 4 + n = (n + 2) + 2 := by omega
  rw [h]
  exact Ev.ev_SS _ (Ev.ev_SS _ H)

-- What is the proof object corresponding to `ev_plus4_tactic`?

-- TERSE: ***

-- We're looking for an expression whose _type_ is `∀ n, Ev n →
-- Ev (4 + n)` -- that is, a _function_ that takes two arguments (one
-- number and a piece of evidence) and returns a piece of evidence!
--
-- Here it is:

-- Note: Because Lean's `Ev` uses `n + 2` rather than `S (S n)`,
-- the arithmetic `4 + n = (n + 2) + 2` requires a small rewrite.
-- In Rocq, where `ev` uses `S (S n)`, this would be definitionally
-- equal.  We use `Eq.mpr` with `omega` to handle this.

-- ev_plus4_term
def ev_plus4_term : ∀ (n : Nat), Ev n → Ev (4 + n) :=
  fun (n : Nat) (H : Ev n) =>
    -- Note: Because Lean's `Ev` uses `n + 2` rather than `S (S n)`,
    -- the types `Ev ((n + 2) + 2)` and `Ev (4 + n)` are not
    -- definitionally equal.  We use `▸` to rewrite.
    have h : (n + 2) + 2 = 4 + n := by omega
    h ▸ Ev.ev_SS (n + 2) (Ev.ev_SS n H)

-- FULL: Recall that `fun n => blah` means "the function that, given `n`,
-- yields `blah`."  Another equivalent way to write this definition is:

-- ev_plus4_term'
def ev_plus4_term' (n : Nat) (H : Ev n) : Ev (4 + n) :=
  have h : (n + 2) + 2 = 4 + n := by omega
  h ▸ Ev.ev_SS (n + 2) (Ev.ev_SS n H)

#check (ev_plus4_term' : ∀ (n : Nat), Ev n → Ev (4 + n))

-- TERSE: ***
-- When we view the proposition being proved by `ev_plus4` as a
-- function type, one interesting point becomes apparent: The second
-- argument's type, `Ev n`, mentions the _value_ of the first
-- argument, `n`.
--
-- While such _dependent types_ are not found in most mainstream
-- programming languages, they can be quite useful in programming
-- too, as the flurry of activity in the functional programming
-- community over the past couple of decades demonstrates.

-- TERSE: ***
-- Notice that both implication (`→`) and quantification (`∀`)
-- correspond to functions on evidence.  In fact, they are really the
-- same thing: `→` is just a shorthand for a degenerate use of
-- `∀` where there is no dependency, i.e., no need to give a
-- name to the type on the left-hand side of the arrow:
--
--            ∀ (x : Nat), Nat
--         =  ∀ (_ : Nat), Nat
--         =  Nat          → Nat

-- FULL: For example, consider this proposition:

def ev_plus2 : Prop :=
  ∀ (n : Nat), ∀ (_ : Ev n), Ev (n + 2)

-- FULL: A proof term inhabiting this proposition would be a function
-- with two arguments: a number `n` and some evidence that `n` is
-- even.  But the name for this evidence is not used in the rest
-- of the statement of `ev_plus2`, so it's a bit silly to bother
-- making up a name for it.  We could write it like this instead:

def ev_plus2' : Prop :=
  ∀ (n : Nat), Ev n → Ev (n + 2)

-- In general, `P → Q` is just syntactic sugar for `∀ (_ : P), Q`.


-- ######################################################
-- * Programming with Tactics

-- If we can build proofs by giving explicit terms rather than
-- executing tactic scripts, you may wonder whether we can build
-- _programs_ using tactics rather than by writing down explicit
-- terms.
--
-- Naturally, the answer is yes!

def add2 : Nat → Nat := by
  intro n
  exact n.succ.succ

#print add2
-- add2 = fun n => n.succ.succ

#eval add2 2
-- 4

-- FULL: Notice that we used `by` to enter tactic mode for building
-- a term of type `Nat → Nat`.  In Lean, unlike Rocq, there is no
-- distinction between `Defined` and `Qed` -- all definitions are
-- transparent by default.  (One can use `@[irreducible]` to make
-- a definition opaque if desired.)
--
-- This feature is mainly useful for writing functions with dependent
-- types, which we won't explore much further in this book.  But it
-- does illustrate the uniformity and orthogonality of the basic
-- ideas in Lean.


-- #################################################################
-- * Logical Connectives as Inductive Types

-- Inductive definitions are powerful enough to express most of the
-- logical connectives we have seen so far.  Indeed, only universal
-- quantification (with implication as a special case) is built into
-- Lean; all the others are defined inductively.
--
-- Let's see how.

-- ** Conjunction

-- To prove that `P ∧ Q` holds, we must present evidence for both
-- `P` and `Q`.  Thus, it makes sense to define a proof object for
-- `P ∧ Q` to consist of a pair of two proofs: one for `P` and
-- another one for `Q`. This leads to the following definition.

namespace MyAnd

inductive And (P Q : Prop) : Prop where
  | intro : P → Q → And P Q

-- Notice the similarity with the definition of the `Prod` type,
-- given in chapter Poly; the only difference is that `Prod` takes
-- `Type` arguments, whereas `And` takes `Prop` arguments.

#print Prod
-- structure Prod (α : Type u_1) (β : Type u_2) ...

-- TERSE: ***
-- This similarity should clarify why pattern matching (via `match`
-- or `obtain`) can be used on a conjunctive hypothesis.  Case analysis
-- allows us to consider all possible ways in which `P ∧ Q` was
-- proved -- here just one (the `And.intro` constructor).

-- proj1'
theorem proj1' (P Q : Prop) (HPQ : And P Q) : P :=
  match HPQ with
  | And.intro hp _ => hp

-- Similarly, the `constructor` tactic works for any inductively
-- defined proposition with exactly one constructor.  In particular,
-- it works for `And`:

-- and_comm
theorem and_comm' (P Q : Prop) : And P Q ↔ And Q P where
  mp := fun ⟨hp, hq⟩ => ⟨hq, hp⟩
  mpr := fun ⟨hq, hp⟩ => ⟨hp, hq⟩

end MyAnd

-- TERSE: ***
-- This shows why the inductive definition of `And` can be
-- manipulated by tactics as we've been doing.  We can also use it to
-- build proofs directly, using pattern-matching.  For instance:

-- (Using Lean's built-in `And` now:)

-- proj1''
def proj1'' (P Q : Prop) (HPQ : P ∧ Q) : P :=
  match HPQ with
  | ⟨hp, _⟩ => hp

-- and_comm'_aux
def and_comm'_aux (P Q : Prop) (H : P ∧ Q) : Q ∧ P :=
  match H with
  | ⟨hp, hq⟩ => ⟨hq, hp⟩

-- and_comm''
def and_comm'' (P Q : Prop) : P ∧ Q ↔ Q ∧ P :=
  ⟨and_comm'_aux P Q, and_comm'_aux Q P⟩

-- FULL:
-- EX2 (conj_fact)
-- Construct a proof object for the following proposition.

-- conj_fact
-- ADMITDEF
def conj_fact : ∀ (P Q R : Prop), P ∧ Q → Q ∧ R → P ∧ R :=
  fun _ _ _ HPQ HQR =>
    match HPQ, HQR with
    | ⟨hp, _⟩, ⟨_, hr⟩ => ⟨hp, hr⟩
-- /ADMITDEF

-- ** Disjunction

-- The inductive definition of disjunction uses two constructors, one
-- for each side of the disjunction:

namespace MyOr

inductive Or (P Q : Prop) : Prop where
  | inl : P → Or P Q
  | inr : Q → Or P Q

-- This declaration explains the behavior of the `cases` tactic on
-- a disjunctive hypothesis, since the generated subgoals match the
-- shape of the `Or.inl` and `Or.inr` constructors.

-- TERSE: ***
-- Once again, we can also directly write proof objects for theorems
-- involving `Or`, without resorting to tactics.

-- inj_l
def inj_l (P Q : Prop) (HP : P) : Or P Q :=
  Or.inl HP

-- inj_l'
theorem inj_l' (P Q : Prop) (HP : P) : Or P Q := by
  exact Or.inl HP

-- TERSE: ***

-- or_elim
def or_elim (P Q R : Prop) (HPQ : Or P Q) (HPR : P → R) (HQR : Q → R) : R :=
  match HPQ with
  | Or.inl hp => HPR hp
  | Or.inr hq => HQR hq

-- or_elim'
theorem or_elim' (P Q R : Prop) (HPQ : Or P Q) (HPR : P → R) (HQR : Q → R) : R := by
  cases HPQ with
  | inl hp => exact HPR hp
  | inr hq => exact HQR hq

end MyOr

-- FULL:
-- EX2 (or_commut')
-- Construct a proof object for the following proposition.

-- or_commut'
-- ADMITDEF
def or_commut' : ∀ (P Q : Prop), P ∨ Q → Q ∨ P :=
  fun _ _ H =>
    match H with
    | Or.inl hp => Or.inr hp
    | Or.inr hq => Or.inl hq
-- /ADMITDEF

-- ** Existential Quantification

-- To give evidence for an existential quantifier, we package a
-- witness `x` together with a proof that `x` satisfies the property
-- `P`:

namespace MyEx

inductive Ex {A : Type} (P : A → Prop) : Prop where
  | intro : ∀ (x : A), P x → Ex P

end MyEx

-- FULL: This probably needs a little unpacking.  The core definition is
-- for a type former `Ex` that can be used to build propositions of
-- the form `Ex P`, where `P` itself is a _function_ from witness
-- values in the type `A` to propositions.  The `intro` constructor
-- then offers a way of constructing evidence for `Ex P`, given a
-- witness `x` and a proof of `P x`.
--
-- In Lean's standard library, this is `Exists` (with notation
-- `∃ x, P x`).

-- TERSE: ***
-- The more familiar form `∃ n, Ev n` desugars to an expression
-- involving `Exists`:

#check (⟨4, Ev.ev_SS 2 (Ev.ev_SS 0 Ev.ev_0)⟩ : ∃ n, Ev n)

-- Here's how to define an explicit proof object involving `Exists`:

-- some_nat_is_even
def some_nat_is_even : ∃ n, Ev n :=
  ⟨4, Ev.ev_SS 2 (Ev.ev_SS 0 Ev.ev_0)⟩

-- FULL:
-- EX2 (ex_ev_Sn)
-- Construct a proof object for the following proposition.

-- ex_ev_Sn
-- ADMITDEF
def ex_ev_Sn : ∃ n, Ev (n + 1) :=
  ⟨1, Ev.ev_SS 0 Ev.ev_0⟩
-- /ADMITDEF

-- TERSE: ***
-- To destruct existentials in a proof term we use pattern matching:

-- dist_exists_or_term
def dist_exists_or_term {X : Type} (P Q : X → Prop) :
    (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x) :=
  fun H => match H with
           | ⟨x, Or.inl hpx⟩ => Or.inl ⟨x, hpx⟩
           | ⟨x, Or.inr hqx⟩ => Or.inr ⟨x, hqx⟩

-- FULL:
-- EX2 (ex_match)
-- Construct a proof object for the following proposition:

-- ex_match
-- ADMITDEF
def ex_match : ∀ (A : Type) (P Q : A → Prop),
    (∀ (x : A), P x → Q x) →
    (∃ x, P x) → (∃ x, Q x) :=
  fun _ _ _ HPQ HP =>
    match HP with
    | ⟨x, hpx⟩ => ⟨x, HPQ x hpx⟩
-- /ADMITDEF

-- ** `True` and `False`

-- The inductive definition of the `True` proposition is simple:

-- (In Lean's core library:)
-- inductive True : Prop where
--   | intro : True

-- It has one constructor (so every proof of `True` is the same, so
-- being given a proof of `True` is not informative.)

-- FULL:
-- EX1 (p_implies_true)
-- Construct a proof object for the following proposition.

-- p_implies_true
-- ADMITDEF
def p_implies_true : ∀ (P : Prop), P → True :=
  fun _ _ => True.intro
-- /ADMITDEF

-- TERSE: ***

-- `False` is equally simple -- indeed, so simple it may look
-- syntactically wrong at first glance!

-- (In Lean's core library:)
-- inductive False : Prop where

-- That is, `False` is an inductive type with _no_ constructors --
-- i.e., no way to build evidence for it.

-- TERSE: ***
-- But it is possible to destruct `False` by pattern matching. There can
-- be no patterns that match it, since it has no constructors.  So
-- the pattern match also is so simple it may look syntactically
-- wrong at first glance.

-- In Lean, we use `nomatch` or `False.elim` for this:

-- false_implies_zero_eq_one
def false_implies_zero_eq_one : False → 0 = 1 :=
  fun contra => nomatch contra

-- Since there are no branches to evaluate, the expression
-- can be considered to have any type we want, including `0 = 1`.
-- Fortunately, it's impossible to ever cause it to be
-- evaluated, because we can never construct a value of type `False`
-- to pass to the function.

-- FULL:
-- EX1 (ex_falso_quodlibet')
-- Construct a proof object for the following proposition.

-- ex_falso_quodlibet'
-- ADMITDEF
def ex_falso_quodlibet' : ∀ (P : Prop), False → P :=
  fun _ contra => nomatch contra
-- /ADMITDEF

-- ######################################################
-- * Equality

-- Even Lean's equality relation is not built in as a primitive
-- operation in the traditional sense.  It is defined inductively.
-- We can define our own version:

namespace EqualityPlayground

-- Here we define our own equality, mirroring the structure of Lean's
-- built-in `Eq`.  The first argument is a _parameter_ (fixed for all
-- constructors) while the second is an _index_:

inductive MyEq {X : Type} (x : X) : X → Prop where
  | refl : MyEq x x

-- (This is essentially the same as Lean's built-in `Eq`:
--   inductive Eq {α : Sort u} (a : α) : α → Prop where
--     | refl : Eq a a
-- The Rocq version uses both arguments as indices, but in Lean
-- having the first argument as a parameter works better for
-- pattern matching and gives a better induction principle.)

scoped infix:50 " === " => MyEq

-- FULL: The way to think about this definition is that, given a set `X`,
-- it defines a _family_ of propositions "`x` is equal to `y`," indexed
-- by pairs of values (`x` and `y`) from `X`.  There is just one way
-- of constructing evidence for members of this family: applying the
-- constructor `MyEq.refl` to a type `X` and a single value `x : X`,
-- which yields evidence that `x` is equal to `x`.
--
-- Other types of the form `MyEq x y` where `x` and `y` are not the
-- same are thus uninhabited.

-- TERSE: ***

-- FULL: We can use `MyEq.refl` to construct evidence that, for example,
-- `2 = 2`. Can we also use it to construct evidence that `1 + 1 = 2`?
-- Yes, we can.  Indeed, it is the very same piece of evidence!
--
-- The reason is that Lean treats as "the same" any two terms that are
-- _convertible_ according to a simple set of computation rules.
--
-- These rules include evaluation of function application, inlining of
-- definitions, and simplification of `match`es.

-- TERSE: Lean terms are "the same" if they are _convertible_
-- according to a simple set of computation rules: evaluation of
-- function applications, inlining of definitions, and simplification
-- of `match`es.

-- four
theorem four_eq : 2 + 2 === 1 + 3 :=
  MyEq.refl

-- TERSE: ***
-- TERSE: `rfl` is essentially just `Eq.refl _`.

-- FULL: The `rfl` tactic that we have used to prove equalities up
-- to now is essentially just shorthand for `Eq.refl _`.
--
-- In tactic-based proofs of equality, the conversion rules are
-- normally hidden in uses of `simp` or `rfl`.  But you can see them
-- directly at work in the following explicit proof objects:

-- four'
def four' : 2 + 2 === 1 + 3 :=
  MyEq.refl

-- singleton
def singleton (X : Type) (x : X) : [] ++ [x] === [x] :=
  MyEq.refl

-- TERSE: ***
-- We can also pattern-match on an equality proof:

-- eq_add
def eq_add (n1 n2 : Nat) (Heq : n1 === n2) : (n1 + 1) === (n2 + 1) :=
  match Heq with
  | .refl => .refl

-- FULL: By pattern-matching against `n1 === n2`, we learn that `n2` is
-- the same as `n1`.  The goal becomes `(n1 + 1) === (n1 + 1)`, which
-- we establish by `.refl`.

-- TERSE: ***
-- A tactic-based proof can use `cases`:

-- eq_add'
theorem eq_add' (n1 n2 : Nat) (Heq : n1 === n2) : (n1 + 1) === (n2 + 1) := by
  cases Heq
  exact MyEq.refl

-- FULL:
-- EX2 (eq_cons)
-- Construct the proof object for the following theorem. Use pattern
-- matching on the equality hypotheses.

-- eq_cons
-- ADMITDEF
def eq_cons (X : Type) (h1 h2 : X) (t1 t2 : List X)
    (Heq : h1 === h2) (Teq : t1 === t2) : (h1 :: t1) === (h2 :: t2) :=
  match Heq, Teq with
  | .refl, .refl => .refl
-- /ADMITDEF

-- EX2 (equality__leibniz_equality)
-- The inductive definition of equality implies _Leibniz equality_:
-- what we mean when we say "`x` and `y` are equal" is that every
-- property `P` that is true of `x` is also true of `y`. Prove that.

-- equality__leibniz_equality
theorem equality__leibniz_equality (X : Type) (x y : X)
    (Heq : x === y) (P : X → Prop) (HPx : P x) : P y := by
  -- ADMITTED
  cases Heq
  exact HPx
  -- /ADMITTED

-- EX2 (equality__leibniz_equality_term)
-- Construct the proof object for the previous exercise.  All it
-- requires is anonymous functions and pattern-matching.

-- equality__leibniz_equality_term
-- ADMITDEF
def equality__leibniz_equality_term (X : Type) (x y : X)
    (Heq : x === y) (P : X → Prop) (HPx : P x) : P y :=
  match Heq with
  | .refl => HPx
-- /ADMITDEF

-- EX3? (leibniz_equality__equality)
-- Show that, in fact, the inductive definition of equality is
-- _equivalent_ to Leibniz equality.  Hint: the proof is quite short;
-- about all you need to do is to invent a clever property `P` to
-- instantiate the antecedent.

-- leibniz_equality__equality
theorem leibniz_equality__equality (X : Type) (x y : X)
    (H : ∀ (P : X → Prop), P x → P y) : x === y :=
  -- ADMITTED
  H (fun z => x === z) MyEq.refl
  -- /ADMITTED

end EqualityPlayground

-- ######################################################
-- * Lean's Trusted Computing Base

-- FULL: One question that arises with any automated proof assistant
-- is "why should we trust it?" -- i.e., what if there is a bug in
-- the implementation that renders all its reasoning suspect?
--
-- While it is impossible to allay such concerns completely, the fact
-- that Lean is based on the Curry-Howard correspondence gives it a
-- strong foundation. Because propositions are just types and proofs
-- are just terms, checking that an alleged proof of a proposition is
-- valid just amounts to _type-checking_ the term.  Type checkers are
-- relatively small and straightforward programs, so the "trusted
-- computing base" for Lean -- the part of the code that we have to
-- believe is operating correctly -- is small too.
--
-- What must a typechecker do?  Its primary job is to make sure that
-- in each function application the expected and actual argument
-- types match, that the arms of a `match` expression are constructor
-- patterns belonging to the inductive type being matched over and
-- all arms of the `match` return the same type, and so on.
--
-- There are a few additional wrinkles:
--
-- First, since Lean types can themselves be expressions, the checker
-- must normalize these (by using the computation rules) before
-- comparing them.
--
-- Second, the checker must make sure that `match` expressions are
-- _exhaustive_.  That is, there must be an arm for every possible
-- constructor.

-- TERSE: The Lean typechecker is what actually checks our proofs.  We
-- have to trust it, but it's relatively small and straightforward.

-- For example, Lean rejects this broken proof:
-- (Uncomment to see the error:)
-- def or_bogus : ∀ (P Q : Prop), P ∨ Q → P :=
--   fun (P Q : Prop) (A : P ∨ Q) =>
--     match A with
--     | Or.inl H => H

-- FULL: All the types here match correctly, but the `match` only
-- considers one of the possible constructors for `Or`.  Lean's
-- exhaustiveness check will reject this definition.
--
-- Third, the checker must make sure that each recursive function
-- terminates.  Lean does this using a structural or well-founded
-- recursion check.  To see why this is essential, consider this
-- alleged proof:

-- (Uncomment to see the error:)
-- def infinite_loop {X : Type} (n : Nat) : X :=
--   infinite_loop n

-- FULL: Were Lean to allow `infinite_loop`, then `False` would be
-- provable via `infinite_loop 0 : False`.  So Lean rejects
-- `infinite_loop`.

-- FULL: Note that the soundness of Lean depends only on the
-- correctness of this typechecking engine, not on the tactic
-- machinery.  If there is a bug in a tactic implementation (which
-- does happen occasionally), that tactic might construct an invalid
-- proof term.  But the kernel checks the term for validity from
-- scratch.  Only theorems whose proofs pass the type-checker can be
-- used in further proof developments.

-- TERSE: The tactic language and its implementation are _not_ part
-- of Lean's TCB.  Lean's kernel checks all proof terms for validity
-- regardless of how they were constructed.

-- FULL:
-- ######################################################
-- * More Exercises

-- Most of the following theorems were already proved with tactics in
-- Logic.  Now construct the proof objects for them directly.

-- EX2 (and_assoc)

-- and_assoc'
-- ADMITDEF
def and_assoc' : ∀ (P Q R : Prop),
    P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
  fun _ _ _ H =>
    match H with
    | ⟨hp, ⟨hq, hr⟩⟩ => ⟨⟨hp, hq⟩, hr⟩
-- /ADMITDEF

-- EX3 (or_distributes_over_and)

-- or_distributes_over_and'
-- ADMITDEF
def or_distributes_over_and' : ∀ (P Q R : Prop),
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
  fun _ _ _ =>
  ⟨fun H =>
     match H with
     | Or.inl hp => ⟨Or.inl hp, Or.inl hp⟩
     | Or.inr ⟨hq, hr⟩ => ⟨Or.inr hq, Or.inr hr⟩,
   fun H =>
     match H with
     | ⟨Or.inl hp, _⟩ => Or.inl hp
     | ⟨_, Or.inl hp⟩ => Or.inl hp
     | ⟨Or.inr hq, Or.inr hr⟩ => Or.inr ⟨hq, hr⟩⟩
-- /ADMITDEF

-- EX3 (negations)

-- double_neg'
-- ADMITDEF
def double_neg' : ∀ (P : Prop), P → ¬¬P :=
  fun _ hp notP => notP hp
-- /ADMITDEF
-- GRADE_THEOREM 1: double_neg

-- contradiction_implies_anything'
-- ADMITDEF
def contradiction_implies_anything' : ∀ (P Q : Prop), (P ∧ ¬P) → Q :=
  fun _ _ H =>
    match H with
    | ⟨hp, hnp⟩ => absurd hp hnp
-- /ADMITDEF
-- GRADE_THEOREM 1: contradiction_implies_anything

-- de_morgan_not_or'
-- ADMITDEF
def de_morgan_not_or' : ∀ (P Q : Prop), ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  fun _ _ H =>
    ⟨fun hp => H (Or.inl hp), fun hq => H (Or.inr hq)⟩
-- /ADMITDEF
-- GRADE_THEOREM 1: de_morgan_not_or

-- EX2 (currying)

-- curry'
-- ADMITDEF
def curry' : ∀ (P Q R : Prop), ((P ∧ Q) → R) → (P → (Q → R)) :=
  fun _ _ _ H hp hq => H ⟨hp, hq⟩
-- /ADMITDEF
-- GRADE_THEOREM 1: curry

-- uncurry'
-- ADMITDEF
def uncurry' : ∀ (P Q R : Prop), (P → (Q → R)) → ((P ∧ Q) → R) :=
  fun _ _ _ H ⟨hp, hq⟩ => H hp hq
-- /ADMITDEF
-- GRADE_THEOREM 1: uncurry

-- ######################################################
-- * Proof Irrelevance

-- FULL: In the Logic chapter we saw that functional extensionality could
-- be added to Lean as an axiom (though Lean actually provides it).
-- A similar notion about propositions can also be defined:

def propositional_extensionality_prop : Prop :=
  ∀ (P Q : Prop), (P ↔ Q) → P = Q

-- Propositional extensionality asserts that if two propositions are
-- equivalent -- i.e., each implies the other -- then they are in
-- fact equal. The _proof objects_ for the propositions might be
-- syntactically different terms. But propositional extensionality
-- overlooks that, just as functional extensionality overlooks the
-- syntactic differences between functions.
--
-- **Important Lean-specific note:** Unlike Rocq, Lean has _proof
-- irrelevance_ built in as a fundamental property of the type theory.
-- In Lean, any two proofs of the same proposition in `Prop` are
-- _definitionally_ equal.  That is, if `h1 h2 : P` where `P : Prop`,
-- then `h1 = h2` is true by `rfl`.  This means proof irrelevance
-- does not need to be assumed as an axiom in Lean -- it is automatic.
--
-- This is a significant difference from Rocq, where proof objects
-- can be inspected and distinguished (though `Qed`-defined proofs
-- are opaque).

-- Nonetheless, propositional extensionality is _not_ automatic in
-- Lean (it is available as `propext` in the core library).  Let us
-- explore its consequences.

-- EX1A (pe_implies_or_eq)
-- Prove the following consequence of propositional extensionality.

-- pe_implies_or_eq
theorem pe_implies_or_eq :
    propositional_extensionality_prop →
    ∀ (P Q : Prop), (P ∨ Q) = (Q ∨ P) := by
  -- ADMITTED
  intro PE P Q
  apply PE
  exact Or.comm
  -- /ADMITTED

-- EX1A (pe_implies_true_eq)
-- Prove that if a proposition `P` is provable, then it is equal to
-- `True` -- as a consequence of propositional extensionality.

-- pe_implies_true_eq
theorem pe_implies_true_eq :
    propositional_extensionality_prop →
    ∀ (P : Prop), P → True = P := by
  -- ADMITTED
  intro PE P hp
  apply PE
  exact ⟨fun _ => hp, fun _ => True.intro⟩
  -- /ADMITTED

-- EX3A (pe_implies_pi)
-- Another, perhaps surprising, consequence of propositional
-- extensionality is that it implies _proof irrelevance_, which
-- asserts that all proof objects for a proposition are equal.
--
-- **Lean note:** As mentioned above, Lean _already has_ proof
-- irrelevance built in!  So this exercise is somewhat artificial
-- in the Lean setting -- we can prove `proof_irrelevance` directly
-- without using propositional extensionality at all.  But we include
-- it for completeness of the translation.

def proof_irrelevance_prop : Prop :=
  ∀ (P : Prop) (pf1 pf2 : P), pf1 = pf2

-- In Lean, proof irrelevance is built in, so we can prove this
-- directly:
theorem proof_irrelevance_lean : proof_irrelevance_prop :=
  fun _ _ _ => rfl

-- But following the Rocq development, here is a proof that uses
-- propositional extensionality:

-- pe_implies_pi
theorem pe_implies_pi :
    propositional_extensionality_prop → proof_irrelevance_prop := by
  -- ADMITTED
  intro _PE P pf1 pf2
  -- In Lean, this is trivially true due to proof irrelevance:
  rfl
  -- /ADMITTED

end ProofObjects
