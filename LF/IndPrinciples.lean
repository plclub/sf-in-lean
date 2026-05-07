-- IndPrinciples: Induction Principles

-- FULL: Every time we declare a new `inductive` datatype, Lean
-- automatically generates an _induction principle_ (called a
-- _recursor_) for this type.  This induction principle is a theorem
-- like any other: if `T` is defined inductively, the corresponding
-- recursor is called `T.rec`.

-- TERSE: Let's take a deeper look at induction.

-- HIDEFROMHTML
import LF.ProofObjects
-- /HIDEFROMHTML

-- ######################################################################
-- * Basics

-- FULL: Here is the induction principle (recursor) for natural numbers:

-- TERSE: The automatically generated _recursor_ for `Nat`:

-- In Lean, the recursor is `@Nat.rec`:
#check @Nat.rec
-- Nat.rec : {motive : Nat → Sort u} →
--   motive 0 → ((n : Nat) → motive n → motive (n + 1)) → (t : Nat) → motive t

-- For proving `Prop`s specifically, we can use `@Nat.rec` with
-- `motive : Nat → Prop`:
-- It says: to show `P n` for all `n`, show `P 0` and show that
-- `P n → P (n + 1)`.

-- TERSE: ***

-- FULL: The `induction` tactic is a straightforward wrapper that, at
-- its core, applies the recursor.  To see this more clearly,
-- let's experiment with directly using `apply Nat.rec`, instead of
-- the `induction` tactic, to carry out some proofs.

-- TERSE: We can directly use the recursor with `exact/apply`:

-- mul_0_r'
theorem mul_0_r' : ∀ (n : Nat),
  n * 0 = 0 := by
  apply Nat.rec
  · -- n = 0
    rfl
  · -- n = n' + 1
    intro n' ih
    simp [Nat.add_mul, ih]

-- FULL: This proof is basically the same as the earlier one, but a
-- few minor differences are worth noting.
--
-- First, in the induction step of the proof (the successor case), we
-- have to do a little bookkeeping manually (`intro`) that
-- `induction` does automatically.
--
-- Second, we do not introduce `n` into the context before applying
-- `Nat.rec` -- the conclusion of `Nat.rec` is a quantified formula,
-- and `apply` needs this conclusion to exactly match the shape of
-- the goal state, including the quantifier.
--
-- Third, we had to manually supply the name of the recursor
-- with `apply`, but `induction` figures that out itself.
--
-- These conveniences make `induction` nicer to use in practice than
-- applying recursors like `Nat.rec` directly.  But it is
-- important to realize that, modulo these bits of bookkeeping,
-- applying `Nat.rec` is what we are really doing.

-- TERSE: Why the `induction` tactic is nicer than `apply`:
--  - `apply` requires extra manual bookkeeping (the `intro` in the
--    inductive case)
--  - `apply` requires `n` to be left universally quantified
--  - `apply` requires us to manually specify the name of the
--    recursor.

-- TERSE: ***

-- FULL
-- EX2 (plus_one_r')
-- Complete this proof without using the `induction` tactic.

-- plus_one_r'
theorem plus_one_r' : ∀ (n : Nat),
  n + 1 = n.succ := by
  -- ADMITTED
  apply Nat.rec
  · rfl
  · intro n' ih
    omega
-- /ADMITTED
-- []
-- /FULL

-- FULL: Lean generates recursors for every datatype defined with
-- `inductive`, including those that aren't recursive.  Although of
-- course we don't need the proof technique of induction to prove
-- properties of non-recursive datatypes, the idea of an induction
-- principle still makes sense for them: it gives a way to prove that
-- a property holds for all values of the type.

-- TERSE: ***
-- TERSE: Lean generates recursors for every datatype defined with
-- `inductive`, including those that aren't recursive.

-- TERSE: An example with no constructor arguments:

inductive Time : Type where
  | day
  | night

#check @Time.rec
-- Time.rec : {motive : Time → Sort u} →
--   motive Time.day → motive Time.night → (t : Time) → motive t

-- TERSE: ***

-- FULL
-- EX1? (rgb)
-- Write out the induction principle that Lean will generate for the
-- following datatype.  Write down your answer on paper or type it
-- into a comment, and then compare it with what Lean prints.

-- (RGB is already defined in Basics, but let's define it locally)
namespace IndPrinciplesExamples

inductive RGB : Type where
  | red | green | blue

#check @RGB.rec
-- []
-- /FULL

-- TERSE: ***
-- TERSE: An example with constructor arguments:

inductive NatList : Type where
  | nnil
  | ncons (n : Nat) (l : NatList)

#check @NatList.rec
-- NatList.rec : {motive : NatList → Sort u} →
--   motive NatList.nnil →
--   ((n : Nat) → (l : NatList) → motive l → motive (NatList.ncons n l)) →
--   (t : NatList) → motive t

-- TERSE: ***

-- In general, the automatically generated recursor for inductive
-- type `T` is formed as follows:
--
-- - Each constructor `c` generates one case of the principle.
-- - If `c` takes no arguments, that case is: "P holds of c"
-- - If `c` takes arguments `x1:a1 ... xn:an`, that case is:
--   "For all x1:a1 ... xn:an,
--       if P holds of each argument of type T,
--       then P holds of c x1 ... xn"

-- TERSE: ***

-- For example, suppose we had written a list definition differently:

inductive NatList' : Type where
  | nnil'
  | nsnoc (l : NatList') (n : Nat)

-- Now the recursor case for `nsnoc` is different:
#check @NatList'.rec
-- The induction hypothesis for `l` appears before the `n` argument.

-- FULL
-- EX2 (booltree_ind)
-- Here is a type for trees that contain a boolean value at each leaf
-- and branch.

inductive BoolTree : Type where
  | bt_empty
  | bt_leaf (b : Bool)
  | bt_branch (b : Bool) (t1 t2 : BoolTree)

-- What is the induction principle for `BoolTree`? Write it down,
-- then check.

def BoolTreePropertyType := BoolTree → Prop

def baseCase (P : BoolTreePropertyType) : Prop :=
  -- ADMITDEF
  P .bt_empty
  -- /ADMITDEF

def leafCase (P : BoolTreePropertyType) : Prop :=
  -- ADMITDEF
  ∀ (b : Bool), P (.bt_leaf b)
  -- /ADMITDEF

def branchCase (P : BoolTreePropertyType) : Prop :=
  -- ADMITDEF
  ∀ (b : Bool) (t1 : BoolTree), P t1 → ∀ (t2 : BoolTree), P t2 → P (.bt_branch b t1 t2)
  -- /ADMITDEF

def booltreeIndType :=
  ∀ (P : BoolTreePropertyType),
    baseCase P →
    leafCase P →
    branchCase P →
    ∀ (b : BoolTree), P b

-- booltree_ind_type_correct
theorem booltree_ind_type_correct : booltreeIndType := by
  -- ADMITTED
  intro P hbase hleaf hbranch b
  induction b with
  | bt_empty => exact hbase
  | bt_leaf b => exact hleaf b
  | bt_branch b t1 t2 ih1 ih2 => exact hbranch b t1 ih1 t2 ih2
-- /ADMITTED

-- GRADE_THEOREM 2: booltree_ind_type_correct
-- []
-- /FULL

-- FULL
-- EX2 (toy_ind)
-- Here is an induction principle for a toy type:
--
--   ∀ (P : Toy → Prop),
--     (∀ (b : Bool), P (con1 b)) →
--     (∀ (n : Nat) (t : Toy), P t → P (con2 n t)) →
--     ∀ (t : Toy), P t
--
-- Give an inductive definition of `Toy`:

inductive Toy : Type where
  -- SOLUTION
  | con1 (b : Bool)
  | con2 (n : Nat) (t : Toy)
  -- /SOLUTION

-- toy_correct
theorem toy_correct : ∃ (f : Bool → Toy) (g : Nat → Toy → Toy),
  ∀ (P : Toy → Prop),
    (∀ (b : Bool), P (f b)) →
    (∀ (n : Nat) (t : Toy), P t → P (g n t)) →
    ∀ (t : Toy), P t := by
  -- ADMITTED
  exact ⟨Toy.con1, Toy.con2, fun P hc1 hc2 t => Toy.rec hc1 (fun n t ih => hc2 n t ih) t⟩
-- /ADMITTED

-- GRADE_THEOREM 2: toy_correct
-- []
-- /FULL

end IndPrinciplesExamples

-- FULL
-- ######################################################################
-- * Polymorphism

-- What about polymorphic datatypes?
--
-- The inductive definition of polymorphic lists
--
--     inductive List (α : Type) : Type where
--       | nil : List α
--       | cons : α → List α → List α
--
-- is very similar to that of `NatList`.  The main difference is
-- that, here, the whole definition is _parameterized_ on a type `α`.

-- TERSE: ***

-- The recursor is likewise parameterized on `α`:
#check @List.rec
-- List.rec : {α : Type u_1} → {motive : List α → Sort u} →
--   motive [] → ((head : α) → (tail : List α) → motive tail → motive (head :: tail)) →
--   (t : List α) → motive t

-- EX1? (tree)
-- Write out the induction principle that Lean will generate for
-- the following datatype.

inductive MyTree (α : Type) : Type where
  | leaf (x : α)
  | node (t1 t2 : MyTree α)

#check @MyTree.rec
-- []

-- EX1? (mytype)
-- Find an inductive definition that gives rise to the
-- following induction principle:
--
--   ∀ {α : Type} (P : MyType α → Prop),
--     (∀ (x : α), P (constr1 x)) →
--     (∀ (n : Nat), P (constr2 n)) →
--     (∀ (m : MyType α), P m → ∀ (n : Nat), P (constr3 m n)) →
--     ∀ (m : MyType α), P m

-- QUIETSOLUTION
inductive MyType (α : Type) : Type where
  | constr1 (x : α)
  | constr2 (n : Nat)
  | constr3 (m : MyType α) (n : Nat)

#check @MyType.rec
-- /QUIETSOLUTION
-- []

-- EX1? (foo)
-- Find an inductive definition that gives rise to the
-- following induction principle:
--
--   ∀ {α β : Type} (P : Foo α β → Prop),
--     (∀ (x : α), P (bar x)) →
--     (∀ (y : β), P (baz y)) →
--     (∀ (f : Nat → Foo α β), (∀ (n : Nat), P (f n)) → P (quux f)) →
--     ∀ (f : Foo α β), P f

-- QUIETSOLUTION
inductive Foo (α : Type) (β : Type) : Type where
  | bar (x : α)
  | baz (y : β)
  | quux (f : Nat → Foo α β)

#check @Foo.rec
-- /QUIETSOLUTION
-- []

-- EX1? (foo')
-- Consider the following inductive definition:

inductive Foo' (α : Type) : Type where
  | c1 (l : List α) (f : Foo' α)
  | c2

-- What induction principle will Lean generate for `Foo'`?
#check @Foo'.rec
-- Note: Lean's recursor does NOT generate an induction hypothesis
-- for the list `l`, only for the recursive `f : Foo' α` field.
-- []
-- /FULL

-- FULL
-- ######################################################################
-- * Induction Hypotheses

-- Where does the phrase "induction hypothesis" fit into this story?
--
-- The induction principle for numbers says: to prove `P n` for all
-- `n`, prove `P 0` and prove `P n → P (n + 1)`.
--
-- We can make proofs by induction more explicit by giving the
-- property `P` a name.

def P_m0r (n : Nat) : Prop := n * 0 = 0

-- mul_0_r''
theorem mul_0_r'' : ∀ (n : Nat), P_m0r n := by
  apply Nat.rec
  · -- n = 0
    rfl
  · -- n = n' + 1
    intro n' ih
    simp only [P_m0r] at *
    simp [Nat.add_mul, ih]

-- FULL: The _induction hypothesis_ is the premise of the
-- implication `P_m0r n' → P_m0r (n' + 1)` -- the assumption that
-- `P` holds of `n'`, which we are allowed to use in proving that `P`
-- holds for `n' + 1`.
-- /FULL

-- FULL
-- ######################################################################
-- * More on the `induction` Tactic

-- The `induction` tactic actually does even more low-level
-- bookkeeping for us than we discussed above.
-- When we begin a proof with `intro n` and then `induction n`,
-- we are first telling Lean to consider a particular `n`
-- (by introducing it into the context) and then telling it to
-- prove something about all numbers (by using induction).

-- TERSE: ***

-- What Lean actually does in this situation, internally, is
-- "re-generalize" the variable we perform induction on.

namespace IndPrinciplesMore

-- add_assoc'
theorem add_assoc' : ∀ (n m p : Nat),
  n + (m + p) = (n + m) + p := by
  intro n m p
  induction n with
  | zero => omega
  | succ n' ih => omega

-- It also works to apply `induction` to a variable that is
-- quantified in the goal.

-- add_comm'
theorem add_comm' : ∀ (n m : Nat),
  n + m = m + n := by
  intro n
  induction n with
  | zero => intro m; omega
  | succ n' ih => intro m; omega

-- EX1? (plus_explicit_prop)
-- Rewrite both `add_assoc'` and `add_comm'` and their proofs in
-- the same style as `mul_0_r''` above -- that is, for each theorem,
-- give an explicit `def` of the proposition being proved by induction,
-- and state the theorem and proof in terms of this defined proposition.

-- SOLUTION
def P_assoc (n m p : Nat) : Prop := n + (m + p) = (n + m) + p

-- add_assoc_P
theorem add_assoc_P : ∀ (m p : Nat), ∀ (n : Nat), P_assoc n m p := by
  intro m p
  apply Nat.rec
  · unfold P_assoc; omega
  · intro n' ih
    unfold P_assoc at *; omega

def P_comm (n m : Nat) : Prop := n + m = m + n

-- add_comm_P
theorem add_comm_P : ∀ (m : Nat), ∀ (n : Nat), P_comm n m := by
  intro m
  apply Nat.rec
  · unfold P_comm; omega
  · intro n' ih
    unfold P_comm at *; omega
-- /SOLUTION
-- []
-- /FULL

end IndPrinciplesMore

-- ######################################################################
-- * Induction Principles for Propositions

-- Inductive definitions of propositions also cause Lean to generate
-- recursors.  For example, recall our proposition `Ev` from IndProp:

#check @Ev.rec
-- Ev.rec : {motive : (a : Nat) → Ev a → Sort u} →
--   motive 0 Ev.ev_0 →
--   (∀ {n : Nat} (a : Ev n), motive n a → motive (n + 2) (Ev.ev_SS a)) →
--   ∀ {a : Nat} (t : Ev a), motive a t

-- In English: Suppose `P` is a property of natural numbers.
-- To show that `P n` holds whenever `n` is even, it suffices to show:
--
-- - `P` holds for 0,
-- - for any `n`, if `n` is even and `P` holds for `n`, then `P`
--   holds for `n + 2`.

-- TERSE: ***

-- The precise form of an inductive definition can affect the
-- recursor Lean generates.

-- Here `n` is an INDEX (appears after the colon):
inductive Le1 : Nat → Nat → Prop where
  | le1_n : ∀ (n : Nat), Le1 n n
  | le1_S : ∀ (n m : Nat), Le1 n m → Le1 n (m + 1)

-- Here `n` is a PARAMETER (appears before the colon):
inductive Le2 (n : Nat) : Nat → Prop where
  | le2_n : Le2 n n
  | le2_S : ∀ (m : Nat), Le2 n m → Le2 n (m + 1)

-- FULL: The second one is better, because it gives a simpler
-- induction principle.
-- Compare:
#check @Le1.rec
-- Le1.rec has `P : Nat → Nat → Prop` (two parameters)

#check @Le2.rec
-- Le2.rec has `P : Nat → Prop` (one parameter, `n` is fixed)

-- TERSE: The latter is simpler, and corresponds to Lean's own
-- definition of `Nat.le`.

-- FULL
-- ######################################################################
-- * Formal vs. Informal Proofs by Induction

-- ** Induction Over an Inductively Defined Set

-- _Template_:
--
--   _Theorem_: For all `n : S`, `P n`, where `S` is some inductively
--   defined set.
--
--   _Proof_: By induction on `n`.
--
--     <one case for each constructor `c` of `S`...>
--
--     - Suppose `n = c a1 ... ak`, where <...and here we state
--       the IH for each `a` of type `S`, if any>.
--       We must show <...and here we restate `P(c a1 ... ak)`>.
--
--       <go on and prove `P n` to finish the case...>
--
--     - <other cases similarly...>                        []

-- ** Induction Over an Inductively Defined Proposition

-- _Template_:
--
--   _Theorem_: For all `x`, `Q x → P x`, where `Q` is some
--   inductively defined proposition.
--
--   _Proof_: By induction on a derivation of `Q`.
--
--     <one case for each constructor `c` of `Q`...>
--
--     - Suppose the final rule used to show `Q` is `c`.
--       Then <state types of all arguments and IH>.
--       We must show `P`.
--
--       <prove `P`...>
--
--     - <other cases similarly...>                        []
-- /FULL

-- ######################################################################
-- * Explicit Proof Objects for Induction

-- FULL: Although tactic-based proofs are normally much easier to
-- work with, the ability to write a proof term directly is sometimes
-- very handy, particularly when we want Lean to do something slightly
-- non-standard.

-- Recall the recursor on naturals:
#check @Nat.rec

-- There's nothing magic about this -- it's just another Lean
-- definition. We can write our own version:

def buildProof
    (P : Nat → Prop)
    (evP0 : P 0)
    (evPS : ∀ (n : Nat), P n → P (n + 1))
    (n : Nat) : P n :=
  match n with
  | 0 => evP0
  | k + 1 => evPS k (buildProof P evP0 evPS k)

def natIndTidy := buildProof

-- FULL: We can read `buildProof` as follows: Suppose we have
-- evidence `evP0` that `P` holds on 0, and evidence `evPS` that
-- `∀ n, P n → P (n + 1)`.  Then we can prove that `P` holds of an
-- arbitrary nat `n` using `buildProof`, which
-- matches on `n`:
--
-- - If `n` is 0, `buildProof` returns `evP0`.
-- - If `n` is `k + 1`, `buildProof` applies itself recursively on
--   `k` to obtain evidence that `P k` holds; then it applies
--   `evPS` on that evidence to show that `P (k + 1)` holds.

-- We can use our own induction principle with `induction ... using`:

-- mul_0_r'''
theorem mul_0_r''' : ∀ (n : Nat),
  n * 0 = 0 := by
  intro n
  induction n using natIndTidy with
  | evP0 => rfl
  | evPS n' ih => simp [Nat.add_mul, ih]

-- FULL
-- A non-standard induction principle that goes "by twos":

def natInd2
    (P : Nat → Prop)
    (P0 : P 0)
    (P1 : P 1)
    (PSS : ∀ (n : Nat), P n → P (n + 2))
    (n : Nat) : P n :=
  match n with
  | 0 => P0
  | 1 => P1
  | n' + 2 => PSS n' (natInd2 P P0 P1 PSS n')

-- This is useful for proving things about evenness:

-- even_ev
theorem even_ev : ∀ (n : Nat), even n = true → Ev n := by
  intro n
  induction n using natInd2 with
  | P0 => intro; exact Ev.ev_0
  | P1 => intro h; simp [even] at h
  | PSS n' ih =>
    intro h
    simp [even] at h
    apply Ev.ev_SS
    exact ih h

-- EX4 (t_tree)
-- What if we wanted to define binary trees using a constructor
-- that bundles children and value into a tuple?

inductive TTree (α : Type) : Type where
  | t_leaf
  | t_branch (triple : TTree α × α × TTree α)

-- Unfortunately, the auto-generated recursor doesn't introduce
-- induction hypotheses for the subtrees:
#check @TTree.rec

-- Define a `reflect` function:
def treflect {α : Type} (t : TTree α) : TTree α :=
  match t with
  | .t_leaf => .t_leaf
  | .t_branch (l, v, r) => .t_branch (treflect r, v, treflect l)

-- We need a custom induction principle. In Lean, we can define one
-- as a recursive function:
def TTree.ind' {α : Type} (P : TTree α → Prop)
    (hleaf : P .t_leaf)
    (hbranch : ∀ (v : α) (l : TTree α), P l → ∀ (r : TTree α), P r →
      P (.t_branch (l, v, r)))
    (t : TTree α) : P t :=
  -- ADMITDEF
  match t with
  | .t_leaf => hleaf
  | .t_branch (l, v, r) => hbranch v l (TTree.ind' P hleaf hbranch l) r (TTree.ind' P hleaf hbranch r)
  -- /ADMITDEF

-- reflect_involution
theorem reflect_involution {α : Type} : ∀ (t : TTree α),
  treflect (treflect t) = t := by
  -- ADMITTED
  intro t
  induction t using TTree.ind' with
  | hleaf => rfl
  | hbranch v l ihl r ihr =>
    simp [treflect, ihl, ihr]
-- /ADMITTED

-- GRADE_THEOREM 6: reflect_involution
-- []
-- /FULL
