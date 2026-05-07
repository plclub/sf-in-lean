-- Rel: Properties of Relations

-- This short (and optional) chapter develops some basic definitions
-- and a few theorems about binary relations in Lean.  The key
-- definitions are repeated where they are actually used (in the
-- Smallstep chapter of _Programming Language Foundations_),
-- so readers who are already comfortable with these ideas can safely
-- skim or skip this chapter.  However, relations are also a good
-- source of exercises for developing facility with Lean's basic
-- reasoning facilities, so it may be useful to look at this material
-- just after the IndProp chapter.

-- TERSE: HIDEFROMHTML
import LF.IndProp
-- TERSE: /HIDEFROMHTML

-- #####################################################################
-- * Relations

-- A binary _relation_ on a set `α` is a family of propositions
-- parameterized by two elements of `α` -- i.e., a proposition about
-- pairs of elements of `α`.

def Rel.Relation (α : Type) := α → α → Prop

-- FULL
-- Somewhat confusingly, the Lean standard library also uses the term
-- "relation" in various forms.  To maintain consistency, we define our
-- own `Relation` type here.  So, henceforth, `Relation` will always
-- refer to a binary relation _on_ some set (between the set and itself),
-- whereas in ordinary mathematical English the word "relation" can
-- refer either to this specific concept or the more general concept
-- of a relation between any number of possibly different sets.  The
-- context of the discussion should always make clear which is meant.
-- /FULL

open Rel in
-- An example relation on `Nat` is `Nat.le`, the less-than-or-equal-to
-- relation, which we usually write `n1 ≤ n2`.

#check @Nat.le
-- Nat.le : Nat → Nat → Prop

#check (Nat.le : Rel.Relation Nat)

-- (Lean's `Nat.le` is defined inductively with constructors
--   `Nat.le.refl : n ≤ n` and `Nat.le.step : n ≤ m → n ≤ m + 1`.)

-- #####################################################################
-- * Basic Properties

-- FULL
-- As anyone knows who has taken an undergraduate discrete math
-- course, there is a lot to be said about relations in general,
-- including ways of classifying relations (as reflexive, transitive,
-- etc.), theorems that can be proved generically about certain sorts
-- of relations, constructions that build one relation from another,
-- etc.  For example...
-- /FULL

-- *** Partial Functions

-- A relation `R` on a set `α` is a _partial function_ if, for every
-- `x`, there is at most one `y` such that `R x y` -- i.e., `R x y1`
-- and `R x y2` together imply `y1 = y2`.

def partial_function {α : Type} (R : Rel.Relation α) :=
  ∀ (x y1 y2 : α), R x y1 → R x y2 → y1 = y2

-- For example, the `NextNat` relation is a partial function.

inductive NextNat : Nat → Nat → Prop where
  | nn (n : Nat) : NextNat n (n + 1)

#check (NextNat : Rel.Relation Nat)

-- next_nat_partial_function
theorem next_nat_partial_function :
    partial_function NextNat := by
  unfold partial_function
  intro x y1 y2 h1 h2
  cases h1; cases h2; rfl

-- However, the `≤` relation on numbers is not a partial function.
-- (Assume, for a contradiction, that `≤` is a partial function.
-- But then, since `0 ≤ 0` and `0 ≤ 1`, it follows that `0 = 1`.
-- This is nonsense, so our assumption was contradictory.)

-- le_not_a_partial_function
theorem le_not_a_partial_function :
    ¬ (partial_function Nat.le) := by
  unfold partial_function
  intro hc
  have h : 0 = 1 := hc 0 0 1 Nat.le.refl (Nat.le.step Nat.le.refl)
  exact absurd h (by decide)

-- FULL
-- EX2? (total_relation_not_partial_function)
-- Show that the `TotalRelation` defined in (an exercise in)
-- IndProp is not a partial function.

-- (Copy the definition of `TotalRelation` from IndProp here
-- so that this file can be graded on its own.)
inductive TotalRelation' : Nat → Nat → Prop where
  | tot (n m : Nat) : TotalRelation' n m

-- total_relation_not_partial_function
theorem total_relation_not_partial_function :
    ¬ (partial_function TotalRelation') := by
  -- ADMITTED
  unfold partial_function
  intro hc
  have h : 0 = 1 := hc 0 0 1 (TotalRelation'.tot 0 0) (TotalRelation'.tot 0 1)
  exact absurd h (by decide)
  -- /ADMITTED
-- []

-- EX2? (empty_relation_partial_function)
-- Show that the `EmptyRelation` defined in (an exercise in)
-- IndProp is a partial function.

-- (Copy the definition of `EmptyRelation` from IndProp here
-- so that this file can be graded on its own.)
inductive EmptyRelation' : Nat → Nat → Prop where

-- empty_relation_partial_function
theorem empty_relation_partial_function :
    partial_function EmptyRelation' := by
  -- ADMITTED
  unfold partial_function
  intro n y1 y2 h1 _
  nomatch h1
  -- /ADMITTED
-- []
-- /FULL

-- *** Reflexive Relations

-- A _reflexive_ relation on a set `α` is one for which every element
-- of `α` is related to itself.

def Rel.reflexive {α : Type} (R : Rel.Relation α) :=
  ∀ (a : α), R a a

-- le_reflexive
theorem le_reflexive :
    Rel.reflexive Nat.le := by
  unfold Rel.reflexive
  intro n
  exact Nat.le.refl

-- *** Transitive Relations

-- A relation `R` is _transitive_ if `R a c` holds whenever `R a b`
-- and `R b c` do.

def Rel.transitive {α : Type} (R : Rel.Relation α) :=
  ∀ (a b c : α), R a b → R b c → R a c

-- le_trans
theorem Rel.le_trans :
    Rel.transitive Nat.le := by
  intro n m o hnm hmo
  exact Nat.le_trans hnm hmo

-- FULL
-- lt_trans
theorem Rel.lt_trans :
    Rel.transitive Nat.lt := by
  unfold Nat.lt Rel.transitive
  intro n m o hnm hmo
  exact Nat.le_trans (Nat.le.step hnm) hmo

-- EX2? (le_trans_hard_way)
-- We can also prove `lt_trans` more laboriously by induction,
-- without using `le_trans`.  Do this.

-- lt_trans'
theorem Rel.lt_trans' :
    Rel.transitive Nat.lt := by
  unfold Nat.lt Rel.transitive
  intro n m o hnm hmo
  -- Prove this by induction on evidence that `m` is less than `o`.
  -- ADMITTED
  induction hmo with
  | refl => exact Nat.le.step hnm
  | step _ ih => exact Nat.le.step ih
  -- /ADMITTED
-- []

-- EX2? (lt_trans'')
-- Prove the same thing again by induction on `o`.

-- lt_trans''
theorem Rel.lt_trans'' :
    Rel.transitive Nat.lt := by
  unfold Nat.lt Rel.transitive
  intro n m o hnm hmo
  induction o with
  -- ADMITTED
  | zero => exact absurd hmo (Nat.not_succ_le_zero m)
  | succ o' ih =>
    cases Nat.eq_or_lt_of_le hmo with
    | inl heq =>
      rw [← heq]; exact Nat.le.step hnm
    | inr hlt =>
      exact Nat.le.step (ih (Nat.lt_succ_iff.mp hlt))
  -- /ADMITTED
-- []

-- The transitivity of `le`, in turn, can be used to prove some facts
-- that will be useful later (e.g., for the proof of antisymmetry
-- below)...

-- le_Sn_le
theorem le_Sn_le : ∀ (n m : Nat), n + 1 ≤ m → n ≤ m := by
  intro n m h
  exact Nat.le_trans (Nat.le.step Nat.le.refl) h

-- EX1? (le_S_n)
theorem le_S_n : ∀ (n m : Nat),
    n + 1 ≤ m + 1 → n ≤ m := by
  -- ADMITTED
  intro n m h
  exact Nat.le_of_succ_le_succ h
  -- /ADMITTED
-- []

-- EX2? (le_Sn_n_inf)
-- Provide an informal proof of the following theorem:
--
--   Theorem: For every `n`, `¬ (n + 1 ≤ n)`
--
--   A formal proof of this is an optional exercise below, but try
--   writing an informal proof without doing the formal proof first.
--
--   Proof:
--   By induction on `n`.
--
--   - Suppose first that `n = 0`.  Then we must show `¬ (1 ≤ 0)`.
--     But this follows immediately from the definition of `≤`, since
--     neither constructor can produce `1 ≤ 0`.
--
--   - Next, suppose `n = n' + 1` for some `n'` with `¬ (n' + 1 ≤ n')`.
--     We must show `¬ (n + 1 ≤ n)` -- that is, `¬ ((n' + 1) + 1 ≤ n' + 1)`.
--     Suppose, for a contradiction, that `(n' + 1) + 1 ≤ n' + 1`.
--     Then, by `le_S_n`, we have `n' + 1 ≤ n'`, which contradicts the
--     induction hypothesis.
-- []

-- EX1? (le_Sn_n)
theorem le_Sn_n : ∀ (n : Nat),
    ¬ (n + 1 ≤ n) := by
  -- ADMITTED
  intro n
  exact Nat.not_succ_le_self n
  -- /ADMITTED
-- []
-- /FULL

-- Reflexivity and transitivity are the main concepts we'll need for
-- later chapters, but, for a bit of additional practice working with
-- relations in Lean, let's look at a few other common ones...

-- *** Symmetric and Antisymmetric Relations

-- A relation `R` is _symmetric_ if `R a b` implies `R b a`.

def Rel.symmetric {α : Type} (R : Rel.Relation α) :=
  ∀ (a b : α), R a b → R b a

-- FULL
-- EX2? (le_not_symmetric)
-- le_not_symmetric
theorem le_not_symmetric :
    ¬ (Rel.symmetric Nat.le) := by
  -- ADMITTED
  unfold Rel.symmetric
  intro h
  have : 1 ≤ 0 := h 0 1 (Nat.le.step Nat.le.refl)
  exact absurd this (by decide)
  -- /ADMITTED
-- []
-- /FULL

-- A relation `R` is _antisymmetric_ if `R a b` and `R b a` together
-- imply `a = b` -- that is, if the only "cycles" in `R` are trivial
-- ones.

def Rel.antisymmetric {α : Type} (R : Rel.Relation α) :=
  ∀ (a b : α), R a b → R b a → a = b

-- FULL
-- EX2? (le_antisymmetric)
-- le_antisymmetric
theorem le_antisymmetric :
    Rel.antisymmetric Nat.le := by
  -- ADMITTED
  unfold Rel.antisymmetric
  intro a b hab hba
  exact Nat.le_antisymm hab hba
  -- /ADMITTED
-- []

-- EX2? (le_step)
-- le_step
theorem le_step : ∀ (n m p : Nat),
    n < m →
    m ≤ p + 1 →
    n ≤ p := by
  -- ADMITTED
  intro n m p hnm hmp
  exact Nat.le_of_succ_le_succ (Nat.le_trans hnm hmp)
  -- /ADMITTED
-- []
-- /FULL

-- *** Equivalence Relations

-- A relation is an _equivalence_ if it's reflexive, symmetric, and
-- transitive.

def Rel.equivalence {α : Type} (R : Rel.Relation α) :=
  (Rel.reflexive R) ∧ (Rel.symmetric R) ∧ (Rel.transitive R)

-- *** Partial Orders and Preorders

-- A relation is a _partial order_ when it's reflexive,
-- _anti_-symmetric, and transitive.  In the standard library
-- it's called just "order" for short.

def Rel.order {α : Type} (R : Rel.Relation α) :=
  (Rel.reflexive R) ∧ (Rel.antisymmetric R) ∧ (Rel.transitive R)

-- A preorder is almost like a partial order, but doesn't have to be
-- antisymmetric.

def Rel.preorder {α : Type} (R : Rel.Relation α) :=
  (Rel.reflexive R) ∧ (Rel.transitive R)

-- FULL
-- le_order
theorem le_order :
    Rel.order Nat.le := by
  unfold Rel.order
  exact ⟨le_reflexive, le_antisymmetric, Rel.le_trans⟩
-- /FULL

-- #####################################################################
-- * Reflexive, Transitive Closure

-- The _reflexive, transitive closure_ of a relation `R` is the
-- smallest relation that contains `R` and that is both reflexive and
-- transitive.  Formally, it is defined like this in the Relations
-- module of the standard library:

inductive Rel.ClosReflTrans {α : Type} (R : Rel.Relation α) : Rel.Relation α where
  | rt_step (x y : α) (h : R x y) : Rel.ClosReflTrans R x y
  | rt_refl (x : α) : Rel.ClosReflTrans R x x
  | rt_trans (x y z : α)
      (hxy : Rel.ClosReflTrans R x y)
      (hyz : Rel.ClosReflTrans R y z) :
      Rel.ClosReflTrans R x z

-- For example, the reflexive and transitive closure of the
-- `NextNat` relation coincides with the `≤` relation.

-- next_nat_closure_is_le
theorem next_nat_closure_is_le : ∀ (n m : Nat),
    (n ≤ m) ↔ (Rel.ClosReflTrans NextNat n m) := by
  intro n m
  constructor
  · -- →
    intro h
    induction h with
    | refl => exact Rel.ClosReflTrans.rt_refl n
    | step h ih =>
      exact Rel.ClosReflTrans.rt_trans n _ _
        ih (Rel.ClosReflTrans.rt_step _ _ (NextNat.nn _))
  · -- ←
    intro h
    induction h with
    | rt_step x y hxy =>
      cases hxy with
      | nn => exact Nat.le.step Nat.le.refl
    | rt_refl => exact Nat.le.refl
    | rt_trans x y z _ _ ih1 ih2 =>
      exact Nat.le_trans ih1 ih2

-- The above definition of reflexive, transitive closure is natural:
-- it says, explicitly, that the reflexive and transitive closure of
-- `R` is the least relation that includes `R` and that is closed
-- under rules of reflexivity and transitivity.  But it turns out
-- that this definition is not very convenient for doing proofs,
-- since the "nondeterminism" of the `rt_trans` rule can sometimes
-- lead to tricky inductions.  Here is a more useful definition:

inductive Rel.ClosReflTrans1n {α : Type}
    (R : Rel.Relation α) : α → α → Prop where
  | rt1n_refl (x : α) : Rel.ClosReflTrans1n R x x
  | rt1n_trans (x y z : α)
      (hxy : R x y) (hrest : Rel.ClosReflTrans1n R y z) :
      Rel.ClosReflTrans1n R x z

-- Our new definition of reflexive, transitive closure "bundles"
-- the `rt_step` and `rt_trans` rules into the single rule step.
-- The left-hand premise of this step is a single use of `R`,
-- leading to a much simpler induction principle.
--
-- Before we go on, we should check that the two definitions do
-- indeed define the same relation...
--
-- First, we prove two lemmas showing that `ClosReflTrans1n` mimics
-- the behavior of the two "missing" `ClosReflTrans` constructors.

-- rsc_R
theorem rsc_R : ∀ {α : Type} (R : Rel.Relation α) (x y : α),
    R x y → Rel.ClosReflTrans1n R x y := by
  intro α R x y h
  exact Rel.ClosReflTrans1n.rt1n_trans x y y h (Rel.ClosReflTrans1n.rt1n_refl y)

-- EX2? (rsc_trans)
-- rsc_trans
theorem rsc_trans :
    ∀ {α : Type} (R : Rel.Relation α) (x y z : α),
      Rel.ClosReflTrans1n R x y →
      Rel.ClosReflTrans1n R y z →
      Rel.ClosReflTrans1n R x z := by
  -- ADMITTED
  intro α R x y z hxy hyz
  induction hxy with
  | rt1n_refl => exact hyz
  | rt1n_trans _ u _ hxu _ ih =>
    exact Rel.ClosReflTrans1n.rt1n_trans _ u z hxu (ih hyz)
  -- /ADMITTED
-- []

-- Then we use these facts to prove that the two definitions of
-- reflexive, transitive closure do indeed define the same relation.

-- EX3? (rtc_rsc_coincide)
-- rtc_rsc_coincide
theorem rtc_rsc_coincide :
    ∀ {α : Type} (R : Rel.Relation α) (x y : α),
      Rel.ClosReflTrans R x y ↔ Rel.ClosReflTrans1n R x y := by
  -- ADMITTED
  intro α R x y
  constructor
  · -- →
    intro h
    induction h with
    | rt_step x y hxy => exact rsc_R R x y hxy
    | rt_refl x => exact Rel.ClosReflTrans1n.rt1n_refl x
    | rt_trans x y z _ _ ih1 ih2 => exact rsc_trans R x y z ih1 ih2
  · -- ←
    intro h
    induction h with
    | rt1n_refl x => exact Rel.ClosReflTrans.rt_refl x
    | rt1n_trans x y z hxy _ ih =>
      exact Rel.ClosReflTrans.rt_trans x y z
        (Rel.ClosReflTrans.rt_step x y hxy) ih
  -- /ADMITTED
-- []

-- LATER
-- #####################################################################
-- SOME MORE OPTIONAL EXERCISES AND SOLUTIONS, TO BE FLESHED OUT LATER

-- EX3? (rt_idempotent)
-- rt_idempotent
theorem rt_idempotent : ∀ {α : Type} (R : Rel.Relation α) (x y : α),
    Rel.ClosReflTrans (Rel.ClosReflTrans R) x y ↔ Rel.ClosReflTrans R x y := by
  -- ADMITTED
  intro α R x y
  constructor
  · intro h
    induction h with
    | rt_step _ _ hxy => exact hxy
    | rt_refl x => exact Rel.ClosReflTrans.rt_refl x
    | rt_trans _ _ _ _ _ ih1 ih2 =>
      exact Rel.ClosReflTrans.rt_trans _ _ _ ih1 ih2
  · intro h
    induction h with
    | rt_step x y hxy =>
      exact Rel.ClosReflTrans.rt_step _ _
        (Rel.ClosReflTrans.rt_step x y hxy)
    | rt_refl x => exact Rel.ClosReflTrans.rt_refl x
    | rt_trans _ _ _ _ _ ih1 ih2 =>
      exact Rel.ClosReflTrans.rt_trans _ _ _ ih1 ih2
  -- /ADMITTED
-- []

-- Define what it means for a relation to preserve a property

def Rel.preserves {α : Type} (R : Rel.Relation α) (P : α → Prop) :=
  ∀ (x y : α), P x → R x y → P y

-- EX3? (rt_preserves)
-- rt_preserves
theorem rt_preserves : ∀ {α : Type} (R : Rel.Relation α) (P : α → Prop),
    Rel.preserves R P → Rel.preserves (Rel.ClosReflTrans R) P := by
  -- ADMITTED
  intro α R P hR
  unfold Rel.preserves
  intro x y hpx htc
  induction htc with
  | rt_step x y hxy => exact hR x y hpx hxy
  | rt_refl => exact hpx
  | rt_trans _ _ _ _ _ ih1 ih2 => exact ih2 (ih1 hpx)
  -- /ADMITTED
-- []
-- /LATER
