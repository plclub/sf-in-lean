-- Logic: Logic in Lean

-- INSTRUCTORS: Warning: This is a LOT of material to get through in
--    two 80-minute lectures, and the last couple of sections are quite
--    meaty.  Pacing is key!

-- SOONER: Unlike earlier chapters, there are probably too many
--    WORKINCLASSes in this chapter.  BCP 20: But conversely some more
--    quizzes would be great!
-- HIDEFROMHTML
import Tactics
-- /HIDEFROMHTML

-- FULL: We have now seen many examples of factual claims (i.e.,
--    _propositions_) and ways of presenting evidence of their truth
--    (_proofs_).  In particular, we have worked extensively with
--    equality propositions (`e1 = e2`), implications (`P → Q`), and
--    quantified propositions (`∀ x, P`).  In this chapter, we will
--    see how Lean can be used to carry out other familiar forms of
--    logical reasoning.
--
--    Before diving into details, we should talk a bit about the status
--    of mathematical statements in Lean. Lean is a _typed_ language,
--    which means that every sensible expression has an associated type.
--    Logical claims are no exception: any statement we might try to
--    prove in Lean has a type, namely `Prop`, the type of
--    _propositions_.  We can see this with the `#check` command:

-- TERSE
-- So far, we have seen...
--
--    - _propositions_: mathematical statements, so far only of 3 kinds:
--          - equality propositions (`e1 = e2`)
--          - implications (`P → Q`)
--          - quantified propositions (`∀ x, P`)
--
--    - _proofs_: ways of presenting evidence for the truth of a
--       proposition
--
-- In this chapter we will introduce several more flavors of both
-- propositions and proofs.

-- * The `Prop` Type

-- Like everything in Lean, well-formed propositions have a _type_:
-- /TERSE

#check (∀ n m : Nat, n + m = m + n : Prop)

-- TERSE: ***
-- Note that _all_ syntactically well-formed propositions have type
-- `Prop` in Lean, regardless of whether they are true or not.
--
-- Simply _being_ a proposition is one thing; being _provable_ is
-- a different thing!

#check (2 = 2 : Prop)

#check (3 = 2 : Prop)

#check (∀ n : Nat, n = 2 : Prop)

-- FULL: Indeed, propositions don't just have types -- they are
--    _first-class_ entities that can be manipulated in all the same ways as
--    any of the other things in Lean's world.

-- TERSE: ***
-- So far, we've seen one primary place where propositions can appear:
--    in `theorem` (and `example`) declarations.

theorem plus_2_2_is_4 :
  2 + 2 = 4 := by rfl

-- FULL: But propositions can be used in other ways.  For example, we
--    can give a name to a proposition using a `def`, just as we
--    give names to other kinds of expressions.
-- TERSE: ***
-- TERSE: Propositions are first-class entities in Lean, though. For
--    example, we can name them:

-- HIDE: Right now, this idiom is used in exactly one place in earlier
--    chapters: in an exercise in Tactics.lean.  I'm going to ignore this
--    and pretend we're introducing it here.  BCP 1/16
def plus_claim : Prop := 2 + 2 = 4
#check (plus_claim : Prop)

-- FULL: We can later use this name in any situation where a proposition is
--    expected -- for example, as the claim in a `theorem` declaration.

theorem plus_claim_is_true :
  plus_claim := by rfl

-- TERSE: ***
-- We can also write _parameterized_ propositions -- that is,
--    functions that take arguments of some type and return a
--    proposition.

-- FULL: For instance, the following function takes a number
--    and returns a proposition asserting that this number is equal to
--    three:

def is_three (n : Nat) : Prop :=
  n = 3
#check (is_three : Nat → Prop)

-- TERSE: ***
-- In Lean, functions that return propositions are said to define
--    _properties_ of their arguments.
--
--    For instance, here's a (polymorphic) property defining the
--    familiar notion of an _injective function_.

def Injective {A B : Type} (f : A → B) : Prop :=
  ∀ x y : A, f x = f y → x = y

theorem succ_inj' : Injective Nat.succ := by
  intro x y h
  exact Nat.succ.inj h

-- TERSE: ***
-- The familiar equality operator `=` is a (binary) function that returns
--    a `Prop`.
--
--    The expression `n = m` is syntactic sugar for `Eq n m`.
--
--    Because `Eq` can be used with elements of any type, it is also
--    polymorphic:

#check (@Eq : {α : Sort _} → α → α → Prop)

-- FULL: (Notice that we wrote `@Eq` instead of `Eq`: The type
--    argument `α` to `Eq` is declared as implicit, and we need to turn
--    off the inference of this implicit argument to see the full type
--    of `Eq`.)
-- TERSE

-- QUIZ
-- What is the type of the following expression?
--
--        Nat.pred (Nat.succ 0) = 0
--
--    (A) `Prop`
--
--    (B) `Nat → Prop`
--
--    (C) `∀ n : Nat, Prop`
--
--    (D) `Nat → Nat`
--
--    (E) Not typeable

-- /QUIZ
-- FOLD
#check (Nat.pred (Nat.succ 0) = 0 : Prop)
-- /FOLD

-- QUIZ
-- What is the type of the following expression?
--
--       ∀ n : Nat, Nat.pred (Nat.succ n) = n
--
--    (A) `Prop`
--
--    (B) `Nat → Prop`
--
--    (C) `∀ n : Nat, Prop`
--
--    (D) `Nat → Nat`
--
--    (E) Not typeable

-- /QUIZ
-- FOLD
#check (∀ n : Nat, Nat.pred (Nat.succ n) = n : Prop)
-- /FOLD

-- QUIZ
-- What is the type of the following expression?
--
--       ∀ n : Nat, Nat.succ (Nat.pred n) = n
--
--    (A) `Prop`
--
--    (B) `Nat → Prop`
--
--    (C) `Nat → Nat`
--
--    (D) Not typeable

-- /QUIZ
-- FOLD
#check (∀ n : Nat, Nat.succ (Nat.pred n) = n : Prop)
-- /FOLD

-- QUIZ
-- What is the type of the following expression?
--
--       fun n : Nat => Nat.succ (Nat.pred n)
--
--    (A) `Prop`
--
--    (B) `Nat → Prop`
--
--    (C) `Nat → Nat`
--
--    (D) Not typeable

-- /QUIZ
-- FOLD
#check (fun n : Nat => Nat.pred (Nat.succ n) : Nat → Nat)
-- /FOLD

-- QUIZ
-- What is the type of the following expression?
--
--       fun n : Nat => Nat.succ (Nat.pred n) = n
--
--    (A) `Prop`
--
--    (B) `Nat → Prop`
--
--    (C) `Nat → Nat`
--
--    (D) Not typeable

-- /QUIZ
-- FOLD
#check (fun n : Nat => Nat.pred (Nat.succ n) = n : Nat → Prop)
-- /FOLD

-- QUIZ
-- Which of the following is _not_ a proposition?
--
--     (A) `3 + 2 = 4`
--
--     (B) `3 + 2 = 5`
--
--     (C) `(3 + 2) == 5`
--
--     (D) `((3+2) == 4) = false`
--
--     (E) `∀ n, ((3+2) == n) = true → n = 5`
--
--     (F) All of these are propositions

-- /QUIZ
-- FOLD
-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "`3 + 2 =? 5` has type `bool`"
-- ADAPTED:
-- `(3 + 2) == 5` has type `Bool`, not `Prop`. In Lean, `==` is the
-- decidable boolean equality, while `=` is propositional equality.
-- However, we can still write `((3+2) == 4) = false` as a `Prop`,
-- since it compares a `Bool` value with `false`.
#check ((3 + 2) == 5 : Bool)
-- /FOLD
-- /TERSE

-- ######################################################################
-- * Logical Connectives

-- ** Conjunction

-- The _conjunction_, or _logical and_, of propositions `A` and `B` is
--    written `A ∧ B`; it represents the claim that both `A` and `B` are
--    true.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by

-- To prove a conjunction, use the `constructor` tactic.  This will
--    generate two subgoals, one for each part of the statement:

  constructor
  · -- 3 + 4 = 7
    rfl
  · -- 2 * 2 = 4
    rfl

-- TERSE: ***

-- For any propositions `A` and `B`, if we assume that `A` and `B`
--    are each true individually, we can conclude that `A ∧ B` is also
--    true.  Lean provides `And.intro` for this.

-- TERSE: we can use `And.intro` to achieve the same effect as `constructor`.

#check @And.intro

-- FULL
-- Since applying a theorem with hypotheses to some goal has the
--    effect of generating as many subgoals as there are hypotheses for
--    that theorem, we can apply `And.intro` to achieve the same effect as
--    `constructor`.

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  · -- 3 + 4 = 7
    rfl
  · -- 2 + 2 = 4
    rfl
-- /FULL

-- FULL
-- EX2 (plus_is_O)
-- /FULL

-- TERSE: ***

example : ∀ (n m : Nat), n + m = 0 → n = 0 ∧ m = 0 := by
  -- FULL: ADMITTED
  -- TERSE: WORKINCLASS
  intro n m h
  cases n with
  | zero =>
    simp at h
    exact ⟨rfl, h⟩
  | succ n' =>
    simp at h
-- FULL: /ADMITTED
-- TERSE: /WORKINCLASS
-- FULL
-- []
-- /FULL

-- TERSE: ***
-- So much for proving conjunctive statements.  To go in the other
--    direction -- i.e., to _use_ a conjunctive hypothesis to help prove
--    something else -- we use `obtain` to decompose it.

-- FULL: When the current proof context contains a hypothesis `H` of the
--    form `A ∧ B`, writing `obtain ⟨HA, HB⟩ := H` will remove `H`
--    from the context and replace it with two new hypotheses: `HA`,
--    stating that `A` is true, and `HB`, stating that `B` is true.

theorem and_example2 :
  ∀ (n m : Nat), n = 0 ∧ m = 0 → n + m = 0 := by
  -- WORKINCLASS
  intro n m H
  obtain ⟨Hn, Hm⟩ := H
  rw [Hn, Hm]
-- /WORKINCLASS

-- TERSE: ***

-- As usual, we can also decompose `H` right at the point where we
--    introduce it, instead of introducing and then decomposing it:

theorem and_example2' :
  ∀ (n m : Nat), n = 0 ∧ m = 0 → n + m = 0 := by
  intro n m ⟨Hn, Hm⟩
  rw [Hn, Hm]

-- FULL
-- TERSE: ***
-- You may wonder why we bothered packing the two hypotheses `n = 0` and
--    `m = 0` into a single conjunction, since we could also have stated the
--    theorem with two separate premises:

theorem and_example2'' :
  ∀ (n m : Nat), n = 0 → m = 0 → n + m = 0 := by
  intro n m Hn Hm
  rw [Hn, Hm]

-- TERSE: For the present example, both ways work.  But ...
-- TERSE: ***
-- TERSE: In other situations we may wind up with a
--    conjunctive hypothesis in the middle of a proof...
-- FULL: For this specific theorem, both formulations are fine.  But
--    it's important to understand how to work with conjunctive
--    hypotheses because conjunctions often arise from intermediate
--    steps in proofs, especially in larger developments.  Here's a
--    simple example:

theorem and_example3 :
  ∀ (n m : Nat), n + m = 0 → n * m = 0 := by
  -- WORKINCLASS
  intro n m H
  have Hpair : n = 0 ∧ m = 0 := by constructor <;> omega
  obtain ⟨Hn, Hm⟩ := Hpair
  subst Hn; subst Hm; rfl
-- /WORKINCLASS
-- /FULL

-- FULL

-- Another common situation is that we know `A ∧ B` but in some
--    context we need just `A` or just `B`.  In such cases we can use
--    `obtain` and use an underscore pattern `_` to indicate that the
--    unneeded conjunct should just be thrown away.

-- HIDEFROMADVANCED
theorem proj1 (P Q : Prop) :
  P ∧ Q → P := by
  intro ⟨HP, _⟩
  exact HP
-- /HIDEFROMADVANCED

-- HIDEFROMADVANCED
-- EX1? (proj2)
-- /HIDEFROMADVANCED
theorem proj2 (P Q : Prop) :
  P ∧ Q → Q := by
-- HIDEFROMADVANCED
  -- ADMITTED
  intro ⟨_, HQ⟩
  exact HQ
  -- /ADMITTED
-- []
-- /HIDEFROMADVANCED

-- Finally, we sometimes need to rearrange the order of conjunctions
--    and/or the grouping of multi-way conjunctions. We can see this
--    at work in the proofs of the following commutativity and
--    associativity theorems

theorem and_commut (P Q : Prop) :
  P ∧ Q → Q ∧ P := by
  intro ⟨HP, HQ⟩
  exact ⟨HQ, HP⟩

-- EX1 (and_assoc)
-- In the following proof of associativity, notice how the _nested_
--    `obtain` pattern breaks the hypothesis `H : P ∧ (Q ∧ R)` down into
--    `HP : P`, `HQ : Q`, and `HR : R`.  Finish the proof.

theorem and_assoc' (P Q R : Prop) :
  P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  intro ⟨HP, HQ, HR⟩
  -- ADMITTED
  exact ⟨⟨HP, HQ⟩, HR⟩
  -- /ADMITTED
-- []
-- /FULL

-- TERSE: ***
-- The infix notation `∧` is actually just syntactic sugar for
--    `And A B`.  That is, `And` is a Lean type that takes two
--    propositions as arguments and yields a proposition.

#check @And  -- And : Prop → Prop → Prop

-- ** Disjunction

-- Another important connective is the _disjunction_, or _logical or_,
--    of two propositions: `A ∨ B` is true when either `A` or `B` is.
--    This infix notation stands for `Or A B`, where
--    `Or : Prop → Prop → Prop`.

-- TERSE: ***
-- To use a disjunctive hypothesis in a proof, we proceed by case
--    analysis -- which, as with other data types like `Nat`, can be done
--    explicitly with `obtain` using the `|` pattern:

-- HIDE: APT 21: There is nothing exactly like this in the library, so
--    no particular name to match. But converse is named `mult_is_O`, so
--    I've changed this to `factor_is_O` to sort of match.
theorem factor_is_O :
  ∀ (n m : Nat), n = 0 ∨ m = 0 → n * m = 0 := by
  -- NOTE: The following comment was adapted from the Rocq original:
  -- ORIGINAL: "This intro pattern implicitly does case analysis on
  --    `n = 0 ∨ m = 0`..."
  -- ADAPTED:
  -- This `obtain` pattern does case analysis on `n = 0 ∨ m = 0`...
  intro n m H
  obtain Hn | Hm := H
  · -- Here, n = 0
    rw [Hn, zero_mul]
  · -- Here, m = 0
    rw [Hm, mul_zero]

-- FULL: We can see in this example that, when we perform case
--    analysis on a disjunction `A ∨ B`, we must separately discharge
--    two proof obligations, each showing that the conclusion holds
--    under a different assumption -- `A` in the first subgoal and `B`
--    in the second.

-- TERSE: ***

-- Conversely, to show that a disjunction holds, it suffices to show
--    that one of its sides holds. This can be done via the tactics
--    `left` and `right`.  As their names imply, the first one requires
--    proving the left side of the disjunction, while the second
--    requires proving the right side.  Here is a trivial use...

theorem or_intro_l (A B : Prop) : A → A ∨ B := by
  intro HA
  left
  exact HA

-- TERSE: ***
-- ... and here is a slightly more interesting example requiring both
--    `left` and `right`:

theorem zero_or_succ :
  ∀ n : Nat, n = 0 ∨ n = Nat.succ (Nat.pred n) := by
  -- WORKINCLASS
  intro n
  cases n with
  | zero => left; rfl
  | succ n' => right; rfl
-- /WORKINCLASS

-- TERSE: HIDEFROMHTML
-- EX2 (mult_is_O)
theorem mult_is_O :
  ∀ (n m : Nat), n * m = 0 → n = 0 ∨ m = 0 := by
  -- ADMITTED
  intro n m H
  cases n with
  | zero => left; rfl
  | succ n' =>
    cases m with
    | zero => right; rfl
    | succ m' =>
      -- H : (n' + 1) * (m' + 1) = 0
      -- By def: (n' + 1) * (m' + 1) = (n' + 1) + ((n' + 1) * m')
      -- which is at least n' + 1, contradicting = 0
      change mul (n' + 1) (m' + 1) = 0 at H
      unfold mul at H
      omega
  -- /ADMITTED
-- []

-- EX1 (or_commut)
theorem or_commut (P Q : Prop) :
  P ∨ Q → Q ∨ P := by
  -- ADMITTED
  intro H
  obtain HP | HQ := H
  · right; exact HP
  · left; exact HQ
  -- /ADMITTED
-- []
-- TERSE: /HIDEFROMHTML

-- ** Falsehood and Negation

-- Up to this point, we have mostly been concerned with proving
--    "positive" statements -- addition is commutative, appending lists
--    is associative, etc.  We are sometimes also interested in negative
--    results, demonstrating that some proposition is _not_ true. Such
--    statements are expressed with the logical negation operator `¬`.

-- TERSE: ***
-- To see how negation works, recall the _principle of explosion_
--    from the Tactics chapter, which asserts that, if we assume a
--    contradiction, then any other proposition can be derived.
--
--    Following this intuition, we could define `¬ P` ("not P") as
--    `∀ Q, P → Q`.

-- TERSE: ***
-- Lean actually makes an equivalent but slightly different choice,
--    defining `¬ P` as `P → False`, where `False` is a specific
--    un-provable proposition defined in the standard library.

-- HIDEFROMHTML
namespace NotPlayground
-- /HIDEFROMHTML

def not (P : Prop) := P → False

#check (not : Prop → Prop)

-- HIDEFROMHTML
end NotPlayground
-- /HIDEFROMHTML

-- TERSE: ***
-- Since `False` is a contradictory proposition, the principle of
--    explosion also applies to it. If we can get `False` into the context,
--    we can use `exact False.elim` or `contradiction` on it to complete
--    any goal:

theorem ex_falso_quodlibet (P : Prop) :
  False → P := by
  intro contra
  exact contra.elim

-- FULL: The Latin _ex falso quodlibet_ means, literally, "from falsehood
--    follows whatever you like"; this is another common name for the
--    principle of explosion.

-- FULL
-- EX2? (not_implies_our_not)
-- Show that Lean's definition of negation implies the intuitive one
--    mentioned above.
--
--    Hint: While getting accustomed to Lean's definition of `Not`, you might
--    find it helpful to `unfold Not` near the beginning of proofs.

theorem not_implies_our_not (P : Prop) :
  ¬P → (∀ (Q : Prop), P → Q) := by
  -- ADMITTED
  intro H Q HP
  unfold Not at H
  exact absurd HP H
  -- /ADMITTED
-- []
-- /FULL

-- TERSE: ***
-- Inequality is a very common form of negated statement, so there is a
--    special notation for it, `x ≠ y`, which is `¬(x = y)`.

-- For example:

theorem zero_not_one : 0 ≠ 1 := by
  -- FULL: The proposition `0 ≠ 1` is exactly the same as
  --    `¬(0 = 1)` -- that is, `Not (0 = 1)` -- which unfolds to
  --    `(0 = 1) → False`.
  -- FULL: To prove an inequality, we may assume the opposite
  --    equality...
  intro contra
  -- FULL: ... and deduce a contradiction from it. Here, the
  --    equality `0 = 1` contradicts the disjointness of
  --    constructors `Nat.zero` and `Nat.succ`, so `contradiction`
  --    takes care of it.
  contradiction

-- TERSE: ***
-- It takes a little practice to get used to working with negation in Lean.
--    Even though _you_ may see perfectly well why a claim involving
--    negation holds, it can be a little tricky at first to see how to make
--    Lean understand it!
--
--    Here are proofs of a few familiar facts to help get you warmed up.

theorem not_False :
  ¬False := by
  unfold Not; intro H; exact H

-- TERSE: ***
theorem contradiction_implies_anything (P Q : Prop) :
  (P ∧ ¬P) → Q := by
  -- WORKINCLASS
  intro ⟨HP, HNP⟩
  unfold Not at HNP
  exact absurd HP HNP
-- /WORKINCLASS

theorem double_neg (P : Prop) :
  P → ¬¬P := by
  -- WORKINCLASS
  intro H G
  exact G H
-- /WORKINCLASS

-- FULL
-- EX2AM? (double_neg_informal)
-- Write an _informal_ proof of `double_neg`:
--
--    _Theorem_: `P` implies `¬¬P`, for any proposition `P`.

-- SOLUTION
-- _Proof_: Suppose some proposition `P` holds.  We must show `¬¬P` --
-- i.e., `¬P → False`, so suppose `¬P` as well and try to derive
-- `False`.  Then we have both `P` and `¬P` (i.e., `P → False`) from
-- which we can indeed derive `False`.  So `¬¬P` holds.
-- /SOLUTION

-- GRADE_MANUAL 2: double_neg_informal
-- []

-- EX1! (contrapositive)
theorem contrapositive (P Q : Prop) :
  (P → Q) → (¬Q → ¬P) := by
  -- ADMITTED
  intro H HNotQ HP
  exact HNotQ (H HP)
  -- /ADMITTED
-- []

-- EX1 (not_both_true_and_false)
theorem not_both_true_and_false (P : Prop) :
  ¬(P ∧ ¬P) := by
  -- ADMITTED
  intro ⟨HP, HNA⟩
  exact HNA HP
  -- /ADMITTED
-- []

-- EX1AM (not_PNP_informal)
-- Write an informal proof (in English) of the proposition `∀ P
--    : Prop, ¬(P ∧ ¬P)`.

-- SOLUTION
-- _Proof_: Suppose, for some `P`, that `(P ∧ ¬P)` holds.  Recall that
-- `¬P` is defined as `P → False`.  Given `P` and `P → False`, we can
-- prove `False`, so `(P ∧ ¬P) → False`, i.e., `¬(P ∧ ¬P)`.
-- /SOLUTION

-- GRADE_MANUAL 1: not_PNP_informal
-- []

-- EX2 (de_morgan_not_or)
-- _De Morgan's Laws_, named for Augustus De Morgan, describe how
--    negation interacts with conjunction and disjunction.  The
--    following law says that "the negation of a disjunction is the
--    conjunction of the negations." There is a dual law
--    `de_morgan_not_and_not` to which we will return at the end of this
--    chapter.
theorem de_morgan_not_or (P Q : Prop) :
    ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  -- ADMITTED
  unfold Not
  intro H
  constructor
  · intro HP; exact H (Or.inl HP)
  · intro HQ; exact H (Or.inr HQ)
  -- /ADMITTED
-- []

-- EX1? (not_S_inverse_pred)
-- Since we are working with natural numbers, we can disprove that
--    `Nat.succ` and `Nat.pred` are inverses of each other:
theorem not_S_pred_n : ¬(∀ n : Nat, Nat.succ (Nat.pred n) = n) := by
  -- ADMITTED
  intro H
  have := H 0
  contradiction
  -- /ADMITTED
-- []
-- /FULL

-- TERSE: ***

-- TERSE: Since inequality involves a negation, getting comfortable
--    with it also often requires a little practice.
--
--    A useful trick: if you are trying to prove a nonsensical goal,
--    apply `exfalso` to change the goal to `False`. This
--    makes it easier to use assumptions of the form `¬P`, and in
--    particular of the form `x ≠ y`.

-- FULL: Since inequality involves a negation, it also requires a little
--    practice to be able to work with it fluently.  Here is one useful
--    trick.
--
--    If you are trying to prove a goal that is nonsensical (e.g., the
--    goal state is `false = true`), apply `exfalso` to change the goal
--    to `False`.
--
--    This makes it easier to use assumptions of the form `¬P` that may
--    be available in the context -- in particular, assumptions of the
--    form `x ≠ y`.

theorem not_true_is_false (b : Bool) :
  b ≠ true → b = false := by
-- FOLD
  intro H
  cases b with
  | true =>
    -- b = true
    exfalso
    exact H rfl
  | false =>
    -- b = false
    rfl
-- /FOLD

-- FULL
-- Since reasoning with `exfalso` is quite common, Lean
--    provides it as a built-in tactic.

theorem not_true_is_false' (b : Bool) :
  b ≠ true → b = false := by
  intro H
  cases b with
  | true =>
    -- b = true
    exfalso               -- <=== explicitly used here
    exact H rfl
  | false => rfl
-- /FULL

-- TERSE
-- LATER: There are probably too many of these particular quizzes...
-- QUIZ
-- To prove the following proposition, which tactics will we need
--    besides `intro` and `apply`/`exact`?
--
--         ∀ X, ∀ a b : X, (a = b) ∧ (a ≠ b) → False
--
--     (A) `obtain`, `unfold Not`, `left` and `right`
--
--     (B) `obtain` and `unfold Not`
--
--     (C) only `obtain`
--
--     (D) `left` and/or `right`
--
--     (E) only `unfold Not`
--
--     (F) none of the above

-- /QUIZ
-- FOLD
theorem quiz1 (X : Type) (a b : X) : (a = b) ∧ (a ≠ b) → False := by
  intro ⟨Hab, Hnab⟩; exact Hnab Hab
-- /FOLD

-- QUIZ
-- To prove the following proposition, which tactics will we
--    need besides `intro` and `apply`/`exact`?
--
--         ∀ P Q : Prop, P ∨ Q → ¬¬(P ∨ Q)
--
--     (A) `obtain`, `unfold Not`, `left` and `right`
--
--     (B) `obtain` and `unfold Not`
--
--     (C) only `obtain`
--
--     (D) `left` and/or `right`
--
--     (E) only `unfold Not`
--
--     (F) none of the above

-- /QUIZ
-- FOLD
theorem quiz2 (P Q : Prop) : P ∨ Q → ¬¬(P ∨ Q) := by
  intro HPQ HnPQ; exact HnPQ HPQ
-- /FOLD

-- QUIZ
-- To prove the following proposition, which tactics will we
--    need besides `intro` and `apply`/`exact`?
--
--          ∀ P Q : Prop, P → (P ∨ ¬¬Q)
--
--     (A) `obtain`, `unfold Not`, `left` and `right`
--
--     (B) `obtain` and `unfold Not`
--
--     (C) only `obtain`
--
--     (D) `left` and/or `right`
--
--     (E) only `unfold Not`
--
--     (F) none of the above

-- /QUIZ
-- FOLD
theorem quiz3 (P Q : Prop) : P → (P ∨ ¬¬Q) := by
  intro HP; left; exact HP
-- /FOLD

-- QUIZ
-- To prove the following proposition, which tactics will we need
--    besides `intro` and `apply`/`exact`?
--
--          ∀ P Q : Prop, P ∨ Q → ¬¬P ∨ ¬¬Q
--
--     (A) `obtain`, `unfold Not`, `left` and `right`
--
--     (B) `obtain` and `unfold Not`
--
--     (C) only `obtain`
--
--     (D) `left` and/or `right`
--
--     (E) only `unfold Not`
--
--     (F) none of the above

-- /QUIZ
-- FOLD
theorem quiz4 (P Q : Prop) : P ∨ Q → ¬¬P ∨ ¬¬Q := by
  intro H
  obtain HP | HQ := H
  · left; intro HnP; exact HnP HP
  · right; intro HnQ; exact HnQ HQ
-- /FOLD

-- QUIZ
-- To prove the following proposition, which tactics will we need
--    besides `intro` and `apply`/`exact`?
--
--          ∀ A : Prop, 1 = 0 → (A ∨ ¬A)
--
--     (A) `contradiction`, `unfold Not`, `left` and `right`
--
--     (B) `contradiction` and `unfold Not`
--
--     (C) only `contradiction`
--
--     (D) `left` and/or `right`
--
--     (E) only `unfold Not`
--
--     (F) none of the above

-- /QUIZ
-- FOLD
theorem quiz5 (A : Prop) : 1 = 0 → (A ∨ ¬A) := by
  intro H; contradiction
-- /FOLD
-- /TERSE

-- ** Truth

-- Besides `False`, Lean's standard library also defines `True`, a
--    proposition that is trivially true. To prove it, we use the
--    constant `True.intro`, which is also defined in the standard
--    library:

theorem True_is_true : True := by
  exact True.intro

-- Unlike `False`, which is used extensively, `True` is used
--    relatively rarely: it is trivial (and therefore uninteresting) to
--    prove as a goal, and it provides no useful information when it
--    appears as a hypothesis.

-- FULL
-- However, `True` can be quite useful when defining complex `Prop`s using
--    conditionals or as a parameter to higher-order `Prop`s. We'll come back
--    to this later.
--
--    For now, let's take a look at how we can use `True` and `False` to
--    achieve an effect similar to that of the `contradiction` tactic, without
--    literally using `contradiction`.

-- Pattern-matching lets us do different things for different
--    constructors.  If the result of applying two different
--    constructors were hypothetically equal, then we could use `match`
--    to convert an unprovable statement (like `False`) to one that is
--    provable (like `True`).

def disc_fn (n : Nat) : Prop :=
  match n with
  | 0 => True
  | _ + 1 => False

theorem disc_example : ∀ n, ¬(0 = n + 1) := by
  intro n contra
  have H : disc_fn 0 := True.intro
  rw [contra] at H
  exact H

-- To generalize this to other constructors, we simply have to provide an
--    appropriate variant of `disc_fn`. To generalize it to other
--    conclusions, we can use `exfalso` to replace them with `False`.
--
--    The built-in `contradiction` tactic takes care of all this for us.

-- EX2AM? (nil_is_not_cons)

-- Use the same technique as above to show that `[] ≠ x :: xs`.
-- Do not use the `contradiction` tactic.

def is_nil {X : Type} (l : List X) : Prop :=
  match l with
  | [] => True
  | _ => False

theorem nil_is_not_cons (X : Type) (x : X) (xs : List X) :
  ¬([] = x :: xs) := by
  -- ADMITTED
  intro Heq
  have H : @is_nil X [] := True.intro
  rw [Heq] at H
  exact H
  -- /ADMITTED
-- []
-- /FULL

-- ** Logical Equivalence

-- The handy "if and only if" connective, which asserts that two
--    propositions have the same truth value, is simply the conjunction
--    of two implications.
--
-- In Lean, `↔` is notation for `Iff`:
--   Iff A B = (A → B) ∧ (B → A)

-- TERSE: ***
theorem iff_sym (P Q : Prop) :
  (P ↔ Q) → (Q ↔ P) := by
  -- WORKINCLASS
  intro ⟨HAB, HBA⟩
  exact ⟨HBA, HAB⟩
-- /WORKINCLASS

theorem not_true_iff_false (b : Bool) :
  b ≠ true ↔ b = false := by
  constructor
  · -- →
    exact not_true_is_false b
  · -- ←
    intro H H'
    rw [H] at H'
    contradiction

-- TERSE: ***
-- TERSE: The `rw` tactic can also be used with `↔`.
-- FULL: We can also use `rw` with an `↔` in either direction,
--    without explicitly thinking about the fact that it is really an
--    `And` underneath.

theorem apply_iff_example1 (P Q R : Prop) :
  (P ↔ Q) → (Q → R) → (P → R) := by
  intro Hiff H HP; exact H (Hiff.mp HP)

theorem apply_iff_example2 (P Q R : Prop) :
  (P ↔ Q) → (P → R) → (Q → R) := by
  intro Hiff H HQ; exact H (Hiff.mpr HQ)

-- TERSE: HIDEFROMHTML
-- EX1? (iff_properties)
-- Using the above proof that `↔` is symmetric (`iff_sym`) as
--    a guide, prove that it is also reflexive and transitive.

theorem iff_refl' (P : Prop) :
  P ↔ P := by
  -- ADMITTED
  exact Iff.rfl
  -- /ADMITTED

theorem iff_trans' (P Q R : Prop) :
  (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  -- ADMITTED
  intro HPQ HQR
  exact Iff.trans HPQ HQR
  -- /ADMITTED
-- []
-- TERSE: /HIDEFROMHTML

-- FULL
-- EX3 (or_distributes_over_and)
theorem or_distributes_over_and (P Q R : Prop) :
  P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  -- ADMITTED
  constructor
  · intro H
    obtain HP | ⟨HQ, HR⟩ := H
    · exact ⟨Or.inl HP, Or.inl HP⟩
    · exact ⟨Or.inr HQ, Or.inr HR⟩
  · intro ⟨HPQ, HPR⟩
    obtain HP | HQ := HPQ
    · exact Or.inl HP
    · obtain HP | HR := HPR
      · exact Or.inl HP
      · exact Or.inr ⟨HQ, HR⟩
  -- /ADMITTED
-- []
-- /FULL

-- ** Setoids and Logical Equivalence

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "Some of Rocq's tactics treat `iff` statements specially...
--    To enable this behavior, we have to import the Rocq library that
--    supports it: `From Stdlib Require Import Setoids.Setoid.`"
-- ADAPTED:
-- In Lean, `rw` and `simp` can be used with `↔` statements in `Prop`
-- contexts, not just equalities.  Lean handles this via type classes
-- and the `Iff` type, so no special imports are needed.

-- FULL: A "setoid" is a set equipped with an equivalence relation -- that
--    is, a relation that is reflexive, symmetric, and transitive.  When two
--    elements of a set are equivalent according to the relation, `rw`
--    can be used to replace one by the other.
--
--    We've seen this already with the equality relation `=` in Lean: when
--    `x = y`, we can use `rw` to replace `x` with `y` or vice-versa.
--
--    Similarly, the logical equivalence relation `↔` is reflexive,
--    symmetric, and transitive, so we can use it to replace one part of a
--    proposition with another: if `P ↔ Q`, then we can use `rw` to
--    replace `P` with `Q`, or vice-versa.

-- TERSE: A "setoid" is a set equipped with an equivalence relation,
--    such as `=` or `↔`.

-- TERSE: ***

-- Here is a simple example demonstrating how these tactics work with
--    `↔`.
--
--    First, let's prove a couple of basic iff equivalences. (For these
--    proofs we are not using setoids yet.)

theorem mul_eq_0 (n m : Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
-- FOLD
  constructor
  · exact mult_is_O n m
  · exact factor_is_O n m
-- /FOLD

theorem or_assoc' (P Q R : Prop) :
  P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := by
-- FOLD
  constructor
  · intro H
    obtain HP | HQR := H
    · exact Or.inl (Or.inl HP)
    · obtain HQ | HR := HQR
      · exact Or.inl (Or.inr HQ)
      · exact Or.inr HR
  · intro H
    obtain HPQ | HR := H
    · obtain HP | HQ := HPQ
      · exact Or.inl HP
      · exact Or.inr (Or.inl HQ)
    · exact Or.inr (Or.inr HR)
-- /FOLD

-- We can now use these facts with `rw` and `rfl` to
--    prove a ternary version of the `mul_eq_0` fact above _without_
--    splitting the top-level iff:

theorem mul_eq_0_ternary (n m p : Nat) :
  n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 := by
  rw [mul_eq_0 (n * m) p, mul_eq_0 n m, or_assoc']

-- SOONER: CH: An exercise would be nice here.

-- ############################################################
-- ** Existential Quantification

-- FULL: Another fundamental logical connective is _existential
--    quantification_. To say that there is some `x` of type `T` such
--    that some property `P` holds of `x`, we write `∃ x : T, P`.
--    As with `∀`, the type annotation `: T` can be omitted if Lean
--    is able to infer from the context what the type of `x` should be.

-- To prove a statement of the form `∃ x, P`, we must show that `P`
--    holds for some specific choice for `x`, known as the _witness_ of the
--    existential.  This is done in two steps: First, we explicitly tell Lean
--    which witness `t` we have in mind by invoking `use t` or anonymous
--    constructor syntax `⟨t, proof⟩`.
--    Then we prove that `P` holds after all occurrences of `x` are replaced
--    by `t`.

def Even (x : Nat) := ∃ n : Nat, x = double n
#check (Even : Nat → Prop)

theorem four_is_Even : Even 4 := by
  unfold Even; exact ⟨2, by rfl⟩

-- TERSE: ***
-- Conversely, if we have an existential hypothesis `∃ x, P x` in
--    the context, we can destruct it to obtain a witness `x` and a
--    hypothesis stating that `P` holds of `x`.

theorem exists_example_2 :
  ∀ n, (∃ m, n = 4 + m) → (∃ o, n = 2 + o) := by
  -- WORKINCLASS
  intro n ⟨m, Hm⟩  -- note the implicit decomposition here
  exact ⟨2 + m, by omega⟩
-- /WORKINCLASS

-- FULL
-- EX1! (dist_not_exists)
-- Prove that "`P` holds for all `x`" implies "there is no `x` for
--    which `P` does not hold."  (Hint: `obtain ⟨x, E⟩ := H` works on
--    existential assumptions!)

theorem dist_not_exists (X : Type) (P : X → Prop) :
  (∀ x, P x) → ¬(∃ x, ¬P x) := by
  -- ADMITTED
  intro H ⟨x, Hx⟩
  exact Hx (H x)
  -- /ADMITTED
-- GRADE_THEOREM 1: dist_not_exists
-- []

-- EX2 (dist_exists_or)
-- FULL: Prove that existential quantification distributes over
--    disjunction.

theorem dist_exists_or (X : Type) (P Q : X → Prop) :
  (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  -- ADMITTED
  constructor
  · -- →
    intro ⟨x, HPQ⟩
    obtain HP | HQ := HPQ
    · left; exact ⟨x, HP⟩
    · right; exact ⟨x, HQ⟩
  · -- ←
    intro H
    obtain ⟨x, Hx⟩ | ⟨x, Hx⟩ := H
    · exact ⟨x, Or.inl Hx⟩
    · exact ⟨x, Or.inr Hx⟩
  -- /ADMITTED
-- GRADE_THEOREM 2: dist_exists_or
-- []

-- EX3? (leb_plus_exists)
theorem leb_plus_exists (n m : Nat) :
  Nat.ble n m = true → ∃ x, m = n + x := by
-- ADMITTED
  intro H
  induction n generalizing m with
  | zero => exact ⟨m, by simp⟩
  | succ n' ih =>
    cases m with
    | zero => simp [Nat.ble] at H
    | succ m' =>
      simp only [Nat.ble] at H
      obtain ⟨x, hx⟩ := ih m' H
      exact ⟨x, by omega⟩
-- /ADMITTED

theorem leb_plus (n m : Nat) : (Nat.ble n (n + m)) = true := by
  simp [Nat.ble_eq]

theorem plus_exists_leb (n m : Nat) :
  (∃ x, m = n + x) → Nat.ble n m = true := by
  -- ADMITTED
  intro ⟨x, Hx⟩
  rw [Hx]
  exact leb_plus n x
  -- /ADMITTED
-- []
-- /FULL

-- TERSE
-- ############################################################
-- ** Recap -- Logical connectives in Lean

-- Basic connectives:
--    - `And : Prop → Prop → Prop` (conjunction):
--      - introduced with the `constructor` tactic
--      - eliminated with `obtain ⟨H1, H2⟩ := H`
--    - `Or : Prop → Prop → Prop` (disjunction):
--      - introduced with `left` and `right` tactics
--      - eliminated with `obtain H1 | H2 := H`
--    - `False : Prop`
--      - eliminated with `exact H.elim` or `contradiction`
--    - `True : Prop`
--      - introduced with `exact True.intro`, but not as useful
--    - `Exists : {α : Type} → (α → Prop) → Prop` (existential)
--      - introduced with `use w` or `exact ⟨w, proof⟩`
--      - eliminated with `obtain ⟨x, H⟩ := H`
--
-- Derived connectives:
--    - `Not : Prop → Prop` (negation):
--      - `Not P` defined as `P → False`
--    - `Iff : Prop → Prop → Prop` (logical equivalence):
--      - `Iff P Q` defined as `(P → Q) ∧ (Q → P)`
--
-- Fundamental connectives we've been using since the beginning:
--    - equality (`e1 = e2`)
--    - implication (`P → Q`)
--    - universal quantification (`∀ x, P`)

-- /TERSE

-- ######################################################################
-- * Programming with Propositions

-- FULL: The logical connectives that we have seen provide a rich
--    vocabulary for defining complex propositions from simpler ones.
--    To illustrate, let's look at how to express the claim that an
--    element `x` occurs in a list `l`.  Notice that this property has a
--    simple recursive structure:
-- TERSE: What does it mean to say that "an element `x` occurs in a
--    list `l`"?
--    - If `l` is the empty list, then `x` cannot occur in it, so the
--      property "`x` appears in `l`" is simply false.
--    - Otherwise, `l` has the form `x' :: l'`.  In this case, `x`
--      occurs in `l` if it is equal to `x'` or it occurs in `l'`.

-- We can translate this directly into a straightforward recursive
--    function taking an element and a list and returning... a proposition!

def In {A : Type} (x : A) (l : List A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x ∨ In x l'

-- TERSE: ***
-- When `In` is applied to a concrete list, it expands into a
--    concrete sequence of nested disjunctions.

example : In 4 [1, 2, 3, 4, 5] := by
  -- WORKINCLASS
  dsimp [In]; right; right; right; left; rfl
-- /WORKINCLASS

example :
  ∀ n, In n [2, 4] →
  ∃ n', n = 2 * n' := by
  -- WORKINCLASS
  intro n H
  dsimp [In] at H
  obtain rfl | rfl | H := H
  · exact ⟨1, by rfl⟩
  · exact ⟨2, by rfl⟩
  · exact H.elim
  -- (Notice the use of the empty pattern to discharge the last case
  --    _en passant_.)
-- /WORKINCLASS

-- TERSE: ***

-- We can also reason about more generic statements involving `In`.

-- TERSE: FOLD
theorem In_map (A B : Type) (f : A → B) (l : List A) (x : A) :
  In x l →
  In (f x) (map f l) := by
  intro H
  induction l with
  | nil =>
    -- l = nil, contradiction
    exact H.elim
  | cons x' l' ih =>
    -- l = x' :: l'
    dsimp [In, map] at *
    obtain rfl | H := H
    · left; rfl
    · right; exact ih H
-- TERSE: /FOLD

-- FULL: (Note here how `In` starts out applied to a variable and only
--    gets expanded when we do case analysis on this variable.)

-- FULL
-- This way of defining propositions recursively is very convenient in
--    some cases, less so in others.  In particular, it is subject to Lean's
--    usual restrictions regarding definitions of recursive functions,
--    e.g., the requirement that they be "obviously terminating."
--
--    In the next chapter, we will see how to define propositions
--    _inductively_ -- a different technique with its own strengths and
--    limitations.

-- EX2 (In_map_iff)
theorem In_map_iff (A B : Type) (f : A → B) (l : List A) (y : B) :
  In y (map f l) ↔
  ∃ x, f x = y ∧ In x l := by
  constructor
  · intro H
    induction l with
    -- ADMITTED
    | nil =>
      -- l = nil, contradiction
      exact H.elim
    | cons x l' ih =>
      -- l = x :: l'
      dsimp [In, map] at *
      obtain rfl | H := H
      · exact ⟨x, rfl, Or.inl rfl⟩
      · obtain ⟨x', Hfx', HIn⟩ := ih H
        exact ⟨x', Hfx', Or.inr HIn⟩
  · intro ⟨x, Hfx, HIn⟩
    rw [← Hfx]
    exact In_map A B f l x HIn
  -- /ADMITTED
-- []

-- EX2 (In_app_iff)
-- LATER: The CIS500 exam in Fall 2020 included an informal proof of
--    this.  We might want to turn it into a(n optional) exercise.
theorem In_app_iff (A : Type) (l l' : List A) (a : A) :
  In a (l ++ l') ↔ In a l ∨ In a l' := by
  induction l with
  -- ADMITTED
  | nil =>
    dsimp [In, List.nil_append]
    constructor
    · intro H; right; exact H
    · intro H
      obtain H | H := H
      · exact H.elim
      · exact H
  | cons x t ih =>
    dsimp [In, List.cons_append]
    constructor
    · intro H
      obtain rfl | H := H
      · left; left; rfl
      · rw [ih] at H
        obtain Ht | Hl' := H
        · left; right; exact Ht
        · right; exact Hl'
    · intro H
      obtain (rfl | Ht) | Hl' := H
      · left; rfl
      · right; rw [ih]; left; exact Ht
      · right; rw [ih]; right; exact Hl'
  -- /ADMITTED
-- []
-- /FULL

-- FULL
-- EX3! (All)
-- We noted above that functions returning propositions can be seen as
--    _properties_ of their arguments. For instance, if `P` has type
--    `Nat → Prop`, then `P n` says that property `P` holds of `n`.
--
--    Drawing inspiration from `In`, write a recursive function `All`
--    stating that some property `P` holds of all elements of a list
--    `l`. To make sure your definition is correct, prove the `All_In`
--    theorem below.  (Of course, your definition should _not_ just
--    restate the left-hand side of `All_In`.)

-- ADMITDEF
def All {T : Type} (P : T → Prop) (l : List T) : Prop :=
  match l with
  | [] => True
  | x :: l' => P x ∧ All P l'
-- /ADMITDEF

theorem All_In (T : Type) (P : T → Prop) (l : List T) :
  (∀ x, In x l → P x) ↔
  All P l := by
  -- ADMITTED
  induction l with
  | nil =>
    dsimp [In, All]
    exact ⟨fun _ => True.intro, fun _ _ h => h.elim⟩
  | cons x l' ih =>
    dsimp [In, All]
    constructor
    · intro H
      constructor
      · exact H x (Or.inl rfl)
      · rw [← ih]
        intro x' Hx'
        exact H x' (Or.inr Hx')
    · intro ⟨Hx, Hall⟩ x' Hx'
      obtain rfl | HIn := Hx'
      · exact Hx
      · rw [← ih] at Hall
        exact Hall x' HIn
  -- /ADMITTED
-- GRADE_THEOREM 3: All_In
-- []

-- EX2? (combine_odd_even)
-- Complete the definition of `combine_odd_even` below.  It takes as
--    arguments two properties of numbers, `Podd` and `Peven`, and it should
--    return a property `P` such that `P n` is equivalent to `Podd n` when
--    `n` is odd and equivalent to `Peven n` otherwise.

-- ADMITDEF
def combine_odd_even (Podd Peven : Nat → Prop) : Nat → Prop :=
  fun n => if odd n then Podd n else Peven n
-- /ADMITDEF

-- To test your definition, prove the following facts:

theorem combine_odd_even_intro
  (Podd Peven : Nat → Prop) (n : Nat) :
    (odd n = true → Podd n) →
    (odd n = false → Peven n) →
    combine_odd_even Podd Peven n := by
  -- ADMITTED
  intro Hodd Heven
  unfold combine_odd_even
  cases H : odd n
  · exact Heven H
  · exact Hodd H
  -- /ADMITTED

theorem combine_odd_even_elim_odd
  (Podd Peven : Nat → Prop) (n : Nat) :
    combine_odd_even Podd Peven n →
    odd n = true →
    Podd n := by
  -- ADMITTED
  unfold combine_odd_even
  intro H Hodd
  rw [Hodd] at H
  dsimp at H
  exact H
  -- /ADMITTED

theorem combine_odd_even_elim_even
  (Podd Peven : Nat → Prop) (n : Nat) :
    combine_odd_even Podd Peven n →
    odd n = false →
    Peven n := by
  -- ADMITTED
  unfold combine_odd_even
  intro H Heven
  rw [Heven] at H
  dsimp at H
  exact H
  -- /ADMITTED
-- []
-- /FULL

-- ######################################################################
-- * Applying Theorems to Arguments

-- FULL: One feature that distinguishes Lean from some other popular proof
--    assistants (e.g., ACL2 and Isabelle) is that it treats _proofs_ as
--    first-class objects.
--
--    There is a great deal to be said about this, but it is not necessary to
--    understand it all in order to use Lean.  This section gives just a
--    taste, leaving a deeper exploration for the optional chapters
--    `ProofObjects` and `IndPrinciples`.
-- TERSE: Lean also treats _proofs_ as first-class objects!

-- We have seen that we can use `#check` to ask Lean to check whether
--    an expression has a given type:

#check (Nat.add : Nat → Nat → Nat)
#check (@rev : {α : Type} → List α → List α)

-- We can also use it to check what theorem a particular identifier
--    refers to:

#check @add_comm  -- ∀ n m, n + m = m + n

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "Check plus_id_example : ..."
-- ADAPTED:
-- The Lean version of `plus_id_example` might not exist with that
-- exact name; the point is that we can `#check` theorem statements.

-- Lean checks the _statements_ of theorems
--    in the same way that it checks the _type_ of any term (e.g., Nat.add).
--    If we leave off the colon and type, Lean will print these types for us.

-- TERSE: ***
-- The reason is that the identifier `add_comm` actually refers to a
--    _proof object_ -- a logical derivation establishing the truth of the
--    statement `∀ n m : Nat, n + m = m + n`.  The type of this object
--    is the proposition that it is a proof of.
-- TERSE: ***
-- The type of an ordinary function tells us what we can do with it.
--    - If we have a term of type `Nat → Nat → Nat`, we can give it two
--      `Nat`s as arguments and get a `Nat` back.
--
--    Similarly, the statement of a theorem tells us what we can use that
--    theorem for.
--    - If we have a term of type `∀ n m, n = m → n + n = m + m` and we
--      provide it two numbers `n` and `m` and a third "argument" of type
--      `n = m`, we get back a proof object of type `n + n = m + m`.

-- FULL: Operationally, this analogy goes even further: by applying a
--    theorem as if it were a function, i.e., applying it to values and
--    hypotheses with matching types, we can specialize its result
--    without having to resort to intermediate assertions.  For example,
--    suppose we wanted to prove the following result:
-- TERSE: ***
-- TERSE: Lean actually allows us to _apply_ a theorem as if it were a
--    function.
--
--    This is often handy in proof scripts -- e.g., suppose we want to
--    prove the following:

theorem add_comm3 :
  ∀ x y z : Nat, x + (y + z) = (z + y) + x := by

-- It appears at first sight that we ought to be able to prove this by
--    rewriting with `add_comm` twice to make the two sides match.  The
--    problem is that the second `rw` will undo the effect of the
--    first.

  intro x y z
  rw [add_comm]
  rw [add_comm]
  -- We are back where we started...
  sorry

-- FULL
-- We encountered similar issues back in Induction, and we saw
--    one way to work around them by using `have` to derive a specialized
--    version of `add_comm` that can be used to rewrite exactly where we
--    want.

theorem add_comm3_take2 :
  ∀ x y z : Nat, x + (y + z) = (z + y) + x := by
  intro x y z
  rw [add_comm]
  have H : y + z = z + y := by rw [add_comm]
  rw [H]
-- /FULL

-- FULL: A more elegant alternative is to apply `add_comm` directly
--    to the arguments we want to instantiate it with, in much the same
--    way as we apply a polymorphic function to a type argument.
-- TERSE: ***
-- TERSE: We can fix this by applying `add_comm` to the arguments we want
--    it to be instantiated with.  Then the `rw` is forced to happen
--    exactly where we want it.

theorem add_comm3_take3 :
  ∀ x y z : Nat, x + (y + z) = (z + y) + x := by
  intro x y z
  rw [add_comm]
  rw [add_comm y z]

-- FULL
-- If we really wanted, we could in fact do it for both rewrites.

theorem add_comm3_take4 :
  ∀ x y z : Nat, x + (y + z) = (z + y) + x := by
  intro x y z
  rw [add_comm x (y + z)]
  rw [add_comm y z]
-- /FULL

-- TERSE: ***
-- Here's another example of using a theorem about lists like
--    a function.  Suppose we have proved the following simple fact
--    about lists...

theorem in_not_nil (A : Type) (x : A) (l : List A) :
  In x l → l ≠ [] := by
-- FOLD
  intro H Hl
  rw [Hl] at H
  exact H
-- /FOLD

-- FULL: (I.e., if a list `l` contains some element `x`, then `l`
--    must be nonempty.)

-- Note that one quantified variable (`x`) does not appear in
--    the conclusion (`l ≠ []`).

-- Intuitively, we should be able to use this theorem to prove the special
--    case where `x` is `42`. However, simply invoking the tactic `apply
--    in_not_nil` will fail because it cannot infer the value of `x`.

theorem in_not_nil_42 :
  ∀ l : List Nat, In 42 l → l ≠ [] := by
  intro l H
  -- `apply in_not_nil` would fail here
  sorry

-- TERSE: ***
-- There are several ways to work around this:

-- We can use `apply ... (x := ...)`:
theorem in_not_nil_42_take2 :
  ∀ l : List Nat, In 42 l → l ≠ [] := by
  intro l H
  exact in_not_nil Nat 42 l H

-- TERSE: ***
-- Or we can use `apply ... at ...`:
theorem in_not_nil_42_take3 :
  ∀ l : List Nat, In 42 l → l ≠ [] := by
  intro l H
  exact in_not_nil _ _ _ H

-- TERSE: ***
-- Or -- this is the new one -- we can explicitly
--    apply the lemma to the value `42` for `x`:
theorem in_not_nil_42_take4 :
  ∀ l : List Nat, In 42 l → l ≠ [] := by
  intro l H
  exact in_not_nil Nat 42 l H

-- TERSE: ***
-- We can also explicitly apply the lemma to a hypothesis,
--    causing the values of the other parameters to be inferred:
theorem in_not_nil_42_take5 :
  ∀ l : List Nat, In 42 l → l ≠ [] := by
  intro l H
  exact in_not_nil _ _ _ H

-- FULL
-- You can "use a theorem as a function" in this way with almost any
--    tactic that can take a theorem's name as an argument.
--
--    Note, also, that theorem application uses the same inference
--    mechanisms as function application; thus, it is possible, for
--    example, to supply wildcards as arguments to be inferred, or to
--    declare some hypotheses to a theorem as implicit by default.
--    These features are illustrated in the proof below. (The details of
--    how this proof works are not critical -- the goal here is just to
--    illustrate applying theorems to arguments.)

example :
  ∀ {n : Nat} {ns : List Nat},
    In n (map (fun m => m * 0) ns) →
    n = 0 := by
  intro n ns H
  rw [In_map_iff] at H
  obtain ⟨m, Hm, _⟩ := H
  simp [mul_zero] at Hm
  exact Hm.symm

-- We will see many more examples in later chapters.
-- /FULL

-- HIDEFROMADVANCED
-- TERSE

-- HIDEFROMHTML
-- HIDE
section FunctionTheoremQuiz
variable (a b : Nat)
variable (H1 : a = b)
variable (H2 : b = 42)
-- /HIDE

-- QUIZ
-- Suppose we have
--
--       a, b : Nat
--       H1 : a = b
--       H2 : b = 42
--       trans_eq : ∀ {α : Type} (x y z : α),
--                    x = y → y = z → x = z
--
--    What is the type of this "proof object"?
--
--       trans_eq a b 42 H1 H2
--
--     (A) `a = b`
--
--     (B) `42 = a`
--
--     (C) `a = 42`
--
--     (D) Does not typecheck

-- /QUIZ
-- FOLD
#check trans_eq a b 42 H1 H2
  -- : a = 42
-- /FOLD

-- QUIZ
-- Suppose, again, that we have
--
--       a, b : Nat
--       H1 : a = b
--       H2 : b = 42
--       trans_eq : ∀ {α : Type} (x y z : α),
--                    x = y → y = z → x = z
--
--    What is the type of this proof object?
--
--       trans_eq _ _ _ H1 H2
--
--     (A) `a = b`
--
--     (B) `42 = a`
--
--     (C) `a = 42`
--
--     (D) Does not typecheck

-- /QUIZ
-- FOLD
#check trans_eq _ _ _ H1 H2
  -- : a = 42
-- /FOLD

-- QUIZ
-- SOONER: BCP 25: Not sure whether the rest of these quizzes are useful
--    enough to justify explaining them in class.
-- Suppose, again, that we have
--
--       a, b : Nat
--       H1 : a = b
--       H2 : b = 42
--       trans_eq : ∀ {α : Type} (x y z : α),
--                    x = y → y = z → x = z
--
--    What is the type of this proof object?
--
--       trans_eq b 42 a H2
--
--     (A) `b = a`
--
--     (B) `b = a → 42 = a`
--
--     (C) `42 = a → b = a`
--
--     (D) Does not typecheck

-- /QUIZ
-- FOLD
#check trans_eq b 42 a H2
    -- : 42 = a → b = a
-- /FOLD

-- QUIZ
-- Suppose, again, that we have
--
--       a, b : Nat
--       H1 : a = b
--       H2 : b = 42
--       trans_eq : ∀ {α : Type} (x y z : α),
--                    x = y → y = z → x = z
--
--    What is the type of this proof object?
--
--       trans_eq 42 a b
--
--     (A) `a = b → b = 42 → a = 42`
--
--     (B) `42 = a → a = b → 42 = b`
--
--     (C) `a = 42 → 42 = b → a = b`
--
--     (D) Does not typecheck

-- /QUIZ
-- FOLD
#check trans_eq 42 a b
    -- : 42 = a → a = b → 42 = b
-- /FOLD

-- QUIZ
-- Suppose, again, that we have
--
--       a, b : Nat
--       H1 : a = b
--       H2 : b = 42
--       trans_eq : ∀ {α : Type} (x y z : α),
--                    x = y → y = z → x = z
--
--    What is the type of this proof object?
--
--       trans_eq _ _ _ H2 H1
--
--     (A) `b = a`
--
--     (B) `42 = a`
--
--     (C) `a = 42`
--
--     (D) Does not typecheck

-- /QUIZ
-- FOLD
-- This does not typecheck because H2 : b = 42 and H1 : a = b
-- would require the middle argument to be both 42 and a, which
-- would require 42 = a to hold. The types don't match up.
-- `trans_eq _ _ _ H2 H1` would be b = b (if it worked), but
-- the middle `42` from H2 doesn't match `a` from H1.
-- /FOLD

-- HIDE
end FunctionTheoremQuiz
-- /HIDE
-- /TERSE
-- /HIDEFROMADVANCED

-- ######################################################################
-- * Working with Decidable Properties

-- We've seen two different ways of expressing logical claims in Lean:
--    with _booleans_ (of type `Bool`), and with _propositions_ (of type
--    `Prop`).
--
--    Here are the key differences between `Bool` and `Prop`:
--
--                                           Bool     Prop
--                                           ====     ====
--          decidable?                      yes       no
--          useable with if/match?          yes       yes*
--          works with rw tactic?           no        yes
--
-- (*In Lean, `if` works with `Prop` when there is a `Decidable` instance!)

-- FULL: The crucial difference between the two worlds is _decidability_.
--    Every (closed) Lean expression of type `Bool` can be simplified in a
--    finite number of steps to either `true` or `false` -- i.e., there is a
--    terminating mechanical procedure for deciding whether or not it is
--    `true`.
--
--    This means that, for example, the type `Nat → Bool` is inhabited only
--    by functions that, given a `Nat`, always yield either `true` or `false`
--    in finite time; and this, in turn, means (by a standard computability
--    argument) that there is _no_ function in `Nat → Bool` that checks
--    whether a given number is the code of a terminating Turing machine.
--
--    By contrast, the type `Prop` includes both decidable and undecidable
--    mathematical propositions; in particular, the type `Nat → Prop` does
--    contain functions representing properties like "the nth Turing machine
--    halts."
--
--    The second row in the table follows directly from this essential
--    difference.  To evaluate a pattern match (or conditional) on a boolean,
--    we need to know whether the scrutinee evaluates to `true` or `false`;
--    this only works for `Bool`, not `Prop`.  (However, in Lean, the
--    `Decidable` type class bridges this gap for many standard propositions.)
--
--    The third row highlights an important practical difference:
--    equality functions like `Nat.beq` that return a boolean cannot be
--    used directly to justify rewriting with the `rw` tactic;
--    propositional equality is required for this.

-- TERSE: Since every function terminates on all inputs in Lean, a function
--    of type `Nat → Bool` is a _decision procedure_ -- i.e., it yields
--    `true` or `false` on all inputs.
--
--      - For example, `even : Nat → Bool` is a decision procedure for the
--        property "is even".

-- TERSE: ***
-- TERSE: It follows that there are some properties of numbers that we _cannot_
--    express as functions of type `Nat → Bool`.
--
--      - For example, the property "is the code of a halting Turing machine"
--        is undecidable, so there is no way to write it as a function of
--        type `Nat → Bool`.
--
--    On the other hand, `Nat → Prop` is the type of _all_ properties of
--    numbers that can be expressed in Lean's logic, including both decidable
--    and undecidable ones.
--
--      - For example, "is the code of a halting Turing machine" is a
--        perfectly legitimate mathematical property, and we can absolutely
--        represent it as a Lean expression of type `Nat → Prop`.

-- TERSE: ***

-- Since `Prop` includes _both_ decidable and undecidable properties, we
--    have two options when we want to formalize a property that happens to
--    be decidable: we can express it either as a boolean computation or as a
--    function into `Prop`.

-- TERSE: For instance, to claim that a number `n` is even, we can say
--    either that `even n` evaluates to `true`...
example : even 42 = true := by rfl

-- ... or that there exists some `k` such that `n = double k`.
example : Even 42 := by
  unfold Even; exact ⟨21, by rfl⟩

-- Of course, it would be deeply strange if these two
--    characterizations of evenness did not describe the same set of
--    natural numbers!
--
--    Fortunately, they do!

-- TERSE: HIDEFROMHTML

-- To prove this, we first need two helper lemmas.

theorem even_double (k : Nat) : even (double k) = true := by
-- FOLD
  induction k with
  | zero => rfl
  | succ k' ih => dsimp [double, even]; exact ih
-- /FOLD

-- FULL
-- EX3 (even_double_conv)
-- /FULL
theorem even_double_conv : ∀ n, ∃ k,
  n = if even n then double k else (double k) + 1 := by
-- FOLD
  -- Hint: Use the `even_S` theorem from `Induction.lean`.
  -- ADMITTED
  intro n
  induction n with
  | zero => exact ⟨0, by rfl⟩
  | succ n' ih =>
    obtain ⟨k, Hk⟩ := ih
    rw [even_S]
    cases H : even n' with
    | true =>
      dsimp
      rw [H] at Hk; dsimp at Hk
      exact ⟨k, by omega⟩
    | false =>
      dsimp
      rw [H] at Hk; dsimp at Hk
      exact ⟨k + 1, by dsimp [double]; omega⟩
  -- /ADMITTED
-- []
-- /FOLD
-- TERSE: /HIDEFROMHTML

-- TERSE: ***
-- Now the main theorem:

theorem even_bool_prop (n : Nat) :
  even n = true ↔ Even n := by
-- FOLD
  constructor
  · intro H
    obtain ⟨k, Hk⟩ := even_double_conv n
    rw [H] at Hk; dsimp at Hk
    exact ⟨k, Hk⟩
  · intro ⟨k, Hk⟩
    rw [Hk]
    exact even_double k
-- /FOLD

-- In view of this theorem, we can say that the boolean computation
--    `even n` is _reflected_ in the truth of the proposition
--    `∃ k, n = double k`.

-- TERSE: ***
-- Similarly, to state that two numbers `n` and `m` are equal, we can
--    say either
--      - (1) that `Nat.beq n m` returns `true`, or
--      - (2) that `n = m`.
--    Again, these two notions are equivalent:

theorem eqb_eq (n1 n2 : Nat) :
  (n1 == n2) = true ↔ n1 = n2 := by
-- FOLD
  constructor
  · exact eqb_true n1 n2
  · intro H; subst H; exact eqb_refl n1
-- /FOLD

-- HIDEFROMADVANCED
-- TERSE: ***

-- So what should we do in situations where some claim could be
--    formalized as either a proposition or a boolean computation? Which
--    should we choose?
--
--    In general, _both_ can be useful.

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "For example, booleans are more useful for defining functions.
--    There is no effective way to _test_ whether or not a `Prop` is
--    true, so we cannot use `Prop`s in conditional expressions."
-- ADAPTED:
-- In Lean, unlike Rocq, we _can_ use `Prop`s in `if` expressions
-- when there is a `Decidable` instance.  For many standard propositions
-- (like `n = m` for natural numbers), Lean automatically provides
-- `Decidable` instances.

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "The following definition is rejected: ..."
-- ADAPTED:
-- In Lean, we can actually write:
def is_even_prime (n : Nat) : Bool :=
  if n = 2 then true else false
-- This works because Lean has a `DecidableEq Nat` instance!

-- FULL: Beyond the fact that non-computable properties are impossible in
--    general to phrase as boolean computations, even many _computable_
--    properties are easier to express using `Prop` than `Bool`, since
--    recursive function definitions in Lean are subject to significant
--    restrictions.  For instance, the next chapter shows how to define the
--    property that a regular expression matches a given string using `Prop`.
--    Doing the same with `Bool` would amount to writing a regular expression
--    matching algorithm, which would be more complicated, harder to
--    understand, and harder to reason about than a simple (non-algorithmic)
--    definition of this property.
--
--    Conversely, an important side benefit of stating facts using booleans
--    is enabling some proof automation through computation with Lean terms, a
--    technique known as _proof by reflection_.
--
--    Consider the following statement:
-- /HIDEFROMADVANCED
-- TERSE: ***
-- TERSE: More generally, stating facts using booleans can often enable
--    effective proof automation through computation with Lean terms, a
--    technique known as _proof by reflection_.
--
--    Consider the following statement:

set_option maxRecDepth 2048 in
example : Even 1000 := by

-- The most direct way to prove this is to give the value of `k`
--    explicitly.

  unfold Even; exact ⟨500, by rfl⟩

-- The proof of the corresponding boolean statement is simpler, because we
--    don't have to invent the witness 500: Lean's computation mechanism
--    does it for us!

example : even 1000 = true := by rfl

-- TERSE: ***
-- Now, the useful observation is that, since the two notions are
--    equivalent, we can use the boolean formulation to prove the other one
--    without mentioning the value 500 explicitly:

set_option maxRecDepth 2048 in
example : Even 1000 := by
  exact (even_bool_prop 1000).mp rfl

-- Although we haven't gained much in terms of proof-script
--    line count in this case, larger proofs can often be made considerably
--    simpler by the use of reflection.  As an extreme example, a famous
--    Rocq proof of the even more famous _4-color theorem_ uses
--    reflection to reduce the analysis of hundreds of different cases
--    to a boolean computation.

-- TERSE: ***

-- Another advantage of booleans is that the _negation_ of a claim
--    about booleans is straightforward to state and (when true) prove:
--    simply flip the expected boolean result.

example : even 1001 = false := by rfl

-- TERSE: ***
-- In contrast, propositional negation can be difficult to work with
--    directly.
--
--    For example, suppose we state the non-evenness of 1001
--    propositionally:

-- Proving this directly -- by assuming that there is some `n` such that
--    `1001 = double n` and then somehow reasoning to a contradiction --
--    would be rather complicated.
--
--    But if we convert it to a claim about the boolean `even` function, we
--    can let Lean do the work for us.

set_option maxRecDepth 2048 in
example : ¬(Even 1001) := by
  -- WORKINCLASS
  rw [← even_bool_prop]
  intro H
  contradiction
-- /WORKINCLASS

-- TERSE: ***

-- Conversely, there are situations where it can be easier to work
--    with propositions rather than booleans.
--
--    In particular, knowing that `(n == m) = true` is generally of
--    little direct help in the middle of a proof involving `n` and `m`.
--    But if we convert the statement to the equivalent form `n = m`,
--    then we can easily `rw` with it.

theorem plus_eqb_example (n m p : Nat) :
  (n == m) = true → (n + p == m + p) = true := by
  -- WORKINCLASS
  intro H
  rw [eqb_eq] at H
  rw [H]
  rw [eqb_eq]
-- /WORKINCLASS

-- FULL: We won't discuss reflection any further for the moment, but
--    it serves as a good example showing the different strengths of
--    booleans and general propositions.

-- Being able to cross back and forth between the boolean and
--    propositional worlds will often be convenient in later chapters.

-- FULL
-- EX2 (logical_connectives)
-- The following theorems relate the propositional connectives studied
--    in this chapter to the corresponding boolean operations.

theorem andb_true_iff (b1 b2 : Bool) :
  (b1 && b2) = true ↔ b1 = true ∧ b2 = true := by
  -- ADMITTED
  cases b1 <;> cases b2 <;> simp
  -- /ADMITTED

theorem orb_true_iff (b1 b2 : Bool) :
  (b1 || b2) = true ↔ b1 = true ∨ b2 = true := by
  -- ADMITTED
  cases b1 <;> cases b2 <;> simp
  -- /ADMITTED
-- GRADE_THEOREM 1: andb_true_iff
-- GRADE_THEOREM 1: orb_true_iff
-- []

-- EX1 (eqb_neq)
-- The following theorem is an alternate "negative" formulation of
--    `eqb_eq` that is more convenient in certain situations.  (We'll see
--    examples in later chapters.)  Hint: `not_true_iff_false`.

theorem eqb_neq (x y : Nat) :
  (x == y) = false ↔ x ≠ y := by
  -- ADMITTED
  constructor
  · intro h hxy
    subst hxy
    rw [eqb_refl] at h
    contradiction
  · intro h
    cases hbeq : (x == y) with
    | false => rfl
    | true =>
      exfalso
      exact h (eqb_true x y hbeq)
  -- /ADMITTED
-- []

-- EX3 (eqb_list)
-- Given a boolean operator `eqb` for testing equality of elements of
--    some type `A`, we can define a function `eqb_list` for testing
--    equality of lists with elements in `A`.  Complete the definition
--    of the `eqb_list` function below.  To make sure that your
--    definition is correct, prove the lemma `eqb_list_true_iff`.

-- ADMITDEF
def eqb_list {A : Type} (eqb : A → A → Bool) : List A → List A → Bool
  | [], [] => true
  | a1 :: l1, a2 :: l2 => eqb a1 a2 && eqb_list eqb l1 l2
  | _, _ => false
-- /ADMITDEF

theorem eqb_list_true_iff (A : Type) (eqb : A → A → Bool)
    (Heqb : ∀ a1 a2, eqb a1 a2 = true ↔ a1 = a2) :
    ∀ l1 l2, eqb_list eqb l1 l2 = true ↔ l1 = l2 := by
-- ADMITTED
  intro l1
  induction l1 with
  | nil =>
    intro l2
    cases l2 with
    | nil => simp [eqb_list]
    | cons a2 l2 => simp [eqb_list]
  | cons a1 l1 ih =>
    intro l2
    cases l2 with
    | nil => simp [eqb_list]
    | cons a2 l2 =>
      simp only [eqb_list]
      rw [andb_true_iff, Heqb, ih]
      constructor
      · intro ⟨h1, h2⟩; rw [h1, h2]
      · intro h; exact ⟨by injection h, by injection h⟩
-- /ADMITTED

-- GRADE_THEOREM 3: eqb_list_true_iff
-- []
-- /FULL

-- FULL
-- EX2! (All_forallb)
-- Prove the theorem below, which relates `forallb`, from the
--    exercise `forall_exists_challenge` in chapter Tactics, to
--    the `All` property defined above.

-- `forallb` is already defined in Tactics.lean, so we reuse it here.

theorem forallb_true_iff (X : Type) (test : X → Bool) (l : List X) :
  forallb test l = true ↔ All (fun x => test x = true) l := by
  -- ADMITTED
  induction l with
  | nil =>
    dsimp [forallb, All]
    exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | cons x l' ih =>
    dsimp [forallb, All]
    rw [andb_true_iff, ih]
  -- /ADMITTED

-- (Ungraded thought question) Are there any important properties of
--    the function `forallb` which are not captured by this
--    specification?

-- SOLUTION
-- This theorem exactly captures the input-output behaviour of
-- `forallb`. However, it does not say anything about the running
-- time.
-- /SOLUTION
-- GRADE_THEOREM 2: forallb_true_iff
-- []
-- /FULL

-- ######################################################################
-- * The Logic of Lean

-- FULL: Lean's logical core, the _Calculus of Inductive
--    Constructions_, differs in some important ways from other formal
--    systems that are used by mathematicians to write down precise and
--    rigorous definitions and proofs -- in particular from
--    Zermelo-Fraenkel Set Theory (ZFC), the most popular foundation for
--    paper-and-pencil mathematics.
--
--    We conclude this chapter with a brief discussion of some of the
--    most significant differences between these two worlds.
-- TERSE: Lean's logical core, the _Calculus of Inductive Constructions_,
--    is a "metalanguage for mathematics" in the same sense as familiar
--    foundations for paper-and-pencil math, like Zermelo-Fraenkel Set
--    Theory (ZFC).
--
--    Mostly, the differences are not too important, but a few points are
--    useful to understand.

-- ** Functional Extensionality

-- HIDEFROMADVANCED
-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "Rocq's logic is quite minimalistic. This means that one
--    occasionally encounters cases where translating standard mathematical
--    reasoning into Rocq is cumbersome -- or even impossible -- unless we
--    enrich its core logic with additional axioms."
-- ADAPTED:
-- Unlike Rocq, Lean has functional extensionality built in as a theorem
-- (via `funext`), so we do not need to add it as an axiom.

-- FULL: For example, the equality assertions that we have seen so far
--    mostly have concerned elements of inductive types (`Nat`, `Bool`,
--    etc.).  But, since Lean's equality operator is polymorphic, we can use
--    it at _any_ type -- in particular, we can write propositions claiming
--    that two _functions_ are equal to each other:
-- TERSE: A first instance has to do with equality of functions.
-- In certain cases Lean can successfully prove equality propositions stating
--    that two _functions_ are equal to each other:

example :
  (fun x => 3 + x) = (fun x => (Nat.pred 4) + x) := by rfl
-- /HIDEFROMADVANCED

-- TERSE: ***
-- These two functions are equal just by simplification, but in general
--    functions can be equal for more interesting reasons.
--
--    In common mathematical practice, two functions `f` and `g` are
--    considered equal if they produce the same output on every input:
--
--     (∀ x, f x = g x) → f = g
--
--    This is known as the principle of _functional extensionality_.

-- FULL
-- (Informally, an "extensional" property is one that pertains to an
--    object's observable behavior.  Thus, functional extensionality
--    simply means that a function's identity is completely determined
--    by what we can observe from it -- i.e., the results we obtain
--    after applying it.)
-- /FULL

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "However, functional extensionality is not part of Rocq's
--    built-in logic."
-- ADAPTED:
-- Unlike Rocq, functional extensionality _is_ part of Lean's built-in
-- logic.  The `funext` tactic provides it.

-- However, for pedagogical purposes and to match the Rocq development,
-- we can also state it as an axiom:

axiom functional_extensionality : ∀ {X Y : Type}
                                    {f g : X → Y},
  (∀ (x : X), f x = g x) → f = g

-- Defining something as an `axiom` has the same effect as stating a
--    theorem and skipping its proof using `sorry`, but it alerts the
--    reader that this isn't just something we're going to come back and
--    fill in later!

-- TERSE: ***
-- We can now invoke functional extensionality in proofs:

example :
  (fun x => x + 1) = (fun x => 1 + x) := by
  apply functional_extensionality
  intro x
  exact add_comm x 1

-- TERSE: ***
-- Naturally, we need to be quite careful when adding new axioms into
--    Lean's logic, as this can render it _inconsistent_ -- that is, it may
--    become possible to prove every proposition, including `False`, `2+2=5`,
--    etc.!
--
--    In general, there is no simple way of telling whether an axiom is safe
--    to add: hard work by highly trained mathematicians is often required to
--    establish the consistency of any particular combination of axioms.
--
--    Fortunately, it is known that adding functional extensionality, in
--    particular, _is_ consistent.

-- TERSE: ***
-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "To check whether a particular proof relies on any additional
--    axioms, use the `Print Assumptions` command"
-- ADAPTED:
-- To check whether a particular proof relies on any additional
-- axioms, use the `#print axioms` command.

-- FULL: (If you try this yourself, you may also see `add_comm` listed as
--    an assumption, depending on whether the copy of `Tactics.lean` in the
--    local directory has the proof of `add_comm` filled in.)

-- FULL
-- EX4 (tr_rev_correct)
-- One problem with the definition of the list-reversing function `rev`
--    that we have is that it performs a call to `++` on each step.  Running
--    `++` takes time asymptotically linear in the size of the list, which
--    means that `rev` is asymptotically quadratic.
--
--    We can improve this with the following two-argument definition:

def rev_append {X : Type} (l1 l2 : List X) : List X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)

def tr_rev {X : Type} (l : List X) : List X :=
  rev_append l []

-- This version of `rev` is said to be _tail recursive_, because the
--    recursive call to the function is the last operation that needs to be
--    performed (i.e., we don't have to execute `++` after the recursive
--    call); a decent compiler will generate very efficient code in this
--    case.
--
--    Prove that the two definitions are indeed equivalent.

theorem rev_append_rev (X : Type) (l1 l2 : List X) :
  rev_append l1 l2 = rev l1 ++ l2 := by
  induction l1 generalizing l2 with
  | nil => rfl
  | cons x l1' ih =>
    -- rev_append (x :: l1') l2 = rev (x :: l1') ++ l2
    -- unfolds to: rev_append l1' (x :: l2) = (rev l1' ++ [x]) ++ l2
    unfold rev_append rev
    rw [ih, app_assoc]
    rfl

theorem tr_rev_correct (X : Type) : @tr_rev X = @rev X := by
-- ADMITTED
  apply functional_extensionality
  intro l
  unfold tr_rev
  rw [rev_append_rev]
  rw [app_nil_r]
-- /ADMITTED
-- []
-- /FULL

-- ** Classical vs. Constructive Logic

-- FULL: We have seen that it is not possible to test whether or not a
--    proposition `P` holds while defining a Lean function (without a
--    `Decidable` instance).  You may be surprised to learn that a similar
--    restriction applies in _proofs_!
--    In other words, the following intuitive reasoning principle is not
--    derivable in Lean (constructively):
-- TERSE: The following reasoning principle is _not_ derivable in
--    Lean's constructive logic (though it can consistently be added
--    as an axiom, or accessed via `Classical.em`):

def excluded_middle := ∀ P : Prop,
  P ∨ ¬P

-- FULL: To understand operationally why this is the case, recall
--    that, to prove a statement of the form `P ∨ Q`, we use the `left`
--    and `right` tactics, which effectively require knowing which side
--    of the disjunction holds.  But the universally quantified `P` in
--    `excluded_middle` is an _arbitrary_ proposition, which we know
--    nothing about.  We don't have enough information to choose which
--    of `left` or `right` to apply.

-- FULL

-- However, in the special case where we happen to know that `P` is
--    reflected in some boolean term `b`, knowing whether it holds or
--    not is trivial: we just have to check the value of `b`.

theorem restricted_excluded_middle (P : Prop) (b : Bool) :
  (P ↔ b = true) → P ∨ ¬P := by
  intro H
  cases b with
  | true => left; exact H.mpr rfl
  | false => right; intro HP; exact absurd (H.mp HP) (by decide)

-- In particular, the excluded middle is valid for equations `n = m`,
--    between natural numbers `n` and `m`.

theorem restricted_excluded_middle_eq (n m : Nat) :
  n = m ∨ n ≠ m := by
  exact Decidable.em (n = m)

-- Sadly, this trick only works for decidable propositions.

-- /FULL

-- FULL: It may seem strange that the general excluded middle is not
--    available by default in Lean (constructively), since it is a
--    standard feature of familiar logics like ZFC.  But there is a
--    distinct advantage in _not_ assuming the excluded middle:
--    statements in Lean make stronger claims than the analogous
--    statements in standard mathematics.  Notably, a Lean proof of
--    `∃ x, P x` always includes a particular value of `x` for which we
--    can prove `P x` -- in other words, every proof of existence is
--    _constructive_.

-- Logics like Lean's, which do not assume the excluded middle, are
--    referred to as _constructive logics_.
--
--    Logical systems such as ZFC, in which the excluded middle does
--    hold for arbitrary propositions, are referred to as _classical_.

-- FULL
-- The following example illustrates why assuming the excluded middle may
--    lead to non-constructive proofs:
--
--    _Claim_: There exist irrational numbers `a` and `b` such that `a ^
--    b` (`a` to the power `b`) is rational.
--
--    _Proof_: It is not difficult to show that `sqrt 2` is irrational.  So if
--    `sqrt 2 ^ sqrt 2` is rational, it suffices to take `a = b = sqrt 2` and
--    we are done.  Otherwise, `sqrt 2 ^ sqrt 2` is irrational.  In this
--    case, we can take `a = sqrt 2 ^ sqrt 2` and `b = sqrt 2`, since `a ^ b
--    = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2`.  []
--
--    Do you see what happened here?  We used the excluded middle to
--    consider separately the cases where `sqrt 2 ^ sqrt 2` is rational
--    and where it is not, without knowing which one actually holds!
--    Because of this, we finish the proof knowing that such `a` and `b`
--    exist, but not being sure of their actual values.
--
--    As useful as constructive logic is, it does have its limitations:
--    There are many statements that can easily be proven in classical
--    logic but that have only much more complicated constructive
--    proofs, and there are some that are known to have no constructive
--    proof at all!  Fortunately, like functional extensionality, the
--    excluded middle is known to be compatible with Lean's logic,
--    allowing us to add it safely as an axiom. However, we will not
--    need to do so here: the results that we cover in Software
--    Foundations can be developed entirely within constructive logic at
--    negligible extra cost.
--
--    It takes some practice to understand which proof techniques must
--    be avoided in constructive reasoning, but arguments by
--    contradiction, in particular, are infamous for leading to
--    non-constructive proofs. Here's a typical example: suppose that we
--    want to show that there exists `x` with some property `P`, i.e.,
--    such that `P x`.  We start by assuming that our conclusion is
--    false; that is, `¬ ∃ x, P x`. From this premise, it is not
--    hard to derive `∀ x, ¬ P x`.  If we manage to show that this
--    results in a contradiction, we arrive at an existence proof
--    without ever exhibiting a value of `x` for which `P x` holds!
--
--    The technical flaw here, from a constructive standpoint, is that we
--    claimed to prove `∃ x, P x` using a proof of `¬¬(∃ x, P x)`.
--    Allowing ourselves to remove double negations from arbitrary
--    statements is equivalent to assuming the excluded middle law, as shown
--    in one of the exercises below.  Thus, this line of reasoning cannot be
--    encoded in Lean without assuming additional axioms.

-- EX3 (excluded_middle_irrefutable)
-- Proving the consistency of Lean with the general excluded middle
--    axiom requires complicated reasoning that cannot be carried out
--    within Lean itself.  However, the following theorem implies that it
--    is always safe to assume a decidability axiom (i.e., an instance
--    of excluded middle) for any _particular_ Prop `P`.  Why?  Because
--    the negation of such an axiom leads to a contradiction.  If `¬(P
--    ∨ ¬P)` were provable, then by `de_morgan_not_or` as proved above,
--    `¬P ∧ ¬¬P` would be provable, which would be a contradiction.  So, it
--    is safe to add `P ∨ ¬P` as an axiom for any particular `P`.
--
--    Succinctly: for any proposition P,
--        Lean is consistent ==> Lean + (P ∨ ¬P) is consistent.

theorem excluded_middle_irrefutable (P : Prop) :
  ¬¬(P ∨ ¬P) := by
  -- ADMITTED
  intro H
  have HH := de_morgan_not_or P (¬P) H
  obtain ⟨HNP, HNNP⟩ := HH
  exact HNNP HNP
  -- /ADMITTED
-- []

-- EX3A (not_exists_dist)
-- It is a theorem of classical logic that the following two
--    assertions are equivalent:
--
--     ¬(∃ x, ¬P x)
--     ∀ x, P x
--
--    The `dist_not_exists` theorem above proves one side of this
--    equivalence. Interestingly, the other direction cannot be proved
--    in constructive logic. Your job is to show that it is implied by
--    the excluded middle.

theorem not_exists_dist :
  excluded_middle →
  ∀ (X : Type) (P : X → Prop),
    ¬(∃ x, ¬P x) → (∀ x, P x) := by
  -- ADMITTED
  intro Hem X P H x
  obtain HPx | HNPx := Hem (P x)
  · exact HPx
  · exfalso; exact H ⟨x, HNPx⟩
  -- /ADMITTED
-- []

-- EX5? (classical_axioms)
-- For those who like a challenge, here is an exercise adapted from the
--    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
--    following five statements, together with `excluded_middle`, can be
--    considered as characterizing classical logic.  We can't prove any
--    of them in Lean (without `Classical`), but we can consistently add
--    any _one_ of them as an axiom if we wish to work in classical logic.
--
--    To see this, prove that all six propositions (these five plus
--    `excluded_middle`) are equivalent.
--
--    Hint: Rather than considering all pairs of statements pairwise,
--    prove a single circular chain of implications that connects them
--    all.

def peirce := ∀ P Q : Prop,
  ((P → Q) → P) → P

def double_negation_elimination := ∀ P : Prop,
  ¬¬P → P

def de_morgan_not_and_not := ∀ P Q : Prop,
  ¬(¬P ∧ ¬Q) → P ∨ Q

def implies_to_or := ∀ P Q : Prop,
  (P → Q) → (¬P ∨ Q)

def consequentia_mirabilis := ∀ P : Prop,
  (¬P → P) → P

-- SOLUTION
-- We prove a circular chain:
--   excluded_middle → double_negation_elimination → de_morgan_not_and_not
--   → excluded_middle
-- and
--   excluded_middle → implies_to_or → excluded_middle
-- and
--   excluded_middle → peirce → excluded_middle
-- and
--   double_negation_elimination ↔ consequentia_mirabilis

theorem ito__em :
  implies_to_or → excluded_middle := by
  unfold implies_to_or; unfold excluded_middle
  intro Hito P
  have H := Hito P P (fun HP => HP)
  obtain HNP | HP := H
  · right; exact HNP
  · left; exact HP

theorem em__ito :
  excluded_middle → implies_to_or := by
  unfold excluded_middle; unfold implies_to_or
  intro Hem P Q H
  obtain HP | HNP := Hem P
  · right; exact H HP
  · left; exact HNP

theorem em__demorgan :
  excluded_middle → de_morgan_not_and_not := by
  unfold excluded_middle; unfold de_morgan_not_and_not
  intro Hem P Q H
  obtain HP | HNP := Hem P
  · left; exact HP
  · obtain HQ | HNQ := Hem Q
    · right; exact HQ
    · exfalso; exact H ⟨HNP, HNQ⟩

theorem demorgan__em :
  de_morgan_not_and_not → excluded_middle := by
  unfold de_morgan_not_and_not; unfold excluded_middle
  intro Hdm P
  apply Hdm
  intro ⟨HNP, HNNP⟩
  exact HNNP HNP

theorem em__dne :
  excluded_middle → double_negation_elimination := by
  intro Hem P HnnP
  obtain HP | HNP := Hem P
  · exact HP
  · exact absurd HNP HnnP

theorem dne__demorgan :
  double_negation_elimination → de_morgan_not_and_not := by
  intro Hc P Q H
  apply Hc
  intro H2
  exact H ⟨fun HP => H2 (Or.inl HP), fun HQ => H2 (Or.inr HQ)⟩

theorem dne__em :
  double_negation_elimination → excluded_middle := by
  intro Hc P
  exact Hc (P ∨ ¬P) (excluded_middle_irrefutable P)

theorem em__peirce :
  excluded_middle → peirce := by
  intro Hem P Q H
  obtain HP | HNP := Hem P
  · exact HP
  · exact H (fun HP => absurd HP HNP)

theorem peirce__em :
  peirce → excluded_middle := by
  intro Hp P
  apply Hp (P ∨ ¬P) False
  intro H
  right
  intro HP
  exact H (Or.inl HP)

theorem consequentia_mirabilis__dne :
  consequentia_mirabilis → double_negation_elimination := by
  intro Hcm P HnnP
  exact Hcm P (fun HnP => absurd HnP HnnP)

theorem dne__consequentia_mirabilis :
  double_negation_elimination → consequentia_mirabilis := by
  intro Hdne P H
  apply Hdne
  intro HnP
  exact HnP (H HnP)
-- /SOLUTION
-- []
-- /FULL
