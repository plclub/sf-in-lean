/- # Logic in Lean -/

/- INSTRUCTORS: Warning: This is a LOT of material to get through in
   two 80-minute lectures, and the last couple of sections are quite
   meaty.  Pacing is key! -/

/- SOONER: Unlike earlier chapters, there are probably too many
 WORKINCLASSes in this chapter.  BCP 20: But conversely some more
 quizzes would be great! -/

-- HIDEFROMHTML
import Basics
import Induction
import Tactics
import CustomTactics
open Nat hiding add_succ mul_succ beq
-- /HIDEFROMHTML

/- FULL: We have now seen many examples of factual claims (i.e.,
    _propositions_) and ways of presenting evidence of their truth
    (_proofs_).  In particular, we have worked extensively with
    equality propositions (`e1 = e2`), implications (`P → Q`), and
    quantified propositions (`∀ x, P`).  In this chapter, we will
    see how Lean can be used to carry out other familiar forms of
    logical reasoning.

    Before diving into details, we should talk a bit about the status
    of mathematical statements in Lean. Lean is a _typed_ language,
    which means that every sensible expression has an associated type.
    Logical claims are no exception: any statement we might try to
    prove in Lean has a type, namely `Prop`, the type of
    _propositions_.  We can see this with the `#check` command: -/

/- TERSE: So far, we have seen:
    * _propositions_: mathematical statements, so far only of 3 kinds:
      * equality propositions (`e1 = e2`)
      * implications (`P -> Q`)
      * quantified propositions (`∀ x, P`)
    * _proofs_: ways of presenting evidence for the truth of a
       proposition

    In this chapter we will introduce several more flavors of both
    propositions and proofs.

    Like everything in Lean, well-formed propositions have a _type_: -/

-------------------------------------------------------------------------------
/- ## The `Prop` Type -/

#check (∀ n m : Nat, n + m = m + n : Prop)

/- Note that _all_ syntactically well-formed propositions have type
    `Prop` in Lean, regardless of whether they are true or not.

    Simply _being_ a proposition is one thing; being _provable_ is
    a different thing! -/

#check (2 = 2 : Prop)
#check (3 = 2 : Prop)
#check (∀ n : Nat, n = 2 : Prop)

/- FULL: Indeed, propositions don't just have types -- they are
    _first-class_ entities that can be manipulated in all the same ways as
    any of the other things in Rocq's world. -/

/- So far, we've seen one primary place where propositions can appear:
    in `theorem` declarations. -/

theorem plus_2_2_is_4 : 2 + 2 = 4 := by rfl

/- FULL: But propositions can be used in other ways.  For example, we
    can give a name to a proposition using a `def`, just as we
    give names to other kinds of expressions. -/

/- TERSE: Propositions are first-class entities.
    For example, we can name them: -/

def plus_claim : Prop := 2 + 2 = 4

#check (plus_claim : Prop)

/- FULL: We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a `theorem` declaration. -/

theorem plus_claim_is_true : plus_claim := by rfl

/- We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. -/

/- FULL: For instance, the following function takes a number and
    returns a proposition asserting that this number is equal to three: -/

def is_three (n : Nat) : Prop := n = 3

#check (is_three : Nat → Prop)

/- In Lean, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an _injective function_. -/

def injective {α β} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

theorem succ_inj' : injective succ := by
  intro x y H; injection H

/- The familiar equality operator `=` is a (binary) function that returns
    a `Prop`. The expression `n = m` is notation for `Eq n m`.
    Because `eq` can be used with elements of any type, it is also
    polymorphic: -/

-- JC: Actually it quantifies over `Sort`, where `Prop = Sort 0`
-- and `Type u = Sort (u + 1)`. Not something that needs teaching
-- right at this moment, but they'll see `Sort` when hovering.
#check (Eq : ∀ {α : Type}, α → α → Prop)

#check pred

/- As a convenience, Lean will cast booleans by equating them to `true`,
    which is why checking them against `Prop` succeeds.
    It also casts boolean equalities to propositions by equating to `true`,
    and boolean inequalities by equating to `false`.
    For clarity, we will avoid relying on these implicit casts. -/

/-- info: false = true : Prop -/
#guard_msgs in
#check (false : Prop)

/-- info: true = true : Prop -/
#guard_msgs in
#check (true : Prop)

/- QUIZ: What is the type of the following expression?
    ```
    pred (succ zero) = zero
    ```

   1. `Prop`
   2. `Nat → Prop`
   3. `∀ n : Nat, Prop`
   4. `Nat → Nat`
   5. Not typeable -/

#check (pred (succ zero) = zero : Prop)

/- QUIZ: What is the type of the following expression?
    ```
    ∀ n : Nat, pred (succ n) = n
    ```

   1. `Prop`
   2. `Nat → Prop`
   3. `∀ n : Nat, Prop`
   4. `Nat → Nat`
   5. Not typeable -/

#check (∀ n : Nat, pred (succ n) = n : Prop)

/- QUIZ: What is the type of the following expression?
    ```
    ∀ n : Nat, succ (pred n)
    ```

   1. `Prop`
   2. `Nat → Prop`
   3. `∀ n : Nat, Prop`
   4. `Nat → Nat`
   5. Not typeable -/

/-- info: type expected, got
  (succ (pred n) : Nat) -/
#guard_msgs in
#check_failure ∀ n : Nat, succ (pred n)

/- QUIZ: What is the type of the following expression?
    ```
    fun n : Nat => succ (pred n)
    ```

   1. `Prop`
   2. `Nat → Prop`
   3. `∀ n : Nat, Prop`
   4. `Nat → Nat`
   5. Not typeable -/

#check (fun n : Nat => succ (pred n) : Nat → Nat)

/- QUIZ: What is the type of the following expression?
    ```
    fun n : Nat => succ (pred n) = n
    ```

   1. `Prop`
   2. `Nat → Prop`
   3. `∀ n : Nat, Prop`
   4. `Nat → Nat`
   5. Not typeable -/

#check (fun n : Nat => succ (pred n) = n : Nat → Prop)

/- QUIZ: Which of the following is _not_ a proposition?

    1. `3 + 2 = 4`
    2. `3 + 2 = 5`
    3. `3 + 2 == 5`
    4. `(3 + 2 == 4) = false`
    5. `∀ n, (3 + 2 == n) = true → n = 5`
    6. All of these are propositions -/

#check (3 + 2 == 5 : Bool)

-------------------------------------------------------------------------------
/- ## Logical Connectives -/

/- ### Conjunction -/

/- The _conjunction_, or _logical and_, of propositions `A` and `B` is written
    `A ∧ B`; it represents the claim that both `A` and `B` are true. -/

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  /- A proof of a conjunction is a pair of proofs of the two components.
      To prove a conjunction, we build a pair using `constructor`. -/
  constructor
  case left  => /- 3 + 4 = 7 -/ rfl
  case right => /- 2 * 2 = 4 -/ rfl

/- The constructor for conjunction is `And.intro`,
    which concludes that `A ∧ B` given that `A` and `B` hold individually. -/

#check (And.intro : ∀ {α β : Prop}, α → β → α ∧ β)

/- We can also apply the constructor for the conjunction explicitly. -/
example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  case left  => /- 3 + 4 = 7 -/ rfl
  case right => /- 2 * 2 = 4 -/ rfl

/- Rather than applying the constructor, we can explicitly provide
    the arguments to the constructor as an `exact` proof. -/
example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact And.intro rfl rfl

/- Lean also has notation for _anonymous constructors_ ⟨arg₁, ..., argₙ⟩,
    which deduces the correct constructor that is needed,
    and applies a list of arguments to that constructor. -/
example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact ⟨rfl, rfl⟩

-- FULL
-- EX2 (add_is_zero)
theorem add_is_zero : ∀ n m : Nat,
    n + m = 0 → n = 0 ∧ m = 0 := by
  -- FULL: ADMITTED
  -- TERSE: WORKINCLASS
  intro n m; cases m
  case zero =>
    rw [add_zero]
    intro e; constructor
    case left => exact e
    case right => rfl
  case succ =>
    rw [add_succ]
    intro e; contradiction
  -- FULL: /ADMITTED
  -- TERSE: /WORKINCLASS
-- []
-- /FULL

/- So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to help prove
    something else -- we can use `let` to obtain the components. -/

example : ∀ n m : Nat,
    n = 0 ∧ m = 0 → n + m = 0 := by
  -- WORKINCLASS
  intro n m H
  let ⟨Hn, Hm⟩ := H
  rw [Hn, Hm]
  -- /WORKINCLASS

/- As usual, we can also match on `H` right at the point where we
    introduce it, instead of introducing and then destructing it: -/
example : ∀ n m : Nat,
    n = 0 ∧ m = 0 → n + m = 0 := by
  intro n m ⟨Hn, Hm⟩
  rw [Hn, Hm]

-- FULL
/- You may wonder why we bothered packing the two hypotheses `n = 0` and
    `m = 0` into a single conjunction, since we could also have stated the
    theorem with two separate premises: -/

example : ∀ n m : Nat,
    n = 0 → m = 0 → n + m = 0 := by
  intro n m Hn Hm
  rw [Hn, Hm]

/- TERSE: For the present example, both ways work.
    But in other situations, we may wind up with a conjunctive hypothesis
    in the middle of a proof... -/

/- FULL: For this specific theorem, both formulations are fine.  But
    it's important to understand how to work with conjunctive
    hypotheses because conjunctions often arise from intermediate
    steps in proofs, especially in larger developments.  Here's a
    simple example: -/

example : ∀ n m : Nat,
    n + m = 0 → n * m = 0 := by
  -- WORKINCLASS
  intro n m H
  apply add_is_zero at H
  let ⟨Hn, Hm⟩ := H
  rw [Hm]; rfl
  -- /WORKINCLASS
-- /FULL

-- FULL
/- Another common situation is that we know `A /\ B` but in some
    context we need just `A` or just `B`.  In such cases we can use
    an underscore pattern `_` to indicate that the unneeded conjunct
    should just be thrown away. -/

theorem proj1 : ∀ P Q : Prop,
    P ∧ Q → P := by
-- HIDEFROMADVANCED
  intro P Q HPQ
  let ⟨HP, _⟩ := HPQ
  exact HP
-- /HIDEFROMADVANCED

-- HIDEFROMADVANCED
-- EX1? (proj2)
-- /HIDEFROMADVANCED
theorem proj2 : ∀ P Q : Prop,
    P ∧ Q → Q := by
-- HIDEFROMADVANCED
  -- ADMITTED
  intro P Q HPQ
  let ⟨_, HQ⟩ := HPQ
  exact HQ
  -- /ADMITTED
-- []
-- /HIDEFROMADVANCED

/- Finally, we sometimes need to rearrange the order of conjunctions
    and/or the grouping of multi-way conjunctions. We can see this
    at work in the proofs of the following commutativity and
    associativity theorems. -/

theorem and_commute : ∀ P Q : Prop,
    P ∧ Q → Q ∧ P := by
  intro P Q ⟨HP, HQ⟩
  constructor
  case left  => exact HQ
  case right => exact HP

/- In the following proof of associativity, notice how the _nested_
    `intro` pattern breaks the hypothesis `H : P /\ (Q /\ R)` down into
    `HP : P`, `HQ : Q`, and `HR : R`.  Finish the proof. -/

-- EX1 (and_associate)
theorem and_associate : ∀ P Q R : Prop,
    P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  intro P Q R ⟨HP, ⟨HQ, HR⟩⟩
  -- ADMITTED
  constructor
  case left =>
    constructor
    case left  => exact HP
    case right => exact HQ
  case right => exact HR
  -- /ADMITTED
-- []
-- /FULL

/- The infix notation `∧` is actually just syntactic sugar for
    `And A B`. That is, `And` is a Lean operator that takes two
    propositions as arguments and yields a proposition. -/

#check (And : Prop → Prop → Prop)

/- ### Disjunction -/

/- Another important connective is the _disjunction_, or _logical or_,
    of two propositions: `A ∨ B` is true when either `A` or `B` is.
    This infix notation stands for `Or A B`, where
    `Or : Prop -> Prop -> Prop`. -/

/- To use a disjunctive hypothesis in a proof, we proceed by case
    analysis -- which, as with other data types like `Nat`, is done
    using `cases`. The two cases are `inl` (for "left injection",
    or "in the left case") and `inr` (for "right injection",
    or "in the right case"). -/

theorem factor_is_zero : ∀ n m : Nat,
    n = 0 ∨ m = 0 → n * m = 0 := by
  intro n m H
  cases H
  /- `n = 0` -/
  case inl Hn => rw [Hn, zero_mul]
  /- `m = 0` -/
  case inr Hm => rw [Hm, mul_zero]

/- FULL: We can see in this example that, when we perform case
    analysis on a disjunction `A ∨ B`, we must separately discharge
    two proof obligations, each showing that the conclusion holds
    under a different assumption -- `A` in the first subgoal and `B`
    in the second. -/

/- Rather than performing case analysis via `cases`, we can also use `obtains`
    to match on the two possible injections, much like with `let`. -/

theorem and_is_false : ∀ b1 b2 : Bool,
    (b1 = false) ∨ (b2 = false) → (b1 && b2) = false := by
  intro b1 b2 H
  obtain Hb1 | Hb2 := H
  case inl => rw [Hb1, Bool.false_and]
  case inr => rw [Hb2, Bool.and_false]

/- Conversely, to show that a disjunction holds, it suffices to show
    that one of its sides holds. This can be done via the tactics
    `left` and `right`.  As their names imply, the first one requires
    proving the left side of the disjunction, while the second
    requires proving the right side.  Here is a trivial use... -/

theorem or_intro_l : ∀ A B : Prop, A → A ∨ B := by
  intro A B HA
  left; exact HA

/- ... and here is a slightly more interesting example requiring both
    `left` and `right`: -/

theorem zero_or_succ : ∀ n : Nat,
    n = 0 ∨ n = pred (succ n) := by
  -- WORKINCLASS
  intro n
  cases n
  case zero => left; rfl
  case succ n => right; dsimp [pred]
  -- /WORKINCLASS

-- TERSE: HIDEFROMHTML
-- EX2 (mul_is_zero)
theorem mul_is_zero : forall n m : Nat,
    n * m = 0 → n = 0 ∨ m = 0 := by
  -- ADMITTED
  intro n m H
  cases m
  case zero => right; rfl
  case succ =>
    cases n
    case zero => left; rfl
    case succ =>
      rw [mul_succ, add_succ] at H
      contradiction
  -- /ADMITTED
-- []

-- EX1 (or_commute)
theorem or_commute : ∀ P Q : Prop,
    P ∨ Q → Q ∨ P := by
  -- ADMITTED
  intro P Q H
  obtain HP | HQ := H
  case inl => right; exact HP
  case inr => left; exact HQ
  -- /ADMITTED
-- []
-- TERSE: /HIDEFROMHTML

/- ### Falsehood and Negation -/

/- Up to this point, we have mostly been concerned with proving
    "positive" statements -- addition is commutative, appending lists
    is associative, etc.  We are sometimes also interested in negative
    results, demonstrating that some proposition is _not_ true. Such
    statements are expressed with the logical negation operator `¬`,
    which a prefix notation for `Not`.

    To see how negation works, recall the _principle of explosion_
    from the `Tactics` chapter, which asserts that, if we assume a
    contradiction, then any other proposition can be derived.

    Following this intuition, we could define `¬ P` ("not `P`") as
    `∀ Q, P → Q`.
    Lean makes an equivalent but slightly different choice,
    defining `~ P` as `P → False`, where `False` is a specific
    unprovable proposition defined in the standard library. -/

#check (Not : Prop → Prop)
#print Not

example : ∀ P, Not P = (P → False) := by intro; rfl
example : ∀ P, (¬ P) = (P → False) := by intro; rfl

/- Since `False` is a contradictory proposition, the principle of
    explosion also applies to it. If we can get `False` into the context,
    we can use `cases` on it to complete any goal: -/

theorem ex_falso_quodlibet : ∀ P : Prop, False → P := by
  intro P contra
  cases contra

/- FULL: The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. -/

-- FULL
-- EX2? (not_implies_other_not)
theorem not_implies_other_not : ∀ P : Prop,
    ¬ P → (∀ Q : Prop, P → Q) := by
  -- ADMITTED
  intro P H Q HP
  unfold Not at H
  apply ex_falso_quodlibet
  apply H
  exact HP
  -- /ADMITTED
-- []
-- /FULL

/- Inequality is a very common form of negated statement, so there is a
    special notation for it: `≠`, which is infix notation for `Ne`. -/

#print Ne

theorem zero_not_one : 0 ≠ 1 := by
  /- FULL: The proposition `0 ≠ 1` is exactly the same as `¬ (0 = 1)`
      -- that is, `Not (0 = 1)` -- which unfolds to `(0 = 1) → False`.
      (We use `unfold Ne Not` explicitly here to illustrate that point,
      but generally it can be omitted.) -/
  unfold Ne Not
  /- FULL: To prove an inequality, we may assume the opposite equality... -/
  intro contra
  /- FULL: ...and deduce a contradiction from it. Here, the equality
      `0 = 1` corresponds to `zero = succ zero`, which contradicts
      disjointness of constructors `zero` and `succ`, so `contradiction`
      takes care of it. -/
  contradiction
  -- JC: `cases contra` and `injection contra` both also work,
  -- but is probably harder to explain.

/- It takes a little practice to get used to working with negation in Rocq.
    Even though _you_ may see perfectly well why a claim involving
    negation holds, it can be a little tricky at first to see how to make
    Rocq understand it!

    Here are proofs of a few familiar facts to help get you warmed up. -/

theorem not_False : ¬ False := by
  unfold Not; intro H; exact H

theorem contradiction_implies_anything : ∀ P Q : Prop,
    (P ∧ ¬ P) → Q := by
  -- WORKINCLASS
  intro P Q ⟨HP, HNP⟩
  unfold Not at HNP
  cases (HNP HP)
  -- /WORKINCLASS

theorem double_neg : ∀ P : Prop, P → ¬ ¬ P := by
  -- WORKINCLASS
  intro P H
  unfold Not
  intro G
  apply G
  exact H
  -- /WORKINCLASS

-- FULL
-- EX2AM? (double_neg_informal)
/- Write an _informal_ proof of `double_neg`:
    _Theorem_: `P` implies `¬ ¬ P`, for any proposition `P`. -/

-- SOLUTION
/- _Proof_: Suppose some proposition `P` holds. We must show `¬ ¬ P` --
    i.e., `¬ P → False`, so suppose `¬ P` as well and try to derive `False`.
    Then we have both `P` and `¬ P` (i.e., `P → False`) from which
    we can indeed derive `False`. So `¬ ¬ P` holds. -/
-- /SOLUTION

-- GRADE_MANUAL 2: double_neg_informal
-- []

-- EX1! (contrapositive)
theorem contrapositive : ∀ P Q : Prop,
    (P → Q) → (¬ Q → ¬ P) := by
  -- ADMITTED
  intro P Q H HNotQ HP
  apply HNotQ
  apply H
  exact HP
  -- /ADMITTED
-- []

-- EX1AM (not_PNP_informal)
/- Write an informal proof of the proposition
    `∀ P : Prop, ¬ (P ∧ ¬ P)`. -/

-- SOLUTION
/- _Proof_: Suppose, for some `P`, that `P ∧ ¬ P` holds.
    Recall that `¬ P` is defined as `P → False`.
    Given `P` and `P → False`, we can prove `False`,
    so `(P ∧ ¬ P) → False`, i.e. `¬ (P ∧ ¬ P)`. -/
-- / SOLUTION

-- GRADE_MANUAL 1: not_PNP_informal
-- []

-- EX2 (de_morgan_not_or)
/-  _De Morgan's Laws_, named for Augustus De Morgan, describe how
    negation interacts with conjunction and disjunction.  The
    following law says that "the negation of a disjunction is the
    conjunction of the negations." There is a dual law
    `de_morgan_not_and_not` to which we will return at the end of this
    chapter. -/
theorem de_morgan_not_or : ∀ P Q : Prop,
    ¬ (P ∨ Q) → ¬ P ∧ ¬ Q := by
  -- ADMITTED
  unfold Not
  intro P Q H
  constructor
  case left  => intro HP; apply H; left; exact HP
  case right => intro HQ; apply H; right; exact HQ
  -- /ADMITTED
-- []

-- EX1? (not_succ_inverse_pred)
/- Since we are working with natural numbers, we can disprove that
    `succ` and `pred` are inverses of each other: -/
theorem not_succ_pred_n : ¬ (∀ n : Nat, succ (pred n) = n) := by
  -- ADMITTED
  intro H
  replace H := H 0
  dsimp [pred] at H
  cases H
  -- /ADMITTED
-- []
-- /FULL

/- TERSE: Since inequality involves a negation, getting comfortable
    with it also often requires a little practice.

    A useful trick: if you are trying to prove a nonsensical goal,
    apply `ex_falso_quodlibet` to change the goal to `False`. This
    makes it easier to use assumptions of the form `¬ P`, and in
    particular of the form `x ≠ y`. -/

/- FULL: Since inequality involves a negation, it also requires a little
    practice to be able to work with it fluently. Here is one useful trick.

    If you are trying to prove a goal that is nonsensical (e.g., the
    goal state is `false = true`), apply `ex_falso_quodlibet` to
    change the goal to [False].

    This makes it easier to use assumptions of the form `¬ P` that may
    be available in the context -- in particular, assumptions of the
    form `x ≠ y`. -/

theorem not_true_is_false : ∀ b : Bool,
    b ≠ true → b = false := by
  -- FOLD
  intro b H
  cases b
  case false => rfl
  case true =>
    unfold Ne Not at H
    apply ex_falso_quodlibet
    apply H; rfl
  -- /FOLD

-- FULL
/- Since reasoning with `ex_falso_quodlibet` is quite common,
    Lean provides a tactic, `exfalso`, for applying it. -/
theorem not_true_is_false' : ∀ b : Bool,
    b ≠ true → b = false := by
  intro b H
  cases b
  case false => rfl
  case true =>
    unfold Ne Not at H
    exfalso -- ⟵ here
    apply H; rfl
-- /FULL

/- HIDE: CH: I don't think this was the original intention, but some
    of these quizzes got unnecessarily tricky and pedantic. For
    instance, the first quiz below makes a big distinction between
    using the destruct tactic and destructing using an intro pattern,
    even if conceptually there is no difference. Could it be that these
    quizzes were devised when intro patterns were not taught in the
    course and an update would be helpful now? Since I don't see the
    gain in tricking a majority of students in giving the "wrong"
    answer, even if it's a perfectly sensible one. -/

/- QUIZ: To prove the following proposition, which tactics will we need
    besides `intro`, `apply`, and `exact`?
    ```
    ∀ X : Prop, ∀ a b : X, a = b ∧ a ≠ b → False
    ```

    1. `cases`, `unfold`, `left`, and `right`
    2. `cases` and `unfold`
    3. only `cases`
    4. `left` and/or `right`
    5. only `unfold`
    6. none of the above -/

-- FOLD
example : ∀ X : Prop, ∀ a b : X, a = b ∧ a ≠ b → False := by
  intro X a b ⟨Hab, Hnab⟩; apply Hnab; exact Hab
-- /FOLD

/- QUIZ: To prove the following proposition, which tactics will we need
    besides `intro`, `apply`, and `exact`?
    ```
    ∀ P Q : Prop, P ∨ Q → ¬ ¬ (P ∨ Q)
    ```

    1. `cases`, `unfold`, `left`, and `right`
    2. `cases` and `unfold`
    3. only `cases`
    4. `left` and/or `right`
    5. only `unfold`
    6. none of the above -/

-- FOLD
example : ∀ P Q : Prop, P ∨ Q → ¬ ¬ (P ∨ Q) := by
  intro P Q HPQ HnPQ
  apply HnPQ at HPQ
  exact HPQ
-- /FOLD

/- QUIZ: To prove the following proposition, which tactics will we need
    besides `intro`, `apply`, and `exact`?
    ```
    ∀ P Q : Prop, P → (P ∨ ¬ ¬ Q)
    ```

    1. `cases`, `unfold`, `left`, and `right`
    2. `cases` and `unfold`
    3. only `cases`
    4. `left` and/or `right`
    5. only `unfold`
    6. none of the above -/

-- FOLD
example : ∀ P Q : Prop, P → (P ∨ ¬ ¬ Q) := by
  intro P Q HP
  left; exact HP
-- /FOLD

/- QUIZ: To prove the following proposition, which tactics will we need
    besides `intro`, `apply`, and `exact`?
    ```
    ∀ P Q : Prop, P ∨ Q → (¬ ¬ P) ∨ (¬ ¬ Q)
    ```

    1. `cases`, `unfold`, `left`, and `right`
    2. `cases` and `unfold`
    3. only `cases`
    4. `left` and/or `right`
    5. only `unfold`
    6. none of the above -/

-- FOLD
example : ∀ P Q : Prop, P ∨ Q → (¬ ¬ P) ∨ (¬ ¬ Q) := by
  intro P Q H
  cases H
  case inl HP => left; intro HnP; apply HnP; exact HP
  case inr HQ => right; intro HnQ; apply HnQ; exact HQ
-- /FOLD

/- QUIZ: To prove the following proposition, which tactics will we need
    besides `intro`, `apply`, and `exact`?
    ```
    ∀ A : Prop, 1 = 0 → (A ∨ ¬ A)
    ```

    1. `contradiction`, `unfold`, `left`, and `right`
    2. `contradiction` and `unfold`
    3. only `contradiction`
    4. `left` and/or `right`
    5. only `unfold`
    6. none of the above -/

-- FOLD
example : ∀ A : Prop, 1 = 0 → (A ∨ ¬ A) := by
  intro A H; contradiction
-- /FOLD

/- ## Truth -/

/- Besides `False`, Lean's standard library also defines `True`,
    a proposition that is trivially true. To prove it, we use
    the constructor `True.intro` explicitly, or the anonymous
    constructor `⟨⟩`, or the `constructor` tactic. -/

example : True := by exact True.intro
example : True := by exact ⟨⟩
example : True := by constructor

/- Unlike `False`, which is used extensively, `True` is used
    relatively rarely: it is trivial (and therefore uninteresting)
    to prove as a goal, and it provides no useful information
    when it appears as a hypothesis. -/

-- FULL
/- However, `True` can be quite useful when defining complex `Prop`s using
    conditionals or as a parameter to higher-order `Prop`s. We'll come back
    to this later.

    For now, let's take a look at how we can use `True` and `False` to
    achieve an effect similar to that of the `contradiction` tactic, without
    literally using `contradiction`. -/

/- Pattern-matching lets us do different things for different
    constructors.  If the result of applying two different
    constructors were hypothetically equal, then we could use [match]
    to convert an unprovable statement (like `False`) to one that is
    provable (like `True`). -/

def discr_fun (n : Nat) : Prop :=
  match n with
  | zero => True
  | succ _ => False

theorem discr_example : ∀ n : Nat, ¬ (zero = succ n) := by
  intro n contra
  have H : discr_fun zero := by exact True.intro
  rw [contra] at H
  dsimp [discr_fun] at H

/- To generalize this to other constructors, we simply have to provide
    an appropriate variant of `discr_fun`. To generalize it to other
    conclusions, we can use `exfalso` to replace them with `False`.
    The `contradiction` tactic takes care of all of this for us. -/

-- EX2AM? (nil_is_not_cons)
/- Use the same technique as above to show that `[] ≠ x :: xs`.
    Do not use the `contradiction` tactic. -/

-- QUIETSOLUTION
def is_nil {X : Type} (xs : List X) : Prop :=
  match xs with
  | [] => True
  | _ :: _ => False
-- /QUIETSOLUTION

theorem nil_is_not_cons : ∀ {α : Type} (x : α) (xs : List α),
    ¬ ([] = x :: xs) := by
  -- ADMITTED
  intro α x xs Heq
  have H : @is_nil α [] := by exact True.intro
  rw [Heq] at H
  dsimp [is_nil] at H
  -- /ADMITTED
-- []
-- /FULL

/- ### Logical Equivalence -/

/- The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is a structure containing
    the two implication directions. `P ↔ Q` is notation for `Iff P Q`. -/

/-- info:
structure Iff (a b : Prop) : Prop
number of parameters: 2
fields:
  Iff.mp : a → b
  Iff.mpr : b → a
constructor:
  Iff.intro {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b -/
#guard_msgs in
#print Iff

#check (fun α β : Prop => α ↔ β : Prop → Prop → Prop)

theorem iff_sym : ∀ P Q : Prop,
    (P ↔ Q) → (Q ↔ P) := by
  -- WORKINCLASS
  intro P Q ⟨HPQ, HQP⟩
  constructor
  case mp => exact HQP
  case mpr => exact HPQ
  -- /WORKINCLASS

theorem not_true_iff_false : ∀ b : Bool,
    b ≠ true ↔ b = false := by
  intro b
  constructor
  case mp => apply not_true_is_false
  case mpr => intro H; rw [H]; intro H'; contradiction

-- TERSE: HIDEFROMHTML
-- EX1? (iff_properties)
/- Using the above proof that `↔` is symmetric (`iff_sym`) as a guide,
    prove that it is also reflexive and transitive. -/

theorem iff_refl : ∀ P : Prop, P ↔ P := by
  -- ADMITTED
  intro P; constructor
  case mp => intro H; exact H
  case mpr => intro H; exact H
  -- /ADMITTED

theorem iff_trans : ∀ P Q R : Prop,
    (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  -- ADMITTED
  intro P Q R ⟨HPQ, HQP⟩ ⟨HQR, HRQ⟩; constructor
  case mp => intro HP; apply HQR; apply HPQ; exact HP
  case mpr => intro HR; apply HQP; apply HRQ; exact HR
  -- /ADMITTED

-- []
-- TERSE: /HIDEFROMHTML

theorem or_associate : ∀ P Q R : Prop,
    P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := by
  intro P Q R; constructor
  case mp =>
    intro H
    obtain HP | (HQ | HR) := H
    case inl     => left; left; exact HP
    case inr.inl => left; right; exact HQ
    case inr.inr => right; exact HR
  case mpr =>
    intro H
    obtain (HP | HQ) | HR := H
    case inl.inl => left; exact HP
    case inl.inr => right; left; exact HQ
    case inr     => right; right; exact HR

-- FULL
-- EX3 (or_distributes_over_and)
theorem or_distributes_over_and : ∀ P Q R : Prop,
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  -- ADMITTED
  intro P Q R; constructor
  case mp =>
    intro HPQR
    obtain HP | ⟨HQ, HR⟩ := HPQR
    case inl =>
      constructor
      case left => left; exact HP
      case right => left; exact HP
    case inr =>
      constructor
      case left => right; exact HQ
      case right => right; exact HR
  case mpr =>
    intro HPQPR
    obtain ⟨HP | HQ, HP | HR⟩ := HPQPR
    case inl.inl => left; exact HP
    case inl.inr => left; exact HP
    case inr.inl => left; exact HP
    case inr.inr => right; exact ⟨HQ, HR⟩
  -- /ADMITTED
-- []
-- /FULL

theorem mul_eq_0 : forall n m : Nat,
    n * m = 0 ↔ n = 0 ∨ m = 0 := by
  intro n m
  constructor
  case mp => apply mul_is_zero
  case mpr => apply factor_is_zero

/- ### Existential Quantification -/

/- FULL: Another fundamental logical connective is _existential quantification_.
    To say that there is some `x` of type `T` such that some property `P`
    holds of `x`, we write `∃ x : T, P`. This is notation for the `Exists`
    connective, and is defined as `Exists (fun (x : T) => P)`.
    As with `∀ x : T`, the type annotation `: T` can be omitted if Lean
    is able to infer from the context what the type of `x` should be.

    To prove a statement of the form `∃ x, P`, we must show that `P`
    holds for some specific choice for `x`, known as the _witness_ of the
    existential.  This is done in two steps: First, we explicitly tell Lean
    which witness `t` we have in mind by invoking the tactic `exists t`.
    Then we prove that `P` holds after all occurrences of `x`
    are replaced by `t`. The `exists` tactic tries to close the proof
    with simple tactics such as `rfl` or `contradiction`, so we may not
    have to prove `P` explicitly. -/

#check (Exists : ∀ {T : Type}, (T → Prop) → Prop)

def Even x := ∃ n : Nat, x = double n

#check (Even : Nat → Prop)

example : Even 4 := by
  unfold Even; exists 2
  -- `4 = double 2` holds by `rfl`,
  -- but is proven automatically by `exists`

/- Conversely, if we have an existential hypothesis `∃ x, P` in the context,
    can destruct it to obtain a witness `x` and a hypothesi stating that `P`
    holds of `x`. -/

example : ∀ n, (∃ m, n = m + 4) → (∃ o, n = o + 2) := by
  -- WORKINCLASS
  intro n ⟨m, Hm⟩
  exists (m + 2)
  -- /WORKINCLASS

-- FULL
-- EX1! (dist_not_exists)
/- Prove that "`P` holds for all `x` implies "there is no `x` for which
    `P` does not hold." (Hint: `cases` works on existential assumptions!) -/

theorem dist_not_exists : ∀ (X : Type) (P : X → Prop),
    (∀ x, P x) → ¬ (∃ x, ¬ P x) := by
  -- ADMITTED
  intro X P H ⟨x, Hx⟩
  apply Hx; apply H
  -- /ADMITTED
-- GRADE_THEOREM 1: dist_not_exists
-- []

-- EX2 (dist_exists_or)
/- FULL: Prove that existential quantification distributes over disjunction. -/

theorem dist_exists_or : ∀ (X : Type) (P Q : X → Prop),
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  -- ADMITTED
  intro X P Q; constructor
  case mp =>
    intro HPQ
    obtain ⟨x, HP | HQ⟩ := HPQ
    case inl => left; exists x
    case inr => right; exists x
  case mpr =>
    intro HPQ
    obtain ⟨x, Hx⟩ | ⟨x, Hx⟩ := HPQ
    case inl => exists x; left; exact Hx
    case inr => exists x; right; exact Hx
  -- /ADMITTED
-- GRADE_THEOREM 2: dist_exists_or
-- []

-- EX3? (leb_plus_exists)
theorem leb_plus_exists : ∀ n m : Nat,
    (n ≤? m = true) → ∃ x, m = x + n := by
  -- ADMITTED
  intro n
  induction n
  case zero => intro m H; exists m
  case succ n' IHn' =>
    intro m
    cases m
    case zero => intro H; contradiction
    case succ m' =>
      intro H
      dsimp [leb] at H
      apply IHn' at H
      let ⟨x, Hx⟩ := H
      exists x
      rw [Hx]; rfl
  -- /ADMITTED

-- QUIETSOLUTION
theorem leb_plus : ∀ n m : Nat,
    (n ≤? (m + n)) = true := by
  intro n
  induction n
  case zero => intro m; rfl
  case succ n' IHn' =>
    intro m
    dsimp [leb]
    apply IHn'
-- /QUIETSOLUTION

theorem add_exists_leb : ∀ n m,
    (∃ x, m = x + n) → n ≤? m = true := by
  -- ADMITTED
  intro n m ⟨x, Hx⟩
  rw [Hx]
  apply leb_plus
  -- /ADMITTED

-- HIDE
/- A direct proof without a lemma. -/
theorem add_exists_leb' : ∀ n m,
    (∃ x, m = x + n) → n ≤? m = true := by
  intro n
  induction n
  case zero => intro m H; rfl
  case succ n' IHn' =>
    intro m ⟨x, Hx⟩
    rw [Hx]
    dsimp [leb]
    apply IHn'
    exists x
-- /HIDE
-- []
-- /FULL

-------------------------------------------------------------------------------
/- ## Recap: Logical Connectives in Lean -/

/- Connectives introduced in this chapter:
    * `A ∧ B` (conjunction):
      * introduced with `constructor`
      * eliminated with `intro ⟨HA, HB⟩` or `let ⟨HA, HB⟩ := H`
    * `A ∨ B` (disjunction):
      * introduced with `left` and `right`
      * eliminated with `cases`
    * `False` (falsehood):
      * eliminated with `cases` or `contradiction`
    * `¬ A` (negation):
      * defined as `A → False`
    * `True` (truthhood):
      * introduced as`True.intro` or with `constructor`
    * `A ↔ B` (iff):
      * introduced with `constructor`
      * eliminated with `intro ⟨HAB, HBA⟩` or `let ⟨HAB, HBA⟩ := H`
    * `∃ x : A, P` (existential):
      * introduced with `exists t`
      * eliminated with `intro ⟨x, Hx⟩` or `let ⟨x, Hx⟩ := H`
 
    Fundamental connectives we've been using since the beginning:
    * equality (`e1 = e2`)
    * implication (`P → Q`)
    * universal quantification (`∀ x, P`) -/

-------------------------------------------------------------------------------
/- ## Programming with Propositions -/

/- FULL: The logical connectives that we have seen provide a rich vocabulary
    for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express teh claim that an element `x`
    occurs in a list `l`.
    Notice that this property has a simple recursive structure: -/

/- TERSE: What does it mean to say that
    "an element `x` occurs in a list `l`"?
    * If `l` is the empty list, then `x` cannot occur in it,
      so the property "`x` appears in `l`" is simply false.
    * Otherwise, `l` has the form `[x' :: l']`.
      In this case, `x` occurs in `l` if it is equal to `x'`
      or if it occurs in `l'`. -/

/- We can translate this directly into a straightforward recursive function
    taken an element and a list and returning... a proposition! -/

def In {α : Type} (x : α) (xs : List α) : Prop :=
  match xs with
  | [] => False
  | x' :: xs' => x = x' ∨ In x xs'

/- When `In` is applied to a concrete list, it exapnds into a concrete sequence
   of nested disjunctions. -/

example : In 4 [1, 2, 3, 4, 5] := by
  -- WORKINCLASS
  dsimp [In]; right; right; right; left; rfl
  -- /WORKINCLASS

example : ∀ n : Nat, In n [2, 4] → ∃ n' : Nat, n = 2 * n' := by
  -- WORKINCLASS
  dsimp [In]
  intro n H
  obtain H | H | ⟨⟨⟩⟩ := H
  case inl => exists 1
  case inr.inl => exists 2
  /- (Notice the use of the empty pattern to discharge the last case.) -/
  -- /WORKINCLASS

/- We can also reason about more generic statements involving `In`. -/

theorem In_map : ∀ (α β : Type) (f : α → β) (xs : List α) (x : α),
    In x xs → In (f x) (List.map f xs) := by
  -- TERSE: FOLD
  intro α β f xs x
  induction xs
  case nil => intro H; contradiction
  case cons x' xs' IH =>
    dsimp [In]
    intro H
    obtain H | H := H
    case inl => rw [H]; left; rfl
    case inr => right; exact (IH H)
  -- TERSE: /FOLD

-- FULL
/- This way of defining propositions recursively is very convenient in
    some cases, less so in others.  In particular, it is subject to the
    usual restrictions regarding definitions of recursive functions,
    e.g., the requirement that they be "obviously terminating."

    In the next chapter, we will see how to define propositions
    _inductively_ -- a different technique with its own strengths and
    limitations. -/

-- EX2 (In_map_iff)
theorem In_map_iff : ∀ (α β : Type) (f : α → β) (xs : List α) (y : β),
    In y (List.map f xs) ↔ ∃ x, f x = y ∧ In x xs := by
  intro α β f xs y
  constructor
  case mp =>
    induction xs
    -- ADMITTED
    case nil => intro H; contradiction
    case cons x' xs' IH =>
      dsimp [In]
      intro H
      obtain H | H := H
      case inl =>
        rw [H]; exists x'; constructor
        case left => rfl
        case right => left; rfl
      case inr =>
        let ⟨x', H1, H2⟩ := (IH H)
        exists x'; constructor
        case left => exact H1
        case right => right; exact H2
    -- /ADMITTED
  case mpr =>
    -- ADMITTED
    intro ⟨x, H1, H2⟩
    rw [← H1]
    apply In_map
    exact H2
    -- /ADMITTED
-- []
-- /FULl

-- FULL
-- EX3! (All)
/- We noted above that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if `P` has type
    `Nat -> Prop`, then `P n` says that property `P` holds of `n`.

    Drawing inspiration from `In`, write a recursive function `All`
    stating that some property `P` holds of all elements of a list
    `xs`. To make sure your definition is correct, prove the `All_In`
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of `All_In`.) -/

def All {α : Type} (P : α → Prop) (xs : List α) : Prop :=
  -- ADMITDEF
  match xs with
  | [] => True
  | x :: xs' => P x ∧ All P xs'
  -- /ADMITDEF

theorem All_In : ∀ α (P : α → Prop) (xs : List α),
    (∀ x, In x xs → P x) ↔ All P xs := by
  -- ADMITTED
  intro α P xs
  induction xs
  case nil =>
    dsimp [In, All]
    constructor
    case mp => intros; exact ⟨⟩
    case mpr => intros; contradiction
  case cons x' xs' IH =>
    dsimp [In, All]
    let ⟨IHl, IHr⟩ := IH
    constructor
    case mp =>
      intro H; constructor
      case left => apply H; left; rfl
      case right =>
        apply IHl
        intro x' Hx'; apply H
        right; exact Hx'
    case mpr =>
      intro ⟨Hx, H⟩ x' Hxxs
      obtain Hxx' | Hxs := Hxxs
      case inl => rw [Hxx']; exact Hx
      case inr => apply IHr; apply H; apply Hxs
  -- /ADMITTED
-- GRADE_THEOREM 3: All_In
-- []

-- EX2? (combine_odd_even)
/- Complete the definition of `combine_odd_even` below. It takes as arguments
    two properties of numbers, `Podd` and `Peven`, and it should return
    a property `P` such that `P n` is equivalent to `Podd n` when `n` is odd
    and equivalent to `Peven n` otherwise. -/

def combine_odd_even (Podd Peven : Nat → Prop) : Nat → Prop :=
  -- ADMITDEF
  fun n => bif odd n then Podd n else Peven n
  -- /ADMITDEF

/- To test your definition, prove the following facts: -/

theorem combined_odd_even_intro : ∀ Podd Peven n,
    (odd n = true → Podd n) →
    (odd n = false → Peven n) →
    combine_odd_even Podd Peven n := by
  -- ADMITTED
  intro Podd Peven n Hodd Heven
  unfold combine_odd_even
  cases h : odd n
  case false =>
    dsimp; apply Heven; exact h
  case true =>
    dsimp; apply Hodd; exact h
  -- /ADMITTED

theorem combined_odd_even_elim_odd : ∀ Podd Peven n,
    combine_odd_even Podd Peven n →
    (odd n = true) →
    Podd n := by
  -- ADMITTED
  intro Podd Peven n H Hodd
  unfold combine_odd_even at H
  rw [Hodd] at H
  dsimp at H; exact H
  -- /ADMITTED

theorem combined_odd_even_elim_even: ∀ Podd Peven n,
    combine_odd_even Podd Peven n →
    (odd n = false) →
    Peven n := by
  -- ADMITTED
  intro Podd Peven n H Hodd
  unfold combine_odd_even at H
  rw [Hodd] at H
  dsimp at H; exact H
  -- /ADMITTED
-- []

-------------------------------------------------------------------------------
/- ## Applying Theorems to Arguments -/

/- FULL: Lean treats _proofs_ as first-class objects.
    There is a great deal to be said about this, but it is not necessary
    to understand it all to use Lean. This section gives just a taste,
    leaving a deeper exploration for the optional chapters
    `ProofObjects` and `IndPrinciples`. -/
/- TERSE: Lean also treats _proofs_ as first-class objects! -/

/- We have seen that we can use `#check` to ask Lean whether an expression
    has a given type: -/

#check (add: Nat → Nat → Nat)

/- We can also use it to check what theorem a particular identifier refers to: -/

/-- info: add_comm (n m : Nat) : n + m = m + n -/
#guard_msgs in
#check add_comm

/-- info: add_assoc (n m p : Nat) : n + (m + p) = n + m + p -/
#guard_msgs in
#check add_assoc

/- Lean checks the _statements_ of the `add_comm` and `add_assoc` theorems
    in the same way that it checks the _type_ of any term (e.g. `add`).
    Leaving off the colon and the type, Lean prints these types
    in the infoview for us.

    Why?

    The reason is that the identifier `add_comm` actually refers to a
    _proof object_ -- a logical derivation establishing the truth of the
    statement `∀ n m, n + m = m + n`. The type of this object
    is the proposition that it is a proof of.

    The type of an ordinary function tells us what we can do with it.
      * If we have a term of type `Nat → Nat → Nat`, we can give it
        two `Nat`s as arguments and get a `Nat` back.
    Similarly, the statement of a theorem tells us what we can use
    that theorem for.
      * If we have a term of type `∀ n m, n = m → n + n = m + n`,
        and we provide it two numbers `n` and `m` and a third "arugment"
        of type `n = m`, we get back a proof object of type `n + n = m + m`. -/

/- FULL: Operationally, this analogy goes even further: by applying a theorem
    as if it were a function, i.e., applying it to values and hypotheses
    with matching types, we can specialize its result without having to
    resort to intermediate assertions. For example, suppose we wanted
    to prove the follwing result: -/

/- TERSE: Lean actually allows us to _apply_ a theorem as if it were
    a function. This is often handy in proof scripts -- e.g., suppose
    we want to prove the following: -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∀ x y z : Nat, x + (y + z) = (z + y) + x := by

/- It appears at first sight that we ought to be able to prove this
    be rewriting with `add_comm` twice to make the two sides match.
    The problem is that the second rewrite will undo the effect
    of the first. -/

  intro x y z
  rw [add_comm]
  rw [add_comm]
  sorry
  /- We are back where we started... -/

/- We can fix this by applying `add_comm` to the arguments we want it
    to be instantiated with, in much the same way as we apply
    a polymorphic function to a type argument. Then the rewrite is forced
    to happen exactly where we want it. -/

example : ∀ x y z : Nat, x + (y + z) = (z + y) + x := by
  intro x y z
  rw [add_comm]
  rw [add_comm z y]

-- FULL
/- If we really wanted, we could in fact do it for both rewrites. -/
example : ∀ x y z : Nat, x + (y + z) = (z + y) + x := by
  intro x y z
  rw [add_comm x (y + z)]
  rw [add_comm z y]
-- /FULL

-- JC: Omitting this example below because `apply` in Lean works like `eapply` in Rocq,
--     and I don't think this is the right moment to introduce the concept of
--     metavariables and the fact that goals are just term holes.
/- Here's another example of using a theorem about lists like a function.
    Suppose we have proven the following simple fact about lists...

theorem In_not_nil : ∀ α (x : α) (xs : List α),
    In x xs → xs ≠ [] := by
  -- FOLD
  intro α x xs H Hxs; rw [Hxs] at H; cases H
  -- /FOLD

/- FULL: (i.e., if a list `xs` contains some element `x`,
    then `xs` must be nonempty.) -/

/- Note that one quantified variable (`x`) does not appear in the conclusion
    (`xs ≠ []`). Intuitively, we should be able ot use this theorem to prove
    the special case where `x` is `42`. However, simply invoking the tactic
    `apply In_not_nil` will fail because it cannot infer the value of `x`. -/

example : ∀ xs : List Nat, In 42 xs → xs ≠ [] := by
  intros xs H
  apply In_not_nil
  exact H

/- There are several way sto work around this: -/

/- We can use `apply ... at ...`: -/
example : ∀ xs : List Nat, In 42 xs → xs ≠ [] := by
  intros xs H
  apply In_not_nil at H
  exact H

/- We can explicitly supply the argument `42` for the parameter `x`: -/
example : ∀ xs : List Nat, In 42 xs → xs ≠ [] := by
  intros xs H
  apply In_not_nil (x := 42)
  exact H

/- Or we can explicitly apply the argument to the lemma directly: -/
example : ∀ xs : List Nat, In 42 xs → xs ≠ [] := by
  intros xs H
  apply In_not_nil Nat 42
  exact H

/- We can also provide the `exact` proof by applying the lemma
    to the hypothesis and allow the other arguments to be inferred: -/
example : ∀ xs : List Nat, In 42 xs → xs ≠ [] := by
  intros xs H
  exact In_not_nil _ _ _ H
-/

-- FULL
/- You can "use a theorem as a function" in this way with almost any tactic
    that can take a theorem's name as an argument.

    Note, also, that theorem application uses the same inference mechanisms
    as function application; thus, it is possible, for example, to supply
    wildcards as arguments to be inferred, or to declare some hypotheses
    to a theorem as implicit by default. These features are illustrated in
    the proof below. (The details of how this proof works are not critical
    -- the goal here is just to illustrate applying theorems to arguments.) -/

example : ∀ {n : Nat} {ns : List Nat},
    In n (List.map (fun m => m * 0) ns) → n = 0 := by
  intros n ns H
  let ⟨m, Hm, _⟩ := (In_map_iff _ _ _ _ _).mp H
  rw [mul_zero] at Hm; rw [Hm]

/- We will see many more examples in later chapters. -/
-- /FULL

-- HIDEFROMADVANCED
-- TERSE

-- HIDE
namespace FunctionTheoremQuiz
-- /HIDE

-- HIDEFROMHTML
/--  warning: declaration uses `sorry` -/
#guard_msgs in
example : ∀ n m : Nat,
    n = m → m = 42 →
    (∀ (α : Type) (a b c : α), a = b → b = c → a = c) →
    True := by
  intros n m H1 H2 trans_eq
-- /HIDEFROMHTML

-- QUIZ
/- Suppose we have
    ```
    n m : Nat
    H1 : n = m
    H2 : b = 42
    trans_eq : ∀ (α : Type) (a b c : α), a = b → b = c → a = c
    ```
    What is the type of this "proof object"?
    ```
    trans_eq Nat n m 42 H1 H2
    ```

    1. `n = m`
    2. `42 = n`
    3. `n = 42`
    4. Does not typecheck
   -/
  -- FOLD
  have : n = 42 := trans_eq Nat n m 42 H1 H2
  -- /FOLD
-- /QUIZ

-- QUIZ
/- Suppose, again, we have
    ```
    n m : Nat
    H1 : n = m
    H2 : b = 42
    trans_eq : ∀ (α : Type) (a b c : α), a = b → b = c → a = c
    ```
    What is the type of this proof object?
    ```
    trans_eq _ _ _ _ H1 H2
    ```

    1. `n = m`
    2. `42 = n`
    3. `n = 42`
    4. Does not typecheck
   -/
  -- FOLD
  have : n = 42 := trans_eq _ _ _ _ H1 H2
  -- /FOLD
-- /QUIZ

-- QUIZ
/- Suppose, again, we have
    ```
    n m : Nat
    H1 : n = m
    H2 : b = 42
    trans_eq : ∀ (α : Type) (a b c : α), a = b → b = c → a = c
    ```
    What is the type of this proof object?
    ```
    trans_eq Nat m 42 n H2
    ```

    1. `m = n`
    2. `m = n → 42 = n`
    3. `42 = n → m = n`
    4. Does not typecheck
   -/
  -- FOLD
  have : 42 = n → m = n := trans_eq Nat m 42 n H2
  -- /FOLD
-- /QUIZ

-- QUIZ
/- Suppose, again, we have
    ```
    n m : Nat
    H1 : n = m
    H2 : b = 42
    trans_eq : ∀ (α : Type) (a b c : α), a = b → b = c → a = c
    ```
    What is the type of this proof object?
    ```
    trans_eq _ 42 n m
    ```

    1. `n = m → m = 42 → n = 42`
    2. `42 = n → n = m → 42 = m`
    3. `n = 42 → 42 = m → n = m`
    4. Does not typecheck
   -/
  -- FOLD
  have : 42 = n → n = m → 42 = m := trans_eq _ 42 n m
  -- /FOLD
-- /QUIZ

-- QUIZ
/- Suppose, again, we have
    ```
    n m : Nat
    H1 : n = m
    H2 : b = 42
    trans_eq : ∀ (α : Type) (a b c : α), a = b → b = c → a = c
    ```
    What is the type of this proof object?
    ```
    trans_eq _ _ _ _ H2 H1
    ```

    1. `b = a`
    2. `42 = a`
    3. `a = 42`
    4. Does not typecheck
   -/
  -- FOLD
  /- have := trans_eq _ _ _ _ H2 H1 -/
  -- /FOLD
-- /QUIZ

  -- HIDEFROMHTML
  sorry
  -- /HIDEFROMHTML

-- HIDE
end FunctionTheoremQuiz
-- /HIDE

-- /TERSE
-- /HIDEFROMADVANCED

-------------------------------------------------------------------------------
/- ## Working with Decidable Properties -/

/- We've seen two different ways of expressing logical claims in Lean:
    with _booleans_ (of type `Bool`), and with _propositions_ (of type `Prop`).
    Here are the key differences between `Bool` and `Prop`:

    |                     | `Bool` | `Prop` |
    | ------------------- | ------ | ------ |
    | decidable?          | yes    | no     |
    | useable with match? | yes    | no     | -/

/- FULL:  FULL: The crucial difference between the two worlds is _decidability_.
    Every (closed) expression of type `Bool` can be simplified in a finite
    number of steps to either `true` or `false` -- i.e., there is a terminating
    mechanical procedure for deciding whether or not it is `true`.

    This means that, for example, the type `Nat → Bool` is inhabited only by
    functions that, given a `Nat, always yield either `true` or `false` in
    finite time; this, in turn, means (by a standard computability argument)
    that there is _no_ function in `Nat → Bool` that checks whether a given
    number is the code of a terminating Turing machine.

    By contrast, the type `Prop` includes both decidable and undecidable
    mathematical propositions; in particular, the type `Nat → Prop`
    does contain functions representing properties like
    "the nth Turing machine halts."

    The second table row follows directly from this essential difference.
    To evaluate a pattern match (or conditional) on a boolean, we need to know
    whether the scrutinee evaluates to `true` or `false`; this only works for
    `bool`, not `Prop`. -/

/- TERSE: Since functions in Lean by default must terminate on all inputs,
    a terminating function of type `Nat → Bool` is a _decision procedure_ --
    i.e., it yields `true` or `false` on all inputs.

    For example, `even : Nat → Bool` is a decision procedure for the property
    "is even". -/

/- Since `Prop` includes _both_ decidable and undecidable properties,
    we have two options when we want to formalize a property that happens
    to be decidable: we can express it either as a boolean computation,
    or as a function into `Prop`. -/

/- For instance, to claim that a number `n` is even,
    we can say either that `even n` evaluates to `true`... -/
example : even 42 = true := by rfl

/- ... or that there exists some `k` such that `n = double k`. -/
example : Even 42 := by exists 21

/- Of course, it would be deeply strange if these two characterizations
    of evenness did not describe the same set of natural numbers!
    Fortunately, they do! -/

-- TERSE: HIDEFROMHTML

/- To prove this, we first need two helper lemmas. -/

theorem even_double : ∀ k : Nat,
    even (double k) = true := by
  -- FOLD
  intro k; induction k
  case zero => rfl
  case succ k' IHk' => dsimp [even, double]; exact IHk'
  -- /FOLD

-- FULL
-- EX3 (even_double_conf)
theorem even_double_conv : ∀ n : Nat, ∃ k : Nat,
    n = bif even n then double k else succ (double k) := by
  -- ADMITTED
  intro n; induction n
  case zero => exists 0
  case succ n' IHn' =>
    let ⟨k', IHk'⟩ := IHn'
    rw [even_succ]
    cases HE : even n'
    case false =>
      rw [HE] at IHk'; dsimp [not] at *
      exists (k' + 1); rw [IHk']
      dsimp [double]
    case true =>
      rw [HE] at IHk'; dsimp [not] at *
      exists k'; congr
  -- /ADMITTED
-- []
-- /FOLD
-- TERSE: /HIDEFROMHTML

/- Now the main theorem: -/
theorem even_bool_prop: ∀ n : Nat,
    even n = true ↔ Even n := by
  -- FOLD
  intro n; constructor
  case mp =>
    intro H
    let ⟨k, Hk⟩ := even_double_conv n
    rw [H] at Hk; dsimp at Hk
    unfold Even; exists k
  case mpr =>
   intro ⟨k, Hk⟩; rw [Hk]; apply even_double
  -- /FOLD

/- In view of this theorem, we can say that the boolean computation `even n`
    is _reflected_ in the truth of the proposition `∃ k, n = double k`. -/

-- HIDE
/- Similarly, we can state what it means for a number to be nonzero
    in two different ways: -/

def Nonzero (n : Nat) : Prop := ∃ m, n = succ m

def nonzero (n : Nat) := not (n == 0)

theorem nonzero_bool_prop : ∀ n : Nat,
    nonzero n = true ↔ Nonzero n := by
  -- WORKINCLASS
  intro n; unfold Nonzero nonzero; constructor
  case mp =>
    intro H; cases n
    case zero => dsimp [not] at H; contradiction
    case succ n' => exists n'
  case mpr =>
    intro ⟨m, Hm⟩; rw [Hm]; rfl
  -- /WORKINCLASS
-- /HIDE

/- Similarly, to state that two numbers `n` and `m` are equal,
    we can say either

    1. that `n == m` returns `true`, or
    2. that `n = m`.

    Again, these two notions are equivalent: -/

theorem beq_eq : ∀ n1 n2 : Nat,
    (n1 == n2) = true ↔ n1 = n2 := by
  -- FOLD
  intro n1 n2; constructor
  case mp => apply eqb_true
  case mpr => intro H; rw [H, eqb_refl]
  -- /FOLD

-- HIDEFROMADVANCED

/- So what should we do in situations where some claim could be formalized
    as either a proposition or a boolean computation?
    Which should we choose?

    In general, _both_ can be useful. For example, booleans are more useful
    for defining functions, since we can test whether they are true using
    conditional expressions. -/

def is_even_prime (n : Nat) : Bool :=
  bif n == 2 then true else false

/- FULL:  FULL: Beyond the fact that non-computable properties are possible
    in general to phrase as boolean computations, even many _computable_
    properties are easier to express using `Prop` than `bool`, since
    recursive function definitions are subject to significant restrictions.
    For instance, the next chapter shows how to define the property that
    a regular expression matches a given string using `Prop`.
    Doing the same with `Bool` would amount to writing a regular expression
    matching algorithm, which would be more complicated, harder to understand,
    and harder to reason about than a simple (non-algorithmic) definition
    of this property.

    Conversely, an important side benefit of stating facts using booleans
    is enabling some proof automation through computation with terms, a
    technique known as _proof by reflection_.

    Consider the following statement: -/

-- JC: This was originally 1000 but Lean's default recursion depth
--     is not large enough to reduce `double 50` lol
example : Even 100 := by
/- The most direct way to prove this is to give the value of `k` explicitly. -/
  unfold Even; exists 50

/- The proof of the corresponding boolean statement is simpler,
    because we don't have to invent the witness `50`:
    computation does it for us! -/

example : even 100 := by rfl

/- Now, the useful observation is that, since the two notions are equivalent,
    we can use the boolean formulation to prove the other one
    without mentioning the value 500 explicitly: -/

example : Even 100 := by
  let ⟨H, _⟩ := even_bool_prop 100
  apply H; rfl

/- Although we haven't gained much in terms of proof-script simplicity
    in this case, larger proofs can often be made considerably simpler
    by the use of reflection. -/

-- JC: Is there a Lean version? Or maybe just mention Rocq?
/- As an extreme example, a famous mechanized proof of the even more famous
    _four colour theorem_ uses reflection ot reduce the analysis of hundreds
    of different cases to a boolean computation. -/

/- Another advantage of booleans is that the _negation_ of a claim about
    booleans is straightforward to state and (when true) to prove:
    simply slip the expected boolean result. -/

example : even 101 = false := by rfl

/- In contrast, propositional negation can be difficult to work with directly.
    For example, suppose we state the nonevenness of `101` propositionally: -/

example : ¬ Even 101 := by
/- Proving this directly -- by assuming that there is some `n` such that
    `101 = double n` and then somehow reasoning to a contradiction --
    would be rather complicated.

    But if we convert it to a claim about the boolean `even` function,
    we can let Lean do the work for us. -/
  -- WORKINCLASS
  intro H; let ⟨_, Hb⟩ := even_bool_prop 101
  apply Hb at H; dsimp [even] at H; contradiction
  -- /WORKINCLASS

/- Conversely, there are situations where it can be easier to work with
    propositions rather than booleans. In particular, knowing that
    `(n == m) = true` is generally of little direct help in the middle of
    a proof involving `n` and `m`. But if we convert the statement to
    the equivalent form `n = m`, then we can easily rewrite with it. -/

theorem add_beq_true : ∀ n m p : Nat,
    (n == m) = true → (n + p == m + p) = true := by
  -- WORKINCLASS
  intro n m p H
  let ⟨Hb, _⟩ := beq_eq n m
  apply Hb at H; rw [H, eqb_refl]
  -- /WORKINCLASS

/- FULL: We won't discuss reflection any further for the moment,
    but it serves as a good example showing the different strengths
    of booleans and general propositions.
    Being able to cross back and forth between the boolean and propositional
    worlds will often be convenient in later chapters. -/

-- FULL

-- EX2 (logical connectives)
/- The following theorems relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. -/

theorem andb_true_iff : ∀ b1 b2 : Bool,
    (b1 && b2) = true ↔ b1 = true ∧ b2 = true := by
  -- ADMITTED
  intro b1 b2; constructor
  case mp =>
    cases b1
    case false => dsimp [and]; intro; contradiction
    case true => dsimp [and]; intro H; exact ⟨rfl, H⟩
  case mpr =>
    cases b1
    case false => intro ⟨_, _⟩; contradiction
    case true => intro ⟨_, H⟩; dsimp [and]; exact H
  -- /ADMITTED

theorem orb_true_iff : ∀ b1 b2 : Bool,
    (b1 || b2) = true ↔ b1 = true ∨ b2 = true := by
  -- ADMITTED
  intro b1 b2; constructor
  case mp =>
    cases b1
    case false => dsimp [or]; intro H; right; exact H
    case true => dsimp [or]; intro; left; rfl
  case mpr =>
    cases b1
    case false =>
      intro H; obtain _ | Hr := H
      case inl => contradiction
      case inr => dsimp [or]; exact Hr
    case true => intro; dsimp [or]
  -- /ADMITTED
-- GRADE_THEOREM 1: andb_true_iff
-- GRADE_THEOREM 2: orb_true_iff
-- []

-- EX3 (beq_list)
/- Given a boolean operator `beq` for testing equality of elements
    of some type `α`, we can define a function `beq_list` for testing
    equality of lists with elements in `α`. Complete the definition
    of the `beq_list` function below. to make sure that your definition
    is correct, prove the lemma `beq_list_true_iff`. -/

def beq_list {α : Type} (beq : α → α → Bool) (xs1 xs2 : List α) : Bool :=
  -- ADMITDEF
  match xs1, xs2 with
  | [], [] => true
  | x1 :: xs1, x2 :: xs2 => beq x1 x2 && beq_list beq xs1 xs2
  | _, _ => false
  -- /ADMITDEF

-- JC: Should this also go after `propext` to use rewriting by `↔`?
theorem beq_list_true_iff : ∀ α (beq : α → α → Bool),
    (∀ x1 x2, beq x1 x2 = true ↔ x1 = x2) →
    ∀ xs1 xs2, beq_list beq xs1 xs2 = true ↔ xs1 = xs2 := by
  -- ADMITTED
  intro α beq Hbeq xs1
  induction xs1
  case nil =>
    intro xs2; cases xs2
    case nil =>
      dsimp [beq_list]; constructor
      case mp => intro; rfl
      case mpr => intro; rfl
    case cons x2 xs2' =>
      dsimp [beq_list]; constructor
      case mp => intro; contradiction
      case mpr => intro; contradiction
  case cons x1 xs1' IHxs1' =>
    intro xs2; cases xs2
    case nil =>
      dsimp [beq_list]; constructor
      case mp => intro; contradiction
      case mpr => intro; contradiction
    case cons x2 xs2' =>
      dsimp [beq_list]
      let ⟨Hl, Hr⟩ := andb_true_iff (beq x1 x2) (beq_list beq xs1' xs2')
      let ⟨Hx1, Hx2⟩ := Hbeq x1 x2
      let ⟨IH1, IH2⟩ := IHxs1' xs2'
      constructor
      case mp =>
        intro H; let ⟨Hx, Hxs⟩ := Hl H; congr
        . apply Hx1; exact Hx
        . apply IH1; exact Hxs
      case mpr =>
        intro H; injection H with Hx Hxs
        apply Hr; constructor
        case left => apply Hx2; exact Hx
        case right => apply IH2; exact Hxs
  -- /ADMITTED
-- GRADE_THEOREM 3: beq_list_true_iff
-- []
-- /FULL

-- FULL
-- EX2! (All_forallb)
/- Prove the theorem below, which relates `forallb`, from the exercise
    `Tactics.forall_exists_challenge`, to the `All` property defined above. -/

/- Copy the definition of `forallb` from Tactics here so that this file can be
    graded on its own. -/
def Logic.forallb {α : Type} (test : α → Bool) (xs : List α) : Bool :=
  -- ADMITDEF
  match xs with
  | [] => true
  | x :: xs' => test x && forallb test xs'
  -- /ADMITDEF

theorem forallb_true_iff : ∀ α (test : α → Bool) (xs : List α),
    Logic.forallb test xs = true ↔ All (fun x => test x = true) xs := by
  -- ADMITTED
  intro α test xs
  induction xs
  case nil =>
    dsimp [Logic.forallb, All]; constructor
    case mp => intro; exact ⟨⟩
    case mpr => intro; rfl
  case cons x xs' IHxs' =>
    let ⟨H1, H2⟩ := andb_true_iff (test x) (Logic.forallb test xs')
    let ⟨IH1, IH2⟩ := IHxs'
    dsimp [Logic.forallb, All]
    constructor
    case mp =>
      intro H
      let ⟨H1', H2'⟩ := H1 H
      constructor
      case left => exact H1'
      case right => apply IH1; exact H2'
    case mpr =>
      intro ⟨H1', H2'⟩
      apply H2; constructor
      case left => exact H1'
      case right => apply IH2; exact H2'
  -- /ADMITTED
/- (Ungraded thought question) Are there any important properties often
    the function `forallb` which are not captured by this specification? -/

-- SOLUTION
/- This theorem exactly captures the input-output behavior of `forallb`.
    However, it does not say anything about the running time. -/
-- /SOLUTION
-- GRADE_THEOREM 2: forallb_true_iff
-- []
-- /FULL

-------------------------------------------------------------------------------
/- ## The Logic of Lean -/

/- FULL: Lean's logical core differs in some important ways from other formal
    systems that are used by mathematicians to write down precise and rigorous
    definitions and proofs -- in particular from Zermelo–Fraenkel Set Theory
    (ZFC), the most popular foundation for paper-and-pencil mathematics.

    We conclude this chapter with a brief discussion of some of the
    most significant differences between these two worlds. -/

/- TERSE: Lean's logical core is a "metalanguage for mathematics" in
    the same sense as familiar foundations for paper-and-pencil math, like
    Zermelo–Fraenkel Set Theory (ZFC).

    Mostly, the differences are not too important,
    but a few points are useful to understand. -/

/- ### Propositional Extensionality -/

/- Lean's logic is quite minimalistic. This means that on occasionally
    encounters cases where translating standard mathematical reasoning
    into Lean is cumbersome -- or even impossible -- unless we enrich
    its core logic with additional axioms. -/

/- FULL: For example, the equality assertions that we have seen so far mostly
    have concerned elements of inductive types (`Nat`, `Bool`, etc.).
    But since the equality operator is polymorphic, we can use it at _any_ type
    -- in particular, we can write propositions claiming that two _propositions_
    are equal to each other: -/

/- TERSE: A first instance has to do with equality of propositions. -/

#check (∀ P Q : Prop, (P ∧ Q) = (Q ∧ P) : Prop)

/- This is an equality between two conjunctions, which itself is also
    a proposition. It states that commuted conjunctions are equal propositions.
    However, we cannot prove this equality by reflexivity, as the two sides
    don't compute to the same term, and we cannot proceed by cases on
    `P` or `Q`, as they are not inductive. -/

/-- Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : ∀ P Q : Prop, P ∧ Q = Q ∧ P := by
  intros P Q; rfl

/-- Tactic `cases` failed -/
#guard_msgs (substring := true) in
example : ∀ P Q : Prop, P ∧ Q = Q ∧ P := by
  intros P Q; cases P

/- However, we _can_ prove that P ∧ Q implies Q ∧ P, and vice versa -- this is
    the commutativity of conjunction that we have seen earlier. -/

#check (@and_comm : ∀ P Q : Prop, P ∧ Q ↔ Q ∧ P)

/- Since it would be convenient to be able to rewrite propositions from
    one side of `↔` to the other, Lean provides an axiom to turn `↔` into `=`,
    which is called _propositional extensionality_ (`propext`).
    We can use it to show that commuted conjoined propositions are equal. -/

/-- info: axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b -/
#guard_msgs in
#print propext

theorem and_comm_eq : ∀ P Q : Prop, (P ∧ Q) = (Q ∧ P) := by
  intro P Q; apply propext; apply and_comm

/- Similarly, we can use it to show that reassociated conjoined propositions
    are equal as well. -/

theorem and_assoc_eq : ∀ P Q R : Prop, ((P ∧ Q) ∧ R) = (P ∧ (Q ∧ R)) := by
  intro P Q R; apply propext; apply and_assoc

/- Here is an example of where using `=` instead of `↔` is more convenient:
    we show that it's possible to "flip" three conjoined propositions. -/

theorem and_comm_flip : ∀ P Q R : Prop,
    (P ∧ Q ∧ R) ↔ (R ∧ Q ∧ P) := by

/- This can be proven by constructing the `↔`, then destructing the `↔`
    in `add_comm` and `add_assoc`, then applying them a few times.
    But this is a lot of hassle, when the proof conceptually simple:
    we flip `Q` and `R`, then we flip that conjunction with `P`, and we
    finish by associativity. By using `and_comm_eq`, this is easily done
    by rewriting equal propositions. -/

  intro P Q R; rw [and_comm_eq Q R, and_comm_eq P, and_assoc_eq]

/- The pattern of deriving an equality of propositions out of `↔`
    then rewriting by that equality is so common that Lean will implicitly
    cast `↔` to `=`, allowing you to rewrite on `↔` directly. -/

theorem and_comm_flip' : ∀ P Q R : Prop,
    (P ∧ Q ∧ R) ↔ (R ∧ Q ∧ P) := by
  intro P Q R; rw [@and_comm Q R, @and_comm P, and_assoc]

/- Under the hood, this proof still uses `propext`, which you can check by
    asking for all of the axioms used by a declaration. -/

/-- info: 'and_comm_flip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms and_comm_flip

/-- info: 'and_comm_flip'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms and_comm_flip'

-- EX1 (mul_eq_0_ternary)
theorem mul_eq_0_ternary : ∀ n m p : Nat,
    n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 := by
  -- ADMITTED
  intro n m p
  rw [mul_eq_0, mul_eq_0, or_associate]
  -- /ADMITTED
-- []

-- EX2 (In_app_iff)
theorem In_app_iff : ∀ (α : Type) (xs xs' : List α) (x : α),
    In x (xs ++ xs') ↔ In x xs ∨ In x xs' := by
  intro α xs; induction xs
  -- ADMITTED
  case nil =>
    intro xs x; constructor
    case mp => intro H; right; exact H
    case mpr =>
      dsimp [In]; intro H; cases H
      case inl H => contradiction
      case inr H => exact H
  case cons y ys IH =>
    intro xs' x; dsimp [In]
    rw [IH, or_assoc]
  -- /ADMITTED
-- []

-- EX1 (beq_neq)
/- The following theorem is an alternative "negative" formulation of `beq_eq`
    that is more convenient in certain situations.
    (We'll see examples in later chapters.) Hint: `not_true_iff_false`. -/
theorem beq_neq : ∀ n m : Nat,
    (n == m) = false ↔ n ≠ m := by
  -- ADMITTED
  intro n m
  rw [← not_true_iff_false]
  unfold Ne
  rw [beq_eq n m]
  -- /ADMITTED
-- []

/- ### Functional Extensionality -/

/- ### Classical vs. Constructive Logic -/
