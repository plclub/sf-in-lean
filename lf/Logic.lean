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
import CustomTactics
open Nat hiding add_succ mul_succ
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

theorem succ_inj : injective succ := by
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

-- JC [TODO]: move this to after propext
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
    rw [or_assoc]
    sorry
  -- /ADMITTED
-- []
-- /FULL

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
