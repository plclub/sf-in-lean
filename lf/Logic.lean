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

/- TERSE: We can also apply the constructor for the conjunction explicitly. -/
example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  case left  => /- 3 + 4 = 7 -/ rfl
  case right => /- 2 * 2 = 4 -/ rfl

/- Or we can anonymous constructor syntax to construct it. -/
example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact ⟨/- 3 + 4 = 7 -/ rfl, /- 2 * 2 = 4 -/ rfl⟩

-- FULL
-- EX2 (plus_is_zero)
theorem plus_is_zero : ∀ n m : Nat,
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
  apply plus_is_zero at H
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
  case succ => right; dsimp [pred]
  -- /WORKINCLASS

-- EX2 (mul_is_succ)
theorem mul_is_succ : forall n m : Nat,
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
  intro P Q H
  cases H
  case inl HP => right; exact HP
  case inr HQ => left; exact HQ

/- ## Falsehood and Negation -/

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
