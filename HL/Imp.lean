/- Imp: Simple Imperative Programs -/

-- Claude: This chapter is being ported from the Rocq `Imp.v` to Lean by
-- Claude.  Human review is needed, especially of the prose and of the
-- pedagogical choices flagged in `MWH`/`dev` notes below.

-- INSTRUCTORS: This chapter plus `Maps` takes a little more than one 80-minute lecture.

-- MWH (port note): Constructors of `Aexp`/`Bexp` are always written with
-- Lean's dot notation (`.ANum`, `.BEq`, …), resolved by the expected type.
-- This is idiomatic Lean and it sidesteps the clash between the `BEq`
-- constructor and Lean's `BEq` typeclass.
-- MWH (port note): The Rocq chapter's "Rocq Automation" tour has been
-- retooled here for Lean.  The tactic *combinators* (`try`, `<;>`,
-- `repeat`) are introduced in this chapter; the heavier decision
-- procedures (`simp`, `omega`) have already been introduced in Logical
-- Foundations, so we use them freely.

import LF.Maps

-- FULL
/-
  In this chapter, we take a more serious look at how to use Lean as a
  tool to study other things.  Our case study is a _simple imperative
  programming language_ called Imp, embodying a tiny core fragment of
  conventional mainstream languages such as C and Java.

  Here is a familiar mathematical function written in Imp.

  ```
  Z := X;
  Y := 1;
  while Z <> 0 do
    Y := Y * Z;
    Z := Z - 1
  end
  ```

  We concentrate here on defining the _syntax_ and _semantics_ of Imp;
  later chapters develop a theory of _program equivalence_ and introduce
  _Hoare Logic_, a popular logic for reasoning about imperative programs.
-/
-- /FULL

/-
  ######################################################################
  # Arithmetic and Boolean Expressions
-/

-- FULL
/-
  We'll present Imp in three parts: first a core language of _arithmetic
  and boolean expressions_, then an extension of these with _variables_,
  and finally a language of _commands_ including assignment, conditionals,
  sequencing, and loops.
-/
-- /FULL

/-
  ######################################################################
  ## Syntax
-/

namespace AExp

-- FULL
/-
  These two definitions specify the _abstract syntax_ of arithmetic and
  boolean expressions.
-/
-- /FULL
-- TERSE: /- Abstract syntax trees for arithmetic and boolean expressions: -/

inductive Aexp where
  | ANum (n : Nat)
  | APlus (a1 a2 : Aexp)
  | AMinus (a1 a2 : Aexp)
  | AMult (a1 a2 : Aexp)

inductive Bexp where
  | BTrue
  | BFalse
  | BEq (a1 a2 : Aexp)
  | BNeq (a1 a2 : Aexp)
  | BLe (a1 a2 : Aexp)
  | BGt (a1 a2 : Aexp)
  | BNot (b : Bexp)
  | BAnd (b1 b2 : Bexp)

-- FULL
/-
  In this chapter, we'll mostly elide the translation from the concrete
  syntax that a programmer would actually write to these abstract syntax
  trees -- the process that, for example, would translate the string
  `"1 + 2 * 3"` to the AST

  ```
  .APlus (.ANum 1) (.AMult (.ANum 2) (.ANum 3))
  ```

  For comparison, here's a conventional BNF (Backus-Naur Form) grammar
  defining the same abstract syntax:

  ```
  a := nat
      | a + a
      | a - a
      | a * a

  b := true
      | false
      | a = a
      | a <> a
      | a <= a
      | a > a
      | ~ b
      | b && b
  ```

  Compared to the Lean version above, the BNF is more informal but
  lighter and easier to read.  It's good to be comfortable with both
  sorts of notations: informal ones for communicating between humans and
  formal ones for carrying out implementations and proofs.
-/
-- /FULL

/-
  ######################################################################
  ## Evaluation
-/

/- _Evaluating_ an arithmetic expression produces a number. -/

def aeval (a : Aexp) : Nat :=
  match a with
  | .ANum n => n
  | .APlus  a1 a2 => aeval a1 + aeval a2
  | .AMinus a1 a2 => aeval a1 - aeval a2
  | .AMult  a1 a2 => aeval a1 * aeval a2

/- test_aeval1 -/
example : aeval (.APlus (.ANum 2) (.ANum 2)) = 4 := by rfl

/- Similarly, evaluating a boolean expression yields a boolean. -/

def beval (b : Bexp) : Bool :=
  match b with
  | .BTrue      => true
  | .BFalse     => false
  | .BEq a1 a2  => aeval a1 == aeval a2
  | .BNeq a1 a2 => aeval a1 != aeval a2
  | .BLe a1 a2  => decide (aeval a1 ≤ aeval a2)
  | .BGt a1 a2  => decide (aeval a1 > aeval a2)
  | .BNot b1    => !beval b1
  | .BAnd b1 b2 => beval b1 && beval b2

-- QUIZ
/-
  What does the following expression evaluate to?

  ```
  aeval (.APlus (.ANum 3) (.AMinus (.ANum 4) (.ANum 1)))
  ```

  (A) true    (B) false    (C) 0    (D) 3    (E) 6
-/
-- /QUIZ

/-
  ######################################################################
  ## Optimization
-/

-- FULL
/-
  We haven't defined very much yet, but we can already get some mileage
  out of the definitions.  Suppose we define a function that takes an
  arithmetic expression and slightly simplifies it, changing every
  occurrence of `0 + e` (i.e., `.APlus (.ANum 0) e`) into just `e`.
-/
-- /FULL

def optimize_0plus (a : Aexp) : Aexp :=
  match a with
  | .ANum n => .ANum n
  | .APlus (.ANum 0) e2 => optimize_0plus e2
  | .APlus  e1 e2 => .APlus  (optimize_0plus e1) (optimize_0plus e2)
  | .AMinus e1 e2 => .AMinus (optimize_0plus e1) (optimize_0plus e2)
  | .AMult  e1 e2 => .AMult  (optimize_0plus e1) (optimize_0plus e2)

-- FULL
/-
  To gain confidence that our optimization is doing the right thing we
  can test it on some examples and see if the output looks OK.
-/
-- /FULL

/- test_optimize_0plus -/
example :
    optimize_0plus (.APlus (.ANum 2)
                     (.APlus (.ANum 0)
                       (.APlus (.ANum 0) (.ANum 1))))
      = .APlus (.ANum 2) (.ANum 1) := by rfl

-- FULL
/-
  But if we want to be certain the optimization is correct -- that
  evaluating an optimized expression _always_ gives the same result as
  the original -- we should prove it!

  Here is a first, deliberately explicit proof.  It works, but notice how
  much of it is repetitive: several cases are discharged by exactly the
  same three-step incantation.
-/
-- /FULL

theorem optimize_0plus_sound (a : Aexp) :
    aeval (optimize_0plus a) = aeval a := by
  induction a with
  | ANum n => rfl
  | APlus a1 a2 ih1 ih2 =>
    cases a1 with
    | ANum n =>
      cases n with
      | zero =>
        simp only [optimize_0plus, aeval, Nat.zero_add]
        exact ih2
      | succ n =>
        simp only [optimize_0plus, aeval]
        rw [ih2]
    | APlus b1 b2 =>
      simp only [optimize_0plus, aeval] at ih1 ⊢
      rw [ih1, ih2]
    | AMinus b1 b2 =>
      simp only [optimize_0plus, aeval] at ih1 ⊢
      rw [ih1, ih2]
    | AMult b1 b2 =>
      simp only [optimize_0plus, aeval] at ih1 ⊢
      rw [ih1, ih2]
  | AMinus a1 a2 ih1 ih2 =>
    simp only [optimize_0plus, aeval]
    rw [ih1, ih2]
  | AMult a1 a2 ih1 ih2 =>
    simp only [optimize_0plus, aeval]
    rw [ih1, ih2]

/-
  ######################################################################
  # Tactic Combinators
-/

-- FULL
/-
  The amount of repetition in that last proof is a little annoying.  And
  if either the language of arithmetic expressions or the optimization
  being proved sound were significantly more complex, it would start to be
  a real problem.

  So far, we've been driving each subgoal by hand.  Lean also provides
  _combinators_ that build bigger tactics out of smaller ones, letting us
  discharge many similar subgoals at once.  Getting used to them takes a
  little energy, but it lets us scale up to more complex definitions and
  more interesting properties without drowning in boring, repetitive
  detail.
-/
-- /FULL
-- TERSE: /- That last proof was repetitive.  Time for a few combinators. -/

/-
  ######################################################################
  ## The `try` combinator
-/

/-
  If `t` is a tactic, then `try t` is a tactic that is just like `t`
  except that, if `t` fails, `try t` _successfully_ does nothing at all
  (rather than failing).
-/

theorem silly1 (P : Prop) (hp : P) : P := by
  try rfl -- `rfl` would fail here, but `try` swallows the failure...
  exact hp -- ...so we can still finish some other way.

theorem silly2 (ae : Aexp) : aeval ae = aeval ae := by
  try rfl -- here `try rfl` just does `rfl`

/-
  There is not much reason to use `try` in completely manual proofs like
  these, but it is very useful together with the `<;>` combinator, which
  we show next.
-/

/-
  ######################################################################
  ## The `<;>` combinator
-/

/-
  The compound tactic `t <;> t'` first performs `t` and then performs `t'`
  on _each subgoal_ generated by `t`.

  For example, consider the following trivial lemma.  Splitting on `n`
  leaves two subgoals that are discharged identically:
-/

theorem foo (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n with
  | zero   => omega
  | succ k => omega

-- TERSE: /- We can collapse the two identical branches with `<;>`: -/
theorem foo' (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n <;> omega -- run `cases n`, then `omega` on each subgoal

-- FULL
/-
  Using `<;>` we can get rid of the repetition in the proof that was
  bothering us a little while ago.  Most cases follow directly from the
  induction hypotheses, so we can dispatch them uniformly and only pause
  on the interesting one.
-/
-- /FULL

theorem optimize_0plus_sound' (a : Aexp) :
    aeval (optimize_0plus a) = aeval a := by
  induction a with
  | ANum n => rfl
  | APlus a1 a2 ih1 ih2 =>
    -- The interesting case: split on the shape of `a1`; when it is a
    -- literal we must additionally check whether it is `0`.
    cases a1 with
    | ANum n => cases n <;> simp_all [optimize_0plus, aeval]
    | APlus b1 b2  => simp_all [optimize_0plus, aeval]
    | AMinus b1 b2 => simp_all [optimize_0plus, aeval]
    | AMult b1 b2  => simp_all [optimize_0plus, aeval]
  | AMinus a1 a2 ih1 ih2 => simp_all [optimize_0plus, aeval]
  | AMult a1 a2 ih1 ih2 => simp_all [optimize_0plus, aeval]

/-
  ######################################################################
  ## The `repeat` combinator
-/

/-
  The `repeat` combinator takes another tactic and keeps applying it until
  it fails or until it succeeds but makes no further progress.

  For example, the following proof keeps trying to close the goal with an
  assumption and, failing that, to split it with a constructor, until
  nothing is left to do:
-/

theorem repeat_example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q ∧ P ∧ Q := by
  repeat first | exact hp | exact hq | constructor

/-
  The tactic `repeat t` never fails: if `t` doesn't apply to the goal,
  then `repeat` _succeeds_ without changing anything (i.e., it repeats
  zero times).  It also has no upper bound on the number of iterations, so
  a tactic that always makes progress will make `repeat` loop forever.
  Unlike evaluation of Lean _terms_, which is guaranteed to terminate,
  _tactic_ evaluation is not -- but this never threatens soundness: a
  diverging tactic just fails to build a proof.
-/

/-
  ######################################################################
  ## Defining new tactics
-/

-- FULL
/-
  Lean also lets us "program" in tactic scripts.  The simplest facility is
  a `macro`, which bundles several tactics into a single new command.  (For
  more sophisticated proof automation Lean offers `macro_rules`, `syntax`,
  and a full metaprogramming API written in Lean itself; see the
  _Metaprogramming in Lean_ book.)

  For example, here is a tiny tactic `crush_conj` that fully splits a goal
  built from `∧` and closes each atom by assumption:
-/
-- /FULL

macro "crush_conj" : tactic => `(tactic| repeat first | assumption | constructor)

theorem crush_example (P Q : Prop) (hp : P) (hq : Q) : (P ∧ Q) ∧ (Q ∧ P) := by
  crush_conj

/-
  ######################################################################
  ## The `omega` tactic
-/

-- FULL
/-
  `omega` is a decision procedure for linear arithmetic over the integers
  and naturals.  If the goal is built from

    - numeric constants, addition, subtraction, and multiplication by
      constants,
    - equality (`=`, `≠`) and ordering (`≤`, `<`, `≥`, `>`), and
    - the logical connectives `∧`, `∨`, `¬`, and `→`,

  then `omega` will either solve it or report that it is false.  (Rocq
  users will recognize this as the analogue of `lia`.)
-/
-- /FULL

example (m n o p : Nat) (h : m + n ≤ n + o ∧ o + 3 = p + 3) : m ≤ p := by
  omega

example (m n : Nat) : m + n = n + m := by omega

example (m n p : Nat) : m + (n + p) = m + n + p := by omega

/-
  ######################################################################
  ## A few more handy tactics
-/

/-
  Finally, here are some miscellaneous tactics -- all introduced in
  Logical Foundations -- that you may find convenient here:

    - `clear h`: delete hypothesis `h` from the context.

    - `subst x`: given a variable `x` with an assumption `x = e` or
      `e = x`, replace `x` by `e` everywhere and clear the assumption;
      `subst_vars` does this for _all_ such assumptions at once.

    - `rename_i x`: give a fresh, readable name to an inaccessible
      hypothesis introduced automatically by a tactic.

    - `assumption`: find a hypothesis that exactly matches the goal and
      use it.

    - `contradiction`: find a hypothesis that is logically `False` and
      close the goal.

    - `constructor`: apply a constructor of the goal's inductive type.
-/

/-
  ######################################################################
  # Optimizing Booleans
-/

-- EX3 (optimize_0plus_b_sound)
/-
  Since the `optimize_0plus` transformation doesn't change the value of an
  `Aexp`, we should be able to apply it to all the `Aexp`s that appear in a
  `Bexp` without changing the `Bexp`'s value.  Write a function that
  performs this transformation on `Bexp`s and prove it sound.  Use the
  combinators we've just seen to make the proof as short and elegant as
  possible.
-/

def optimize_0plus_b (b : Bexp) : Bexp :=
  -- ADMITDEF
  match b with
  | .BTrue      => .BTrue
  | .BFalse     => .BFalse
  | .BEq a1 a2  => .BEq (optimize_0plus a1) (optimize_0plus a2)
  | .BNeq a1 a2 => .BNeq (optimize_0plus a1) (optimize_0plus a2)
  | .BLe a1 a2  => .BLe (optimize_0plus a1) (optimize_0plus a2)
  | .BGt a1 a2  => .BGt (optimize_0plus a1) (optimize_0plus a2)
  | .BNot b1    => .BNot (optimize_0plus_b b1)
  | .BAnd b1 b2 => .BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  -- /ADMITDEF

/- optimize_0plus_b_test1 -/
example :
    optimize_0plus_b (.BNot (.BGt (.APlus (.ANum 0) (.ANum 4)) (.ANum 8)))
      = .BNot (.BGt (.ANum 4) (.ANum 8)) := by rfl -- ADMITTED
-- GRADE_THEOREM 0.5: optimize_0plus_b_test1

/- optimize_0plus_b_test2 -/
example :
    optimize_0plus_b (.BAnd (.BLe (.APlus (.ANum 0) (.ANum 4)) (.ANum 5)) .BTrue)
      = .BAnd (.BLe (.ANum 4) (.ANum 5)) .BTrue := by rfl -- ADMITTED
-- GRADE_THEOREM 0.5: optimize_0plus_b_test2

theorem optimize_0plus_b_sound (b : Bexp) :
    beval (optimize_0plus_b b) = beval b := by
  -- ADMITTED
  induction b with
  | BNot b1 ih => simp only [optimize_0plus_b, beval]; rw [ih]
  | BAnd b1 b2 ih1 ih2 => simp only [optimize_0plus_b, beval]; rw [ih1, ih2]
  | _ => simp only [optimize_0plus_b, beval, optimize_0plus_sound]
  -- /ADMITTED
-- GRADE_THEOREM 2: optimize_0plus_b_sound
-- []

/-
  ######################################################################
  # Evaluation as a Relation
-/

-- FULL
/-
  We have presented `aeval` and `beval` as functions defined by
  recursion.  Another way to think about evaluation -- one that is often
  more flexible -- is as a _relation_ between expressions and their
  values.  This perspective leads to inductive definitions like the
  following.  We name the hypotheses in each case (`h1`, `h2`); this
  gives us readable names to refer to during proofs.
-/
-- /FULL

inductive AevalR : Aexp → Nat → Prop where
  | E_ANum (n : Nat) :
      AevalR (.ANum n) n
  | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat)
      (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.APlus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : Aexp) (n1 n2 : Nat)
      (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.AMinus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : Aexp) (n1 n2 : Nat)
      (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.AMult a1 a2) (n1 * n2)

/-
  It will be convenient to have an infix notation for `AevalR`.  We'll
  write `e ==> n` to mean that arithmetic expression `e` evaluates to
  value `n`.  (We scope the notation to this namespace so it doesn't
  collide with other evaluation relations later.)
-/

scoped notation:55 e:56 " ==> " n:56 => AevalR e n

/-
  ######################################################################
  ## Inference Rule Notation
-/

-- FULL
/-
  In informal discussions, it is convenient to write the rules for
  `AevalR` and similar relations in the more readable graphical form of
  _inference rules_, where the premises above the line justify the
  conclusion below the line.  For example, the constructor `E_APlus`

  ```
      | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat) :
          AevalR a1 n1 →
          AevalR a2 n2 →
          AevalR (.APlus a1 a2) (n1 + n2)
  ```

  can be written like this as an inference rule:

  ```
                            e1 ==> n1
                            e2 ==> n2
                      --------------------          (E_APlus)
                      APlus e1 e2 ==> n1+n2
  ```

  There is nothing very deep going on here: a group of inference rules
  corresponds to a single inductive definition; each rule's name
  corresponds to a constructor name; above the line are the premises,
  below the line the conclusion; and metavariables like `e1` and `n1`
  are implicitly universally quantified.  The whole collection of rules
  defines `==>` as the smallest relation closed under them:

  ```
                          -----------                (E_ANum)
                          ANum n ==> n

                            e1 ==> n1
                            e2 ==> n2
                      --------------------           (E_APlus)
                      APlus e1 e2 ==> n1+n2

                            e1 ==> n1
                            e2 ==> n2
                     ---------------------           (E_AMinus)
                     AMinus e1 e2 ==> n1-n2

                            e1 ==> n1
                            e2 ==> n2
                      --------------------           (E_AMult)
                      AMult e1 e2 ==> n1*n2
  ```
-/
-- /FULL

-- QUIZ
/-
  Which rules are needed to prove the following?

  ```
  .AMult (.APlus (.ANum 3) (.ANum 1)) (.ANum 0) ==> 0
  ```

  (A) `E_ANum` and `E_APlus`
  (B) `E_ANum` only
  (C) `E_ANum` and `E_AMult`
  (D) `E_AMult` and `E_APlus`
  (E) `E_ANum`, `E_AMult`, and `E_APlus`
-/
-- /QUIZ

/-
  ######################################################################
  ## Equivalence of the Definitions
-/

/-
  It is straightforward to prove that the relational and functional
  definitions of evaluation agree.
-/

theorem aevalR_iff_aeval (a : Aexp) (n : Nat) :
    a ==> n ↔ aeval a = n := by
  constructor
  · intro h
    induction h with
    | E_ANum n => rfl
    | E_APlus a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [aeval]; rw [ih1, ih2]
    | E_AMinus a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [aeval]; rw [ih1, ih2]
    | E_AMult a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [aeval]; rw [ih1, ih2]
  · intro h
    subst h
    induction a with
    | ANum n => exact .E_ANum n
    | APlus a1 a2 ih1 ih2 => exact .E_APlus a1 a2 _ _ ih1 ih2
    | AMinus a1 a2 ih1 ih2 => exact .E_AMinus a1 a2 _ _ ih1 ih2
    | AMult a1 a2 ih1 ih2 => exact .E_AMult a1 a2 _ _ ih1 ih2

/-
  Again, we can make the proof quite a bit shorter using the combinators
  from the previous section.
-/

theorem aevalR_iff_aeval' (a : Aexp) (n : Nat) :
    a ==> n ↔ aeval a = n := by
  constructor
  · intro h; induction h <;> simp_all [aeval]
  · intro h; subst h; induction a <;> constructor <;> assumption

-- EX3 (bevalR)
/-
  Write a relation `BevalR` in the same style as `AevalR`, and prove that
  it is equivalent to `beval`.
-/

inductive BevalR : Bexp → Bool → Prop where
  -- SOLUTION
  | E_BTrue  : BevalR .BTrue true
  | E_BFalse : BevalR .BFalse false
  | E_BEq (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ==> n1) (h2 : a2 ==> n2) :
      BevalR (.BEq a1 a2) (n1 == n2)
  | E_BNeq (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ==> n1) (h2 : a2 ==> n2) :
      BevalR (.BNeq a1 a2) (n1 != n2)
  | E_BLe (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ==> n1) (h2 : a2 ==> n2) :
      BevalR (.BLe a1 a2) (decide (n1 ≤ n2))
  | E_BGt (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ==> n1) (h2 : a2 ==> n2) :
      BevalR (.BGt a1 a2) (decide (n1 > n2))
  | E_BNot (b : Bexp) (bv : Bool) (h : BevalR b bv) :
      BevalR (.BNot b) (!bv)
  | E_BAnd (b1 b2 : Bexp) (tv1 tv2 : Bool) (h1 : BevalR b1 tv1) (h2 : BevalR b2 tv2) :
      BevalR (.BAnd b1 b2) (tv1 && tv2)
  -- /SOLUTION

scoped notation:55 e:56 " ==>b " b:56 => BevalR e b

theorem bevalR_iff_beval (b : Bexp) (bv : Bool) :
    b ==>b bv ↔ beval b = bv := by
  -- ADMITTED
  constructor
  · intro h
    induction h with
    | E_BTrue => rfl
    | E_BFalse => rfl
    | E_BEq a1 a2 n1 n2 h1 h2 =>
        simp only [beval]; rw [(aevalR_iff_aeval a1 n1).mp h1, (aevalR_iff_aeval a2 n2).mp h2]
    | E_BNeq a1 a2 n1 n2 h1 h2 =>
        simp only [beval]; rw [(aevalR_iff_aeval a1 n1).mp h1, (aevalR_iff_aeval a2 n2).mp h2]
    | E_BLe a1 a2 n1 n2 h1 h2 =>
        simp only [beval]; rw [(aevalR_iff_aeval a1 n1).mp h1, (aevalR_iff_aeval a2 n2).mp h2]
    | E_BGt a1 a2 n1 n2 h1 h2 =>
        simp only [beval]; rw [(aevalR_iff_aeval a1 n1).mp h1, (aevalR_iff_aeval a2 n2).mp h2]
    | E_BNot b bv h ih => simp only [beval]; rw [ih]
    | E_BAnd b1 b2 tv1 tv2 h1 h2 ih1 ih2 => simp only [beval]; rw [ih1, ih2]
  · intro h
    subst h
    induction b with
    | BTrue  => exact .E_BTrue
    | BFalse => exact .E_BFalse
    | BEq a1 a2  => exact .E_BEq a1 a2 _ _ ((aevalR_iff_aeval a1 _).mpr rfl) ((aevalR_iff_aeval a2 _).mpr rfl)
    | BNeq a1 a2 => exact .E_BNeq a1 a2 _ _ ((aevalR_iff_aeval a1 _).mpr rfl) ((aevalR_iff_aeval a2 _).mpr rfl)
    | BLe a1 a2  => exact .E_BLe a1 a2 _ _ ((aevalR_iff_aeval a1 _).mpr rfl) ((aevalR_iff_aeval a2 _).mpr rfl)
    | BGt a1 a2  => exact .E_BGt a1 a2 _ _ ((aevalR_iff_aeval a1 _).mpr rfl) ((aevalR_iff_aeval a2 _).mpr rfl)
    | BNot b ih => exact .E_BNot b _ ih
    | BAnd b1 b2 ih1 ih2 => exact .E_BAnd b1 b2 _ _ ih1 ih2
  -- /ADMITTED
-- GRADE_THEOREM 3: bevalR_iff_beval
-- []

end AExp

/-
  ######################################################################
  ## Computational vs. Relational Definitions
-/

-- FULL
/-
  For the definitions of evaluation for arithmetic and boolean
  expressions, the choice of whether to use functional or relational
  definitions is mainly a matter of taste.  However, there are many
  situations where relational definitions work much better than
  functional ones.
-/
-- /FULL
-- TERSE: /- Sometimes relational definitions are the only reasonable option... -/

namespace AevalRDivision

/-
  For example, suppose that we wanted to extend the arithmetic operations
  with division:
-/

inductive Aexp where
  | ANum (n : Nat)
  | APlus (a1 a2 : Aexp)
  | AMinus (a1 a2 : Aexp)
  | AMult (a1 a2 : Aexp)
  | ADiv (a1 a2 : Aexp)             -- NEW

/-
  Extending the definition of `aeval` to handle this new operation would
  not be straightforward (what should we return as the result of
  `.ADiv (.ANum 5) (.ANum 0)`?).  But extending the relation is easy.
-/

inductive AevalR : Aexp → Nat → Prop where
  | E_ANum (n : Nat) : AevalR (.ANum n) n
  | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.APlus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.AMinus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.AMult a1 a2) (n1 * n2)
  | E_ADiv (a1 a2 : Aexp) (n1 n2 n3 : Nat)             -- NEW
      (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) (hpos : n2 > 0) (hdiv : n2 * n3 = n1) :
      AevalR (.ADiv a1 a2) n3

/-
  Notice that this evaluation relation corresponds to a _partial_
  function: there are some inputs for which it does not specify an output.
-/

end AevalRDivision

namespace AevalRExtended

-- TERSE: /- Another example: a _nondeterministic_ number generator: -/
/-
  Or suppose that we want to extend the arithmetic operations by a
  nondeterministic number generator `AAny` that, when evaluated, may
  yield any number.  (This is not the same as making a _probabilistic_
  choice among all numbers -- we only say which results are _possible_.)
-/

inductive Aexp where
  | AAny                            -- NEW
  | ANum (n : Nat)
  | APlus (a1 a2 : Aexp)
  | AMinus (a1 a2 : Aexp)
  | AMult (a1 a2 : Aexp)

/-
  Again, extending `aeval` would be tricky, since evaluation is now _not_
  a deterministic function from expressions to numbers; but extending the
  relation is no problem.
-/

inductive AevalR : Aexp → Nat → Prop where
  | E_Any (n : Nat) : AevalR .AAny n                   -- NEW
  | E_ANum (n : Nat) : AevalR (.ANum n) n
  | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.APlus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.AMinus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.AMult a1 a2) (n1 * n2)

end AevalRExtended

-- FULL
/-
  At this point you may be wondering: which of these styles should I use
  by default?

  Where the thing being defined is not easy to express as a function --
  or is genuinely _not_ a function -- there is no real choice.  When both
  styles are workable, relational definitions can be more elegant and
  easier to understand, and Lean generates useful inversion and induction
  principles from them.  On the other hand, functional definitions are
  automatically deterministic and total (for a relation we must _prove_
  these if we need them), and we can use Lean's computation mechanism to
  simplify them during proofs.

  In large developments it is common to give a definition in _both_
  styles plus a lemma that the two coincide, allowing later proofs to
  switch between points of view at will -- exactly what we did above.
-/
-- /FULL
-- TERSE: /- Functional: computation.  Relational: expressive.  Best: both, proved equivalent. -/

/-
  ######################################################################
  # Expressions With Variables
-/

-- FULL
/-
  Let's return to defining Imp.  The next thing we need to do is to
  enrich our arithmetic and boolean expressions with variables.  To keep
  things simple, we'll assume that all variables are global and that they
  only hold numbers.
-/
-- /FULL

/-
  ######################################################################
  ## States
-/

-- FULL
/-
  Since we'll want to look variables up to find out their current values,
  we'll use total maps from the `Maps` chapter.  A _machine state_ (or
  just _state_) represents the current values of all variables at some
  point in the execution of a program.

  For simplicity, we assume that the state is defined for _all_
  variables.  Because each variable stores a natural number, we represent
  the state as a total map from strings (variable names) to `Nat`, with
  `0` as the default value.
-/
-- /FULL

abbrev State := TotalMap String Nat

/-
  ######################################################################
  ## Syntax
-/

/-
  We can add variables to the arithmetic expressions we had before simply
  by including one more constructor.  (This is a fresh `Aexp`, replacing
  the variable-free one from the `AExp` namespace above.)
-/

inductive Aexp where
  | ANum (n : Nat)
  | AId (x : String)                -- NEW
  | APlus (a1 a2 : Aexp)
  | AMinus (a1 a2 : Aexp)
  | AMult (a1 a2 : Aexp)

/- The `Bexp` definition is unchanged, except that it now refers to the
   new `Aexp`. -/

inductive Bexp where
  | BTrue
  | BFalse
  | BEq (a1 a2 : Aexp)
  | BNeq (a1 a2 : Aexp)
  | BLe (a1 a2 : Aexp)
  | BGt (a1 a2 : Aexp)
  | BNot (b : Bexp)
  | BAnd (b1 b2 : Bexp)

/- Defining a few variable names as shorthands will make examples easier
   to read. -/

def W : String := "W"
def X : String := "X"
def Y : String := "Y"
def Z : String := "Z"

/-
  ######################################################################
  ## Notations
-/

-- Claude (port note): The Rocq chapter builds a custom `<{ ... }>` grammar
-- so that Imp programs can be written with concrete `+`, `:=`, `;`,
-- `if`/`while` syntax.  We take the lighter route used elsewhere in this
-- translation: two coercions let us drop the `AId`/`ANum` wrappers, and we
-- otherwise write programs with the ordinary constructors.

-- FULL
/-
  To make Imp programs easier to read and write, we introduce two
  implicit coercions.  In Lean, a `Coe` instance tells the elaborator how
  to turn a value of one type into another automatically:
   - `Coe String Aexp` lets us write a bare variable (a `String`) where an
     `Aexp` is expected; the string is implicitly wrapped with `AId`.
   - `OfNat Aexp n` lets us write a numeric literal where an `Aexp` is
     expected; it is implicitly wrapped with `ANum`.
-/
-- /FULL

instance : Coe String Aexp where
  coe := .AId

instance (n : Nat) : OfNat Aexp n where
  ofNat := .ANum n

/- With these, we can write `.APlus 3 (.AMult X 2)` instead of
   `.APlus (.ANum 3) (.AMult (.AId "X") (.ANum 2))`. -/

def example_aexp : Aexp := .APlus 3 (.AMult X 2)
def example_bexp : Bexp := .BAnd .BTrue (.BNot (.BLe X 4))

/-
  ######################################################################
  ## Evaluation
-/

-- FULL
/-
  The arithmetic and boolean evaluators must now be extended to handle
  variables, taking a state `st` as an extra argument.  A variable is
  looked up in the state with the map-indexing notation `st[x]` from the
  `Maps` chapter.
-/
-- /FULL

def aeval (st : State) (a : Aexp) : Nat :=
  match a with
  | .ANum n => n
  | .AId x => st[x]                  -- NEW
  | .APlus  a1 a2 => aeval st a1 + aeval st a2
  | .AMinus a1 a2 => aeval st a1 - aeval st a2
  | .AMult  a1 a2 => aeval st a1 * aeval st a2

def beval (st : State) (b : Bexp) : Bool :=
  match b with
  | .BTrue      => true
  | .BFalse     => false
  | .BEq a1 a2  => aeval st a1 == aeval st a2
  | .BNeq a1 a2 => aeval st a1 != aeval st a2
  | .BLe a1 a2  => decide (aeval st a1 ≤ aeval st a2)
  | .BGt a1 a2  => decide (aeval st a1 > aeval st a2)
  | .BNot b1    => !beval st b1
  | .BAnd b1 b2 => beval st b1 && beval st b2

/- We write the empty state (every variable `0`) as `∅`, and reuse the
   total-map update notation `x →ₜ v ; st` for states. -/

def empty_st : State := ∅

/- test_aexp1 -/
example : aeval (X →ₜ 5 ; empty_st) (.APlus 3 (.AMult X 2)) = 13 := by rfl

/- test_aexp2 -/
example : aeval (X →ₜ 5 ; Y →ₜ 4 ; empty_st) (.APlus Z (.AMult X Y)) = 20 := by rfl

/- test_bexp1 -/
example : beval (X →ₜ 5 ; empty_st) (.BAnd .BTrue (.BNot (.BLe X 4))) = true := by rfl

/-
  ######################################################################
  # Commands
-/

-- FULL
/-
  Now we are ready to define the syntax and behavior of Imp _commands_
  (or _statements_).  Informally, commands `c` are described by the
  following BNF grammar:

  ```
  c := skip
     | x := a
     | c ; c
     | if b then c else c end
     | while b do c end
  ```

  Here is the formal definition of the abstract syntax of commands.
-/
-- /FULL

inductive Com where
  | CSkip
  | CAsgn (x : String) (a : Aexp)
  | CSeq (c1 c2 : Com)
  | CIf (b : Bexp) (c1 c2 : Com)
  | CWhile (b : Bexp) (c : Com)

-- FULL
/-
  For example, here is the factorial function again, written as a formal
  definition.  When this command terminates, the variable `Y` will
  contain the factorial of the initial value of `X`.  (Compare this to
  the concrete Imp program at the very start of the chapter.)
-/
-- /FULL

def fact_in_lean : Com :=
  .CSeq (.CAsgn Z X)
  (.CSeq (.CAsgn Y 1)
  (.CWhile (.BNeq Z 0)
    (.CSeq (.CAsgn Y (.AMult Y Z))
           (.CAsgn Z (.AMinus Z 1)))))

/- A few more examples. -/

/- *** Assignment: -/
def plus2 : Com := .CAsgn X (.APlus X 2)
def XtimesYinZ : Com := .CAsgn Z (.AMult X Y)

/- *** Loops: -/
def subtract_slowly_body : Com :=
  .CSeq (.CAsgn Z (.AMinus Z 1))
        (.CAsgn X (.AMinus X 1))

def subtract_slowly : Com :=
  .CWhile (.BNeq X 0) subtract_slowly_body

def subtract_3_from_5_slowly : Com :=
  .CSeq (.CAsgn X 3)
  (.CSeq (.CAsgn Z 5)
    subtract_slowly)

/- *** An infinite loop: -/
def loop : Com := .CWhile .BTrue .CSkip

/-
  ######################################################################
  # Evaluating Commands
-/

-- FULL
/-
  Next we need to define what it means to evaluate an Imp command.  The
  fact that `while` loops don't necessarily terminate makes defining an
  evaluation function tricky.
-/
-- /FULL

/-
  ######################################################################
  ## Evaluation as a Function (Failed Attempt)
-/

/-
  Here's an attempt at defining an evaluation function for commands (with
  a bogus `while` case).
-/

def ceval_fun_no_while (st : State) (c : Com) : State :=
  match c with
  | .CSkip => st
  | .CAsgn x a => (x →ₜ aeval st a ; st)
  | .CSeq c1 c2 =>
      let st' := ceval_fun_no_while st c1
      ceval_fun_no_while st' c2
  | .CIf b c1 c2 =>
      if beval st b then ceval_fun_no_while st c1
      else ceval_fun_no_while st c2
  | .CWhile _ _ => st               -- bogus

-- FULL
/-
  In a more conventional functional language like OCaml or Haskell we
  could add the `while` case as follows:

  ```
  | .CWhile b c =>
      if beval st b then ceval_fun st (.CSeq c (.CWhile b c))
      else st
  ```

  Lean doesn't accept such a definition ("fail to show termination")
  because the function we want to define is not guaranteed to terminate.
  Indeed, it _doesn't_ always terminate: the full `ceval_fun` applied to
  the `loop` program above would run forever.  Since Lean aims to be not
  just a programming language but also a consistent logic, any
  potentially non-terminating function must be rejected.  Here is what
  would go wrong if Lean allowed non-terminating recursive functions:

  ```
  def loop_false (n : Nat) : False := loop_false n
  ```

  That is, propositions like `False` would become provable (`loop_false 0`
  would be a proof of `False`), a disaster for logical consistency.
-/
-- /FULL
-- TERSE: /- A nonterminating `def loop_false (n) : False := loop_false n` would make `False` provable, so Lean rejects it. -/

/-
  ######################################################################
  ## Evaluation as a Relation
-/

-- FULL
/-
  Here's a better way: define `ceval` as a _relation_ rather than a
  _function_ -- i.e., make its result a `Prop` rather than a `State`,
  similar to what we did for `AevalR` above.  This frees us from awkward
  workarounds and gives more flexibility: for nondeterministic languages,
  evaluation isn't even a function.

  We'll use the notation `st =[ c ]=> st'` for the relation, meaning that
  executing program `c` in the starting state `st` results in the ending
  state `st'`.  Here is an informal definition, as inference rules:

  ```
                        -----------------                  (E_Skip)
                        st =[ skip ]=> st

                        aeval st a = n
                --------------------------------           (E_Asgn)
                st =[ x := a ]=> (x →ₜ n ; st)

                        st  =[ c1 ]=> st'
                        st' =[ c2 ]=> st''
                      ---------------------                (E_Seq)
                      st =[ c1;c2 ]=> st''

                       beval st b = true
                        st =[ c1 ]=> st'
             --------------------------------------        (E_IfTrue)
             st =[ if b then c1 else c2 end ]=> st'

                      beval st b = false
                        st =[ c2 ]=> st'
             --------------------------------------        (E_IfFalse)
             st =[ if b then c1 else c2 end ]=> st'

                      beval st b = false
                 -----------------------------             (E_WhileFalse)
                 st =[ while b do c end ]=> st

                       beval st b = true
                        st =[ c ]=> st'
               st' =[ while b do c end ]=> st''
               --------------------------------            (E_WhileTrue)
               st  =[ while b do c end ]=> st''
  ```

  Here is the formal definition.  Make sure you understand how it
  corresponds to the inference rules.
-/
-- /FULL

inductive Ceval : Com → State → State → Prop where
  | E_Skip (st : State) :
      Ceval .CSkip st st
  | E_Asgn (st : State) (a : Aexp) (n : Nat) (x : String)
      (h : aeval st a = n) :
      Ceval (.CAsgn x a) st (x →ₜ n ; st)
  | E_Seq (c1 c2 : Com) (st st' st'' : State)
      (h1 : Ceval c1 st st') (h2 : Ceval c2 st' st'') :
      Ceval (.CSeq c1 c2) st st''
  | E_IfTrue (st st' : State) (b : Bexp) (c1 c2 : Com)
      (hb : beval st b = true) (hc : Ceval c1 st st') :
      Ceval (.CIf b c1 c2) st st'
  | E_IfFalse (st st' : State) (b : Bexp) (c1 c2 : Com)
      (hb : beval st b = false) (hc : Ceval c2 st st') :
      Ceval (.CIf b c1 c2) st st'
  | E_WhileFalse (b : Bexp) (st : State) (c : Com)
      (hb : beval st b = false) :
      Ceval (.CWhile b c) st st
  | E_WhileTrue (st st' st'' : State) (b : Bexp) (c : Com)
      (hb : beval st b = true) (hc : Ceval c st st')
      (hloop : Ceval (.CWhile b c) st' st'') :
      Ceval (.CWhile b c) st st''

notation:40 st0 " =[ " c " ]=> " st1 => Ceval c st0 st1

/-
  The cost of defining evaluation as a relation instead of a function is
  that we now need to construct a _proof_ that some program evaluates to
  some result state, rather than letting Lean's computation mechanism do
  it for us.
-/

example :
    empty_st =[ .CSeq (.CAsgn X 2)
                  (.CIf (.BLe X 1) (.CAsgn Y 3) (.CAsgn Z 4)) ]=>
      (Z →ₜ 4 ; X →ₜ 2 ; empty_st) := by
  -- We must supply the intermediate state.
  apply Ceval.E_Seq (st' := (X →ₜ 2 ; empty_st))
  · apply Ceval.E_Asgn; rfl
  · apply Ceval.E_IfFalse
    · rfl
    · apply Ceval.E_Asgn; rfl

-- EX2 (ceval_example2)
example :
    empty_st =[ .CSeq (.CAsgn X 0) (.CSeq (.CAsgn Y 1) (.CAsgn Z 2)) ]=>
      (Z →ₜ 2 ; Y →ₜ 1 ; X →ₜ 0 ; empty_st) := by
  -- ADMITTED
  apply Ceval.E_Seq (st' := (X →ₜ 0 ; empty_st))
  · apply Ceval.E_Asgn; rfl
  · apply Ceval.E_Seq (st' := (Y →ₜ 1 ; X →ₜ 0 ; empty_st))
    · apply Ceval.E_Asgn; rfl
    · apply Ceval.E_Asgn; rfl
  -- /ADMITTED
-- []

/-
  ######################################################################
  ## Determinism of Evaluation
-/

-- FULL
/-
  Changing from a computational to a relational definition of evaluation
  is a good move because it frees us from the artificial requirement that
  evaluation be a total function.  But it raises a question: is the
  relational definition really a partial _function_?  Could the same
  command, from the same state, evaluate to two different final states?
  In fact this cannot happen: `ceval` _is_ a partial function.
-/
-- /FULL

theorem ceval_deterministic (c : Com) (st st1 st2 : State)
    (e1 : st =[ c ]=> st1) (e2 : st =[ c ]=> st2) : st1 = st2 := by
  induction e1 generalizing st2 with
  | E_Skip st =>
      cases e2 with
      | E_Skip => rfl
  | E_Asgn st a n x h =>
      cases e2 with
      | E_Asgn _ _ n' _ h' => subst h; subst h'; rfl
  | E_Seq c1 c2 st st' st'' h1 h2 ih1 ih2 =>
      cases e2 with
      | E_Seq _ _ _ st2' _ h1' h2' =>
          have hst : st' = st2' := ih1 _ h1'
          subst hst
          exact ih2 _ h2'
  | E_IfTrue st st' b c1 c2 hb hc ih =>
      cases e2 with
      | E_IfTrue _ _ _ _ _ hb' hc' => exact ih _ hc'
      | E_IfFalse _ _ _ _ _ hb' hc' => simp_all
  | E_IfFalse st st' b c1 c2 hb hc ih =>
      cases e2 with
      | E_IfTrue _ _ _ _ _ hb' hc' => simp_all
      | E_IfFalse _ _ _ _ _ hb' hc' => exact ih _ hc'
  | E_WhileFalse b st c hb =>
      cases e2 with
      | E_WhileFalse _ _ _ hb' => rfl
      | E_WhileTrue _ _ _ _ _ hb' hc' hl' => simp_all
  | E_WhileTrue st st' st'' b c hb hc hloop ih1 ih2 =>
      cases e2 with
      | E_WhileFalse _ _ _ hb' => simp_all
      | E_WhileTrue _ st2' _ _ _ hb' hc' hl' =>
          have hst : st' = st2' := ih1 _ hc'
          subst hst
          exact ih2 _ hl'

-- EX3 (pup_to_n)
/-
  Write an Imp program that sums the numbers from `1` to `X` (inclusive)
  in the variable `Y`.  Your program should update the state as shown in
  `pup_to_2_ceval`, which you can reverse-engineer to discover the program
  you should write.  The proof of that theorem will be somewhat lengthy.
-/

def pup_to_n : Com :=
  -- ADMITDEF
  .CSeq (.CAsgn Y 0)
    (.CWhile (.BLe 1 X)
      (.CSeq (.CAsgn Y (.APlus Y X))
             (.CAsgn X (.AMinus X 1))))
  -- /ADMITDEF

theorem pup_to_2_ceval :
    (X →ₜ 2 ; empty_st) =[ pup_to_n ]=>
      (X →ₜ 0 ; Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; empty_st) := by
  -- ADMITTED
  unfold pup_to_n
  apply Ceval.E_Seq (st' := (Y →ₜ 0 ; X →ₜ 2 ; empty_st))
  · apply Ceval.E_Asgn; rfl
  · apply Ceval.E_WhileTrue (st' := (X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; empty_st))
    · rfl
    · apply Ceval.E_Seq (st' := (Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; empty_st)) <;>
        (apply Ceval.E_Asgn; rfl)
    · apply Ceval.E_WhileTrue
        (st' := (X →ₜ 0 ; Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; empty_st))
      · rfl
      · apply Ceval.E_Seq (st' := (Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; empty_st)) <;>
          (apply Ceval.E_Asgn; rfl)
      · apply Ceval.E_WhileFalse; rfl
  -- /ADMITTED
-- []

/-
  ######################################################################
  # Reasoning About Imp Programs
-/

-- FULL
/-
  We'll get into more systematic and powerful techniques for reasoning
  about Imp programs in later chapters, but we can already do a few things
  (albeit in a somewhat low-level way) just by working with the bare
  definitions.  This section explores some examples.
-/
-- /FULL

theorem plus2_spec (st : State) (n : Nat) (st' : State)
    (hx : st[X] = n) (heval : st =[ plus2 ]=> st') :
    st'[X] = n + 2 := by
  -- Inverting `heval` forces one step of the `ceval` computation: since
  -- `plus2` is an assignment, `st'` must be `st` extended at `X`.
  unfold plus2 at heval
  cases heval with
  | E_Asgn _ _ m _ h =>
      simp only [aeval] at h
      rw [TotalMap.update_eq]
      omega

-- EX3 (XtimesYinZ_spec)
/- State and prove a specification of `XtimesYinZ`. -/

theorem XtimesYinZ_spec (st : State) :
    st =[ XtimesYinZ ]=> (Z →ₜ st[X] * st[Y] ; st) := by
  -- SOLUTION
  unfold XtimesYinZ
  apply Ceval.E_Asgn
  rfl
  -- /SOLUTION
-- GRADE_MANUAL 3: XtimesYinZ_spec
-- []

-- EX3! (loop_never_stops)
theorem loop_never_stops (st st' : State) : ¬ (st =[ loop ]=> st') := by
  -- ADMITTED
  intro contra
  -- Generalize over the command so the induction remembers what `loop` is.
  have key : ∀ (c : Com) (s s' : State), (s =[ c ]=> s') → c = loop → False := by
    intro c s s' hce
    induction hce with
    | E_WhileFalse b s0 c0 hb =>
        intro heq; unfold loop at heq; injection heq with e1 _
        subst e1; simp [beval] at hb
    | E_WhileTrue s0 s0' s0'' b c0 hb hc hloop ih1 ih2 =>
        intro heq; exact ih2 heq
    | E_Skip s0 => intro heq; simp [loop] at heq
    | E_Asgn s0 a n x h => intro heq; simp [loop] at heq
    | E_Seq c1 c2 s0 s0' s0'' h1 h2 ih1 ih2 => intro heq; simp [loop] at heq
    | E_IfTrue s0 s0' b c1 c2 hb hc ih => intro heq; simp [loop] at heq
    | E_IfFalse s0 s0' b c1 c2 hb hc ih => intro heq; simp [loop] at heq
  exact key loop st st' contra rfl
  -- /ADMITTED
-- []

-- EX3 (no_whiles_eqv)
/-
  The following function yields `true` just on programs with no while
  loops.  Using `inductive`, write a property `NoWhilesR` that holds
  exactly when `c` is while-free, then prove it equivalent to `no_whiles`.
-/

def no_whiles (c : Com) : Bool :=
  match c with
  | .CSkip      => true
  | .CAsgn _ _  => true
  | .CSeq c1 c2 => no_whiles c1 && no_whiles c2
  | .CIf _ ct cf => no_whiles ct && no_whiles cf
  | .CWhile _ _ => false

inductive NoWhilesR : Com → Prop where
  -- SOLUTION
  | nw_Skip : NoWhilesR .CSkip
  | nw_Asgn (x : String) (a : Aexp) : NoWhilesR (.CAsgn x a)
  | nw_Seq (c1 c2 : Com) (h1 : NoWhilesR c1) (h2 : NoWhilesR c2) :
      NoWhilesR (.CSeq c1 c2)
  | nw_If (b : Bexp) (c1 c2 : Com) (h1 : NoWhilesR c1) (h2 : NoWhilesR c2) :
      NoWhilesR (.CIf b c1 c2)
  -- /SOLUTION

theorem no_whiles_eqv (c : Com) : no_whiles c = true ↔ NoWhilesR c := by
  -- ADMITTED
  constructor
  · induction c with
    | CSkip => intro _; exact .nw_Skip
    | CAsgn x a => intro _; exact .nw_Asgn x a
    | CSeq c1 c2 ih1 ih2 =>
        intro h; simp only [no_whiles, Bool.and_eq_true] at h
        exact .nw_Seq _ _ (ih1 h.1) (ih2 h.2)
    | CIf b c1 c2 ih1 ih2 =>
        intro h; simp only [no_whiles, Bool.and_eq_true] at h
        exact .nw_If _ _ _ (ih1 h.1) (ih2 h.2)
    | CWhile b c ih => intro h; simp [no_whiles] at h
  · intro h
    induction h with
    | nw_Skip => rfl
    | nw_Asgn x a => rfl
    | nw_Seq c1 c2 h1 h2 ih1 ih2 => simp [no_whiles, ih1, ih2]
    | nw_If b c1 c2 h1 h2 ih1 ih2 => simp [no_whiles, ih1, ih2]
  -- /ADMITTED
-- []

-- EX4 (no_whiles_terminating)
/-
  Imp programs that don't involve while loops always terminate.  State and
  prove a theorem `no_whiles_terminating` that says this.  Use either
  `no_whiles` or `NoWhilesR`, as you prefer.
-/

theorem no_whiles_terminating (c : Com) (st : State) (h : NoWhilesR c) :
    ∃ st', st =[ c ]=> st' := by
  -- SOLUTION
  induction h generalizing st with
  | nw_Skip => exact ⟨st, .E_Skip st⟩
  | nw_Asgn x a => exact ⟨(x →ₜ aeval st a ; st), .E_Asgn st a (aeval st a) x rfl⟩
  | nw_Seq c1 c2 h1 h2 ih1 ih2 =>
      obtain ⟨st', hc1⟩ := ih1 st
      obtain ⟨st'', hc2⟩ := ih2 st'
      exact ⟨st'', .E_Seq c1 c2 st st' st'' hc1 hc2⟩
  | nw_If b c1 c2 h1 h2 ih1 ih2 =>
      cases hb : beval st b with
      | true =>
          obtain ⟨st', hc1⟩ := ih1 st
          exact ⟨st', .E_IfTrue st st' b c1 c2 hb hc1⟩
      | false =>
          obtain ⟨st', hc2⟩ := ih2 st
          exact ⟨st', .E_IfFalse st st' b c1 c2 hb hc2⟩
  -- /SOLUTION
-- []

/-
  Claude: PORT STATUS — this chapter is a work in progress.

  DONE (compiling; survives to_verso → HL.ImpVerso builds):
    - AExp module: Aexp/Bexp syntax, aeval/beval, optimize_0plus + soundness
    - Tactic combinators (try, <;>, repeat, macro), omega, handy-tactics recap
    - optimize_0plus_b (EX3)
    - Evaluation as a Relation: AevalR + `==>`, inference rules,
      aevalR_iff_aeval (x2), BevalR (EX3) + bevalR_iff_beval,
      AevalRDivision / AevalRExtended, tradeoffs
    - Expressions With Variables: State, coercions, aeval/beval, Com + examples
    - Evaluating Commands: ceval_fun_no_while, Ceval + `=[ c ]=>`, examples,
      ceval_deterministic
    - Reasoning About Imp Programs: pup_to_n/pup_to_2_ceval, plus2_spec,
      XtimesYinZ_spec (EX3), loop_never_stops (EX3!), no_whiles/NoWhilesR +
      no_whiles_eqv (EX3), no_whiles_terminating (EX4)

  NOT DONE YET — remaining sections of sfdev/lf/Imp.v to port:
    - Case Study (Optional), Imp.v:2774
        * subtract_slowly_spec (EX4?, Imp.v:2919): loop-invariant style proof
          about `subtract_slowly`.
    - Additional Exercises, Imp.v:2986
        * stack_compiler (EX3, Imp.v:2988): define `s_execute` (stack machine)
          and `s_compile : aexp -> list sinstr`; needs a `SInstr` inductive
          (SPush/SLoad/SPlus/SMinus/SMult) and a list-based stack.
        * execute_app (EX3, Imp.v:3114)
        * stack_compiler_correct (EX3, Imp.v:3134): the correctness theorem;
          the standard proof needs a strengthened lemma over an arbitrary
          initial stack (generalize the stack before inducting).
        * short_circuit (EX3?, Imp.v:3184): short-circuiting `beval`.
        * break_imp (EX4?, Imp.v:3227): extends Com with `CBreak`; new
          relational semantics `ceval` carrying a `result` (SContinue/SBreak).
          Large. See verso-book branch (lf/Imp.lean ~line 1141, CEvalBreak) for
          a prior take on the signal type.
        * while_break_true (EX3A?, Imp.v:3454)
        * ceval_deterministic for break (EX4A?, Imp.v:3477)
        * exn_imp (EX4A?, Imp.v:3524): exceptions variant. Large.
        * add_for_loop (EX4?, Imp.v:3728): add a C-style `for` loop to Com,
          its notation, and extend ceval.

  When resuming: keep the established conventions (dot-notation constructors,
  `→ₜ`/`st[x]` state ops, no `<{ }>` grammar, `-- EXn`/`-- SOLUTION`/`-- ADMITTED`
  /`-- GRADE_*` markers, ``` fences for display blocks), and after each chunk
  run `make check-verso-chapters` so the to_verso round-trip stays green.
-/
