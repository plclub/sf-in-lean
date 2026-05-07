-- Imp: Simple Imperative Programs

-- INSTRUCTORS: This chapter plus Maps takes a little more than one
--    80-minute lecture.  It could be streamlined a bit further without
--    losing much, by removing (for example) the inference rules and BNF
--    notations from the terse version.

-- HIDEFROMADVANCED

-- We concentrate here on defining the _syntax_ and _semantics_ of
-- Imp; later, in _Programming Language Foundations_ (_Software
-- Foundations_, volume 2), we develop a theory of _program
-- equivalence_ and introduce _Hoare Logic_, a popular logic for
-- reasoning about imperative programs.

-- /HIDEFROMADVANCED
-- TERSE: HIDEFROMHTML
import LF.Maps
-- TERSE: /HIDEFROMHTML

-- #######################################################
-- * Arithmetic and Boolean Expressions

-- We'll present Imp in three parts: first a core language of
-- _arithmetic and boolean expressions_, then an extension of these
-- with _variables_, and finally a language of _commands_ including
-- assignment, conditionals, sequencing, and loops.

-- #######################################################
-- ** Syntax

-- TERSE: HIDEFROMHTML
section SimpleAExp

-- TERSE: /HIDEFROMHTML
-- FULL: These two definitions specify the _abstract syntax_ of
-- arithmetic and boolean expressions.
-- TERSE: _Abstract syntax trees_ for arithmetic and boolean expressions:

inductive SAExp : Type where
  | ANum (n : Nat)
  | APlus (a1 a2 : SAExp)
  | AMinus (a1 a2 : SAExp)
  | AMult (a1 a2 : SAExp)

inductive SBExp : Type where
  | BTrue
  | BFalse
  | BEq (a1 a2 : SAExp)
  | BNeq (a1 a2 : SAExp)
  | BLe (a1 a2 : SAExp)
  | BGt (a1 a2 : SAExp)
  | BNot (b : SBExp)
  | BAnd (b1 b2 : SBExp)

open SAExp SBExp

-- FULL: In this chapter, we'll mostly elide the translation from the
-- concrete syntax that a programmer would actually write to these
-- abstract syntax trees -- the process that, for example, would
-- translate the string "1 + 2 * 3" to the AST
--
--       APlus (ANum 1) (AMult (ANum 2) (ANum 3))

-- FULL
-- For comparison, here's a conventional BNF (Backus-Naur Form)
-- grammar defining the same abstract syntax:
--
--     a := nat
--         | a + a
--         | a - a
--         | a * a
--
--     b := true
--         | false
--         | a = a
--         | a <> a
--         | a <= a
--         | a > a
--         | ~ b
--         | b && b
-- /FULL

-- #######################################################
-- ** Evaluation

-- _Evaluating_ an arithmetic expression produces a number.

def saeval (a : SAExp) : Nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (saeval a1) + (saeval a2)
  | AMinus a1 a2 => (saeval a1) - (saeval a2)
  | AMult a1 a2 => (saeval a1) * (saeval a2)

-- test_aeval1
example : saeval (APlus (ANum 2) (ANum 2)) = 4 := by rfl

-- Similarly, evaluating a boolean expression yields a boolean.

def sbeval (b : SBExp) : Bool :=
  match b with
  | SBExp.BTrue => true
  | SBExp.BFalse => false
  | SBExp.BEq a1 a2 => (saeval a1) == (saeval a2)
  | SBExp.BNeq a1 a2 => !(saeval a1 == saeval a2)
  | SBExp.BLe a1 a2 => Nat.ble (saeval a1) (saeval a2)
  | SBExp.BGt a1 a2 => !(Nat.ble (saeval a1) (saeval a2))
  | SBExp.BNot b1 => !(sbeval b1)
  | SBExp.BAnd b1 b2 => sbeval b1 && sbeval b2

-- #######################################################
-- ** Optimization

-- FULL: We haven't defined very much yet, but we can already get some
-- mileage out of the definitions.  Suppose we define a function that
-- takes an arithmetic expression and slightly simplifies it, changing
-- every occurrence of `0 + e` (i.e., `APlus (ANum 0) e`) into just
-- `e`.

def optimize_0plus (a : SAExp) : SAExp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)

-- HIDEFROMADVANCED

-- test_optimize_0plus
example :
    optimize_0plus (APlus (ANum 2)
                          (APlus (ANum 0)
                                 (APlus (ANum 0) (ANum 1))))
    = APlus (ANum 2) (ANum 1) := by rfl

-- /HIDEFROMADVANCED

-- FULL: But if we want to be certain the optimization is correct --
-- that evaluating an optimized expression _always_ gives the same
-- result as the original -- we should prove it!

theorem optimize_0plus_sound (a : SAExp) :
    saeval (optimize_0plus a) = saeval a := by
  induction a with
  | ANum n => rfl
  | APlus a1 a2 ih1 ih2 =>
    cases a1 with
    | ANum n =>
      cases n with
      | zero => simp [optimize_0plus, saeval, ih2]
      | succ n' => simp [optimize_0plus, saeval, ih2]
    | APlus a1_1 a1_2 =>
      simp only [optimize_0plus, saeval] at ih1 ⊢; rw [ih1, ih2]
    | AMinus a1_1 a1_2 =>
      simp only [optimize_0plus, saeval] at ih1 ⊢; rw [ih1, ih2]
    | AMult a1_1 a1_2 =>
      simp only [optimize_0plus, saeval] at ih1 ⊢; rw [ih1, ih2]
  | AMinus a1 a2 ih1 ih2 =>
    simp only [optimize_0plus, saeval]; rw [ih1, ih2]
  | AMult a1 a2 ih1 ih2 =>
    simp only [optimize_0plus, saeval]; rw [ih1, ih2]

-- #######################################################
-- * Lean Automation

-- FULL: The amount of repetition in this last proof is a little
-- annoying.  Lean provides various automation facilities to help.
-- We've already seen `simp`, `omega`, and `decide` in earlier
-- chapters.  Here we just note that the `simp` tactic with the
-- right lemmas can dispatch many goals automatically.

-- #######################################################
-- ** Tacticals

-- _Tacticals_ is a term for tactics that take other tactics as
-- arguments -- "higher-order tactics," if you will.

-- #######################################################
-- *** The `try` combinator

-- In Lean's tactic mode, `try tac` runs `tac` and, if it fails,
-- does nothing (rather than failing).

theorem silly1' (P : Prop) (hp : P) : P := by
  try rfl  -- rfl would fail here, but `try` catches the failure
  exact hp

-- HIDEFROMADVANCED
theorem silly2' (ae : SAExp) : saeval ae = saeval ae := by
  try rfl  -- This just does `rfl`.
-- /HIDEFROMADVANCED

-- #######################################################
-- *** The `<;>` combinator

-- In Lean, `tac1 <;> tac2` applies `tac2` to every goal generated
-- by `tac1`.

-- For example:

theorem foo' (n : Nat) : (Nat.ble 0 n) = true := by
  cases n <;> simp [Nat.ble]

-- Using automation, we can make the optimize_0plus_sound proof shorter:

theorem optimize_0plus_sound' (a : SAExp) :
    saeval (optimize_0plus a) = saeval a := by
  induction a with
  | ANum _ => rfl
  | APlus a1 a2 ih1 ih2 =>
    cases a1 with
    | ANum n =>
      cases n with
      | zero => simp [optimize_0plus, saeval, ih2]
      | succ _ => simp [optimize_0plus, saeval, ih2]
    | APlus _ _ =>
      simp only [optimize_0plus, saeval] at ih1 ⊢; rw [ih1, ih2]
    | AMinus _ _ =>
      simp only [optimize_0plus, saeval] at ih1 ⊢; rw [ih1, ih2]
    | AMult _ _ =>
      simp only [optimize_0plus, saeval] at ih1 ⊢; rw [ih1, ih2]
  | AMinus a1 a2 ih1 ih2 => simp [optimize_0plus, saeval, ih1, ih2]
  | AMult a1 a2 ih1 ih2 => simp [optimize_0plus, saeval, ih1, ih2]

-- EX3 (optimize_0plus_b_sound)
-- Since the `optimize_0plus` transformation doesn't change the value
-- of `SAExp`s, we should be able to apply it to all the `SAExp`s that
-- appear in a `SBExp` without changing the `SBExp`'s value.  Write a
-- function that performs this transformation on `SBExp`s and prove
-- it is sound.  Use automation to make the proof as short and elegant
-- as possible.

-- ADMITDEF
def optimize_0plus_b (b : SBExp) : SBExp :=
  match b with
  | SBExp.BTrue => SBExp.BTrue
  | SBExp.BFalse => SBExp.BFalse
  | SBExp.BEq a1 a2 => SBExp.BEq (optimize_0plus a1) (optimize_0plus a2)
  | SBExp.BNeq a1 a2 => SBExp.BNeq (optimize_0plus a1) (optimize_0plus a2)
  | SBExp.BLe a1 a2 => SBExp.BLe (optimize_0plus a1) (optimize_0plus a2)
  | SBExp.BGt a1 a2 => SBExp.BGt (optimize_0plus a1) (optimize_0plus a2)
  | SBExp.BNot b1 => SBExp.BNot (optimize_0plus_b b1)
  | SBExp.BAnd b1 b2 => SBExp.BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
-- /ADMITDEF

-- optimize_0plus_b_test1
example :
    optimize_0plus_b (SBExp.BNot (SBExp.BGt (APlus (ANum 0) (ANum 4)) (ANum 8))) =
                     (SBExp.BNot (SBExp.BGt (ANum 4) (ANum 8))) := by
  -- ADMITTED
  rfl
  -- /ADMITTED

-- optimize_0plus_b_test2
example :
    optimize_0plus_b (SBExp.BAnd (SBExp.BLe (APlus (ANum 0) (ANum 4)) (ANum 5)) SBExp.BTrue) =
                     (SBExp.BAnd (SBExp.BLe (ANum 4) (ANum 5)) SBExp.BTrue) := by
  -- ADMITTED
  rfl
  -- /ADMITTED

theorem optimize_0plus_b_sound (b : SBExp) :
    sbeval (optimize_0plus_b b) = sbeval b := by
  -- ADMITTED
  induction b with
  | BTrue => rfl
  | BFalse => rfl
  | BEq a1 a2 => simp [optimize_0plus_b, sbeval, optimize_0plus_sound]
  | BNeq a1 a2 => simp [optimize_0plus_b, sbeval, optimize_0plus_sound]
  | BLe a1 a2 => simp [optimize_0plus_b, sbeval, optimize_0plus_sound]
  | BGt a1 a2 => simp [optimize_0plus_b, sbeval, optimize_0plus_sound]
  | BNot b1 ih => simp [optimize_0plus_b, sbeval, ih]
  | BAnd b1 b2 ih1 ih2 => simp [optimize_0plus_b, sbeval, ih1, ih2]
  -- /ADMITTED
-- GRADE_THEOREM 0.5: optimize_0plus_b_test1
-- GRADE_THEOREM 0.5: optimize_0plus_b_test2
-- GRADE_THEOREM 2: optimize_0plus_b_sound

-- #######################################################
-- ** The `omega` Tactic

-- The `omega` tactic in Lean implements a decision procedure for
-- linear arithmetic over natural numbers and integers.

-- silly_presburger_example
example (m n o p : Nat)
    (h : m + n <= n + o /\ o + 3 = p + 3) :
    m <= p := by
  omega

-- add_comm__omega
example (m n : Nat) : m + n = n + m := by
  omega

-- add_assoc__omega
example (m n p : Nat) : m + (n + p) = m + n + p := by
  omega

-- #######################################################
-- * Evaluation as a Relation

-- We have presented `saeval` and `sbeval` as functions defined by
-- pattern matching.  Another way to think about evaluation -- one
-- that is often more flexible -- is as a _relation_ between
-- expressions and their values.

inductive SAEvalR : SAExp → Nat → Prop where
  | E_ANum (n : Nat) :
      SAEvalR (ANum n) n
  | E_APlus (e1 e2 : SAExp) (n1 n2 : Nat) :
      SAEvalR e1 n1 →
      SAEvalR e2 n2 →
      SAEvalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : SAExp) (n1 n2 : Nat) :
      SAEvalR e1 n1 →
      SAEvalR e2 n2 →
      SAEvalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : SAExp) (n1 n2 : Nat) :
      SAEvalR e1 n1 →
      SAEvalR e2 n2 →
      SAEvalR (AMult e1 e2) (n1 * n2)

-- We'll write `e ==> n` to mean that arithmetic expression `e`
-- evaluates to value `n`.

local infix:90 " s==> " => SAEvalR

-- #######################################################
-- ** Equivalence of the Definitions

-- It is straightforward to prove that the relational and functional
-- definitions of evaluation agree.

theorem saevalR_iff_saeval (a : SAExp) (n : Nat) :
    (a s==> n) ↔ saeval a = n := by
  constructor
  · intro h
    induction h with
    | E_ANum _ => rfl
    | E_APlus _ _ _ _ _ _ ih1 ih2 => simp [saeval, ih1, ih2]
    | E_AMinus _ _ _ _ _ _ ih1 ih2 => simp [saeval, ih1, ih2]
    | E_AMult _ _ _ _ _ _ ih1 ih2 => simp [saeval, ih1, ih2]
  · revert n
    induction a with
    | ANum n => intro n h; simp [saeval] at h; subst h; exact SAEvalR.E_ANum n
    | APlus a1 a2 ih1 ih2 =>
      intro n h; simp [saeval] at h; subst h
      exact SAEvalR.E_APlus a1 a2 _ _ (ih1 _ rfl) (ih2 _ rfl)
    | AMinus a1 a2 ih1 ih2 =>
      intro n h; simp [saeval] at h; subst h
      exact SAEvalR.E_AMinus a1 a2 _ _ (ih1 _ rfl) (ih2 _ rfl)
    | AMult a1 a2 ih1 ih2 =>
      intro n h; simp [saeval] at h; subst h
      exact SAEvalR.E_AMult a1 a2 _ _ (ih1 _ rfl) (ih2 _ rfl)

-- TERSE: HIDEFROMHTML
end SimpleAExp
-- TERSE: /HIDEFROMHTML

-- #######################################################
-- ** Computational vs. Relational Definitions

-- FULL: For the definitions of evaluation for arithmetic and boolean
-- expressions, the choice of whether to use functional or relational
-- definitions is mainly a matter of taste: either way works fine.
--
-- However, there are many situations where relational definitions of
-- evaluation work much better than functional ones.

-- For example, suppose that we wanted to extend the arithmetic
-- operations with division.  Extending `aeval` to handle this new
-- operation would not be straightforward (what should we return as
-- the result of `ADiv (ANum 5) (ANum 0)`?).  But extending `aevalR`
-- is very easy -- we just add a rule with a side condition requiring
-- the divisor to be nonzero.

-- Similarly, if we want to extend the arithmetic operations by a
-- nondeterministic number generator, relational definitions handle
-- this naturally while functional definitions cannot.

-- #######################################################
-- * Expressions With Variables

-- Let's return to defining Imp, where the next thing we need to do
-- is to enrich our arithmetic and boolean expressions with variables.
--
-- To keep things simple, we'll assume that all variables are global
-- and that they only hold numbers.

-- #######################################################
-- ** States

-- A _machine state_ (or just _state_) represents the current values
-- of all variables at some point in the execution of a program.

-- FULL: For simplicity, we assume that the state is defined for
-- _all_ variables, even though any given program is only able to
-- mention a finite number of them.  Because each variable stores a
-- natural number, we can represent the state as a total map from
-- strings (variable names) to `Nat`, and will use `0` as default
-- value in the store.

def State := TotalMap Nat

-- ###################################################
-- ** Syntax

-- We can add variables to the arithmetic expressions we had before
-- simply by including one more constructor:

inductive AExp : Type where
  | ANum (n : Nat)
  | AId (x : String)             -- <--- NEW
  | APlus (a1 a2 : AExp)
  | AMinus (a1 a2 : AExp)
  | AMult (a1 a2 : AExp)

-- Defining a few variable names as notational shorthands will make
-- examples easier to read:

def W : String := "W"
def X : String := "X"
def Y : String := "Y"
def Z : String := "Z"

-- The definition of `BExp` is unchanged (except that it now refers
-- to the new `AExp`):

inductive BExp : Type where
  | BTrue
  | BFalse
  | BEqA (a1 a2 : AExp)
  | BNeq (a1 a2 : AExp)
  | BLe (a1 a2 : AExp)
  | BGt (a1 a2 : AExp)
  | BNot (b : BExp)
  | BAnd (b1 b2 : BExp)

open AExp BExp

-- ** Notations

-- To make Imp programs easier to read and write, we introduce some
-- coercions. In Lean, we can use instance declarations to
-- automatically coerce `Nat` to `AExp` and `String` to `AExp`.

instance {n : Nat} : OfNat AExp n where
  ofNat := ANum n

instance : Coe String AExp where
  coe := AId

-- ###################################################
-- ** Evaluation

-- FULL: The arith and boolean evaluators must now be extended to
-- handle variables in the obvious way, taking a state `st` as an
-- extra argument.

def aeval (st : State) (a : AExp) : Nat :=
  match a with
  | ANum n => n
  | AId x => st x                     -- <--- NEW
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)

def beval (st : State) (b : BExp) : Bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEqA a1 a2 => (aeval st a1) == (aeval st a2)
  | BNeq a1 a2 => !(aeval st a1 == aeval st a2)
  | BLe a1 a2 => Nat.ble (aeval st a1) (aeval st a2)
  | BGt a1 a2 => !(Nat.ble (aeval st a1) (aeval st a2))
  | BNot b1 => !(beval st b1)
  | BAnd b1 b2 => beval st b1 && beval st b2

-- We can use our notation for total maps in the specific case of
-- states -- i.e., we write the empty state as `tEmpty 0`.

def empty_st : State := tEmpty 0

-- Also, we can add a notation for a "singleton state" with just one
-- variable bound to a value.
notation:100 x " !-> " v => (x !-> v ; empty_st)

-- FULL
-- aexp1
example :
    aeval (X !-> 5) (APlus (ANum 3) (AMult (AId X) (ANum 2)))
    = 13 := by rfl

-- aexp2
example :
    aeval (X !-> 5 ; Y !-> 4 ; empty_st)
      (APlus (AId Z) (AMult (AId X) (AId Y)))
    = 20 := by rfl

-- bexp1
example :
    beval (X !-> 5) (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
    = true := by rfl
-- /FULL

-- #######################################################
-- * Commands

-- Now we are ready to define the syntax and behavior of Imp
-- _commands_ (or _statements_).

-- ###################################################
-- ** Syntax

-- HIDEFROMADVANCED
-- Informally, commands `c` are described by the following BNF grammar.
--
--      c := skip
--         | x := a
--         | c ; c
--         | if b then c else c end
--         | while b do c end

-- Here is the formal definition of the abstract syntax of commands:

-- /HIDEFROMADVANCED

inductive Com : Type where
  | CSkip
  | CAsgn (x : String) (a : AExp)
  | CSeq (c1 c2 : Com)
  | CIf (b : BExp) (c1 c2 : Com)
  | CWhile (b : BExp) (c : Com)

open Com

-- For example, here is the factorial function written as a formal
-- definition.  When this command terminates, the variable `Y` will
-- contain the factorial of the initial value of `X`.

def fact_in_lean : Com :=
  CSeq (CAsgn Z (AId X))
  (CSeq (CAsgn Y (ANum 1))
  (CWhile (BNeq (AId Z) (ANum 0))
    (CSeq (CAsgn Y (AMult (AId Y) (AId Z)))
          (CAsgn Z (AMinus (AId Z) (ANum 1))))))

-- HIDEFROMADVANCED

-- ** More Examples

-- *** Assignment:

def plus2 : Com :=
  CAsgn X (APlus (AId X) (ANum 2))

def XtimesYinZ : Com :=
  CAsgn Z (AMult (AId X) (AId Y))

-- *** Loops

def subtract_slowly_body : Com :=
  CSeq (CAsgn Z (AMinus (AId Z) (ANum 1)))
       (CAsgn X (AMinus (AId X) (ANum 1)))

def subtract_slowly : Com :=
  CWhile (BNeq (AId X) (ANum 0))
    subtract_slowly_body

def subtract_3_from_5_slowly : Com :=
  CSeq (CAsgn X (ANum 3))
  (CSeq (CAsgn Z (ANum 5))
    subtract_slowly)

-- *** An infinite loop:

def loop : Com :=
  CWhile BTrue CSkip

-- /HIDEFROMADVANCED

-- ################################################################
-- * Evaluating Commands

-- Next we need to define what it means to evaluate an Imp command.
-- The fact that `while` loops don't necessarily terminate makes
-- defining an evaluation function tricky...

-- ####################################
-- ** Evaluation as a Function (Failed Attempt)

-- Here's an attempt at defining an evaluation function for commands
-- (with a bogus `while` case).

def cevalFunNoWhile (st : State) (c : Com) : State :=
  match c with
  | CSkip => st
  | CAsgn x a => (x !-> aeval st a ; st)
  | CSeq c1 c2 =>
      let st' := cevalFunNoWhile st c1
      cevalFunNoWhile st' c2
  | CIf b c1 c2 =>
      if beval st b
      then cevalFunNoWhile st c1
      else cevalFunNoWhile st c2
  | CWhile _ _ => st  -- bogus

-- FULL
-- In a more conventional functional programming language like OCaml or
-- Haskell we could add the `while` case with a recursive call.
-- Lean doesn't accept such a definition because the function we want
-- to define is not guaranteed to terminate.  Indeed, it _doesn't_
-- always terminate: for example, applied to the `loop` program above
-- it would never terminate.
--
-- Since Lean aims to be not just a functional programming language but
-- also a consistent logic, any potentially non-terminating function
-- needs to be rejected.  If we could define:
--
--     def loop_false (n : Nat) : False := loop_false n
--
-- then `False` would become provable, which would be a disaster for
-- Lean's logical consistency.
-- /FULL

-- ####################################
-- ** Evaluation as a Relation

-- Here's a better way: define `ceval` as a _relation_ rather than a
-- _function_ -- i.e., make its result a `Prop` rather than a `State`.

-- We'll use the notation `st =[ c ]=> st'` for the `ceval` relation:
-- `st =[ c ]=> st'` means that executing program `c` in a starting
-- state `st` results in an ending state `st'`.

-- *** Operational Semantics

-- Here is an informal definition of evaluation, presented as
-- inference rules for readability:
--
--                            -----------------                    (E_Skip)
--                            st =[ skip ]=> st
--
--                            aeval st a = n
--                    -------------------------------              (E_Asgn)
--                    st =[ x := a ]=> (x !-> n ; st)
--
--                            st  =[ c1 ]=> st'
--                            st' =[ c2 ]=> st''
--                          ---------------------                   (E_Seq)
--                          st =[ c1;c2 ]=> st''
--
--                           beval st b = true
--                            st =[ c1 ]=> st'
--                 --------------------------------------       (E_IfTrue)
--                 st =[ if b then c1 else c2 end ]=> st'
--
--                          beval st b = false
--                            st =[ c2 ]=> st'
--                 --------------------------------------      (E_IfFalse)
--                 st =[ if b then c1 else c2 end ]=> st'
--
--                          beval st b = false
--                     -----------------------------           (E_WhileFalse)
--                     st =[ while b do c end ]=> st
--
--                           beval st b = true
--                            st =[ c ]=> st'
--                   st' =[ while b do c end ]=> st''
--                   --------------------------------           (E_WhileTrue)
--                   st  =[ while b do c end ]=> st''

-- Here is the formal definition.  Make sure you understand how it
-- corresponds to the inference rules.

inductive CEval : Com → State → State → Prop where
  | E_Skip (st : State) :
      CEval CSkip st st
  | E_Asgn (st : State) (a : AExp) (n : Nat) (x : String) :
      aeval st a = n →
      CEval (CAsgn x a) st (x !-> n ; st)
  | E_Seq (c1 c2 : Com) (st st' st'' : State) :
      CEval c1 st st' →
      CEval c2 st' st'' →
      CEval (CSeq c1 c2) st st''
  | E_IfTrue (st st' : State) (b : BExp) (c1 c2 : Com) :
      beval st b = true →
      CEval c1 st st' →
      CEval (CIf b c1 c2) st st'
  | E_IfFalse (st st' : State) (b : BExp) (c1 c2 : Com) :
      beval st b = false →
      CEval c2 st st' →
      CEval (CIf b c1 c2) st st'
  | E_WhileFalse (b : BExp) (st : State) (c : Com) :
      beval st b = false →
      CEval (CWhile b c) st st
  | E_WhileTrue (st st' st'' : State) (b : BExp) (c : Com) :
      beval st b = true →
      CEval c st st' →
      CEval (CWhile b c) st' st'' →
      CEval (CWhile b c) st st''

notation:40 st " =[ " c " ]=> " st' => CEval c st st'

-- The cost of defining evaluation as a relation instead of a function
-- is that we now need to construct a _proof_ that some program
-- evaluates to some result state, rather than just letting Lean's
-- computation mechanism do it for us.

-- ceval_example1
example :
    empty_st =[
      CSeq (CAsgn X (ANum 2))
           (CIf (BLe (AId X) (ANum 1))
                (CAsgn Y (ANum 3))
                (CAsgn Z (ANum 4)))
    ]=> (Z !-> 4 ; X !-> 2 ; empty_st) := by
  -- We must supply the intermediate state
  apply CEval.E_Seq _ _ _ (X !-> 2 ; empty_st)
  · apply CEval.E_Asgn; rfl
  · apply CEval.E_IfFalse
    · rfl
    · apply CEval.E_Asgn; rfl

-- FULL
-- EX2 (ceval_example2)
-- ceval_example2
example :
    empty_st =[
      CSeq (CAsgn X (ANum 0))
      (CSeq (CAsgn Y (ANum 1))
            (CAsgn Z (ANum 2)))
    ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0 ; empty_st) := by
  -- ADMITTED
  apply CEval.E_Seq _ _ _ (X !-> 0 ; empty_st)
  · apply CEval.E_Asgn; rfl
  · apply CEval.E_Seq _ _ _ (Y !-> 1 ; X !-> 0 ; empty_st)
    · apply CEval.E_Asgn; rfl
    · apply CEval.E_Asgn; rfl
  -- /ADMITTED

-- EX3? (pup_to_n)
-- Write an Imp program that sums the numbers from `1` to `X`
-- (inclusive: `1 + 2 + ... + X`) in the variable `Y`.

-- ADMITDEF
def pup_to_n : Com :=
  CSeq (CAsgn Y (ANum 0))
       (CWhile (BLe (ANum 1) (AId X))
         (CSeq (CAsgn Y (APlus (AId Y) (AId X)))
               (CAsgn X (AMinus (AId X) (ANum 1)))))
-- /ADMITDEF

-- pup_to_2_ceval
theorem pup_to_2_ceval :
    (X !-> 2 ; empty_st) =[
      pup_to_n
    ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ;
         Y !-> 0 ; X !-> 2 ; empty_st) := by
  -- ADMITTED
  unfold pup_to_n
  apply CEval.E_Seq _ _ _ (Y !-> 0 ; X !-> 2 ; empty_st)
  · apply CEval.E_Asgn; rfl
  · apply CEval.E_WhileTrue _
      (X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2 ; empty_st)
    · rfl
    · apply CEval.E_Seq _ _ _
        (Y !-> 2 ; Y !-> 0 ; X !-> 2 ; empty_st)
      · apply CEval.E_Asgn; rfl
      · apply CEval.E_Asgn; rfl
    · apply CEval.E_WhileTrue _
        (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ;
         Y !-> 0 ; X !-> 2 ; empty_st)
      · rfl
      · apply CEval.E_Seq _ _ _
          (Y !-> 3 ; X !-> 1 ; Y !-> 2 ;
           Y !-> 0 ; X !-> 2 ; empty_st)
        · apply CEval.E_Asgn; rfl
        · apply CEval.E_Asgn; rfl
      · apply CEval.E_WhileFalse; rfl
  -- /ADMITTED
-- /FULL

-- #######################################################
-- ** Determinism of Evaluation

-- FULL: Changing from a computational to a relational definition of
-- evaluation is a good move because it frees us from the artificial
-- requirement that evaluation should be a total function.  But it
-- also raises a question: Is the second definition of evaluation
-- really a partial _function_?  Or is it possible that, beginning from
-- the same state `st`, we could evaluate some command `c` in
-- different ways to reach two different output states `st'` and
-- `st''`?
--
-- In fact, this cannot happen: `ceval` _is_ a partial function.
-- /FULL

theorem ceval_deterministic {c : Com} {st st1 st2 : State}
    (h1 : st =[ c ]=> st1)
    (h2 : st =[ c ]=> st2) :
    st1 = st2 := by
  induction h1 generalizing st2 with
  | E_Skip _ =>
    cases h2; rfl
  | E_Asgn _ _ _ _ ha =>
    cases h2 with
    | E_Asgn _ _ _ _ ha' => rw [ha] at ha'; rw [ha']
  | E_Seq _ _ _ _ _ _ _ ih1 ih2 =>
    cases h2 with
    | E_Seq _ _ _ st'0 _ h2a h2b =>
      have := ih1 h2a
      subst this
      exact ih2 h2b
  | E_IfTrue _ _ _ _ _ hb _ ih =>
    cases h2 with
    | E_IfTrue _ _ _ _ _ hb' h' => exact ih h'
    | E_IfFalse _ _ _ _ _ hb' _ => simp [hb] at hb'
  | E_IfFalse _ _ _ _ _ hb _ ih =>
    cases h2 with
    | E_IfTrue _ _ _ _ _ hb' _ => simp [hb] at hb'
    | E_IfFalse _ _ _ _ _ hb' h' => exact ih h'
  | E_WhileFalse _ _ _ hb =>
    cases h2 with
    | E_WhileFalse _ _ _ => rfl
    | E_WhileTrue _ _ _ _ _ hb' _ _ => simp [hb] at hb'
  | E_WhileTrue _ _ _ _ _ hb _ _ ih1 ih2 =>
    cases h2 with
    | E_WhileFalse _ _ _ hb' => simp [hb] at hb'
    | E_WhileTrue _ st'0 _ _ _ hb' h2a h2b =>
      have := ih1 h2a
      subst this
      exact ih2 h2b

-- FULL
-- #######################################################
-- * Reasoning About Imp Programs

-- We'll get into more systematic and powerful techniques for
-- reasoning about Imp programs in _Programming Language Foundations_,
-- but we can already do a few things just by working with the bare
-- definitions.

theorem plus2_spec {st : State} {n : Nat} {st' : State}
    (hx : st X = n)
    (heval : st =[ plus2 ]=> st') :
    st' X = n + 2 := by
  unfold plus2 at heval
  cases heval with
  | E_Asgn _ _ _ _ h =>
    simp [tUpdate, aeval, hx] at h ⊢
    omega

-- EX3? (XtimesYinZ_spec)
-- State and prove a specification of `XtimesYinZ`.

-- SOLUTION
theorem XtimesYinZ_spec (st : State) :
    st =[ XtimesYinZ ]=> (Z !-> st X * st Y ; st) := by
  apply CEval.E_Asgn; rfl
-- /SOLUTION
-- GRADE_MANUAL 3: XtimesYinZ_spec

-- EX3! (loop_never_stops)
theorem loop_never_stops {st st' : State}
    (h : st =[ loop ]=> st') : False := by
  -- ADMITTED
  unfold loop at h
  -- We need to do induction on the derivation.
  -- We use `remember` pattern: generalize and then do induction.
  generalize hc : CWhile BTrue CSkip = c at h
  induction h with
  | E_WhileFalse _ _ _ hb =>
    cases hc; simp [beval] at hb
  | E_WhileTrue _ _ _ _ _ hb _ _ _ ih2 =>
    exact ih2 hc
  | _ => cases hc
  -- /ADMITTED

-- EX3 (no_whiles_eqv)
-- Consider the following function:

def no_whiles (c : Com) : Bool :=
  match c with
  | CSkip => true
  | CAsgn _ _ => true
  | CSeq c1 c2 => no_whiles c1 && no_whiles c2
  | CIf _ ct cf => no_whiles ct && no_whiles cf
  | CWhile _ _ => false

-- This predicate yields `true` just on programs that have no while
-- loops.  Using `inductive`, write a property `NoWhilesR` such that
-- `NoWhilesR c` is provable exactly when `c` is a program with no
-- while loops.  Then prove its equivalence with `no_whiles`.

inductive NoWhilesR : Com → Prop where
  -- SOLUTION
  | nw_Skip : NoWhilesR CSkip
  | nw_Asgn (x : String) (ae : AExp) : NoWhilesR (CAsgn x ae)
  | nw_Seq (c1 c2 : Com) :
      NoWhilesR c1 → NoWhilesR c2 → NoWhilesR (CSeq c1 c2)
  | nw_If (be : BExp) (c1 c2 : Com) :
      NoWhilesR c1 → NoWhilesR c2 → NoWhilesR (CIf be c1 c2)
  -- /SOLUTION

theorem no_whiles_eqv (c : Com) :
    no_whiles c = true ↔ NoWhilesR c := by
  -- ADMITTED
  constructor
  · intro h
    induction c with
    | CSkip => exact NoWhilesR.nw_Skip
    | CAsgn x a => exact NoWhilesR.nw_Asgn x a
    | CSeq c1 c2 ih1 ih2 =>
      simp [no_whiles, Bool.and_eq_true] at h
      exact NoWhilesR.nw_Seq c1 c2 (ih1 h.1) (ih2 h.2)
    | CIf b c1 c2 ih1 ih2 =>
      simp [no_whiles, Bool.and_eq_true] at h
      exact NoWhilesR.nw_If b c1 c2 (ih1 h.1) (ih2 h.2)
    | CWhile _ _ => simp [no_whiles] at h
  · intro h
    induction h with
    | nw_Skip => rfl
    | nw_Asgn _ _ => rfl
    | nw_Seq _ _ _ _ ih1 ih2 => simp [no_whiles, ih1, ih2]
    | nw_If _ _ _ _ _ ih1 ih2 => simp [no_whiles, ih1, ih2]
  -- /ADMITTED

-- EX4 (no_whiles_terminating)
-- Imp programs that don't involve while loops always terminate.
-- State and prove a theorem `no_whiles_terminating` that says this.

-- SOLUTION
theorem no_whiles_terminating {c : Com} {st : State}
    (h : NoWhilesR c) :
    ∃ st', st =[ c ]=> st' := by
  induction h generalizing st with
  | nw_Skip => exact ⟨st, CEval.E_Skip st⟩
  | nw_Asgn x ae =>
    exact ⟨x !-> aeval st ae ; st, CEval.E_Asgn st ae _ x rfl⟩
  | nw_Seq c1 c2 _ _ ih1 ih2 =>
    obtain ⟨st', h1⟩ := ih1 (st := st)
    obtain ⟨st'', h2⟩ := ih2 (st := st')
    exact ⟨st'', CEval.E_Seq c1 c2 st st' st'' h1 h2⟩
  | nw_If be c1 c2 _ _ ih1 ih2 =>
    cases hb : beval st be with
    | true =>
      obtain ⟨st', h1⟩ := ih1 (st := st)
      exact ⟨st', CEval.E_IfTrue st st' be c1 c2 hb h1⟩
    | false =>
      obtain ⟨st', h2⟩ := ih2 (st := st)
      exact ⟨st', CEval.E_IfFalse st st' be c1 c2 hb h2⟩
-- /SOLUTION
-- GRADE_MANUAL 6: no_whiles_terminating
-- /FULL

-- TERSE: HIDEFROMHTML

-- #######################################################
-- * Additional Exercises

-- EX3 (stack_compiler)
-- Old HP Calculators, programming languages like Forth and Postscript,
-- and abstract machines like the Java Virtual Machine all evaluate
-- arithmetic expressions using a _stack_.

-- The instruction set for our stack language:

inductive SInstr : Type where
  | SPush (n : Nat)
  | SLoad (x : String)
  | SPlus
  | SMinus
  | SMult

open SInstr

-- Write a function to evaluate programs in the stack language.

-- ADMITDEF
def sExecute (st : State) (stack : List Nat) (prog : List SInstr) : List Nat :=
  match prog, stack with
  | [], _ => stack
  | SPush n :: prog', _ => sExecute st (n :: stack) prog'
  | SLoad x :: prog', _ => sExecute st (st x :: stack) prog'
  | SPlus :: prog', n :: m :: stack' => sExecute st ((m + n) :: stack') prog'
  | SMinus :: prog', n :: m :: stack' => sExecute st ((m - n) :: stack') prog'
  | SMult :: prog', n :: m :: stack' => sExecute st ((m * n) :: stack') prog'
  | _ :: prog', _ => sExecute st stack prog'  -- bad state: skip
-- /ADMITDEF

-- s_execute1
example :
    sExecute empty_st []
      [SPush 5, SPush 3, SPush 1, SMinus]
    = [2, 5] := by
  -- ADMITTED
  rfl
  -- /ADMITTED
-- GRADE_THEOREM 1: s_execute1

-- s_execute2
example :
    sExecute (X !-> 3) [3, 4]
      [SPush 4, SLoad X, SMult, SPlus]
    = [15, 4] := by
  -- ADMITTED
  rfl
  -- /ADMITTED
-- GRADE_THEOREM 0.5: s_execute2

-- Next, write a function that compiles an `AExp` into a stack
-- machine program.

-- ADMITDEF
def sCompile (e : AExp) : List SInstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus a1 a2 => sCompile a1 ++ sCompile a2 ++ [SPlus]
  | AMinus a1 a2 => sCompile a1 ++ sCompile a2 ++ [SMinus]
  | AMult a1 a2 => sCompile a1 ++ sCompile a2 ++ [SMult]
-- /ADMITDEF

-- s_compile1
example :
    sCompile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
    = [SLoad X, SPush 2, SLoad Y, SMult, SMinus] := by
  -- ADMITTED
  rfl
  -- /ADMITTED
-- GRADE_THEOREM 1.5: s_compile1

-- EX3 (execute_app)
-- Execution can be decomposed: executing stack program `p1 ++ p2` is
-- the same as executing `p1`, taking the resulting stack, and
-- executing `p2` from that stack.

theorem execute_app (st : State) (p1 p2 : List SInstr) (stack : List Nat) :
    sExecute st stack (p1 ++ p2) = sExecute st (sExecute st stack p1) p2 := by
  -- ADMITTED
  induction p1 generalizing stack with
  | nil => simp [sExecute, List.nil_append]
  | cons i p1' ih =>
    simp [List.cons_append]
    cases i with
    | SPush n => simp [sExecute]; exact ih (n :: stack)
    | SLoad x => simp [sExecute]; exact ih (st x :: stack)
    | SPlus =>
      match stack with
      | [] => simp [sExecute]; exact ih []
      | [x] => simp [sExecute]; exact ih [x]
      | x :: y :: rest => simp [sExecute]; exact ih ((y + x) :: rest)
    | SMinus =>
      match stack with
      | [] => simp [sExecute]; exact ih []
      | [x] => simp [sExecute]; exact ih [x]
      | x :: y :: rest => simp [sExecute]; exact ih ((y - x) :: rest)
    | SMult =>
      match stack with
      | [] => simp [sExecute]; exact ih []
      | [x] => simp [sExecute]; exact ih [x]
      | x :: y :: rest => simp [sExecute]; exact ih ((y * x) :: rest)
  -- /ADMITTED

-- EX3 (stack_compiler_correct)
-- Now we'll prove the correctness of the compiler.

theorem s_compile_correct_aux (st : State) (e : AExp) (stack : List Nat) :
    sExecute st stack (sCompile e) = aeval st e :: stack := by
  -- ADMITTED
  induction e generalizing stack with
  | ANum n => rfl
  | AId x => rfl
  | APlus a1 a2 ih1 ih2 =>
    simp [sCompile, execute_app, ih1, ih2, sExecute, aeval]
  | AMinus a1 a2 ih1 ih2 =>
    simp [sCompile, execute_app, ih1, ih2, sExecute, aeval]
  | AMult a1 a2 ih1 ih2 =>
    simp [sCompile, execute_app, ih1, ih2, sExecute, aeval]
  -- /ADMITTED

theorem s_compile_correct (st : State) (e : AExp) :
    sExecute st [] (sCompile e) = [aeval st e] := by
  -- ADMITTED
  exact s_compile_correct_aux st e []
  -- /ADMITTED
-- GRADE_THEOREM 2.5: s_compile_correct_aux
-- GRADE_THEOREM 0.5: s_compile_correct

-- FULL
-- EX3? (short_circuit)
-- Most modern programming languages use a "short-circuit" evaluation
-- rule for boolean `and`: to evaluate `BAnd b1 b2`, first evaluate
-- `b1`.  If it evaluates to `false`, then the entire `BAnd`
-- expression evaluates to `false` immediately, without evaluating
-- `b2`.  Otherwise, `b2` is evaluated to determine the result.
--
-- Write an alternate version of `beval` that performs short-circuit
-- evaluation of `BAnd` in this manner, and prove that it is
-- equivalent to `beval`.

-- SOLUTION
def beval_sc (st : State) (b : BExp) : Bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEqA a1 a2 => (aeval st a1) == (aeval st a2)
  | BNeq a1 a2 => !(aeval st a1 == aeval st a2)
  | BLe a1 a2 => Nat.ble (aeval st a1) (aeval st a2)
  | BGt a1 a2 => !(Nat.ble (aeval st a1) (aeval st a2))
  | BNot b1 => !(beval_sc st b1)
  | BAnd b1 b2 =>
    match beval_sc st b1 with
    | false => false
    | true => beval_sc st b2

theorem beval__beval_sc (st : State) (b : BExp) :
    beval st b = beval_sc st b := by
  induction b with
  | BTrue => rfl
  | BFalse => rfl
  | BEqA _ _ => rfl
  | BNeq _ _ => rfl
  | BLe _ _ => rfl
  | BGt _ _ => rfl
  | BNot b ih => simp [beval, beval_sc, ih]
  | BAnd b1 b2 ih1 ih2 =>
    simp [beval, beval_sc, ih1, ih2]
    cases beval_sc st b1 <;> simp
-- /SOLUTION

-- EX4? (break_imp)
-- Imperative languages like C and Java often include a `break` or
-- similar statement for interrupting the execution of loops.

namespace BreakImp

inductive Com : Type where
  | CSkip
  | CBreak                           -- <--- NEW
  | CAsgn (x : String) (a : AExp)
  | CSeq (c1 c2 : Com)
  | CIf (b : BExp) (c1 c2 : Com)
  | CWhile (b : BExp) (c : Com)

open Com

inductive Result : Type where
  | SContinue
  | SBreak

open Result

inductive CEvalBreak : Com → State → Result → State → Prop where
  | E_Skip (st : State) :
      CEvalBreak CSkip st SContinue st
  -- SOLUTION
  | E_Break (st : State) :
      CEvalBreak CBreak st SBreak st
  | E_Asgn (st : State) (a : AExp) (n : Nat) (x : String) :
      aeval st a = n →
      CEvalBreak (CAsgn x a) st SContinue (x !-> n ; st)
  | E_SeqContinue (c1 c2 : Com) (st st' st'' : State) (s : Result) :
      CEvalBreak c1 st SContinue st' →
      CEvalBreak c2 st' s st'' →
      CEvalBreak (CSeq c1 c2) st s st''
  | E_SeqBreak (c1 c2 : Com) (st st' : State) :
      CEvalBreak c1 st SBreak st' →
      CEvalBreak (CSeq c1 c2) st SBreak st'
  | E_IfTrue (st st' : State) (b : BExp) (c1 c2 : Com) (s : Result) :
      beval st b = true →
      CEvalBreak c1 st s st' →
      CEvalBreak (CIf b c1 c2) st s st'
  | E_IfFalse (st st' : State) (b : BExp) (c1 c2 : Com) (s : Result) :
      beval st b = false →
      CEvalBreak c2 st s st' →
      CEvalBreak (CIf b c1 c2) st s st'
  | E_WhileFalse (b : BExp) (st : State) (c : Com) :
      beval st b = false →
      CEvalBreak (CWhile b c) st SContinue st
  | E_WhileContinue (st st' st'' : State) (b : BExp) (c : Com) :
      beval st b = true →
      CEvalBreak c st SContinue st' →
      CEvalBreak (CWhile b c) st' SContinue st'' →
      CEvalBreak (CWhile b c) st SContinue st''
  | E_WhileBreak (st st' : State) (b : BExp) (c : Com) :
      beval st b = true →
      CEvalBreak c st SBreak st' →
      CEvalBreak (CWhile b c) st SContinue st'
  -- /SOLUTION

-- Now prove the following properties of your definition:

theorem break_ignore {c : Com} {st st' : State} {s : Result}
    (h : CEvalBreak (CSeq CBreak c) st s st') :
    st = st' := by
  -- ADMITTED
  cases h with
  | E_SeqContinue _ _ _ _ _ _ h1 _ => cases h1
  | E_SeqBreak _ _ _ _ h1 => cases h1; rfl
  -- /ADMITTED
-- GRADE_THEOREM 1.5: break_ignore

theorem while_continue {b : BExp} {c : Com} {st st' : State} {s : Result}
    (h : CEvalBreak (CWhile b c) st s st') :
    s = SContinue := by
  -- ADMITTED
  cases h with
  | E_WhileFalse _ _ _ _ => rfl
  | E_WhileContinue _ _ _ _ _ _ _ _ => rfl
  | E_WhileBreak _ _ _ _ _ _ => rfl
  -- /ADMITTED
-- GRADE_THEOREM 1.5: while_continue

theorem while_stops_on_break {b : BExp} {c : Com} {st st' : State}
    (hb : beval st b = true)
    (hc : CEvalBreak c st SBreak st') :
    CEvalBreak (CWhile b c) st SContinue st' := by
  -- ADMITTED
  exact CEvalBreak.E_WhileBreak st st' b c hb hc
  -- /ADMITTED
-- GRADE_THEOREM 1: while_stops_on_break

theorem seq_continue {c1 c2 : Com} {st st' st'' : State}
    (h1 : CEvalBreak c1 st SContinue st')
    (h2 : CEvalBreak c2 st' SContinue st'') :
    CEvalBreak (CSeq c1 c2) st SContinue st'' := by
  -- ADMITTED
  exact CEvalBreak.E_SeqContinue c1 c2 st st' st'' SContinue h1 h2
  -- /ADMITTED
-- GRADE_THEOREM 1: seq_continue

theorem seq_stops_on_break {c1 c2 : Com} {st st' : State}
    (h : CEvalBreak c1 st SBreak st') :
    CEvalBreak (CSeq c1 c2) st SBreak st' := by
  -- ADMITTED
  exact CEvalBreak.E_SeqBreak c1 c2 st st' h
  -- /ADMITTED
-- GRADE_THEOREM 1: seq_stops_on_break

end BreakImp

-- EX4? (add_for_loop)
-- Add C-style `for` loops to the language of commands, update the
-- `ceval` definition to define the semantics of `for` loops, and add
-- cases for `for` loops as needed so that all the proofs in this
-- file are accepted by Lean.
--
-- A `for` loop should be parameterized by (a) a statement executed
-- initially, (b) a test that is run on each iteration of the loop to
-- determine whether the loop should continue, (c) a statement
-- executed at the end of each loop iteration, and (d) a statement
-- that makes up the body of the loop.

-- /FULL
-- TERSE: /HIDEFROMHTML
