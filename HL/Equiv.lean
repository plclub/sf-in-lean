import SFLMeta

import LF.CustomTactics
import LF.Typeclasses
import HL.Imp


open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Equiv: Program Equivalence" =>
%%%
tag := "Equiv"
htmlSplit := .never
file := some "Equiv"
%%%

```lean
open scoped HasEval MyGetElem Com
```

# Behavioral Equivalence

::::full
In {ref "Slang"}[an earlier chapter], we investigated the correctness of a very
simple program transformation: the `optimize0plus` function.  The
programming language we were considering was the first version of
the language of arithmetic expressions - with no variables - so
in that setting it was very easy to define what it means for a
program transformation to be correct: it should always yield a
program that evaluates to the same number as the original.

To talk about the correctness of program transformations for the
full Imp language - in particular, assignment - we need to
consider the role of mutable state and develop a more
sophisticated notion of correctness, which we'll call _behavioral
equivalence_.
::::

::::full
For example:
- `X + 2` is behaviorally equivalent to `1 + X + 1`
- `X - X` is behaviorally equivalent to `0`
- `(X - 1) + 1` is _not_ behaviorally equivalent to `X`
::::

## Definitions

::::full
For `aexp`s and `bexp`s with variables, the definition we want is
clear: Two `aexp`s or `bexp`s are "behaviorally equivalent" if
they evaluate to the same result in every state.
::::

```lean
def Aexp.Equiv (a₁ a₂ : Aexp) : Prop :=
  ∀ (st : State),
    a₁.eval st = a₂.eval st

def Bexp.Equiv (b₁ b₂ : Bexp) : Prop :=
  ∀ (st : State),
    b₁.eval st = b₂.eval st
```

We'll also define a notation for `Equiv`:

```lean
class Equiv (α : Type) where
  equiv : α → α → Prop

infix:70 " ≃ " => Equiv.equiv -- you can type `≃` as \equiv

instance : Equiv Aexp where
  equiv := Aexp.Equiv

instance : Equiv Bexp where
  equiv := Bexp.Equiv

@[simp]
theorem Aexp.equiv_notation {a₁ a₂ : Aexp} : a₁.Equiv a₂ ↔ a₁ ≃ a₂ := by rfl
@[simp]
theorem Aexp.equiv_def {a₁ a₂ : Aexp} :
    a₁ ≃ a₂ ↔ ∀ (st : State), a₁.eval st = a₂.eval st := by rfl

@[simp]
theorem Bexp.equiv_notation {b₁ b₂ : Bexp} : b₁.Equiv b₂ ↔ b₁ ≃ b₂ := by rfl
@[simp]
theorem Bexp.equiv_def {b₁ b₂ : Bexp} :
    b₁ ≃ b₂ ↔ ∀ (st : State), b₁.eval st = b₂.eval st := by rfl
```

::::full
Here are some simple examples of equivalences of arithmetic
and boolean expressions.
::::

```lean
example : aexp { X - X } ≃ aexp { 0 } := by simp
```


```lean
example : bexp { X - X = 0 } ≃ bexp { true } := by simp
```

::::full
For commands, the situation is a little more subtle.  We
can't simply say "two commands are behaviorally equivalent if they
evaluate to the same ending state whenever they are started in the
same initial state," because some commands, when run in some
starting states, don't terminate in any final state at all!

What we need instead is this: two commands are behaviorally
equivalent if, for any given starting state, they either (1) both
diverge or else (2) both terminate in the same final state.  A
compact way to express this is "if the first one terminates in a
particular state then so does the second, and vice versa."
::::

```lean
def Com.Equiv (c₁ c₂ : Com) : Prop :=
    ∀ {st st' : State},
      (st =[ c₁ ]=> st') ↔ (st =[ c₂ ]=> st')

instance : Equiv Com where
  equiv := Com.Equiv

@[simp]
theorem Com.equiv_notation {c₁ c₂ : Com} : c₁.Equiv c₂ ↔ c₁ ≃ c₂ := by rfl
@[simp]
theorem Com.equiv_def {c₁ c₂ : Com} : c₁ ≃ c₂ ↔
    ∀ {st st' : State}, (st =[ c₁ ]=> st') ↔ (st =[ c₂ ]=> st') := by rfl
```

## Simple Examples

```lean
namespace Com
```

::::full
  For examples of command equivalence, let's start by looking at
  a trivial equivalence involving {name}`skip`.
::::

```lean
theorem skip_left {c : Com} : imp { skip; c } ≃ c := by
  workinclass!
    rw [equiv_def]
    intro st st''
    constructor
    · intro h
      inversion h with
      | seq st' h1 h2 =>
        inversion h1
        exact h2
    · intro h
      exact EvalR.seq EvalR.skip h
```

:::::exercise (rating := 2) (name:= "skip_right")
Prove that adding a {name}`skip` _after_ a command also results in an
equivalent program.

```lean
theorem skip_right {c : Com} : imp { c; skip } ≃ c := by
  solution!
    rw [equiv_def]
    intro st st''
    constructor
    · intro h
      inversion h with
      | seq st' h1 h2 =>
        inversion h2
        exact h1
    · intro h
      exact EvalR.seq h EvalR.skip
```
:::::

::::full
Similarly, here is a simple equivalence that optimises `if`
commands.
::::

```lean
theorem if_true_simple {c₁ c₂ : Com} : imp {if (true) {c₁} else {c₂}} ≃ c₁ := by
  rw [equiv_def]
  intro st st'
  constructor
  · intro h
    inversion h with
    | ifTrue hb hc => exact hc
    | ifFalse hb hc => simp at hb
  · intro h
    apply EvalR.ifTrue _ h
    simp
```

::::full
Of course, no programmer would write a conditional whose condition
is literally `true`.  (At least, no human programmer - compilers
and macro preprocessors do this sort of thing internally all the
time!) But they might write one whose condition is _equivalent_ to
true:
::::

::::full
_Theorem_: If `b` is equivalent to `true`, then `if (b) {c₁} else {c₂}` is equivalent to `c₁`.
_Proof_:
 - (`→`) We must show, for all `st` and `st'`, that if
   `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'` then
   `st =[ c₁ ]=> st'`.

   Proceed by cases on the rules that could possibly have been
   used to show `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'`,
   namely {name}`Com.EvalR.ifTrue` and {name}`Com.EvalR.ifFalse`.

   - Suppose the final rule in the derivation of
     `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'` was {name}`Com.EvalR.ifTrue`.
     We then have, by the premises of {name}`Com.EvalR.ifTrue`, that
     `st =[ c₁ ]=> st'`. This is exactly what we set out to prove.

   - On the other hand, suppose the final rule in the derivation
     of `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'` was `Com.EvalR.ifFalse`.
     We then know that `b.eval st = false` and `st =[ c₂ ]=> st'`.

     Recall that `b` is equivalent to `true`, i.e., forall `st`,
     `b.eval st = (bexp {true}).eval st`.  In particular, this means
     that `b.eval st = true`, since `(bexp {true}).eval st = true`.  But
     this is a contradiction, since {name}`Com.EvalR.ifFalse` requires that
     `b.eval st = false`.  Thus, the final rule could not have
     been {name}`Com.EvalR.ifFalse`.

 - (`<-`) We must show, for all `st` and `st'`, that if
   `st =[ c₁ ]=> st'` then
   `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'`.

   Since `b` is equivalent to `true`, we know that `b.eval st` =
   `(bexp {true}).eval st = true` = `true`.  Together with the assumption that
   `st =[ c₁ ]=> st'`, we can apply {name}`Com.EvalR.ifTrue` to derive
   `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'`.
::::

::::full
Here is the formal version of this proof:
::::

```lean
theorem if_true {b : Bexp} {c₁ c₂ : Com} (hb : b ≃ bexp {true}) :
    imp {if (b) {c₁} else {c₂}} ≃ c₁ := by
  rw [equiv_def]
  intro st st'
  constructor
  · intro h
    inversion h <;> simp_all
  · intro h
    apply EvalR.ifTrue _ h
    simp_all
```

:::::exercise (rating := 2) (name := "if_false_equiv")
```lean
theorem if_false {b : Bexp} {c₁ c₂ : Com} (hb : b ≃ bexp {false}) :
    imp {if (b) {c₁} else {c₂}} ≃ c₂ := by
  solution!
    rw [equiv_def]
    intro st st'
    constructor
    · intro h
      inversion h <;> simp_all
    · intro h
      apply EvalR.ifFalse _ h
      simp_all
```
:::::


:::::exercise (rating := 3) (name := "swap_if_branches")
Show that we can swap the branches of an `if` if we also negate its
condition.

```lean
theorem swap_if_branches {b : Bexp} {c₁ c₂ : Com} :
    imp {if (b) {c₁} else {c₂}} ≃
    imp {if (¬ b) {c₂} else {c₁}} := by
  solution!
    rw [equiv_def]
    intro st st'
    constructor
    · intro h
      inversion h with
      | ifTrue hb hc =>
        apply EvalR.ifFalse _ hc
        simp [hb]
      | ifFalse hb hc =>
        apply EvalR.ifTrue _ hc
        simp [hb]
    · intro h
      inversion h with
      | ifTrue hb hc =>
        apply EvalR.ifFalse _ hc
        simp_all
      | ifFalse hb hc =>
        apply EvalR.ifTrue _ hc
        simp_all
```
:::::

::::full
For `while` loops, we can give a similar pair of theorems.  A loop
whose guard is equivalent to {name}`false` is equivalent to {name}`skip`,
while a loop whose guard is equivalent to {name}`true` is equivalent to
`while (true) {skip} end` (or any other non-terminating program).
::::

::::full
The first of these facts is easy.
::::

```lean
theorem while_false_equiv {b : Bexp} {c : Com} (hb : b ≃ bexp {false}) :
    imp {while (b) {c}} ≃ imp {skip} := by
  rw [equiv_def]
  intro st st''
  constructor
  · intro h
    inversion h with
    | whileFalse => exact EvalR.skip
    | whileTrue st' hb' hc hloop =>
      simp_all
  · intro h
    inversion h
    apply EvalR.whileFalse
    simp_all
```

:::::exercise (rating := 2) (name := "while_false_informal") (level:= Advanced) (manual:= true)
Write an informal proof of `while_false_equiv`.
:::::

::::full
To prove the second fact, we need an auxiliary lemma stating that
`while` loops whose guards are equivalent to {name}`true` never
terminate.
::::

::::full
_Lemma_: If `b` is equivalent to {name}`true`, then it cannot be
the case that `st =[ while (b) {c} ]=> st'`.

_Proof_: Suppose that `st =[ while (b) {c} ]=> st'`.  We show,
by induction on a derivation of `st =[ while (b) {c} ]=> st'`,
that this assumption leads to a contradiction. The only two cases
to consider are {name}`Com.EvalR.whileFalse` and {name}`Com.EvalR.whileTrue`; the others
are contradictory.

- Suppose `st =[ while (b) {c} ]=> st'` is proved using rule
  {name}`Com.EvalR.whileFalse`.  Then by assumption `b.eval st = false`. But
  this contradicts the assumption that `b` is equivalent to
  `true`.

- Suppose `st =[ while (b) {c} ]=> st'` is proved using rule
  {name}`Com.EvalR.whileTrue`.  We must have:

  1. `b.eval st = true`, and
  2. there is some `st₀` such that `st =[ c ] => st₀` and
     `st₀ =[ while (b) {c} ]=> st'`.
  3. Also, we are given an induction hypothesis saying that
     `st₀ =[ while (b) {c} ]=> st'` leads to a contradiction,

  We obtain a contradiction by 2 and 3.
::::

```lean
theorem while_true_nonterm {b : Bexp} {c : Com} {st st' : State} (hb : b ≃ bexp {true}) :
    ¬ st =[ while (b) {c} ]=> st' := by
  workinclass!
    intro contra
    generalize heq : (imp {while (b) {c}}) = com at contra
    induction contra with
    | whileFalse hb' =>
      injection heq with hbeq hceq
      subst hbeq
      simp_all -- hb and hb' are contradictory
    | whileTrue hb' hc' hwhile ih1 ih2 =>
      exact ih2 heq
    | skip | asgn | seq | ifTrue | ifFalse =>
      contradiction -- `heq` says that different commands are equal
```
:::::exercise (rating := 2) (name := "while_true_nonterm_informal") (manual:= true)
Explain what the lemma `while_true_nonterm` means in English.
:::::

:::::exercise (rating := 2) (name := "while_true")
Prove the following theorem.
_Hint_: You'll want to use `while_true_nonterm` here.

```lean
theorem while_true {b : Bexp} {c : Com} (hb : b ≃ bexp {true}) :
    imp {while (b) {c}} ≃ imp {while (true) {skip}} := by
  solution!
    rw [equiv_def]
    intro st st'
    constructor
    · intro h
      exfalso
      exact while_true_nonterm hb h
    · intro h
      exfalso
      apply while_true_nonterm _ h
      rw [Bexp.equiv_def]
      intro
      rfl
```
:::::

::::full
A more interesting fact about `while` commands is that any number
of copies of the body can be "unrolled" without changing meaning.

Loop unrolling is an important transformation in any real
compiler, so its correctness is of more than just academic
interest!
::::

```lean
theorem loop_unrolling {b : Bexp} {c : Com} :
    imp { while (b) {c} } ≃
    imp {
      if (b) {c} else {skip};
      while (b) {c}
    } := by
  workinclass!
    rw [equiv_def]
    intro st st'
    constructor
    · intro h
      inversion h with
      | whileFalse hb =>
        apply EvalR.seq (st' := st)
        · exact EvalR.ifFalse hb EvalR.skip
        · exact EvalR.whileFalse hb
      | whileTrue stmid hb hc hloop =>
        apply EvalR.seq _ hloop
        exact EvalR.ifTrue hb hc
    · intro h
      inversion h with
      | seq stmid h1 h2 =>
        inversion h1 with
        | ifTrue hb hc =>
          exact EvalR.whileTrue hb hc h2
        | ifFalse hb hc =>
          inversion hc
          exact h2
```

:::::full
::::exercise (rating := 2) (name := "seq_assoc") (optional:= true)
```lean
theorem seq_assoc {c₁ c₂ c₃ : Com} :
  imp {~(imp {c₁; c₂}); c₃} ≃ imp {c₁; c₂; c₃} := by
    solution!
      intro st₁ st₂
      constructor <;> intro h
      · inversion h with
        | seq h₁ h₂ =>
            inversion h₁
            apply EvalR.seq; assumption
            apply EvalR.seq <;> assumption
      · inversion h with
        | seq h₁ h₂ =>
            inversion h₂
            apply EvalR.seq <;> try assumption
            apply EvalR.seq <;> assumption
```
::::
:::::

::::full
Proving program properties involving assignments is one place
where the fact that we are treating equality on program states
extensionally (e.g., `x →ₜ m[x] ; m` and `m` are equal maps) comes
in handy.
::::

```lean
theorem identity_assignment {X : Ident} :
    imp { X := X } ≃ imp { skip } := by
  rw [equiv_def]
  intro st st'
  constructor
  · intro h
    inversion h with
    | asgn n h =>
      subst h
      simp only [Aexp.eval_id, TotalMap.update_same]
      exact Com.EvalR.skip
  · intro h
    inversion h
    have h' : st =[ X := X ]=> X →ₜ st[X] ; st := by
      apply Com.EvalR.asgn
      simp
    simp_all [TotalMap.update_same]
```

:::::exercise (rating := 2) (name := "assign_equiv")
```lean
theorem assign_equiv {X : Ident} {a : Aexp} (ha : aexp { X } ≃ a) :
    imp { skip } ≃ imp { X := a } := by
  solution!
    rw [equiv_def]
    rw [Aexp.equiv_def] at ha
    intro st st'
    constructor
    · intro h
      inversion h
      have h' : st =[ X := ~a ]=> X →ₜ st[X]; st := by
        apply Com.EvalR.asgn
        simp [← ha]
      simp_all [← ha]
    · intro h
      inversion h with
      | asgn n h =>
        subst h
        simp only [← ha, Aexp.eval_id, TotalMap.update_same]
        exact Com.EvalR.skip
```
:::::

:::::full
::::exercise (rating := 2) (name := "equiv_classes") (manual:= true) (optional := true)
Given the following programs, group together those that are
equivalent in Imp. Your answer should be given as a list of lists,
where each sub-list represents a group of equivalent programs. For
example, if you think programs (a) through (h) are all equivalent
to each other, but not to (i), your answer should look like this:

```
[ [progA, progB, progC, progD, progE, progF, progG, progH], [progI] ]
```

Write down your answer below in the definition of  `equiv_classes`

```lean
def progA : Com :=
  imp {
    while (X > 0) {
       X := X + 1
    }
  }

def progB : Com :=
  imp {
    if (X = 0) {
       X := X + 1;
       Y := 1
     } else {
       Y := 0
     };
     X := X - Y;
     Y := 0
  }

def progC : Com :=
  imp { skip }

def progD : Com :=
  imp {
    while (X ≠ 0) {
       X := (X * Y) + 1
    }
  }

def progE : Com :=
  imp { Y := 0 }

def progF : Com :=
  imp {
    Y := X + 1;
    while (X ≠ Y) {
      Y := X + 1
    }
  }

def progG : Com :=
  imp {
    while (true) {
      skip
    }
  }

def progH : Com :=
  imp {
    while (X ≠ X) {
      X := X + 1
    }
  }

def progI : Com :=
  imp {
    while (X ≠ Y) {
      X := Y + 1
    }
  }
```

```lean
def equiv_classes : List (List Com) :=
-- SOLUTION
  [ [progA, progD] ,
    [progB, progE] ,
    [progC, progH] ,
    [progF, progG] ,
    [progI] ]
-- END SOLUTION
```
::::
:::::

# Properties of Behavior Equivalence

::::full
We next consider some fundamental properties of program equivalence.
::::

## Behavioral Equivalence is an Equivalence

::::full
First, let's verify that the equivalences on {name}`Aexp`s, {name}`Bexp`s, and
{name}`Com`s really are _equivalences_ - ie, that they are reflexive,
symmetric, and transitive. These proofs are all easy.
::::

```lean
end Com

theorem Aexp.equiv_refl (a : Aexp) : a ≃ a := by simp_all
theorem Aexp.equiv_symm {a₁ a₂ : Aexp} (h : a₁ ≃ a₂) : a₂ ≃ a₁ := by simp_all
theorem Aexp.equiv_trans {a₁ a₂ a₃ : Aexp} (h₁ : a₁ ≃ a₂) (h₂ : a₂ ≃ a₃) : a₁ ≃ a₃ := by simp_all

theorem Bexp.equiv_refl {b : Bexp} : b ≃ b := by simp_all
theorem Bexp.equiv_symm {b₁ b₂ : Bexp} (h : b₁ ≃ b₂) : b₂ ≃ b₁ := by simp_all
theorem Bexp.equiv_trans {b₁ b₂ b₃ : Bexp} (h₁ : b₁ ≃ b₂) (h₂ : b₂ ≃ b₃) : b₁ ≃ b₃ := by simp_all

theorem Com.equiv_refl {c : Com} : c ≃ c := by simp_all
theorem Com.equiv_symm {c₁ c₂ : Com} (h : c₁ ≃ c₂) : c₂ ≃ c₁ := by simp_all
theorem Com.equiv_trans {c₁ c₂ c₃ : Com} (h₁ : c₁ ≃ c₂) (h₂ : c₂ ≃ c₃) : c₁ ≃ c₃ := by simp_all
```

::::full
Lean has a standard library definition for relations that are equivalences, unsurprisingly called
{name}`Equivalence`. To show that a relation is an {name}`Equivalence`,
one needs only supply proofs of the three properties above:

```lean
theorem Com.equiv_equivalence : Equivalence Com.Equiv where
  refl := @Com.equiv_refl
  symm := Com.equiv_symm
  trans := Com.equiv_trans
```
::::

## Behavioral Equivalence is a Congruence

::::full

Less obviously, behavioral equivalence is also a _congruence_.
That is, the equivalence of two subprograms implies the
equivalence of the larger programs in which they are embedded:

              a ≃ a'
     -------------------------
        (x := a) ≃ (x := a')

            c1 ≃ c1'
            c2 ≃ c2'
     --------------------------
      (c1 ; c2) ≃ (c1' ; c2')

... and so on for the other forms of commands.

(Note that we are using the inference rule notation here not
as part of an inductive definition, but simply to write down some
valid implications in a readable format. We prove these
implications below.)
::::

::::full
We will see a concrete example of why these congruence
properties are important in the following section (in the proof of
`fold_constants_com_sound`), but the main idea is that they allow
us to replace a small part of a large program with an equivalent
small part and know that the whole large programs are equivalent
_without_ doing an explicit proof about the parts that didn't
change - i.e., the "proof burden" of a small change to a large
program is proportional to the size of the change, not the
program!
::::


```lean
theorem Com.congruence.asgn {x : Ident} {a a' : Aexp} (ha : a ≃ a') :
    imp {x := a} ≃ imp {x := a'} := by
  rw [equiv_def]
  intro st st'
  constructor <;>
  · intro h
    inversion h with
    | asgn n h =>
      subst h
      apply Com.EvalR.asgn
      simp_all
```

::::full
The congruence property for loops is a little more interesting,
since it requires induction.

_Theorem_: Equivalence is a congruence for `while` -- that is, if
`b` is equivalent to `b'` and `c` is equivalent to `c'`, then
`while (b) {c}` is equivalent to `while (b') {c'}`.

_Proof_: Suppose `b` is equivalent to `b'` and `c` is
equivalent to `c'`.  We must show, for every `st` and `st'`, that
`st =[ while (b) {c} ]=> st'` iff `st = while (b') {c'}]=> st'`.
We consider the two directions separately.

  - (`→`) We show that `st =[ while (b) {c} ]=> st'` implies
    `st =[ while (b') {c'} ]=> st'`, by induction on a
    derivation of `st =[ while (b) {c} ]=> st'`.  The only
    nontrivial cases are when the final rule in the derivation is
    {name}`Com.EvalR.whileFalse` or {name}`Com.EvalR.whileTrue`.

      - {name}`Com.EvalR.whileFalse`: In this case, the form of the rule gives us
        `b.eval st = false` and `st = st'`.  But then, since
        `b` and `b'` are equivalent, we have `b'.eval st = false`,
        and {name}`Com.EvalR.whileFalse` applies, giving us
        `st =[ while (b') {c'} ]=> st'`, as required.

      - {name}`Com.EvalR.whileTrue`: The form of the rule now gives us `b.eval st = true`,
        with `st =[ c ]=> st'₀` and `st'₀ =[ while {b} {c} ]=> st'`
        for some state `st'₀`, with the
        induction hypothesis `st'₀ =[ while (b') {c'} ]=> st'`.

        Since `c` and `c'` are equivalent, we know that `st =[ c']=> st'0`.
        And since `b` and `b'` are equivalent,
        we have `b'.eval st = true`.  Now {name}`Com.EvalR.whileTrue` applies,
        giving us `st =[ while (b') {c'} ]=> st'`, as
        required.

  - (`←`) Similar.
::::

:::dev "Sati (satiscugcat)"
```
NOT PORTED YET - remaining portions of Equiv.v left (apart from the portions explicitly stated so far).
  - The rest of "Behavioural Equivalence is a Congruence"
  - The section on "Program Transformation"
  - Soundness of (0 + n) Elimination
  - Extended Exercise: Nondeterministic Imp
  - Additional Exercises
```
:::
