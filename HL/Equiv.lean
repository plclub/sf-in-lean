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
For `Aexp`s and `Bexp`s with variables, the definition we want is
clear: Two `Aexp`s or `Bexp`s are "behaviorally equivalent" if
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
     `b.eval st = (Bexp {true}).eval st`.  In particular, this means
     that `b.eval st = true`, since `(Bexp {true}).eval st = true`.  But
     this is a contradiction, since {name}`Com.EvalR.ifFalse` requires that
     `b.eval st = false`.  Thus, the final rule could not have
     been {name}`Com.EvalR.ifFalse`.

 - (`<-`) We must show, for all `st` and `st'`, that if
   `st =[ c₁ ]=> st'` then
   `st =[ imp {if (b) {c₁} else {c₂}} ]=> st'`.

   Since `b` is equivalent to `true`, we know that `b.eval st` =
   `(Bexp {true}).eval st = true` = `true`.  Together with the assumption that
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
def equiv_classes : List (List Com) := solution!(
  [ [progA, progD] ,
    [progB, progE] ,
    [progC, progH] ,
    [progF, progG] ,
    [progI] ]
)
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

            c₁ ≃ c₁'
            c₂ ≃ c₂'
     --------------------------
      (c₁ ; c₂) ≃ (c₁' ; c₂')

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
theorem Com.congruence_asgn {x : Ident} {a a' : Aexp} (ha : a ≃ a') :
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

```lean
theorem Com.congruence_while {b b' : Bexp} {c c' : Com} (hb : b ≃ b') (hc : c ≃ c') :
    imp {while (b) {c}} ≃ imp {while (b') {c'}} := by
  workinclass!
    rw [equiv_def]
    intro st st'
    constructor
    · intro h
      generalize heq : (imp {while (b) {c}}) = com at h
      induction h with
      | whileFalse hb' =>
        injection heq with hbeq hceq
        subst hbeq
        apply Com.EvalR.whileFalse
        rw [← hb]
        exact hb'
      | whileTrue hb' hc' hwhile _ ih2 =>
        injection heq with beq ceq
        subst beq ceq
        rw [hb] at hb'
        specialize ih2 rfl
        apply Com.EvalR.whileTrue hb' _ ih2
        · rw [equiv_def] at hc
          exact hc.mp hc'
      | skip | asgn | seq | ifTrue | ifFalse =>
        contradiction
    · intro h
      generalize heq : (imp {while (~b') {~c'}}) = com at h
      induction h with
      | whileFalse hb' =>
        injection heq with hbeq hceq
        subst hbeq
        apply Com.EvalR.whileFalse
        rw [hb]
        exact hb'
      | whileTrue hb' hc' hwhile _ ih2 =>
        injection heq with beq ceq
        subst beq ceq
        rw [← hb] at hb'
        specialize ih2 rfl
        apply Com.EvalR.whileTrue hb' _ ih2
        · rw [equiv_def] at hc
          exact hc.mpr hc'
      | skip | asgn | seq | ifTrue | ifFalse =>
        contradiction
```
:::::exercise (rating := 3) (name := "Com.congruence_seq") (optional := true)
```lean
theorem Com.congruence_seq {c₁ c₁' c₂ c₂' : Com} (hc₁ : c₁ ≃ c₁') (hc₂ : c₂ ≃ c₂') :
    imp {c₁ ; ~c₂} ≃ imp {c₁' ; c₂'} := by
  solution!(
    intro st st'
    constructor
    · intro h
      inversion h with
      | seq hc₁' hc₂' =>
        rw [equiv_def] at hc₁
        rw [equiv_def] at hc₂
        exact Com.EvalR.seq (hc₁.mp hc₁') (hc₂.mp hc₂')
    · intro h
      inversion h with
      | seq hc₁' hc₂' =>
        rw [equiv_def] at hc₁
        rw [equiv_def] at hc₂
        exact Com.EvalR.seq (hc₁.mpr hc₁') (hc₂.mpr hc₂')
  )
```
:::::

:::::exercise (rating := 3) (name := "Com.congruence_if")
```lean
theorem Com.congruence_if {b b' : Bexp} {c₁ c₁' c₂ c₂' : Com}
   (hb : b ≃ b') (hc₁ : c₁ ≃ c₁') (hc₂ : c₂ ≃ c₂') :
    (imp {if (b) {c₁} else {c₂}}).Equiv
    (imp {if (b') {c₁'} else {c₂'}}) := by
  solution!(
    intro st st'
    constructor
    · intro h
      inversion h with
      | ifTrue hb' hc₁' =>
        rw [hb] at hb'
        apply Com.EvalR.ifTrue <;> try assumption
        · rw [equiv_def] at hc₁
          exact (hc₁.mp hc₁')
      | ifFalse hb' hc₂' =>
        rw [hb] at hb'
        apply Com.EvalR.ifFalse <;> try assumption
        · rw [equiv_def] at hc₂
          exact (hc₂.mp hc₂')
    · intro h
      inversion h with
      | ifTrue hb' hc₁' =>
        rw [← hb] at hb'
        apply Com.EvalR.ifTrue <;> try assumption
        · rw [equiv_def] at hc₁
          exact (hc₁.mpr hc₁')
      | ifFalse hb' hc₂' =>
        rw [← hb] at hb'
        apply Com.EvalR.ifFalse <;> try assumption
        · rw [equiv_def] at hc₂
          exact (hc₂.mpr hc₂')
  )
```
:::::

::::full
For example, here are two programs and a proof of their equivalence using their congruence theorems.
::::

```lean
example :
    imp {X := 0; if (X = 0) {Y := 0} else {Y := 42}} ≃
    imp {X := 0; if (X = 0) {Y := X - X} else {Y := 42}} := by
  apply Com.congruence_seq
  · apply Com.equiv_refl
  · apply Com.congruence_if
    · apply Bexp.equiv_refl
    · apply Com.congruence_asgn
      simp
    · apply Com.equiv_refl
```

:::::exercise (rating := 3) (name := "not_congr") (level := Advanced) (manual := true)
We've shown that the {name}`Com.Equiv` relation is both an equivalence and
a congruence on commands.  Can you think of a relation on commands
that is an equivalence but _not_ a congruence?  Write down the
relation (formally), together with an informal sketch of a proof
that it is an equivalence and a counterexample showing it is not a
congruence.
:::::

# Program Transformation

::::full
A _program transformation_ is a function that takes a program as input
and produces a modified program as output.  Compiler
optimizations such as constant folding are canonical examples,
but there are many others.
::::

```lean
def Aexp.TransSound (trans : Aexp → Aexp) : Prop :=
  ∀ (a : Aexp), a ≃ (trans a)

@[simp]
theorem Aexp.transSound_def {trans : Aexp → Aexp} :
    TransSound trans ↔ ∀ (a : Aexp), a ≃ (trans a) := by rfl

def Bexp.TransSound (trans : Bexp → Bexp) : Prop :=
  ∀ (b : Bexp), b ≃ (trans b)

@[simp]
theorem Bexp.transSound_def {trans : Bexp → Bexp} :
    TransSound trans ↔ ∀ (b : Bexp), b ≃ (trans b) := by rfl

def Com.TransSound (trans : Com → Com) : Prop :=
  ∀ (c : Com), c ≃ (trans c)

@[simp]
theorem Com.transSound_def {trans : Com → Com} :
    TransSound trans ↔ ∀ (c : Com), c ≃ (trans c) := by rfl
```


## The Constant-Folding Transformation

::::full
An expression is _constant_ if it contains no variable references.

Constant folding is an optimization that finds constant
expressions and replaces them by their values.
::::

```lean
def Aexp.foldConstants (a : Aexp) : Aexp :=
  match a with
  | .num n => .num n
  | .id x => .id x
  | aexp { ~a₁ + ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => .num (n₁ + n₂)
    | a₁', a₂' => aexp { ~a₁' + ~a₂' }
  | aexp { ~a₁ - ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => .num (n₁ - n₂)
    | a₁', a₂' => aexp { ~a₁' - ~a₂' }
  | aexp { ~a₁ * ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => .num (n₁ * n₂)
    | a₁', a₂' => aexp { ~a₁' * ~a₂' }

@[simp]
theorem Aexp.foldConstants_num (n : Nat) : (Aexp.num n).foldConstants = .num n := rfl
@[simp]
theorem Aexp.foldConstants_id (x : Ident) : (Aexp.id x).foldConstants = .id x := rfl

theorem Aexp.foldConstants_cases (a₁ a₂ : Aexp) :
    (∃ n₁ n₂, a₁.foldConstants = .num n₁ ∧ a₂.foldConstants = .num n₂) ∨
    (aexp {a₁ + a₂}).foldConstants = (aexp {~a₁.foldConstants + ~a₂.foldConstants}) ∧
    (aexp {a₁ - a₂}).foldConstants = (aexp {~a₁.foldConstants - ~a₂.foldConstants}) ∧
    (aexp {a₁ * a₂}).foldConstants = (aexp {~a₁.foldConstants * ~a₂.foldConstants}) := by
  cases ha₁ : a₁.foldConstants with
  | num n₁ =>
    cases ha₂ : a₂.foldConstants with
    | num n₂ =>
      left
      exists n₁, n₂
    | _ =>
      simp [foldConstants, ha₁, ha₂]
  | _ =>
    simp [foldConstants, ha₁]
```

:::dev "Niklas Halonen (xhalo32)"
Make sure we have explained what named cases hypotheses does (`cases ha₁ : a₁.foldConstants` in the above proof).
:::

```lean
example : (aexp { (1 + 2) * X }).foldConstants = (aexp { 3 * X }) := by rfl
```

::::full
 Note that this version of constant folding doesn't do other
"obvious" things like eliminating trivial additions (e.g.,
rewriting `0 + X` to just  `X`).: we are focusing on a single
optimization for the sake of simplicity.

It is not hard to incorporate other ways of simplifying
expressions -- the definitions and proofs just get longer.  We'll
consider some in the exercises.
::::

```lean
example : (aexp { X - ((0 * 6) + Y) }).foldConstants = (aexp { X - (0 + Y) }) := by rfl
```

::::full
Not only can we lift {name}`Aexp.foldConstants` to {name}`Bexp` in the {name}`Bexp.eq`,
{name}`Bexp.neq`, and {name}`Bexp.le` cases, we can also look for constant
_boolean_ expressions and evaluate them in place as well.
::::

```lean
def Bexp.foldConstants (b : Bexp) : Bexp :=
  match b with
  | bexp { true } => bexp { true }
  | bexp { false } => bexp { false }
  | bexp { ~a₁ = ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => if n₁ = n₂ then bexp { true } else bexp {false}
    | a₁', a₂' => bexp { ~a₁' = ~a₂' }
  | bexp { ~a₁ ≠ ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => if n₁ ≠ n₂ then bexp { true } else bexp {false}
    | a₁', a₂' => bexp { ~a₁' ≠ ~a₂' }
  | bexp { ~a₁ ≤ ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => if n₁ ≤ n₂ then bexp { true } else bexp {false}
    | a₁', a₂' => bexp { ~a₁' ≤ ~a₂' }
  | bexp { ~a₁ > ~a₂ } =>
    match a₁.foldConstants, a₂.foldConstants with
    | .num n₁, .num n₂ => if n₁ > n₂ then bexp { true } else bexp {false}
    | a₁', a₂' => bexp { ~a₁' > ~a₂' }
  | bexp { ¬ ~b₁ } =>
    match b₁.foldConstants with
    | bexp { true } => bexp { false }
    | bexp { false } => bexp { true }
    | b₁' => bexp { ¬ ~b₁' }
  | bexp { ~b₁ ∧ ~b₂ } =>
    match b₁.foldConstants, b₂.foldConstants with
    | bexp { true }, bexp { true } => bexp { true }
    | bexp { true }, bexp { false } => bexp { false }
    | bexp { false }, bexp { true } => bexp { false }
    | bexp { false }, bexp { false } => bexp { false }
    | b₁', b₂' => bexp { ~b₁' ∧ ~b₂' }

@[simp]
theorem Bexp.foldConstants_true : (bexp { true }).foldConstants = (bexp { true }) := rfl
@[simp]
theorem Bexp.foldConstants_false : (bexp { false }).foldConstants = (bexp { false }) := rfl

theorem Bexp.foldConstants_comp (a₁ a₂ : Aexp) :
    (∃ n₁ n₂, a₁.foldConstants = .num n₁ ∧ a₂.foldConstants = .num n₂) ∨
    (bexp {~a₁ = ~a₂}).foldConstants = (bexp {~a₁.foldConstants = ~a₂.foldConstants}) ∧
    (bexp {~a₁ ≠ ~a₂}).foldConstants = (bexp {~a₁.foldConstants ≠ ~a₂.foldConstants}) ∧
    (bexp {~a₁ ≤ ~a₂}).foldConstants = (bexp {~a₁.foldConstants ≤ ~a₂.foldConstants}) ∧
    (bexp {~a₁ > ~a₂}).foldConstants = (bexp {~a₁.foldConstants > ~a₂.foldConstants}) := by
  cases ha₁ : a₁.foldConstants with
  | num n₁ =>
    cases ha₂ : a₂.foldConstants with
    | num n₂ =>
      left
      exists n₁, n₂
    | _ =>
      simp [foldConstants, ha₁, ha₂]
  | _ => simp [foldConstants, ha₁]

theorem Bexp.foldConstants_unary (b : Bexp) :
    (b.foldConstants = (bexp { true }) ∨ b.foldConstants = (bexp { false })) ∨
    (bexp { ¬~b }).foldConstants = (bexp { ¬(~b.foldConstants)}) := by
  cases hb : b.foldConstants with
  | bool b' =>
    simp_all
  | _ =>
    simp [foldConstants, hb]

theorem Bexp.foldConstants_binary (b₁ : Bexp) (b₂ : Bexp) :
    ((b₁.foldConstants = (bexp { true }) ∨ b₁.foldConstants = (bexp { false })) ∧
     (b₂.foldConstants = (bexp { true }) ∨ b₂.foldConstants = (bexp { false }))) ∨
    (bexp {~b₁ ∧ ~b₂}).foldConstants = (bexp {~b₁.foldConstants ∧ ~b₂.foldConstants}) := by
  cases hb₁ : b₁.foldConstants with
  | bool b₁' =>
    cases hb₂ : b₂.foldConstants with
    | bool b₂' => simp_all
    | _ => simp [foldConstants, hb₁, hb₂]
  | _ => simp [foldConstants, hb₁]


```
```lean
example : (bexp { true ∧ ¬( false ∧ true) }).foldConstants = (bexp { true }) := by rfl
example : (bexp { (X = Y) ∧ ( 0 = (2 - (1 + 1))) }).foldConstants = (bexp { (X = Y) ∧ true }) := by rfl
```

::::full
To fold constants in a command, we simply apply the
appropriate folding functions on all embedded expressions.
::::

```lean
def Com.foldConstants (c : Com) : Com :=
  match c with
  | imp { skip } => imp { skip }
  | imp { x := ~a } => imp { x := ~a.foldConstants }
  | imp { c₁ ; c₂ } =>  imp { c₁.foldConstants ; c₂.foldConstants }
  | imp { if (b) { c₁ } else { c₂ }} =>
    match b.foldConstants with
    | bexp { true } => c₁.foldConstants
    | bexp { false } => c₂.foldConstants
    | b' => imp { if (b') {c₁.foldConstants} else { c₂.foldConstants}}
  | imp { while (b) {c}} =>
    match b.foldConstants with
    | bexp { true } => imp { while (true) { skip }}
    | bexp { false } => imp { skip }
    | b' => imp { while (b') {c.foldConstants}}

example :
  (imp {
    X := 4 + 5;
    Y := X - 3;
    if ((X - Y) = (2 + 4)) {skip} else {Y := 0};
    if (0 ≤ (4 - (2 - 1))) {Y := 0} else {skip};
    while (Y = 0) {X := X+1}
  }).foldConstants =
  (imp {
    X := 9;
    Y := X - 3;
    if ((X - Y) = 6) {skip} else {Y := 0};
    Y := 0;
    while (Y = 0) {X := X+1}
  }) := by rfl
```

## Soundness of Constant Folding

::::full
Now we need to show that what we've done is correct.
::::

::::full
Here's the proof for arithmetic expressions.
::::

```lean
theorem Aexp.foldConstants_sound : TransSound foldConstants := by
  intro a st
  induction a with
  | num n | id x => rfl
  | _ a₁ a₂ _ _ =>
    cases foldConstants_cases a₁ a₂ with
    | inl h =>
      obtain ⟨n₁, n₂, h₁, h₂⟩ := h
      simp_all [foldConstants]
    | inr h =>
      simp_all
```

An equivalent version using the {tactic}`fun_induction` tactic would look simpler:
```lean
theorem Aexp.foldConstants_sound' : TransSound foldConstants := by
  intro a st
  fun_induction foldConstants a <;> simp_all
```

:::::full
::::exercise (rating := 3) (manual := true) (optional := true) (name := "fold_bexp_Eq_informal")
Here is an informal proof of the `eq` case of the soundness
argument for boolean expression constant folding.  Read it
carefully and compare it to the formal proof that follows.  Then
fill in the `le` case of the formal proof (without looking at the
`eq` case, if possible).

_Theorem_: The constant folding function for booleans,
`fold_constants_bexp`, is sound.

_Proof_: We must show that `b` is equivalent to `fold_constants_bexp b`,
for all boolean expressions `b`.  Proceed by induction on `b`.  We
show just the case where `b` has the form `a₁ = a₂`.

In this case, we must show
```
(imp { a₁ = a₂ }).eval st = (fold_constants_bexp (imp { a₁ = a₂ })).eval st
```

There are two cases to consider:

- First, suppose `fold_constants_aexp a₁ = imp { n₁ }` and
  `fold_constants_aexp a₂ = imp { n₂ }` for some `n₁` and `n₂`.

  In this case, we have

```
  fold_constants_bexp (imp { a₁ = a₂ }) = if (n₁ = n₂) then imp { true } else imp { false }
```

  and

```
(imp {a₁ = a₂}).eval st = a₁.eval st = a₂.eval st.
```

  By the soundness of constant folding for arithmetic
  expressions (`fold_constants_aexp_sound`), we know

```
           a₁.eval st
         = (fold_constants_aexp a₁).eval st
         = (imp { n₁ }).eval st
         = n₁
```

  and

```
           a₂.eval st
         = (fold_constants_aexp a₂).eval st
         = (imp { n₂ }).eval st
         = n₂
```

  so

```
          imp { a₁ = a₂ }.eval st
         = (aeval a₁) = (aeval a₂)
         = n₁ = n₂
```

      Also, it is easy to see (by considering the cases `n₁ = n₂` and
      `n₁ ≠ n₂` separately) that
```
          (if n₁ = n₂ then (imp { true }) else (imp { false }) ).eval st
         = if n₁ = n₂ then imp { true }.eval st else imp { false }.eval st
         = if n₁ = n₂ then true else false
         = n₁ = n₂
```
      So
```
           ((imp { a₁ = a₂ })).eval st
         = n₁ = n₂.
         = (if n₁ = n₂ then (imp { true }) else (imp { false }) ).eval st,
```
       as required.

     - Otherwise, one of `fold_constants_aexp a₁` and
       `fold_constants_aexp a₂` is not a constant.  In this case, we
       must show
```
           imp { a₁ = a₂ }.eval st
         = beval st (<{ (fold_constants_aexp a₁) =
                         (fold_constants_aexp a₂) }>),
```
       which, by the definition of {name}`Bexp.eval`, is the same as showing
```
           a₁.eval st = a₂.eval st
         = ((fold_constants_aexp a₁)) =.eval st
                   ((fold_constants_aexp a₂))..eval st
```
       But the soundness of constant folding for arithmetic
       expressions (`fold_constants_aexp_sound`) gives us
```
         a₁ = (fold_constants_aexp a₁).eval st
         a₂ = (fold_constants_aexp a₂),.eval st
```
       completing the case.

```lean
theorem fold_constants_bexp_sound : Bexp.TransSound Bexp.foldConstants := by
  sorry
/- Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* true and false are immediate
    try reflexivity.
  - (* BEq
    simpl.
    remember (fold_constants_aexp a₁) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a₂) as a₂' eqn:Heqa2'.
    replace a₁.eval st with a1'.eval st by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace a₂.eval st with a₂'.eval st by
       (subst a₂'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a₂'; try reflexivity.
    (* The only interesting case is when both a₁ and a₂
       become constants after folding
      simpl. destruct (n = n0); reflexivity.
  - (* BNeq
    simpl.
    remember (fold_constants_aexp a₁) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a₂) as a₂' eqn:Heqa2'.
    replace a₁.eval st with a1'.eval st by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace a₂.eval st with a₂'.eval st by
       (subst a₂'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a₂'; try reflexivity.
    (* The only interesting case is when both a₁ and a₂
       become constants after folding
      simpl. destruct (n = n0); reflexivity.
  - (* BLe
    (* ADMIT
    simpl.
    remember (fold_constants_aexp a₁) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a₂) as a₂' eqn:Heqa2'.
    (* a slightly alternative approach using asserts:
    assert a₁ = a1'.eval st as H1. {.eval st
      subst a1'. apply fold_constants_aexp_sound. }
    assert a₂ = a₂'.eval st as H2. {.eval st
      subst a₂'. apply fold_constants_aexp_sound. }
    rewrite H1. rewrite H2.
    destruct a1'; destruct a₂'; try reflexivity.
      (* Again, the only interesting case is when both a₁ and a₂
          become constants after folding
      simpl. destruct (n ≤ n0); reflexivity.
    (* /ADMIT
  - (* BGt
    (* ADMIT
    simpl.
    remember (fold_constants_aexp a₁) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a₂) as a₂' eqn:Heqa2'.
    (* a slightly alternative approach using asserts:
    assert a₁ = a1'.eval st as H1. {.eval st
      subst a1'. apply fold_constants_aexp_sound. }
    assert a₂ = a₂'.eval st as H2. {.eval st
      subst a₂'. apply fold_constants_aexp_sound. }
    rewrite H1. rewrite H2.
    destruct a1'; destruct a₂'; try reflexivity.
      (* Again, the only interesting case is when both a₁ and a₂
          become constants after folding
      simpl. destruct (n ≤ n0); reflexivity.
    (* /ADMIT
  - (* BNot
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd
    simpl.
    remember (fold_constants_bexp b₁) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b₂) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
(* ADMITTED
Qed.
(* /ADMITTED  -/
```
::::
:::::

:::::full
::::exercise (rating := 3) (name := "fold_constants_com_sound") (manual := true) (optional := true)
Complete the `while` case of the following proof.

```lean
theorem fold_constants_com_sound : Com.TransSound Com.foldConstants := by sorry
/- Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* skip  apply refl_cequiv.
  - (* :=  apply CAsgn_congruence.
              apply fold_constants_aexp_sound.
  - (* ;  apply CSeq_congruence; assumption.
  - (* if
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          [fold_constants_bexp_sound].)
    + (* b always true
      apply trans_cequiv with c₁; try assumption.
      apply if_true; assumption.
    + (* b always false
      apply trans_cequiv with c₂; try assumption.
      apply if_false; assumption.
  - (* while
    (* ADMITTED
    assert (bequiv b (fold_constants_bexp b)).
    { (* Pf of assertion  apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      (* Again, the cases where [fold_constants_com] doesn't change
          the test or don't change the loop body follow from the IH
          and [fold_constants_bexp_sound]
      try (apply CWhile_congruence; assumption).
    + (* b always true
      apply while_true; assumption.
    + (* b always false
      apply while_false; assumption.  Qed.
(* /ADMITTED -/
```
::::
:::::

# Soundness of (0 + n) Elimination, Redux

:::suppressPreviousHeaderWhenTerse
:::

:::::full

::::exercise (rating := 4) (name := "optimize0plus_var") (optional := true)
Recall the definition `optimize0plus` from the {ref "Slang"}[Slang] chapter:

```
def optimize0plus (a : Aexp) : Aexp :=
  match a with
  | num   n          => num n
  | plus  (num 0) e₂ => optimize0plus e₂
  | plus  e₁      e₂ => plus  (optimize0plus e₁) (optimize0plus e₂)
  | minus e₁      e₂ => minus (optimize0plus e₁) (optimize0plus e₂)
  | mult  e₁      e₂ => mult  (optimize0plus e₁) (optimize0plus e₂)
```

Note that this function is defined over the old version of `Aexp`s,
without states.

Write a new version of this function that deals with variables (by
leaving them alone), plus analogous ones for `Bexp`s and commands:

```
Aexp.optimize0plus
Bexp.optimize0plus
Com.optimize0plus
```

```lean
def Aexp.optimize0plus (a : Aexp) : Aexp := solution!(
  match a with
  | Aexp.num n => Aexp.num n
  | Aexp.id x => Aexp.id x
  | (aexp { 0 + ~a₂ }) => Aexp.optimize0plus a₂
  | (aexp { ~a₁ + ~a₂ }) => (aexp { ~(Aexp.optimize0plus a₁) + ~(Aexp.optimize0plus a₂) })
  | (aexp { ~a₁ - ~a₂ }) => (aexp { ~(Aexp.optimize0plus a₁) - ~(Aexp.optimize0plus a₂) })
  | (aexp { ~a₁ * ~a₂ }) => (aexp { ~(Aexp.optimize0plus a₁) * ~(Aexp.optimize0plus a₂) })
)

def Bexp.optimize0plus (b : Bexp) : Bexp := solution!(
  match b with
  | (bexp { true })        => (bexp { true })
  | (bexp { false })       => (bexp { false })
  | (bexp { ~a₁ = ~a₂ })  => (bexp { ~(Aexp.optimize0plus a₁) =  ~(Aexp.optimize0plus a₂) })
  | (bexp { ~a₁ ≠ ~a₂ })  => (bexp { ~(Aexp.optimize0plus a₁) ≠ ~(Aexp.optimize0plus a₂) })
  | (bexp { ~a₁ ≤ ~a₂ }) => (bexp { ~(Aexp.optimize0plus a₁) ≤ ~(Aexp.optimize0plus a₂) })
  | (bexp { ~a₁ > ~a₂ })  => (bexp { ~(Aexp.optimize0plus a₁) >  ~(Aexp.optimize0plus a₂) })
  | (bexp { ¬ ~b₁ })     => (bexp { ¬ ~(Bexp.optimize0plus b₁) })
  | (bexp { ~b₁ ∧ ~b₂ }) => (bexp { ~(Bexp.optimize0plus b₁) ∧ ~(Bexp.optimize0plus b₂) })
)

def Com.optimize0plus (c : Com) : Com := solution!(
match c with
| (imp { skip })                     => (imp { skip })
| (imp { x := ~a })                   => (imp { x := ~(Aexp.optimize0plus a) })
| (imp { c₁ ; c₂ })                  => imp { ~(Com.optimize0plus c₁) ; ~(Com.optimize0plus c₂) }
| (imp { if (b) {c₁} else {c₂} }) =>
    imp { if (~(Bexp.optimize0plus b)) {~(Com.optimize0plus c₁)} else {~(Com.optimize0plus c₂)} }
| (imp { while (b) {c₁} })         => imp { while (~(Bexp.optimize0plus b))
                                        {~(Com.optimize0plus c₁)} }
)
```

```lean
example :
    Com.optimize0plus
       (imp { while (X ≠ 0) { X := 0 + X - 1 } }) =
    (imp { while (X ≠ 0) { X := X - 1 } }) := by
  solution!
    rfl
```

Prove that these three functions are sound, as we did for
`foldConstants`.  Make sure you use the congruence lemmas in the
proof for {name}`Com.optimize0plus` - otherwise it will be _long_!

```lean
theorem optimize0plus_aexp_sound: Aexp.TransSound Aexp.optimize0plus := by sorry
/- Proof.
  (* ADMITTED
  unfold atrans_sound, aequiv.
  intros a st.
  induction a;
    (* Aexp.num and Aexp.id are immediate by definition
    try (reflexivity);
    (* AMinus and AMult are immediate by IH
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - (* APlus
    destruct a₁;
    (* everything but Aexp.num and Aexp.id follow from the IH
    try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + (* Aexp.num
      simpl. rewrite IHa2.
      destruct n as [| n'].
      * (* n = 0
        apply add_0_l.
      * (* n = S n'
        simpl. reflexivity.
    + (* Aexp.id
      simpl. rewrite IHa2. reflexivity.  Qed.
(* /ADMITTED -/

theorem optimize0plus_bexp_sound: Bexp.TransSound Bexp.optimize0plus := by sorry
/-  (* ADMITTED
  unfold btrans_sound, bequiv.
  intros b st. induction b; simpl;
               try reflexivity;
               try (rewrite IHb1; rewrite IHb2; reflexivity);
               try (rewrite <- optimize0plus_aexp_sound;
                    rewrite <- optimize0plus_aexp_sound;
                    reflexivity).
  - (* BNot
    rewrite IHb. reflexivity.  Qed.
(* /ADMITTED -/

theorem optimize0plus_com_sound: Com.TransSound Com.optimize0plus := by sorry
/-
  (* ADMITTED
  unfold ctrans_sound, cequiv.
  intros c.
  induction c;
  intros st st'; simpl.
  - (* skip
    apply refl_cequiv.
  - (* :=
    apply CAsgn_congruence.
    apply optimize0plus_aexp_sound.
  - (* ;
    apply CSeq_congruence; unfold cequiv.
    + apply IHc1.
    + apply IHc2.
  - (* if
    apply CIf_congruence; unfold cequiv.
    + apply optimize0plus_bexp_sound.
    + apply IHc1.
    + apply IHc2.
  - (* while
    apply CWhile_congruence; unfold cequiv.
    + apply optimize0plus_bexp_sound.
    + apply IHc.  Qed.
(* /ADMITTED
(* GRADE_THEOREM 2: optimize0plus_com_sound -/
```

Finally, let's define a compound optimizer on commands that first
folds constants (using {name}`Com.foldConstants`) and then eliminates
`0 + n` terms (using{name}`Com.optimize0plus`).

```lean
def optimizer (c : Com) := Com.optimize0plus (Com.foldConstants c)
```

Prove that this optimizer is sound.

```lean
theorem optimizer_sound : Com.TransSound optimizer := by sorry
 /- (* ADMITTED
  unfold ctrans_sound. unfold optimizer.
  intros c.
  apply trans_cequiv with (fold_constants_com c).
  - apply fold_constants_com_sound. -/
```
::::
:::::

# Proving Inequivalence

Next, let's look at some programs that are _not_ equivalent.

Suppose that `c₁` is a command of the form

```
  X := a₁; Y := a₂
```

and `c₂` is the command

```
       X := a₁; Y := a₂'
```

where `a₂'` is formed by substituting `a₁` for all occurrences
of `X` in `a₂`.

For example, `c₁` and `c₂` might be:

```
       c₁  =  (X := 42 + 53;
               Y := Y + X)
       c₂  =  (X := 42 + 53;
               Y := Y + (42 + 53))
```

Clearly, this _particular_ `c₁` and `c₂` are equivalent.  Is this
true in general?

:::full
We will see in a moment that it is not, but it is worthwhile
to pause, now, and see if you can find a counter-example on your
own.
:::

More formally, here is the function that substitutes an arithmetic
expression `u` for each occurrence of a given variable `x` in
another expression `a`:

```lean
def Aexp.subst (x : String) (u : Aexp) (a : Aexp) : Aexp :=
  match a with
  | Aexp.num n       =>
      Aexp.num n
  | Aexp.id x'       =>
      if x = x' then u else Aexp.id x'
  | (aexp { ~a₁ + ~a₂ })  =>
      (aexp { ~(Aexp.subst x u a₁) + ~(Aexp.subst x u a₂) })
  | (aexp { ~a₁ - ~a₂ }) =>
      (aexp { ~(Aexp.subst x u a₁) - ~(Aexp.subst x u a₂) })
  | (aexp { ~a₁ * ~a₂ })  =>
      (aexp { ~(Aexp.subst x u a₁) * ~(Aexp.subst x u a₂) })

example :
  Aexp.subst X (aexp { 42 + 53 })  (aexp { Y + X })
  = (aexp {  Y + (42 + 53) }) := by rfl
```

And here is the property we are interested in, expressing the
claim that commands `c₁` and `c₂` as described above are
always equivalent.

```lean
def SubstEquivProperty : Prop := ∀ (x₁ x₂ : String) (a₁ a₂ : Aexp),
  (imp { x₁ := a₁; x₂ := a₂ }) ≃
  (imp { x₁ := a₁; x₂ := ~(Aexp.subst x₁ a₁ a₂) })
```


Sadly, the property does _not_ always hold.

Here is a counterexample:
```
  X := X + 1; Y := X
```

If we perform the substitution, we get

```
  X := X + 1; Y := X + 1
```

which clearly isn't equivalent.

```lean
theorem subst_inequiv : ¬ SubstEquivProperty := by sorry
/-
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that [subst_equiv_property]
     holds allows us to prove that these two programs are
     equivalent...
  remember <{ X := X + 1;
              Y := X }>
      as c₁.
  remember <{ X := X + 1;
              Y := X + 1 }>
      as c₂.
  assert (cequiv c₁ c₂) by (subst; apply Contra).
  clear Contra.

  (* ... allows us to show that the command `c₂` can terminate
     in two different final states:
        st1 = (Y →ₜ 1 ; X →ₜ 1)
        st2 = (Y →ₜ 2 ; X →ₜ 1).
  remember (Y →ₜ 1 ; X →ₜ 1) as st1.
  remember (Y →ₜ 2 ; X →ₜ 1) as st2.
  assert (H1 : empty_st =[ c₁ ]=> st1);
  assert (H2 : empty_st =[ c₂ ]=> st2);
  try (subst;
       apply E_Seq with (st' := (X →ₜ 1));
       apply E_Asgn; reflexivity).
  clear Heqc1 Heqc2.

  apply H in H1.
  clear H.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction.
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c₂ empty_st); assumption).
  clear H1 H2.

  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. discriminate. Qed.
-/
```

:::::full
::::exercise (rating := 4) (name := "better_subst_equiv") (optional := true)

The equivalence we had in mind above was not complete nonsense --
in fact, it was actually almost right.  To make it correct, we
just need to exclude the case where the variable `X` occurs in the
right-hand side of the first assignment statement.

```lean
inductive VarNotUsedInAexp (x : String) : Aexp → Prop where
  | num {n : Nat} : VarNotUsedInAexp x (Aexp.num n)
  | id {y : String} (h : x ≠ y) : VarNotUsedInAexp x (Aexp.id y)
  | plus {a₁ a₂ : Aexp}
      (h₁ : VarNotUsedInAexp x a₁)
      (h₂ : VarNotUsedInAexp x a₂) :
      VarNotUsedInAexp x ((aexp { ~a₁ + ~a₂ }))
  | minus {a₁ a₂ : Aexp}
      (h₁ : VarNotUsedInAexp x a₁)
      (h₂ : VarNotUsedInAexp x a₂) :
      VarNotUsedInAexp x ((aexp { ~a₁ - ~a₂ }))
  | mult {a₁ a₂ : Aexp}
      (h₁ : VarNotUsedInAexp x a₁)
      (h₂ : VarNotUsedInAexp x a₂) :
      VarNotUsedInAexp x ((aexp { ~a₁ * ~a₂ }))
```

```lean
theorem Aexp.eval_weakening {x : String} {st : State} {a : Aexp} {ni : Nat}
  (h : VarNotUsedInAexp x a) :
  a.eval (x →ₜ ni ; st) = a.eval st := by sorry
/- Proof.
  (* ADMITTED
  intros x st a.
  induction a; intros nx Hx;
    (* the binary operators follow from the IH
    try (simpl; inversion Hx; subst;
         rewrite IHa1; try assumption;
         rewrite IHa2; try assumption;
         reflexivity).
  - (* Aexp.num
    reflexivity.
  - (* Aexp.id
    inversion Hx; subst. simpl.
    apply t_update_neq. assumption. Qed.
  (* /ADMITTED -/
```

Using `VarNotUsedInAexp`, formalize and prove a correct version
of `SubstEquivProperty`.

:::solution
```lean
theorem aeval_subst {x : String} {st : State} {a₁ a₂ : Aexp}
  (h : VarNotUsedInAexp x a₁) :
  a₂.eval (x →ₜ a₁.eval st ; st) = (Aexp.subst x a₁ a₂).eval (x →ₜ a₁.eval st ; st) := by sorry
/- Proof.
  intros x st a₁ a₂ Hi.
  generalize dependent st.
  induction a₂ as [| x' | | | ]; intros st;
    (* operator cases follow from the IH
    try (simpl; rewrite → IHa2_1; rewrite → IHa2_2; reflexivity).
  - (* Aexp.num
    reflexivity.
  - (* Aexp.id
    unfold Aexp.subst.
    destruct (String.eqb_spec x x') as [H | H].
    + (* x = x'
      subst x'.
      rewrite aeval_weakening with (a := a₁); try assumption.
      simpl. rewrite t_update_eq. reflexivity.
    + (* x ≠ x'
      reflexivity.  Qed. -/

theorem subst_equiv {x₁ x₂ : String} {a₁ a₂ : Aexp}
  (h : VarNotUsedInAexp x₁ a₁) :
  imp { x₁ := a₁; x₂ := a₂ } ≃
  imp { x₁ := a₁; x₂ := ~(Aexp.subst x₁ a₁ a₂)} := by sorry
/- Proof.
  unfold cequiv. intros x₁ x₂ a₁ a₂ Hi.
  split; intros Hce.
  ·
    inversion Hce; subst.
    apply E_Seq with st'0; try assumption.
    inversion H4; subst. apply E_Asgn.
    inversion H1; subst. symmetry. apply aeval_subst.
    assumption.
  ·
    inversion Hce; subst.
    apply E_Seq with st'0.
    + assumption.
    + inversion H4; subst. apply E_Asgn.
      inversion H1; subst. apply aeval_subst.
      assumption.  Qed. -/
```
:::
::::
:::::

:::::full
::::exercise (rating := 3) (name := "inequiv_exercise") (manual := true) (optional := true)
Prove that an infinite loop is not equivalent to `skip`.

```lean
theorem inequiv_exercise:
  ¬ (imp { while (true) {skip} } ≃ imp { skip }) := by sorry
/- Proof.
  (* ADMITTED
  intros Contra.
  assert (~(empty_st =[ while true do skip end ]=> empty_st)) as H.
  { apply while_true_nonterm. apply refl_bequiv. }
  apply H.
  apply (Contra empty_st empty_st).
  apply E_Skip. Qed.
(* /ADMITTED -/
```
::::
:::::

# Extended Exercise: Nondeterministic Imp

:::suppressPreviousHeaderWhenTerse
:::

:::::full
As we have seen (in theorem `ceval_deterministic` in the `Imp`
chapter), Imp's evaluation relation is deterministic.  However,
_non_-determinism is an important part of the definition of many
real programming languages. For example, in many imperative
languages (such as C and its relatives), the order in which
function arguments are evaluated is unspecified: the program
fragment

```
  x = 0;
  f(++x, x)
```

might call `f` with arguments `(1, 0)` or `(1, 1)`, depending how
the compiler chooses to order things.  This can be a little
confusing for programmers, but it gives compiler writers useful
freedom.

In this exercise, we will extend Imp with a simple
nondeterministic command and study how this change affects
program equivalence.  The new command has the syntax `havoc X`,
where `X` is an identifier. The effect of executing `havoc X` is
to assign an _arbitrary_ number to the variable `X`,
nondeterministically. For example, after executing the program:

```
  havoc Y;
  Z := Y * 2
```

the value of `Y` can be any number, while the value of `Z` is
twice that of `Y` (so `Z` is always even). Note that we are not
saying anything about the _probabilities_ of the outcomes -- just
that there are (infinitely) many different outcomes that can
possibly happen after executing this nondeterministic code.

In a sense, a variable on which we do `havoc` roughly corresponds
to an uninitialized variable in a low-level language like C.  After
the `havoc`, the variable holds a fixed but arbitrary number.  Most
sources of nondeterminism in language definitions are there
precisely because programmers don't care which choice is made (and
so it is good to leave it open to the compiler to choose whichever
will run faster).

We call this new language _Himp_ ("Imp extended with `havoc`").

```lean
namespace Himp
```

To formalize Himp, we first add a clause to the definition of
commands.

```lean
inductive Com : Type where
  | skip : Com
  | asgn : String → Aexp → Com
  | seq : Com → Com → Com
  | cond : Bexp → Com → Com → Com
  | whileDo : Bexp → Com → Com
  | havoc : String → Com  --  <--- NEW
```
:::details "Notation encoding: commands, macro rules"
```lean
namespace Com

/-- Assignment -/
syntax:max "havoc" ppHardSpace ident : imp_com

open Lean

scoped macro_rules
  | `(imp { $s }) => do
    let stx ← match s with
      | `(imp_com| skip) => ``(Com.skip)
      | `(imp_com| havoc $x:ident) => ``(Com.havoc $x)
      | `(imp_com| $x:ident) => ``(($x : Com))
      | `(imp_com| $c₁ ; $c₂) =>
        ``(Com.seq (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| $x:ident := $a) =>
        ``(Com.asgn $x (aexp {$a}))
      | `(imp_com| if ($b) {$c₁} else {$c₂}) =>
        ``(Com.cond (bexp {$b}) (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| while ($b) {$c}) =>
        ``(Com.whileDo (bexp {$b}) (imp {$c}))
      | `(imp_com| ~$c) => `(($c : Com))
      | _ => Macro.throwUnsupported
    return Imp.Elab.withSourceInfoOf s stx

end Com

open scoped Com

namespace Delab
open Lean PrettyPrinter Imp.Delab

@[app_unexpander Com.havoc]
def unexpandComHavoc : Unexpander
  | `($_ $x:ident) => `(imp { havoc $x:ident })
  | _ => throw ()

attribute [app_unexpander Com.skip] unexpandComSkip
attribute [app_unexpander Com.asgn] unexpandComAsgn
attribute [app_unexpander Com.seq] unexpandComSeq
attribute [app_unexpander Com.cond] unexpandComCond
attribute [app_unexpander Com.whileDo] unexpandComWhileDo

end Delab
```

```lean
/-- info: imp {havoc X} : Com -/
#guard_msgs in
#check imp { havoc X }
```
:::

::::exercise (rating := 2) (name := "himp_eval") (manual := true) (optional := true)
Now, we must extend the operational semantics. We have provided
a template for the `Com.EvalR` relation below, specifying the big-step
semantics. What rule(s) must be added to the definition of `Com.EvalR`
to formalize the behavior of the `havoc` command?

```lean
inductive Com.EvalR : Com → State → State → Prop where
  | skip {st : State} : EvalR (imp {skip}) st st
  | asgn {st : State} {a : Aexp} {n : Nat} {x : Ident} (h : a.eval st = n) :
      EvalR (imp {x := a}) st (x →ₜ n ; st)
  | seq {c₁ c₂ : Com} {st st' st'' : State} (h₁ : EvalR c₁ st st') (h₂ : EvalR c₂ st' st'') :
      EvalR (imp {c₁; c₂}) st st''
  | ifTrue {st st' : State} {b : Bexp} {c₁ c₂ : Com} (hb : b.eval st = true)
      (hc : EvalR c₁ st st') :
      EvalR (imp {if (b) {c₁} else {c₂}}) st st'
  | ifFalse {st st' : State} {b : Bexp} {c₁ c₂ : Com} (hb : b.eval st = false)
      (hc : EvalR c₂ st st') :
      EvalR (imp {if (b) {c₁} else {c₂}}) st st'
  | whileFalse {b : Bexp} {st : State} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {while (b) {c}}) st st
  | whileTrue {st st' st'' : State} {b : Bexp} {c : Com} (hb : b.eval st = true)
      (hc : EvalR c st st') (hloop : Com.EvalR (imp {while (b) {c}}) st' st'') :
      EvalR (imp {while (b) {c}}) st st''
-- SOLUTION
  | havoc {st : State} {x : String} {n : Nat} :
      EvalR (imp {havoc x}) st (x →ₜ n ; st)
-- END SOLUTION
```

:::details "Notation encoding: commands"
```lean
open scoped HasEval

instance : HasEval Com State State where
  Eval := Com.EvalR

@[simp]
theorem Com.evalR_eq {c : Com} {st st' : State} :
    EvalR c st st' ↔ st =[ c ]=> st' := by rfl
```
:::


As a sanity check, the following claims should be provable for
your definition:

```lean
example : ∅ =[ havoc X ]=> (X →ₜ 0) := by
  solution!
    constructor
```

```lean
example : ∅ =[ skip; havoc Z ]=> (Z →ₜ 42) := by
  solution!
    apply Com.EvalR.seq; constructor; constructor
```

Finally, we repeat the definition of command equivalence from above:

```lean
def Com.Equiv (c₁ c₂ : Com) : Prop := ∀ (st st' : State),
  (st =[ c₁ ]=> st') ↔ (st =[ c₂ ]=> st')

instance : Equiv Com where
  equiv := Com.Equiv

@[simp]
theorem Com.equiv_notation {c₁ c₂ : Com} : c₁.Equiv c₂ ↔ c₁ ≃ c₂ := by rfl
@[simp]
theorem Com.equiv_def {c₁ c₂ : Com} : c₁ ≃ c₂ ↔
    ∀ {st st' : State}, (st =[ c₁ ]=> st') ↔ (st =[ c₂ ]=> st') := by rfl
```

Let's apply this definition to prove some nondeterministic
programs equivalent / inequivalent.
::::
:::::

:::::full
::::exercise (rating := 3) (name := "havoc_swap") (manual := true) (optional := true)
Are the following two programs equivalent?

```lean
def pXY := imp { havoc X ; havoc Y }

def pYX := imp { havoc Y; havoc X }
```

If you think they are equivalent, prove it. If you think they are
not, prove that.

:::solution
Note that this is proving something general, considering arbitrary
x and y, not just the (distinct) string constants X and Y; this is
why the case distinction is needed.

```lean
theorem pXY_approx_pYX {x y : String} {st st' : State}
  (h : st =[ havoc x; havoc y ]=> st') :
  st =[ havoc y; havoc x ]=> st' := by sorry
/-  intros x y st st' H.
  destruct (String.eqb_spec x y) as [Hid | Hid].
  - (* x = y
    subst.  assumption.
  - (* x ≠ y
    inversion H; subst; clear H.
    inversion H2; subst; clear H2.
    inversion H5; subst; clear H5.
    apply E_Seq with (st' := (y →ₜ n0 ; st)).
    + constructor.
    + rewrite t_update_permute.
      * constructor.
      * assumption.
Qed. -/
```
:::

```lean
theorem pXY_cequiv_pYX :
  (pXY ≃ pYX) ∨ ¬ (pXY ≃ pYX) := by
/- Hint: You may want to use `update_permute` at some point,
     in which case you'll probably be left with `X ≠ Y` as a
     hypothesis. You can use `contradiction to discharge this. -/
  solution!
    sorry
    /- left. intros st st'.
    split; apply pXY_approx_pYX; reflexivity. -/
```
::::
:::::

:::::full
::::exercise (rating := 4) (name := "havoc_copy") (optional := true)
Are the following two programs equivalent?

```lean
def ptwice :=
  (imp { havoc X; havoc Y })

def pcopy :=
  (imp { havoc X; Y := X })
```

If you think they are equivalent, then prove it. If you think they
are not, then prove that.  (Hint: You may find the {tactic}`have` tactic
useful.)

```lean
theorem ptwice_equiv_pcopy :
  (ptwice ≃ pcopy) ∨ ¬(ptwice ≃ pcopy) := by sorry
/- Proof. (* ADMITTED
  right. intro Hc. unfold cequiv in Hc.
  assert (empty_st =[ ptwice ]=> (Y →ₜ 1 ; X →ₜ 0)).
  - apply E_Seq with (X →ₜ 0); constructor.
  - rewrite Hc in H. inversion H. inversion H2. inversion H5. subst.
    clear -H13.
    simpl in H13. rewrite t_update_eq in H13.
  (* LATER: This trick with [f_equal] is non-evident but highly
     useful to process contradictory equalities on functions.
     See [p₃_p₄_inequiv] for a more drastic reduction in code.
    assert (H0 : n = 1).
    { apply (f_equal (fun st => st Y)) in H13.
      apply H13. }
    assert (H1 : n = 0).
    { apply (f_equal (fun st => st X)) in H13.
      apply H13. }
    rewrite H0 in H1. discriminate.
Qed.
(* /ADMITTED -/
```
::::
:::::

:::::full
The definition of program equivalence we are using here has some
subtle consequences on programs that may loop forever.  What
`Equiv` says is that the set of possible _terminating_ outcomes
of two equivalent programs is the same. However, in a language
with nondeterminism, like Himp, some programs always terminate,
some programs always diverge, and some programs can
nondeterministically terminate in some runs and diverge in
others. The final part of the following exercise illustrates this
phenomenon.
:::::

:::::full
::::exercise (rating := 4) (name := "p₁_p₂_term") (level := Advanced)
Consider the following commands:

```lean
def p₁ : Com :=
  imp {
    while (X = 0) {
       havoc Y;
       X := X + 1
    }
  }

def p₂ : Com :=
  imp{
    while (¬ (X = 0)) {
       skip
    }
  }

```

Intuitively, `p₁` and `p₂` have the same termination behavior:
either they loop forever, or they terminate in the same state they
started in.  We can capture the termination behavior of `p₁` and
`p₂` individually with these lemmas:

```lean
theorem p₁_may_diverge (st st' : State) (h : st[X] ≠ 0) :
  ¬ (st =[ p₁ ]=> st') := by
  solution!
    sorry
    /- Proof. (* ADMITTED
      intros. intros Hcontra.
      remember p₁ as p₁' eqn:Heqp₁'. remember st' as st'' eqn:Heqst''.
      induction Hcontra; inversion Heqp₁'.
      - (* E_WhileFalse  subst. simpl in H0.
        apply negb_false_iff in H0. apply eqb_eq in H0.
        apply H in H0. assumption.
      - (* E_WhileTrue  subst. apply IHHcontra2; try reflexivity.
        inversion Hcontra1. subst.
        inversion H3; subst. inversion H6; subst.
        rewrite t_update_eq. simpl. lia.
    Qed. -/
```

:::gradeTheorem 3 p₁_may_diverge
:::

```lean
theorem p₂_may_diverge (st st' : State) (h : st[X] ≠ 0) :
  ¬ (st =[ p₂ ]=> st') := by
  solution!
    sorry
/- (* ADMITTED
  intros. intros Hcontra.
  remember p₂ as p₂' eqn:Heqp₂'. remember st' as st'' eqn:Heqst''.
  induction Hcontra; inversion Heqp₂'.
  - (* E_WhileFalse  subst. simpl in H0.
    apply negb_false_iff in H0. apply eqb_eq in H0.
    apply H in H0. assumption.
  - (* E_WhileTrue  subst. apply IHHcontra2; try reflexivity.
    inversion Hcontra1. subst.
    assumption.
Qed. (* /ADMITTED -/
```

:::gradeTheorem 3 p₂_may_diverge
:::
::::
:::::

:::::full
::::exercise (rating := 4) (name := "p₁_p₂_equiv") (level := Advanced)
Use these two lemmas to prove that `p₁` and `p₂` are actually
equivalent.

```lean
theorem p₁_p₂_equiv : p₁ ≃ p₂ := by
  solution!
    sorry
    /- Proof. (* ADMITTED
      split; intros.
      - remember p₁ as p₁' eqn:Heqp₁'.
        destruct H; inversion Heqp₁'; subst.
        + (* E_WhileFalse  apply E_WhileFalse. assumption.
        + (* E_WhileTrue  apply p₁_may_diverge in H1.
          * inversion H1.
          * simpl in H. apply negb_true_iff in H. apply eqb_neq in H.
            inversion H0. subst. inversion H4. subst. inversion H7. subst.
            rewrite t_update_eq. simpl. lia.
      - remember p₂ as p₂' eqn:Heqp₂'.
        destruct H; inversion Heqp₂'; subst.
        + (* E_WhileFalse  apply E_WhileFalse. assumption.
        + (* E_WhileTrue  apply p₂_may_diverge in H1.
          * inversion H1.
          * simpl in H. apply negb_true_iff in H. apply eqb_neq in H.
            inversion H0. subst. assumption.
    Qed. (* /ADMITTED -/
```

:::gradeTheorem 6 p₁_p₂_equiv
:::

::::
:::::

:::::full
::::exercise (rating := 4) (name := "p₃_p₄_inequiv") (level := Advanced)
Prove that the following programs are _not_ equivalent.  (Hint:
What should the value of `Z` be when `p₃` terminates?  What about
`p₄`?)

```lean
def p₃ : Com :=
  imp {
    Z := 1;
    while (X ≠ 0) {
      havoc X;
      havoc Z
    }
  }

def p₄ : Com :=
  imp {
    X := 0;
    Z := 1
  }
```

:::solution
First, note that the programs `p₃` and `p₄` are not equivalent:
when `p₃` terminates, even though `X` definitely has value `0`,
`Z` might have any natural number as the value.
:::

```lean
theorem p₃_p₄_inequiv : ¬ (p₃ ≃ p₄) := by
  solution!
    sorry
   /- Proof. (* ADMITTED
      intros Hcontra.
      unfold cequiv in Hcontra.
      remember (X →ₜ 1) as st.
      assert (st =[ p₃ ]=> (Z →ₜ 0 ; X →ₜ 0 ; Z →ₜ 1 ; st)).
      - eapply E_Seq.
        + constructor. reflexivity.
        + simpl. eapply E_WhileTrue.
          * subst. reflexivity.
          * eapply E_Seq; constructor.
          * apply E_WhileFalse.
            reflexivity.
      - apply Hcontra in H.
        inversion H. subst.
        inversion H2. subst.
        inversion H5. subst.
        simpl in H6.
        apply (f_equal (fun st => st Z)) in H6.
        discriminate H6.
    Qed. (* /ADMITTED -/
```

:::gradeTheorem 6 p₃_p₄_inequiv
:::

::::
:::::



:::::full
::::exercise (rating := 5) (name := "p₅_p₆_equiv") (level := Advanced) (optional := true)
Prove that the following commands are equivalent.  (Hint: As
mentioned above, our definition of `Equiv` for Himp only takes
into account the sets of possible terminating configurations: two
programs are equivalent if and only if the set of possible terminating
states is the same for both programs when given a same starting state
`st`.  If `p₅` terminates, what should the final state be? Conversely,
is it always possible to make `p₅` terminate?)

```lean
def p₅ : Com :=
  imp {
    while (X ≠ 1) {
      havoc X
    }
  }

def p₆ : Com := imp { X := 1 }
```

:::solution
Programs `p₅` and `p₆` are equivalent although `p₅` may diverge,
while `p₆` always terminates. The definition we took for `Equiv`
cannot distinguish between these two scenarios. It accepts the two
programs as equivalent on the basis that: if `p₅` terminates it
produces the same final state as `p₆`, and there exists an
execution in which `p₅` terminates and does exactly as `p₆`.

There are two directions to the proof:

`→`: Observe that whenever `p₅` terminates, it does so with `X`
set to `1`, and no other variable changed. But this is exactly the
behavior of `p₆`. Thus given a pair of states `st` and `st'` and
that `st =[ p₅ ]=> st'`, the answer to the question
"Does `st =[ p₆ ]=> st'`?"  is "Yes".

`←` (and more controversially): Given that `st =[ p₆ ]=> st'` for
some `st` and `st'`, can we show that `st =[ p₅ ]=> st'`? Observe
that we can use the hypothesis to conclude that
`st' = (X →ₜ 1 ; st)`.
Is there some execution of `p₅` starting from `st` which also
ends up in `st'`? Yes!

Hence their equivalence.

```lean
theorem p₅_summary (st st' : State) (h : st =[ p₅ ]=> st') : st' = (X →ₜ 1 ; st) := by sorry
/- Proof.
  intros. remember p₅ as p₅' eqn:Heqp₅'.
  induction H; inversion Heqp₅'; subst.
  - (* E_WhileFalse
    simpl in H. apply negb_false_iff in H. apply eqb_eq in H.
    rewrite <- H. rewrite t_update_same. reflexivity.
  - (* E_WhileTrue
    apply IHceval₂ in Heqp₅'.
    inversion H0; subst.
    apply t_update_shadow. -/
```
:::

```lean
theorem p₅_p₆_equiv : p₅ ≃ p₆ := by
  solution!
    sorry
    /- Proof. (* ADMITTED
      split; intros.
      - (* →
        apply p₅_summary in H. subst. constructor. reflexivity.
      - (* <-  inversion H. subst.
        simpl. simpl in H.
        destruct ((st X) = 1) eqn:Heqb.
        + (* X = 1
          apply eqb_eq in Heqb.
          rewrite <- Heqb.
          rewrite t_update_same.
          apply E_WhileFalse. simpl. rewrite → Heqb.
          reflexivity.
        + (* X ≠ 1
          apply E_WhileTrue with (st' := (X →ₜ 1 ; st)).
          * simpl. rewrite Heqb. reflexivity.
          * constructor.
          * apply E_WhileFalse. reflexivity. -/
```
::::

```lean
end Himp
```
:::::

# Additional Exercises

:::suppressPreviousHeaderWhenTerse
:::

:::::full
::::exercise (rating := 3) (name := "swap_noninterfering_assignments") (optional := true)
(Hint: You may or may not - depending how you approach it - need
to use `ext` explicitly for this one.)

```lean
theorem swap_noninterfering_assignments (l₁ l₂ : String) (a₁ a₂ : Aexp)
  (hl : l₁ ≠ l₂)
  (h₁ : VarNotUsedInAexp l₁ a₂)
  (h₂ : VarNotUsedInAexp l₂ a₁) :
  imp { l₁ := a₁; l₂ := a₂ } ≃ imp { l₂ := a₂; l₁ := a₁ } := by
    solution!
      sorry
      /- Proof.
      (* ADMITTED
        assert (HS : forall l₁ l₂ a₁ a₂,
          l₁ ≠ l₂ →
          VarNotUsedInAexp l₁ a₂ →
          VarNotUsedInAexp l₂ a₁ →
          forall st st',
            st =[ l₁ := a₁; l₂ := a₂ ]=> st' →
            st =[ l₂ := a₂; l₁ := a₁ ]=> st').
        { intros l₁ l₂ a₁ a₂ Hneq HNE1 HNE2 st st' H.
          inversion H; subst. inversion H2; subst. inversion H5; subst.
          eapply E_Seq.
          - apply E_Asgn. reflexivity.
          - rewrite → (t_update_permute _ _ _ _ _ _ Hneq).
            replace (aeval (l₁ →ₜ a₁; st) a₂) with a₂.eval st..eval st
            + apply E_Asgn. apply aeval_weakening. apply HNE2.
            + symmetry. apply aeval_weakening. apply HNE1. }
        split; eauto.
      Qed. (* /ADMITTED -/
```
::::
:::::

:::::full
::::exercise (rating := 4) (name := "for_while_equiv") (optional := true)
This exercise extends the optional `add_for_loop` exercise from
the {ref "Imp"}[Imp] chapter, where you were asked to extend the language
of commands with C-style `for` loops.  Prove that the command:

```
for (c₁; b; c₂) {
  c₃
}
```

is equivalent to:

```
c₁;
while (b) {
  c₃;
  c₂
}
```
::::
:::::

:::::full
::::exercise (rating := 4) (name := "cApprox") (level := Advanced) (optional := true)
In this exercise we define an asymmetric variant of program
equivalence we call _program approximation_. We say that a
program `c₁` _approximates_ a program `c₂` when, for each of
the initial states for which `c₁` terminates, `c₂` also terminates
and produces the same final state. Formally, program approximation
is defined as follows:

```lean
def Approx (c₁ c₂ : Com) : Prop := forall (st st' : State),
  (st =[ c₁ ]=> st') → (st =[ c₂ ]=> st')
```

For example, the program `c₁`

```
while (X ≠ 1) {
  X := X - 1
}
```

approximates `c₂`: `X := 1`, but `c₂` does not approximate `c₁`
since `c₁` does not terminate when `X = 0` but `c₂` does.  If two
programs approximate each other in both directions, then they are
equivalent.

Find two programs `c₃` and `c₄` such that neither approximates
the other.

```lean
def c₃ : Com := solution!(imp { X := 1 })
def c₄ : Com := solution!(imp { X := 2 })
```

```lean
theorem c₃_c₄_different : ¬ (Approx c₃ c₄) ∧ ¬ (Approx c₄ c₃) := by
  solution!
    sorry
    /- Proof. (* ADMITTED
      unfold not, capprox; split; intros.

      - assert (empty_st =[ c₃ ]=> (X →ₜ 1)).
        + constructor. reflexivity.
        + apply H in H0. inversion H0; subst. simpl in H5.
          assert ((X →ₜ 2) X = 2).
          * reflexivity.
          * assert ((X →ₜ 1) X = 1).
            -- reflexivity.
            -- rewrite → H5 in H1. rewrite → H2 in H1. inversion H1.

      - assert (empty_st =[ c₄ ]=> (X →ₜ 2)).
        + constructor. reflexivity.
        + apply H in H0. inversion H0; subst. simpl in H5.
          assert ((X →ₜ 2) X = 2).
          * reflexivity.
          * assert ((X →ₜ 1) X = 1).
            -- reflexivity.
            -- rewrite → H5 in H2. rewrite → H1 in H2. inversion H2.
    Qed. (* /ADMITTED-/
```

Find a program `cMin` that approximates every other program.

```lean
def cMin : Com := solution!(imp { while (true) { skip } })

theorem cMin_minimal (c : Com) : Approx cMin c := by
  solution!
    sorry
    /- Proof. (* ADMITTED
      unfold capprox. intros.
      apply loop_never_stops in H.
      inversion H.
    Qed. (* /ADMITTED -/
```

Finally, find a non-trivial property which is preserved by
program approximation (when going from left to right).

```lean
def zprop (c : Com) : Prop := solution!(forall st, exists st', (st =[ c ]=> st'))
```

:::solution
Intuitively, `zprop` holds of programs that terminate on all
inputs.
:::

```lean
theorem zprop_preserving (c c' : Com) (hc : zprop c) (ha : Approx c c') : zprop c' := by
  solution!
    sorry
      /- Proof. (* ADMITTED
        unfold zprop, capprox. intros.
        specialize (H st). inversion H as `st'`.
        apply H0 in H1. exists st'. assumption.
      Qed. -/
```
::::
:::::
