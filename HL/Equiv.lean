import SFLMeta

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
open scoped MyGetElem
```

:::dev "Sati (satiscugcat)"
  At this point, the Rocq file provides instructions about using a new directory,
  making sure the project is set up properly, and also instructions about how to
  deal with the exercises. I am assuming these things are being moved to Intro.lean?
  I am excluding them for now.
:::


:::dev "Sati (satiscugcat)"

```
namespace Equiv

```
:::
# Behavioral Equivaleence
::::full

  In an earlier chapter, we investigated the correctness of a very
  simple program transformation: the `optimize_0plus` function.  The
  programming language we were considering was the first version of
  the language of arithmetic expressions -- with no variables -- so
  in that setting it was very easy to define what it means for a
  program transformation to be correct: it should always yield a
  program that evaluates to the same number as the original.

  To talk about the correctness of program transformations for the
  full Imp language -- in particular, assignment -- we need to
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
def Aexp.equiv (a₁ a₂ : Aexp) : Prop :=
  ∀ (st: State),
    a₁.eval st = a₂.eval st
```

```lean
def Bexp.equiv (b₁ b₂ : Bexp) : Prop :=
  ∀ (st: State),
    b₁.eval st = b₂.eval st
```

-- ::::full
-- Here are some simple examples of equivalences of arithmetic
-- and boolean expressions.
-- ::::

```lean
example : Aexp.equiv
          (aexp { X - X })
          (aexp { 0 }) :=
  by
    intros st
    simp
```


```lean
example : Bexp.equiv
          (bexp { X - X = 0 })
          (bexp { true }) :=
  by
    intros st
    simp
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
def Com.equiv (c₁ c₂: Com) : Prop :=
    ∀ (st st': State),
      (st =[ c₁ ]=> st') ↔ (st =[ c₂ ]=> st')
```

## Simple Examples

::::full
  For examples of command equivalence, let's start by looking at
  a trivial equivalence involving `skip`.
::::

```lean
theorem skip_left: ∀ c,
  Com.equiv
    (imp { skip; ~c })
    c := by
  workinclass!
    intros c st st'
    constructor <;> intro h
    case mp =>
      cases h with
      | seq _ _ _ _ _ h1 h2 =>
        cases h1 with
        | skip => assumption
    case mpr =>
      apply Com.EvalR.seq _ _ _ st
      · apply Com.EvalR.skip
      · assumption
```

:::dev "Sati (satiscugcat)"
Is the syntax of Imp settled? I find this really unintuitive.
:::
:::::exercise (rating := 2) (name:= "skip_right")
Prove that adding a `skip` _after_ a command also results in an
equivalent program.

```lean
theorem skip_right : ∀ c,
  Com.equiv
    (imp { ~c  skip; })
    c := by
  solution!(
    intros c st st'
    constructor <;> intro h
    case mp =>
      cases h with
      | seq _ _ _ _ _ h1 h2 =>
        cases h2 with
        | skip => assumption
    case mpr =>
      apply Com.EvalR.seq _ _ _ st'
      · assumption
      · apply Com.EvalR.skip
  )
```
:::::

::::full
Similarly, here is a simple equivalence that optimises `if`
commands.
::::

```lean
theorem if_true_simple: ∀ c₁ c₂,
  Com.equiv
    (imp {if (true) {~c₁} else {~c₂}})
    c₁ := by
  intro c₁ c₂ st st'
  constructor <;> intro h
  case mp =>
    cases h with
    | ifTrue => assumption
    | ifFalse => contradiction
  case mpr =>
    apply Com.EvalR.ifTrue
    · rfl
    · assumption
```

::::full
Of course, no programmer would write a conditional whose condition
is literally `true`.  (At least, no human programmer -- compilers
and macro preprocessors do this sort of thing internally all the
time!) But they might write one whose condition is _equivalent_ to
true:
::::
:::dev "Sati (satiscugcat)"
The to\_verso script seems to use `\[\]` blocks, but these seem to
cause problems with the tilde. Currently skipping them and just using
backticks.
:::
::::full
_Theorem_: If `b` is equivalent to `true`, then `if (~b) {~c₁}
else {~c₂}` is equivalent to `c₁`.
_Proof_:
 - (`->`) We must show, for all `st` and `st'`, that if
   `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'` then
   `st =[ c₁ ]=> st'`.

   Proceed by cases on the rules that could possibly have been
   used to show `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'`,
   namely `Com.EvalR.ifTrue` and `Com.EvalR.ifFalse`.

   - Suppose the final rule in the derivation of
     `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'` was `Com.EvalR.ifTrue`.
     We then have, by the premises of `Com.EvalR.ifTrue`, that
     `st =[ c₁ ]=> st'`. This is exactly what we set out to prove.

   - On the other hand, suppose the final rule in the derivation
     of `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'` was `Com.EvalR.ifFalse`.
     We then know that `b.eval st = false` and `st =[ c₂ ]=> st'`.

     Recall that `b` is equivalent to `true`, i.e., forall `st`,
     `b.eval st = (bexp {true}).eval st`.  In particular, this means
     that `b.eval st = true`, since `(bexp {true}).eval st = true`.  But
     this is a contradiction, since `Com.EvalR.ifFalse` requires that
     `b.eval st = false`.  Thus, the final rule could not have
     been `Com.EvalR.ifFalse`.

 - (`<-`) We must show, for all `st` and `st'`, that if
   `st =[ c₁ ]=> st'` then
   `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'`.

   Since `b` is equivalent to `true`, we know that `b.eval st` =
   `(bexp {true}).eval st = true` = `true`.  Together with the assumption that
   `st =[ c₁ ]=> st'`, we can apply `Com.EvalR.ifTrue` to derive
   `st =[ imp {if (~b) {~c₁} else {~c₂}} ]=> st'`.
::::

::::full
Here is the formal version of this proof:
::::

:::dev "Sati (satiscugcat)"
`if_true` causes a naming conflict, I don't know with what.
:::
```lean
theorem if_true_equiv: ∀ b c₁ c₂,
  Bexp.equiv b (bexp {true}) ->
  Com.equiv
    (imp {if (~b) {~c₁} else {~c₂}})
    c₁ := by
  intro b c₁ c₂ hb st st'
  constructor <;> intro h
  case mp =>
    cases h with
    | ifTrue => assumption
    | ifFalse _ _ _ _ _ hb' hc =>
      unfold Bexp.equiv at hb; simp at hb
      rw [hb] at hb'
      contradiction
  case mpr =>
    apply Com.EvalR.ifTrue <;> try assumption
    unfold Bexp.equiv at hb; dsimp at hb
    apply hb
```


:::::exercise (rating := 2) (name := "if_false_equiv")
```lean
theorem if_false_equiv: ∀ b c₁ c₂,
  Bexp.equiv b (bexp {false}) ->
  Com.equiv
    (imp {if (~b) {~c₁} else {~c₂}})
    c₂ := by
  solution!(
    intro b c₁ c₂ hb st st'
    constructor <;> intro h
    case mp =>
      cases h with
      | ifTrue _ _ _ _ _ hb' hc =>
        unfold Bexp.equiv at hb; dsimp at hb
        rw [hb] at hb'
        contradiction
      | ifFalse => assumption
    case mpr =>
      apply Com.EvalR.ifFalse <;> try assumption
      unfold Bexp.equiv at hb; dsimp at hb
      apply hb
  )
```
:::::


:::::exercise (rating := 3) (name := "swap_if_branches")
Show that we can swap the branches of an `if` if we also negate its
condition.

```lean
theorem swap_if_branches : ∀ b c₁ c₂,
  Com.equiv
    (imp {if (~b) {~c₁} else {~c₂}})
    (imp {if (¬ ~b) {~c₂} else {~c₁}}) := by
  solution!(
    intro b c₁ c₂ st st'
    constructor <;> intro h
    case mp =>
      cases h with
      | ifTrue _ _ _ _ _ hb hc =>
        apply Com.EvalR.ifFalse <;> try assumption
        simp_all
      | ifFalse _ _ _ _ _ hb hc =>
        apply Com.EvalR.ifTrue <;> try assumption
        simp_all
    case mpr =>
      cases h with
      | ifTrue _ _ _ _ _ hb hc =>
        apply Com.EvalR.ifFalse <;> try assumption
        simp_all
      | ifFalse _ _ _ _ _ hb hc =>
        apply Com.EvalR.ifTrue <;> try assumption
        simp_all
  )
```
:::::

::::full
For `while` loops, we can give a similar pair of theorems.  A loop
whose guard is equivalent to `false` is equivalent to `skip`,
while a loop whose guard is equivalent to `true` is equivalent to
`while (true) {skip;} end` (or any other non-terminating program).
::::

::::full
The first of these facts is easy.
::::

```lean
theorem while_false_equiv : ∀ b c,
  Bexp.equiv b (bexp {false}) ->
  Com.equiv
    (imp {while (~b) {~c}})
    (imp {skip;}) := by
  intro b c hb st st'
  constructor <;> intro h
  case mp =>
    cases h with
    | whileFalse => apply Com.EvalR.skip
    | whileTrue _ _ _ _ _ hb' hc hloop =>
      rw [hb] at hb'
      simp at hb'
  case mpr =>
    cases h with
    | skip =>
      apply Com.EvalR.whileFalse
      apply hb
```

:::::exercise (rating := 2) (name := "while_false_informal") (level:= Advanced) (manual:= true)
Write an informal proof of `while_false_equiv`.
:::::

::::full
To prove the second fact, we need an auxiliary lemma stating that
`while` loops whose guards are equivalent to `true` never
terminate.
::::

::::full
_Lemma_: If `b` is equivalent to `true`, then it cannot be
the case that `st =[ while (~b) {~c} ]=> st'`.

_Proof_: Suppose that `st =[ while (~b) {~c} ]=> st'`.  We show,
by induction on a derivation of `st =[ while (~b) {~c} ]=> st'`,
that this assumption leads to a contradiction. The only two cases
to consider are `Com.EvalR.whileFalse` and `Com.EvalR.whileTrue`; the others
are contradictory.

- Suppose `st =[ while (~b) {~c} ]=> st'` is proved using rule
  `Com.EvalR.whileFalse`.  Then by assumption `b.eval st = false`. But
  this contradicts the assumption that `b` is equivalent to
  `true`.

- Suppose `st =[ while (~b) {~c} ]=> st'` is proved using rule
  `Com.EvalR.whileTrue`.  We must have:

  1. `b.eval st = true`, and
  2. there is some `st₀` such that `st =[ c ] => st₀` and
     `st₀ =[ while (~b) {~c} ]=> st'`.
  3. Also, we are given an induction hypothesis saying that
     `st₀ =[ while (~b) {~c} ]=> st'` leads to a contradiction,

  We obtain a contradiction by 2 and 3.
::::

```lean
theorem while_true_nonterm : ∀ b c st st',
  Bexp.equiv b (bexp {true}) ->
  ¬ (st =[ while (~b) {~c} ]=> st') := by
  workinclass!
    intro b c st st' hb contra
    have key : ∀ (c': Com) (s s': State), (s =[ c' ]=> s') -> c' = (imp {while (~b) {~c}}) -> False :=
      by
        intro c' s s' hce
        induction hce with
        | whileFalse b' s0 c0 hb' =>
          intro heq; injection heq with beq ceq
          subst beq; rw [hb] at hb'
          simp at hb'
        | whileTrue s0 s0' s0'' b' c0 hb hc' hwhile ih1 ih2 => exact ih2
        | skip => simp
        | asgn => simp
        | seq => simp
        | ifTrue => simp
        | ifFalse => simp
    exact key (imp {while (~b) {~c}}) st st' contra (by rfl)
```
:::::exercise (rating := 2) (name := "while_true_nonterm_informal") (manual:= true)
Explain what the lemma `while_true_nonterm` means in English.
:::::
:::::exercise (rating := 2) (name := "while_true")
Prove the following theorem. _Hint_: You'll want to use
`while_true_nonterm` here.

```lean
theorem while_true : ∀ b c,
  Bexp.equiv b (bexp {true}) ->
  Com.equiv
    (imp {while (~b) {~c}})
    (imp {while (true) {skip;}}) := by
  solution!(
    intro b c beq st st'
    constructor
    case mp =>
      intro h
      apply False.elim
      exact while_true_nonterm b c st st' beq h
    case mpr =>
      intro h
      apply False.elim
      have bexp_equiv_refl : ∀ (b: Bexp), b.equiv b :=
        by
          intro b st
          rfl
      exact while_true_nonterm (bexp {true}) (imp {skip;}) st st' (bexp_equiv_refl (bexp {true})) h
  )
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
theorem loop_unrolling : ∀ b c,
  Com.equiv
    (imp {while (~b) {~c}})
    (imp {
      if (~b) {~c} else {skip;}
      while (~b) {~c}
    }) := by
  workinclass!
    intro b c st st'
    constructor <;> intro hce
    case mp =>
      cases hce with
      | whileFalse _ _ _ hb =>
        apply Com.EvalR.seq _ _ _ st
        · apply Com.EvalR.ifFalse <;> try assumption
          apply Com.EvalR.skip
        · apply Com.EvalR.whileFalse <;> try assumption
      | whileTrue _ st'' _ _ _ hb hc hloop =>
        apply Com.EvalR.seq _ _ _ st''
        · apply Com.EvalR.ifTrue <;> try assumption
        · assumption
    case mpr =>
      cases hce with
      | seq _ _ _ st'' _ h1 h2 =>
        cases h1 with
        | ifTrue _ _ _ _ _ hb hc =>
          apply Com.EvalR.whileTrue _ st'' <;> try assumption
        | ifFalse _ _ _ _ _ hb hc =>
          cases hc with
          | skip => assumption
```
:::dev "Sati (satiscugcat)"
Leaving out optional exercise `seq_assoc` for now.
:::

::::full
Proving program properties involving assignments is one place
where the fact that we are treating equality on program states
extensionally (e.g., `x →ₜ m[x] ; m` and `m` are equal maps) comes
in handy.
::::

:::dev "Sati (satiscugcat)"
I am not able to use `m[x]` syntax here for some reason? I have to use function application and then do some weird manipulation.
syntax.
:::
```lean
theorem identity_assignment : ∀ X,
  Com.equiv
    (imp {X := X;})
    (imp {skip;}) := by
  intro X st st'
  constructor <;> intro hce
  case mp =>
    cases hce with
    | asgn _ _ n _ h =>
      dsimp at h
      rw [← h, TotalMap.update_same]
      apply Com.EvalR.skip

  case mpr =>
    cases hce with
    | skip =>
      suffices st =[ X := X; ]=> X →ₜ st[X] ; st by
        simp only [TotalMap.update_same] at this
        exact this
      apply Com.EvalR.asgn
      simp
```

:::::exercise (rating := 2) (name := "assign_equiv")
```lean
theorem assign_equiv : ∀ (X : Ident) (a : Aexp),
  Aexp.equiv (aexp {X}) a ->
  Com.equiv
    (imp {skip;})
    (imp {X := ~a;}) := by
  solution!(
    intro X a aeq st st'
    constructor <;> intro hce
    case mp =>
      cases hce with
      | skip =>
        unfold Aexp.equiv at aeq
        dsimp at aeq
        suffices st =[ X:= ~a; ]=> X →ₜ st[X]; st by
          simp only [TotalMap.update_same] at this
          exact this
        apply Com.EvalR.asgn
        simp [aeq]
    case mpr =>
      cases hce with
      | asgn _ _ n _ h =>
        unfold Aexp.equiv at aeq
        dsimp at aeq
        rw [← h, ← aeq, TotalMap.update_same]
        apply Com.EvalR.skip
  )
```
:::::

:::dev "Sati (satiscugcat)"
Leaving out optional exercise `equiv_classes` for now.
:::

# Properties of Behavior Equivalence

::::full
We next consider some fundamental properties of program equivalence.
::::

## Behavioral Equivalence is an Equivalence

::::full
First, let's verify that the equivalences on `Aexp`s, `Bexp`s, and
`Com`s really are _equivalences_ -- ie, that they are reflexive,
symmetric, and transitive. These proofs are all easy.
::::

```lean
theorem Aexp.equiv.refl : ∀ (a : Aexp),
  a.equiv a := by
  intros a st
  rfl
```

```lean
theorem Aexp.equiv.sym : ∀ (a₁ a₂ : Aexp),
  a₁.equiv a₂ → a₂.equiv a₁ := by
  intro a₁ a₂ h st
  rw [h]
```

```lean
theorem Aexp.equiv.trans : ∀ (a₁ a₂ a₂ : Aexp),
  a₁.equiv a₂ → a₂.equiv a₃ → a₁.equiv a₃ := by
  intro a₁ a₂ a₃ h₁ h₂ st
  rw [h₁, h₂]
```


```lean
theorem Bexp.equiv.refl : ∀ (b : Bexp),
  b.equiv b := by
  intros b st
  rfl
```

```lean
theorem Bexp.equiv.sym : ∀ (b₁ b₂ : Bexp),
  b₁.equiv b₂ → b₂.equiv b₁ := by
  intro b₁ b₂ h st
  rw [h]
```

```lean
theorem Bexp.equiv.trans : ∀ (b₁ b₂ b₂ : Bexp),
  b₁.equiv b₂ → b₂.equiv b₃ → b₁.equiv b₃ := by
  intro b₁ b₂ b₃ h₁ h₂ st
  rw [h₁, h₂]
```


```lean
theorem Com.equiv.refl : ∀ (c : Com),
  c.equiv c := by
  intros c st st'
  rfl
```

```lean
theorem Com.equiv.sym : ∀ (c₁ c₂ : Com),
  c₁.equiv c₂ → c₂.equiv c₁ := by
  intro c₁ c₂ h st st'
  rw [h]
```

```lean
theorem Com.equiv.trans : ∀ (c₁ c₂ c₂ : Com),
  c₁.equiv c₂ → c₂.equiv c₃ → c₁.equiv c₃ := by
  intro c₁ c₂ c₃ h₁ h₂ st st'
  rw [h₁, h₂]
```
## Behavioral Equivalence is a Congruence

::::full

Less obviously, behavioral equivalence is also a _congruence_.
That is, the equivalence of two subprograms implies the
equivalence of the larger programs in which they are embedded:

             aequiv a a'
     -------------------------
     cequiv (x := a) (x := a')

          cequiv c1 c1'
          cequiv c2 c2'
     --------------------------
     cequiv (c1;c2) (c1';c2')

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
change -- i.e., the "proof burden" of a small change to a large
program is proportional to the size of the change, not the
program!
::::


```lean
theorem Com.congruence.asgn : ∀ x a a',
  Aexp.equiv a a' ->
  Com.equiv (imp {x := ~a;}) (imp {x := ~a';}) := by
  intro x a a' heqv st st'
  constructor <;> intro hce
  case mp =>
    cases hce with
    | asgn _  _ n _ h =>
      subst h; apply Com.EvalR.asgn
      rw [heqv]
  case mpr => 
    cases hce with
    | asgn _ _ n _ h =>
      subst h; apply Com.EvalR.asgn
      rw [heqv]
```

::::full
The congruence property for loops is a little more interesting,
since it requires induction.

_Theorem_: Equivalence is a congruence for `while` -- that is, if
`b` is equivalent to `b'` and `c` is equivalent to `c'`, then
`while (~b) {~c}` is equivalent to `while (~b') {~c'}`.

_Proof_: Suppose `b` is equivalent to `b'` and `c` is
equivalent to `c'`.  We must show, for every `st` and `st'`, that
`st =[ while (~b) {~c} ]=> st'` iff `st = while (~b') {~c'}
]=> st'`.  We consider the two directions separately.

  - (`->`) We show that `st =[ while (~b) {~c} ]=> st'` implies
    `st =[ while (~b') {~c'} ]=> st'`, by induction on a
    derivation of `st =[ while (~b) {~c} ]=> st'`.  The only
    nontrivial cases are when the final rule in the derivation is
    `Com.EvalR.whileFalse` or `Com.EvalR.whileTrue`.

      - `Com.EvalR.whileFalse`: In this case, the form of the rule gives us
        `beval st b = false` and `st = st'`.  But then, since
        `b` and `b'` are equivalent, we have `beval st b' =false`, 
        and `Com.EvalR.whileFalse` applies, giving us
        `st =[ while (~b') {~c'} ]=> st'`, as required.

      - `Com.EvalR.whileTrue`: The form of the rule now gives us `beval st b = true`, 
        with `st =[ c ]=> st'0` and `st'0 =[ while {~b} {~c} ]=> st'`
        for some state `st'0`, with the
        induction hypothesis `st'0 =[ while (~b') {~c'} ]=> st'`.

        Since `c` and `c'` are equivalent, we know that `st =[ c']=> st'0`.
        And since `b` and `b'` are equivalent,
        we have `beval st b' = true`.  Now `Com.EvalR.whileTrue` applies,
        giving us `st =[ while (~b') {~c'} ]=> st'`, as
        required.

  - (`<-`) Similar. 
::::
-- Extremely annoying proof that I was trying to get done.
-- ```lean
-- theorem Com.congruence.while : ∀ (b b': Bexp) (c c': Com),
--   b.equiv b' -> c.equiv c' ->
--   Com.equiv (imp {while (~b) {~c}}) (imp {while (~b') {~c'}}) := by
  
--   workinclass!
--   have A : ∀ (b b': Bexp) (c c': Com) (st st': State),
--              b.equiv b' -> c.equiv c' ->
--              st =[ while (~b) {~c} ]=> st' ->
--              st =[ while (~b') {~c'} ]=> st' := by
             
--              unfold Bexp.equiv; unfold Com.equiv
             
--              intro b b' c c' st st' hbe hce
             
--              have key: ∀ c0 st0 st0', c0 = (imp {while (~b) {~c}}) ->
--                        st0 =[ c0 ]=> st0' ->
--                        ∀ c'0, c'0 = (imp {while (~b') {~c'}}) ->
--                        c0.equiv c'0 -> 
--                        st0 =[ c'0 ]=> st0' := by
                  
--                   intro c0 st0 st0' c0eq hc0
--                   induction hc0 with
--                   | whileFalse b0 st0 c00 hb0 =>
--                     intro c'0 c'0eq ceq         
--                     injection c0eq with beq ceq; subst beq ceq
--                     rw [c'0eq]
--                     apply Com.EvalR.whileFalse; rw [<- hbe, hb0]
--                   | whileTrue s0 s0' s0'' b0 c00 hb0 hc00 hwhile ih1 ih2 =>
--                     -- apply ih2; assumption
--                     injection c0eq with beq ceq; subst beq ceq
--                     apply Com.EvalR.whileTrue _ s0'
--                     · sorry
--                     · sorry
--                     · apply ih2; rfl
--                   | skip => simp at c0eq
--                   | ifTrue => simp at c0eq
--                   | ifFalse => simp at c0eq
--                   | asgn => simp at c0eq
                  
--                   | _ => sorry
               
--              sorry
--   sorry
-- ```
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
