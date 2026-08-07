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
      unfold Bexp.equiv at hb; simp at hb
      apply hb
```
