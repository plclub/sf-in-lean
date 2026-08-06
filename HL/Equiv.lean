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
    (imp {skip; ~c})
    c := 
  by
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


