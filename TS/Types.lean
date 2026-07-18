import VersoManual
import VersoManual.InlineLean
import Illuminate
import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer
import SFLMeta.Bnf
import SFLMeta.Ignore
import SFLMeta.Save
import SFLMeta.Comment
import SFLMeta.Exercise
import SFLMeta.Grade
import SFLMeta.Hide
import SFLMeta.Instructors
import SFLMeta.Quiz
import SFLMeta.SlideBreak
import SFLMeta.Solution
import SFLMeta.Terse
import TS.Smallstep

open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "Types: Type Systems" =>
%%%
tag := "Types"
htmlSplit := .never
file := some "Types"
%%%

:::dev
mwhicks1: This chapter comes after Smallstep in PLF, which comes after Imp
and Hoare Logic. It defines its own typed language and does not use Imp; for
the generic relation vocabulary (`Relation`, `IsNormalForm`, `Deterministic`,
`Multi`) it imports the Smallstep chapter rather than re-inlining those
definitions. Its own language and `⟶`/`⟶*` notation live in a `TM` namespace
so they don't clash with Smallstep's when both chapters are in the book.
:::

:::instructors
This chapter is short, but chewy.  Although all the individual pieces
are reasonably simple and familiar, there are quite a few of them and
the way they fit together is a bit intricate, especially coming on top
of the Smallstep material, which many students also find a bit
challenging.

Spending an entire 80-minute class on this chapter feels about right.
Going through the proofs of progress and preservation very carefully,
at the board, was critical.  Doing the quizzes together is good -- a few
more quizzes would be better.

For this lecture, I (BCP) find it useful to make a physical 1-page
"cheat sheet" for students, containing:
  - syntax of terms
  - definition of values
  - canonical forms lemmas
  - definitions of typing and step relations
This makes it more fun to put proofs on the board because the class can
help.
:::

:::dev
SOONER: Beginning at the Types chapter, the text gets a bit sparse!

SOONER: The quizzes we have are pretty good, but the ones at the end of
the chapter are too hard to jump straight into -- we need something in
the middle.  (BCP 11/18: Actually, the ones at the end of the chapter
are OK, but it's disappointing that no property breaks!)

LATER: For consistency with the STLC definitions in future chapters, it
would be better and simpler to represent numbers by a simple nat, rather
than as strings of `succ` applied to `0` (which also introduces
subtleties that are really not the main point here).  But the present
formulation is not a big problem either.

LATER: Harper's lecture from the Milner symposium would make a good
support for this lecture.

LATER: There are a bunch of slides from earlier offerings of CIS500 that
might be wonderful additions to the TERSE notes.
  https://www.seas.upenn.edu/~cis500/cis500-f06/lectures/1002.pdf
  https://www.seas.upenn.edu/~cis500/cis500-f06/lectures/1004.pdf

LATER: There are some notational choices that need to be made
consistently throughout the rest of the notes: naming of inference
rules, naming of constructors, naming of syntactic categories, ...
:::

::::full
Our next major topic is _type systems_ -- static program analyses that
classify expressions according to the "shapes" of their results.  We'll
begin with a typed version of the simplest imaginable language, to
introduce the basic ideas of types and typing rules and the fundamental
theorems about type systems: _type preservation_ and _progress_.  In the
next chapter we'll move on to the _simply typed lambda-calculus_, which
lives at the core of every modern functional programming language
(including Lean!).
::::

:::terse
New topic: _type systems_
  - This chapter: a toy type system for a toy language
    - typing relation
    - _progress_ and _preservation_ theorems
  - Next chapter: _simply typed lambda-calculus_
:::

# Typed Arithmetic Expressions

::::full
To motivate the discussion of type systems, let's begin as usual with a
tiny toy language. We want it to have the potential for programs to go
wrong because of runtime type errors, so we endow it with two kinds of
data -- numbers and booleans -- where not every operation is defined on
both types of data. For example, program terms like `5 + true` and
`if 42 then 0 else 1` use undefined operator/data-type combinations.

The language definition is completely routine.
::::

:::terse
  - A simple toy language where expressions may fail with dynamic type
    errors
    - numbers (and arithmetic)
    - booleans (and conditionals)
  - This means we can write _stuck_ terms like `5 + true` and
    `if 42 then 0 else 1`.
:::

## Syntax

Here is the syntax of program terms, informally:

```
t ::= true | false | if t then t else t | 0 | succ t | pred t | iszero t
```

And here it is formally:

```lean
namespace TM

inductive Tm where
  | tru
  | fls
  | ite (c t e : Tm)
  | zero
  | succ (t : Tm)
  | pred (t : Tm)
  | isZero (t : Tm)
```

### Notation

::::full
Writing terms as raw constructors (`.ite .fls .zero (.succ .zero)`) gets
unreadable quickly.  We introduce a _concrete syntax_ so that a term can be
written inside `<{ … }>` -- for example `<{ if false then 0 else succ 0 }>` --
mirroring the informal grammar above.  A bare identifier is spliced as a Lean
term (so a variable `t` is written just `t`); `~e` escapes an arbitrary Lean
expression, and `( … )` groups.
::::

```lean
declare_syntax_cat tm
-- The keyword atoms (`true`/`false`/`succ`/`pred`/`iszero`) are parsed as bare
-- identifiers and dispatched in the macro below, rather than declared as
-- reserved symbols.  Reserving them would break ordinary Lean uses of
-- `true`/`false` and clash with the constructor/case names `succ`, `pred`.
syntax:max num : tm
syntax:max ident : tm
syntax:75 ident ppHardSpace tm:76 : tm
syntax:max "(" tm ")" : tm
syntax:max "~" term:max : tm
syntax:50 "if " tm:51 " then " tm:51 " else " tm:51 : tm
syntax:max "<{ " tm " }>" : term

open Lean in
macro_rules
  | `(<{ $n:num }>) =>
      if n.getNat == 0 then `(Tm.zero)
      else Macro.throwErrorAt n "the only numeric literal in this language is 0"
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "true"  => `(Tm.tru)
      | "false" => `(Tm.fls)
      | _ => `($x)   -- a bare identifier is a spliced Lean term (usually a variable)
  | `(<{ $f:ident $e:tm }>) =>
      match f.getId.toString with
      | "succ"   => `(Tm.succ <{ $e }>)
      | "pred"   => `(Tm.pred <{ $e }>)
      | "iszero" => `(Tm.isZero <{ $e }>)
      | _ => Macro.throwErrorAt f s!"unknown operator `{f.getId}`"
  | `(<{ ($e) }>) => `(<{ $e }>)
  | `(<{ ~$e }>)  => pure e
  | `(<{ if $c then $t else $e }>) => `(Tm.ite <{ $c }> <{ $t }> <{ $e }>)
```

::::full
A _delaborator_ closes the loop: it walks a `Tm` value and rebuilds the
concrete syntax, so that terms appearing in goals, `#check`, and `#eval`
output print as `<{ … }>` rather than as a pile of constructors.  (Setting
`pp.notation false` turns it off, revealing the raw constructors.)  A `Ty`
prints as `Bool` or `Nat`.
::::

```lean
open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
/-- Re-inserts parentheses in `tm` output according to the grammar's precedences. -/
@[category_parenthesizer tm]
def tm.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `tm true wrapParens prec <|
    parenthesizeCategoryCore `tm prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(tm| ($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `tm` concrete syntax from a `Tm` term. -/
partial def delabTmInner : DelabM (TSyntax `tm) := do
  let stx ←
    match_expr ← getExpr with
    | Tm.tru => `(tm| $(mkIdent `true):ident)
    | Tm.fls => `(tm| $(mkIdent `false):ident)
    | Tm.zero => `(tm| 0)
    | Tm.succ _ => do `(tm| $(mkIdent `succ):ident $(← withAppArg delabTmInner))
    | Tm.pred _ => do `(tm| $(mkIdent `pred):ident $(← withAppArg delabTmInner))
    | Tm.isZero _ => do `(tm| $(mkIdent `iszero):ident $(← withAppArg delabTmInner))
    | Tm.ite _ _ _ => do
        let c ← withAppFn <| withAppFn <| withAppArg delabTmInner
        let t ← withAppFn <| withAppArg delabTmInner
        let e ← withAppArg delabTmInner
        `(tm| if $c then $t else $e)
    | _ => do
        -- A bare variable prints without the `~` escape; anything else keeps it.
        match ← delab with
        | `($i:ident) => `(tm| $i:ident)
        | e => `(tm| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Tm.tru, delab app.Tm.fls, delab app.Tm.zero, delab app.Tm.succ,
  delab app.Tm.pred, delab app.Tm.isZero, delab app.Tm.ite]
partial def delabTm : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Tm.tru => true | Tm.fls => true | Tm.zero => true
    | Tm.succ _ => true | Tm.pred _ => true | Tm.isZero _ => true
    | Tm.ite _ _ _ => true | _ => false
  match ← delabTmInner with
  | `(tm| ~$e) => pure e
  | e => `(<{ $e }>)
```

### Values

_Values_ are terms that are "terminal", in the sense that they cannot evaluate further.
`true`, `false`, and numeric values (`0`, and `succ` (successor) of a numeric value).

```lean
inductive Tm.IsBValue : Tm → Prop where
  | tru : Tm.IsBValue <{ true }>
  | fls : Tm.IsBValue <{ false }>

inductive Tm.IsNValue : Tm → Prop where
  | zero : Tm.IsNValue <{ 0 }>
  | succ (t : Tm) (h : Tm.IsNValue t) : Tm.IsNValue <{ succ t }>

def Tm.IsValue (t : Tm) : Prop := Tm.IsBValue t ∨ Tm.IsNValue t
```

:::dev
```
HIDE: CH: This definition of numeric values that insists on well-typing
seems overly complicated to me.  This idea is later dropped in MoreStlc
both for numbers and also for lists, and some careful students do seem
to notice the change and wonder about it.
```
:::

## Operational Semantics

::::full
Here is the single-step relation, first informally...
::::

```
                   -------------------------------                   (ifTrue)
                   if true then t1 else t2 ⟶ t1

                   -------------------------------                  (ifFalse)
                   if false then t1 else t2 ⟶ t2

                               t1 ⟶ t1'
            ------------------------------------------------             (ifStep)
            if t1 then t2 else t3 ⟶ if t1' then t2 else t3

                             t1 ⟶ t1'
                         --------------------                          (succStep)
                         succ t1 ⟶ succ t1'

                           ------------                               (predZero)
                           pred 0 ⟶ 0

                         numeric value v
                        -------------------                        (predSucc)
                        pred (succ v) ⟶ v

                              t1 ⟶ t1'
                         --------------------                          (predStep)
                         pred t1 ⟶ pred t1'

                          -----------------                         (isZeroZero)
                          iszero 0 ⟶ true

                         numeric value v
                      -------------------------                  (isZeroSucc)
                      iszero (succ v) ⟶ false

                            t1 ⟶ t1'
                       ------------------------                      (isZeroStep)
                       iszero t1 ⟶ iszero t1'
```

::::full
... and then formally:
::::

:::slidebreak
:::

```lean
-- We give the rules with explicit `Tm.Step …` and then attach `⟶` as a
-- *scoped* notation.  Scoping keeps it from clashing with the Smallstep
-- chapter's own global `⟶` (a different relation): inside this chapter's `TM`
-- namespace the two overload, and Lean picks the one that typechecks.
inductive Tm.Step : Tm → Tm → Prop where
  | ifTrue (t1 t2 : Tm) : Tm.Step <{ if true then t1 else t2 }> t1
  | ifFalse (t1 t2 : Tm) : Tm.Step <{ if false then t1 else t2 }> t2
  | ifStep (c c' t2 t3 : Tm) :
      Tm.Step c c' → Tm.Step <{ if c then t2 else t3 }> <{ if c' then t2 else t3 }>
  | succStep (t1 t1' : Tm) : Tm.Step t1 t1' → Tm.Step <{ succ t1 }> <{ succ t1' }>
  | predZero : Tm.Step <{ pred 0 }> <{ 0 }>
  | predSucc (v : Tm) : Tm.IsNValue v → Tm.Step <{ pred (succ v) }> v
  | predStep (t1 t1' : Tm) : Tm.Step t1 t1' → Tm.Step <{ pred t1 }> <{ pred t1' }>
  | isZeroZero : Tm.Step <{ iszero 0 }> <{ true }>
  | isZeroSucc (v : Tm) : Tm.IsNValue v → Tm.Step <{ iszero (succ v) }> <{ false }>
  | isZeroStep (t1 t1' : Tm) : Tm.Step t1 t1' → Tm.Step <{ iszero t1 }> <{ iszero t1' }>

scoped notation:40 t:41 " ⟶ " t':41 => Tm.Step t t'
```

::::full
The `Tm.IsNValue` premises in `predSucc` and `isZeroSucc` are needed
for determinism (this will be proved in an optional exercise below).
::::

::::full
Notice that the `Tm.Step` relation doesn't care about whether the
expression being stepped makes global sense -- it just checks that the
operation in the _next_ reduction step is being applied to the right
kinds of operands.  For example, the term `succ true` cannot take a
step, but the almost as obviously nonsensical term
```
succ (if true then true else true)
```
can take a step (once, before becoming stuck).
::::

## Normal Forms and Values

The first interesting thing to notice about this `Tm.Step` relation is that
the strong progress theorem from the Smallstep chapter fails here.  That
is, there are terms that are normal forms (they can't take a step) but
not values (they are not included in our definition of possible "results
of reduction").

Such terms are _stuck_.

:::dev "Claude" PotentialImprovement
These two facts about `Tm` are the single-sorted successors of the `Combined`-language
exercises `combined_step_deterministic` and `combined_strong_progress`, which were cut
from the Smallstep chapter (the two-sorted Slang cannot express the ill-formed / stuck
terms they relied on).  Make sure this chapter covers both angles those exercises did:
determinism of stepping (`step_deterministic`, below) and the failure of strong
progress via stuck terms (`some_term_is_stuck`, below).  If either is thinner than the
cut Combined exercises, port the missing part here.
:::

```lean
def Tm.IsNormalForm (t : Tm) : Prop := _root_.IsNormalForm Tm.Step t

def Tm.IsStuck (t : Tm) : Prop := Tm.IsNormalForm t ∧ ¬ Tm.IsValue t
```

:::::exercise (rating := 2) (name := "some_term_is_stuck")
```lean
theorem some_term_is_stuck : ∃ t, Tm.IsStuck t := by
  solution!
    refine ⟨<{ succ false }>, ?_, ?_⟩
    · intro hc; obtain ⟨t', hstp⟩ := hc
      cases hstp with
      | succStep _ _ h => cases h
    · intro h
      cases h with
      | inl hb => cases hb
      | inr hn => cases hn with | succ _ h => cases h
```
:::::

:::slidebreak
:::

However, although values and normal forms are _not_ the same in this
language, the set of values is a subset of the set of normal forms.

This is important because it shows we did not accidentally define things
so that some value could still take a step.

:::dev
```
SOONER: Not exactly sure why, but this seems to be very tricky for
students.
```
:::

```lean
theorem nvalue_is_nf (t : Tm) (h : Tm.IsNValue t) : Tm.IsNormalForm t := by
  induction h with
  | zero => intro hc; obtain ⟨t', hstp⟩ := hc; cases hstp
  | succ t0 hn0 ih =>
      intro hc; obtain ⟨t', hstp⟩ := hc
      cases hstp with
      | succStep _ t1' h => exact ih ⟨t1', h⟩
```

:::::exercise (rating := 3) (name := "value_is_nf")
(Hint: You will reach a point in this proof where you need to use an
induction to reason about a term that is known to be a numeric value.
This induction can be performed either over the term itself or over the
evidence that it is a numeric value.  The proof goes through in either
case, but you will find that one way is quite a bit shorter than the
other.  For the sake of the exercise, try to complete the proof both
ways.)

```lean
theorem value_is_nf (t : Tm) (h : Tm.IsValue t) : Tm.IsNormalForm t := by
  solution!
    cases h with
    | inl hb => intro hc; obtain ⟨t', hstp⟩ := hc; cases hb <;> cases hstp
    | inr hn => exact nvalue_is_nf t hn
```
:::::

:::dev
```
HIDE: The "other way" mentioned in the hint -- induction on the term
itself rather than on the numeric-value evidence.  It goes through, but
is a bit longer than the `nvalue_is_nf` route above.
```
:::

```lean
theorem value_is_nf' : ∀ t, Tm.IsValue t → Tm.IsNormalForm t := by
  intro t
  induction t with
  | tru => intro _ hc; obtain ⟨t', hstp⟩ := hc; cases hstp
  | fls => intro _ hc; obtain ⟨t', hstp⟩ := hc; cases hstp
  | ite c t0 e _ _ _ =>
      intro h; cases h with
      | inl hb => cases hb
      | inr hn => cases hn
  | zero => intro _ hc; obtain ⟨t', hstp⟩ := hc; cases hstp
  | succ t0 ih =>
      -- The `succ` case is the only one that doesn't immediately present a
      -- contradiction.  Considering how a `succ` term can be a value, it is
      -- syntactically not a boolean value, but the numeric value case
      -- requires a bit more work.
      intro h hc; obtain ⟨t', hstp⟩ := hc
      cases hstp with
      | succStep _ t1' hstp' =>
          cases h with
          | inl hb => cases hb
          -- By the IH, if `t0` is a numeric value, then it can not step.
          | inr hn => cases hn with
            | succ _ hn0 => exact ih (.inr hn0) ⟨t1', hstp'⟩
  | pred t0 _ =>
      intro h; cases h with
      | inl hb => cases hb
      | inr hn => cases hn
  | isZero t0 _ =>
      intro h; cases h with
      | inl hb => cases hb
      | inr hn => cases hn
```

:::::exercise (rating := 3) (name := "step_deterministic")
Use `value_is_nf` (here, `nvalue_is_nf`) to show that the `Tm.Step` relation
is also deterministic.

```lean
theorem step_deterministic : Deterministic Tm.Step := by
  solution!
    intro x y1 y2 h1
    induction h1 generalizing y2 with
    | ifTrue t1 t2 =>
        intro h2; cases h2 with
        | ifTrue => rfl
        | ifStep _ _ _ _ hc => cases hc
    | ifFalse t1 t2 =>
        intro h2; cases h2 with
        | ifFalse => rfl
        | ifStep _ _ _ _ hc => cases hc
    | ifStep c c' t2 t3 hc ih =>
        intro h2; cases h2 with
        | ifTrue => cases hc
        | ifFalse => cases hc
        | ifStep _ c'' _ _ hc2 => rw [ih _ hc2]
    | succStep t1 t1' hs ih =>
        intro h2; cases h2 with
        | succStep _ _ hs2 => rw [ih _ hs2]
    | predZero =>
        intro h2; cases h2 with
        | predZero => rfl
        | predStep _ _ hs => cases hs
    | predSucc v hv =>
        intro h2; cases h2 with
        | predSucc => rfl
        | predStep _ _ hs => exact absurd ⟨_, hs⟩ (nvalue_is_nf _ (.succ v hv))
    | predStep t1 t1' hs ih =>
        intro h2; cases h2 with
        | predZero => cases hs
        | predSucc _ hv => exact absurd ⟨_, hs⟩ (nvalue_is_nf _ (.succ _ hv))
        | predStep _ _ hs2 => rw [ih _ hs2]
    | isZeroZero =>
        intro h2; cases h2 with
        | isZeroZero => rfl
        | isZeroStep _ _ hs => cases hs
    | isZeroSucc v hv =>
        intro h2; cases h2 with
        | isZeroSucc => rfl
        | isZeroStep _ _ hs => exact absurd ⟨_, hs⟩ (nvalue_is_nf _ (.succ v hv))
    | isZeroStep t1 t1' hs ih =>
        intro h2; cases h2 with
        | isZeroZero => cases hs
        | isZeroSucc _ hv => exact absurd ⟨_, hs⟩ (nvalue_is_nf _ (.succ _ hv))
        | isZeroStep _ _ hs2 => rw [ih _ hs2]
```
:::::

::::quiz
Is the following term stuck?
```
iszero (if true then (succ 0) else 0)
```
(A) Yes    (B) No
::::

::::quiz
What about this one? Is it stuck?
```
if (succ 0) then true else false
```
(A) Yes    (B) No
::::

::::quiz
What about this one? Is it stuck?
```
succ (succ 0)
```
(A) Yes    (B) No
::::

::::quiz
What about this one? Is it stuck?
```
succ (if true then true else true)
```
(A) Yes    (B) No

(Hint: Notice that the `Tm.Step` relation doesn't care about whether the
expression being stepped makes global sense -- it just checks that the
operation in the _next_ reduction step is being applied to the right
kinds of operands.)
::::

::::full
_Optional aside, good practice with step relations but tangential to the
main development._  We define an alternate step relation `⇢` and a step
_function_ for it -- converting a hidden draft from the Rocq source into
live Lean using this chapter's `<{ … }>` grammar and reserved-notation
setup.
::::

:::dev
```
HIDE: In the Rocq source these were a hidden, never-uncommented draft
(with `eval` still to be renamed to `step`).  Here they are activated as
live Lean.  The step relation and function build; the yes/no answers below
are stated but not (yet) proved -- a natural follow-up exercise.
```
:::

Suppose we define an alternate single-step relation, written `t ⇢ t'`,
that _drops_ the `Tm.IsNValue` premise from the `predSucc` and `isZeroSucc`
rules -- so `pred (succ t)` and `iszero (succ t)` may step even when `t` is
not a numeric value.  (It is built with exactly the same reserved-notation
setup as `Tm.Step`; note `predSucc`/`isZeroSucc` no longer take a premise.)

```lean
syntax:40 term:41 " ⇢ " term:41 : term
macro_rules | `($t ⇢ $t') => `($(Lean.mkIdent `Tm.AltStep) $t $t')

inductive Tm.AltStep : Tm → Tm → Prop where
  | ifTrue (t1 t2 : Tm) : <{ if true then t1 else t2 }> ⇢ t1
  | ifFalse (t1 t2 : Tm) : <{ if false then t1 else t2 }> ⇢ t2
  | ifStep (t1 t1' t2 t3 : Tm) : t1 ⇢ t1' →
      <{ if t1 then t2 else t3 }> ⇢ <{ if t1' then t2 else t3 }>
  | succStep (t1 t1' : Tm) : t1 ⇢ t1' → <{ succ t1 }> ⇢ <{ succ t1' }>
  | predZero : <{ pred 0 }> ⇢ <{ 0 }>
  | predSucc (t1 : Tm) : <{ pred (succ t1) }> ⇢ t1
  | predStep (t1 t1' : Tm) : t1 ⇢ t1' → <{ pred t1 }> ⇢ <{ pred t1' }>
  | isZeroZero : <{ iszero 0 }> ⇢ <{ true }>
  | isZeroSucc (t1 : Tm) : <{ iszero (succ t1) }> ⇢ <{ false }>
  | isZeroStep (t1 t1' : Tm) : t1 ⇢ t1' → <{ iszero t1 }> ⇢ <{ iszero t1' }>

@[app_unexpander Tm.AltStep]
def Tm.AltStep.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $t $t') => `($t ⇢ $t')
  | _ => throw ()
```

Some questions about this relation (answers inline):

  - Is `⇢` deterministic (`∀ t t' t'', t ⇢ t' → t ⇢ t'' → t' = t''`)?  No:
    `pred (succ (pred 0))` steps to both `pred 0` (by `predSucc`) and
    `pred (succ 0)` (by `predStep`, since `pred 0 ⇢ 0`).

  - Is every `Tm.Step` normal form also a `⇢` normal form?  No:
    `pred (succ true)` is stuck for `Tm.Step` but steps under `⇢` (to
    `true`, by `predSucc`, now that the `Tm.IsNValue` premise is gone).

  - Is every `⇢` normal form also a `Tm.Step` normal form?  Yes -- `Tm.Step`
    is a subrelation of `⇢`, so anything stuck for `⇢` is stuck for `Tm.Step`.

  - Is every value reachable by `Tm.Step` (in many steps) also reachable by
    `⇢` (in many steps)?  Yes, for the same subrelation reason.

  - Conversely?  No: `iszero (succ true)` reaches the value `false` under
    `⇢` but is stuck under `Tm.Step`.

A _functional_ version computes a single `⇢` step of a term, returning
`none` when the term is a `⇢` normal form.  This is a nice chance to see a
step _function_, which the chapter otherwise gives only as a relation:

```lean
def alt_simplify_step (t : Tm) : Option Tm :=
  match t with
  | <{ if t1 then t2 else t3 }> =>
      match alt_simplify_step t1 with
      | some t1' => some <{ if t1' then t2 else t3 }>
      | none =>
        match t1 with
        | <{ true }>  => some t2
        | <{ false }> => some t3
        | _           => none
  | <{ succ t1 }> =>
      match alt_simplify_step t1 with
      | some t1' => some <{ succ t1' }>
      | none     => none
  | <{ pred t1 }> =>
      match alt_simplify_step t1 with
      | some t1' => some <{ pred t1' }>
      | none =>
        match t1 with
        | <{ 0 }>       => some <{ 0 }>
        | <{ succ t2 }> => some t2
        | _             => none
  | <{ iszero t1 }> =>
      match alt_simplify_step t1 with
      | some t1' => some <{ iszero t1' }>
      | none =>
        match t1 with
        | <{ 0 }>       => some <{ true }>
        | <{ succ t2 }> => some <{ false }>
        | _             => none
  | _ => none

-- `pred (succ true)` steps under `⇢` (the dropped `IsNValue` premise) even
-- though it is stuck under `Tm.Step`:
example : alt_simplify_step <{ pred (succ true) }> = some <{ true }> := rfl
example : alt_simplify_step <{ if true then 0 else succ 0 }> = some <{ 0 }> := rfl
example : alt_simplify_step <{ 0 }> = none := rfl
```

## Typing

::::full
The next critical observation is that, although this language has stuck
terms, they are always nonsensical, mixing booleans and numbers in a way
that we don't even _want_ to have a meaning.  We can easily exclude such
ill-typed terms by defining a _typing relation_ that relates terms to the
types (either numeric or boolean) of their final results.
::::

:::terse
_Types_ describe the possible shapes of values.
:::

:::dev
```
NOTATION: SOONER: BCP 19: Wondering if we should replace "\in" by just
"in"...  The backslash is ugly, and I've never succeeded in getting the
\in to reliably typeset as a symbol.  I suppose something like :: would be
another alternative.  Or indeed just :, if we put <{...}> around all
typing judgements.  BCP 23: :: seems not to work (not sure why - maybe
used in the standard library?), but putting <{...}> around all typing
judgements seems like a better solution anyway.  Then, I think, we could
just use :, which would be perfect.  Maybe even |- instead of |-- ??

SOONER: BCP 21: What about putting the brackets around the very outside?
I.e., <{ |-- true \in Bool }> instead of |-- <{ true }> \in Bool?  After
all, the type (and later the context) are also from the object language...

NOTATION: SAZ 2024 - I have implemented this suggestion, which I think is
a bit nicer.  We can get away with a simpler solution in this file because
we don't have variables, etc.

SOONER: Andrew Appel 23: In my opinion, 80 is the wrong level, and Iris
made the wrong decision.  However, last year we modified the VST level to
80 because some research projects import both VST and Iris.  So I still
recommend 80 for SF.
```
:::

::::full
The _typing relation_ `⊢ t ⦂ T` relates terms to the types of their
results.  In informal notation it is often written `⊢ t ⦂ T` and
pronounced "`t` has type `T`."  The `⊢` symbol is called a "turnstile."
Below, we're going to see richer typing relations where one or more
additional "context" arguments are written to the left of the turnstile.
For the moment, the context is always empty.

```
                     ---------------              (tru)
                     ⊢ true ⦂ Bool

                     ----------------             (fls)
                     ⊢ false ⦂ Bool

      ⊢ t1 ⦂ Bool    ⊢ t2 ⦂ T    ⊢ t3 ⦂ T
      -----------------------------------------   (ite)
            ⊢ if t1 then t2 else t3 ⦂ T

                     ----------                   (zero)
                     ⊢ 0 ⦂ Nat

                     ⊢ t1 ⦂ Nat
                   ----------------               (succ)
                   ⊢ succ t1 ⦂ Nat

                     ⊢ t1 ⦂ Nat
                   ----------------               (pred)
                   ⊢ pred t1 ⦂ Nat

                     ⊢ t1 ⦂ Nat
                  -------------------             (isZero)
                  ⊢ iszero t1 ⦂ Bool
```
::::

:::slidebreak
:::

```lean
inductive Ty where
  | bool
  | nat

-- As with `⟶`, reserve the typing notation so the relation can be defined
-- using it.  The whole judgment is wrapped in `<{ … }>` (like the Rocq
-- `<{ |-- t \in T }>`): the term is written in the object grammar (bare
-- variables, no inner `<{ }>`) and the type as `Bool`/`Nat` (a type variable is
-- spliced, `~T` escapes to a Lean `Ty`).  The `app_unexpander` prints it back.
syntax:max "<{ " "⊢ " tm " ⦂ " ident " }>" : term
syntax:max "<{ " "⊢ " tm " ⦂ " "~" term:max " }>" : term
macro_rules
  | `(<{ ⊢ $t ⦂ $T:ident }>) =>
      match T.getId.toString with
      | "Bool" => `($(Lean.mkIdent `Tm.HasType) <{ $t }> Ty.bool)
      | "Nat"  => `($(Lean.mkIdent `Tm.HasType) <{ $t }> Ty.nat)
      | _      => `($(Lean.mkIdent `Tm.HasType) <{ $t }> $T)
  | `(<{ ⊢ $t ⦂ ~$T }>) => `($(Lean.mkIdent `Tm.HasType) <{ $t }> $T)

inductive Tm.HasType : Tm → Ty → Prop where
  | tru : <{ ⊢ true ⦂ Bool }>
  | fls : <{ ⊢ false ⦂ Bool }>
  | ite (t1 t2 t3 : Tm) (T : Ty) :
      <{ ⊢ t1 ⦂ Bool }> → <{ ⊢ t2 ⦂ T }> → <{ ⊢ t3 ⦂ T }> →
      <{ ⊢ if t1 then t2 else t3 ⦂ T }>
  | zero : <{ ⊢ 0 ⦂ Nat }>
  | succ (t1 : Tm) : <{ ⊢ t1 ⦂ Nat }> → <{ ⊢ succ t1 ⦂ Nat }>
  | pred (t1 : Tm) : <{ ⊢ t1 ⦂ Nat }> → <{ ⊢ pred t1 ⦂ Nat }>
  | isZero (t1 : Tm) : <{ ⊢ t1 ⦂ Nat }> → <{ ⊢ iszero t1 ⦂ Bool }>

open Lean PrettyPrinter Delaborator SubExpr in
/-- Print `Ty.bool`/`Ty.nat` as `Bool`/`Nat`. -/
@[delab app.Ty.bool, delab app.Ty.nat]
def delabTy : Delab := whenPPOption getPPNotation do
  match_expr ← getExpr with
  | Ty.bool => `($(mkIdent `Bool):ident)
  | Ty.nat  => `($(mkIdent `Nat):ident)
  | _ => failure

@[app_unexpander Tm.HasType]
def Tm.HasType.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ <{ $t }> $T:ident) => `(<{ ⊢ $t ⦂ $T }>)
  | `($_ $t:ident $T:ident)  => `(<{ ⊢ $(⟨t.raw⟩) ⦂ $T }>)
  | `($_ $t $T)              => `(<{ ⊢ ~$t ⦂ ~$T }>)
  | _ => throw ()

example : <{ ⊢ if false then 0 else succ 0 ⦂ Nat }> :=
  .ite _ _ _ _ .fls .zero (.succ _ .zero)
```

:::slidebreak
:::

::::full
It's important to realize that the typing relation is a _conservative_
(or _static_) approximation: it does not consider what happens when the
term is reduced -- in particular, it does not calculate the type of its
normal form.
::::

:::terse
Typing is a _conservative_ (or _static_) approximation to behavior.

In particular, a term can be ill typed even though it steps to something
well typed.
:::

```lean
example : ¬ <{ ⊢ if false then 0 else true ⦂ Bool }> := by
  intro hc; cases hc with | ite _ _ _ _ h1 h2 h3 => cases h2

example :
    ¬ <{ ⊢ if iszero (succ 0) then succ false else true ⦂ Bool }> := by
  intro hc; cases hc with | ite _ _ _ _ h1 h2 h3 => cases h2
```

:::::exercise (rating := 1) (name := "succ_hastype_nat__hastype_nat")
```lean
example (t : Tm) (h : <{ ⊢ succ t ⦂ Nat }>) : <{ ⊢ t ⦂ Nat }> := by
  solution!
    cases h with | succ _ hh => exact hh
```
:::::

## Canonical forms

The following two lemmas capture the fundamental fact that the
definitions of boolean and numeric values agree with the typing relation:
a well-typed value of type `Bool` is a boolean value, and of type `Nat` a
numeric value.

```lean
theorem bool_canonical (t : Tm) (hT : <{ ⊢ t ⦂ Bool }>) (hv : Tm.IsValue t) : Tm.IsBValue t := by
  cases hv with
  | inl hb => exact hb
  | inr hn => cases hn with
    | zero => cases hT
    | succ t0 h => cases hT

theorem nat_canonical (t : Tm) (hT : <{ ⊢ t ⦂ Nat }>) (hv : Tm.IsValue t) : Tm.IsNValue t := by
  cases hv with
  | inl hb => cases hb <;> cases hT
  | inr hn => exact hn
```

## Progress

The typing relation enjoys two critical properties.

The first is that well-typed normal forms are not stuck -- or conversely,
if a term is well typed, then either it is a value or it can take at
least one step.  We call this _progress_.

:::::exercise (rating := 3) (name := "finish_progress")
Complete the formal proof of the `progress` property.  (Make sure you
understand the parts we've given of the informal proof in the following
exercise before starting -- this will save you a lot of time.)

```lean
theorem progress (t : Tm) (T : Ty) (hT : <{ ⊢ t ⦂ T }>) : Tm.IsValue t ∨ ∃ t', t ⟶ t' := by
  solution!
    induction hT with
    | tru => exact .inl (.inl .tru)
    | fls => exact .inl (.inl .fls)
    | zero => exact .inl (.inr .zero)
    | ite t1 t2 t3 T h1 h2 h3 ih1 ih2 ih3 =>
        right
        cases ih1 with
        | inl hv1 =>
            cases bool_canonical t1 h1 hv1 with
            | tru => exact ⟨t2, .ifTrue t2 t3⟩
            | fls => exact ⟨t3, .ifFalse t2 t3⟩
        | inr hs1 => obtain ⟨t1', h⟩ := hs1
                     exact ⟨<{ if t1' then t2 else t3 }>, .ifStep t1 t1' t2 t3 h⟩
    | succ t1 h ih =>
        cases ih with
        | inl hv => exact .inl (.inr (.succ t1 (nat_canonical t1 h hv)))
        | inr hs => obtain ⟨t', h'⟩ := hs; exact .inr ⟨<{ succ t' }>, .succStep t1 t' h'⟩
    | pred t1 h ih =>
        right
        cases ih with
        | inl hv =>
            cases nat_canonical t1 h hv with
            | zero => exact ⟨<{ 0 }>, .predZero⟩
            | succ t0 hn0 => exact ⟨t0, .predSucc t0 hn0⟩
        | inr hs => obtain ⟨t', h'⟩ := hs; exact ⟨<{ pred t' }>, .predStep t1 t' h'⟩
    | isZero t1 h ih =>
        right
        cases ih with
        | inl hv =>
            cases nat_canonical t1 h hv with
            | zero => exact ⟨<{ true }>, .isZeroZero⟩
            | succ t0 hn0 => exact ⟨<{ false }>, .isZeroSucc t0 hn0⟩
        | inr hs => obtain ⟨t', h'⟩ := hs; exact ⟨<{ iszero t' }>, .isZeroStep t1 t' h'⟩
```

:::grade
```
GRADE_THEOREM 3: progress
```
:::
:::::

::::quiz
What is the relation between the _progress_ property defined here and the
_strong progress_ from the Smallstep chapter?

(A) No difference -- they mean the same thing

(B) Progress implies strong progress

(C) Strong progress implies progress

(D) No relationship

(E) Dunno
::::

:::::exercise (rating := 3) (name := "finish_progress_informal")
Complete the corresponding informal proof.

_Theorem_: If `⊢ t ⦂ T`, then either `t` is a value or else `t ⟶ t'` for
some `t'`.

_Proof_: By induction on a derivation of `⊢ t ⦂ T`.

  - If the last rule in the derivation is `ite`, then `t = if t1 then t2
    else t3`, with `⊢ t1 ⦂ Bool`, `⊢ t2 ⦂ T` and `⊢ t3 ⦂ T`.  By the IH,
    either `t1` is a value or else `t1` can step to some `t1'`.

    - If `t1` is a value, then by the canonical forms lemmas and the fact
      that `⊢ t1 ⦂ Bool` we have that `t1` is a boolean value
      (`Tm.IsBValue`) -- i.e., it is either `true` or `false`.  If `t1 = true`, then `t` steps to `t2` by
      `ifTrue`, while if `t1 = false`, then `t` steps to `t3` by
      `ifFalse`.  Either way, `t` can step, which is what we wanted to
      show.

    - If `t1` itself can take a step, then, by `ifStep`, so can `t`.

:::solution
```
- If the last rule in the derivation is `tru`, then `t = true`, which
  is a boolean value and hence a value.  The cases for `fls` and `zero`
  are similar.

- If the last rule in the derivation is `succ`, then `t = succ t1`, with
  `⊢ t1 ⦂ Nat`.  By the IH, either `t1` is a value or else `t1` can step
  to some `t1'`.

  - If `t1` is a value, then by the canonical forms lemma `t1` is an
    `nvalue`, and hence `t` is also an `nvalue` (and hence a value) by
    `succ`.

  - If `t1` can take a step, then by `succStep`, so can `t`.

- If the last rule in the derivation is `pred`, then `t = pred t1`, with
  `⊢ t1 ⦂ Nat`.  By the IH, either `t1` is a value or else `t1` can step
  to some `t1'`.

  - If `t1` is a value, then (by the same argument as in the previous
    case) it must be an `nvalue`.  By case analysis on the `nvalue`
    judgement, there are two cases:

    - If `t1 = 0`, then `t` can take a step by `predZero`.

    - Otherwise, `t1 = succ t1'`, with `t1'` an `nvalue`.  Hence `t` can
      again take a step, this time by `predSucc`.

  - Finally, if `t1` can take a step, then by `predStep`, so can `t`.

- If the last rule in the derivation is `isZero`, then `t = iszero t1`,
  with `⊢ t1 ⦂ Nat`.  By the IH, either `t1` is a value or else `t1` steps
  to some `t1'`.

  - If `t1` is a value, it must be an `nvalue`, and there are two cases to
    consider:

    - If `t1 = 0`, then `t` can take a step by `isZeroZero`.

    - Otherwise, `t1 = succ t1'` where `t1'` is an `nvalue`.  Hence `t` can
      take a step by `isZeroSucc`.

  - If `t1` can take a step, then so can `t`, by `isZeroStep`.
```
:::

:::grade
```
GRADE_MANUAL 3: finish_progress_informal
```
:::
:::::

::::full
This theorem is more interesting than the strong progress theorem that we
saw in the Smallstep chapter, where _all_ normal forms were values.  Here
a term can be stuck, but only if it is ill typed.
::::

::::quiz
Quick review: in the language defined at the start of this chapter...

  - Every well-typed normal form is a value.

(A) True    (B) False

:::answer
TRUE: This is the content of the progress theorem.
:::
::::

::::quiz
In this language...

  - Every value is a normal form.

(A) True    (B) False

:::answer
TRUE: This can be proved by induction on values.
:::
::::

::::quiz
In this language...

  - The single-step reduction relation is a partial function (i.e., it is
    deterministic).

(A) True    (B) False

:::answer
TRUE: This is the determinism theorem.
:::
::::

::::quiz
In this language...

  - The single-step reduction relation is a _total_ function.

(A) True    (B) False

:::answer
FALSE: normal forms do not reduce to anything.
:::
::::

## Type Preservation

The second critical property of typing is that, when a well-typed term
takes a step, the result is a well-typed term (of the same type).

:::::exercise (rating := 2) (name := "finish_preservation")
Complete the formal proof of the `preservation` property.  (Again, make
sure you understand the informal proof fragment in the following exercise
first.)

```lean
theorem preservation (t t' : Tm) (T : Ty) (hT : <{ ⊢ t ⦂ T }>) (he : t ⟶ t') : <{ ⊢ t' ⦂ T }> := by
  solution!
    induction hT generalizing t' with
    | tru => cases he
    | fls => cases he
    | zero => cases he
    | ite t1 t2 t3 T h1 h2 h3 ih1 ih2 ih3 =>
        cases he with
        | ifTrue => exact h2
        | ifFalse => exact h3
        | ifStep _ c' _ _ hc => exact .ite c' t2 t3 T (ih1 c' hc) h2 h3
    | succ t1 h ih =>
        cases he with
        | succStep _ t1' hs => exact .succ t1' (ih t1' hs)
    | pred t1 h ih =>
        cases he with
        | predZero => exact .zero
        | predSucc v hv => cases h with | succ _ hh => exact hh
        | predStep _ t1' hs => exact .pred t1' (ih t1' hs)
    | isZero t1 h ih =>
        cases he with
        | isZeroZero => exact .tru
        | isZeroSucc v hv => exact .fls
        | isZeroStep _ t1' hs => exact .isZero t1' (ih t1' hs)
```

:::grade
```
GRADE_THEOREM 2: preservation
```
:::
:::::

:::::exercise (rating := 3) (name := "finish_preservation_informal")
Complete the following informal proof.

_Theorem_: If `⊢ t ⦂ T` and `t ⟶ t'`, then `⊢ t' ⦂ T`.

_Proof_: By induction on a derivation of `⊢ t ⦂ T`.

  - If the last rule in the derivation is `ite`, then `t = if t1 then t2
    else t3`, with `⊢ t1 ⦂ Bool`, `⊢ t2 ⦂ T` and `⊢ t3 ⦂ T`.

    Inspecting the rules for the small-step reduction relation and
    remembering that `t` has the form `if ...`, we see that the only ones
    that could have been used to prove `t ⟶ t'` are `ifTrue`,
    `ifFalse`, or `ifStep`.

    - If the last rule was `ifTrue`, then `t' = t2`.  But we know that
      `⊢ t2 ⦂ T`, so we are done.

    - If the last rule was `ifFalse`, then `t' = t3`.  But we know that
      `⊢ t3 ⦂ T`, so we are done.

    - If the last rule was `ifStep`, then `t' = if t1' then t2 else t3`,
      where `t1 ⟶ t1'`.  We know `⊢ t1 ⦂ Bool` so, by the IH, `⊢ t1' ⦂
      Bool`.  The `ite` rule then gives us `⊢ if t1' then t2 else t3 ⦂ T`,
      as required.

:::solution
```
- If the last rule in the derivation were `tru`, then `t = true`.
  However, `true` does not step to anything, so this case is vacuously
  true.

- Similarly, neither `fls` nor `zero` could be the final rule in the
  derivation.

- If the last rule in the derivation is `succ`, then `t = succ t1` with
  `⊢ t1 ⦂ Nat` and `T = Nat`.  The only rule which could have been used to
  show that `t` steps is `succStep`, in which case `t1` steps to some
  `t1'`.  So, by the IH, `⊢ t1' ⦂ Nat`, and hence `t' = succ t1'` also has
  type `Nat` by `succ`.

- If the last rule in the derivation is `pred`, then `t = pred t1` with
  `⊢ t1 ⦂ Nat`.  There are only three rules which could have been the last
  rule in the derivation of `pred t1 ⟶ t'`.

  - If the last rule was `predZero`, then `t' = 0` which has type `Nat`.

  - If the last rule was `predSucc`, then `t1 = succ t'`; by inversion
    on the fact that `⊢ t1 ⦂ Nat` it follows that `⊢ t' ⦂ Nat` as well.

  - If the last rule was `predStep`, then `t1` steps to some `t1'`; by the
    IH `⊢ t1' ⦂ Nat`, and so `pred t1'` has type `Nat` as well by
    `pred`.

- If the last rule in the derivation is `isZero`, then `t = iszero t1`
  with `⊢ t1 ⦂ Nat` and `T = Bool`.  There are only three rules which
  could have been the last rule in the derivation of `iszero t1 ⟶ t'`.

  - If the last rule was `isZeroZero`, then `t' = true` which has type
    `Bool`.

  - If the last rule was `isZeroSucc`, then `t' = false` which has type
    `Bool`.

  - If the last rule was `isZeroStep`, then `t1` steps to some `t1'`.  By
    the IH, `⊢ t1' ⦂ Nat` as well, and hence `t' = iszero t1'` has type
    `Bool` by `isZero`.
```
:::

:::grade
```
GRADE_MANUAL 3: finish_preservation_informal
```
:::
:::::

:::::exercise (rating := 3) (name := "preservation_alternate_proof")
Now prove the same property again by induction on the _evaluation_
derivation instead of on the typing derivation.  Begin by carefully
reading and thinking about the first few lines of the above proofs to
make sure you understand what each one is doing.  The set-up for this
proof is similar, but not exactly the same.

```lean
theorem preservation' (t t' : Tm) (T : Ty) (hT : <{ ⊢ t ⦂ T }>) (he : t ⟶ t') : <{ ⊢ t' ⦂ T }> := by
  solution!
    induction he generalizing T with
    | ifTrue t1 t2 => cases hT with | ite _ _ _ _ h1 h2 h3 => exact h2
    | ifFalse t1 t2 => cases hT with | ite _ _ _ _ h1 h2 h3 => exact h3
    | ifStep c c' t2 t3 hc ih =>
        cases hT with | ite _ _ _ _ h1 h2 h3 => exact .ite c' t2 t3 T (ih .bool h1) h2 h3
    | succStep t1 t1' hs ih => cases hT with | succ _ h => exact .succ t1' (ih .nat h)
    | predZero => cases hT with | pred _ h => exact .zero
    | predSucc v hv => cases hT with | pred _ h => cases h with | succ _ hh => exact hh
    | predStep t1 t1' hs ih => cases hT with | pred _ h => exact .pred t1' (ih .nat h)
    | isZeroZero => cases hT with | isZero _ h => exact .tru
    | isZeroSucc v hv => cases hT with | isZero _ h => exact .fls
    | isZeroStep t1 t1' hs ih => cases hT with | isZero _ h => exact .isZero t1' (ih .nat h)
```

:::grade
```
GRADE_THEOREM 3: preservation'
```
:::
:::::

::::full
The preservation theorem is often called _subject reduction_, because it
tells us what happens when the "subject" of the typing relation is
reduced.  This terminology comes from thinking of typing statements as
sentences, where the term is the subject and the type is the predicate.
::::

## Type Soundness

Putting progress and preservation together, we see that a well-typed term
can never reach a stuck state.

```lean
def Tm.MultiStep (t1 t2 : Tm) : Prop := Multi Tm.Step t1 t2

scoped notation:40 t1:41 " ⟶* " t2:41 => Tm.MultiStep t1 t2

theorem soundness (t t' : Tm) (T : Ty) (hT : <{ ⊢ t ⦂ T }>) (hm : t ⟶* t') : ¬ Tm.IsStuck t' := by
  induction hm generalizing T with
  | refl a =>
      intro hst; obtain ⟨hnf, hnv⟩ := hst
      cases progress a T hT with
      | inl hv => exact hnv hv
      | inr hs => exact hnf hs
  | step a b c h1 h2 ih => exact ih T (preservation a b T hT h1)
```

::::quiz
Suppose we add the following two new rules to the reduction relation:
```
| ST_PredTrue  : pred true  ⟶ pred false
| ST_PredFalse : pred false ⟶ pred true
```
Which of the following properties remain true in the presence of these
rules?  (Choose 1 for yes, 2 for no.)

  - Determinism of `Tm.Step`
  - Progress
  - Preservation

:::answer
All three remain true.
:::
::::

::::quiz
Suppose, instead, that we add this new rule to the typing relation:
```
| T_IfFunny : ⊢ t2 ⦂ Nat → ⊢ if true then t2 else t3 ⦂ Nat
```
Which of the following properties remain true in the presence of this
rule?

  - Determinism of `Tm.Step`
  - Progress
  - Preservation

:::answer
All three remain true.
:::
::::

# Additional Exercises

:::::exercise (rating := 3) (name := "subject_expansion")
Having seen the subject reduction property, one might wonder whether the
opposite property -- subject _expansion_ -- also holds.  That is, is it
always the case that, if `t ⟶ t'` and `⊢ t' ⦂ T`, then `⊢ t ⦂ T`?  If so,
prove it.  If not, give a counter-example.

:::solution
```
Subject expansion does not hold in this language (or most interesting
languages).  For example, `if false then true else 0` is ill typed, but
it reduces to the well-typed term `0`.
```
:::

```lean
theorem subject_expansion :
    (∀ (t t' : Tm) (T : Ty), t ⟶ t' ∧ <{ ⊢ t' ⦂ T }> → <{ ⊢ t ⦂ T }>)
    ∨ ¬ (∀ (t t' : Tm) (T : Ty), t ⟶ t' ∧ <{ ⊢ t' ⦂ T }> → <{ ⊢ t ⦂ T }>) := by
  solution!
    right
    intro hse
    have hT : <{ ⊢ if false then true else 0 ⦂ Nat }> :=
      hse <{ if false then true else 0 }> <{ 0 }> .nat ⟨.ifFalse <{ true }> <{ 0 }>, .zero⟩
    cases hT with | ite _ _ _ _ h1 h2 h3 => cases h2

end TM
```
:::::

The following are _thought exercises_: for each modification, say which
of determinism / progress / preservation still hold, with a
counterexample if one breaks.  (These are graded manually; there is no
Lean code to complete.)

:::dev
```
HIDE: Two further variations kept for the instructors only (they overlap
with the two quizzes in the Type Soundness section above).

variation1a (EX2M?): add the two step rules
  ST_PredTrue  : pred true  ⟶ pred false
  ST_PredFalse : pred false ⟶ pred true
-- Determinism, Progress, and Preservation all remain true.

variation1b (EX2M?): add the typing rule
  T_IfFunny : ⊢ t2 ⦂ Nat → ⊢ if true then t2 else t3 ⦂ Nat
-- Determinism, Progress, and Preservation all remain true.
```
:::

:::::exercise (rating := 2) (name := "variation1")
Suppose that we add this new rule to the typing relation:
```
T_SuccBool : ⊢ t ⦂ Bool → ⊢ succ t ⦂ Bool
```
Which of the following properties remain true in the presence of this
rule?  For each one, write either "remains true" or else "becomes false."
If a property becomes false, give a counterexample.

  - Determinism of `Tm.Step`
  - Progress
  - Preservation

:::solution
```
- Determinism: remains true (the `step` relation is unchanged).
- Progress: becomes false -- `succ true` is now well typed (`⊢ succ true ⦂
  Bool`) but is stuck.
- Preservation: remains true.
```
:::

:::grade
```
GRADE_MANUAL 2: variation1
```
:::
:::::

:::::exercise (rating := 2) (name := "variation2")
Suppose, instead, that we add this new rule to the `Tm.Step` relation:
```
ST_Funny1 : if true then t2 else t3 ⟶ t3
```
Which of the above properties become false in the presence of this rule?
For each one that does, give a counter-example.

:::solution
```
- Determinism: becomes false -- `if true then 0 else (succ 0)` can now step
  to either `0` (ifTrue) or `succ 0` (ST_Funny1).
- Progress and preservation: remain true.
```
:::

:::grade
```
GRADE_MANUAL 2: variation2
```
:::
:::::

:::::exercise (rating := 2) (name := "variation3")
Suppose instead that we add this rule:
```
ST_Funny2 : t2 ⟶ t2' → if t1 then t2 else t3 ⟶ if t1 then t2' else t3
```
Which of the above properties become false in the presence of this rule?
For each one that does, give a counter-example.

:::solution
```
Determinism becomes false (e.g. `if false then (pred 0) else (succ 0)`
can step by either `ifFalse` or the new rule).  Progress and
preservation remain true.
```
:::
:::::

:::::exercise (rating := 2) (name := "variation4")
Suppose instead that we add this rule:
```
ST_Funny3 : pred false ⟶ pred (pred false)
```
Which of the above properties become false in the presence of this rule?
For each one that does, give a counter-example.

:::solution
```
All three properties remain true.
```
:::
:::::

:::::exercise (rating := 2) (name := "variation5")
Suppose instead that we add this rule:
```
T_Funny4 : ⊢ 0 ⦂ Bool
```
Which of the above properties become false in the presence of this rule?
For each one that does, give a counter-example.

:::solution
```
Progress becomes false: `if 0 then true else true` has type `Bool`, is a
   normal form, and is not a value.
```
:::
:::::

:::::exercise (rating := 2) (name := "variation6")
Suppose instead that we add this rule:
```
T_Funny5 : ⊢ pred 0 ⦂ Bool
```
Which of the above properties become false in the presence of this rule?
For each one that does, give a counter-example.

:::solution
```
Preservation becomes false: `pred 0` has type `Bool` and steps to `0`,
   which does not have type `Bool`.
```
:::
:::::

:::::exercise (rating := 3) (name := "more_variations")
Make up some exercises of your own along the same lines as the ones
above.  Try to find ways of selectively breaking properties -- i.e., ways
of changing the definitions that break just one of the properties and
leave the others alone.
:::::

:::dev
```
LATER: How about turning this into variation9?
```
:::

:::::exercise (rating := 1) (name := "remove_pred0")
The reduction rule `predZero` is a bit counter-intuitive: we might feel
that it makes more sense for the predecessor of `0` to be undefined,
rather than being defined to be `0`.  Can we achieve this simply by
removing the rule from the definition of `Tm.Step`?  Would doing so create
any problems elsewhere?

:::solution
```
Yes, but doing this would break the progress property.  A better way would
be to raise an exception in this case, but this requires that we add
exceptions to the language we're formalizing!
```
:::

:::grade
```
GRADE_MANUAL 1: remove_pred0
```
:::
:::::

:::::exercise (rating := 4) (name := "prog_pres_bigstep")
Suppose our evaluation relation is defined in the big-step style.  State
appropriate analogs of the progress and preservation properties.  (You do
not need to prove them.)

Can you see any limitations of either of your properties?  Do they allow
for nonterminating programs?  Why might we prefer the small-step semantics
for stating preservation and progress?

:::solution
```
The type preservation property for the big-step semantics is similar to
the one we gave for the small-step semantics: if a well-typed term
evaluates to some final value, then this value has the same type as the
original term.  The proof is similar to the one we gave.  However,
preservation for small-step semantics implies that all intermediate states
(i.e., all states reachable in multi-step) are well-typed, whereas big-step
semantics only relates a term to its final evaluation result, with no
notion of "intermediate state" about which preservation can make
guarantees.

The situation with the progress property is more interesting.  A direct
analog (if a term is well typed then it evaluates to some other term)
makes a much stronger claim than the progress theorem we have given: it
says that every well-typed term can be evaluated to some final value---that
is, that evaluation always terminates on well-typed terms.  For arithmetic
expressions, this happens to be the case, but for more interesting
languages (languages involving general recursion, for example) it will
often not be true.  For such languages, we simply have no progress property
in the big-step style: in effect, there is no way to tell the difference
between reaching an error state and failing to terminate.  This is one
reason that language theorists generally prefer the small-step style.
```
:::

:::grade
```
GRADE_MANUAL 6: prog_pres_bigstep
```
:::
:::::

:::dev
```
PORT STATUS: Covers everything except the HIDE
"Typed Imp" (TImp) section, which uses Imp (deferred with the rest of the
Imp-dependent TS material).  Graded exercises from the class autograder
(`TypesTest.v`) all present & building (bare + Verso), 0 sorries:
`some_term_is_stuck`, `value_is_nf`, `progress`, `preservation`, `preservation'`,
subject_expansion, and the manual/prose exercises finish_progress_informal,
finish_preservation_informal, variation1, variation2, remove_pred0,
prog_pres_bigstep.  All chapter quizzes, the informal progress/preservation
proofs, `not_has_type'`, and the alternate `value_is_nf'` proof (term
induction) are now present.
```
:::
