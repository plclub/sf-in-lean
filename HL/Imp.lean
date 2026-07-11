import VersoManual
import VersoManual.InlineLean
import Illuminate
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
import LF.Maps
import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer
open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "Imp: Simple Imperative Programs" =>
%%%
tag := "Imp"
htmlSplit := .never
file := some "Imp"
%%%

:::instructors
This chapter plus `Maps` takes a little more than one
   80-minute lecture.  It could be streamlined a bit further without
   losing much, by removing (for example) the inference rules and BNF
   notations from the terse version.

   (BCP 21: ... Actually, I tried removing inference rules from the
   TERSE version; eventually decided that it makes some of the
   definitions harder to talk about.)
:::

:::dev
SOONER: Needs some WORKINCLASSes and some quizzes

LATER: Another nice challenge exercise at some point would be to add
   C-style arrays (i.e., indirect read/write).  This sets up some
   really nice challenge problems in Hoare (reasoning about arrays /
   aliasing / etc.).

SOONER: BCP 25: Maybe we should write /\ instead of && in assertions,
   to save a mismatch in the `dec_minimum` exercise in Hoare2?

   At some point we could consider moving material from the old
   HoareLists to this chapter (and into later files, as
   appropriate).  We haven't done it yet because it's a shame to
   complicate the nice simple presentation here when it's used as the
   basis for applications like Xavier's static analysis lectures.
   Also, we now have a whole volume on real separation logic...

MWH (port note): The Rocq chapter's "Rocq Automation" tour has been
retooled here for Lean.  The tactic combinators `try` and `repeat` (and the
custom-tactic `macro`) are introduced in this chapter; `<;>` and `simp` were
already introduced in Logical Foundations (`<;>` in `Induction`)
so we use them freely and the `<;>` section
below is a recap.  For linear arithmetic we use `lia`;
NOTE that LF currently
introduces `omega`, not `lia`, so this needs to be reconciled volume-wide
(either introduce `lia` in LF, or keep `omega`).
:::

::::full
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
::::

We concentrate here on defining the _syntax_ and _semantics_ of Imp;
later in this volume we develop a theory of _program equivalence_ and introduce
_Hoare Logic_, a popular logic for reasoning about imperative programs.

# Arithmetic and Boolean Expressions

:::dev
SOONER: At this point, I usually take some of the lecture time to
   give a high-level picture of the structure of an interpreter, the
   processes of lexing and parsing, the notion of ASTs, etc.  Might be
   nice to work some of those ideas into the notes. - BCP
:::

::::full
We'll present Imp in three parts: first a core language of _arithmetic
and boolean expressions_, then an extension of these with _variables_,
and finally a language of _commands_ including assignment, conditionals,
sequencing, and loops.
::::

## Syntax

```lean
namespace Warmup
```

::::full
These two definitions specify the _abstract syntax_ of arithmetic and
boolean expressions.
::::

:::terse
Abstract syntax trees for arithmetic and boolean expressions:
:::

```lean
inductive Aexp where
  | num (n : Nat)
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)

inductive Bexp where
  | bool (b : Bool)
  | eq (a1 a2 : Aexp)
  | neq (a1 a2 : Aexp)
  | le (a1 a2 : Aexp)
  | gt (a1 a2 : Aexp)
  | not (b : Bexp)
  | and (b1 b2 : Bexp)
```

:::dev
  SOONER: mwhicks1: Will we develop `ImpParser`? Mentioned below as an optional chapter
:::

::::full
In this chapter, we'll mostly elide the translation from the concrete
syntax that a programmer would actually write to these abstract syntax
trees -- the process that, for example, would translate the string
`"1 + 2 * 3"` to the AST `.plus (.num 1) (.mult (.num 2) (.num 3))`.

The optional chapter `ImpParser` develops a simple lexical analyzer and
parser that can perform this translation.  You do not need to understand
that chapter to understand this one, but if you haven't already taken a
course where these techniques are covered (e.g., a course on compilers)
you may want to skim it.

For comparison, here's a conventional BNF (Backus-Naur Form) grammar
defining the same abstract syntax:

```
a := nat
    | a + a
    | a - a
    | a * a

b := bool
    | a = a
    | a <> a
    | a <= a
    | a > a
    | ~ b
    | b && b
```

Compared to the Lean version above...

  - The BNF is more informal -- for example, it gives some suggestions
    about the surface syntax of expressions (like the fact that the
    addition operation is written with an infix `+`) while leaving other
    aspects of lexical analysis and parsing (like the relative precedence
    of `+`, `-`, and `*`, the use of parens to group subexpressions, etc.)
    unspecified.  Some additional information -- and human intelligence --
    would be required to turn this description into a formal definition,
    e.g., for implementing a compiler.

    The Lean version consistently omits all this information and
    concentrates on the abstract syntax only.

  - Conversely, the BNF version is lighter and easier to read.  Its
    informality makes it flexible, a big advantage in situations like
    discussions at the blackboard, where conveying general ideas is more
    important than nailing down every detail precisely.

    Indeed, there are dozens of BNF-like notations and people switch
    freely among them -- usually without bothering to say which kind of
    BNF they're using, because there is no need to: a rough-and-ready
    informal understanding is all that's important.

It's good to be comfortable with both sorts of notations: informal ones
for communicating between humans and formal ones for carrying out
implementations and proofs.
::::

## Evaluation

_Evaluating_ an arithmetic expression produces a number.

:::dev
chenson2018: TODO: seal evaluators with `@[irreducible]` and prove
   *characterizing lemmas* (one
   `rfl` equation per constructor) that proofs rewrite with instead of
   unfolding the definition; tag lemmas `@[simp]`.
:::

```lean
def Aexp.eval (a : Aexp) : Nat :=
  match a with
  | num   n     =>  n
  | plus  a1 a2 =>  eval a1 + eval a2
  | minus a1 a2 =>  eval a1 - eval a2
  | mult  a1 a2 =>  eval a1 * eval a2

example : Aexp.eval (.plus (.num 2) (.num 2)) = 4 := by rfl
```

Similarly, evaluating a boolean expression yields a boolean.

```lean
def Bexp.eval (b : Bexp) : Bool :=
  match b with
  | bool b     =>  b
  | eq   a1 a2 =>  a1.eval == a2.eval
  | neq  a1 a2 =>  a1.eval != a2.eval
  | le   a1 a2 =>  a1.eval ≤ a2.eval
  | gt   a1 a2 =>  a1.eval > a2.eval
  | not  b1    =>  !eval b1
  | and  b1 b2 =>  eval b1 && eval b2
```

::::quiz
What does the following expression evaluate to?

```
Aexp.eval (.plus (.num 3) (.minus (.num 4) (.num 1)))
```

(A) true    (B) false    (C) 0    (D) 3    (E) 6
::::

## Optimization

::::full
We haven't defined very much yet, but we can already get some mileage
out of the definitions. Suppose we define a function that takes an
arithmetic expression and slightly simplifies it, changing every
occurrence of `0 + e` (i.e., `.plus (.num 0) e`) into just `e`.
::::

```lean
def Aexp.optimize_0plus (a : Aexp) : Aexp :=
  match a with
  | num   n          => num n
  | plus  (num 0) e2 => optimize_0plus e2
  | plus  e1      e2 => plus  (optimize_0plus e1) (optimize_0plus e2)
  | minus e1      e2 => minus (optimize_0plus e1) (optimize_0plus e2)
  | mult  e1      e2 => mult  (optimize_0plus e1) (optimize_0plus e2)
```

::::full
To gain confidence that our optimization is doing the right thing we
can test it on some examples and see if the output looks OK.
::::

```lean
example :
    Aexp.optimize_0plus (.plus (.num 2)
                               (.plus (.num 0)
                                      (.plus (.num 0) (.num 1))))
      = .plus (.num 2) (.num 1) := by rfl
```

::::full
But if we want to be certain the optimization is correct -- that
evaluating an optimized expression _always_ gives the same result as
the original -- we should prove it!

Here is a first, deliberately explicit proof. It works, but notice how
much of it is repetitive: several cases are discharged by exactly the
same three-step incantation.
::::

```lean
theorem optimize_0plus_sound (a : Aexp) :
    a.optimize_0plus.eval = a.eval := by
  induction a with
  | num n => rfl
  | plus a1 a2 ih1 ih2 =>
    cases a1 with
    | num n =>
      cases n with
      | zero =>
        simp only [Aexp.optimize_0plus, Aexp.eval, Nat.zero_add]
        exact ih2
      | succ n =>
        simp only [Aexp.optimize_0plus, Aexp.eval]
        rw [ih2]
    | plus b1 b2 =>
      simp only [Aexp.optimize_0plus, Aexp.eval] at ih1 ⊢
      rw [ih1, ih2]
    | minus b1 b2 =>
      simp only [Aexp.optimize_0plus, Aexp.eval] at ih1 ⊢
      rw [ih1, ih2]
    | mult b1 b2 =>
      simp only [Aexp.optimize_0plus, Aexp.eval] at ih1 ⊢
      rw [ih1, ih2]
  | minus a1 a2 ih1 ih2 =>
    simp only [Aexp.optimize_0plus, Aexp.eval]
    rw [ih1, ih2]
  | mult a1 a2 ih1 ih2 =>
    simp only [Aexp.optimize_0plus, Aexp.eval]
    rw [ih1, ih2]
```

# Optimizing Booleans

:::::exercise (rating := 3) (name := "optimize_0plus_b_sound")
Since the `Aexp.optimize_0plus` transformation doesn't change the value of an
`Aexp`, we should be able to apply it to all the `Aexp`s that appear in a
`Bexp` without changing the `Bexp`'s value.  Write a function that
performs this transformation on `Bexp`s and prove it sound.  Use the
combinators we've just seen to make the proof as short and elegant as
possible.

```lean
def Bexp.optimize_0plus_b (b : Bexp) : Bexp := solution!(
  match b with
  | bool b    =>  bool b
  | eq a1 a2  =>  eq a1.optimize_0plus a2.optimize_0plus
  | neq a1 a2 =>  neq a1.optimize_0plus a2.optimize_0plus
  | le a1 a2  =>  le a1.optimize_0plus a2.optimize_0plus
  | gt a1 a2  =>  gt a1.optimize_0plus a2.optimize_0plus
  | not b1    =>  not (optimize_0plus_b b1)
  | and b1 b2 =>  and (optimize_0plus_b b1) (optimize_0plus_b b2))

example :
    Bexp.optimize_0plus_b
        (.not (.gt (.plus (.num 0) (.num 4)) (.num 8)))
      = (.not (.gt (.num 4) (.num 8))) := solution!(by rfl)
```

:::grade
```
GRADE_THEOREM 0.5: optimize_0plus_b_test1
```
:::

```lean
example :
    Bexp.optimize_0plus_b
        (.and (.le (.plus (.num 0) (.num 4)) (.num 5)) (.bool true))
      = (.and (.le (.num 4) (.num 5)) (.bool true)) := solution!(by rfl)
```

:::grade
```
GRADE_THEOREM 0.5: optimize_0plus_b_test2
```
:::

```lean
theorem optimize_0plus_b_sound (b : Bexp) :
    b.optimize_0plus_b.eval = b.eval := by
  solution!
    induction b with
    | not b1 ih => simp only [Bexp.optimize_0plus_b, Bexp.eval]; rw [ih]
    | and b1 b2 ih1 ih2 => simp only [Bexp.optimize_0plus_b, Bexp.eval]; rw [ih1, ih2]
    | _ => simp only [Bexp.optimize_0plus_b, Bexp.eval, optimize_0plus_sound]
```

:::grade
```
GRADE_THEOREM 2: optimize_0plus_b_sound
```
:::
:::::

# Evaluation as a Relation

::::full
We have presented `Aexp.eval` and `Bexp.eval` as functions defined by
recursion. Another way to think about evaluation -- one that is often
more flexible -- is as a _relation_ between expressions and their
values. This perspective leads to inductive definitions like the
following. We name the hypotheses in each case (`h1`, `h2`); this
gives us readable names to refer to during proofs.
::::

```lean
inductive Aexp.evalR : Aexp → Nat → Prop where
  | E_ANum (n : Nat) :
      Aexp.evalR (.num n) n
  | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat)
      (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.plus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : Aexp) (n1 n2 : Nat)
      (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.minus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : Aexp) (n1 n2 : Nat)
      (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.mult a1 a2) (n1 * n2)
```

:::dev
chenson2018: There is still some naming weirdness in the relation forms of evaluation that should be addressed later. The inductive should be in upper camel case (you can disambiguate which evaluation with its name) and the constructors should not have these `E_A` prefixes.
:::

::::full
A small notational aside. We could instead have presented this relation
with *positional* hypotheses -- no names for the premises:

```
inductive Aexp.evalR : Aexp → Nat → Prop where
  | E_ANum (n : Nat) :
      Aexp.evalR (.num n) n
  | E_APlus (e1 e2 : Aexp) (n1 n2 : Nat) :
      Aexp.evalR e1 n1 →
      Aexp.evalR e2 n2 →
      Aexp.evalR (.plus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : Aexp) (n1 n2 : Nat) :
      Aexp.evalR e1 n1 →
      Aexp.evalR e2 n2 →
      Aexp.evalR (.minus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : Aexp) (n1 n2 : Nat) :
      Aexp.evalR e1 n1 →
      Aexp.evalR e2 n2 →
      Aexp.evalR (.mult e1 e2) (n1 * n2)
```

The version above instead gives explicit names to the hypotheses in each
case (the `h1`/`h2`). Naming the hypotheses gives us more control over the
names chosen during proofs involving the relation, at the cost of making
the definition a little more verbose. We adopt the named style.
::::

It will be convenient to have an infix notation for `Aexp.evalR`.  We'll
write `e ⇓ n` to mean that arithmetic expression `e` evaluates to
value `n`.  (We scope the notation to this namespace so it doesn't
collide with other evaluation relations later.)  In Lean the notation is
declared right after the inductive.

```lean
scoped notation:55 e:56 " ⇓ " n:56 => Aexp.evalR e n
```

## Inference Rule Notation

::::full
In informal discussions, it is convenient to write the rules for
`Aexp.evalR` and similar relations in the more readable graphical form of
_inference rules_, where the premises above the line justify the
conclusion below the line.  For example, the constructor `E_APlus`

```
    | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat) :
        Aexp.evalR a1 n1 →
        Aexp.evalR a2 n2 →
        Aexp.evalR (.plus a1 a2) (n1 + n2)
```

can be written like this as an inference rule:

```
                          e1 ⇓ n1
                          e2 ⇓ n2
                    --------------------          (E_APlus)
                    plus e1 e2 ⇓ n1+n2
```

Formally, there is nothing deep about inference rules: they are just
implications. You can read the rule name on the right as the name of the
constructor and read each of the linebreaks between the premises above the
line (as well as the line itself) as `→`.  All the variables mentioned in
the rule (`e1`, `n1`, etc.) are implicitly bound by universal quantifiers
at the beginning. (Such variables are often called _metavariables_ to
distinguish them from the variables of the language we are defining. At
the moment, our arithmetic expressions don't include variables, but we'll
soon be adding them.) The whole collection of rules is understood as being
wrapped in an inductive declaration. In informal prose, this is sometimes
indicated by saying something like "Let `aevalR` be the smallest relation
closed under the following rules...".

To summarize: a group of inference rules corresponds to a single inductive
definition; each rule's name corresponds to a constructor name; above the
line are the premises, below the line the conclusion; and metavariables
like `e1` and `n1` are implicitly universally quantified. The whole
collection of rules defines `⇓` as the smallest relation closed under
them:

```
                        -----------                (E_ANum)
                        num n ⇓ n

                          e1 ⇓ n1
                          e2 ⇓ n2
                    --------------------           (E_APlus)
                    plus e1 e2 ⇓ n1+n2

                          e1 ⇓ n1
                          e2 ⇓ n2
                   ---------------------           (E_AMinus)
                   minus e1 e2 ⇓ n1-n2

                          e1 ⇓ n1
                          e2 ⇓ n2
                    --------------------           (E_AMult)
                    mult e1 e2 ⇓ n1*n2
```
::::

:::instructors
It might be useful to write the inference rules on the
chalkboard, walking through the translation from the inductive
definition, and then use these quizzes to check comprehension.
BCP 21: Too heavy.

LATER: The first two quizzes here seem kind of boring.
:::

:::dev
mwhicks1: both of the next two quizzes were hidden in the source
material; the first quiz here is shown, the second is kept under `HIDE`.
:::

::::quiz
Which rules are needed to prove the following?

```
.mult (.plus (.num 3) (.num 1)) (.num 0) ⇓ 0
```

(A) `E_ANum` and `E_APlus`
(B) `E_ANum` only
(C) `E_ANum` and `E_AMult`
(D) `E_AMult` and `E_APlus`
(E) `E_ANum`, `E_AMult`, and `E_APlus`
::::

::::hide
````
-- QUIZ
/-
  Which rules are needed to prove the following?

  ```
  .minus (.num 3) (.minus (.num 2) (.num 1)) ⇓ 2
  ```

  (A) `E_ANum` and `E_APlus`
  (B) `E_ANum` only
  (C) `E_ANum` and `E_AMinus`
  (D) `E_AMinus` and `E_APlus`
  (E) `E_ANum`, `E_AMinus`, and `E_APlus`
-/
-- /QUIZ
````
::::

:::dev
mwhicks1: Not sure if we need ⇓b, or whether we can define
⇓ overloaded. Don't understand Lean notation yet!
:::

:::::exercise (rating := 1) (name := "beval_rules")
Here, again, is the definition of the `Bexp.eval` function:

```
def Bexp.eval (b : Bexp) : Bool :=
  match b with
  | bool b     => b
  | eq   a1 a2 => a1.eval == a2.eval
  | neq  a1 a2 => a1.eval != a2.eval
  | le   a1 a2 => a1.eval ≤ a2.eval
  | gt   a1 a2 => a1.eval > a2.eval
  | not  b1    => !eval b1
  | and  b1 b2 => eval b1 && eval b2
```

Write out a corresponding definition of boolean evaluation as a relation
(in inference rule notation).

:::solution
````
Answer (`⇓b` is defined below):

```
                        -------------              (E_bool)
                        bool b ⇓b b

                          e1 ⇓ n1
                          e2 ⇓ n2
                   -------------------------        (E_BEq)
                   eq e1 e2 ⇓b (n1 =? n2)

                          e1 ⇓ n1
                          e2 ⇓ n2
                 -------------------------------    (E_BNeq)
                 neq e1 e2 ⇓b negb (n1 =? n2)

                          e1 ⇓ n1
                          e2 ⇓ n2
                   --------------------------       (E_BLe)
                   le e1 e2 ⇓b (n1 <=? n2)

                          e1 ⇓ n1
                          e2 ⇓ n2
                -------------------------------     (E_BGt)
                gt e1 e2 ⇓b negb (n1 <=? n2)

                           e ⇓b b
                      ------------------            (E_BNot)
                      not e ⇓b negb b

                          e1 ⇓b b1
                          e2 ⇓b b2
                  --------------------------        (E_BAnd)
                  and e1 e2 ⇓b andb b1 b2
```
````
:::

:::grade
```
GRADE_MANUAL 1: beval_rules
```
:::
:::::

## Equivalence of the Definitions

It is straightforward to prove that the relational and functional
definitions of evaluation agree.

:::dev
SOONER: BCP 23: Why can't we do induction on H in the ← direction??
:::

```lean
theorem aevalR_iff_aeval (a : Aexp) (n : Nat) :
    a ⇓ n ↔ a.eval = n := by
  constructor
  · intro h
    induction h with
    | E_ANum n => rfl
    | E_APlus a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [Aexp.eval]; rw [ih1, ih2]
    | E_AMinus a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [Aexp.eval]; rw [ih1, ih2]
    | E_AMult a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [Aexp.eval]; rw [ih1, ih2]
  · intro h
    subst h
    induction a with
    | num n => exact .E_ANum n
    | plus a1 a2 ih1 ih2 => exact .E_APlus a1 a2 _ _ ih1 ih2
    | minus a1 a2 ih1 ih2 => exact .E_AMinus a1 a2 _ _ ih1 ih2
    | mult a1 a2 ih1 ih2 => exact .E_AMult a1 a2 _ _ ih1 ih2
```

Again, we can make the proof quite a bit shorter using the combinators
from the previous section.

:::dev
mwhicks1: the `-- WORKINCLASS` marker leaves this shorter proof as a live in-class exercise.
:::

```lean
theorem aevalR_iff_aeval' (a : Aexp) (n : Nat) :
    a ⇓ n ↔ Aexp.eval a = n := by
  workinclass!
    constructor
    · intro h; induction h <;> simp_all [Aexp.eval]
    · intro h; subst h; induction a <;> constructor <;> assumption
```

:::::exercise (rating := 3) (name := "bevalR")
Write a relation `Bexp.evalR` in the same style as `Aexp.evalR`, and prove that
it is equivalent to `Bexp.eval`.

```lean
inductive Bexp.evalR : Bexp → Bool → Prop where
  -- SOLUTION
  | E_bool (b : Bool) : Bexp.evalR (.bool b) b
  | E_BEq (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ⇓ n1) (h2 : a2 ⇓ n2) :
      Bexp.evalR (.eq a1 a2) (n1 == n2)
  | E_BNeq (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ⇓ n1) (h2 : a2 ⇓ n2) :
      Bexp.evalR (.neq a1 a2) (n1 != n2)
  | E_BLe (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ⇓ n1) (h2 : a2 ⇓ n2) :
      Bexp.evalR (.le a1 a2) (n1 ≤ n2)
  | E_BGt (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ⇓ n1) (h2 : a2 ⇓ n2) :
      Bexp.evalR (.gt a1 a2) (n1 > n2)
  | E_BNot (b : Bexp) (bv : Bool) (h : Bexp.evalR b bv) :
      Bexp.evalR (.not b) (!bv)
  | E_BAnd (b1 b2 : Bexp) (tv1 tv2 : Bool) (h1 : Bexp.evalR b1 tv1) (h2 : Bexp.evalR b2 tv2) :
      Bexp.evalR (.and b1 b2) (tv1 && tv2)
  -- END SOLUTION

scoped notation:55 e:56 " ⇓b " b:56 => Bexp.evalR e b
```

:::dev
mwhicks1: There is no keyboard shortcut for a subscript b, nor is there one for c (to use used with cevalR below). There are numbers, x, y, z, l, m, n, etc.
:::

```lean
theorem bevalR_iff_beval (b : Bexp) (bv : Bool) :
    b ⇓b bv ↔ Bexp.eval b = bv := by
  solution!
    constructor
    · intro h
      induction h with
      | E_bool b => rfl
      | E_BEq a1 a2 n1 n2 h1 h2 =>
          simp only [Bexp.eval]; rw [(aevalR_iff_aeval a1 n1).mp h1, (aevalR_iff_aeval a2 n2).mp h2]
      | E_BNeq a1 a2 n1 n2 h1 h2 =>
          simp only [Bexp.eval]; rw [(aevalR_iff_aeval a1 n1).mp h1, (aevalR_iff_aeval a2 n2).mp h2]
      | E_BLe a1 a2 n1 n2 h1 h2 =>
          simp only [Bexp.eval]; rw [(aevalR_iff_aeval a1 n1).mp h1, (aevalR_iff_aeval a2 n2).mp h2]
      | E_BGt a1 a2 n1 n2 h1 h2 =>
          simp only [Bexp.eval]; rw [(aevalR_iff_aeval a1 n1).mp h1, (aevalR_iff_aeval a2 n2).mp h2]
      | E_BNot b bv h ih => simp only [Bexp.eval]; rw [ih]
      | E_BAnd b1 b2 tv1 tv2 h1 h2 ih1 ih2 => simp only [Bexp.eval]; rw [ih1, ih2]
    · intro h
      subst h
      induction b with
      | bool b => exact .E_bool b
      | eq a1 a2  => exact .E_BEq a1 a2 _ _ ((aevalR_iff_aeval a1 _).mpr rfl) ((aevalR_iff_aeval a2 _).mpr rfl)
      | neq a1 a2 => exact .E_BNeq a1 a2 _ _ ((aevalR_iff_aeval a1 _).mpr rfl) ((aevalR_iff_aeval a2 _).mpr rfl)
      | le a1 a2  => exact .E_BLe a1 a2 _ _ ((aevalR_iff_aeval a1 _).mpr rfl) ((aevalR_iff_aeval a2 _).mpr rfl)
      | gt a1 a2  => exact .E_BGt a1 a2 _ _ ((aevalR_iff_aeval a1 _).mpr rfl) ((aevalR_iff_aeval a2 _).mpr rfl)
      | not b ih => exact .E_BNot b _ ih
      | and b1 b2 ih1 ih2 => exact .E_BAnd b1 b2 _ _ ih1 ih2
```

:::grade
```
GRADE_THEOREM 3: bevalR_iff_beval
```
:::
:::::

```lean
end Warmup
```

## Computational vs. Relational Definitions

::::full
For the definitions of evaluation for arithmetic and boolean
expressions, the choice of whether to use functional or relational
definitions is mainly a matter of taste. However, there are many
situations where relational definitions work much better than
functional ones.
::::

:::terse
Sometimes relational definitions are the only reasonable option...
:::

```lean
namespace AevalRDivision
```

For example, suppose that we wanted to extend the arithmetic operations
with division:

```lean
inductive Aexp where
  | num (n : Nat)
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)
  | div (a1 a2 : Aexp)             -- NEW
```

Extending the definition of `Aexp.eval` to handle this new operation would
not be straightforward (what should we return as the result of
`.div (.num 5) (.num 0)`?). But extending the relation is easy.

:::terse
What should `Aexp.eval` return for `.div (.num 1) (.num 0)`??
:::

```lean
inductive Aexp.evalR : Aexp → Nat → Prop where
  | E_ANum (n : Nat) : Aexp.evalR (.num n) n
  | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.plus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.minus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.mult a1 a2) (n1 * n2)
  | E_ADiv (a1 a2 : Aexp) (n1 n2 n3 : Nat)             -- NEW
      (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) (hpos : n2 > 0) (hdiv : n2 * n3 = n1) :
      Aexp.evalR (.div a1 a2) n3
```

Notice that this evaluation relation corresponds to a _partial_
function: there are some inputs for which it does not specify an output.

```lean
end AevalRDivision

namespace AevalRExtended
```

:::terse
Another example: a _nondeterministic_ number generator:
:::

Or suppose that we want to extend the arithmetic operations by a
nondeterministic number generator `any` that, when evaluated, may
yield any number.  (This is not the same as making a _probabilistic_
choice among all numbers -- we only say which results are _possible_.)

```lean
inductive Aexp where
  | any                            -- NEW
  | num (n : Nat)
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)
```

Again, extending `Aexp.eval` would be tricky, since evaluation is now _not_
a deterministic function from expressions to numbers; but extending the
relation is no problem.

:::terse
What should `Aexp.eval` do with nondeterminism??
:::

```lean
inductive Aexp.evalR : Aexp → Nat → Prop where
  | E_Any (n : Nat) : Aexp.evalR .any n                   -- NEW
  | E_ANum (n : Nat) : Aexp.evalR (.num n) n
  | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.plus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.minus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.mult a1 a2) (n1 * n2)

end AevalRExtended
```

:::dev
mwhicks1: The following text seems not quite right to me. First, you can
use options for partial functions, and that's very natural to do in Lean
as a monad. Second, and related, monadic functions need not even be
terminating if the implement the `CCPO` typeclass and are labeled as
a `partial_fixpoint`. Maybe we don't want to get into the second thing here,
but failing to mention options (which I think were introduced in LF) seems
a bit surprising.
:::

::::full
At this point you may be wondering: which of these styles should I use
by default?

Where the thing being defined is not easy to express as a function --
or is genuinely _not_ a function -- there is no real choice. When both
styles are workable, relational definitions can be more elegant and
easier to understand, and Lean generates useful inversion and induction
principles from them. On the other hand, functional definitions are
automatically deterministic and total (for a relation we must _prove_
these if we need them), and we can use Lean's computation mechanism to
simplify them during proofs.

In large developments it is common to give a definition in _both_
styles plus a lemma that the two coincide, allowing later proofs to
switch between points of view at will -- exactly what we did above.
::::

:::terse
Functional: computation. Relational: expressive. Best: both, proved equivalent.
:::

# Expressions With Variables

::::full
Let's return to defining Imp. The next thing we need to do is to
enrich our arithmetic and boolean expressions with variables. To keep
things simple, we'll assume that all variables are global and that they
only hold numbers.
::::

## States

:::dev
LATER: Maybe this section needs a little preface talking about "what is
   the meaning of an expression with variables?"...

LATER: (Note copied from Equiv right before the `assign_aequiv`
   exercise): Some or all of this discussion should really happen when
   states are introduced in Imp.v, and the whole idea of treating states as
   an ADT should be raised there.
:::

Since we'll want to look variables up to find out their current values,
we'll use total maps from the `Maps` chapter. A _machine state_ (or
just _state_) represents the current values of all variables at some
point in the execution of a program.

::::full
For simplicity, we assume that the state is defined for _all_ variables,
even though any given program is only able to mention a finite number of
them. Because each variable stores a natural number, we represent the
state as a total map from strings (variable names) to `Nat`, and will use
`0` as the default value in the store.
::::

We give the type of variable identifiers a name, `Ident`. For now it is just
   `String`; naming it makes the intent clearer.

```lean
abbrev Ident := String
abbrev State := TotalMap Ident Nat
```

## Syntax

We can add variables to the arithmetic expressions we had before simply
by including one more constructor.  (This is a fresh `Aexp`, replacing
the variable-free one from the `Warmup` namespace above.)

```lean
inductive Aexp where
  | num (n : Nat)
  | id (x : Ident)                -- NEW
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)
```

:::dev
chenson2018: Rather than define identifiers as Ident, a more general approach is
to use a *type variable* with `DecidableEq` (as the
`Maps` chapter does), threaded through `Aexp`/`Bexp`/`Com`/`State`.  Stashed
for a future decision; the parameterized version would look like:

```
inductive Aexp (V : Type) where
  | num (n : Nat)
  | id (x : V)
  | plus (a1 a2 : Aexp V)
  | minus (a1 a2 : Aexp V)
  | mult (a1 a2 : Aexp V)
-- … then `Bexp V`, `Com V`, `abbrev State (V) [DecidableEq V] :=
-- TotalMap V Nat`, and `[DecidableEq V]` wherever a lookup/update is
-- performed.
```
:::

The `Bexp` definition is unchanged, except that it now refers to the new `Aexp`.

```lean
inductive Bexp where
  | bool (b : Bool)
  | eq (a1 a2 : Aexp)
  | neq (a1 a2 : Aexp)
  | le (a1 a2 : Aexp)
  | gt (a1 a2 : Aexp)
  | not (b : Bexp)
  | and (b1 b2 : Bexp)
```

Defining a few variable names as shorthands will make examples easier
   to read.

:::instructors
We usually don't use x as a "bare identifier" in examples
   -- it is normally wrapped in an id constructor.  If this were _always_
   the case, then it would make more sense to define the notation `[x]` to
   mean `[id (Id 0)]`.  But there quite a few counterexamples. Maybe we
   could define `[xx]` to mean `[id (Id 0)]`, or some such? But it's still
   awkward.
   BCP/AAA 2/16: Should we use a coercion for this?  It means introducing a
   new concept -- a somewhat magical one -- but it will make examples look
   quite a bit nicer...
   BCP 11/16: It will also solve some problems later on with confusions
   about bound identifiers in Stlc vs. "global" ones in Imp. I think it's a
   good idea to try it for the next big revision.
   ET 10/17: coercions and notations are done, see below.  (still keeping
   the global variables W, X, Y, Z for readability)
   BCP 7/20: This still needs another look to see if there's a way to make
   it globally better.
:::

```lean
def W : Ident := "W"
def X : Ident := "X"
def Y : Ident := "Y"
def Z : Ident := "Z"
```

::::full
(This convention for naming program variables (`X`, `Y`, `Z`) clashes a
bit with our earlier use of uppercase letters for types. Since we're not
using polymorphism heavily in the chapters developed to Imp, this
overloading should not cause confusion.)
::::

## Notations

::::full
To make Imp programs easier to read and write, we introduce some notations and implicit
coercions.

You do not need to understand exactly what these declarations do. Briefly, though:

- The `declare_syntax_cat` directive adds a new non-terminal to Lean's grammar, called
  `imp_aexp`. We'll add additional non-terminals further below.
- Each `syntax` directive defines a grammar production, of which there are eight in
  total. The first two define literals, `num` and `ident`, as `imp_aexp`s. The next
  deveral directives define productions for building larger expressions, with
  some annotations to define precedence, etc.
- Finally, `macro_rules` is used to translate each production of the `imp_aexp` nonterminal
  into a Lean expression.
- The same basic pattern is followed for `bexp`s too.
::::

```lean
/-- Arithmetic expressions of Imp -/
declare_syntax_cat imp_aexp
/-- Numeric literal -/
syntax:max num : imp_aexp
/-- Variable reference -/
syntax:max ident : imp_aexp
/-- Addition -/
syntax:65 imp_aexp:65 " + " imp_aexp:66 : imp_aexp
/-- Subtraction -/
syntax:65 imp_aexp:65 " - " imp_aexp:66 : imp_aexp
/-- Multiplication -/
syntax:70 imp_aexp:70 " * " imp_aexp:71 : imp_aexp
/-- Parentheses for grouping -/
syntax "(" imp_aexp ")" : imp_aexp
/-- Escape to Lean -/
syntax:max "~" term:max : imp_aexp

/-- Embed an Imp arithmetic expression into a Lean term -/
syntax:min "aexp " "{" imp_aexp "}" : term
```

:::instructors
A variable reference elaborates to `Aexp.id $x` with the identifier spliced
as a *term*, not as a string literal. So `aexp { X }` is `Aexp.id X`, using
the declared constant `X : Ident`, exactly matching hand-written terms like
`.asgn X …` and the shape the state/`ceval` proofs expect. (Rocq's `<{ }>`
does the same via its `constr` fallback, yielding `AId X`.) A consequence is
that a variable name must be a declared `Ident` constant — as W/X/Y/Z are.
:::

```lean
open Lean in
macro_rules
  | `(aexp { $n:num }) => `(Aexp.num $(quote n.getNat))
  | `(aexp { $x:ident }) => `(Aexp.id $x)
  | `(aexp { ~$e }) => pure e
  | `(aexp { $a + $b }) => `(Aexp.plus (aexp {$a}) (aexp {$b}))
  | `(aexp { $a - $b }) => `(Aexp.minus (aexp {$a}) (aexp {$b}))
  | `(aexp { $a * $b }) => `(Aexp.mult (aexp {$a}) (aexp {$b}))
  | `(aexp { ($a) }) => `(aexp {$a})
```

:::instructors
The literals `true`/`false` are accepted through the bare-identifier form
(`syntax:max ident : imp_bexp`) and turned into `Bexp.bool` by the macro
below, which rejects any other identifier. We take this route rather than
declaring `true`/`false` as symbols: as reserved keywords they would break
ordinary Lean uses of `true`/`false`, and as non-reserved symbols they would
clash with the bare-identifier form of `imp_aexp`.
:::

```lean
/-- Boolean expressions of Imp -/
declare_syntax_cat imp_bexp
/-- Boolean literal (`true` or `false`) -/
syntax:max ident : imp_bexp
/-- Equality of arithmetic expressions -/
syntax:50 imp_aexp:51 " = " imp_aexp:51 : imp_bexp
/-- Disequality of arithmetic expressions -/
syntax:50 imp_aexp:51 " <> " imp_aexp:51 : imp_bexp
/-- Less than or equal -/
syntax:50 imp_aexp:51 " <= " imp_aexp:51 : imp_bexp
/-- Greater than -/
syntax:50 imp_aexp:51 " > " imp_aexp:51 : imp_bexp
/-- Boolean negation -/
syntax:70 "! " imp_bexp:70 : imp_bexp
/-- Boolean conjunction -/
syntax:35 imp_bexp:36 " && " imp_bexp:35 : imp_bexp
/-- Parentheses for grouping -/
syntax "(" imp_bexp ")" : imp_bexp
/-- Escape to Lean -/
syntax:max "~" term:max : imp_bexp

/-- Embed an Imp boolean expression into a Lean term -/
syntax:min "bexp " "{" imp_bexp "}" : term
```

:::instructors
The antiquotations are annotated with their category (`$a:imp_aexp`,
`$b:imp_bexp`) because an `imp_bexp` can begin with an `imp_aexp` (a
comparison); without the annotation the parser would descend into `imp_aexp`
and then insist on a comparison operator.
:::

```lean
open Lean in
macro_rules
  | `(bexp { $x:ident }) =>
    match x.getId with
    | `true  => `(Bexp.bool true)
    | `false => `(Bexp.bool false)
    | _      => Macro.throwErrorAt x s!"expected 'true' or 'false', got '{x.getId}'"
  | `(bexp { ~$e }) => pure e
  | `(bexp { $a:imp_aexp = $b:imp_aexp }) => `(Bexp.eq (aexp {$a}) (aexp {$b}))
  | `(bexp { $a:imp_aexp <> $b:imp_aexp }) => `(Bexp.neq (aexp {$a}) (aexp {$b}))
  | `(bexp { $a:imp_aexp <= $b:imp_aexp }) => `(Bexp.le (aexp {$a}) (aexp {$b}))
  | `(bexp { $a:imp_aexp > $b:imp_aexp }) => `(Bexp.gt (aexp {$a}) (aexp {$b}))
  | `(bexp { ! $b:imp_bexp }) => `(Bexp.not (bexp {$b}))
  | `(bexp { $b1:imp_bexp && $b2:imp_bexp }) => `(Bexp.and (bexp {$b1}) (bexp {$b2}))
  | `(bexp { ($b:imp_bexp) }) => `(bexp {$b})
```

::::full
We make it a little easier to write Imp programs using normal constructors (i.e.,
without notation), by using _implicit coercions_.
In Lean, a `Coe` instance tells the elaborator how to turn a
value of one type into another automatically:
 - `Coe Ident Aexp` lets us write a bare variable (an `Ident`) where an
   `Aexp` is expected; the identifier is implicitly wrapped with `id`.
 - `OfNat Aexp n` lets us write a numeric literal where an `Aexp` is
   expected; it is implicitly wrapped with `num`.
 - `Coe Bool Bexp` lets us write a boolean literal (`true`/`false`) where a
   `Bexp` is expected; it is implicitly wrapped with `bool`.
::::

```lean
instance : Coe Ident Aexp where
  coe := .id

instance (n : Nat) : OfNat Aexp n where
  ofNat := .num n

instance : Coe Bool Bexp where
  coe := .bool
```

::::full
With these coercions we can write `.plus 3 (.mult X 2)` instead of the fully
   explicit `.plus (.num 3) (.mult (.id "X") (.num 2))`, and `.and true (.not …)`
   instead of `.and (.bool true) (.not …)`. More readably still, the concrete
   syntax from the Notations section lets us write these examples directly:
::::

```lean
def example_aexp : Aexp := aexp { 3 + (X * 2) }
def example_bexp : Bexp := bexp { true && !(X <= 4) }
```

## Delaborators

::::full
The notations above are _input_ only: they teach Lean how to *read* `aexp
{ … }` and `bexp { … }`, but Lean still *prints* an expression using its raw
constructors -- `example_aexp` shows up as `Aexp.plus (Aexp.num 3) …` rather
than `aexp { 3 + X * 2 }`. A _delaborator_ closes the loop. Where a `macro`
turns surface syntax into a term (_elaboration_), a delaborator does the
reverse: it turns an elaborated term back into surface syntax so that Lean's
own output uses our concrete Imp notation.

Each delaborator below walks a term of the given type and rebuilds the
matching piece of `imp_aexp`/`imp_bexp` syntax; a subterm Lean doesn't
recognize is printed with the `~` escape. The `@[delab …]` attribute
registers the top-level function to fire whenever Lean is about to display a
term headed by one of those constructors -- unless notation printing has been
switched off with `set_option pp.notation false`, which lets us fall back to
the raw constructors when debugging (see _Desugaring Notations_ below). The
companion _category parenthesizer_ re-inserts the parentheses the grammar's
precedences demand, so that, e.g., `(1 + 2) * 3` prints with its parentheses
intact.

You do not need to understand the details. The result is that a `#check`, an
`#eval`, or a proof goal mentioning an Imp expression is displayed in
readable Imp syntax rather than as a pile of constructors.
::::

```lean
namespace Imp.Delab
open Lean PrettyPrinter Delaborator SubExpr Parenthesizer

/-- Re-inserts parentheses in `imp_aexp` output according to the grammar's precedences. -/
@[category_parenthesizer imp_aexp]
def imp_aexp.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `imp_aexp true wrapParens prec <|
    parenthesizeCategoryCore `imp_aexp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

/-- Re-inserts parentheses in `imp_bexp` output according to the grammar's precedences. -/
@[category_parenthesizer imp_bexp]
def imp_bexp.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `imp_bexp true wrapParens prec <|
    parenthesizeCategoryCore `imp_bexp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

/-- Tag freshly built syntax with the term info that Lean's pretty printer expects. -/
def annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

/-- Rebuild `imp_aexp` concrete syntax from an `Aexp` term. -/
partial def delabAexpInner : DelabM (TSyntax `imp_aexp) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | Aexp.num _ =>
      match (← withAppArg getExpr).nat? with
      | some v => pure ⟨Syntax.mkNumLit (toString v) |>.raw⟩
      | none   => `(imp_aexp| ~$(← withAppArg delab))
    | Aexp.id _ =>
      -- A variable reference like aexp { X } elaborates to Aexp.id X where X is the declared Ident constant, so the delaborators print the constant's name as a bare identifier (and also handle the .id "X" string-literal form).
      match ← withAppArg getExpr with
      | .const nm _      => `(imp_aexp| $(mkIdent nm):ident)
      | .lit (.strVal s) => `(imp_aexp| $(mkIdent (.mkSimple s)):ident)
      | _                => `(imp_aexp| ~$(← withAppArg delab))
    | Aexp.plus _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_aexp| $s1 + $s2)
    | Aexp.minus _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_aexp| $s1 - $s2)
    | Aexp.mult _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_aexp| $s1 * $s2)
    | _ => `(imp_aexp| ~$(← delab))
  annAsTerm stx

/-- Rebuild `imp_bexp` concrete syntax from a `Bexp` term. -/
partial def delabBexpInner : DelabM (TSyntax `imp_bexp) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | Bexp.bool _ =>
      match ← withAppArg getExpr with
      | .const ``Bool.true _  => `(imp_bexp| $(mkIdent `true):ident)
      | .const ``Bool.false _ => `(imp_bexp| $(mkIdent `false):ident)
      | _                     => `(imp_bexp| ~$(← withAppArg delab))
    | Bexp.eq _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_bexp| $s1:imp_aexp = $s2:imp_aexp)
    | Bexp.neq _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_bexp| $s1:imp_aexp <> $s2:imp_aexp)
    | Bexp.le _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_bexp| $s1:imp_aexp <= $s2:imp_aexp)
    | Bexp.gt _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_bexp| $s1:imp_aexp > $s2:imp_aexp)
    | Bexp.not _ =>
      let s ← withAppArg delabBexpInner
      `(imp_bexp| ! $s)
    | Bexp.and _ _ =>
      let s1 ← withAppFn <| withAppArg delabBexpInner
      let s2 ← withAppArg delabBexpInner
      `(imp_bexp| $s1 && $s2)
    | _ => `(imp_bexp| ~$(← delab))
  annAsTerm stx
```

The `whenPPOption getPPNotation` wrapper lets `set_option pp.notation false`
switch this delaborator off, revealing the raw constructors (see the
"Desugaring Notations" discussion, after the commands are introduced).

```lean
@[delab app.Aexp.num, delab app.Aexp.id, delab app.Aexp.plus,
  delab app.Aexp.minus, delab app.Aexp.mult]
partial def delabAexp : Delab := whenPPOption getPPNotation do
  -- This delaborator only understands `Aexp`'s constructors -- bail otherwise.
  guard <| match_expr ← getExpr with
    | Aexp.num _ => true
    | Aexp.id _ => true
    | Aexp.plus _ _ => true
    | Aexp.minus _ _ => true
    | Aexp.mult _ _ => true
    | _ => false
  match ← delabAexpInner with
  | `(imp_aexp| ~$e) => pure e
  | e => `(term| aexp { $e })

@[delab app.Bexp.bool, delab app.Bexp.eq, delab app.Bexp.neq, delab app.Bexp.le,
  delab app.Bexp.gt, delab app.Bexp.not, delab app.Bexp.and]
partial def delabBexp : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Bexp.bool _ => true
    | Bexp.eq _ _ => true
    | Bexp.neq _ _ => true
    | Bexp.le _ _ => true
    | Bexp.gt _ _ => true
    | Bexp.not _ => true
    | Bexp.and _ _ => true
    | _ => false
  match ← delabBexpInner with
  | `(imp_bexp| ~$e) => pure e
  | e => `(term| bexp { $e })

end Imp.Delab
```

::::full
With the delaborators in place, Lean now prints Imp expressions using the
concrete syntax rather than their raw constructors.
::::

```lean
/-- info: aexp {3 + X * 2} : Aexp -/
#guard_msgs in
#check aexp { 3 + (X * 2) }

/-- info: bexp {true && ! (X <= 4)} : Bexp -/
#guard_msgs in
#check bexp { true && !(X <= 4) }
```

## Evaluation

::::full
The arithmetic and boolean evaluators must now be extended to handle
variables, taking a state `st` as an extra argument.  A variable is
looked up in the state with the map-indexing notation `st[x]` from the
`Maps` chapter.
::::

:::terse
Now we need to add an `st` parameter to both evaluation functions:
:::

```lean
def Aexp.eval (st : State) (a : Aexp) : Nat :=
  match a with
  | num   n     =>  n
  | id    x     =>  st[x]                    -- NEW
  | plus  a1 a2 =>  eval st a1 + eval st a2
  | minus a1 a2 =>  eval st a1 - eval st a2
  | mult  a1 a2 =>  eval st a1 * eval st a2

def Bexp.eval (st : State) (b : Bexp) : Bool :=
  match b with
  | bool b      =>  b
  | eq   a1 a2  =>  a1.eval st == a2.eval st
  | neq  a1 a2  =>  a1.eval st != a2.eval st
  | le   a1 a2  =>  a1.eval st ≤  a2.eval st
  | gt   a1 a2  =>  a1.eval st >  a2.eval st
  | not  b1     =>  !b1.eval st
  | and  b1 b2  =>  b1.eval st && b2.eval st
```

We reuse the total-map notation (`x →ₜ v ; ∅` etc.) for states.

```lean
example : aexp { 3 + (X * 2) }.eval (X →ₜ 5 ; ∅) = 13 := by rfl

example : aexp { Z + (X * Y) }.eval (X →ₜ 5 ; Y →ₜ 4 ; ∅) = 20 := by rfl

example : bexp { true && !(X <= 4) }.eval (X →ₜ 5 ; ∅) = true := by rfl
```

:::dev
dsainati: Bikeshedding: I'm not sure how I feel about this arrow subscript for maps. Easy to change later but just flagging to discuss. mwhicks1: This comes from the Maps chapter, which chenson2018 is working on. There is a keyboard shortcut for ↦ we could use (\mapsto).
:::

# Commands

::::full
Now we are ready to define the syntax and behavior of Imp _commands_
(or _statements_). Informally, commands `c` are described by the
following BNF grammar:

```
c := skip
   | x := a
   | c ; c
   | if b then c else c end
   | while b do c end
```

Here is the formal definition of the abstract syntax of commands.
::::

```lean
inductive Com where
  | skip
  | asgn (x : Ident) (a : Aexp)
  | seq (c1 c2 : Com)
  | cond (b : Bexp) (c1 c2 : Com)
  | whileDo (b : Bexp) (c : Com)
```

Concrete syntax for commands, in the style of the `ssft24` Imp `Stmt`
   grammar: an `imp_com` category with an `imp { … }` hook. Assignments and
   `skip` end in `;`, and sequencing is written by juxtaposition. Conditions use
   the `imp_bexp` grammar; the branch/loop bodies use the `imp_com` grammar. As
   with expressions, `~c` escapes back to an ordinary Lean term of type `Com`.

```lean
/-- Imp commands -/
declare_syntax_cat imp_com
```

`skip` is *not* a reserved keyword: it is accepted through a bare
   identifier-terminated command (`syntax ident ";" : imp_com`) and recognised
   in the macro below, which rejects any other identifier. This keeps `skip`
   usable as the bare constructor name `Com.skip` in `match`/`induction`
   elsewhere in the file, and avoids reserving `skip` globally.

```lean
/-- The command that does nothing (`skip;`) -/
syntax ident ";" : imp_com
/-- Sequencing: one command after another -/
syntax imp_com ppDedent(ppLine imp_com) : imp_com
/-- Assignment -/
syntax ident " := " imp_aexp ";" : imp_com
/-- Conditional -/
syntax "if " "(" imp_bexp ")" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}" ppHardSpace "else" ppHardSpace "{") ppLine imp_com ppDedent(ppLine "}") : imp_com
/-- Loop -/
syntax "while " "(" imp_bexp ")" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}") : imp_com
/-- Escape to Lean -/
syntax:max "~" term:max : imp_com

/-- Include an Imp command in Lean code -/
syntax:min "imp" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}") : term

open Lean in
macro_rules
  | `(imp { $x:ident ; }) =>
    if x.getId == `skip then `(Com.skip)
    else Macro.throwErrorAt x s!"expected 'skip', got '{x.getId}'"
  | `(imp { $c1 $c2 }) =>
    `(Com.seq (imp {$c1}) (imp {$c2}))
  | `(imp { $x:ident := $a; }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c1} else {$c2} }) =>
    `(Com.cond (bexp {$b}) (imp {$c1}) (imp {$c2}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { ~$c }) =>
    pure c
```

::::full
Just as we did for expressions, we add a delaborator so that Lean prints
commands back in the `imp { … }` concrete syntax (see the Delaborators
section above). It reuses the expression delaborators for the condition of an
`if`/`while` and for the right-hand side of an assignment, and prints an
unrecognized subcommand with the `~` escape.
::::

```lean
namespace Imp.Delab
open Lean PrettyPrinter Delaborator SubExpr

/-- Rebuild `imp_com` concrete syntax from a `Com` term. -/
partial def delabComInner : DelabM (TSyntax `imp_com) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | Com.skip => `(imp_com| skip;)
    | Com.asgn _ _ =>
      match ← withAppFn <| withAppArg getExpr with
      | .const nm _ =>
        let a ← withAppArg delabAexpInner
        `(imp_com| $(mkIdent nm):ident := $a;)
      | .lit (.strVal s) =>
        let a ← withAppArg delabAexpInner
        `(imp_com| $(mkIdent (.mkSimple s)):ident := $a;)
      | _ => `(imp_com| ~$(← delab))
    | Com.seq _ _ =>
      let s1 ← withAppFn <| withAppArg delabComInner
      let s2 ← withAppArg delabComInner
      `(imp_com| $s1 $s2)
    | Com.cond _ _ _ =>
      let b  ← withAppFn <| withAppFn <| withAppArg delabBexpInner
      let c1 ← withAppFn <| withAppArg delabComInner
      let c2 ← withAppArg delabComInner
      `(imp_com| if ($b) {$c1} else {$c2})
    | Com.whileDo _ _ =>
      let b ← withAppFn <| withAppArg delabBexpInner
      let c ← withAppArg delabComInner
      `(imp_com| while ($b) {$c})
    | _ => `(imp_com| ~$(← delab))
  annAsTerm stx

@[delab app.Com.skip, delab app.Com.asgn, delab app.Com.seq,
  delab app.Com.cond, delab app.Com.whileDo]
partial def delabCom : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Com.skip => true
    | Com.asgn _ _ => true
    | Com.seq _ _ => true
    | Com.cond _ _ _ => true
    | Com.whileDo _ _ => true
    | _ => false
  match ← delabComInner with
  | `(imp_com| ~$e) => pure e
  | e => `(term| imp { $e })

end Imp.Delab
```

::::full
As an example, here is the factorial function again, written as a formal
definition. When this command terminates, the variable `Y` will
contain the factorial of the initial value of `X`.  (Compare this to
the concrete Imp program at the very start of the chapter.)
::::

```lean
def fact_in_lean : Com := imp {
  Z := X;
  Y := 1;
  while (Z <> 0) {
    Y := Y * Z;
    Z := Z - 1;
  }
}
```

::::full
Because we registered a delaborator, we can inspect a defined program with
`#print`, which shows the stored definition using the same concrete syntax:
::::

```lean
/--
info: def fact_in_lean : Com :=
imp {
  Z := X;
  Y := 1;
  while (Z <> 0) {
    Y := Y * Z;
    Z := Z - 1;
  }
}
-/
#guard_msgs in
#print fact_in_lean
```

## Desugaring Notations

::::full
The `imp { … }` notation, together with the delaborators, is purely a
convenience for reading and writing programs. Occasionally, such as when debugging
a definition or a stuck proof, the concrete syntax `hide`s the underlying structure
we want to see. For those moments we can switch the Imp notation off in Lean's
output with `set_option pp.notation false`, which our delaborators honor.

Note that unlike a `def`, `imp { … }` is a `macro` which is expanded during elaboration,
*before* the resulting term is type-checked. So `fact_in_lean` is not a
program hidden behind a layer of notation that a proof must first peel back;
it simply *is* the underlying tree of `Com`, `Aexp`, and `Bexp` constructors.
Consequently, when a proof goal mentions an Imp program, tactics such as
`cases`, `injection`, and `simp` already act on those constructors directly
-- there is nothing to "unfold". The delaborators affect only how that tree
is *displayed*. Nevertheless, seeing the raw constructors is sometimes very helpful!
::::

```lean
/-- info: imp {
  X := X + 1;
} : Com -/
#guard_msgs in
#check imp { X := X + 1; }

/-- info: Com.asgn X ((Aexp.id X).plus (Aexp.num 1)) : Com -/
#guard_msgs in
set_option pp.notation false in
#check imp { X := X + 1; }
```

## More Examples

A few more examples.

:::slidebreak
:::

Assignment:

```lean
def plus2 : Com := imp { X := X + 2; }
def XtimesYinZ : Com := imp { Z := X * Y; }
```

:::slidebreak
:::

Loops:

```lean
def subtract_slowly_body : Com := imp {
  Z := Z - 1;
  X := X - 1;
}

def subtract_slowly : Com := imp {
  while (X <> 0) {
    ~subtract_slowly_body
  }
}

def subtract_3_from_5_slowly : Com := imp {
  X := 3;
  Z := 5;
  ~subtract_slowly
}
```

:::slidebreak
:::

An infinite loop:

```lean
def loop : Com := imp { while (true) { skip; } }
```

::::hide
```
/- Exponentiation: -/
def exp_body : Com := imp {
  Z := Z * X;
  Y := Y - 1;
}
def pexp : Com := imp {
  while (Y <> 0) {
    ~exp_body
  }
}
/- (Note that `pexp` should be run in a state where `Z` is `1`.) -/
```
::::

# Evaluating Commands

::::full
Next we need to define what it means to evaluate an Imp command.  The
fact that `while` loops don't necessarily terminate makes defining an
evaluation function tricky.
::::

## Evaluation as a Function (Failed Attempt)

Here's an attempt at defining an evaluation function for commands (with
a bogus `while` case).

:::dev
LATER: In SmallStep we need to package the state and command into a pair,
   so that we can talk about normal forms and such. Probably we should do it
   here too, for consistency. (Won't change much except the type
   declarations, but we'll need to add a comment why we wrote them this
   way.)
:::

```lean
def Com.ceval_fun_no_while (st : State) (c : Com) : State :=
  match c with
  | imp {skip;} => st
  | imp {x := ~a;} => (x →ₜ Aexp.eval st a ; st)
  | imp {~c1 ~c2} =>
      let st' := ceval_fun_no_while st c1
      ceval_fun_no_while st' c2
  | imp {if (~b) {~c1} else {~c2}} =>
      if Bexp.eval st b then ceval_fun_no_while st c1
      else ceval_fun_no_while st c2
  | imp {while (~_) {~_}} => st     -- bogus
```

::::full
In a more conventional functional language like OCaml or Haskell we
could add the `while` case as follows:

```
| .whileDo b c =>
    if Bexp.eval st b then ceval_fun st (.seq c (.whileDo b c))
    else st
```

Lean doesn't accept such a definition ("fail to show termination")
because the function we want to define is not guaranteed to terminate.
Indeed, it _doesn't_ always terminate: the full `ceval_fun` applied to
the `loop` program above would run forever. Since Lean aims to be not
just a programming language but also a consistent logic, any
potentially non-terminating function must be rejected. Here is what
would go wrong if Lean allowed non-terminating recursive functions:

```
def loop_false (n : Nat) : False := loop_false n
```

That is, propositions like `False` would become provable (`loop_false 0`
would be a proof of `False`), a disaster for logical consistency.

Thus, because it doesn't terminate on all inputs, the full `ceval_fun`
cannot be written in Lean -- at least not without additional tricks and
workarounds.
::::

:::dev
   Perhaps that discussion should be moved to -- or previewed in --
   Logic.v?  MRC'20: It's already in ProofObjects (which not everyone
   sees).
:::

:::terse
A nonterminating `def loop_false (n) : False := loop_false n` would make `False` provable, so Lean rejects it.
:::

## Evaluation as a Relation

Here's a better way: define `ceval` as a _relation_ rather than a
_function_ -- i.e., make its result a `Prop` rather than a `State`,
similar to what we did for `Aexp.evalR` above.

::::full
This is an important change. Besides freeing us from awkward workarounds,
it gives us more flexibility in the definition. For example, if we
add nondeterministic features like `any` to the language, we want the
definition of evaluation to be nondeterministic -- i.e., not only will it
not be total, it will not even be a function!
::::

:::dev
mwhicks1: I kind of hate this notation. Is there something more standard
in Lean? CSLib precedent maybe?
:::

We'll use the notation `st =[ c ]=> st'` for the `ceval` relation:
`st =[ c ]=> st'` means that executing program `c` in a starting state
`st` results in an ending state `st'`.  This can be pronounced "`c` takes
state `st` to `st'`".

:::slidebreak
:::

Operational Semantics

:::dev
SOONER: BCP 21: I wonder if `E_Seq` would be easier to work with if st' and
   st'' were swapped...
:::

Here is an informal definition of evaluation, presented as inference rules
for readability:

```
                      -----------------                  (E_Skip)
                      st =[ skip ]=> st

                      Aexp.eval st a = n
              --------------------------------           (E_Asgn)
              st =[ x := a ]=> (x →ₜ n ; st)

                      st  =[ c1 ]=> st'
                      st' =[ c2 ]=> st''
                    ---------------------                (E_Seq)
                    st =[ c1;c2 ]=> st''

                     Bexp.eval st b = true
                      st =[ c1 ]=> st'
           --------------------------------------        (E_IfTrue)
           st =[ if b then c1 else c2 end ]=> st'

                    Bexp.eval st b = false
                      st =[ c2 ]=> st'
           --------------------------------------        (E_IfFalse)
           st =[ if b then c1 else c2 end ]=> st'

                    Bexp.eval st b = false
               -----------------------------             (E_WhileFalse)
               st =[ while b do c end ]=> st

                     Bexp.eval st b = true
                      st =[ c ]=> st'
             st' =[ while b do c end ]=> st''
             --------------------------------            (E_WhileTrue)
             st  =[ while b do c end ]=> st''
```

Here is the formal definition.  Make sure you understand how it
corresponds to the inference rules.

```lean
inductive Ceval : Com → State → State → Prop where
  | E_Skip (st : State) :
      Ceval (imp {skip;}) st st
  | E_Asgn (st : State) (a : Aexp) (n : Nat) (x : Ident)
      (h : Aexp.eval st a = n) :
      Ceval (imp {x := ~a;}) st (x →ₜ n ; st)
  | E_Seq (c1 c2 : Com) (st st' st'' : State)
      (h1 : Ceval c1 st st') (h2 : Ceval c2 st' st'') :
      Ceval (imp {~c1 ~c2}) st st''
  | E_IfTrue (st st' : State) (b : Bexp) (c1 c2 : Com)
      (hb : Bexp.eval st b = true) (hc : Ceval c1 st st') :
      Ceval (imp {if (~b) {~c1} else {~c2}}) st st'
  | E_IfFalse (st st' : State) (b : Bexp) (c1 c2 : Com)
      (hb : Bexp.eval st b = false) (hc : Ceval c2 st st') :
      Ceval (imp {if (~b) {~c1} else {~c2}}) st st'
  | E_WhileFalse (b : Bexp) (st : State) (c : Com)
      (hb : Bexp.eval st b = false) :
      Ceval (imp {while (~b) {~c}}) st st
  | E_WhileTrue (st st' st'' : State) (b : Bexp) (c : Com)
      (hb : Bexp.eval st b = true) (hc : Ceval c st st')
      (hloop : Ceval (imp {while (~b) {~c}}) st' st'') :
      Ceval (imp {while (~b) {~c}}) st st''

notation:40 st0 " =[ " c " ]=> " st1 => Ceval c st0 st1
```

The cost of defining evaluation as a relation instead of a function is
that we now need to construct a _proof_ that some program evaluates to
some result state, rather than letting Lean's computation mechanism do
it for us.

```lean
example :
    ∅ =[ imp {
           X := 2;
           if (X <= 1) {
             Y := 3;
           } else {
             Z := 4;
           }
         } ]=> (Z →ₜ 4 ; X →ₜ 2 ; ∅) := by
  -- We must supply the intermediate state.
  apply Ceval.E_Seq (st' := (X →ₜ 2 ; ∅))
  · apply Ceval.E_Asgn; rfl
  · apply Ceval.E_IfFalse
    · rfl
    · apply Ceval.E_Asgn; rfl
```

:::::exercise (rating := 2) (name := "ceval_example2")
```lean
example :
    ∅ =[ imp {
           X := 0;
           Y := 1;
           Z := 2;
         } ]=> (Z →ₜ 2 ; Y →ₜ 1 ; X →ₜ 0 ; ∅) := by
  solution!
    apply Ceval.E_Seq (st' := (X →ₜ 0 ; ∅))
    · apply Ceval.E_Asgn; rfl
    · apply Ceval.E_Seq (st' := (Y →ₜ 1 ; X →ₜ 0 ; ∅))
      · apply Ceval.E_Asgn; rfl
      · apply Ceval.E_Asgn; rfl
```
:::::

:::terse
What sorts of things might we want to prove using these definitions?  Here are some simple examples...
:::

:::dev
  PR: I phrased these quizzes with the following alternatives:
   (A) Not true
   (B) True and easily provable
   (C) True and takes more work to prove
   (D) True and cannot be proved without additional axioms
:::

::::quiz
Is the following proposition provable?

```
∀ (c : Com) (st st' : State),
  st =[ imp { skip; ~c } ]=> st' →
  st =[ c ]=> st'
```

(A) Yes    (B) No    (C) Not sure

:::answer
```
theorem quiz1_answer (c : Com) (st st' : State)
    (h : st =[ imp { skip; ~c } ]=> st') : st =[ c ]=> st' := by
  cases h with
  | E_Seq _ _ _ smid _ h1 h2 =>
      cases h1 with
      | E_Skip _ => exact h2
```
:::
::::

::::quiz
Is the following proposition provable?

```
∀ (c1 c2 : Com) (st st' : State),
  st =[ imp { ~c1 ~c2 } ]=> st' →
  st =[ c1 ]=> st →
  st =[ c2 ]=> st'
```

(A) Yes    (B) No    (C) Not sure

:::instructors
Answer is given later (`quiz2_answer`) as it depends on `ceval_deterministic`.
:::
::::

::::quiz
Is the following proposition provable?

```
∀ (b : Bexp) (c : Com) (st st' : State),
  st =[ imp { if (~b) { ~c } else { ~c } } ]=> st' →
  st =[ c ]=> st'
```

(A) Yes    (B) No    (C) Not sure

:::answer
```
theorem quiz3_answer (b : Bexp) (c : Com) (st st' : State)
    (h : st =[ imp { if (~b) { ~c } else { ~c } } ]=> st') : st =[ c ]=> st' := by
  cases h with
  | E_IfTrue _ _ _ _ _ hb hc => exact hc
  | E_IfFalse _ _ _ _ _ hb hc => exact hc
```
:::
::::

::::quiz
Is the following proposition provable?

```
∀ (b : Bexp),
  (∀ st, Bexp.eval st b = true) →
  ∀ (c : Com) (st : State),
  ¬ ∃ st', st =[ imp { while (~b) { ~c } } ]=> st'
```

(A) Yes    (B) No    (C) Not sure

:::answer
```
-- This one is tricky!
theorem quiz4_answer (b : Bexp) (hbtrue : ∀ st, Bexp.eval st b = true)
    (c : Com) (st : State) : ¬ ∃ st', st =[ imp { while (~b) { ~c } } ]=> st' := by
  rintro ⟨st', hev⟩
  have key : ∀ (cmd : Com) (s s' : State),
      (s =[ cmd ]=> s') → cmd = (imp { while (~b) { ~c } }) → False := by
    intro cmd s s' hce
    induction hce with
    | E_WhileFalse b0 s0 c0 hbf =>
        intro heq; injection heq with e1 _; subst e1
        rw [hbtrue s0] at hbf; simp at hbf
    | E_WhileTrue s0 s0' s0'' b0 c0 hbt hc0 hloop ih1 ih2 =>
        intro heq; exact ih2 heq
    | E_Skip s0 => intro heq; simp at heq
    | E_Asgn s0 a n x h => intro heq; simp at heq
    | E_Seq d1 d2 s0 s0' s0'' hh1 hh2 ih1 ih2 => intro heq; simp at heq
    | E_IfTrue s0 s0' b0 d1 d2 hb0 hc0 ih => intro heq; simp at heq
    | E_IfFalse s0 s0' b0 d1 d2 hb0 hc0 ih => intro heq; simp at heq
  exact key _ st st' hev rfl
```
:::
::::

::::quiz
Is the following proposition provable?

```
∀ (b : Bexp) (c : Com) (st : State),
  (¬ ∃ st', st =[ imp { while (~b) { ~c } } ]=> st') →
  ∀ st'', Bexp.eval st'' b = true
```

(A) Yes    (B) No    (C) Not sure

:::answer
This claim is *false*, so it cannot be proved -- the proof gets
stuck immediately:

```
theorem quiz5_answer (b : Bexp) (c : Com) (st : State)
    (H : ¬ ∃ st', st =[ imp { while (~b) { ~c } } ]=> st') :
    ∀ st'', Bexp.eval st'' b = true := by
  intro st''
  -- Can't make any progress -- the claim is false!
```
:::
::::

## Determinism of Evaluation

:::dev
LATER: Maybe this should go at the end of the file in a section marked
   optional? Not everybody will want to spend time on it.
:::

::::full
Changing from a computational to a relational definition of evaluation
is a good move because it frees us from the artificial requirement that
evaluation be a total function. But it raises a question: is the
relational definition really a partial _function_? Could the same
command, from the same state, evaluate to two different final states?
In fact this cannot happen: `ceval` _is_ a partial function.
::::

:::terse
Finally, we should pause to check that our evaluation relation really is a (partial) function...
:::

:::dev
LATER: Informal proof needed! (And one can surely be found in some past
   CIS500 exam solutions!)
:::

```lean
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
```

::::hide
```
/- Answer to the second quiz above (deferred because it depends on
   `ceval_deterministic`). -/
theorem quiz2_answer (c1 c2 : Com) (st st' : State)
    (h1 : st =[ .seq c1 c2 ]=> st') (h2 : st =[ c1 ]=> st) : st =[ c2 ]=> st' := by
  cases h1 with
  | E_Seq _ _ _ smid _ hc1 hc2 =>
      have hmid : smid = st := ceval_deterministic c1 st smid st hc1 h2
      subst hmid
      exact hc2
```
::::

:::::exercise (rating := 3) (name := "pup_to_n")
Write an Imp program that sums the numbers from `1` to `X` (inclusive)
in the variable `Y`.  Your program should update the state as shown in
`pup_to_2_ceval`, which you can reverse-engineer to discover the program
you should write.  The proof of that theorem will be somewhat lengthy.

```lean
def pup_to_n : Com := solution!(
  imp {
    Y := 0;
    while (1 <= X) {
      Y := Y + X;
      X := X - 1;
    }
  })
```

:::hide
   Result is the same as `(X →ₜ 0 ; Y →ₜ 3 ; ∅)` if one admits
   functional extensionality.
:::

```lean
theorem pup_to_2_ceval :
    (X →ₜ 2 ; ∅) =[ pup_to_n ]=>
      (X →ₜ 0 ; Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅) := by
  solution!
    unfold pup_to_n
    apply Ceval.E_Seq (st' := (Y →ₜ 0 ; X →ₜ 2 ; ∅))
    · apply Ceval.E_Asgn; rfl
    · apply Ceval.E_WhileTrue (st' := (X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅))
      · rfl
      · apply Ceval.E_Seq (st' := (Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅)) <;>
          (apply Ceval.E_Asgn; rfl)
      · apply Ceval.E_WhileTrue
          (st' := (X →ₜ 0 ; Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅))
        · rfl
        · apply Ceval.E_Seq (st' := (Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅)) <;>
            (apply Ceval.E_Asgn; rfl)
        · apply Ceval.E_WhileFalse; rfl
```
:::::

:::dev
LATER: Comment from reader: Another good place to mention lack of
   functional extensionality.  The 6 `→ₜ`/`t_update`s in the above theorem
   are not redundant, nor would `pup_to_2_ceval` be provable if the
   algorithm were defined differently (e.g., if it used `Z` as a "buffer"
   variable instead of decrementing `X`).
:::

# Reasoning About Imp Programs

:::dev
LATER: This section doesn't seem very useful -- to anybody! It takes too
   much time to go through it in class, and even for advanced students it's
   too low-level and grubby to be a very convincing motivation for what
   follows -- i.e., to feel motivated by its grubbiness, you have to
   understand it, but this takes more time than it's worth. Better to cut
   the whole rest of the file (except the further exercises at the very end),
   or at least make it optional.
   (BCP 10/18: However, this removes quite a few exercises. Is the homework
   assignment still meaty enough? I'm going to leave it as-is for now, but
   we should reconsider this later.)
:::

::::full
We'll get into more systematic and powerful techniques for reasoning
about Imp programs in the next chapter, but we can
already do a few things (albeit in a somewhat low-level way) just by
working with the bare definitions. This section explores some examples.
::::

```lean
theorem plus2_spec (st : State) (n : Nat) (st' : State)
    (hx : st[X] = n) (heval : st =[ plus2 ]=> st') :
    st'[X] = n + 2 := by
  -- Inverting `heval` forces one step of the `ceval` computation: since
  -- `plus2` is an assignment, `st'` must be `st` extended at `X`.
  unfold plus2 at heval
  cases heval with
  | E_Asgn _ _ m _ h =>
      simp only [Aexp.eval] at h
      rw [TotalMap.update_eq]
      lia
```

:::dev
LATER: This used to be recommended.  Should it be reinstated?
:::

:::::exercise (rating := 3) (name := "XtimesYinZ_spec")
State and prove a specification of `XtimesYinZ`.

```lean
-- SOLUTION
/- Here is a specification in the style of `plus2_spec`: -/
theorem XtimesYinZ_spec1 (st : State) (nx ny : Nat) (st' : State)
    (hx : st[X] = nx) (hy : st[Y] = ny) (heval : st =[ XtimesYinZ ]=> st') :
    st'[Z] = nx * ny := by
  unfold XtimesYinZ at heval
  cases heval with
  | E_Asgn _ _ n _ h =>
      simp only [Aexp.eval] at h
      subst hx hy
      rw [TotalMap.update_eq]
      exact h.symm

/- Though perhaps a cleaner specification would be: -/
theorem XtimesYinZ_spec (st : State) :
    st =[ XtimesYinZ ]=> (Z →ₜ st[X] * st[Y] ; st) := by
  unfold XtimesYinZ
  apply Ceval.E_Asgn
  rfl

/- A less informative specification would be ... -/
theorem XtimesYinZ_spec2 (st : State) : ∃ st', st =[ XtimesYinZ ]=> st' := by
  exact ⟨(Z →ₜ st[X] * st[Y] ; st), by unfold XtimesYinZ; apply Ceval.E_Asgn; rfl⟩
-- END SOLUTION
```

:::grade
```
GRADE_MANUAL 3: XtimesYinZ_spec
```
:::
:::::

:::::exercise (rating := 3) (name := "loop_never_stops")
Hint: proceed by induction on the assumed derivation showing that `loop`
terminates.  Most of the cases are immediately contradictory and so can be
solved in one step (by `simp`/`discriminate` on the impossible command
equation).

```lean
theorem loop_never_stops (st st' : State) : ¬ (st =[ loop ]=> st') := by
  solution!
    intro contra
    -- Generalize over the command so the induction remembers what `loop` is.
    have key : ∀ (c : Com) (s s' : State), (s =[ c ]=> s') → c = loop → False := by
      intro c s s' hce
      induction hce with
      | E_WhileFalse b s0 c0 hb =>
          intro heq; unfold loop at heq; injection heq with e1 _
          subst e1; simp [Bexp.eval] at hb
      | E_WhileTrue s0 s0' s0'' b c0 hb hc hloop ih1 ih2 =>
          intro heq; exact ih2 heq
      | E_Skip s0 => intro heq; simp [loop] at heq
      | E_Asgn s0 a n x h => intro heq; simp [loop] at heq
      | E_Seq c1 c2 s0 s0' s0'' h1 h2 ih1 ih2 => intro heq; simp [loop] at heq
      | E_IfTrue s0 s0' b c1 c2 hb hc ih => intro heq; simp [loop] at heq
      | E_IfFalse s0 s0' b c1 c2 hb hc ih => intro heq; simp [loop] at heq
    exact key loop st st' contra rfl
```
:::::

:::dev
LATER: Marc Bezem 2022:
   There are trade-offs between using tactics and additional lemmas. Here is
   a case where a lemma would make things clearer. For `loop_never_stops`,
   the surprise is that it is proved by induction, and the Rocq tactic
   `remember` is hard to understand. The following formulation explains the
   induction better:

```
     Theorem loop_never_stops' : forall st st' c,
       st =[ c ]=> st' -> c = loop -> False.
```

   The equivalence of the two formulations is an easy lemma.  (Note: the Lean
   proof above already takes exactly this generalized-`key` shape.)
   BCP 23: Not sure I see a big difference between the two presentations: both
   statements are negations, and the `remember` in the proof is avoided in
   the new one by introducing an equality in the theorem statement that IMO
   is not very pretty...
:::

:::::exercise (rating := 3) (name := "no_whiles_eqv")
The following function yields `true` just on programs with no while
loops. Using `inductive`, write a property `NoWhilesR` that holds
exactly when `c` is while-free, then prove it equivalent to `Com.no_whiles`.

```lean
def Com.no_whiles (c : Com) : Bool :=
  match c with
  | imp {skip;} => true
  | imp {_x := ~_a;} => true
  | imp {~c1 ~c2} => no_whiles c1 && no_whiles c2
  | imp {if (~_) {~ct} else {~cf}} => no_whiles ct && no_whiles cf
  | imp {while (~_) {~_}} => false

inductive NoWhilesR : Com → Prop where
  -- SOLUTION
  | nw_Skip : NoWhilesR (imp { skip; })
  | nw_Asgn (x : Ident) (a : Aexp) : NoWhilesR (imp { x := ~a; })
  | nw_Seq (c1 c2 : Com) (h1 : NoWhilesR c1) (h2 : NoWhilesR c2) :
      NoWhilesR (imp { ~c1 ~c2 })
  | nw_If (b : Bexp) (c1 c2 : Com) (h1 : NoWhilesR c1) (h2 : NoWhilesR c2) :
      NoWhilesR (imp { if (~b) { ~c1 } else { ~c2 } })
  -- END SOLUTION

theorem no_whiles_eqv (c : Com) : Com.no_whiles c = true ↔ NoWhilesR c := by
  solution!
    constructor
    · induction c with
      | skip => intro _; exact .nw_Skip
      | asgn x a => intro _; exact .nw_Asgn x a
      | seq c1 c2 ih1 ih2 =>
          intro h; simp only [Com.no_whiles, Bool.and_eq_true] at h
          exact .nw_Seq _ _ (ih1 h.1) (ih2 h.2)
      | cond b c1 c2 ih1 ih2 =>
          intro h; simp only [Com.no_whiles, Bool.and_eq_true] at h
          exact .nw_If _ _ _ (ih1 h.1) (ih2 h.2)
      | whileDo b c ih => intro h; simp [Com.no_whiles] at h
    · intro h
      induction h with
      | nw_Skip => rfl
      | nw_Asgn x a => rfl
      | nw_Seq c1 c2 h1 h2 ih1 ih2 => simp [Com.no_whiles, ih1, ih2]
      | nw_If b c1 c2 h1 h2 ih1 ih2 => simp [Com.no_whiles, ih1, ih2]
```
:::::

:::::exercise (rating := 4) (name := "no_whiles_terminating")
Imp programs that don't involve while loops always terminate.  State and
prove a theorem `no_whiles_terminating` that says this.  Use either
`Com.no_whiles` or `NoWhilesR`, as you prefer.

```lean
theorem no_whiles_terminating (c : Com) (st : State) (h : NoWhilesR c) :
    ∃ st', st =[ c ]=> st' := by
  solution!
    induction h generalizing st with
    | nw_Skip => exact ⟨st, .E_Skip st⟩
    | nw_Asgn x a => exact ⟨(x →ₜ Aexp.eval st a ; st), .E_Asgn st a (Aexp.eval st a) x rfl⟩
    | nw_Seq c1 c2 h1 h2 ih1 ih2 =>
        obtain ⟨st', hc1⟩ := ih1 st
        obtain ⟨st'', hc2⟩ := ih2 st'
        exact ⟨st'', .E_Seq c1 c2 st st' st'' hc1 hc2⟩
    | nw_If b c1 c2 h1 h2 ih1 ih2 =>
        cases hb : Bexp.eval st b with
        | true =>
            obtain ⟨st', hc1⟩ := ih1 st
            exact ⟨st', .E_IfTrue st st' b c1 c2 hb hc1⟩
        | false =>
            obtain ⟨st', hc2⟩ := ih2 st
            exact ⟨st', .E_IfFalse st st' b c1 c2 hb hc2⟩
```

And here is an alternative solution by induction on `c` (using
   `Com.no_whiles` instead of `NoWhilesR`):

```lean
-- SOLUTION
theorem no_whiles_terminating' (c : Com) (st1 : State)
    (hb : Com.no_whiles c = true) : ∃ st2, st1 =[ c ]=> st2 := by
  induction c generalizing st1 with
  | skip => exact ⟨st1, .E_Skip st1⟩
  | asgn x a => exact ⟨(x →ₜ Aexp.eval st1 a ; st1), .E_Asgn st1 a (Aexp.eval st1 a) x rfl⟩
  | seq c1 c2 ih1 ih2 =>
      simp only [Com.no_whiles, Bool.and_eq_true] at hb
      obtain ⟨st1', hc1⟩ := ih1 st1 hb.1
      obtain ⟨st1'', hc2⟩ := ih2 st1' hb.2
      exact ⟨st1'', .E_Seq c1 c2 st1 st1' st1'' hc1 hc2⟩
  | cond b ct cf ih1 ih2 =>
      simp only [Com.no_whiles, Bool.and_eq_true] at hb
      cases hbev : Bexp.eval st1 b with
      | true =>
          obtain ⟨st2, h⟩ := ih1 st1 hb.1
          exact ⟨st2, .E_IfTrue st1 st2 b ct cf hbev h⟩
      | false =>
          obtain ⟨st2, h⟩ := ih2 st1 hb.2
          exact ⟨st2, .E_IfFalse st1 st2 b ct cf hbev h⟩
  | whileDo b c ih => simp [Com.no_whiles] at hb
-- END SOLUTION
```
:::::

:::dev
```
mwhicks1: NOT PORTED YET — remaining sections of sfdev/lf/Imp.v to port:
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
      * short_circuit (EX3?, Imp.v:3184): short-circuiting `Bexp.eval`.
      * break_imp (EX4?, Imp.v:3227): extends Com with `CBreak`; new
        relational semantics `ceval` carrying a `result` (SContinue/SBreak).
        Large. See verso-book branch (lf/Imp.lean ~line 1141, CEvalBreak) for
        a prior take on the signal type.
      * while_break_true (EX3A?, Imp.v:3454)
      * ceval_deterministic for break (EX4A?, Imp.v:3477)
      * exn_imp (EX4A?, Imp.v:3524): exceptions variant. Large.
      * add_for_loop (EX4?, Imp.v:3728): add a C-style `for` loop to Com,
        its notation, and extend ceval.
```
:::
