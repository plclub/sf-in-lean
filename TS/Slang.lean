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
open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "Slang: Arithmetic and Boolean Expressions" =>
%%%
tag := "Slang"
htmlSplit := .never
file := some "Slang"
%%%

::::full
We begin our study of type systems for programming languages by looking at a language
we call *Slang* (_simple language_). Despite its simplicity, Slang
lets us introduce key concepts for specifying the _syntax_ and _semantics_ of
programming languages, and show how those concepts are realized in Lean.
::::

# Arithmetic and Boolean Expressions

:::instructors
At this point, I usually take some of the lecture time to
   give a high-level picture of the structure of an interpreter, the
   processes of lexing and parsing, the notion of ASTs, etc.  Might be
   nice to work some of those ideas into the notes. - BCP
:::

::::full
Slang is a simple core language of _arithmetic and boolean expressions_
sufficient to express simple computations and logical predicates.
::::

## Syntax

```lean
namespace Slang
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
  SOONER: mwhicks1: Will we develop `ImpParser`? Previously, the text
  below said "The optional chapter `ImpParser` develops a simple lexical analyzer and
  parser that can perform this translation.  You do not need to understand
  that chapter to understand this one, but if you haven't already taken a
  course where these techniques are covered (e.g., a course on compilers)
  you may want to skim it." I removed this because now this chapter is not
  about Imp but about a much simpler language, and also it lives in TS not HL.
:::

::::full
In this chapter, we'll mostly elide the translation from the concrete
syntax that a programmer would actually write to these abstract syntax
trees -- the process that, for example, would translate the string
`"1 + 2 * 3"` to the AST `.plus (.num 1) (.mult (.num 2) (.num 3))`.

For comparison, here's a conventional BNF (Backus-Naur Form) grammar
defining the same abstract syntax:

```
  a := nat
      | a + a
      | a − a
      | a × a

  b := bool
      | a = a
      | a ≠ a
      | a ≤ a
      | a > a
      | ¬ b
      | b ∧ b
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

```lean
def Aexp.eval (a : Aexp) : Nat :=
  match a with
  | num   n     =>  n
  | plus  a1 a2 =>  eval a1 + eval a2
  | minus a1 a2 =>  eval a1 - eval a2
  | mult  a1 a2 =>  eval a1 * eval a2
```

::::full
By convention, we pair the definition with one _simplification lemma_ which says
how `eval` behaves on each constructor. Proofs then rewrite by these lemmas rather
than peeking through the definition of `eval`.  We tag each lemma `@[simp]`, so `simp`
applies them automatically.
::::

```lean
@[simp] theorem Aexp.eval_num (n : Nat) : (num n).eval = n := rfl
@[simp] theorem Aexp.eval_plus (a1 a2 : Aexp) : (plus a1 a2).eval = a1.eval + a2.eval := rfl
@[simp] theorem Aexp.eval_minus (a1 a2 : Aexp) : (minus a1 a2).eval = a1.eval - a2.eval := rfl
@[simp] theorem Aexp.eval_mult (a1 a2 : Aexp) : (mult a1 a2).eval = a1.eval * a2.eval := rfl

example : Aexp.eval (.plus (.num 2) (.num 2)) = 4 := by simp
```

Similarly, evaluating a boolean expression yields a boolean, and we give it
the same treatment.

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

@[simp] theorem Bexp.eval_bool (b : Bool) : (bool b).eval = b := rfl
@[simp] theorem Bexp.eval_eq (a1 a2 : Aexp) : (eq a1 a2).eval = (a1.eval == a2.eval) := rfl
@[simp] theorem Bexp.eval_neq (a1 a2 : Aexp) : (neq a1 a2).eval = (a1.eval != a2.eval) := rfl
@[simp] theorem Bexp.eval_le (a1 a2 : Aexp) : (le a1 a2).eval = (a1.eval ≤ a2.eval : Bool) := rfl
@[simp] theorem Bexp.eval_gt (a1 a2 : Aexp) : (gt a1 a2).eval = (a1.eval > a2.eval : Bool) := rfl
@[simp] theorem Bexp.eval_not (b : Bexp) : (not b).eval = !b.eval := rfl
@[simp] theorem Bexp.eval_and (b1 b2 : Bexp) : (and b1 b2).eval = (b1.eval && b2.eval) := rfl
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
We can now get some mileage out of these definitions. Suppose we define a
function that takes an arithmetic expression and slightly simplifies it, changing
every occurrence of `0 + e` (i.e., `.plus (.num 0) e`) into just `e`.
::::

```lean
def Aexp.optimize0plus (a : Aexp) : Aexp :=
  match a with
  | num   n          => num n
  | plus  (num 0) e2 => optimize0plus e2
  | plus  e1      e2 => plus  (optimize0plus e1) (optimize0plus e2)
  | minus e1      e2 => minus (optimize0plus e1) (optimize0plus e2)
  | mult  e1      e2 => mult  (optimize0plus e1) (optimize0plus e2)
```

::::full
To gain confidence that our optimization is doing the right thing we
can test it on some examples and see if the output looks OK.
::::

```lean
example :
    Aexp.optimize0plus (.plus (.num 2)
                               (.plus (.num 0)
                                      (.plus (.num 0) (.num 1))))
      = .plus (.num 2) (.num 1) := by rfl
```

::::full
But if we want to be certain the optimization is correct -- that
evaluating an optimized expression _always_ gives the same result as
the original -- we should prove it!

Here is a first, deliberately explicit proof, by induction on `a`. The
interesting case is `plus`: because `optimize0plus` treats `plus (num 0) e`
specially, we case-split on the left operand `a1` -- and, when it is a numeral,
on whether that numeral is `0` -- to line the proof up with the function's own
branches. Once the constructors are exposed, each case is discharged by
essentially the same incantation: unfold `optimize0plus`, rewrite `eval` by its
characterizing lemmas, then finish with the induction hypotheses. Notice how
repetitive that makes the proof.
::::

```lean
theorem optimize0plus_sound (a : Aexp) :
    a.optimize0plus.eval = a.eval := by
  induction a with
  | num n => rfl
  | plus a1 a2 ih1 ih2 =>
    cases a1 with
    | num n =>
      cases n with
      | zero =>
        simp only [Aexp.optimize0plus, Aexp.eval_plus, Aexp.eval_num, Nat.zero_add]
        exact ih2
      | succ n =>
        simp only [Aexp.optimize0plus, Aexp.eval_plus, Aexp.eval_num]
        rw [ih2]
    | plus b1 b2 =>
      simp only [Aexp.optimize0plus, Aexp.eval_plus] at ih1 ⊢
      rw [ih1, ih2]
    | minus b1 b2 =>
      simp only [Aexp.optimize0plus, Aexp.eval_plus] at ih1 ⊢
      rw [ih1, ih2]
    | mult b1 b2 =>
      simp only [Aexp.optimize0plus, Aexp.eval_plus] at ih1 ⊢
      rw [ih1, ih2]
  | minus a1 a2 ih1 ih2 =>
    simp only [Aexp.optimize0plus, Aexp.eval_minus]
    rw [ih1, ih2]
  | mult a1 a2 ih1 ih2 =>
    simp only [Aexp.optimize0plus, Aexp.eval_mult]
    rw [ih1, ih2]
```

::::full
We can do much better. The case analysis we performed by hand -- peeling
`plus` apart to reach the `plus (num 0) e` branch -- is exactly the case
analysis that `optimize0plus` itself performs. For any function, Lean
generates a matching *induction principle*, here `Aexp.optimize0plus.induct`,
that follows the function's own recursion structure.  Inducting with it (via
`induction a using …`) hands us one goal per branch of `optimize0plus`, the
special `plus (num 0) e` branch included -- so the nested `cases` disappear.

Every remaining goal now has the same shape, so we can attack them uniformly
with the `<;>` combinator, which runs a single tactic on *all* the goals
produced by the `induction`.  That tactic is `simp_all [Aexp.optimize0plus]`:
it unfolds `optimize0plus`, rewrites `eval` by the `@[simp]` characterizing
lemmas, and uses the induction hypotheses -- which `simp_all` picks up from the
local context automatically -- to close each goal. The whole proof collapses to
two lines.
::::

```lean
theorem optimize0plus_sound' (a : Aexp) :
    a.optimize0plus.eval = a.eval := by
  induction a using Aexp.optimize0plus.induct <;>
    simp_all [Aexp.optimize0plus]
```

:::::exercise (rating := 3) (name := "optimize0plusB_sound")
Since the {name}`Aexp.optimize0plus` transformation doesn't change the value of an
`Aexp`, we should be able to apply it to all the `Aexp`s that appear in a
`Bexp` without changing the `Bexp`'s value.  Write a function that
performs this transformation on `Bexp`s and prove it sound. Use the
combinators we've just seen to make the proof as short and elegant as
possible.

```lean
def Bexp.optimize0plusB (b : Bexp) : Bexp := solution!(
  match b with
  | bool b    =>  bool b
  | eq a1 a2  =>  eq a1.optimize0plus a2.optimize0plus
  | neq a1 a2 =>  neq a1.optimize0plus a2.optimize0plus
  | le a1 a2  =>  le a1.optimize0plus a2.optimize0plus
  | gt a1 a2  =>  gt a1.optimize0plus a2.optimize0plus
  | not b1    =>  not (optimize0plusB b1)
  | and b1 b2 =>  and (optimize0plusB b1) (optimize0plusB b2))

example :
    Bexp.optimize0plusB
        (.not (.gt (.plus (.num 0) (.num 4)) (.num 8)))
      = (.not (.gt (.num 4) (.num 8))) := solution!(by rfl)
```

:::grade
```
GRADE_THEOREM 0.5: optimize0plusB_test1
```
:::

```lean
example :
    Bexp.optimize0plusB
        (.and (.le (.plus (.num 0) (.num 4)) (.num 5)) (.bool true))
      = (.and (.le (.num 4) (.num 5)) (.bool true)) := solution!(by rfl)
```

:::grade
```
GRADE_THEOREM 0.5: optimize0plusB_test2
```
:::

```lean
theorem optimize0plusB_sound (b : Bexp) :
    b.optimize0plusB.eval = b.eval := by
  solution!
    induction b <;>
      simp_all [Bexp.optimize0plusB, optimize0plus_sound]
```

:::grade
```
GRADE_THEOREM 2: optimize0plusB_sound
```
:::
:::::

:::::exercise (rating := 4) (name := "optimize")
The optimization implemented by our {name}`Aexp.optimize0plus` is only one of
many possible optimizations on arithmetic and boolean expressions. Write a more
sophisticated optimizer and prove it correct. (You will probably find it easiest
to start small -- add just a single, simple optimization and its correctness proof
and build up incrementally to something more interesting.)
:::::

# Evaluation as a Relation

::::full
We have presented {name}`Aexp.eval` and {name}`Bexp.eval` as functions defined by
recursion. Another way to think about evaluation -- one that is often
more flexible -- is as a _relation_ between expressions and their
values. This perspective leads to inductive definitions like the
following.
::::

```lean
inductive Aexp.EvalR : Aexp → Nat → Prop where
  | num (n : Nat) : EvalR (.num n) n
  | plus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.plus a1 a2) (n1 + n2)
  | minus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.minus a1 a2) (n1 - n2)
  | mult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.mult a1 a2) (n1 * n2)
```

We could instead have presented this relation with *positional* hypotheses --
no names for the premises.

```lean
namespace ArithUnnamed

inductive Aexp.EvalR : Aexp → Nat → Prop where
  | num (n : Nat) : EvalR (.num n) n
  | plus (e1 e2 : Aexp) (n1 n2 : Nat) : EvalR e1 n1 → EvalR e2 n2 → EvalR (.plus e1 e2) (n1 + n2)
  | minus (e1 e2 : Aexp) (n1 n2 : Nat) : EvalR e1 n1 → EvalR e2 n2 → EvalR (.minus e1 e2) (n1 - n2)
  | mult (e1 e2 : Aexp) (n1 n2 : Nat) : EvalR e1 n1 → EvalR e2 n2 → EvalR (.mult e1 e2) (n1 * n2)

end ArithUnnamed
```

::::full
The version above makes the rules somewhat easier to read, but gives less control over naming
the hypotheses during proofs involving the relation. For this reason we adopt the named style.
::::

It will be convenient to have an infix notation for {name}`Aexp.EvalR`. We'll
write `e ⇓ n` to mean that arithmetic expression `e` evaluates to
value `n`.

```lean
scoped notation:55 e:56 " ⇓ " n:56 => Aexp.EvalR e n
```

::::full
In Lean the `notation` is declared right after the inductive.
The `scoped` keyword allows us to scope the notation to the present namespace so it doesn't
collide with other evaluation relations later.
::::

:::dev
SOONER: mwhicks1: The Rocq version here says "As we saw in our case study of regular expressions
in chapter IndProp, Rocq provides a way to use this notation in the definition of aevalR itself."
It then re-shows the definition with Downarrow. We need to resolve how we want to do this.
:::

## Inference Rule Notation

::::full
In informal discussions, it is convenient to write the rules for
{name}`Aexp.EvalR` and similar relations in the more readable graphical form of
_inference rules_, where the premises above the line justify the
conclusion below the line. For example, the constructor `plus`
can be written like this as an inference rule:

```
                         e1 ⇓ n1
                         e2 ⇓ n2
                    ------------------          (plus)
                    plus e1 e2 ⇓ n1+n2
```

Notice the structural correspondence between this rule and our version of the inductive
type with unnamed hypotheses:

```
    | plus (a1 a2 : Aexp) (n1 n2 : Nat) :
        EvalR a1 n1 →
        EvalR a2 n2 →
        EvalR (.plus a1 a2) (n1 + n2)
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
indicated by saying something like "Let `Aexp.EvalR` be the smallest relation
closed under the following rules...".

To summarize: a group of inference rules corresponds to a single inductive
definition; each rule's name corresponds to a constructor name; above the
line are the premises, below the line the conclusion; and metavariables
like `e1` and `n1` are implicitly universally quantified. The whole
collection of rules defines `⇓` as the smallest relation closed under
them:

```
                        ---------                (num)
                        num n ⇓ n

                         e1 ⇓ n1
                         e2 ⇓ n2
                    ------------------           (plus)
                    plus e1 e2 ⇓ n1+n2

                         e1 ⇓ n1
                         e2 ⇓ n2
                   -------------------           (minus)
                   minus e1 e2 ⇓ n1-n2

                         e1 ⇓ n1
                         e2 ⇓ n2
                    ------------------           (mult)
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

::::quiz
Which rules are needed to prove the following?

```
.mult (.plus (.num 3) (.num 1)) (.num 0) ⇓ 0
```

(A) `num` and `plus`
(B) `num` only
(C) `num` and `mult`
(D) `mult` and `plus`
(E) `num`, `mult`, and `plus`
::::

::::hide
-- QUIZ
/-
  Which rules are needed to prove the following?

  ```
  .minus (.num 3) (.minus (.num 2) (.num 1)) ⇓ 2
  ```

  (A) `num` and `plus`
  (B) `num` only
  (C) `num` and `minus`
  (D) `minus` and `plus`
  (E) `num`, `minus`, and `plus`
-/
-- /QUIZ
::::

:::dev
SOONER: mwhicks1: Not sure if we need ⇓b, or whether we can define
⇓ overloaded. Don't understand Lean notation yet!
:::

:::dev
SOONER: chenson2018: About `Bexp.eval` below: We should discuss a way to recall definitions without
having to write them out manually like this. I think a simple `#print` may work as an
alternative, assuming there are no namespace issues..
:::

:::::exercise (rating := 1) (name := "beval_rules")
Here, again, is the definition of the {name}`Bexp.eval` function:

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
                        -----------              (bool)
                        bool b ⇓b b

                        e1 ⇓ n1
                        e2 ⇓ n2
                   ----------------------        (eq)
                   eq e1 e2 ⇓b (n1 =? n2)

                        e1 ⇓ n1
                        e2 ⇓ n2
                 ----------------------------    (neq)
                 neq e1 e2 ⇓b negb (n1 =? n2)

                        e1 ⇓ n1
                        e2 ⇓ n2
                   -----------------------       (le)
                   le e1 e2 ⇓b (n1 <=? n2)

                        e1 ⇓ n1
                        e2 ⇓ n2
                ----------------------------     (gt)
                gt e1 e2 ⇓b negb (n1 <=? n2)

                          e ⇓b b
                      ---------------            (not)
                      not e ⇓b negb b

                        e1 ⇓b b1
                        e2 ⇓b b2
                  -----------------------        (and)
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

```lean
theorem Aexp.evalR_iff_eval (a : Aexp) (n : Nat) :
    a ⇓ n ↔ a.eval = n := by
  constructor
  · intro h
    induction h with
    | num n => rfl
    | plus a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [Aexp.eval_plus]; rw [ih1, ih2]
    | minus a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [Aexp.eval_minus]; rw [ih1, ih2]
    | mult a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [Aexp.eval_mult]; rw [ih1, ih2]
  · intro h
    subst h
    induction a with
    | num n => exact .num n
    | plus a1 a2 ih1 ih2 => exact .plus a1 a2 _ _ ih1 ih2
    | minus a1 a2 ih1 ih2 => exact .minus a1 a2 _ _ ih1 ih2
    | mult a1 a2 ih1 ih2 => exact .mult a1 a2 _ _ ih1 ih2
```

We can make the proof quite a bit shorter using more automation like we did in
the previous section.

:::dev
SOONER: mwhicks1: the `workinclass!` marker should signal this live in-class exercise.
But it is not rendering properly on the HTML. In fact it replaces `workinclass!` with
the `all_goals` tactic, which we don't need.
:::

```lean
theorem Aexp.evalR_iff_eval' (a : Aexp) (n : Nat) :
    a ⇓ n ↔ a.eval = n := by
  workinclass!
    constructor
    · intro h; induction h <;> simp_all
    · intro h; subst h; induction a <;> constructor <;> assumption
```

:::::exercise (rating := 3) (name := "bevalR")
Write a relation `Bexp.EvalR` in the same style as {name}`Aexp.EvalR`, and prove that
it is equivalent to {name}`Bexp.eval`.

```lean
inductive Bexp.EvalR : Bexp → Bool → Prop where
  -- SOLUTION
  | bool (b : Bool) : EvalR (.bool b) b
  | eq (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ⇓ n1) (h2 : a2 ⇓ n2) : EvalR (.eq a1 a2) (n1 == n2)
  | neq (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ⇓ n1) (h2 : a2 ⇓ n2) : EvalR (.neq a1 a2) (n1 != n2)
  | le (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ⇓ n1) (h2 : a2 ⇓ n2) : EvalR (.le a1 a2) (n1 ≤ n2)
  | gt (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ⇓ n1) (h2 : a2 ⇓ n2) : EvalR (.gt a1 a2) (n1 > n2)
  | not (b : Bexp) (bv : Bool) (h : EvalR b bv) : EvalR (.not b) (!bv)
  | and (b1 b2 : Bexp) (tv1 tv2 : Bool) (h1 : EvalR b1 tv1) (h2 : EvalR b2 tv2) :
      EvalR (.and b1 b2) (tv1 && tv2)
  -- END SOLUTION

scoped notation:55 e:56 " ⇓b " b:56 => Bexp.EvalR e b
```

:::dev
mwhicks1: There is no keyboard shortcut for a subscript b, nor is there one for c
(to use used with cevalR below). There are numbers, x, y, z, l, m, n, etc.
:::

```lean
theorem Bexp.evalR_iff_eval (b : Bexp) (bv : Bool) :
    b ⇓b bv ↔ b.eval = bv := by
  solution!
    constructor
    · intro h
      induction h <;> simp_all [Aexp.evalR_iff_eval]
    · intro h
      subst h
      induction b <;> constructor <;> simp_all [Aexp.evalR_iff_eval]
```

:::grade
```
GRADE_THEOREM 3: Bexp.evalR_iff_eval
```
:::
:::::

```lean
end Slang
```

## Computational vs. Relational Definitions

::::full
For the definitions of evaluation for arithmetic and boolean
expressions, the choice of whether to use functional or relational
definitions is mainly a matter of taste. However, there are
situations where relational definitions work much better than
functional ones.
::::

:::terse
Sometimes relational definitions are the only reasonable option...
:::

```lean
namespace Slang.AevalRDivision
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
not be straightforward due to division being a _partial_ operation; i.e.,
what should we return as the result of `.div (.num 5) (.num 0)`?
Partiality is no problem for the relational definition.

:::terse
What should `Aexp.eval` return for `.div (.num 1) (.num 0)`??
:::

```lean
inductive Aexp.EvalR : Aexp → Nat → Prop where
  | num (n : Nat) : EvalR (.num n) n
  | plus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.plus a1 a2) (n1 + n2)
  | minus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.minus a1 a2) (n1 - n2)
  | mult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.mult a1 a2) (n1 * n2)
  | div (a1 a2 : Aexp) (n1 n2 n3 : Nat)             -- NEW
      (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) (hpos : n2 > 0) (hdiv : n2 * n3 = n1) :
      EvalR (.div a1 a2) n3
```

Notice that there are some inputs (those with a divisor of 0) for which this relation
does not specify an output.

```lean
end Slang.AevalRDivision

namespace Slang.AevalRExtended
```

:::terse
Another example: a _nondeterministic_ number generator:
:::

As another example, suppose that we want to extend the arithmetic operations by a
nondeterministic number generator `any` that, when evaluated, may
yield any number. (This is not the same as making a _probabilistic_
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
inductive Aexp.EvalR : Aexp → Nat → Prop where
  | any (n : Nat) : EvalR .any n                   -- NEW
  | num (n : Nat) : EvalR (.num n) n
  | plus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.plus a1 a2) (n1 + n2)
  | minus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.minus a1 a2) (n1 - n2)
  | mult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : EvalR a1 n1) (h2 : EvalR a2 n2) :
      EvalR (.mult a1 a2) (n1 * n2)

end Slang.AevalRExtended
```

:::dev
SOONER: mwhicks1: The following text seems not quite right to me. First, you can
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
