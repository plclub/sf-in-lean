import SFLMeta

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Slang: Arithmetic and Boolean Expressions" =>
%%%
tag := "Slang"
htmlSplit := .never
file := some "Slang"
%%%

:::dev "Benjamin Pierce (bcpierce00)"
We need to figure out our approach to text width, especially
for proofs.  Quite a few proofs here don't render into the
chosen page width, and for terse mode it will be worse.
:::

::::full
In *Logical Foundations* (LF) we went through the basics of how to use Lean to
prove theorems and write functional programs. Now, we begin to shift gears
to using it to reason about properties of programs and programming languages.
We begin by looking at a language we call *Slang* (for _simple
language_). Despite its simplicity, Slang lets us introduce key concepts for
specifying the _syntax_ and _semantics_ of programming languages and show how
those concepts are realized in Lean.

(This chapter is shared, word for word, between two volumes: *Type Systems* (TS) and
*Hoare Logic* (HL). If you have already worked through it in the other volume, you can
safely skip ahead to the next chapter of this one.)
::::

# Arithmetic and Boolean Expressions

:::instructors
At this point, I usually take some of the lecture time to
give a high-level picture of the structure of an interpreter, the
processes of lexing and parsing, the notion of ASTs, etc.  Might be
nice to work some of those ideas into the notes. - BCP
:::
:::dev "Michael Hicks (mwhicks1)" PotentialImprovement
  Will we develop `ImpParser`? Previously, the text
  below said "The optional chapter `ImpParser` develops a simple lexical analyzer and
  parser that can perform this translation.  You do not need to understand
  that chapter to understand this one, but if you haven't already taken a
  course where these techniques are covered (e.g., a course on compilers)
  you may want to skim it." I removed this because now this chapter is not
  about Imp but about a much simpler language, and also it lives in TS not HL.
  BCP: We don't need to take this digression for now.  Later, we could consider
  making a real chapter about lexing and parsing, maybe even with some proofs.
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
  | plus (a₁ a₂ : Aexp)
  | minus (a₁ a₂ : Aexp)
  | mult (a₁ a₂ : Aexp)

inductive Bexp where
  | bool (b : Bool)
  | eq (a₁ a₂ : Aexp)
  | neq (a₁ a₂ : Aexp)
  | le (a₁ a₂ : Aexp)
  | gt (a₁ a₂ : Aexp)
  | not (b : Bexp)
  | and (b₁ b₂ : Bexp)
```

::::full
In this chapter, we'll ignore the translation from the _concrete
syntax_ that a programmer would actually write to these abstract syntax
trees -- the process that, for example, would translate the string
{lean}`"1 + 2 * 3"` to the AST `.plus (.num 1) (.mult (.num 2) (.num 3))`.

For comparison, here's a conventional BNF (Backus-Naur Form) grammar
defining the same abstract syntax:

```bnf
a ::= nat
    | a "+" a
    | a "−" a
    | a "*" a ;
b ::= bool
    | a "=" a
    | a "≠" a
    | a "≤" a
    | a ">" a
    | "¬" b
    | b "∧" b ;
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
namespace Aexp
def eval (a : Aexp) : Nat :=
  match a with
  | num   n     =>  n
  | plus  a₁ a₂ =>  a₁.eval + a₂.eval
  | minus a₁ a₂ =>  a₁.eval - a₂.eval
  | mult  a₁ a₂ =>  a₁.eval * a₂.eval

@[simp] theorem eval_num (n : Nat) : (num n).eval = n := rfl
@[simp] theorem eval_plus (a₁ a₂ : Aexp) : (plus a₁ a₂).eval = a₁.eval + a₂.eval := rfl
@[simp] theorem eval_minus (a₁ a₂ : Aexp) : (minus a₁ a₂).eval = a₁.eval - a₂.eval := rfl
@[simp] theorem eval_mult (a₁ a₂ : Aexp) : (mult a₁ a₂).eval = a₁.eval * a₂.eval := rfl

example : eval (.plus (.num 2) (.num 2)) = 4 := by simp
end Aexp
```

Similarly, evaluating a boolean expression yields a boolean.

```lean
namespace Bexp
def eval (b : Bexp) : Bool :=
  match b with
  | bool b     =>  b
  | eq   a₁ a₂ =>  a₁.eval == a₂.eval
  | neq  a₁ a₂ =>  a₁.eval != a₂.eval
  | le   a₁ a₂ =>  a₁.eval ≤ a₂.eval
  | gt   a₁ a₂ =>  a₁.eval > a₂.eval
  | not  b₁    =>  !eval b₁
  | and  b₁ b₂ =>  eval b₁ && eval b₂

@[simp] theorem eval_bool (b : Bool) : (bool b).eval = b := rfl
@[simp] theorem eval_eq (a₁ a₂ : Aexp) : (eq a₁ a₂).eval = (a₁.eval == a₂.eval) := rfl
@[simp] theorem eval_neq (a₁ a₂ : Aexp) : (neq a₁ a₂).eval = (a₁.eval != a₂.eval) := rfl
@[simp] theorem eval_le (a₁ a₂ : Aexp) : (le a₁ a₂).eval = (a₁.eval ≤ a₂.eval : Bool) := rfl
@[simp] theorem eval_gt (a₁ a₂ : Aexp) : (gt a₁ a₂).eval = (a₁.eval > a₂.eval : Bool) := rfl
@[simp] theorem eval_not (b : Bexp) : (not b).eval = !b.eval := rfl
@[simp] theorem eval_and (b₁ b₂ : Bexp) : (and b₁ b₂).eval = (b₁.eval && b₂.eval) := rfl
end Bexp
```

It's worth noting that `≤` and `>` are {lean}`Prop`-valued, i.e. `a₁.eval st ≤ a₂.eval st` is a proposition,
but {name}`Bexp.eval` returns a {name}`Bool`, so Lean implicitly inserts a {name}`decide` coercion.
You can observe the call to {name}`decide` by hovering over {name}`Bexp.eval_le` and {name}`Bexp.eval_gt`.

::::quiz
What does the following expression evaluate to?

```
Aexp.eval (.plus (.num 3) (.minus (.num 4) (.num 1)))
```

(A) true    (B) false    (C) 0    (D) 3    (E) 6
::::

:::quizSolution
(E) 6
:::

## Optimization

::::full
We can now start to get some mileage out of these definitions. Suppose we define a
function that takes an arithmetic expression and slightly simplifies it, changing
every occurrence of `0 + e` (i.e., `.plus (.num 0) e`) into just `e`.
::::

```lean
def Aexp.optimize0plus (a : Aexp) : Aexp :=
  match a with
  | num   n          => num n
  | plus  (num 0) e₂ => optimize0plus e₂
  | plus  e₁      e₂ => plus  (optimize0plus e₁) (optimize0plus e₂)
  | minus e₁      e₂ => minus (optimize0plus e₁) (optimize0plus e₂)
  | mult  e₁      e₂ => mult  (optimize0plus e₁) (optimize0plus e₂)
```

::::full
To gain confidence that our optimization is doing the right thing, we
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

Here is a first, deliberately explicit, proof, by induction on `a`. The
interesting case is {name}`Aexp.plus`: because {name}`Aexp.optimize0plus` treats `plus (num 0) e`
specially, we case-split on the left operand `a₁` -- and, when it is a numeral,
on whether that numeral is `0` -- to line the proof up with the function's own
branches. Once the constructors are exposed, each case is discharged by
essentially the same incantation: unfold {name}`Aexp.optimize0plus`, rewrite {name}`Aexp.eval` by its
characterizing lemmas, then finish with the induction hypotheses. Notice how
repetitive that makes the proof.
::::

```lean
theorem optimize0plus_sound (a : Aexp) :
    a.optimize0plus.eval = a.eval := by
  induction a with
  | num n => rfl
  | plus a₁ a₂ ih₁ ih₂ =>
    cases a₁ with
    | num n =>
      cases n with
      | zero =>
        simp only [Aexp.optimize0plus, Aexp.eval_plus, Aexp.eval_num, Nat.zero_add]
        exact ih₂
      | succ n =>
        simp only [Aexp.optimize0plus, Aexp.eval_plus, Aexp.eval_num]
        rw [ih₂]
    | plus b₁ b₂ =>
      simp only [Aexp.optimize0plus, Aexp.eval_plus] at ih₁ ⊢
      rw [ih₁, ih₂]
    | minus b₁ b₂ =>
      simp only [Aexp.optimize0plus, Aexp.eval_plus] at ih₁ ⊢
      rw [ih₁, ih₂]
    | mult b₁ b₂ =>
      simp only [Aexp.optimize0plus, Aexp.eval_plus] at ih₁ ⊢
      rw [ih₁, ih₂]
  | minus a₁ a₂ ih₁ ih₂ =>
    simp only [Aexp.optimize0plus, Aexp.eval_minus]
    rw [ih₁, ih₂]
  | mult a₁ a₂ ih₁ ih₂ =>
    simp only [Aexp.optimize0plus, Aexp.eval_mult]
    rw [ih₁, ih₂]
```

::::full
We can do much better. The case analysis we performed by hand -- peeling
`plus` apart to reach the `plus (num 0) e` branch -- is exactly the case
analysis that {name}`Aexp.optimize0plus` itself performs.

The {tactic}`fun_induction` tactic
inducts along a function's *own* recursion structure: `fun_induction
Aexp.optimize0plus a` hands us one goal per branch of `optimize0plus` -- the
special `plus (num 0) e` branch included -- so the nested {tactic}`cases` disappear.

Before applying `fun_induction` to a function as complex as {name}`Aexp.optimize0plus`,
let's see how it works on somthing simpler. Recall the definition of `Nat.even` and `Nat.odd`:

```lean
def Nat.even (n : Nat) :=
  match n with
  | 0 => true
  | 1 => false
  | n' + 2 => even n'

def Nat.odd (n : Nat) := Nat.even (n + 1)
```

Normally, if we perform induction on `n`, we get two cases - `0` and `n' + 1` -
one for each of the cases in the inductive definition of natural numbers.
Functional induction on {name}`Nat.even`, however, gives us three cases - `0`, `1`, and `n' + 2` -
corresponding to each of the cases of its definition.

```lean
example (n : Nat) (h : Nat.even n = true) : Nat.odd n = false := by
  fun_induction Nat.even n
  . rfl
  . contradiction
  . simp [Nat.odd, Nat.even] at *
    lia
```

Now let's try using {tactic}`fun_induction` on {name}`Aexp.optimize0plus`. When we do this,
every goal has the same shape, so we can attack them uniformly
with the {tactic}`<;>` combinator and a single tactic, {tactic}`simp_all`, which rewrites
{name}`Aexp.eval` by the `@[simp]` characterizing lemmas and uses the induction hypotheses
-- which it picks up from the local context automatically -- to close
each goal. The whole proof collapses to two lines.
::::

::::terse
We can use {tactic}`fun_induction` to achieve a much shorter proof.
::::

```lean
theorem optimize0plus_sound' (a : Aexp) :
    a.optimize0plus.eval = a.eval := by
  fun_induction Aexp.optimize0plus a <;> simp_all
```

:::::exercise (rating := 3) (name := "optimize0plusB_sound")
Since the {name}`Aexp.optimize0plus` transformation doesn't change the value of an
{name}`Aexp`, we should be able to apply it to all the {name}`Aexp`s that appear in a
{name}`Bexp` without changing the {name}`Bexp`'s value.  Write a function that
performs this transformation on {name}`Bexp`s and prove it sound. Use the
combinators we've just seen to make the proof as short and elegant as
possible.

```lean
def Bexp.optimize0plusB (b : Bexp) : Bexp := solution!(
  match b with
  | bool b    =>  bool b
  | eq a₁ a₂  =>  eq a₁.optimize0plus a₂.optimize0plus
  | neq a₁ a₂ =>  neq a₁.optimize0plus a₂.optimize0plus
  | le a₁ a₂  =>  le a₁.optimize0plus a₂.optimize0plus
  | gt a₁ a₂  =>  gt a₁.optimize0plus a₂.optimize0plus
  | not b₁    =>  not (optimize0plusB b₁)
  | and b₁ b₂ =>  and (optimize0plusB b₁) (optimize0plusB b₂))

theorem optimize0plusB_test1 :
    Bexp.optimize0plusB
        (.not (.gt (.plus (.num 0) (.num 4)) (.num 8)))
      = (.not (.gt (.num 4) (.num 8))) := solution!(by rfl)
```

:::gradeTheorem "0.5" optimize0plusB_test1
:::

```lean
theorem optimize0plusB_test2 :
    Bexp.optimize0plusB
        (.and (.le (.plus (.num 0) (.num 4)) (.num 5)) (.bool true))
      = (.and (.le (.num 4) (.num 5)) (.bool true)) := solution!(by rfl)
```

:::gradeTheorem "0.5" optimize0plusB_test2
:::

```lean
theorem optimize0plusB_sound (b : Bexp) :
    b.optimize0plusB.eval = b.eval := by
  solution!
    induction b <;>
      simp_all [Bexp.optimize0plusB, optimize0plus_sound]
```

:::gradeTheorem 2 optimize0plusB_sound
:::
:::::

:::::exercise (rating := 4) (name := "optimize") (optional := Yes)
The optimization implemented by our {name}`Aexp.optimize0plus` is only one of
many possible optimizations on arithmetic and boolean expressions. Write a more
sophisticated optimizer and prove it correct. (You will probably find it easiest
to start small -- add just a single, simple optimization and its correctness proof --
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
  | plus {a₁ a₂ : Aexp} {n₁ n₂ : Nat} (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.plus a₁ a₂) (n₁ + n₂)
  | minus {a₁ a₂ : Aexp} {n₁ n₂ : Nat} (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.minus a₁ a₂) (n₁ - n₂)
  | mult {a₁ a₂ : Aexp} {n₁ n₂ : Nat} (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.mult a₁ a₂) (n₁ * n₂)
```

One comment on the style of this definition.
We could instead have presented this relation with *positional* hypotheses --
no names for the premises.

```lean
namespace ArithUnnamed

inductive Aexp.EvalR : Aexp → Nat → Prop where
  | num (n : Nat) : EvalR (.num n) n
  | plus {a₁ a₂ : Aexp} {n₁ n₂ : Nat} : EvalR a₁ n₁ → EvalR a₂ n₂ → EvalR (.plus a₁ a₂) (n₁ + n₂)
  | minus {a₁ a₂ : Aexp} {n₁ n₂ : Nat} : EvalR a₁ n₁ → EvalR a₂ n₂ → EvalR (.minus a₁ a₂) (n₁ - n₂)
  | mult {a₁ a₂ : Aexp} {n₁ n₂ : Nat} : EvalR a₁ n₁ → EvalR a₂ n₂ → EvalR (.mult a₁ a₂) (n₁ * n₂)

end ArithUnnamed
```

::::full
The version above makes the rules somewhat easier to read, but gives less control over naming
the hypotheses during proofs involving the relation. For this reason we adopt the named style.
::::

It will be convenient to have an infix notation for {name}`Aexp.EvalR`. We'll
write `e ⇓ n` to mean that arithmetic expression `e` evaluates to
value `n`. The `⇓` symbol is typed `\Downarrow`.

```lean
scoped notation:55 e:56 " ⇓ " n:56 => Aexp.EvalR e n
```

::::full
The `notation` is declared right after the inductive.
The `scoped` keyword allows us to scope the notation to the present namespace so it doesn't
collide with other evaluation relations later.
::::

## Inference Rule Notation

::::full
In informal discussions, it is convenient to write the rules for
{name}`Aexp.EvalR` and similar relations in the more readable graphical form of
_inference rules_, where the premises above the line justify the
conclusion below the line. For example, the constructor `plus`
can be written like this as an inference rule:

```
                         a₁ ⇓ n₁
                         a₂ ⇓ n₂
                    ------------------          (plus)
                    plus a₁ a₂ ⇓ n₁ + n₂
```

Notice the structural correspondence between this rule and our version of the inductive
type with unnamed hypotheses:

```
    | plus (a₁ a₂ : Aexp) (n₁ n₂ : Nat) :
        EvalR a₁ n₁ →
        EvalR a₂ n₂ →
        EvalR (.plus a₁ a₂) (n₁ + n₂)
```

Formally, there is nothing deep about inference rules: they are just
an informal notation for implications.
You can read the rule name on the right as the name of the
constructor and read each of the linebreaks between the premises above the
line (as well as the line itself) as `→`.  All the variables mentioned in
the rule (`a₁`, `n₁`, etc.) are implicitly bound by universal quantifiers
at the beginning. (Such variables are often called _metavariables_ to
distinguish them from the variables of whatever language we are defining. At
the moment, our arithmetic expressions don't include variables, but we'll
soon be adding them.) The whole collection of rules is understood as being
wrapped, implicitly, in an inductive declaration.
In informal prose, this is sometimes
indicated by saying something like "Let {name}`Aexp.EvalR` be the smallest relation
closed under the following rules...".

To summarize: a group of inference rules corresponds to a single inductive
definition; each rule's name corresponds to a constructor name; above the
line are the premises, below the line the conclusion; metavariables
like `a₁` and `n₁` are implicitly universally quantified. The whole
collection of rules defines `⇓` as the smallest relation closed under
them:

```
                        ---------                (num)
                        num n ⇓ n

                         a₁ ⇓ n₁
                         a₂ ⇓ n₂
                    ------------------           (plus)
                    plus a₁ a₂ ⇓ n₁ + n₂

                         a₁ ⇓ n₁
                         a₂ ⇓ n₂
                   -------------------           (minus)
                   minus a₁ a₂ ⇓ n₁ - n₂

                         a₁ ⇓ n₁
                         a₂ ⇓ n₂
                    ------------------           (mult)
                    mult a₁ a₂ ⇓ n₁*n₂
```
::::

:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement
The first two quizzes here seem kind of boring.
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

:::quizSolution
(E) `num`, `mult`, and `plus`
:::

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

:::dev "Michael Hicks (mwhicks1)" BeforeNextRelease
Not sure if we need ⇓b, or whether we can define
⇓ overloaded. Don't understand Lean notation yet!
:::
:::dev "Chris Henson (chenson₂018)" BeforeNextRelease
About `Bexp.eval` below: We should discuss a way to recall definitions without
having to write them out manually like this. I think a simple `#print` may work as an
alternative, assuming there are no namespace issues..
:::

:::::exercise (rating := 1) (name := "beval_rules") (optional := Yes)
Here, again, is the definition of the {name}`Bexp.eval` function:

```display
def Bexp.eval (b : Bexp) : Bool :=
  match b with
  | bool b     => b
  | eq   a₁ a₂ => a₁.eval == a₂.eval
  | neq  a₁ a₂ => a₁.eval != a₂.eval
  | le   a₁ a₂ => a₁.eval ≤ a₂.eval
  | gt   a₁ a₂ => a₁.eval > a₂.eval
  | not  b₁    => !eval b₁
  | and  b₁ b₂ => eval b₁ && eval b₂
```

Write out a corresponding definition of boolean evaluation as a relation
in inference rule notation.

::::solution

```
Answer (`⇓` is defined below):

                  -------------                (bool)
                   bool bv ⇓ bv

                        a₁ ⇓ n₁
                        a₂ ⇓ n₂
                  ---------------------        (eq)
                  eq a₁ a₂ ⇓ (n₁ == n₂)

                        a₁ ⇓ n₁
                        a₂ ⇓ n₂
                ---------------------          (neq)
                 neq a₁ a₂ ⇓ n₁ != n₂

                        a₁ ⇓ n₁
                        a₂ ⇓ n₂
                  --------------------------   (le)
                  le a₁ a₂ ⇓ (Nat.ble n₁ n₂)

                        a₁ ⇓ n₁
                        a₂ ⇓ n₂
                  ---------------------------  (gt)
                  gt a₁ a₂ ⇓ !(Nat.ble n₁ n₂)

                         b ⇓ bv
                     -----------               (not)
                     not b ⇓ !bv

                        b₁ ⇓ bv₁
                        b₂ ⇓ bv₂
                 ----------------------        (and)
                 and b₁ b₂ ⇓ bv₁ && bv₂
```
::::

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
    | plus h₁ h₂ ih₁ ih₂ => simp only [Aexp.eval_plus]; rw [ih₁, ih₂]
    | minus h₁ h₂ ih₁ ih₂ => simp only [Aexp.eval_minus]; rw [ih₁, ih₂]
    | mult h₁ h₂ ih₁ ih₂ => simp only [Aexp.eval_mult]; rw [ih₁, ih₂]
  · intro h
    subst h
    induction a with
    | num n => exact .num n
    | plus a₁ a₂ ih₁ ih₂ => exact .plus ih₁ ih₂
    | minus a₁ a₂ ih₁ ih₂ => exact .minus ih₁ ih₂
    | mult a₁ a₂ ih₁ ih₂ => exact .mult ih₁ ih₂
```

We can make the proof quite a bit shorter using more automation like we did in
the previous section.

```lean
theorem Aexp.evalR_iff_eval' (a : Aexp) (n : Nat) :
    a ⇓ n ↔ a.eval = n := by
  workinclass!
    constructor <;> intro h
    · induction h <;> simp_all
    · subst h; induction a <;> constructor <;> assumption
```

:::::exercise (rating := 3) (name := "bevalR")
Write a relation `Bexp.EvalR` in the same style as {name}`Aexp.EvalR`, and prove that
it is equivalent to {name}`Bexp.eval`.

```lean
inductive Bexp.EvalR : Bexp → Bool → Prop where
  -- SOLUTION
  | bool (b : Bool) : EvalR (.bool b) b
  | eq {a₁ a₂ : Aexp} {n₁ n₂ : Nat} (h₁ : a₁ ⇓ n₁) (h₂ : a₂ ⇓ n₂) : EvalR (.eq a₁ a₂) (n₁ == n₂)
  | neq {a₁ a₂ : Aexp} {n₁ n₂ : Nat} (h₁ : a₁ ⇓ n₁) (h₂ : a₂ ⇓ n₂) : EvalR (.neq a₁ a₂) (n₁ != n₂)
  | le {a₁ a₂ : Aexp} {n₁ n₂ : Nat} (h₁ : a₁ ⇓ n₁) (h₂ : a₂ ⇓ n₂) : EvalR (.le a₁ a₂) (n₁ ≤ n₂)
  | gt {a₁ a₂ : Aexp} {n₁ n₂ : Nat} (h₁ : a₁ ⇓ n₁) (h₂ : a₂ ⇓ n₂) : EvalR (.gt a₁ a₂) (n₁ > n₂)
  | not {b : Bexp} {bv : Bool} (h : EvalR b bv) : EvalR (.not b) (!bv)
  | and {b₁ b₂ : Bexp} {bv₁ bv₂ : Bool} (h₁ : EvalR b₁ bv₁) (h₂ : EvalR b₂ bv₂) :
      EvalR (.and b₁ b₂) (bv₁ && bv₂)
  -- END SOLUTION

scoped notation:55 e:56 " ⇓ " b:56 => Bexp.EvalR e b
```

```lean
theorem Bexp.evalR_iff_eval (b : Bexp) (bv : Bool) :
    b ⇓ bv ↔ b.eval = bv := by
  solution!
    constructor <;> intro h
    · induction h <;> simp_all [Aexp.evalR_iff_eval]
    · subst h
      induction b <;> constructor <;> simp_all [Aexp.evalR_iff_eval]
```

:::gradeTheorem 3 Bexp.evalR_iff_eval
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
  | plus (a₁ a₂ : Aexp)
  | minus (a₁ a₂ : Aexp)
  | mult (a₁ a₂ : Aexp)
  | div (a₁ a₂ : Aexp)             -- NEW
```

Extending the definition of `Aexp.eval` to handle this new operation would
not be straightforward due to division being a _partial_ operation; i.e.,
what should we return as the result of `.div (.num 5) (.num 0)`?
One option would be to lift the definition of `Aexp.eval` to return an option:

```lean
namespace Aexp

def eval (a : Aexp) : Option Nat :=
  match a with
  | num   n     =>  some n
  | plus  a₁ a₂ =>  match a₁.eval, a₂.eval with
                    | some n₁, some n₂ => some (n₁ + n₂)
                    | _, _ => none
  | minus a₁ a₂ =>  match a₁.eval, a₂.eval with
                    | some n₁, some n₂ => some (n₁ - n₂)
                    | _, _ => none
  | mult  a₁ a₂ =>  match a₁.eval, a₂.eval with
                    | some n₁, some n₂ => some (n₁ * n₂)
                    | _, _ => none
  | div   a₁ a₂ =>  match a₁.eval, a₂.eval with
                    | _, some 0 => none
                    | some n₁, some n₂ => some (n₁ * n₂)
                    | _, _ => none
end Aexp
```

This definition is a lot wordier than the earlier version. There are tools
to reduce this overhead, namely monads, but we will not discuss these in
Software Foundations in Lean. Curious readers can learn more about them
from [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/Monads/).

By contrast, partiality is no problem for the relational
version of the definition.

:::terse
What should `Aexp.eval` return for `.div (.num 1) (.num 0)`??
:::

```lean
inductive Aexp.EvalR : Aexp → Nat → Prop where
  | num (n : Nat) : EvalR (.num n) n
  | plus (a₁ a₂ : Aexp) (n₁ n₂ : Nat) (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.plus a₁ a₂) (n₁ + n₂)
  | minus (a₁ a₂ : Aexp) (n₁ n₂ : Nat) (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.minus a₁ a₂) (n₁ - n₂)
  | mult (a₁ a₂ : Aexp) (n₁ n₂ : Nat) (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.mult a₁ a₂) (n₁ * n₂)
  | div (a₁ a₂ : Aexp) (n₁ n₂ n₃ : Nat)             -- NEW
      (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) (hpos : n₂ > 0) (hdiv : n₂ * n₃ = n₁) :
      EvalR (.div a₁ a₂) n₃
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
  | plus (a₁ a₂ : Aexp)
  | minus (a₁ a₂ : Aexp)
  | mult (a₁ a₂ : Aexp)
```

Again, extending `Aexp.eval` would be tricky, since evaluation is now _not_
a deterministic function from expressions to numbers; but extending the
relation is no problem.

:::terse
What should `Aexp.eval` do with nondeterminism??
:::
h₂
```lean
inductive Aexp.EvalR : Aexp → Nat → Prop where
  | any (n : Nat) : EvalR .any n                   -- NEW
  | num (n : Nat) : EvalR (.num n) n
  | plus (a₁ a₂ : Aexp) (n₁ n₂ : Nat) (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.plus a₁ a₂) (n₁ + n₂)
  | minus (a₁ a₂ : Aexp) (n₁ n₂ : Nat) (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.minus a₁ a₂) (n₁ - n₂)
  | mult (a₁ a₂ : Aexp) (n₁ n₂ : Nat) (h₁ : EvalR a₁ n₁) (h₂ : EvalR a₂ n₂) :
      EvalR (.mult a₁ a₂) (n₁ * n₂)

end Slang.AevalRExtended
```

::::full
At this point you may be wondering: which of these styles should I use
by default?

Where the thing being defined is not easy to express as a function,
definitions are often simpler. When both
styles are workable, relational definitions can be more elegant and
easier to understand, and Lean generates useful inversion and induction
principles from them. On the other hand, functional definitions are
automatically deterministic and total -- whereas, for a relation,
we must _prove_ these if we need them --
and we can use Lean's computation mechanism to simplify them during proofs.

In large developments it is common to give a definition in _both_
styles plus a lemma that the two coincide, allowing later proofs to
switch between points of view at will -- exactly what we did above
in {name}`Slang.Aexp.evalR_iff_eval` and {name}`Slang.Bexp.evalR_iff_eval`.
::::

:::terse
Functional: computation. Relational: expressive. Best: both, proved equivalent.
:::
