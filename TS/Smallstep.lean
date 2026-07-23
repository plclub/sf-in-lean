import SFLMeta

import TS.Slang

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Smallstep: Small-step Operational Semantics" =>
%%%
tag := "Smallstep"
htmlSplit := .never
file := some "Smallstep"
%%%

:::dev "Benjamin Pierce (bcpierce00)"
The `hiding lean` (above in the source file) should not be needed any more and should be removed from all files everywhere it exists.
:::

:::dev "Michael Hicks (mwhicks1)"
This chapter adapts Smallstep to follow Slang, the initial part
of Imp, on just Aexp and Bexp (without variables). This means that parts
of this chapter had to adjust: Concurrent Imp is dropped in favor of Nondeterministic
Aexp, and the stack machine is simplified to just Aexps without variables.
:::

:::dev BeforeNextRelease
In this and later chapters, we are not very consistent about
   presenting computation rules first and congruence rules after...
:::

:::instructors
This chapter is meaty, but quite short -- probably too short
   for a whole week of class (though long enough that it will probably spill
   into part of a second 80-minute lecture).  Some of the material from
   Types (maybe even the whole thing) can be included in the same week (and
   perhaps the same homework assignment).

We've tried to be consistent about terminology here and in
   following chapters:
     - "steps" for the single-step relation;
     - "reduces", "executes", or "normalizes" for multi-step;
     - "evaluates" for big-step.
   One caveat for lecturers: the intuition of "abstract virtual machines" is
   fine but doesn't work well if you overdo it.  For example, real VMs don't
   generally spin off other VMs recursively, as our smallstep rules do!
:::

:::dev
HIDE: Sometime in the early 2010s, we did some mining past exams for
   exercises...
   - Loris: No interesting exercise in Finals of 2007-2009-2010-2011.
     Nothing in second midterms except for 2011.
   - 2011 midterm proposes the following exercise: give the small step
     relation of FLIP X (alternatively HAVOC, ANYTHING).  We could then ask
     to extend the proof of equivalence of big step vs small step (personally
     don't like it too much).
   - Maybe we can ask how they would adapt the definition of Hoare triple to
     small step (maybe in the exam).

HIDE: BCP: I also have a bunch of slides from earlier offerings of CIS500
   that might be good additions to the TERSE notes.

HIDE: Possible major restructuring: This chapter might better be postponed
   to later in the course.  A big-step presentation of STLC (and maybe even
   some of the extensions like subtyping?) could come first.  However, this
   would invite a much bigger change, where *all* the variants of STLC (with
   refs, with subtyping, ...) are done in big-step style.  This requires more
   thought...

HIDE: Wonder whether it would be interesting to show them how to make a
   correspondence with a "real abstract machine" at a lower level...?  There's
   a start at an exercise along these lines below.
:::

# Big-step and Small-step Evaluation

::::full
The evaluators we saw for {ref "Slang"}[Slang] were formulated in a "big-step"
style: they specify how a given expression can be evaluated to its final
value "all in one big step":

```
2 + 2 + 3 * 4 ⇓ 16
```

This style is simple and natural for many purposes -- indeed, Gilles Kahn,
who popularized it, called it _natural semantics_.  But there are some
things it does not do well.  In particular, it does not give us a convenient
way of talking about _concurrent_ programming languages, where the semantics
of a program -- the essence of how it behaves -- includes not just which
input states get mapped to which output states, but also the intermediate
states that it passes through along the way; this is crucial, since these
states can also be observed by concurrently executing code.

Another shortcoming of the big-step style is more technical but equally
critical in many situations.  Suppose we want to define a variant of our
expression language where a value could be _either_ a number _or_ a list of
numbers.  In the syntax of this extended language, it will be possible to
write strange expressions like `2 + nil`, and our semantics for arithmetic
expressions will then need to say something about how such expressions
behave.  One possibility is to maintain the convention that every arithmetic
expression evaluates to some number by choosing some way of viewing a list
as a number -- e.g., by specifying that a list should be interpreted as `0`
when it occurs in a context expecting a number.  But this would be a bit of
a hack.

A much more natural approach is simply to say that the behavior of the
expression `2 + nil` is _undefined_ -- i.e., it doesn't evaluate to any
result at all.  And we can easily do this: we just have to formulate `aeval`
and `beval` as inductive propositions rather than functions, so that we can
make them partial functions instead of total ones.

Now, however, we encounter a subtlety that will become important once we
move to a full programming language with looping.
There, a program might fail to produce a result
for _two quite different reasons_: either because the execution gets into an
infinite loop or because, at some point, the program tries to do an
operation that makes no sense, such as adding a number to a list, so that
none of the evaluation rules can be applied.

These two outcomes -- nontermination vs. getting stuck in an erroneous
configuration -- should not be confused.  In particular, we want to _allow_
the first (because permitting the possibility of infinite loops is the price
we pay for the convenience of programming with general looping constructs)
but _prevent_ the second (which is just wrong), for example by
adding some form of _typechecking_ to the language.  Indeed, this will be a
major topic of the next chapter, on _types_.  As a first step, we need a way
of presenting the semantics that allows us to distinguish nontermination
from erroneous "stuck states."

So, for lots of reasons, we'd like to have a finer-grained way of defining
and reasoning about program behaviors.  This is the topic of the present
chapter.  Our goal is to replace the "big-step" `Eval` relation with a
"small-step" relation that specifies, for a given program, how its atomic
steps of computation are performed.  In the _small-step_ style, we show how
to "reduce" an expression to a simpler form by performing a single step of
computation:

```
2 + 2 + 3 * 4
⟶ 2 + 2 + 12
⟶ 4 + 12
⟶ 16
```
::::

::::terse
Our semantics for expressions is written in the so-called "big-step" style.
Evaluation rules take an expression to a final answer "all in one step":

```
2 + 2 + 3 * 4 ⇓ 16
```

But big-step semantics makes it hard to talk about what happens _along the
way_.

_Small-step_ style: alternatively, we can show how to "reduce" an expression
to a simpler form by performing a single step of computation:

```
2 + 2 + 3 * 4
⟶ 2 + 2 + 12
⟶ 4 + 12
⟶ 16
```

Advantages of the small-step style include:

  - Finer-grained "abstract machine", closer to real implementations.
  - Extends smoothly to concurrent languages and languages with other sorts
    of _computational effects_.
  - Separates _divergence_ (nontermination) from _stuckness_ (run-time
    error).
::::

# A Toy Language

::::full
To save space, we start with an incredibly simple language of just
constants and addition.  (We use single-letter constructors `c` and `p`
-- for Constant and Plus -- for brevity.)  The same techniques scale up to
richer languages.
::::

```lean
inductive Tm where
  | c (n : Nat)          -- Constant
  | p (t1 t2 : Tm)       -- Plus
```

A standard big-step evaluator, as a function.

```lean
def evalF (t : Tm) : Nat :=
  match t with
  | .c n => n
  | .p t1 t2 => evalF t1 + evalF t2
```

Here is the same evaluator, written in exactly the same style, but formulated as an
inductively defined relation. We use the notation `t ⇓ n` for "`t` evaluates to `n`."

```
                        -------                (const)
                        c n ⇓ n

                        t1 ⇓ n1
                        t2 ⇓ n2
                    -----------------          (plus)
                    p t1 t2 ⇓ n1 + n2
```

```lean
inductive Eval : Tm → Nat → Prop where
  | const (n : Nat) : Eval (.c n) n
  | plus (t1 t2 : Tm) (n1 n2 : Nat) (h1 : Eval t1 n1) (h2 : Eval t2 n2) : Eval (.p t1 t2) (n1 + n2)

notation:50 t " ⇓ " n => Eval t n
```

::::full
Now, here is the corresponding _small-step_ relation, written `t ⟶ t'`:

```
                -------------------------------      (plus)
                p (c n1) (c n2) ⟶ c (n1 + n2)

                         t1 ⟶ t1'
                    --------------------             (plusLeft)
                    p t1 t2 ⟶ p t1' t2

                         t2 ⟶ t2'
                 ----------------------------        (plusRight)
                 p (c n1) t2 ⟶ p (c n1) t2'
```
::::

```lean
namespace SimpleArith1

inductive Step : Tm → Tm → Prop where
  | plus (n1 n2 : Nat) :
      Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm)
      (h : Step t1 t1') :
      Step (.p t1 t2) (.p t1' t2)
  | plusRight (n1 : Nat) (t2 t2' : Tm)
      (h : Step t2 t2') :
      Step (.p (.c n1) t2) (.p (.c n1) t2')

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
```

::::full
Things to notice:

  - We are defining a single reduction step, in which just one `p` node is
    replaced by its value.

  - Each step finds the _leftmost_ `p` node that is ready to go (both of its
    operands are constants) and rewrites it in place.  The first rule tells
    how to rewrite this `p` node itself; the other two rules tell how to
    find it.

  - A term that is just a constant cannot take a step.
::::

:::terse
Notice: each step reduces the _leftmost_ `p` node that is ready to go -- the first rule tells how
to rewrite it, the second and third tell where to find it -- and constants do not step to anything.
:::

Let's pause and check a couple of examples of reasoning with the step relation.

If `t1` steps to `t1'`, then `p t1 t2` steps to `p t1' t2`.

```lean
example :
    (.p
      (.p (.c 1) (.c 3))
      (.p (.c 2) (.c 4))) ⟶
    (.p
      (.c 4)
      (.p (.c 2) (.c 4))) := by
  apply Step.plusLeft; apply Step.plus
```

:::::exercise (rating := 1) (name := "test_step_2")
Right-hand sides step only once the left side is a value.

```lean
example :
    (.p
      (.c 0)
      (.p
        (.c 2)
        (.p
          (.c 1)
          (.c 3))))
      ⟶
    (.p
      (.c 0)
      (.p
        (.c 2)
        (.c 4))) := by
  solution!
    apply Step.plusRight; apply Step.plusRight; apply Step.plus
```
:::::

::::quiz
To what does the following term step?

```
.p
  (.p
    (.c 1)
    (.c 2))
  (.p
    (.c 1)
    (.c 2))
```

(A) `.c 6`
(B) `.p (.c 3) (.p (.c 1) (.c 2))`
(C) `.p (.p (.c 1) (.c 2)) (.c 3)`
(D) `.p (.c 3) (.c 3)`
(E) None of the above
::::

:::quizSolution
(B) `.p (.c 3) (.p (.c 1) (.c 2))`
:::

::::quiz
What about this one?

```
.c 1
```

(A) `.c 1`
(B) `.p (.c 0) (.c 1)`
(C) None of the above
::::

:::quizSolution
(C) None of the above
:::

```lean
end SimpleArith1
```

# Relations

::::full
We will be working with several different single-step relations, so it is
helpful to generalize a bit and state a few definitions and theorems about
relations in general. (The optional chapter `Rel` in _Logical Foundations_
develops some of these ideas in a bit more detail; reviewing that chapter
may be useful if the treatment here feels too terse.)

A _binary relation_ on a type `X` is a family of propositions parameterized
by two elements of `X` -- i.e., a proposition about pairs of elements of
`X`.
::::

:::terse
The step relation `⟶` is an example of a relation on `Tm`.
:::

:::dev "Michael Hicks (mwhicks1)" BeforeNextRelease
Should we be getting this (and `Deterministic`, `Multi`, etc.
   if appropriate) from the Lean standard library? If not, should we match the
   concepts in CSLib, if they exists there?
:::

```lean
def Relation (X : Type) := X → X → Prop
```

:::full
Our main examples of such relations in this chapter will be the
single-step reduction relation, `⟶`, and its multi-step variant, `⟶*`,
defined below, but there are many other examples -- e.g., the "equals,"
"less than," "less than or equal to," and "is the square of" relations on
numbers, and the "prefix of" relation on lists and strings.
:::

One simple property a relation may have is being _deterministic_: like
Slang's big-step evaluation, each element is related to at most one other.

_Theorem_: For each `t`, there is at most one `t'` such that `t` steps to
`t'`.  We prove it by induction on the derivation of the first step.

_Proof sketch_: We show that if `x` steps to both `y1` and `y2`, then `y1`
and `y2` are equal, by induction on a derivation of `x ⟶ y1`.  There are
several cases, depending on the last rule used in this derivation and the
last rule in the given derivation of `x ⟶ y2`.

  - If both are `plus`, the result is immediate.
  - The cases when both derivations end with `plusLeft` or `plusRight` follow by
    the induction hypothesis.
  - It cannot happen that one is `plus` and the other is `plusLeft`/`plusRight`,
    since this would imply that `x` has the form `p t1 t2` where both `t1`
    and `t2` are constants (by `plus`) _and_ one of `t1` or `t2` has the
    form `p _`.
  - Similarly, it cannot happen that one is `plusLeft` and the other is
    `plusRight`, since this would imply that `x` has the form `p t1 t2` where
    `t1` has both the form `p t11 t12` and the form `c n`.

Formally,

```lean
def Deterministic {X : Type} (R : Relation X) : Prop :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2

namespace SimpleArith2

theorem step_deterministic : Deterministic SimpleArith1.Step := by
  intro x y1 y2 h1
  induction h1 generalizing y2 with
  | plus n1 n2 =>
      intro h2
      cases h2 <;> first | rfl | cases ‹SimpleArith1.Step (.c _) _›
  | plusLeft t1 t1' t2 hs ih =>
      intro h2
      cases h2 <;> first | cases ‹SimpleArith1.Step (.c _) _› | rw [ih _ ‹SimpleArith1.Step t1 _›]
  | plusRight n1 t2 t2' hs ih =>
      intro h2
      cases h2 <;> first | cases ‹SimpleArith1.Step (.c _) _› | rw [ih _ ‹SimpleArith1.Step t2 _›]

end SimpleArith2
```

:::dev "Michael Hicks (mwhicks1)"
In the Rocq there is the development of a special tactic to make this proof simpler.
Do we want that here?
:::

## Values

::::full
Next, it will be useful to slightly reformulate the definition of
single-step reduction by stating it in terms of "values."

It can be useful to think of the `⟶` relation as defining an _abstract
machine_:

  - At any moment, the _state_ of the machine is a term.
  - A _step_ of the machine is an atomic unit of computation -- here, a
    single "add" operation.
  - The _halting states_ of the machine are ones where there is no more
    computation to be done.

We can then _execute_ a term `t` as follows:

  - Take `t` as the starting state of the machine.
  - Repeatedly use the `⟶` relation to find a sequence of machine states,
    starting with `t`, where each state steps to the next.
  - When no more reduction is possible, "read out" the final state of the
    machine as the result of execution.

Intuitively, it is clear that the final states of our machine are always
terms of the form `c n` for some `n`.  We call such terms _values_.
::::

:::terse
Final states of our machine are terms of the form `c n`.  We call such terms _values_.
:::

```lean
inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)
```

::::full
Having introduced the idea of values, we can use it in the definition of
the `⟶` relation to write the `plusRight` rule in a slightly more elegant way.

```
                ------------------------------      (plus)
                p (c n1) (c n2) ⟶ c (n1 + n2)

                         t1 ⟶ t1'
                    -------------------             (plusLeft)
                    p t1 t2 ⟶ p t1' t2

                         IsValue v1
                         t2 ⟶ t2'
                    -------------------             (plusRight)
                    p v1 t2 ⟶ p v1 t2'
```

Again, the variable names in the informal presentation carry important
information: by convention, `v1` ranges only over values, while `t1` and
`t2` range over arbitrary terms.

(Given this convention, the explicit `IsValue` hypothesis is arguably
redundant, since the naming convention tells us where to add it when
translating the informal rule to Lean.  We'll keep it for now, to maintain
a close correspondence between the informal and Lean versions of the rules,
but later on we'll drop it in informal rules for brevity.)
::::

Here are the formal rules.

```lean
inductive Step : Tm → Tm → Prop where
  | plus (n1 n2 : Nat) :
      Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm)
      (h : Step t1 t1') :
      Step (.p t1 t2) (.p t1' t2)
  | plusRight (v1 t2 t2' : Tm)
      (hv : IsValue v1)
      (h : Step t2 t2') :
      Step (.p v1 t2) (.p v1 t2')

notation:40 t:41 " ⟶ " t':41 => Step t t'
```

:::::exercise (rating := 3) (name := "redo_determinism")
As a sanity check on this change, let's re-verify determinism.  Here's an
informal proof:

_Proof sketch_: We must show that if `x` steps to both `y1` and `y2`, then
`y1` and `y2` are equal.  Consider the final rules used in the derivations
of `x ⟶ y1` and `x ⟶ y2`.

  - If both are `plus`, the result is immediate.
  - The cases when both derivations end with `plusLeft` or `plusRight` follow by
    the induction hypothesis.
  - It cannot happen that one is `plus` and the other is `plusLeft`/`plusRight`,
    since this would imply that `x` has the form `p t1 t2` where both `t1`
    and `t2` are constants (by `plus`) _and_ one of `t1` or `t2` has the
    form `p _`.
  - Similarly, it cannot happen that one is `plusLeft` and the other is
    `plusRight`, since this would imply that `x` has the form `p t1 t2` where
    `t1` both has the form `p t11 t12` and is a value (hence has the form
    `c n`).

Most of this proof is the same as the one above.  But to get maximum
benefit from the exercise you should try to write your formal version from
scratch and just use the earlier one if you get stuck.  The impossible
cross-cases now also use the fact that a `IsValue` (a `c n`) cannot step.

```lean
theorem step_deterministic : Deterministic Step := by
  solution!
    intro x y1 y2 h1
    induction h1 generalizing y2 with
    | plus n1 n2 =>
        intro h2; cases h2 with
        | plus => rfl
        | plusLeft _ _ _ hs => cases hs
        | plusRight _ _ _ hv hs => cases hs
    | plusLeft t1 t1' t2 hs ih =>
        intro h2; cases h2 with
        | plus => cases hs
        | plusLeft _ _ _ hs2 => rw [ih _ hs2]
        | plusRight _ _ _ hv hs2 => cases hv; cases hs
    | plusRight v1 t2 t2' hv hs ih =>
        intro h2; cases h2 with
        | plus => cases hs
        | plusLeft _ _ _ hs2 => cases hv; cases hs2
        | plusRight _ _ _ hv2 hs2 => rw [ih _ hs2]
```

:::gradeTheorem 3 "step_deterministic"
:::
:::::

## Strong Progress and Normal Forms

::::full
The definition of single-step reduction for our toy language is fairly
simple, but for a larger language it would be easy to forget one of the
rules and accidentally create a situation where some term cannot take a
step even though it has not been completely reduced to a value.  The
following theorem shows that we did not, in fact, make such a mistake here.

_Theorem_ (_Strong Progress_): If `t` is a term, then either `t` is a value
or else there exists a term `t'` such that `t ⟶ t'`.

_Proof_: By induction on `t`.

  - Suppose `t = c n`.  Then `t` is a value.
  - Suppose `t = p t1 t2`, where (by the IH) `t1` either is a value or can
    step to some `t1'`, and where `t2` is either a value or can step to some
    `t2'`.  We must show `p t1 t2` is either a value or steps to some `t'`.

    - If `t1` and `t2` are both values, then `t` can take a step, by
      `plus`.
    - If `t1` is a value and `t2` can take a step, then so can `t`, by
      `plusRight`.
    - If `t1` can take a step, then so can `t`, by `plusLeft`.

Or, formally:
::::

```lean
theorem strong_progress (t : Tm) : IsValue t ∨ ∃ t', t ⟶ t' := by
  induction t with
  | c n => left; exact .const n
  | p t1 t2 ih1 ih2 =>
      right
      cases ih1 with
      | inl hv1 =>
          cases ih2 with
          | inl hv2 =>
              cases hv1 with
              | const n1 =>
                  cases hv2 with
                  | const n2 => exact ⟨.c (n1 + n2), .plus n1 n2⟩
          | inr h2 =>
              obtain ⟨t2', ht2⟩ := h2
              exact ⟨.p t1 t2', .plusRight t1 t2 t2' hv1 ht2⟩
      | inr h1 =>
          obtain ⟨t1', ht1⟩ := h1
          exact ⟨.p t1' t2, .plusLeft t1 t1' t2 ht1⟩
```

::::full
This important property is called _strong progress_, because every term
either is a value or can "make progress" by stepping to some other term.
(The qualifier "strong" distinguishes it from a more refined version that
we'll see in later chapters, called simply _progress_.)

The idea of "making progress" can be extended to tell us something
interesting about values in this language: they are exactly the terms that
do _not_ make progress in this sense.  Let's give a name to "terms that
cannot make progress."  We'll call them _normal forms_.
::::

```lean
def IsNormalForm {X : Type} (R : Relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'
```

::::full
Note that this definition specifies what it is to be a normal form for an
_arbitrary_ relation `R` over an arbitrary type `X`, not just for the
particular single-step reduction relation over terms that we are interested
in at the moment.  We'll re-use the same terminology for talking about
other relations later in the course.
::::

We can use this terminology to generalize the observation we made in the
strong progress theorem: in this language (though not necessarily, in
general), normal forms and values are actually the same thing.

```lean
theorem value_is_nf (v : Tm) (h : IsValue v) : IsNormalForm Step v := by
  intro hc
  obtain ⟨t', ht⟩ := hc
  cases h with
  | const n => cases ht

theorem nf_is_value (t : Tm) (h : IsNormalForm Step t) : IsValue t := by
  cases strong_progress t with
  | inl hv => exact hv
  | inr hstep => exact absurd hstep h

theorem nf_same_as_value (t : Tm) : IsNormalForm Step t ↔ IsValue t :=
  ⟨nf_is_value t, value_is_nf t⟩
```

Why is this interesting? Because `IsValue` is a _syntactic_ concept -- it is
defined by looking at the way a term is written -- while `IsNormalForm` is a
_semantic_ one -- it is defined by looking at how the term steps.

It is not obvious that these concepts should characterize the same set of terms!

Indeed, we could easily have written the definitions (incorrectly) so that
they would _not_ coincide.

Suppose, for example, we define `IsValue` so that it includes some terms that
are not finished reducing.  (Even if you don't work the exercise
`value_not_same_as_normal_form1` below and the following ones, make sure you
can think of an example of such a term.)

```lean
namespace Temp1

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)
  | funny (t1 : Tm) (n : Nat) : IsValue (.p t1 (.c n))     -- <---

inductive Step : Tm → Tm → Prop where
  | plus (n1 n2 : Nat) : Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm) (h : Step t1 t1') : Step (.p t1 t2) (.p t1' t2)
  | plusRight (v1 t2 t2' : Tm) (hv : IsValue v1) (h : Step t2 t2') : Step (.p v1 t2) (.p v1 t2')
```

::::quiz
Using this wrong definition of `IsValue`, to how many different values does
the following term reduce in zero or more steps?

```
.p (.p (.c 1) (.c 2)) (.c 3)
```

:::quizSolution
```
Three:  `.p (.p (.c 1) (.c 2)) (.c 3)` itself is a value;
`.p (.c 3) (.c 3)` is a value; `.c 6` is a value.
```
:::
::::

::::hide
```lean
theorem testval1 : IsValue (.p (.p (.c 1) (.c 2)) (.c 3)) := .funny _ 3
theorem testval2 :
    Step (.p (.p (.c 1) (.c 2)) (.c 3)) (.p (.c 3) (.c 3))
      ∧ IsValue (.p (.c 3) (.c 3)) := by
  exact ⟨by apply Step.plusLeft; apply Step.plus, .funny _ 3⟩
theorem testval3 : Step (.p (.c 3) (.c 3)) (.c 6) ∧ IsValue (.c 6) :=
  ⟨.plus 3 3, .const 6⟩
```
::::

::::quiz
To how many different terms does the following term `Step` (in one step)?

```
.p (.p (.c 1) (.c 2)) (.p (.c 3) (.c 4))
```

:::quizSolution
```
Two: `.p (.c 3) (.p (.c 3) (.c 4))` via `plusLeft` and
`.p (.p (.c 1) (.c 2)) (.c 7)` via `plusRight`.
```
:::
::::

:::::exercise (rating := 3) (name := "value_not_same_as_normal_form1")
```lean
theorem value_not_same_as_normal_form :
    ∃ v, IsValue v ∧ ¬ IsNormalForm Step v := by
  apply Exists.intro (.p (.c 0) (.c 0))
  apply And.intro (.funny _ 0)
  solution!
    intro h
    exact h ⟨.c (0 + 0), .plus 0 0⟩
```
:::::

```lean
end Temp1
```

:::::exercise (rating := 2) (name := "value_not_same_as_normal_form2")
Or we might (again, wrongly) define `Step` so that it permits something
designated as a value to reduce further.  We again lose the property that
values are the same as normal forms.

```lean
namespace Temp2

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)               -- Original definition

inductive Step : Tm → Tm → Prop where
  | funny (n : Nat) : Step (.c n) (.p (.c n) (.c 0))     -- <--- NEW
  | plus (n1 n2 : Nat) : Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm) (h : Step t1 t1') : Step (.p t1 t2) (.p t1' t2)
  | plusRight (v1 t2 t2' : Tm) (hv : IsValue v1) (h : Step t2 t2') : Step (.p v1 t2) (.p v1 t2')
```

::::quiz
With this definition, to how many different terms does the following term
step (in exactly one step)?

```
.p (.c 1) (.c 3)
```

:::quizSolution
```
Three: `plus` yields `.c 4`; `plusLeft` with `funny` yields
`.p (.p (.c 1) (.c 0)) (.c 3)`; `plusRight` with `funny` yields
`.p (.c 1) (.p (.c 3) (.c 0))`.
```
:::
::::

```lean
theorem value_not_same_as_normal_form :
    ∃ v, IsValue v ∧ ¬ IsNormalForm Step v := by
  apply Exists.intro (.c 5)
  apply And.intro (.const 5)
  solution!
    intro h
    exact h ⟨.p (.c 5) (.c 0), .funny 5⟩

end Temp2
```
:::::

:::::exercise (rating := 3) (name := "value_not_same_as_normal_form3")
Finally, we might define `IsValue` and `Step` so that there is some term that
is _not_ a value but that _also_ cannot take a step.  Such terms are said to
be _stuck_.  In this case, this is caused by a mistake in the semantics, but
we will also see situations where, even in a correct language definition, it
makes sense to allow some terms to be stuck.  (Note that `plusRight` is missing
below.)

```lean
namespace Temp3

inductive IsValue : Tm → Prop where
  | const (n : Nat) : IsValue (.c n)

inductive Step : Tm → Tm → Prop where
  | plus (n1 n2 : Nat) : Step (.p (.c n1) (.c n2)) (.c (n1 + n2))
  | plusLeft (t1 t1' t2 : Tm) (h : Step t1 t1') : Step (.p t1 t2) (.p t1' t2)
```

::::quiz
With this definition, to how many terms does the following term step (in
one step)?

```
.p (.c 1) (.p (.c 1) (.c 2))
```

:::quizSolution
none!
:::
::::

```lean
theorem value_not_same_as_normal_form :
    ∃ t, ¬ IsValue t ∧ IsNormalForm Step t := by
  apply Exists.intro (.p (.c 1) (.p (.c 1) (.c 2)))
  apply And.intro
  · solution!
      intro h; cases h
  · solution!
      intro h
      obtain ⟨t', ht⟩ := h
      cases ht with
      | plusLeft _ _ _ hs => cases hs

end Temp3
```
:::::

# Multi-Step Reduction

::::full
We've been working so far with the _single-step reduction_ relation `⟶`,
which formalizes the individual steps of an abstract machine for executing
programs.  We can use the same machine to reduce programs to completion --
to find out what final result they yield.  This can be formalized as
follows:

  - First, we define a _multi-step reduction relation_ `⟶*`, which relates
    terms `t` and `t'` if `t` can reach `t'` by any number (including zero)
    of single reduction steps.
  - Then we define a "result" of a term `t` as a normal form that `t` can
    reach by multi-step reduction.

Since we'll want to reuse the idea of multi-step reduction many times with
many different single-step relations, let's define the concept generically.
Given a relation `R` (e.g., the step relation `⟶`), we define a new relation
`Multi R`, called the _multi-step closure of `R`_, as follows.
::::

```lean
inductive Multi {X : Type} (R : Relation X) : X → X → Prop where
  | refl (x : X) : Multi R x x
  | step (x y z : X) (h1 : R x y) (h2 : Multi R y z) : Multi R x z
```

::::full
The effect of this definition is that `Multi R` relates two elements `x` and `y` if
- `x = y`, or
- `R x y`, or
- there is some nonempty sequence `z₁`, `z₂` , ..., `zₙ` such that
           `R x₁ z₁`,
           `R z₁ z₂`,
           ...,
           `R zₙ y`.

Intuitively, if `R` describes a single-step of computation, then `z₁ ... zₙ` are the intermediate steps of computation that get us from `x` to `y`.
::::

We write `⟶*` for the `Multi Step` relation on terms
```lean
notation:40 t:41 " ⟶* " t':41 => Multi Step t t'
```

The relation `Multi R` has several crucial properties.

::::full
First, it is obviously _reflexive_ (a term can execute to itself by taking zero steps).

Second, it _contains_ `R` -- single-step reductions are a particular case of
multi-step executions.  (It is this fact that justifies the word "closure"
in "multi-step closure of `R`.")
::::

```lean
theorem multi_single {X : Type} (R : Relation X) (x y : X) (h : R x y) :
    Multi R x y :=
  .step x y y h (.refl y)
```

::::full
Third, `Multi R` is _transitive_.
::::

```lean
theorem multi_trans {X : Type} (R : Relation X) (x y z : X)
    (g : Multi R x y) (h : Multi R y z) : Multi R x z := by
  induction g with
  | refl a => exact h
  | step a b c h1 h2 ih => exact .step a b z h1 (ih h)
```

::::full
In particular, for the `Multi Step` relation on terms, if `t1 ⟶* t2` and
   `t2 ⟶* t3`, then `t1 ⟶* t3`.
::::

::::quiz
Which of the following relations on numbers _cannot_ be expressed as
`Multi R` for some `R`?

(A) less than or equal
(B) strictly less than
(C) equal
(D) none of the above
::::

:::quizSolution
(B) strictly less than
:::

## Examples

```lean
example :
    (.p (.p (.c 0) (.c 3)) (.p (.c 2) (.c 4))) ⟶* .c ((0 + 3) + (2 + 4)) := by
  apply Multi.step (y := .p (.c (0 + 3)) (.p (.c 2) (.c 4)))
  · exact .plusLeft _ _ _ (.plus 0 3)
  apply Multi.step (y := .p (.c (0 + 3)) (.c (2 + 4)))
  · exact .plusRight _ _ _ (.const _) (.plus 2 4)
  · exact multi_single _ _ _ (.plus (0 + 3) (2 + 4))
```

:::::exercise (rating := 1) (name := "test_multistep_2")
```lean
example : (.c 3 : Tm) ⟶* .c 3 := solution!(.refl _)
```
:::::

:::::exercise (rating := 1) (name := "test_multistep_3")
```lean
example : (.p (.c 0) (.c 3)) ⟶* .p (.c 0) (.c 3) := solution!(.refl _)
```
:::::

:::::exercise (rating := 2) (name := "test_multistep_4")
```lean
example :
    (.p (.c 0) (.p (.c 2) (.p (.c 0) (.c 3))))
      ⟶* (.p (.c 0) (.c (2 + (0 + 3)))) := by
  solution!
    apply Multi.step (y := .p (.c 0) (.p (.c 2) (.c (0 + 3))))
    · exact .plusRight _ _ _ (.const 0) (.plusRight _ _ _ (.const 2) (.plus 0 3))
    · exact multi_single _ _ _ (.plusRight _ _ _ (.const 0) (.plus 2 (0 + 3)))
```
:::::

## Normal Forms Again

If `t` reduces to `t'` in zero or more steps and `t'` is a normal form, we
   say that "`t'` is _a normal form of_ `t`."

```lean
def IsNormalFormOf {X : Type} (R : Relation X) (t t' : X) : Prop :=
  Multi R t t' ∧ IsNormalForm R t'
```

:::full
We have already seen that, for our language, single-step reduction is
deterministic -- i.e., a given term can take a single step in at most one
way.  It follows that, if `t` can reach a normal form, then this normal form
is unique.

In other words, we can actually pronounce `IsNormalFormOf t t'`
as "`t'` is _the_ normal form of `t`."
:::

:::terse
When `R` is deterministic (as for our language's semantics), then its normal form is _unique_.
:::

:::dev PotentialImprovement
YOTAM: The proof can be given for the general case, i.e. that
   determinism of a relation implies the determinism of its `IsNormalFormOf`
   induced counterpart.  BCP 23: That would be a nice improvement.
:::

:::::exercise (rating := 3) (name := "normal_forms_unique")
```lean
theorem normal_forms_unique : Deterministic (IsNormalFormOf Step) := by
  -- We recommend using this initial setup as-is!
  intro x y1 y2 p1 p2
  obtain ⟨p11, p12⟩ := p1
  obtain ⟨p21, p22⟩ := p2
  solution!
    induction p11 generalizing y2 with
    | refl a =>
        cases p21 with
        | refl => rfl
        | step _ b _ h1 _ => exact absurd ⟨b, h1⟩ p12
    | step a b c h1 h2 ih =>
        cases p21 with
        | refl => exact absurd ⟨b, h1⟩ p22
        | step _ b' _ h1' h2' =>
            have hbb : b = b' := step_deterministic _ _ _ h1 h1'
            subst hbb
            exact ih y2 p12 h2' p22
```
:::::

:::full
Indeed, something stronger is true for this language (though not for all the
languages we will see): the reduction of _any_ term `t` will eventually
reach a normal form in a finite number of steps -- i.e., `IsNormalFormOf` is
a _total_ function.  We say the `Step` relation is _normalizing_.  To prove
it, we need a couple of congruence lemmas.
:::

:::terse
The `Step` relation is _normalizing_ it is deterministic and always reaches a normal form
in a finite number of steps.
:::

```lean
def Normalizing {X : Type} (R : Relation X) : Prop :=
  ∀ t, ∃ t', IsNormalFormOf R t t'

theorem multistep_congr_1 (t1 t1' t2 : Tm) (h : t1 ⟶* t1') : (.p t1 t2) ⟶* (.p t1' t2) := by
  induction h with
  | refl x => exact .refl _
  | step x y z h1 h2 ih => exact .step _ (.p y t2) _ (.plusLeft x y t2 h1) ih
```

:::::exercise (rating := 2) (name := "multistep_congr_2")
```lean
theorem multistep_congr_2 (v1 t2 t2' : Tm) (hv : IsValue v1) (h : t2 ⟶* t2') :
    (.p v1 t2) ⟶* (.p v1 t2') := by
  solution!
    induction h with
    | refl x => exact .refl _
    | step x y z h1 h2 ih => exact .step _ (.p v1 y) _ (.plusRight v1 x y hv h1) ih
```
:::::

::::full
With these lemmas in hand, the main proof is a straightforward induction.

_Theorem_: The `Step` relation is normalizing -- i.e., for every `t` there
exists some `t'` such that `t` reduces to `t'` and `t'` is a normal form.

_Proof sketch_: By induction on terms.  There are two cases:

  - `t = c n` for some `n`.  Here `t` doesn't take a step, and we have
    `t' = t`.  We derive the left-hand side by reflexivity and the right-hand
    side by observing (a) that values are normal forms (by
    `nf_same_as_value`) and (b) that `t` is a value (by `const`).

  - `t = p t1 t2` for some `t1` and `t2`.  By the IH, `t1` and `t2` reduce to
    normal forms `t1'` and `t2'`.  Recall that normal forms are values (by
    `nf_same_as_value`); we therefore know that `t1' = c n1` and `t2' = c n2`
    for some `n1` and `n2`.  We combine the `⟶*` derivations for `t1` and
    `t2` using `multistep_congr_1` and `multistep_congr_2` to prove that
    `p t1 t2` reduces in many steps to `t' = c (n1 + n2)`.  Finally,
    `c (n1 + n2)` is a value, which is in turn a normal form.
::::

```lean
theorem step_normalizing : Normalizing Step := by
  intro t
  induction t with
  | c n => exact ⟨.c n, .refl _, (nf_same_as_value _).mpr (.const n)⟩
  | p t1 t2 ih1 ih2 =>
      obtain ⟨t1', hs1, hnf1⟩ := ih1
      obtain ⟨t2', hs2, hnf2⟩ := ih2
      obtain ⟨n1⟩ := (nf_same_as_value _).mp hnf1
      obtain ⟨n2⟩ := (nf_same_as_value _).mp hnf2
      apply Exists.intro (.c (n1 + n2))
      apply And.intro _ ((nf_same_as_value _).mpr (.const _))
      apply multi_trans _ _ _ _ (multistep_congr_1 t1 (.c n1) t2 hs1)
      apply multi_trans _ _ _ _ (multistep_congr_2 (.c n1) t2 (.c n2) (.const n1) hs2)
      exact multi_single _ _ _ (.plus n1 n2)
```

## Equivalence of Big-Step and Small-Step

:::dev PotentialImprovement
We could really use more informal proofs in this section, at least
   in the solutions!
:::

Having defined the operational semantics of our tiny programming language in
two different ways (big-step and small-step), it makes sense to ask whether
these definitions actually define the same thing!

They do, though it takes
a little work to show it.  The details are left as an exercise.  We consider
the two implications separately.  First, big-step evaluation implies
multi-step reduction to a value.

:::::exercise (rating := 3) (name := "multistep_of_eval")
```lean
theorem multistep_of_eval (t : Tm) (n : Nat) (h : t ⇓ n) : t ⟶* .c n := by
  solution!
    induction h with
    | const n => exact .refl _
    | plus t1 t2 n1 n2 h1 h2 ih1 ih2 =>
        apply multi_trans _ _ _ _ (multistep_congr_1 t1 (.c n1) t2 ih1)
        apply multi_trans _ _ _ _ (multistep_congr_2 (.c n1) t2 (.c n2) (.const n1) ih2)
        exact multi_single _ _ _ (.plus n1 n2)
```

The key ideas in the proof can be seen in the following picture:

```
p t1 t2 ⟶            (by plusLeft)
p t1' t2 ⟶           (by plusLeft)
p t1'' t2 ⟶          (by plusLeft)
...
p (c n1) t2 ⟶        (by plusRight)
p (c n1) t2' ⟶       (by plusRight)
p (c n1) t2'' ⟶      (by plusRight)
...
p (c n1) (c n2) ⟶    (by plus)
c (n1 + n2)
```

That is, the multi-step reduction of a term of the form `p t1 t2` proceeds in
three phases:

  - First, we use `plusLeft` some number of times to reduce `t1` to a normal
    form, which must (by `nf_same_as_value`) be a term of the form `c n1` for
    some `n1`.
  - Next, we use `plusRight` some number of times to reduce `t2` to a normal
    form, which must again be a term of the form `c n2` for some `n2`.
  - Finally, we use `plus` one time to reduce `p (c n1) (c n2)` to
    `c (n1 + n2)`.

To formalize this intuition, you'll need the congruence lemmas from above,
plus some basic properties of `⟶*` (that it is reflexive, transitive, and
includes `⟶`).
:::::

:::::exercise (rating := 3) (name := "multistep_of_eval_inf")
Write a detailed informal version of the proof of `multistep_of_eval`.  (A
paper exercise -- there is no Lean proof to fill in here.)

:::solution
```
_Theorem_: for all `t`, `n`, if `t ⇓ n` then `t ⟶* c n`.

_Proof_: By induction on a derivation of `t ⇓ n`.

  - Suppose the final rule used to show `t ⇓ n` is `const`.  Then `t = c n`.
    We must show `c n ⟶* c n`.  This holds by `refl`.

  - Suppose the final rule used to show `t ⇓ n` is `plus`.  Then
    `t = p t1 t2`, and we know that `t1 ⇓ c n1` and `t2 ⇓ c n2` for some
    `n1` and `n2`, with `n = n1 + n2`.  The IH tells us that `t1 ⟶* c n1` and
    `t2 ⟶* c n2`.  We must show that `p t1 t2 ⟶* c (n1 + n2)`.

    First, `p t1 t2 ⟶* p (c n1) t2` by `multistep_congr_1` and the multistep
    derivation for `t1`.  Observing that `c n1` is a value, we also have
    `p (c n1) t2 ⟶* p (c n1) (c n2)` by `multistep_congr_2` and the multistep
    derivation for `t2`.  It's also easy to see by `plus` that
    `p (c n1) (c n2) ⟶ c (n1 + n2)`, and so, by `Step` and
    `refl`, that the same is true for `⟶*`.  We can now use transitivity
    of `⟶*` to stitch these derivations together, proving
    `p t1 t2 ⟶* c (n1 + n2)`.
```
:::

:::grade
```
GRADE_MANUAL 3: multistep_of_eval_inf
```
:::
:::::

For the converse, we need one lemma, which establishes a relation between
   single-step reduction and big-step evaluation.  A single step preserves the
   big-step value.

:::::exercise (rating := 3) (name := "eval_of_step")
```lean
theorem eval_of_step (t t' : Tm) (n : Nat) (hs : t ⟶ t') (he : t' ⇓ n) : t ⇓ n := by
  solution!
    induction hs generalizing n with
    | plus n1 n2 =>
        cases he with
        | const _ => exact .plus _ _ n1 n2 (.const n1) (.const n2)
    | plusLeft t1 t1' t2 h1 ih =>
        cases he with
        | plus _ _ m1 m2 he1 he2 => exact .plus t1 t2 m1 m2 (ih m1 he1) he2
    | plusRight v1 t2 t2' hv h2 ih =>
        cases he with
        | plus _ _ m1 m2 he1 he2 => exact .plus v1 t2 m1 m2 he1 (ih m2 he2)
```
:::::

The fact that small-step reduction implies big-step evaluation is now
straightforward to prove, once we have factored out the observation that
every normal form is a value.  The proof proceeds by induction on the
multi-step reduction sequence that is buried in the hypothesis
`IsNormalFormOf t t'`.  (Make sure you understand the statement before you
start to work on the proof.)

:::::exercise (rating := 3) (name := "eval_of_multistep")
```lean
theorem eval_of_multistep (t t' : Tm) (h : IsNormalFormOf Step t t') :
    ∃ n, t' = .c n ∧ t ⇓ n := by
  solution!
    obtain ⟨hs, hnf⟩ := h
    obtain ⟨n⟩ := (nf_same_as_value t').mp hnf
    have H : ∀ (a tc : Tm), Multi Step a tc → tc = .c n → a ⇓ n := by
      intro a tc hst
      induction hst with
      | refl b => intro heq; subst heq; exact .const n
      | step b c d h1 h2 ih => intro heq; exact eval_of_step b c n h1 (ih heq)
    exact ⟨n, rfl, H t (.c n) hs rfl⟩
```
:::::

:::dev "Michael Clarkson (clarksmr)" PotentialImprovement
I would have thought this is how to state and prove the theorem:

```
theorem eval_of_multistep' (t : Tm) (n : Nat) (h : t ⟶* .c n) : t ⇓ n
```

It's simpler to prove this version -- no reasoning about normal forms is
needed -- and the statement is clearly the converse of `multistep_of_eval`,
so we could get a corollary stating an equivalence:
`t ⇓ n ↔ t ⟶* c n`.  And that seems to finish the subsection on a much
stronger note.
BCP 10/18: The new proof is attractively short, but I'm not 100% convinced
this is what we really want to show.  (It assumes that all normal forms have
the shape `c n`, no?)
LY: The formulation as an equivalence looks nice, but it needs to be paired
with the result that every normal form is a `c n`, which is indeed proved
earlier (`nf_is_value`), but that point seems too subtle to make for this
course.
:::

:::::exercise (rating := 3) (name := "interp_tm")
Remember that we also defined big-step evaluation of terms as a function
`evalF`.  Prove that it is equivalent to the relational semantics.  (Hint: we
just proved that `Eval` and `multistep` are equivalent, so logically it
doesn't matter which you choose.  One will be easier than the other, though!)

```lean
theorem evalF_eval (t : Tm) (n : Nat) : evalF t = n ↔ t ⇓ n := by
  solution!
    constructor
    · intro hi
      subst hi
      induction t with
      | c n => exact .const n
      | p t1 t2 ih1 ih2 => exact .plus t1 t2 _ _ ih1 ih2
    · intro he
      induction he with
      | const n => rfl
      | plus t1 t2 n1 n2 h1 h2 ih1 ih2 => simp only [evalF]; rw [ih1, ih2]
```
:::::

# Small-Step Slang

::::full
Now for a more serious example: a small-step semantics for the richer
arithmetic and boolean expressions of the {ref "Slang"}[Slang] chapter (with subtraction,
multiplication, and the boolean operators) rather than the two-constructor
toy language we have used so far.

The small-step reduction relations for these expressions are straightforward
extensions of the tiny language we've been working up to now.  To make them
easier to read, we introduce the symbolic notations `⟶a` and `⟶b` for the
arithmetic and boolean step relations.
::::

:::terse
Small-step semantics for the richer `Slang` arithmetic and boolean
expressions.  Notations: `⟶a` (arithmetic) and `⟶b` (boolean).
:::

We work in the `Slang` namespace, reusing the arithmetic and boolean expression
syntax (`Aexp`, `Bexp`) and the big-step evaluator (`Aexp.eval`) from the
`Slang` chapter:

```lean
namespace Slang
```

## Arithmetic Expressions

The arithmetic _values_ (the normal forms of the small-step relation below)
are just the numeric literals:

```lean
inductive IsAValue : Aexp → Prop where
  | num (n : Nat) : IsAValue (.num n)
```

::::full
Here is the small-step relation for arithmetic expressions.  A compound
expression reduces its left operand first; once that is a value, it reduces
its right operand; once both are values, it computes the result.  (We show
the rules for `+` in full; those for `−` and `×` have exactly the same
shape.)

```
                        a1 ⟶a a1'
                   --------------------             (plusLeft)
                   a1 + a2 ⟶a a1' + a2

                 IsAValue v1      a2 ⟶a a2'
                 ---------------------------        (plusRight)
                   v1 + a2 ⟶a v1 + a2'

                 -------------------------          (plus)
                 n1 + n2 ⟶a num (n1 + n2)
```
::::

:::instructors
Warn students about the notational confusion with the rules plus, etc.
:::

```lean
inductive AStep : Aexp → Aexp → Prop where
  | plusLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : AStep (.plus a1 a2) (.plus a1' a2)
  | plusRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      AStep (.plus v1 a2) (.plus v1 a2')
  | plus (n1 n2 : Nat) :  AStep (.plus (.num n1) (.num n2)) (.num (n1 + n2))
  | minusLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : AStep (.minus a1 a2) (.minus a1' a2)
  | minusRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      AStep (.minus v1 a2) (.minus v1 a2')
  | minus (n1 n2 : Nat) : AStep (.minus (.num n1) (.num n2)) (.num (n1 - n2))
  | multLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : AStep (.mult a1 a2) (.mult a1' a2)
  | multRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      AStep (.mult v1 a2) (.mult v1 a2')
  | mult (n1 n2 : Nat) : AStep (.mult (.num n1) (.num n2)) (.num (n1 * n2))

scoped notation:40 a:41 " ⟶a " a':41 => AStep a a'
```

::::full
Notice that `AStep` has exactly the shape `Aexp → Aexp → Prop` -- i.e., it is a
`Relation Aexp` in the sense of the _Relations_ section above. So the generic
vocabulary from that section (`Deterministic`, `IsNormalForm`, the multi-step
closure `Multi`, ...) applies to it directly.
::::

Here is a one-step reduction: since the left operand `3` is already a value,
the right operand is the one that takes a step.

```lean
example :
    (Aexp.plus (.num 3) (.plus (.num 2) (.num 1))) ⟶a (.plus (.num 3) (.num 3)) :=
  .plusRight _ _ _ (.num 3) (.plus 2 1)
```

:::::exercise (rating := 2) (name := "strong_progress_arith")
Every arithmetic expression is either a value or can take a step -- the same
_strong progress_ property we proved for the toy language, now for the richer
`Slang` arithmetic expressions.

```lean
theorem strong_progress_arith (a : Aexp) : IsAValue a ∨ ∃ a', a ⟶a a' := by
  solution!
    induction a with
    | num n => exact .inl (.num n)
    | plus a1 a2 ih1 ih2 =>
        right
        cases ih1 with
        | inr h1 => obtain ⟨a1', ha1⟩ := h1; exact ⟨_, .plusLeft _ _ _ ha1⟩
        | inl hv1 => cases hv1 with
          | num n1 => cases ih2 with
            | inr h2 => obtain ⟨a2', ha2⟩ := h2
                        exact ⟨_, .plusRight _ _ _ (.num n1) ha2⟩
            | inl hv2 => cases hv2 with
              | num n2 => exact ⟨_, .plus n1 n2⟩
    | minus a1 a2 ih1 ih2 =>
        right
        cases ih1 with
        | inr h1 => obtain ⟨a1', ha1⟩ := h1; exact ⟨_, .minusLeft _ _ _ ha1⟩
        | inl hv1 => cases hv1 with
          | num n1 => cases ih2 with
            | inr h2 => obtain ⟨a2', ha2⟩ := h2
                        exact ⟨_, .minusRight _ _ _ (.num n1) ha2⟩
            | inl hv2 => cases hv2 with
              | num n2 => exact ⟨_, .minus n1 n2⟩
    | mult a1 a2 ih1 ih2 =>
        right
        cases ih1 with
        | inr h1 => obtain ⟨a1', ha1⟩ := h1; exact ⟨_, .multLeft _ _ _ ha1⟩
        | inl hv1 => cases hv1 with
          | num n1 => cases ih2 with
            | inr h2 => obtain ⟨a2', ha2⟩ := h2
                        exact ⟨_, .multRight _ _ _ (.num n1) ha2⟩
            | inl hv2 => cases hv2 with
              | num n2 => exact ⟨_, .mult n1 n2⟩
```
:::::

## Boolean Expressions

::::full
The small-step relation for boolean expressions reduces the arithmetic
subexpressions of a comparison (using `⟶a`) and then applies the comparison,
and it short-circuits `¬` and `∧` on boolean literals.

We are not actually going to bother to define boolean values, since they
aren't needed in the definition of `⟶b` below (why?), though they might be if
our language were a bit more complicated (why?).

Again we show a
representative sample; `neq`, `le`, and `gt` follow the same pattern as `eq`.

```
                        a1 ⟶a a1'
                  --------------------             (eqLeft)
                  a1 = a2 ⟶b a1' = a2

                IsAValue v1      a2 ⟶a a2'
                ---------------------------        (eqRight)
                  v1 = a2 ⟶b v1 = a2'

                  ---------------------            (eq)
                  n1 = n2 ⟶b (n1 = n2)

                        b1 ⟶b b1'
                      --------------               (notStep)
                      ¬ b1 ⟶b ¬ b1'

                    ----------------               (notTrue)
                    ¬ true ⟶b false

                  ---------------------            (andFalse)
                  false ∧ b2 ⟶b false
```

Here are the formal rules.
::::

```lean
inductive BStep : Bexp → Bexp → Prop where
  | eqLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : BStep (.eq a1 a2) (.eq a1' a2)
  | eqRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      BStep (.eq v1 a2) (.eq v1 a2')
  | eq (n1 n2 : Nat) : BStep (.eq (.num n1) (.num n2)) (.bool (decide (n1 = n2)))
  | neqLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : BStep (.neq a1 a2) (.neq a1' a2)
  | neqRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      BStep (.neq v1 a2) (.neq v1 a2')
  | neq (n1 n2 : Nat) : BStep (.neq (.num n1) (.num n2)) (.bool (decide (n1 ≠ n2)))
  | leLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : BStep (.le a1 a2) (.le a1' a2)
  | leRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      BStep (.le v1 a2) (.le v1 a2')
  | le (n1 n2 : Nat) : BStep (.le (.num n1) (.num n2)) (.bool (decide (n1 ≤ n2)))
  | gtLeft (a1 a1' a2 : Aexp) (h : AStep a1 a1') : BStep (.gt a1 a2) (.gt a1' a2)
  | gtRight (v1 a2 a2' : Aexp) (hv : IsAValue v1) (h : AStep a2 a2') :
      BStep (.gt v1 a2) (.gt v1 a2')
  | gt (n1 n2 : Nat) : BStep (.gt (.num n1) (.num n2)) (.bool (decide (n1 > n2)))
  | notStep (b1 b1' : Bexp) (h : BStep b1 b1') : BStep (.not b1) (.not b1')
  | notTrue : BStep (.not (.bool true)) (.bool false)
  | notFalse : BStep (.not (.bool false)) (.bool true)
  | andStep (b1 b1' b2 : Bexp) (h : BStep b1 b1') : BStep (.and b1 b2) (.and b1' b2)
  | andTrueStep (b2 b2' : Bexp) (h : BStep b2 b2') :
      BStep (.and (.bool true) b2) (.and (.bool true) b2')
  | andFalse (b2 : Bexp) : BStep (.and (.bool false) b2) (.bool false)
  | andTrueTrue : BStep (.and (.bool true) (.bool true)) (.bool true)
  | andTrueFalse : BStep (.and (.bool true) (.bool false)) (.bool false)

scoped notation:40 b:41 " ⟶b " b':41 => BStep b b'
```

A boolean example -- the left comparison operand reduces first:

```lean
example :
    (Bexp.le (.plus (.num 1) (.num 1)) (.num 3)) ⟶b (.le (.num 2) (.num 3)) :=
  .leLeft _ _ _ (.plus 1 1)
```

::::quiz
Which of these properties does this small-step semantics for `Slang`
expressions satisfy?  (Yes or No for each.)

  - determinism
  - strong progress (every non-value takes a step)
  - values and normal forms coincide (i.e., there are no "stuck" terms)
  - the step relation is normalizing (i.e., evaluation always terminates)

:::quizSolution
Yes to all four.  Expression evaluation always terminates, so `⟶a` (and `⟶b`) are normalizing.
:::
::::

::::full
Let us make good on the first of those answers.  Both step relations are
_deterministic_: the value guards on the "step the right operand" rules mean
that at most one rule ever applies to a given term.
::::

:::::exercise (rating := 3) (name := "astep_deterministic")
The arithmetic step relation is deterministic.  (Structurally this is the
value-based determinism proof from the toy language, repeated for `+`, `−`,
and `×`; the impossible cross-cases close because a value `num n` cannot step.)

```lean
theorem astep_deterministic : Deterministic AStep := by
  solution!
    intro x y1 y2 h1
    induction h1 generalizing y2 <;> intro h2 <;> cases h2 <;>
      first
        | rfl
        | cases ‹AStep (Aexp.num _) _›
        | (cases ‹IsAValue _›; cases ‹AStep (Aexp.num _) _›)
        | (congr 1 <;> first | rfl | (apply ‹∀ _, AStep _ _ → _ = _› <;> assumption))
```
:::::

:::::exercise (rating := 3) (name := "bstep_deterministic")
The boolean step relation is deterministic too.  The comparison cases (`eq`,
`neq`, `le`, `gt`) reduce their operands with `⟶a`, so they inherit determinism
from `astep_deterministic`; `¬` and the short-circuiting `∧` contribute only
base cases.

```lean
theorem bstep_deterministic : Deterministic BStep := by
  solution!
    intro x y1 y2 h1
    induction h1 generalizing y2 <;> intro h2 <;> cases h2 <;>
      first
        | rfl
        | cases ‹AStep (Aexp.num _) _›
        | (cases ‹IsAValue _›; cases ‹AStep (Aexp.num _) _›)
        | cases ‹BStep (Bexp.bool _) _›
        | (congr 1 <;> first | rfl | (apply astep_deterministic <;> assumption) | (apply ‹∀ _, BStep _ _ → _ = _› <;> assumption))
```
:::::

## Nondeterministic Evaluation

::::full
The relation `⟶a` above bakes in a _left-to-right_ evaluation order: the rule
`plusRight` can fire only once the left operand is already a value (`IsAValue v1`).
But nothing about the _meaning_ of `+` requires that order -- we could just as
well reduce the right operand first, or interleave the two.  Different orders
are exactly what a concurrent or optimizing implementation might choose, so it
is natural to ask whether the choice can affect the final answer.

Let's find out.  We define a second small-step relation, `⟶n`, that is
identical to `⟶a` except that we _drop_ the `IsAValue` side-condition: either
operand may take a step at any time.
::::

:::terse
`⟶n`: like `⟶a`, but with the `IsAValue` guard on the "step the right operand"
rules removed, so the evaluation order is nondeterministic.
:::

```lean
inductive ANStep : Aexp → Aexp → Prop where
  | plusLeft (a1 a1' a2 : Aexp) (h : ANStep a1 a1') :  ANStep (.plus a1 a2) (.plus a1' a2)
  | plusRight (a1 a2 a2' : Aexp) (h : ANStep a2 a2') : ANStep (.plus a1 a2) (.plus a1 a2')
  | plus (n1 n2 : Nat) : ANStep (.plus (.num n1) (.num n2)) (.num (n1 + n2))
  | minusLeft (a1 a1' a2 : Aexp) (h : ANStep a1 a1') : ANStep (.minus a1 a2) (.minus a1' a2)
  | minusRight (a1 a2 a2' : Aexp) (h : ANStep a2 a2') : ANStep (.minus a1 a2) (.minus a1 a2')
  | minus (n1 n2 : Nat) : ANStep (.minus (.num n1) (.num n2)) (.num (n1 - n2))
  | multLeft (a1 a1' a2 : Aexp) (h : ANStep a1 a1') : ANStep (.mult a1 a2) (.mult a1' a2)
  | multRight (a1 a2 a2' : Aexp) (h : ANStep a2 a2') : ANStep (.mult a1 a2) (.mult a1 a2')
  | mult (n1 n2 : Nat) : ANStep (.mult (.num n1) (.num n2)) (.num (n1 * n2))

scoped notation:40 a:41 " ⟶n " a':41 => ANStep a a'
```

Unlike `⟶a`, this relation really is nondeterministic: a single term can step
in two different ways, depending on which operand we choose to advance.

```lean
theorem anstep_not_deterministic : ¬ Deterministic ANStep := by
  intro hd
  have s1 : ANStep (.plus (.plus (.num 1) (.num 1)) (.plus (.num 2) (.num 2)))
      (.plus (.num 2) (.plus (.num 2) (.num 2))) :=
    .plusLeft _ _ _ (.plus 1 1)
  have s2 : ANStep (.plus (.plus (.num 1) (.num 1)) (.plus (.num 2) (.num 2)))
      (.plus (.plus (.num 1) (.num 1)) (.num 4)) :=
    .plusRight _ _ _ (.plus 2 2)
  have heq := hd _ _ _ s1 s2
  simp at heq
```

::::full
Remarkably, this nondeterminism does _not_ affect the final answer.  The key
observation is that a single step never changes the big-step _value_ of an
expression -- whichever operand we advance, `eval` is preserved.
::::

:::::exercise (rating := 2) (name := "anstep_preserves_eval")
Prove that one nondeterministic step leaves the big-step value unchanged.
_Hint:_ induction on the step derivation; each case is immediate from `eval`
and, where present, the induction hypothesis.

```lean
theorem anstep_preserves_eval (a a' : Aexp) (h : a ⟶n a') : a.eval = a'.eval := by
  solution!
    induction h <;> simp only [Aexp.eval, *]
```
:::::

This lifts to any number of steps by a routine induction on the multi-step
derivation:

```lean
theorem multi_anstep_preserves_eval (a a' : Aexp) (h : Multi ANStep a a') : a.eval = a'.eval := by
  induction h with
  | refl x => rfl
  | step x y z h1 _ ih => rw [anstep_preserves_eval x y h1]; exact ih
```

::::full
Finally we can compare the two semantics.  The deterministic relation `⟶a` is
a _special case_ of `⟶n`: every `⟶a` step is also an `⟶n` step (it merely
happens, in addition, to respect the `IsAValue` guard).
::::

```lean
theorem astep_imp_anstep (a a' : Aexp) (h : a ⟶a a') : a ⟶n a' := by
  induction h with
  | plusLeft a1 a1' a2 _ ih => exact .plusLeft a1 a1' a2 ih
  | plusRight v1 a2 a2' _ _ ih => exact .plusRight v1 a2 a2' ih
  | plus n1 n2 => exact .plus n1 n2
  | minusLeft a1 a1' a2 _ ih => exact .minusLeft a1 a1' a2 ih
  | minusRight v1 a2 a2' _ _ ih => exact .minusRight v1 a2 a2' ih
  | minus n1 n2 => exact .minus n1 n2
  | multLeft a1 a1' a2 _ ih => exact .multLeft a1 a1' a2 ih
  | multRight v1 a2 a2' _ _ ih => exact .multRight v1 a2 a2' ih
  | mult n1 n2 => exact .mult n1 n2

theorem multi_astep_imp_anstep (a a' : Aexp) (h : Multi AStep a a') : Multi ANStep a a' := by
  induction h with
  | refl x => exact .refl x
  | step x y z h1 _ ih => exact .step x y z (astep_imp_anstep x y h1) ih
```

:::::exercise (rating := 3) (name := "astep_anstep_agree")
Now put the pieces together: prove that the deterministic and nondeterministic
semantics always compute the _same_ final result.  That is, if `a` fully
reduces to `.num n1` under `⟶a` and to `.num n2` under `⟶n`, then `n1 = n2`.

_Hint:_ both `.num n1` and `.num n2` are reachable by `⟶n` (use
`multi_astep_imp_anstep` for the first), and `⟶n` preserves `eval`.

```lean
theorem astep_anstep_agree (a : Aexp) (n1 n2 : Nat)
    (hd : Multi AStep a (.num n1)) (hn : Multi ANStep a (.num n2)) : n1 = n2 := by
  solution!
    have e1 := multi_anstep_preserves_eval a (.num n1)
      (multi_astep_imp_anstep a (.num n1) hd)
    have e2 := multi_anstep_preserves_eval a (.num n2) hn
    simp only [Aexp.eval] at e1 e2
    lia
```
:::::

::::full
So even though `⟶n` is genuinely nondeterministic, the value it eventually
produces is completely determined -- and it is the same value the deterministic
machine (and the big-step evaluator) computes.  This _confluence to a unique
result_ is exactly the property one wants when reordering or parallelizing the
evaluation of pure expressions.
::::

## A Small-Step Stack Machine

Our last example is a small-step semantics for a _stack machine_ that evaluates
arithmetic expressions. The machine's instructions push a constant or combine the
top two stack entries. The machine's behavior should match the big-step `Aexp.eval`
function defined earlier.

A _program_ is a list of instructions, and the _stack_ is a list of numbers.

```lean
inductive SInstr where
  | push (n : Nat)
  | plus
  | minus
  | mult

abbrev Stack := List Nat
abbrev Prog := List SInstr
```

The compiler emits code in the postfix order sketched above:

```lean
def compile : Aexp → Prog
  | .num n => [.push n]
  | .plus a1 a2 => compile a1 ++ compile a2 ++ [.plus]
  | .minus a1 a2 => compile a1 ++ compile a2 ++ [.minus]
  | .mult a1 a2 => compile a1 ++ compile a2 ++ [.mult]

example : compile (.plus (.num 2) (.num 3)) = [.push 2, .push 3, .plus] := rfl
```

Now the small-step machine itself: each step consumes the next instruction and
updates the stack.

```lean
inductive StackStep : Prog × Stack → Prog × Stack → Prop where
  | push (p : Prog) (stk : Stack) (n : Nat) : StackStep (.push n :: p, stk) (p, n :: stk)
  | plus (p : Prog) (stk : Stack) (n m : Nat) :
      StackStep (.plus :: p, n :: m :: stk) (p, (m + n) :: stk)
  | minus (p : Prog) (stk : Stack) (n m : Nat) :
      StackStep (.minus :: p, n :: m :: stk) (p, (m - n) :: stk)
  | mult (p : Prog) (stk : Stack) (n m : Nat) :
      StackStep (.mult :: p, n :: m :: stk) (p, (m * n) :: stk)
```

The machine is deterministic:

```lean
theorem stack_step_deterministic : Deterministic StackStep := by
  intro x y1 y2 h1 h2
  cases h1 <;> cases h2 <;> rfl
```

:::::exercise (rating := 3) (name := "compiler_is_correct") (level := Advanced)
Prove the compiler correct: running the compiled program from the empty stack
reduces, in some number of steps, to a stack holding exactly the value of the
expression.

_Hint:_ this will not go through by a direct induction -- the induction
hypothesis is too weak.  Prove a more general statement first, about running
`compile a` followed by _any_ leftover program `p`, starting from _any_ stack
`stk`.  (Reassociating the `++`s with `List.append_assoc`, and chaining steps
with `multi_trans`/`multi_single`, are the moves you need.)

```lean
theorem compiler_is_correct (a : Aexp) :
    Multi StackStep (compile a, []) ([], [a.eval]) := by
  solution!
    have gen : ∀ (a : Aexp) (p : Prog) (stk : Stack),
        Multi StackStep (compile a ++ p, stk) (p, a.eval :: stk) := by
      intro a
      induction a with
      | num n =>
          intro p stk
          simp only [compile, Aexp.eval]
          exact multi_single _ _ _ (StackStep.push p stk n)
      | plus a1 a2 ih1 ih2 =>
          intro p stk
          simp only [compile, Aexp.eval, List.append_assoc]
          exact multi_trans _ _ _ _ (ih1 _ stk)
            (multi_trans _ _ _ _ (ih2 _ (a1.eval :: stk))
              (multi_single _ _ _ (StackStep.plus p stk a2.eval a1.eval)))
      | minus a1 a2 ih1 ih2 =>
          intro p stk
          simp only [compile, Aexp.eval, List.append_assoc]
          exact multi_trans _ _ _ _ (ih1 _ stk)
            (multi_trans _ _ _ _ (ih2 _ (a1.eval :: stk))
              (multi_single _ _ _ (StackStep.minus p stk a2.eval a1.eval)))
      | mult a1 a2 ih1 ih2 =>
          intro p stk
          simp only [compile, Aexp.eval, List.append_assoc]
          exact multi_trans _ _ _ _ (ih1 _ stk)
            (multi_trans _ _ _ _ (ih2 _ (a1.eval :: stk))
              (multi_single _ _ _ (StackStep.mult p stk a2.eval a1.eval)))
    have hfin := gen a [] []
    simp only [List.append_nil] at hfin
    exact hfin
```
:::::

```lean
end Slang
```
