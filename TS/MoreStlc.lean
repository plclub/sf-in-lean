import SFLMeta
import TS.StlcProp
import LF.CustomTactics
open Verso.Genre Manual
open SFLMeta


#doc (Manual) "MoreStlc: More on the Simply Typed Lambda-Calculus" =>
%%%
tag := "MoreStlc"
htmlSplit := .never
file := some "MoreStlc"
%%%

:::dev PotentialImprovement
Not enough quizzes??
:::

# Simple Extensions to STLC

The simply typed lambda-calculus has a rich enough structure to make
its theoretical properties interesting, but it is not much of a
programming language!

In this chapter, we begin to close the gap with real-world languages by
introducing a number of familiar features that have straightforward
treatments at the level of typing.

## Numbers

::::full
As we saw in the `StlcExtended` exercises at the end of the {ref "StlcProp"}[StlcProp]
chapter, adding types, constants, and primitive operations for
natural numbers is easy - basically just a matter of combining
the {ref "Types"}[Types] and {ref "Stlc"}[Stlc] chapters.  Adding more realistic
numeric types like machine integers and floats is also
straightforward, though of course the specifications of the
numeric primitives become more fiddly.
::::

::::terse
Adding types, constants, and primitive operations for
natural numbers is easy (as we saw in the `StlcExtended` exercises).
::::

::::full
When writing a complex expression, it is useful to be able
to give names to some of its subexpressions to avoid repetition
and increase readability.  Most languages provide one or more ways
of doing this.  In OCaml and Haskell, for example, we can write `let x = t₁ in t₂` to mean
 "reduce the expression `t₁` to a value and
bind the name `x` to this value while reducing `t₂`."

Our `let`-binder follows OCaml in choosing a standard
_call-by-value_ evaluation order, where the `let`-bound term must
be fully reduced before reduction of the `let`-body can begin.
The typing rule `let` tells us that the type of a `let` can be
calculated by calculating the type of the `let`-bound term,
extending the context with a binding with this type, and in this
enriched context calculating the type of the body (which is then
the type of the whole `let` expression).

At this point in the book, it's probably easier simply to look at
the rules defining this new feature than to wade through a lot of
English text conveying the same information.  Here they are:
::::


::::terse
A more interesting extension... let-bindings.

When writing a complex expression, it is often useful to give
names to some of its subexpressions: this avoids repetition and
often increases readability.
::::

Syntax:

```display
  t ::=                   Terms
      | ...                 (other terms same as before)
      | let x = t₁ in t₂    let-binding
```

Reduction:
```display
                                 t₁ ⟶ t₁'
                     -------------------------------------        (let₁)
                     let x = t₁ in t₂ ⟶ let x = t₁' in t₂

                        ---------------------------------         (letValue)
                        let x = v₁ in t₂ ⟶ [x := v₁] t₂
```

Typing:

```display
             Γ ⊢ t₁ ⦂ τ₁      x ↦ τ₁ ; Γ ⊢ t₂ ⦂ τ₂
             -------------------------------------------      (let)
                     Γ ⊢ let x = t₁ in t₂ ⦂ τ₂
```

## Pairs

::::full
Our functional programming examples in Lean have made
frequent use of _pairs_ of values.  The type of such a pair is
called a _product type_.

The formalization of pairs is almost too simple to be worth
discussing.  However, let's look briefly at the various parts of
the definition to emphasize the common pattern.
::::

In Lean, there are two ways of extracting the components of a pair:
_pattern matching_ and the projection operators `fst` and `snd`.
Just for fun, let's do our pairs the latter way.  For
example, here's how we'd write a function that takes a pair of
numbers and returns the pair of their sum and difference:

```display
       λx : Nat × Nat.
          let sum = fst x + snd x in
          let diff = fst x - snd x in
          (sum, diff)
```

::::full
Adding pairs to the simply typed lambda-calculus, then, involves
adding two new forms of term - pairing, written `(t₁,t₂)`, and
projection, written `fst t` for the first projection from `t` and
`snd t` for the second projection - plus one new type constructor,
`τ₁ × τ₂`, called the _product_ of `τ₁` and `τ₂`.
::::

Syntax:

```display
       t ::=                Terms
           | ...
           | (t₁, t₂)         pair
           | fst t            first projection
           | snd t            second projection

       v ::=                Values
           | ...
           | (v₁, v₂)         pair value

       τ ::=                Types
           | ...
           | τ₁ × τ₂          product type
```

::::full
For reduction, we need several new rules specifying how pairs and projection behave.
::::

::::terse
Reduction...
::::

```display
                              t₁ ⟶ t₁'
                         --------------------                        (pair₁)
                         (t₁,t₂) ⟶ (t₁',t₂)

                              t₂ ⟶ t₂'
                         --------------------                        (pair₂)
                         (v₁,t₂) ⟶ (v₁,t₂')

                               t ⟶ t'
                           ------------------                        (fst₁)
                           fst t ⟶ fst t'

                          ------------------                       (fstPair)
                           fst (v₁,v₂) ⟶ v₁

                               t ⟶ t'
                           ------------------                      (snd₁)
                           snd t ⟶ snd t'

                          ------------------                       (sndPair)
                          snd (v₁,v₂) ⟶ v₂
```

::::full
Rules `fstPair` and `sndPair` say that, when a fully
reduced pair meets a first or second projection, the result is
the appropriate component.  The congruence rules `fst₁` and
`snd₁` allow reduction to proceed under projections, when the
term being projected from has not yet been fully reduced.
`pair₁` and `pair₂` reduce the parts of pairs: first the
left part, and then - when a value appears on the left - the right
part.  The ordering arising from the use of the metavariables `v`
and `t` in these rules enforces a left-to-right evaluation
strategy for pairs.  (Note the implicit convention that
metavariables like `v` and `v₁` can only denote values.)  We've
also added a clause to the definition of values, above, specifying
that `(v₁,v₂)` is a value.  The fact that the components of a pair
value must themselves be values ensures that a pair passed as an
argument to a function will be fully reduced before the function
body starts executing.
::::

::::full
The typing rules for pairs and projections are straightforward.
::::

::::terse
Typing:
::::


```display
                     Γ ⊢ t₁ ⦂ τ₁     Γ t₂ ⦂ τ₂
                    ------------------------------              (pair)
                      Γ ⊢(t₁, t₂) ⦂ τ₁ × τ₂

                           Γ ⊢ t ⦂ τ₁ × τ₂
                        -----------------------                  (fst)
                            Γ ⊢ fst t ⦂ τ₁

                            Γ ⊢ t ⦂ τ₁ × τ₂
                        -----------------------                   (snd)
                             Γ ⊢ snd t ⦂ τ₂
```

::::full
`pair` says that `(t₁, t₂)` has type `τ₁ × τ₂` if `t₁` has
type `τ₁` and `t₂` has type `τ₂`.  Conversely, `fst` and `snd`
tell us that, if `t` has a product type `τ₁ × τ₂` (i.e., if it
will reduce to a pair), then the types of the projections from
this pair are `τ₁` and `τ₂`.
::::

## Unit

Another handy base type is the singleton type `Unit`.

::::full
It has a single element - the term constant `unit` (with a small `u`) -
and a typing rule making `unit` an element of `Unit`.  We
also add `unit` to the set of possible values - indeed, `unit` is
the _only_ possible result of reducing an expression of type `Unit`.
::::


Syntax:

```display
       t ::=                Terms
           | ...               (other terms same as before)
           | unit              unit

       v ::=                Values
           | ...
           | unit              unit value

       τ ::=                Types
           | ...
           | Unit              unit type
```

Typing:

```display
                         ----------------                       (unit)
                         Γ ⊢ unit ⦂ Unit
```

::::full
It may seem a little strange to bother defining a type that
has just one element -- after all, wouldn't every computation
living in such a type be trivial?

This is a fair question, and indeed in the STLC the `Unit` type is
not especially critical (though we'll see two uses for it below).
Where `Unit` really comes in handy is in richer languages with
_side effects_ -- e.g., assignment statements that mutate
variables or pointers, exceptions and other sorts of nonlocal
control structures, etc.  In such languages, it is convenient to
have a type for the (trivial) result of an expression that is
evaluated only for its effect.
::::

::::quiz
Is `unit` the only term of type `Unit`?

    (A) Yes

    (B) No
::::

::::quizSolution
No! For instance `λx:Unit. x` unit is also a _term_ of type `Unit`.
::::


## Sums

Many programs need to deal with values that can take two distinct
forms.  For example, we might identify students in a university
database using _either_ their name _or_ their id number. A search
function might return _either_ a matching value _or_ an error code.

These are specific examples of a binary _sum type_ (sometimes called
a _disjoint union_), which describes a set of values drawn from
one of two given types, e.g.:

```display
       Nat + Bool
```

::::terse
    We create elements of these types by tagging elements of the
    component types, telling on which side of the sum we are putting
    them. E.g.,

```display
   inl 42   ⦂ Nat + Bool
   inr true ⦂ Nat + Bool
```
::::

::::full
We create elements of these types by _tagging_ elements of
the component types.  For example, if `n` is a `Nat` then `inl n`
is an element of `Nat + Bool`; similarly, if `b` is a `Bool` then
`inr b` is a `Nat + Bool`.  The names of the tags `inl` and `inr`
arise from thinking of them as functions

```display
       inl ⦂ Nat  → Nat + Bool
       inr ⦂ Bool → Nat + Bool
```

that "inject" elements of `Nat` or `Bool` into the left and right
components of the sum type `Nat + Bool`.  (But note that we don't
actually treat them as functions in the way we formalize them:
`inl` and `inr` are keywords, and `inl t` and `inr t` are primitive
syntactic forms, not function applications.)
::::

In general, the elements of a type `τ₁ + τ₂` consist of the
elements of `τ₁` tagged with the token `inl`, plus the elements of
`τ₂` tagged with `inr`.

(As we've seen in Lean programming, one important use of sums is
signaling errors:

```display
      div ⦂ Nat → Nat → (Nat + Unit)
      div =
        λx:Nat. λy:Nat,
          if iszero y then
            inr unit
          else
            inl ...
```

::::full
The type `Nat + Unit` above is in fact isomorphic to {lean}`Option Nat` in Lean -
i.e., it's easy to write functions that translate back and forth.

To _use_ elements of sum types, we introduce a `case`
construct (a very simplified form of Lean's `match`) to destruct
them. For example, the following procedure converts a `Nat + Bool` into a `Nat`:
::::

::::terse
Values of sum type are "destructed" by case analysis:
::::

```display
    getNat ⦂ Nat+Bool → Nat
    getNat =
      λx:Nat+Bool,
        case x of
          inl n => n
        | inr b => if b then 1 else 0
```

More formally...

Syntax:

```display
       t ::=                Terms
           | ...               (other terms same as before)
           | inl τ₂ t₁         tagging (left)
           | inr τ₁ t₂         tagging (right)
           | case t of         case analysis
               inl x₁ => t₁
             | inr x₂ => t₂

       v ::=                Values
           | ...
           | inl τ₂ v₁         tagged value (left)
           | inr τ₁ v₂         tagged value (right)

       τ ::=                Types
           | ...
           | τ₁ + τ₂           sum type
```

Reduction:

```display
                               t₁ ⟶ t₁'
                        ------------------------                       (inl)
                        inl τ₂ t₁ ⟶ inl τ₂ t₁'

                               t₂ ⟶ t₂'
                        ------------------------                       (inr)
                        inr τ₁ t₂ ⟶ inr τ₁ t₂'

                               t ⟶ t'
               -------------------------------------------            (case)
                case t of inl x₁ => t₁ | inr x₂ => t₂ ⟶
               case t' of inl x₁ => t₁ | inr x₂ => t₂

            -----------------------------------------------        (caseInl)
            case (inl τ₂ v₁) of inl x₁ => t₁ | inr x₂ => t₂
                           ⟶  [x₁ := v₁]t₁

            -----------------------------------------------        (caseInr)
            case (inr τ₁ v₂) of inl x₁ => t₁ | inr x₂ => t₂
                           ⟶  [x₂ := v₂]t₂
```

Typing:

```display
                            Γ ⊢ t₁ ⦂ τ₁
                   ----------------------------                      (inl)
                       Γ ⊢ inl τ₂ t₁ ⦂ τ₁ + τ₂


                          Γ ⊢ t₂ ⦂ τ₂
                   ---------------------------                       (inr)
                     Γ ⊢ inr τ₁ t₂ ⦂ τ₁ + τ₂


                        Γ ⊢ t ⦂ τ₁ + τ₂
                     x₁ ↦ τ₁; Γ ⊢ t₁ ⦂ τ₃
                     x₂ ↦ τ₂; Γ ⊢ t₂ ⦂ τ₃
         ----------------------------------------------------        (case)
             Γ ⊢ case t of inl x₁ => t₁ | inr x₂ => t₂ ⦂ τ₃
```

We use the type annotations on `inl` and `inr` to make the typing
relation deterministic (each term has at most one type), as we
did for functions.

::::full
Without this extra information, the typing rule `inl`, for
example, would have to say that, once we have shown that `t₁` is
an element of type `τ₁`, we can derive that `inl t₁` is an element
of `τ₁ + τ₂` for _any_ type `τ₂`.  For example, we could derive both
`inl 5 : Nat + Nat`and `inl 5 : Nat + Bool` (and infinitely many other types).
This peculiarity (technically, a failure of uniqueness of types) would mean t
hat we cannot build a typechecking algorithm simply by "reading the rules from bottom to
top" as we could for all the other features seen so far.

There are various ways to deal with this difficulty.  One simple
one -- which we've adopted here -- forces the programmer to
explicitly annotate the "other side" of a sum type when performing
an injection.  This is a bit heavy for programmers (so real
languages adopt other solutions), but it is easy to understand and formalize.
::::

::::dev PotentialImprovement
AAA: The explanation above is not entirely accurate. The
exact same problem appears with functions. Perhaps it would be
better to remove this explanation and just say that we want to make
the typing rules simpler.  BCP: Don't see in what way this is
inaccurate...
::::

::::quiz
What does the following term step to (in one step)?

```display
      let f = λx : Nat + Bool.
         case x of
           inl n => n + 3
           | inr b => 0 in
      f (inl Bool 4)
```

```display
    (A)  (λx : Nat + Bool.
            case x of
              inl n => n + 3
              | inr b => 0
         ) (inl Bool 4)

    (B) 7

    (C)  case inl Bool 4 of
           inl n => n + 3
         | inr b => 0

    (D) f (inl Bool 4)
```
::::


::::quiz
What about this one?

```display
  (λx : Nat + Bool.
     case x of
     inl n => n + 3
     | inr b => 0
  ) (inl Bool 4)
```

```display
   (A)  7

   (B)  case inl Bool 4 of
          inl n => n + 3
        | inr b => 0

   (C)  4 + 3
```
::::

::::quiz
What about this one?

```display
       case inl Bool 4 of
         inl n => n + 3
         | inr b => 0

   (A)  4 + 3

   (B)  7

   (C)  0
```

::::


## Lists

::::full
The typing features we have seen can be classified into
_base types_ like `Bool`, and _type constructors_ like `→` and
`×` that build new types from old ones.  Another useful type
constructor is `List`.  For every type `τ`, the type `List τ`
describes finite-length lists whose elements are drawn from `τ`.

In principle, we could encode lists using pairs, sums, unit, and
_recursive_ types. But giving semantics to recursive types is
non-trivial. Instead, we'll just discuss the special case of lists
directly.

Below we give the syntax, semantics, and typing rules for lists.
Except for the fact that explicit type annotations are mandatory
on `nil` and cannot appear on `cons`, these lists are essentially
identical to those we built in Rocq.  We use `case`, rather than
`head` and `tail` operators, to destruct lists, to avoid dealing
with questions like "what is the `head` of the ∅ list?"

For example, here is a function that calculates the sum of
the first two elements of a list of numbers:

      λ x:List Nat.
      case x of
        nil   => 0
        | a :: x' => case x' of
                     nil    => a
                     | b :: x'' => a + b
::::


Syntax:

```display
       t ::=                Terms
           | ...
           | nil τ             ∅ list
           | t₁ :: t₂          cons
           | case t₁ of        case analysis
               nil      => t₂
               | xh::xt => t₃

       v ::=                Values
           | ...
           | nil τ             nil value
           | v₁ :: v₂          cons value

       τ ::=                Types
           | ...
           | List τ            list of τs
```

Reduction:

```display
                                t₁ ⟶ t₁'
                       --------------------------                    (cons₁)
                         t₁ :: t₂ ⟶ t₁' :: t₂

                                t₂ ⟶ t₂'
                       --------------------------                    (cons₂)
                         v₁ :: t₂ ⟶ v₁ :: t₂'

                              t₁ ⟶ t₁'
                -------------------------------------------         (listCase₁)
                 (case t₁ of nil => t₂ | xh :: xt => t₃) ⟶
                (case t₁' of nil => t₂ | xh :: xt => t₃)

               ------------------------------------------          (listCaseNil)
               (case nil τ₁ of nil => t₂ | xh :: xt => t₃)
                                ⟶ t₂

              -------------------------------------------         (listCaseCons)
              (case (vh :: vt) of nil => t₂ | xh :: xt => t₃)
                          ⟶ [xh:=vh][xt:=vt] t₃
```

 Typing:

```display
                        ----------------------------                    (nil)
                        Γ ⊢ nil τ₁ ⦂ List τ₁

                     Γ ⊢ t₁ ⦂ τ₁      Γ ⊢ t₂ ⦂ List τ₁
            -------------------------------------------------           (cons)
                         Γ ⊢ t₁ :: t₂ ⦂ List τ₁

                        Γ ⊢ t₁ ⦂ List τ₁
                        Γ ⊢ t₂ ⦂ τ₂
                  (xh ↦ τ₁; xt ↦ List τ₁; Γ) ⊢ t₃ ⦂ τ₂
          ----------------------------------------------------         (listCase)
             Γ ⊢ (case t₁ of nil => t₂ | xh :: xt => t₃) ⦂ τ₂
```


## General Recursion

Another facility found in most programming languages (including Lean)
is the ability to define recursive functions.  For example,
we would like to be able to define and use the factorial function
like this:

```display
      let fact = λx:Nat.
                   if x=0 then 1 else x * (fact (pred x))) in
      fact 3.
```

Note that the right-hand side of this binder mentions `fact`, the
variable being bound - something that is not allowed according
to the way we defined `let` above.

::::full
(The body of a `let` is typechecked in the same context as the
`let` itself, which means that the recursive occurrence of `fact` in the
body will not have a type in the context when it is looked up by the
`var` rule.)
::::

::::full
Changing the `let` rule to handle "recursive definitions"
like this is possible, but it requires some extra effort -- e.g.,
passing around an extra "environment" of recursive function
definitions in the definition of the `step` relation.  We're going
to take a simpler path here.
::::

::::terse
Extending our formalization of `let`s to handle "recursive definitions"
would require non-trivial effort.
::::


::::dev PotentialImprovement
The explanations in this section are not clear enough!
::::

Here is another way of presenting recursive functions that is
a bit more verbose but equally powerful and much more straightforward
to formalize: instead of writing recursive definitions, we will define
a _fixed-point operator_ called `fix` that performs the "unfolding"
of the recursive definition in the right-hand side as needed, during
reduction.

For example, instead of
```display
      fact = λax:Nat.
                if x=0 then 1 else x * (fact (pred x)))
```

we will write:

```
      fact =
          fix
            (λaf:Nat → Nat.
               λx:Nat.
                  if x=0 then 1 else x * (f (pred x)))
```

::::full
We can derive the latter from the former as follows:

- In the right-hand side of the definition of `fact`, replace
  recursive references to `fact` by a fresh variable `f`.

- Add an abstraction binding `f` at the front, with an
  appropriate type annotation.  (Since we are using `f` in place
  of `fact`, which had type `Nat→Nat`, we should require `f`
  to have the same type.)  The new abstraction has type
  `(Nat→Nat) → (Nat→Nat)`.

- Apply `fix` to this abstraction.  This application has
  type `Nat→Nat`.

- Use all of this as the right-hand side of an ordinary
  `let`-binding for `fact`.
::::

::::full
For the mathematically inclined,
the intuition here is that the higher-order function `f`
passed to `fix` is a _generator_ for the `fact` function: if `f`
is applied to a function that "approximates" the desired behavior
of `fact` up to some number `n` (that is, a function that returns
correct results on inputs less than or equal to `n` but we don't
care what it does on inputs greater than `n`), then `f` returns a
slightly better approximation to `fact` -- a function that returns
correct results for inputs up to `n+1`.  Applying `fix` to this
generator returns its _fixed point_, which is a function that
gives the desired behavior for all inputs `n`.

(The term "fixed point" is used here in exactly the same sense as
in ordinary mathematics, where a fixed point of a function `f` is
an input `x` such that `f(x) = x`.  Here, a fixed point of a
function `F` of type `(Nat→Nat)→(Nat→Nat)` is a function `f` of
type `Nat→Nat` such that `F f` behaves the same as `f`.)
::::

Syntax:
```display
       t ::=                Terms
           | ...
           | fix t₁            fixed-point operator
```

Reduction:
```display
                                t₁ ⟶ t₁'
                            ------------------                   (fix₁)
                            fix t₁ ⟶ fix t₁'

               --------------------------------------------      (fixAbs)
               fix (λxf:τ₁.t₁) ⟶ [xf:=fix (λxf:τ₁.t₁)] t₁
```

Typing:

```display
                           Γ ⊢ t₁ ⦂ τ₁ → τ₁
                           ------------------                    (fix)
                           Γ ⊢ fix t₁ ⦂ τ₁
```

::::dev PotentialImprovement
CH: Is it worth mentioning that in `fixAbs` we substitute a
non-value for a variable, but that's still okay? It may be good to give an
informal explanation. Formally, one thing that saves the day is that in the
substitution lemma we don't actually require `v` to be a value, which goes
against the informal convention used in this file (e.g., we can't omit the
value requirement in letValue without breaking determinism).
::::

::::dev PotentialImprovement
Robert Rand: This isn't very clear if the students haven't done
the nat exercises in the previous chapter. (Which is particularly likely
if stlc and morestlc are subsequent lectures in the same week.) Also,
removing the explicit annotations on the step relation might make this
more readible. (Also, doesn't fit on a slide.)  BCP 23: Yes, this is a
bit drinking from the firehose / lecturing with a firehose. Not sure
what to replace it with, though. (And breaking it across slides in the
terse version seems worse than scrolling in this -- rare --
instance.))
::::

Let's see how `fixAbs` works by reducing `fact 3 = fix F 3`, where

```display
    F = (λf. λx. if x=0 then 1 else x * (f (pred x)))
```

(type annotations are omitted for brevity).

```display
    fix F 3

⟶ fixAbs + app₁

    (λx. if x=0 then 1 else x * (fix F (pred x))) 3

⟶ appAbs

    if 3=0 then 1 else 3 * (fix F (pred 3))

⟶ if0Nonzero

    3 * (fix F (pred 3))

⟶ fixAbs + mult₂ + app₁

    3 * ((λx. if x=0 then 1 else x * (fix F (pred x))) (pred 3))

⟶ predNat + mult₂ + app₂

    3 * ((λx. if x=0 then 1 else x * (fix F (pred x))) 2)

⟶ appAbs + mult₂

    3 * (if 2=0 then 1 else 2 * (fix F (pred 2)))

⟶ if0Nonzero + mult₂

    3 * (2 * (fix F (pred 2)))

⟶ fixAbs + 2 × mult₂ + app₁

    3 * (2 * ((λx. if x=0 then 1 else x * (fix F (pred x))) (pred 2)))

⟶ predNat + 2 x mult₂ + app₂

    3 * (2 * ((λx. if x=0 then 1 else x * (fix F (pred x))) 1))

⟶ appAbs + 2 x mult₂

    3 * (2 * (if 1=0 then 1 else 1 * (fix F (pred 1))))

⟶ if0Nonzero + 2 x mult₂

    3 * (2 * (1 * (fix F (pred 1))))

⟶ fixAbs + 3 x mult₂ + app₁

    3 * (2 * (1 * ((λx. if x=0 then 1 else x * (fix F (pred x))) (pred 1))))

⟶ predNat + 3 × mult₂ + app₂

    3 * (2 * (1 * ((λx. if x=0 then 1 else x * (fix F (pred x))) 0)))

⟶ appAbs + 3 × mult₂

    3 * (2 * (1 * (if 0=0 then 1 else 0 * (fix F (pred 0)))))

⟶ if0Zero + 3 x mult₂

    3 * (2 * (1 * 1))

⟶ multNats + 2 x mult₂

    3 * (2 * 1)

⟶ multNats + mult₂

    3 * 2

⟶ multNats

    6
```


The simply typed lambda-calculus with fixed points is a famous and
extensively studied system. It is often called _PCF_ because it is a
simple language of "partial computable functions".

::::terse
One important point to note is that, unlike
definitions in Lean, there is nothing to prevent functions defined
using `fix` from diverging.
::::

:::dev PotentialImprovement
It might be useful to say more, here, about why it makes
sense to formalize a nonterminating language in a terminating one.
Remind them that we did the same with Imp.
:::

:::quiz
Is this a well-typed Stlc term? What does it evaluate to?
```display
        fix (λf: Nat→Nat. λx:Nat. f x) 0

   (A) no

   (B) yes, diverges

   (C) yes, [42]

   (D) yes, [0]
```
:::

:::quiz
Which of the following are (intuitively) true for Stlc + fixpoints.

(A) deterministic

(B) progress

(C) preservation

(D) normalizing (i.e. every well-typed term reduces to a normal form)
:::

:::::full

::::exercise (rating := 1) (name := "halve_fix") (optional := true)

Translate this informal recursive definition into one using `fix`:
```display
      halve =
        λx:Nat.
           if x=0 then 0
           else if (pred x)=0 then 0
           else 1 + (halve (pred (pred x)))
```

:::solution
```display
      halve =
          fix
            (λf:Nat→Nat.
               λx:Nat.
                  if x=0 then 0
                  else if (pred x)=0 then 0
                  else 1 + (f (pred (pred x))))
```
:::
::::

::::exercise (rating := 1) (name := "fact_steps") (optional := true)
Write down the sequence of steps that the term `fact 1` goes
through to reduce to a normal form (assuming the usual reduction
rules for arithmetic operations.

:::solution
```display
        fact 1
      = fix (λf:Nat→Nat. λx:Nat. if x=0 then 1 else x * (f (pred x))) 1
    ⟶ (λx: Nat, if x = 0 then 1 else x * (fact (pred x))) 1
    ⟶ if 1 = 0 then 1 else 1 * (fact (pred 1))
    ⟶ 1 * (fact (pred 1))
    ⟶ 1 * ((λx:Nat. if x=0 then 1 else x * (fact (pred x))) (pred 1))
    ⟶ 1 * ((λx:Nat. if x=0 then 1 else x * (fact (pred x))) 0)
    ⟶ 1 * (if 0=0 then 1 else 0 * (fact (pred 0)))
    ⟶ 1 * 1
    ⟶ 1
```
Also see the solution to exercise `fact_example` below.
:::
::::

The ability to form the fixed point of a function of type `τ→τ`
for any `τ` has some surprising consequences.  In particular, it
implies that _every_ type is inhabited by some term.  To see this,
observe that, for every type `τ`, we can define the term:

```display
    fix (λx:τ,x)
```

By `fix`  and `abs`, this term has type `τ`.  By `fixAbs`
it reduces to itself, over and over again.  Thus it is a
_diverging element_ of `τ`.

More usefully, here's an example using `fix` to define a
two-argument recursive function:
```display
    equal =
      fix
        (\eq:Nat→Nat→Bool.
           \m:Nat. \n:Nat.
             if m=0 then iszero n
             else if n=0 then false
             else eq (pred m) (pred n))
```

And finally, here is an example where `fix` is used to define a
_pair_ of recursive functions (illustrating the fact that the type
`τ₁` in the rule `fix` need not be a function type):

```display
    let evenodd =
         fix
           (\eo: ((Nat → Nat) * (Nat → Nat)).
              (\n:Nat. if0 n then 1 else (snd eo (pred n)),
               \n:Nat. if0 n then 0 else (fst eo (pred n)))) in
    let even = fst evenodd in
    let odd  = snd evenodd in
    (even 3, even 4)}
```

:::::

# Records

:::dev PotentialImprovement
Needs a bit more text too.  And tersification.
:::

::::full
As a final example of a basic extension of the STLC, let's look
briefly at how to define _records_ and their types.  Intuitively,
records can be obtained from pairs by two straightforward
generalizations: they are n-ary (rather than just binary) and
their fields are accessed by _label_ (rather than position).
::::

::::terse
As a final example, records can be presented as a
generalization of pairs:
    - they are n-ary (rather than binary);
    - they are accessed by _label_ (rather than position).
::::
:::dev PotentialImprovement
Too terse?
:::

Syntax:

```display
       t ::=                          Terms
           | ...
           | {i₁=t₁, ..., in=tn}        record
           | t.i                        projection

       v ::=                          Values
           | ...
           | {i₁=v₁, ..., in=vn}         record value

       τ ::=                          Types
           | ...
           | {i₁:τ₁, ..., in:τn}         record type
```

::::full
The generalization from products should be pretty obvious.  But
it's worth noticing the ways in which what we've actually written is
even _more_ informal than the informal syntax we've used in previous
sections and chapters: we've used "`...`" in several places to mean "any number of these,"
and we've omitted explicit mention of the usual
side condition that the labels of a record should not contain any repetitions.
::::

::::terse
Note that this is a quite informal definition compared to
previous ones:

- it uses "`...`" in the syntax for records
- it omits a usual side condition that the labels of a record should
  not contain repetitions.
::::

Reduction:

```display
                              ti ⟶ ti'
                 ------------------------------------                  (rcd)
                     {i₁=v₁, ..., im=vm, in=ti , ...}
                 ⟶ {i₁=v₁, ..., im=vm, in=ti', ...}

                              t ⟶ t'
                            --------------                           (proj₁)
                            t.i ⟶ t'.i

                      -------------------------                    (projRcd)
                      {..., i=vi, ...}.i ⟶ vi
```


::::full
Again, these rules are a bit informal.  For example, the first rule
is intended to be read "if `ti` is the leftmost field that is not a
value and if `ti` steps to `ti'`, then the whole record steps..."
In the last rule, the intention is that there should be only one
field called `i`, and that all the other fields must contain values.
::::

::::terse
- In the first rule, `ti` must be the leftmost field that is not a value;
- In the last rule, there should be only one field called `i`,
  and all the other fields must contain values.
::::


The typing rules are also simple:

```display
               Γ ⊢ t₁ ⦂ τ₁     ...     Γ ⊢ tn ⦂ Tn
          -----------------------------------------------------        (rcd)
          Γ ⊢ {i₁=t₁, ..., in=tn} ⦂ {i₁:τ₁, ..., in:Tn}


                      Γ ⊢ t ⦂ {..., i:Ti, ...}
                    ---------------------------------                  (proj)
                          Γ ⊢ t.i ⦂ Ti
```

::::full
There are several ways to approach formalizing the above definitions.

- We can directly formalize the syntactic forms and inference
  rules, staying as close as possible to the form we've given
  them above.  This is conceptually straightforward, and it's
  probably what we'd want to do if we were building a real
  compiler (in particular, it will allow us to print error
  messages in the form that programmers will find easy to
  understand).  But the formal versions of the rules will not be
  very pretty or easy to work with, because all the `...`s above
  will have to be replaced with explicit quantifications or
  comprehensions.  For this reason, records are not included in
  the extended exercise at the end of this chapter.  (It is
  still useful to discuss them informally here because they will
  help motivate the addition of subtyping to the type system
  when we get to the Sub chapter.)

- Alternatively, we could look for a smoother way of presenting
  records -- for example, a binary presentation with one
  constructor for the ∅ record and another constructor for
  adding a single field to an existing record, instead of a
  single monolithic constructor that builds a whole record at
  once.  This is the right way to go if we are primarily
  interested in studying the metatheory of the calculi with
  records, since it leads to clean and elegant definitions and
  proofs.

- Finally, if we like, we can avoid formalizing records
  altogether, by stipulating that record notations are just
  informal shorthands for more complex expressions involving
  pairs and product types.  We sketch this approach in the next
  section.
::::

::::terse
Formalizing all this would take some work.
::::

::::dev "Daniel Sainati (@dsainati1)" PotentialImprovement
If we make a Records chapter, come back here and add foreward links
::::

::::full
Let's see how records can be encoded using just pairs and
`unit`.  (This clever encoding, as well as the observation that it
also extends to systems with subtyping, is due to Luca Cardelli.)

First, observe that we can encode arbitrary-size _tuples_ using
nested pairs and the `unit` value.  To avoid overloading the pair
notation `(t₁,t₂)`, we'll use curly braces without labels to write
down tuples, so `{}` is the ∅ tuple, `{5}` is a singleton
tuple, `{5,6}]`is a 2-tuple (morally the same as a pair),
`{5,6,7}` is a triple, etc.

```display
      {}                 ⟶  unit
      {t₁, t₂, ..., tn}  ⟶  (t₁, trest)
                                where {t₂, ..., tn} ⟶ trest
```

Similarly, we can encode tuple types using nested product types:

```display
      {}                 ⟶  Unit
      {τ₁, τ₂, ..., Tn}  ⟶  τ₁ * TRest
                                where {τ₂, ..., τn} ⟶ τn
```
The operation of projecting a field from a tuple can be encoded
using a sequence of second projections followed by a first
projection:

```display
      t.0        ⟶  fst t
      t.(n+1)    ⟶  (snd t).n
```

Next, suppose that there is some total ordering on record labels,
so that we can associate each label with a unique natural number.
This number is called the _position_ of the label.  For example,
we might assign positions like this:

```display
      LABEL   POSITION
      a       0
      b       1
      c       2
      ...     ...
      bar     1395
      ...     ...
      foo     4460
      ...     ...
```

We use these positions to encode record values as tuples (i.e., as
nested pairs) by sorting the fields according to their positions.
For example:

```display
      {a=5,b=6}       ⟶   {5,6}
      {a=5,c=7}       ⟶   {5,unit,7}
      {c=7,a=5}       ⟶   {5,unit,7}
      {c=5,b=3}       ⟶   {unit,3,5}
      {f=8,c=5,a=7}   ⟶   {7,unit,5,unit,unit,8}
      {f=8,c=5}       ⟶   {unit,unit,5,unit,unit,8}
```

Note that each field appears in the position associated with its
label, that the size of the tuple is determined by the label with
the highest position, and that we fill in unused positions with
`unit`.

We do exactly the same thing with record types:

```display
      {a:Nat,b:Nat}       ⟶   {Nat,Nat}
      {c:Nat,a:Nat}       ⟶   {Nat,Unit,Nat}
      {f:Nat,c:Nat}       ⟶   {Unit,Unit,Nat,Unit,Unit,Nat}
```

Finally, record projection is encoded as a tuple projection from
the appropriate position:

```display
      t.l ⟶ t.(position of l)
```

It is not hard to check that all the typing rules for the original
"direct" presentation of records are validated by this
encoding.  (The reduction rules are "almost validated" -- not
quite, because the encoding reorders fields.)

:::dev PotentialImprovement
This translation is not quite faithful in a certain sense,
because a projection of a nonexistent field will be well typed (at
type Unit), while it would be ill-typed in the language with real
records.  Should this be mentioned?
:::

Of course, this encoding will not be very efficient if we
happen to use a record with label `foo`!  But things are not
actually as bad as they might seem: for example, if we assume that
our compiler can see the whole program at the same time, we can
_choose_ the numbering of labels so that we assign small positions
to the most frequently used labels.  Indeed, there are industrial
compilers that essentially do this!
::::

::::full
Just as products can be generalized to records, sums can be
generalized to n-ary labeled types called _variants_.  Instead of
`τ₁+τ₂`, we can write something like `<l₁:τ₁,l₂:τ₂,...ln:τn>`
where `l₁`,`l₂`,... are field labels which are used both to build
instances and as case arm labels.

These n-ary variants give us almost enough mechanism to build
arbitrary inductive data types like lists and trees from
scratch -- the only thing missing is a way to allow _recursion_ in
type definitions.  We won't cover this here, but detailed
treatments can be found in many textbooks -- e.g., Types and
Programming Languages {citep Bib.pierce2002}[].
::::


## Exercise: Formalizing the Extensions

::::full
In this series of exercises, you will formalize some of the
extensions described in this chapter.  We've provided the
necessary additions to the syntax of terms and types, and we've
included a few examples that you can test your definitions with to
make sure they are working as expected.  You'll fill in the rest
of the definitions and extend all the proofs accordingly.

To get you started, we've provided implementations for:
  - numbers
  - sums
  - lists
  - unit

You need to complete the implementations for:
  - pairs
  - let (which involves binding)
  - fix

A good strategy is to work on the extensions one at a time (first
pairs, then let, then fix), in separate passes, rather than trying
to do all three at once in a single pass.  For each definition or
proof, begin by reading carefully through the parts that are
provided for you, referring to the text in the {ref "Stlc"}[Stlc] chapter
for high-level intuitions and the embedded comments for detailed
mechanics.
::::

:::::full
Syntax:

```lean
namespace STLCExtended

open scoped MyGetElem

inductive Ty : Type where
  | arrow : Ty → Ty → Ty
  | nat  : Ty
  | sum  : Ty → Ty → Ty
  | list : Ty → Ty
  | unit : Ty
  | prod : Ty → Ty → Ty

inductive Tm : Type where
  -- pure STLC
  | var : String → Tm
  | app : Tm → Tm → Tm
  | abs : String → Ty → Tm → Tm
  -- numbers
  | const: Nat → Tm
  | succ : Tm → Tm
  | pred : Tm → Tm
  | mult : Tm → Tm → Tm
  | ite0  : Tm → Tm → Tm → Tm
  -- sums
  | inl : Ty → Tm → Tm
  | inr : Ty → Tm → Tm
  | case : Tm → String → Tm → String → Tm → Tm
          -- i.e., `case t of inl x₁ => t₁ | inr x₂ => t₂`
  -- lists
  | nil : Ty → Tm
  | cons : Tm → Tm → Tm
  | listCase : Tm → Tm → String → String → Tm → Tm
          -- i.e., [case t₁ of | nil => t₂ | x::y => t₃]
  -- unit
  | unit : Tm

  -- You are going to be working on the following extensions:

  -- pairs
  | pair : Tm → Tm → Tm
  | fst : Tm → Tm
  | snd : Tm → Tm
  -- let
  | let : String → Tm → Tm → Tm
         -- i.e., [let x = t₁ in t₂]
  -- fix
  | fix  : Tm → Tm
```

Note that, for brevity, we've omitted booleans and instead
provided a single `if0` form combining a zero test and a
conditional.  That is, instead of writing

```display
       if x = 0 then ... else ...
```

we'll write this:

```display
       if0 x then ... else ...
```

::::details "Notation"
```lean
syntax:max "~" term:max : stlcTy
syntax:max "(" stlcTy ")" : stlcTy
syntax:max ident : stlcTy
syntax:50 "List" stlcTy:50 : stlcTy
syntax:50 stlcTy:51 " → " stlcTy:50 : stlcTy
syntax:50 stlcTy:51 " × " stlcTy:50 : stlcTy
syntax:50 stlcTy:51 " + " stlcTy:50 : stlcTy
syntax:50 stlcTy:51 " -> " stlcTy:50 : stlcTy
syntax:max (name := tyBracket) "<{ " stlcTy " }>" : term

scoped macro_rules (kind := tyBracket)
  | `(<{ ~$τ:term }>)    => pure τ
  | `(<{ ($τ:stlcTy) }>) => `(<{ $τ:stlcTy }>)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Nat" => `(Ty.nat)
      | "Unit" => `(Ty.unit)
      | _ => `(($x : Ty))
  | `(<{ $τ₁:stlcTy → $τ₂:stlcTy }>)  => `(Ty.arrow <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)
  | `(<{ List $τ₁:stlcTy  }>)  => `(Ty.list <{ $τ₁:stlcTy }>)
  | `(<{ $τ₁:stlcTy × $τ₂:stlcTy }>)  => `(Ty.prod <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)
  | `(<{ $τ₁:stlcTy + $τ₂:stlcTy }>)  => `(Ty.sum <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)
  | `(<{ $τ₁:stlcTy -> $τ₂:stlcTy }>) => `(Ty.arrow <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)
```

```lean
#check <{ Nat -> Nat }>
#check <{ List Nat }>
#check <{ (Nat × Nat) -> Nat }>
#check <{ (Nat + Nat) → Nat }>
```

```lean
scoped syntax:max num : stlcTm
scoped syntax:60 stlcTm:61 " * " stlcTm:60 : stlcTm
scoped syntax:50 "if0 " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

scoped syntax:60 " inr " stlcTy:60 stlcTm:60 : stlcTm
scoped syntax:60 " inl " stlcTy:60 stlcTm:60 : stlcTm
scoped syntax:50 "case " stlcTm:50 " of " "inl" stlcVar " => " stlcTm:50 " | "
  "inr" stlcVar " => " stlcTm:50 : stlcTm

scoped syntax:60 " nil " stlcTy:60 : stlcTm
scoped syntax:60 stlcTm:61 " :: " stlcTm:60 : stlcTm
scoped syntax:50 "case " stlcTm:50 " of " "nil" " => " stlcTm:50 " | "
  stlcVar " :: " stlcVar " => " stlcTm:50 : stlcTm

scoped syntax:60 " ( " stlcTm:60 " , " stlcTm:60 " ) " : stlcTm

scoped syntax:50 "let " stlcVar " = " stlcTm:50 " in " stlcTm:50 : stlcTm

open Lean in
scoped macro_rules (kind := Stlc.tmBracket)
  | `(<{ ~$e:term }>)    => pure e
  | `(<{ ($t:stlcTm) }>) => `(<{ $t:stlcTm }>)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Nat"  => Macro.throwErrorAt x "`Nat` is a type, not a term"
      | "Unit"  => Macro.throwErrorAt x "`Unit` is a type, not a term"
      | "succ" => Macro.throwErrorAt x "`succ` must be applied to an argument"
      | "fst" => Macro.throwErrorAt x "`fst` must be applied to an argument"
      | "snd" => Macro.throwErrorAt x "`snd` must be applied to an argument"
      | "nil" => Macro.throwErrorAt x  "`nil` must be applied to an argument"
      | "pred" => Macro.throwErrorAt x "`pred` must be applied to an argument"
      | "inl" => Macro.throwErrorAt x "`inl` must be applied to two arguments"
      | "inr" => Macro.throwErrorAt x "`inr` must be applied to two arguments"
      | "fix" => Macro.throwErrorAt x  "`fix` must be applied to an argument"
      | "unit" =>  `(Tm.unit)
      | _      => `(Tm.var $(quote x.getId.toString))
  | `(<{ λ $x : $τ . $t }>) => do
      `(Tm.abs $(← Stlc.varStr x) <{ $τ:stlcTy }> <{ $t:stlcTm }>)
  | `(<{ $t₁:stlcTm $t₂:stlcTm }>) =>
      match t₁ with
      | `(stlcTm| $f:ident) =>
          match f.getId.toString with
          | "succ" => `(Tm.succ <{ $t₂:stlcTm }>)
          | "pred" => `(Tm.pred <{ $t₂:stlcTm }>)
          | "fst" => `(Tm.fst <{ $t₂:stlcTm }>)
          | "snd" => `(Tm.snd <{ $t₂:stlcTm }>)
          | "inl" => Macro.throwErrorAt f  "`inl` must be applied to two arguments"
          | "inr" => Macro.throwErrorAt f  "`inr` must be applied to two arguments"
          | "fix" =>  `(Tm.fix  <{ $t₂:stlcTm }>)
          | _      => `(Tm.app  <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
      | _ => `(Tm.app <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)

  | `(<{ $n:num }>)      => `(Tm.const $n)
  | `(<{ $t₁:stlcTm * $t₂:stlcTm }>) => `(Tm.mult <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
  | `(<{ if0 $c then $t else $e }>) =>
      `(Tm.ite0 <{ $c:stlcTm }> <{ $t:stlcTm }> <{ $e:stlcTm }>)

  | `(<{ inl $τ $t}>) => `(Tm.inl <{ $τ:stlcTy }> <{ $t:stlcTm }>)
  | `(<{ inr $τ $t}>) => `(Tm.inr <{ $τ:stlcTy }> <{ $t:stlcTm }>)
  | `(<{ case $t of inl $x₁ => $t₁ | inr $x₂ => $t₂}>) => do
      `(Tm.case <{ $t:stlcTm }> $(← Stlc.varStr x₁) <{ $t₁:stlcTm }>
          $(← Stlc.varStr x₂) <{ $t₂:stlcTm }>)

  | `(<{ nil $τ }>) => `(Tm.nil <{ $τ:stlcTy }>)
  | `(<{ $t₁:stlcTm :: $t₂:stlcTm }>) => `(Tm.cons <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
  | `(<{ case $t of nil => $t₁ | $x₁ :: $x₂ => $t₂}>) => do
      `(Tm.listCase <{ $t:stlcTm }> <{ $t₁:stlcTm }>
          $(← Stlc.varStr x₁) $(← Stlc.varStr x₂) <{ $t₂:stlcTm }>)

  | `(<{ ( $t₁:stlcTm , $t₂:stlcTm ) }>) => `(Tm.pair <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)

  | `(<{ let $x = $t₁ in $t₂ }>) => do
    `(Tm.let $(← Stlc.varStr x) <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
```

```lean
#check <{ case x :: y of nil => 0 | x :: y => 1 }>
#check <{ inl Nat (3, 4) }>
```

```lean
open Lean in
/-- Is `s` usable as a bare variable in `stlcTm` rather than as reserved syntax? -/
def isPlainTmVarName (s : String) : Bool :=
  Stlc.isPlainName s && s != "Nat" && s != "succ" && s != "pred" && s != "unit"
    && s != "Unit" && s != "inl" && s != "inr" && s != "if0" && s != "case" && s != "nil"
    && s != "fix"

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTy` concrete syntax from a `Ty` value. -/
partial def delabTyInner : DelabM (TSyntax `stlcTy) := do
  let stx ←
    match_expr ← getExpr with
    | Ty.nat => `(stlcTy| $(mkIdent `Nat):ident)
    | Ty.unit => `(stlcTy| $(mkIdent `Unit):ident)
    | Ty.arrow _ _ => do
        let a ← withAppFn <| withAppArg delabTyInner
        let b ← withAppArg delabTyInner
        `(stlcTy| $a → $b)
    | Ty.prod _ _ => do
        let a ← withAppFn <| withAppArg delabTyInner
        let b ← withAppArg delabTyInner
        `(stlcTy| $a × $b)
    | Ty.sum _ _ => do
        let a ← withAppFn <| withAppArg delabTyInner
        let b ← withAppArg delabTyInner
        `(stlcTy| $a + $b)
    | Ty.list _ => do
        let b ← withAppArg delabTyInner
        `(stlcTy| List $b)
    | _ => do
        match ← delab with
        | `($i:ident) => `(stlcTy| $i:ident)
        | e => `(stlcTy| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTm` concrete syntax from a `Tm` value. -/
partial def delabTmInner : DelabM (TSyntax `stlcTm) := do
  let stx ←
    match_expr ← getExpr with
    | Tm.var _ => do
        let x ← withAppArg delab
        match x with
        | `($s:str) =>
            if isPlainTmVarName s.getString then
              `(stlcTm| $(mkIdent (Name.mkSimple s.getString)):ident)
            else
              let var : Term := mkIdent ``Tm.var
              `(stlcTm| ~($var $x))
        | _ =>
            let var : Term := mkIdent ``Tm.var
            `(stlcTm| ~($var $x))
    | Tm.const _ => do
        let n ← withAppArg delab
        match n with
        | `($n:num) => `(stlcTm| $n:num)
        | _ =>
            let const : Term := mkIdent ``Tm.const
            `(stlcTm| ~($const $n))
    | Tm.app _ _ => do
        let f ← withAppFn <| withAppArg delabTmInner
        let a ← withAppArg delabTmInner
        `(stlcTm| $f $a)
    | Tm.abs _ _ _ => do
        let x ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
        let τ ← withAppFn <| withAppArg delabTyInner
        let t ← withAppArg delabTmInner
        `(stlcTm| λ $x : $τ . $t)
    | Tm.let _ _ _ => do
        let x ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
        let t₁ ← withAppFn <| withAppArg delabTmInner
        let t₂ ← withAppArg delabTmInner
        `(stlcTm| let $x = $t₁ in $t₂)
    | Tm.succ _ => do
        let t ← withAppArg delabTmInner
        `(stlcTm| succ $t)
    | Tm.pred _ => do
        let t ← withAppArg delabTmInner
        `(stlcTm| pred $t)
    | Tm.mult _ _ => do
        let a ← withAppFn <| withAppArg delabTmInner
        let b ← withAppArg delabTmInner
        `(stlcTm| $a * $b)
    | Tm.ite0 _ _ _ => do
        let c ← withAppFn <| withAppFn <| withAppArg delabTmInner
        let t ← withAppFn <| withAppArg delabTmInner
        let e ← withAppArg delabTmInner
        `(stlcTm| if0 $c then $t else $e)
    | Tm.inl _ _ => do
        let τ ← withAppFn <| withAppArg delabTyInner
        let t ← withAppArg delabTmInner
        `(stlcTm| inl $τ $t)
    | Tm.inr _ _ => do
        let τ ← withAppFn <| withAppArg delabTyInner
        let t ← withAppArg delabTmInner
        `(stlcTm| inr $τ $t)
    | Tm.case _ _ _ _ _ => do
        let c  ← withAppFn <| withAppFn <| withAppFn <| withAppFn <| withAppArg delabTmInner
        let x₁ ← withAppFn <| withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
        let t₁ ← withAppFn <| withAppFn <| withAppArg delabTmInner
        let x₂ ← withAppFn <| withAppArg Stlc.delabVarInner
        let t₂ ← withAppArg delabTmInner
        `(stlcTm| case $c of inl $x₁ => $t₁ | inr $x₂ => $t₂)
    | Tm.nil _ => do
        let t ← withAppArg delabTyInner
        `(stlcTm| nil $t)
    | Tm.pair _ _ => do
        let a ← withAppFn <| withAppArg delabTmInner
        let b ← withAppArg delabTmInner
        `(stlcTm| ( $a , $b ) )
    | Tm.fst _ => do
        let b ← withAppArg delabTmInner
        `(stlcTm| fst $b )
    | Tm.snd _ => do
        let b ← withAppArg delabTmInner
        `(stlcTm| snd $b )
    | Tm.listCase _ _ _ _ _ => do
        let c ←  withAppFn <| withAppFn <| withAppFn <| withAppFn <| withAppArg delabTmInner
        let t₁ ← withAppFn <| withAppFn <| withAppFn <| withAppArg delabTmInner
        let x₁ ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
        let x₂ ← withAppFn <| withAppArg Stlc.delabVarInner
        let t₂ ← withAppArg delabTmInner
        `(stlcTm| case $c of nil => $t₁ | $x₁ :: $x₂ => $t₂)
    | Tm.fix _ => do
        let t ← withAppArg delabTmInner
        `(stlcTm| $(mkIdent `fix):ident $t)
    | Tm.unit => do
        `(stlcTm| $(mkIdent `unit):ident)
    | _ => do
        -- `subst` is defined below, so it is matched by name rather than with
        -- `match_expr`; a substitution prints in its own bracket notation.
        let e ← getExpr
        if e.getAppFn.constName? == some `SltcExtended.subst && e.getAppNumArgs == 3 then
          let x ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
          let s ← withAppFn <| withAppArg delabTmInner
          let t ← withAppArg delabTmInner
          `(stlcTm| [$x := $s] $t)
        else
          match ← delab with
          | `($i:ident) => `(stlcTm| $i:ident)
          | e => `(stlcTm| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.StlcExtended.Ty.nat, delab app.StlcExtended.Ty.arrow, delab app.StlcExtended.Ty.unit,
  delab app.StlcExtended.Ty.prod, delab app.StlcExtended.Ty.sum, delab app.StlcExtended.Ty.list]
def delabTy : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Ty.nat => true | Ty.arrow _ _ => true
    | Ty.prod _ _ => true | Ty.sum _ _ => true
    | Ty.list _ => true | Ty.unit => true | _ => false
  match ← delabTyInner with
  | `(stlcTy| ~$e) => pure e
  | e => `(<{ $e:stlcTy }>)

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.StlcExtended.Tm.var, delab app.StlcExtended.Tm.app, delab app.StlcExtended.Tm.abs,
  delab app.StlcExtended.Tm.const, delab app.StlcExtended.Tm.succ, delab app.StlcExtended.Tm.pred,
  delab app.StlcExtended.Tm.mult, delab app.StlcExtended.Tm.ite0, delab app.StlcExtended.Tm.nil,
  delab app.StlcExtended.Tm.cons, delab app.StlcExtended.Tm.listCase, delab app.StlcExtended.Tm.inl,
  delab app.StlcExtended.Tm.inr, delab app.StlcExtended.Tm.case, delab app.StlcExtended.Tm.pair,
  delab app.StlcExtended.Tm.fst, delab app.StlcExtended.Tm.snd, delab app.StlcExtended.Tm.unit,
  delab app.StlcExtended.Tm.let, delab app.StlcExtended.Tm.fix ]
def delabTm : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Tm.var _ => true | Tm.app _ _ => true | Tm.abs _ _ _ => true
    | Tm.const _ => true | Tm.succ _ => true | Tm.pred _ => true
    | Tm.mult _ _ => true | Tm.ite0 _ _ _ => true
    | Tm.unit => true | Tm.fix _ => true | Tm.let _ _ _ => true
    | Tm.inl _ _ => true | Tm.inr _ _ => true | Tm.case _ _ _ _ _ => true
    | Tm.nil _ => true | Tm.cons _ _ => true | Tm.listCase _ _ _ _ _ => true
    | Tm.pair _ _ => true | Tm.fst _ => true | Tm.snd _ => true
    | _ => false
  match ← delabTmInner with
  | `(stlcTm| ~($e)) => pure e
  | `(stlcTm| ~$e) => pure e
  | e => `(<{ $e:stlcTm }>)
```
::::
:::::

:::ignore
Checks that the extended grammar parses the way it should.

```lean -show
#check <{ unit }>
#check <{ λx : Nat. x }>
#check <{ if0 x then x else x }>
#check <{ if0 y x then x else x }>
#check <{ if0 (y x) then x else x }>
#check <{ x * y * z }>
#check <{ succ (pred x) }>
#check <{ succ x y }>
#check <{ inr Nat (λx : Unit . x) }>
#check <{ nil Nat }>
#check <{ 3 :: nil Nat }>
#check <{ (x , y) }>
#check <{ fst x }>
-- why does this one not work
-- #check <{ fst (x , y) }>
#check <{ inl Nat 3 }>
#check <{ x (succ y) }>
#check <{ x * y z }>
#check <{ x * y (succ z) }>
#check <{ z x y }>
#check <{ z x * y }>
#check <{ λ x : Nat . λ y : Nat . if0 x then 0 else pred (x * y) }>
```
:::

:::dev "Daniel Sainati (@dsainati1)" BeforeNextRelease
This notation is mostly there but there were a couple issues I didn't know how to fix.
Need to fix them before a real release:
* Delaborator isn't actually printing the above examples in STLC syntax, idk why
* Some terms don't work in pattern matches for some reason
:::

## Substitution

::::exercise (rating := 3) (name := "STLCExtended.subst") (manual := true)

```lean
section
set_option hygiene false in
local macro_rules (kind := Stlc.tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← Stlc.varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  -- pure STLC
  | .var y =>
      if x = y then s else t
  | .abs y τ t₁ =>
      if x = y then t else <{ λ ~y : ~τ . [~x := ~s] ~t₁ }>
  | <{ ~t₁ ~t₂ }> =>
      <{ ([~x := ~s] ~t₁) ([~x := ~s] ~t₂) }>
  -- numbers
  | .const _ =>
      t
  | <{ succ ~t₁ }> =>
      <{ succ ([~x := ~s] ~t₁) }>
  | <{ pred ~t₁ }> =>
      <{ pred ([~x := ~s] ~t₁) }>
  | <{ ~t₁ * ~t₂ }> =>
      <{ ([~x := ~s] ~t₁) * ([~x := ~s] ~t₂) }>
  | <{ if0 ~t₁ then ~t₂ else ~t₃ }> =>
      <{ if0 [~x := ~s] ~t₁ then [~x := ~s] ~t₂ else [~x := ~s] ~t₃ }>
  -- sums
  | .inl τ₂ t₁ =>
      <{inl ~τ₂ ( [~x:= ~s] ~t₁) }>
  | .inr τ₂ t₁ =>
      <{inr ~τ₂ ( [~x:= ~s] ~t₁) }>
  | <{case ~t of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂}> =>
      let t₁ := if x = x₁ then t₁ else <{ [~x := ~s] ~t₁ }>
      let t₂ := if x = x₂ then t₂ else <{ [~x := ~s] ~t₂ }>
      <{case ([~x := ~s] ~t) of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂ }>
  -- lists
  | .nil _ => t
  | <{~t₁ :: ~t₂}> =>
      <{ ([~x := ~s] ~t₁) :: [~x := ~s] ~t₂ }>
  | <{case ~t₁ of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃}> =>
      let t₃ := if x = x₁ || x = x₂ then t₃ else <{ [~x := ~s] ~t₃ }>
      <{case ( [~x := ~s] ~t₁ ) of
          nil => [~x := ~s] ~t₂
        | x₁ :: x₂ =>  ~t₃ }>
  -- unit
  | .unit => <{ unit }>

  -- Complete the following cases.

  -- pairs
  | <{(~t₁, ~t₂)}> =>
      solution!(<{ ([~x := ~s] ~t₁ , [~x := ~s] ~t₂) }>)
  | Tm.fst t =>
      solution!(<{ fst ([~x := ~s] ~t)}>)
  | Tm.snd t =>
      solution!(<{ snd ([~x := ~s] ~t)}>)
  -- let
  | <{let ~y = ~t₁ in ~t₂}> => solution!(
      let t₂ := if x = y then t₂ else <{ [~x := ~s] ~t₂ }>
      <{let ~y = [~x := ~s] ~t₁ in ~t₂ }>)
  -- fix
  | <{ fix ~t₁ }> => solution!(<{ fix ([~x := ~s] ~t₁) }>)
end

macro_rules (kind := Stlc.tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← Stlc.varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)
```

:::dev PotentialImprovement
We need to add a test case somewhere that exercises the
situation `[x:=s] (let x = foo in bar)`

Also, a common failure mode seems to be that the definition
of subst for the let construct used the variable x without binding
it with an universal quantifier. So the let rule was specialized to
the specific variable x rather than quantifying over all
variables. How could we help people avoid this?
:::

:::instructors
BCP23: a common failure mode seems to be that the
definition of subst for the let construct used the variable x without
binding it with an universal quantifier. So the let rule was specialized
to the specific variable x rather than quantifying over all
variables. Hopefully the following unit tests will help!
:::

Make sure the following tests are valid by reflexivity:

```lean
example : <{ [z := 0] (let w = z in z) }> = <{ let w = 0 in 0 }> := by
  solution!
    rfl

example : <{ [z := 0] (let w = z in w) }> = <{ let w = 0 in w }> := by
  solution!
    rfl

example : <{  [z := 0] (let y = succ 0 in z) }> = <{ let y = succ 0 in 0 }> := by
  solution!
    rfl
```
::::

## Reduction

Next we define the values of our language.

```lean
inductive Tm.IsValue : Tm → Prop where
  -- In pure STLC, function abstractions are values:
  | abs (x : String) (τ₂ : Ty) (t₁ : Tm) : IsValue <{λ ~x : ~τ₂ . ~t₁}>
  -- Numbers are values:
  | nat (n : Nat) : IsValue (.const n)
  -- A tagged value is a value:
  | inl (v : Tm) (τ₁ : Ty) :
      IsValue v →
      IsValue <{inl ~τ₁ ~v}>
  | inr  (v : Tm) (τ₁ : Ty) :
      IsValue v →
      IsValue <{inr ~τ₁ ~v}>
  -- A list is a value iff its head and tail are values:
  | nil (τ₁ : Ty) : IsValue <{nil ~τ₁}>
  | cons (v₁ v₂ : Tm) :
      IsValue v₁ →
      IsValue v₂ →
      IsValue <{~v₁ :: ~v₂}>
  -- A unit is always a value
  | unit : IsValue .unit
  -- A pair is a value if both components are:
  | pair (v₁ v₂ : Tm) :
      IsValue v₁ →
      IsValue v₂ →
      IsValue <{(~v₁, ~v₂)}>
```

::::exercise (rating := 3) (name := "STLCExtended.step") (manual := true)
```lean
section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
  -- pure STLC
  | appAbs (x : String) (τ₂ : Ty) (t₁ v₂ : Tm) :
        v₂.IsValue →
         <{(λ ~x: ~τ₂ . ~t₁) ~v₂}> ⟶ <{ [~x := ~v₂] ~t₁ }>
  | app₁ (t₁ t₁' t₂ : Tm) :
         t₁ ⟶ t₁' →
         <{~t₁ ~t₂}> ⟶ <{~t₁' ~t₂}>
  | app₂ (v₁ t₂ t₂' : Tm) :
        v₁.IsValue →
         t₂ ⟶ t₂' →
         <{~v₁ ~t₂}> ⟶ <{~v₁  ~t₂'}>
  -- numbers
  | succ (t₁ t₁' : Tm) :
         t₁ ⟶ t₁' →
         <{succ ~t₁}> ⟶ <{succ ~t₁'}>
  | succNat (n : Nat) :
      <{ succ ~(Tm.const n) }> ⟶ Tm.const (n + 1)
    | pred (t₁ t₁' : Tm) (h : t₁ ⟶ t₁') :
      <{ pred ~t₁ }> ⟶ <{ pred ~t₁' }>
  | predConst (n : Nat) :
      <{ pred ~(Tm.const n) }> ⟶ Tm.const (n - 1)
  | multConst (n₁ n₂ : Nat) :
      <{ ~(Tm.const n₁) * ~(Tm.const n₂) }> ⟶ Tm.const (n₁ * n₂)
  | mult1 (t₁ t₁' t₂ : Tm) (h : t₁ ⟶ t₁') :
      <{ ~t₁ * ~t₂ }> ⟶ <{ ~t₁' * ~t₂ }>
  | mult2 (v₁ t₂ t₂' : Tm) (hv : v₁.IsValue) (h : t₂ ⟶ t₂') :
      <{ ~v₁ * ~t₂ }> ⟶ <{ ~v₁ * ~t₂' }>
  | if0Step (t₁ t₁' t₂ t₃ : Tm) (h : t₁ ⟶ t₁') :
      <{ if0 ~t₁ then ~t₂ else ~t₃ }> ⟶ <{ if0 ~t₁' then ~t₂ else ~t₃ }>
  | if0Zero (t₂ t₃ : Tm) :
      <{ if0 0 then ~t₂ else ~t₃ }> ⟶ t₂
  | if0Nonzero (n : Nat) (t₂ t₃ : Tm) :
      <{ if0 ~(Tm.const (n + 1)) then ~t₂ else ~t₃ }> ⟶ t₃
  -- sums
  | inl (t₁ t₁' : Tm) (τ₂ : Ty) :
        t₁ ⟶ t₁' →
        <{inl ~τ₂ ~t₁}> ⟶ <{inl ~τ₂ ~t₁'}>
  | inr (t₂ t₂' : Tm) (τ₁ : Ty) :
        t₂ ⟶ t₂' →
        <{inr ~τ₁ ~t₂}> ⟶ <{inr ~τ₁ ~t₂'}>
  | case (t t' : Tm) (x₁ : String) (t₁ : Tm) (x₂ : String) (t₂ : Tm) :
        t ⟶ t' →
        <{case ~t of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂}> ⟶
        <{case ~t' of inl ~x₁ =>~ t₁ | inr ~x₂ => ~t₂}>
  | caseInl (v : Tm) (x₁:String) (t₁ : Tm) (x₂ : String) (t₂ : Tm) (τ₂ : Ty) :
        v.IsValue →
        <{case inl ~τ₂ ~v of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂}> ⟶ <{ [~x₁ := ~v] ~t₁ }>
  | caseInr (v : Tm) (x₁:String) (t₁ : Tm) (x₂ : String) (t₂ : Tm) (τ₁ : Ty) :
        v.IsValue →
        <{case inr ~τ₁ v of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂}> ⟶ <{ [~x₂ := ~v] ~t₂ }>
  -- lists
  | cons₁ (t₁ t₁' t₂ : Tm) :
       t₁ ⟶ t₁' →
       <{~t₁ :: ~t₂}> ⟶ <{~t₁' :: ~t₂}>
  | cons₂ (v₁ t₂ t₂' : Tm) :
       v₁.IsValue →
       t₂ ⟶ t₂' →
       <{~v₁ :: ~t₂}> ⟶ <{~v₁ :: ~t₂'}>
  | listCase₁ (t₁ t₁' t₂ : Tm) (x₁ x₂ : String) (t₃ : Tm) :
       t₁ ⟶ t₁' →
       <{case ~t₁ of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃}> ⟶
       <{case ~t₁' of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃}>
  | listCaseNil (τ₁ : Ty) (t₂ : Tm) (x₁ x₂ : String) (t₃ : Tm) :
       <{case nil ~τ₁ of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃}> ⟶ t₂
  | listCaseCons (v₁ vl t₂ : Tm) (x₁ x₂ : String) (t₃ : Tm) :
       v₁.IsValue →
       vl.IsValue →
       <{case ~v₁ :: ~vl of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃}>
         ⟶  <{ [~x₂ := ~vl] ([~x₁ := ~v₁] ~t₃) }>

  -- Add rules for the following extensions.

  -- pairs
  -- SOLUTION
  | pair₁  (t₁ t₁' t₂ : Tm) :
        t₁ ⟶ t₁' →
        <{ (~t₁, ~t₂) }> ⟶ <{ (~t₁' , ~t₂) }>
  | pair₂ (v₁ t₂ t₂' : Tm) :
        v₁.IsValue →
        t₂ ⟶ t₂' →
        <{ (~v₁, ~t₂) }> ⟶  <{ (~v₁, ~t₂') }>
  | fst₁ (t t' : Tm) :
        t ⟶ t' →
        <{ fst ~t }> ⟶ <{ fst ~t' }>
  | fstPair (v₁ v₂ : Tm) :
        v₁.IsValue →
        v₂.IsValue →
        Tm.fst  <{ (~v₁ , ~v₂) }> ⟶ v₁
  | snd₁ (t t' : Tm) :
        t ⟶ t' →
        <{ snd ~t }> ⟶ <{ snd ~t' }>
  | sndPair (v₁ v₂ : Tm) :
        v₁.IsValue →
        v₂.IsValue →
        Tm.snd  <{ (~v₁, ~v₂) }> ⟶ v₂
  -- END SOLUTION
  -- let
  -- SOLUTION
  | let₁ (x : String) (t₁ t₁' t₂ : Tm) :
       t₁ ⟶ t₁' →
       <{ let ~x = ~t₁ in ~t₂}> ⟶ <{ let ~x = ~t₁' in ~t₂ }>
  | letValue (x : String) (v₁ t₂ : Tm) :
       v₁.IsValue →
       <{ let ~x = ~v₁ in ~t₂ }> ⟶ <{ [~x := ~v₁] ~t₂ }>
  -- END SOLUTION
  -- fix
  -- SOLUTION
  | fix₁ (t₁ t₁' : Tm) :
       t₁ ⟶ t₁' →
       <{ fix ~t₁ }> ⟶ <{ fix ~t₁' }>
   | fixAbs (x : String) (τ₁ : Ty) (t₁ : Tm) :
      <{ fix (λ ~x : ~τ₁ . ~t₁) }> ⟶
      <{ [~x := fix (λ ~x : ~τ₁ . ~t₁) ] ~t₁ }>
  -- END SOLUTION
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'
```
::::

## Typing

::::exercise (rating := 3) (name := "STLCExtended.HasType") (manual := true)

```lean
abbrev Context := PartialMap String Ty
```

:::details "Notation encoding: contexts and judgments"
The context grammar `stlcCtx` is reused as well; only the map it denotes is new,
since the types it stores are this language's.  As with `subst`, the judgment
rule is introduced twice: `local` and hygiene-free while the relation is being
declared, then again for real.

```lean
open Lean in
/-- The `Context` denoted by a context expression. -/
partial def ctxTerm (G : TSyntax `stlcCtx) : MacroM Term :=
  match G with
  | `(stlcCtx| ∅)   => `((∅ : Context))
  | `(stlcCtx| ~$e) => pure e
  | `(stlcCtx| $x:stlcVar ↦ $τ:stlcTy ; $G:stlcCtx) => do
      `(PartialMap.update $(← ctxTerm G) $(← Stlc.varStr x) <{ $τ:stlcTy }>)
  | _ => Macro.throwUnsupported

section StlcExtended
set_option hygiene false in
local macro_rules (kind := Stlc.judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $τ:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $τ:stlcTy }>)
```
:::

```lean
inductive HasType : Context → Tm → Ty → Prop where
  -- pure STLC
  | var (Γ : Context) (x : String) (τ₁ : Ty) (h : Γ[x] = some τ₁) :
      <{ ~Γ ⊢ ~(Tm.var x) ⦂ ~τ₁ }>
  | abs (Γ : Context) (x : String) (τ₁ τ₂ : Ty) (t₁ : Tm)
      (h : <{ ~x ↦ ~τ₂ ; ~Γ ⊢ ~t₁ ⦂ ~τ₁ }>) :
      <{ ~Γ ⊢ λ ~x : ~τ₂ . ~t₁ ⦂ ~τ₂ → ~τ₁ }>
  | app (Γ : Context) (τ₁ τ₂ : Ty) (t₁ t₂ : Tm)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ ~τ₂ → ~τ₁ }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~τ₂ }>) :
      <{ ~Γ ⊢ ~t₁ ~t₂ ⦂ ~τ₁ }>
  -- numbers
  | const (Γ : Context) (n : Nat) :
      <{ ~Γ ⊢ ~(Tm.const n) ⦂ Nat }>
  | succ (Γ : Context) (t₁ : Tm) (h : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) :
      <{ ~Γ ⊢ succ ~t₁ ⦂ Nat }>
  | pred (Γ : Context) (t₁ : Tm) (h : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) :
      <{ ~Γ ⊢ pred ~t₁ ⦂ Nat }>
  | mult (Γ : Context) (t₁ t₂ : Tm)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ Nat }>) :
      <{ ~Γ ⊢ ~t₁ * ~t₂ ⦂ Nat }>
  | ite0 (Γ : Context) (t₁ t₂ t₃ : Tm) (τ : Ty)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~τ }>)
      (h₃ : <{ ~Γ ⊢ ~t₃ ⦂ ~τ }>) :
      <{ ~Γ ⊢ if0 ~t₁ then ~t₂ else ~t₃ ⦂ ~τ }>
  -- sums
  | inl (Γ : Context) (t₁ : Tm) (τ₁ τ₂ : Ty) :
      <{ ~Γ ⊢ ~t₁ ⦂ ~τ₁ }> →
      <{ ~Γ ⊢ (inl ~τ₂ ~t₁) ⦂ ~τ₁ + ~τ₂ }>
  | inr (Γ : Context) (t₂ : Tm) (τ₁ τ₂ : Ty) :
      <{ ~Γ ⊢ ~t₂ ⦂ ~τ₂ }> →
      <{ ~Γ ⊢ (inr ~τ₁ ~t₂) ⦂ ~τ₁ + ~τ₂ }>
  | case (Γ : Context) (x₁ x₂ : String) (τ₁ τ₂ τ₃: Ty) (t t₁ t₂ : Tm) :
      <{ ~Γ ⊢ ~t ⦂ ~τ₁ + ~τ₂ }> →
      <{ ~x₁ ↦ τ₁ ; ~Γ ⊢ ~t₁ ⦂ ~τ₃ }> →
      <{ ~x₂ ↦ τ₂ ; ~Γ ⊢ ~t₂ ⦂ ~τ₃ }> →
      <{ ~Γ ⊢ case ~t of inl ~x₁ => ~t₁ | inr ~x₂ => ~t₂ ⦂ ~τ₃ }>
  -- lists
  | nil (Γ : Context) (τ₁ : Ty) :
      <{ ~Γ ⊢ nil ~τ₁ ⦂ List ~τ₁ }>
  | cons (Γ : Context) (t₁ t₂ : Tm) (τ₁ : Ty) :
      <{ ~Γ ⊢ ~t₁ ⦂ ~τ₁ }> →
      <{ ~Γ ⊢ ~t₂ ⦂ List ~τ₁ }> →
      <{ ~Γ ⊢ ~t₁ :: ~t₂ ⦂ List ~τ₁ }>
  | listCase (Γ : Context) (t₁ t₂ t₃ : Tm) (x₁ x₂ : String) (τ₁ τ₂ : Ty) :
      <{ ~Γ ⊢ ~t₁ ⦂ List τ₁ }> →
      <{ ~Γ ⊢ ~t₂ ⦂ ~τ₂ }> →
      <{ ~x₁ ↦ τ₁ ; ~x₂ ↦ List ~τ₁ ; ~Γ ⊢ ~t₃ ⦂ ~τ₂ }> →
      <{ ~Γ ⊢ case ~t₁ of nil => ~t₂ | ~x₁ :: ~x₂ => ~t₃ ⦂ ~τ₂ }>
  -- unit
  | unit (Γ : Context) :
      <{ ~Γ ⊢ unit ⦂ Unit }>

  -- Add rules for the following extensions.

  -- pairs
  -- SOLUTION
  | pair (Γ : Context) (t₁ t₂ : Tm) (τ₁ τ₂ : Ty) :
      <{ ~Γ ⊢ ~t₁ ⦂ ~τ₁ }> →
      <{ ~Γ ⊢ ~t₂ ⦂ ~τ₂ }> →
      <{ ~Γ ⊢ (~t₁, ~t₂) ⦂ ~τ₁ × ~τ₂ }>
  | fst (Γ : Context) (t : Tm) (τ₁ τ₂ : Ty) :
      <{ ~Γ ⊢ t ⦂ ~τ₁ × ~τ₂ }> →
      <{ ~Γ ⊢ fst ~t ⦂ ~τ₁ }>
  | snd (Γ : Context) (t : Tm) (τ₁ τ₂ : Ty) :
      <{ ~Γ ⊢ ~t ⦂ ~τ₁ × ~τ₂ }> →
      <{ ~Γ ⊢ snd ~t ⦂ ~τ₂ }>
  -- END SOLUTION
  -- let
  -- SOLUTION
  | let (Γ : Context) (x : String) (t₁ t₂ : Tm) (τ₁ τ₂ : Ty) :
      <{ ~Γ ⊢ ~t₁ ⦂ τ₁ }> →
      <{ ~x ↦ ~τ₁ ; ~Γ ⊢ ~t₂ ⦂ ~τ₂ }> →
      <{ ~Γ ⊢ let ~x = ~t₁ in ~t₂ ⦂ ~τ₂ }>
  -- END SOLUTION
  -- fix
  -- SOLUTION
  | fix (Γ : Context) (t₁ : Tm) (τ₁ : Ty) :
      <{ ~Γ ⊢ ~t₁ ⦂ ~τ₁ → ~τ₁ }> →
      <{ ~Γ ⊢ fix ~t₁ ⦂ ~τ₁ }>
  -- END SOLUTION
```

:::autogradedHole HasType
:::
::::


::::details "Notation encoding: the judgment, for real"
Closing the section retires the hygiene-free rule; the same rule is then
declared again, hygienically, for every later use, and a pair of unexpanders
prints judgments back in their own notation.

```lean
end StlcExtended

scoped macro_rules (kind := Stlc.judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $τ:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $τ:stlcTy }>)

open Lean PrettyPrinter in
/-- Rebuild `stlcCtx` syntax from the term syntax of a `Context`, so that a
context prints as `x ↦ Nat ; Γ` rather than as a chain of map updates. -/
partial def unexpandCtx : Term → UnexpandM (TSyntax `stlcCtx)
  | `(∅) => `(stlcCtx| ∅)
  | `($x:str →ₚ $τ) => do
      unexpandCtx (← `($x →ₚ $τ ; ∅))
  | `($x:str →ₚ $τ ; $G) => do
      let G' ← unexpandCtx G
      let x' : TSyntax `stlcVar ←
        if Stlc.isPlainName x.getString then
          `(stlcVar| $(mkIdent (Name.mkSimple x.getString)):ident)
        else `(stlcVar| ~$x)
      match τ with
      | `(<{ $T':stlcTy }>) => `(stlcCtx| $x':stlcVar ↦ $T' ; $G')
      | _                   => `(stlcCtx| $x':stlcVar ↦ ~($τ) ; $G')
  | G => `(stlcCtx| ~($G))

open Lean PrettyPrinter in
@[app_unexpander HasType]
def HasType.unexpand : Unexpander
  | `($_ $G <{ $t:stlcTm }> <{ $τ:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ $τ }>)
  | `($_ $G <{ $t:stlcTm }> $τ) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ ~($τ) }>)
  | `($_ $G $t <{ $τ:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ $τ }>)
  | `($_ $G $t $τ) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ ~($τ) }>)
  | _ => throw ()
```
::::

## Examples

:::::exercise (rating := 5) (name := "STLCExtended.examples") (optional := true)

This section presents formalized versions of the examples from
above (plus several more).

For each example, replace `sorry` once you've implemented enough of
the definitions for the tests to pass.

The examples at the beginning focus on specific features; you can
use these to make sure your definition of a given feature is
reasonable before moving on to extending the proofs later in the
file with the cases relating to this feature.
The later examples require all the features together, so you'll
need to come back to these when you've got all the definitions
filled in.

```lean
namespace Examples
```

```lean
namespace Numbers

def tm_test := <{if0 (pred (succ (pred (2 * 0)))) then 5 else 6}>

theorem typechecks : <{ ∅ ⊢ ~tm_test ⦂ Nat }> := by
  solution!
    sorry
```

:::gradeTheorem "0.5" typechecks
:::

```lean
theorem reduces : tm_test ⟶* (Tm.const 5) := by solution!(sorry)
```

:::gradeTheorem "0.5" reduces
:::

```lean
end Numbers
```

```lean
namespace Prod

-- snd (fst ((5, 6), 7))
def tm_test := Tm.snd (.fst (.pair (.pair (.const 5) (.const 6)) (.const 7)))

theorem typechecks : <{ ∅ ⊢ ~tm_test ⦂ Nat }> := by solution!(sorry)
```

:::gradeTheorem "0.5" typechecks
:::

```lean
theorem reduces : tm_test ⟶* Tm.const 6 := by solution!(sorry)
```

:::gradeTheorem "0.5" reduces
:::

```lean
end Prod
```

```lean
namespace Let

def tm_test := <{let x = (pred 6) in (succ x)}>

theorem typechecks : <{ ∅ ⊢ ~tm_test ⦂ Nat }> := by solution!(sorry)
```

:::gradeTheorem "0.5" typechecks
:::

```lean
theorem reduces :
  tm_test ⟶* Tm.const 6 := by solution!(sorry)
```
:::gradeTheorem "0.5" reduces
:::

```lean
end Let
```

```lean
namespace Let1

def tm_test :=
  <{ let z = pred 6 in
     (succ z) }>

theorem typechecks :
  <{ ∅ ⊢ ~tm_test ⦂ Nat }> := by solution!(sorry)
```

:::gradeTheorem "0.5" typechecks
:::

```lean
theorem reduces :
  tm_test ⟶* Tm.const 6 := by solution!(sorry)
```

:::gradeTheorem "0.5" reduces
:::

```lean
end Let1
```

```lean
namespace Sums1

def tm_test :=
  <{ case (inl Nat 5) of
       inl x => x
     | inr y => y }>

theorem typechecks :
  <{ ∅ ⊢ ~tm_test ⦂ Nat }> := by solution!(sorry)
```

:::gradeTheorem "0.5" typechecks
:::

```lean
theorem reduces :
  tm_test ⟶* Tm.const 5 := by solution!(sorry)
```

:::gradeTheorem "0.5" reduces
:::

```lean
end Sums1

namespace Sums2

def tm_test :=
  <{ let processSum =
     (λx:Nat + Nat.
       case x of
          inl n => n
        | inr n => (if0 n then 1 else 0)) in
     (processSum (inl Nat 5), processSum (inr Nat 5)) }>

theorem typechecks :
  <{ ∅ ⊢ ~tm_test ⦂ Nat × Nat }> := by solution!(sorry)
```

:::gradeTheorem "0.5" typechecks
:::

```lean
theorem reduces :
  tm_test ⟶* <{ (5, Tm.const 0) }> := by solution!(sorry)
```

:::gradeTheorem "0.5" reduces
:::

```lean
end Sums2
```

```lean
namespace Lists

def tm_test :=
  <{ let l = (5 :: 6 :: (nil Nat)) in
     case l of
       nil => 0
     | x :: y => (x * x) }>

theorem typechecks :
  <{ ∅ ⊢ ~tm_test ⦂ Nat }> := by solution!(sorry)
```

:::gradeTheorem "0.5" typechecks
:::

```lean
theorem reduces :
  tm_test ⟶* Tm.const 25 := by solution!(sorry)
```
:::gradeTheorem "0.5" reduces
:::

```lean
end Lists
```

```lean
namespace Fix1

def fact :=
  <{ fix
      (λf:Nat→Nat.
        λa:Nat.
         if0 a then 1 else (a * (f (pred a)))) }>

-- (Warning: you may be able to typecheck `fact` but still have some rules wrong!) *)

theorem typechecks :
  <{ ∅ ⊢ ~fact ⦂ Nat → Nat }> := by solution!(sorry)
```

:::gradeTheorem "0.5" typechecks
:::

```lean
theorem reduces :
  <{ ~fact 4 }> ⟶* Tm.const 24 := by solution!(sorry)
```

:::gradeTheorem "0.5" reduces
:::

```lean
end Fix1

namespace Fix2

def map :=
  <{ λg:Nat→Nat.
       fix
         (λf:(List Nat)→(List Nat).
            λl:List Nat.
               case l of
                 nil => nil Nat
               | x::l => ((g x)::(f l))) }>

theorem typechecks :
  <{ ∅ ⊢ ~map ⦂
     (Nat → Nat) → (List Nat) → (List Nat) }> := by solution!(sorry)
```

:::gradeTheorem "0.5" typechecks
:::

```lean
theorem reduces :
  <{ ~map (λa:Nat. succ a) (1 :: 2 :: (nil Nat)) }>
  ⟶* <{ 2 :: 3 :: (nil Nat) }> := by solution!(sorry)
```

:::gradeTheorem "0.5" reduces
:::

```lean
end Fix2

namespace Fix3

def equal :=
  <{ fix
        (λeq:Nat→Nat→Nat.
           λm:Nat. λn:Nat.
             if0 m then (if0 n then 1 else 0)
             else (if0 n
                   then 0
                   else (eq (pred m) (pred n)))) }>

theorem typechecks :
 <{ ∅ ⊢ ~equal ⦂ Nat → Nat → Nat }> := by solution!(sorry)
```

:::gradeTheorem "0.5" typechecks
:::

```lean
theorem reduces :
  <{ ~equal 4 4 }> ⟶* Tm.const 1 := by solution!(sorry)
```

:::gradeTheorem "0.5" reduces
:::

```lean
theorem reduces2 :
  <{ ~equal 4 5 }> ⟶* Tm.const 0 := by solution!(sorry)
```

:::gradeTheorem "0.5" reduces2
:::

```lean
end Fix3

namespace Fix4

/- def eotest :=
  <{ let evenodd =
           fix
           (λeo: (Nat → Nat) × (Nat → Nat).
              (λn:Nat. if0 n then 1 else (snd eo (pred n)) ,
               λn:Nat. if0 n then 0 else (fst eo (pred n)))) in
     let even = fst evenodd in
     let odd  = snd evenodd in
     (even 3, even 4) }>

theorem typechecks :
  <{ ∅ ⊢ ~eotest ⦂ Nat × Nat }> := by solution!(sorry)

:::gradeTheorem "0.5" typechecks
:::

theorem reduces :
  eotest ⟶* <{ (0, 1) }> := by solution!(sorry)

:::gradeTheorem "0.5" reduces
:::
  -/
```

:::dev "Daniel Sainati (@dsainati1)" BeforeNextRelease
Can't get this one to parse for some reason
:::

```lean
end Fix4
end Examples
```
:::::

# Properties of Typing

The proofs of progress and preservation for this enriched system
are essentially the same (though of course longer) as for the pure
STLC.

:::instructors
These need to be graded manually, because if
the relevant definitions aren't implemented above and below, then
the missing cases don't appear in the proofs.
:::

## Progress

::::exercise (rating := 3) (name := "STLCExtended.progress")

Complete the proof of `progress`

Theorem: Suppose `∅ ⊢ t ⦂ τ`.  Then either
  1. `t` is a value, or
  2. `t ⟶ t'` for some `t'`.

Proof: By induction on the given typing derivation.

```lean
theorem progress (t : Tm) (τ : Ty) (ht :<{ ∅ ⊢ ~t ⦂ ~τ }>) :
    t.IsValue ∨ exists t', t ⟶ t' := by
    solution!
      sorry
```
::::

## Weakening

The weakening claim is exactly the same as for the original STLC.

```lean
theorem weakening {Γ Γ' : Context} {t : Tm} {τ: Ty}
    (hi : Γ ⊆ Γ')
    (ht : <{ ~Γ ⊢ ~t ⦂ ~τ }>) :
     <{ ~Γ' ⊢ ~t ⦂ ~τ }> := by
  sorry
```

```lean
theorem weakening_empty (Γ : Context) (t : Tm) (τ: Ty)
    (ht :<{ ∅ ⊢ ~t ⦂ ~τ }>) :
    <{ ~Γ ⊢ ~t ⦂ ~τ }> := by
  apply weakening _ ht
  intro _ _ h
  rw [PartialMap.getElem_empty] at h
  contradiction
```

## Substitution

::::exercise (rating := 2) (name := "STLCExtended.substitution_preserves_typing")
Complete the proof of `substitution_preserves_typing`

```lean
theorem substitution_preserves_typing (Γ : Context) (x : String) (τ₁ : Ty) (t v : Tm) (τ : Ty)
    (ht : <{ ~x ↦ ~τ₁ ; ~Γ ⊢ ~t ⦂ ~τ }>)
    (hv : <{ ∅ ⊢ ~v ⦂ ~τ₁ }>) :
    <{ ~Γ ⊢ [~x := ~v] ~t ⦂ ~τ }> := by
  solution!
    sorry
```
::::

## Preservation


::::exercise (rating := 3) (name := "STLCExtended.preservation")
Complete the proof of `preservation`:

```lean
theorem preservation (t t' : Tm) (τ : Ty)
    (ht : <{ ∅ ⊢ ~t ⦂ ~τ }>)
    (he : t ⟶ t') :
    <{ ∅ ⊢ ~t' ⦂ ~τ }> := by
  solution!
    sorry
```
::::

```lean
end STLCExtended
```
