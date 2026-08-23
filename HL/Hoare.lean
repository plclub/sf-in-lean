import SFLMeta

import LF.CustomTactics
import HL.Imp

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Hoare: Hoare Logic, Part I" =>
%%%
tag := "Hoare"
htmlSplit := .never
file := some "Hoare"
%%%

:::instructors
In one 80-minute lecture, going at a moderate pace,
I (BCP) can easily cover up through the sequencing rule.  The
second lecture then covers the rest of this file and a bit of
Hoare2, with plenty of time for real-time clicker quizzes and
WORKINCLASS Rocq experiments (the students seemed to like these) and
one more lecture for Hoare2.

Covering both Hoare and Hoare2 in one week (two 80-minute lectures)
is possible but challenging.  Don't get bogged down in digressions!
:::

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2025)
There is an excellent and fairly polished problem
on a Hoare Logic for a little assembly language in the materials
for the 2025 CIS 5000 final exam at Penn. We should turn it into an
exercise in this chapter!
:::

:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement (year := 2025)
````
The concrete syntax in this chapter has been a long
and evolving project! The latest development in this saga is a big
round of improvements by Steve Zdancewic in 2024, with further
polishing in 2025 by Noé de Santo and others. I've tried to prune
back most of the notes-to-selves in this file, just leaving a few
for further exploration at some point...

 - BCP 23: I *think* Assertions should either just be boolean
   expressions or else they should be their own things with
   math-looking syntax.  But in any case it would be good to get
   rid of all the coercion stuff.

 - BCP 21: An interesting concrete syntax idea: maybe we could
    write triples as ```<{ {P} c {Q} }>``` instead of ```{{P}} c
    {{Q}}```.  Maybe this would be better, both in terms of keeping
    the standard notation, and in terms of keeping the "<{...}>
    around object-language syntax" convention. And it's the same
    number of characters. :-) (Fewer, in many circumstances,
    because when writing in comments or on the board we can leave
    off the outer brackets.)  We should try it.  BCP 23: Tried it.
    Was not able to push it all the way through, but this part
    seems promising.

 - BCP 21: We should try either dropping the rule of consequence
  completely or at least using it very seldom; instead, we should
  just include uses of implication in each rule.  This would (a) make
  the assignment rule, especially, MUCH easier to explain, and (b)
  better align with the next chapter.  (One reason this chapter is
  hard to explain is that the assignment rule is so rigid -- this
  forces us to state the first several of examples in a silly, rigid,
  confusing way.) BCP 23: I think this change is quite important.
  Should be given high priority.
  BCP 25: The SparseAnnotations material from Hoare2 is relevant!
````
:::

:::dev "Niklas Halonen (xhalo32)"
Reply to Benjamin's note above:
The way we do it now in Lean is to have a custom elaborater which avoids all the coercions plus doesn't need the syntax category for assertions.
:::

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2021)
Any chance we could move the (awkwardly placed)
weakest precondition discussion to this chapter instead?

The terse version of the chapter needs serious
work -- it has gotten quite ragged after a bunch of reorganization
of the chapter over the past couple years.  BCP 23: Did some work
on it.  Bit better now.  But the notation issues make everything a
bit heavy.
:::

:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement (year := 2019)
For the second midterm in the the 19fa instance of
CIS500, we did a little experiment with setting up a
total-correctness Hoare logic for Imp.  Would be fun to turn that
into either an extended exercise or perhaps a little chapter on its
own. I can give the .v file to anyone that wants. (It is
technically pretty complete but needs words and a couple more
examples.)
:::

:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement (year := 2020)
```
I really dislike beginning with assignment.  I know
we can't do any examples without it, but IMO the examples *with* it
are incomprehensible anyway! How about: skip, sequencing,
conditionals, assignment, consequence, and finally while?  BCP 21:
Partially implemented.  I didn't go as far as the rearrangement I
proposed last year, because it would have involved some substantial
rewriting, but I did at least move skip and ; to before assignment.
```
:::

:::dev
```
HIDE: What about typesetting multi-line triples as
{{ P }}
   c
{{ Q }}
instead of
  {{ P }}
c
  {{ Q }}
when we print them?
```

```
HIDE: At some point we should try one more time to see if it's
possible to use single curly braces for Hoare triples.  The Rocq
manual says "For the sake of factorization with Rocq predefined
rules, simple rules have to be observed for notations starting with
a symbol: e.g., rules starting with { or ( should be put at level
0."  Maybe this suggests a way forward...?
BCP 10/18: Nope.  Writing
   Notation "'{' P '}' c '{' Q '}'" :=
     (ValidHoareTriple P c Q) (at level 0, c at next level)
     : hoare_spec_scope.
yields
    Error: A notation must include at least one symbol.
```

HIDE: This file and all later ones should make a habit of always
presenting both syntax and semantics of new language constructs in
informal style as well as formal.  See MoreStlc.v for a
template.
:::

:::dev PotentialImprovement
```
in the HTML, consider changing the sizes of some symbols,
e.g. make ∀ bigger and make <<->> and ->> and ↦ smaller.
Check that both full and terse look good.
```
:::

::::full
In an {ref "Imp"}[earlier chapter], we began applying the mathematical tools
developed in the first part of the course to studying the theory
of a small programming language, Imp.

- We defined a type of _abstract syntax trees_ for Imp, together
  with an _evaluation relation_ (a partial function on states)
  that specifies the _operational semantics_ of programs.

  The language we defined, though small, captures some of the key
  features of full-blown languages like C, C++, and Java,
  including the fundamental notion of mutable state and some
  common control structures.

- We proved a number of _metatheoretic properties_ -- "meta" in
  the sense that they are properties of the language as a whole,
  rather than of particular programs in the language.  These
  included:

    - determinism of evaluation

    - equivalence of some different ways of writing down the
      definitions (e.g., functional and relational definitions of
      arithmetic expression evaluation)

    - guaranteed termination of certain classes of programs

    - correctness (in the sense of preserving meaning) of a number
      of useful program transformations

    - behavioral equivalence of programs (in the Equiv chapter).

If we stopped here, we would already have something useful: a set
of tools for defining and discussing programming languages and
language features that are mathematically precise, flexible, and
easy to work with, applied to a set of key properties.  All of
these properties are things that language designers, compiler
writers, and users might care about knowing.  Indeed, many of them
are so fundamental to our understanding of the programming
languages we deal with that we might not consciously recognize
them as "theorems."  But properties that seem intuitively obvious
can sometimes be quite subtle (sometimes also subtly wrong!).

In another volume of this series (_Type Systems_),
we expand upon the theme of metatheoretic properties of whole
languages when we discuss _types_ and _type
soundness_. In this chapter, though, we turn to a different set
of issues.
::::

Our goal in this chapter is to develop the tools to work through
some simple examples of _program verification_ -- i.e., to use the
precise definition of Imp to prove formally that particular
programs satisfy particular specifications of their behavior.

We'll develop a reasoning system called _Floyd-Hoare Logic_ --
often shortened to just _Hoare Logic_ -- in which each of the
syntactic constructs of Imp is equipped with a generic "proof
rule" that can be used to reason compositionally about the
correctness of programs involving this construct.

::::full
Hoare Logic originated in the 1960s, and it continues to be the
subject of intensive research right up to the present day.  It
lies at the core of a multitude of tools that are being used in
academia and industry to specify and verify real software systems.
::::

:::slidebreak
:::

Hoare Logic combines two beautiful ideas: a natural way of writing
down _specifications_ of programs, and a _structured proof
technique_ for proving that programs are correct with respect to
such specifications -- where by "structured" we mean that the
structure of proofs directly mirrors the structure of the programs
that they are about.

:::dev PotentialImprovement
Add some material talking about particular impressive
examples of program verification using successors of Hoare logic.
It would also be good to talk a little more about the history of
Hoare logic and give some pointers to good books (Esp. JCR's).
:::

:::dev
```
HIDE: MRC'20: The terse version used to start with just an outline of
what we've done and of this chapter, but it never mentioned Hoare logic!
The text above seems like a better intro.

MRC'20: this is the former terse intro.

 What we've done so far:

 - Formalized Imp
      - identifiers and states
      - abstract syntax trees
      - evaluation functions (for [aexp]s and [bexp]s)
      - evaluation relation (for commands)

 - Proved some _metatheoretic_ properties
     - determinism of evaluation
     - equivalence of some different ways of writing down the
       definitions (e.g., functional and relational definitions of
       arithmetic expression evaluation)
     - guaranteed termination of certain classes of programs
     - meaning-preservation of some program transformations
     - behavioral equivalence of programs ([Equiv])

 We've dealt with a few sorts of properties of Imp programs:
   - Termination
   - Nontermination
   - Equivalence

 Topic:
   - A systematic method for reasoning about the _functional
     correctness_ of programs in Imp

 Goals:
   - a natural notation for _program specifications_ and
   - a _compositional_ proof technique for program correctness

 Plan:
   - specifications (assertions / Hoare triples)
   - proof rules
   - loop invariants
   - decorated programs
   - examples
```
:::

# Assertions

An _assertion_ is a logical claim about the state of a program's
memory -- formally, a predicate of `State`s.

```lean
open scoped Com MyGetElem

abbrev Assertion := State → Prop
```

:::dev
HIDE: MRC'20: pulled up these examples from the quiz/optional
exercise so that there would be some modeling of the kinds of
answers we expect.
:::

For example,

- `fun st => st[X] = 3` holds for states `st` in which value of `X`
  is `3`,

- `fun st => True` hold for all states, and

- `fun st => False` holds for no states.

::::quiz
Paraphrase the following assertions in English (i.e., say
which states satisfy them)

(A) `fun st => st[X] ≤ st[Y]`

(B) `fun st => st[X] = 3 ∨ st[X] ≤ st[Y]`

(C) `fun st => st[Z] * st[Z] ≤ st[X] ∧ ¬ ((st[Z] + 1) * (st[Z] + 1) ≤ st[X])`
::::

::::::full
:::::exercise (rating := 1) (name := "assertions") (optional := true)
Paraphrase the following assertions in English (or your favorite
natural language).

```lean
namespace ExAssertions
def assertion1 : Assertion := fun st => st[X] ≤ st[Y]
def assertion2 : Assertion :=
  fun st => st[X] = 3 ∨ st[X] ≤ st[Y]
def assertion3 : Assertion :=
  fun st => st[Z] * st[Z] ≤ st[X] ∧
            ¬ ((st[Z] + 1) * (st[Z] + 1) ≤ st[X])
def assertion4 : Assertion :=
  fun st => st[Z] = max st[X] st[Y]
```

:::solution
1) The value of X is less or equal than the value of Y.
2) The value of X is 3 or is less or equal than the value of Y.
3) The value of Z is the integer square root of X.
4) The value of Z is the greater of the values of X and Y
:::

```lean
end ExAssertions
```
:::::

::::::

## Notations for Assertions

::::full
This way of writing assertions can be a little bit heavy,
for two reasons: (1) every single assertion that we ever write is
going to begin with `fun st => `; and (2) this state `st` is the
only one that we ever use to look up variables in assertions (we
will almost never need to talk about two different memory states at the
same time).  For discussing examples informally, we'll adopt some
simplifying conventions: we'll drop the initial `fun st =>`, and
we'll write just `X` to mean `st[X]`.  Thus, instead of writing

```display
fun st => st[X] = m
```

we'll write just

```display
{{ X = m }}.
```

Here the "doubly curly" braces `{{` and `}}` delimit
the scope of an assertion.  We'll see more examples below.
::::

::::terse
We'll use Lean's notation features to make assertions
look as much like informal math as possible.

For example, instead of writing

```display
fun st => st[X] = m
```

we'll usually write just

```display
{{ X = m }}
```
::::

::::full
This example also illustrates a convention that we'll use
throughout the Hoare Logic chapters: in informal assertions,
capital letters like `X`, `Y`, and `Z` are Imp variables, while
lowercase letters like `x`, `y`, `m`, and `n` are ordinary Lean
variables (of type `Nat`).  This is why, when translating from
informal to formal, we replace `X` with `st[X]` but leave `m`
alone.
::::

:::dev PotentialImprovement
Say more about that??
:::

:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement (year := 2018)
```
The following is a really good attempt (by
Li-Yao) to lighten the notation for assertions.  It hasn't quite
converged (e.g., we're not happy about [ap]), and there is an
uncomfortable amount of magic to it, but we should think about it
some more...

One thing to consider adding is turning bassertion into a coercion.
APT: I've tried that and it helps.

APT: Overall, I really like this new notation a LOT and I would
favor switching to it. Remainder of this chapter and Hoare2 are
converted to use it.

MRC'20: The notation is great in the Rocq source code!  Thanks for
all the hard work.  It makes almost everything much more pleasant
to read.  There are a couple further improvements that I wonder
about.  (I'm not qualified to do them!)

  1. It would help to have a bit of explanation of what's going on,
     even if it were just hidden for instructors.  I do confess I
     don't understand some of this implicit coercion magic, nor
     does the Rocq manual chapter on it read very easily for me.

  2. It's mysterious to me why sometimes I need to write
     [%assertion] or [: Assertion] to get parsing to work right.
     Some more explanation of that, with some examples to play
     with, would be nice.

  3. Though the notations look great in the Rocq source code, they
     work somewhat less well in the middle of a proof.  Rocq almost
     immediately starts expanding them in the proof state, and that
     gets confusing (to me and my students) rather quickly.  I
     wonder whether there's a way to make Rocq less aggressive about
     this?

APT'21: I fully agree that the expanded notations are not easy to
read. I think the coercions are the biggest reason for that, and
things would be a bit better if the coercions are used only for
input, i.e. we should add

  Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

[BCP 21: Added!]

This would be even better if we chose shorter names for the
coercions, e.g.  'lift_Prop', etc.

[BCP 21: Didn't do this yet -- had trouble deciding on nice short
names.  (E.g., 'lift_nat' is not so clear.)]
```
:::

:::dev BeforeNextRelease
RRand 2022: The coercion printing in recent updates is
making the Hoare logic statements we're aiming to prove essentially
unreadable. If the implicit coercions are too hard to deal with (I
don't see why they would be, given the number of coercion happening
here and in Imp) I would roll back to a previous version.  I cannot
read what's happening in my Rocq buffer.
:::

:::dev
```
HIDE: SAZ  2024: I'm confused by the above discussion.  Doesn't
[Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop]
request Rocq to _show_ those coercions?  I've removed it.
```

```
HIDE: SAZ 2024:
From what I can tell, the reason the notations expand during
the proofs is that they're writen in such a way that they
inlude type annotations [(a : Aexp)] and explicit lambdas
[(fun st => a st + b st)], neither of which is stable under
simplification.  For example:

 [(fun st =>
    (fun st => (X:Aexp) st + (Y:Aexp) st) st +
    (fun st => (Z:Aexp) st) st)]

Will print as [X + Y + Z] until simplification, at which point
we have [(fun st => st X + st Y + st Z)] but there is no notation
that covers this case.
```
:::

::::full
The convention described above can be implemented with a little
syntax magic, using coercions and a custom grammar, much as we did
with the `imp { … }` notation in {ref "Imp"}[Imp]. This new
notation automatically lifts `Aexp`s, numbers, and `Prop`s into
`Assertion`s when they appear between the `{{ _ }}` brackets, or
when Lean knows that the type of an expression is `Assertion`.

There is no need to understand the details of how these notations work.
::::

::::terse
Here, the `{{ A }}` brackets delimit the scope of the
assertion notation.
::::

:::dev
HIDE: Make things easily unfoldable.

HIDE: MRC'20: Recording this here because it took a merry chase through
the Rocq manual to find it:  this version of the `Arguments` command is
documented under `simpl`.
:::

:::dev "One An (meluge)"
The Rocq source here issues `Arguments assert_of_Prop /.` (and
likewise for the other two lifting functions) so that `simpl` always unfolds
them, with this instructors note: "These `Arguments` commands tell Rocq that
these functions should always be unfolded during simplification (by `simpl`)."

```
SAZ 2024 - Why do we want these functions to simplify?
Ans: If [a : aexp] then in the assertion_scope [(X →ₜ a st; st)] and
[(X →ₜ aeval st a; st)] look different but are actually identical
thanks to the coercion [Aexp_of_aexp].
```

Claude suggested `@[simp]`-tagged characterizing
lemmas next to the three lifting functions, a global simp attribute means
every `simp` unfolds applied occurrences. Is there a better way?
:::

:::dev
NOTATION: BCP 20: It probably makes sense now to put all these in a
custom grammar, so that we can really control how it looks and get
rid of things like ap.

```
NOTATION: SAZ 2024: I have tried to implement the suggestion above.

There is now a custom entry [assn] for defining the syntax of
assertions.  Like the delimiters <{ }> used for Imp programs,
we now also have {{ }} delimiters for use with Assertions.

Inside that scope, variables, arithmetic and boolean expressions,
propositions, and function arguments are interpreted in the current
state.  This replaces the need for [ap], [ap2], and explicit lifting
markers.

A raw Lean assertion can also be written directly inside {{ }}.
```
:::

:::instructors
The `{{ }}` syntax has `lead` precedence since otherwise it leads to some conflicts with triples.
This has the downside that assertions need to be wrapped in `()` parentheses when passed as arguments.
:::

```lean
namespace Assertion

section
open Lean Elab Term

scoped syntax:max (name := assn) "assn(" ident "; " term ")" : term
scoped syntax:lead "{{" term "}}" : term

@[term_elab assn]
def assnElab : TermElab := fun stx _type? => do
  match stx with
  | `(assn($st; $t:term)) =>
    let t ← elabTerm t none
    let ty ← Meta.inferType t
    -- if (← Meta.isDefEq ty (mkConst ``_root_.Ident)) then -- this incorrectly assigns metavariables
    if (ty.constName == ``_root_.Ident) then
      return mkApp6 (mkConst ``_root_.MyGetElem.getElem)
        (mkApp2 (mkConst ``TotalMap) (mkConst ``String) (mkConst ``Nat))
        (mkConst ``String)
        (mkConst ``Nat)
        (← Meta.synthInstance <| mkApp3 (mkConst ``_root_.MyGetElem)
          (mkApp2 (mkConst ``TotalMap) (mkConst ``String) (mkConst ``Nat))
          (mkConst ``String)
          (mkConst ``Nat))
        (← elabTerm st none) t
    if (ty.constName == ``_root_.Aexp) then -- Detect an embedded `Aexp` and turn it into `Aexp.eval st t`
      return (mkApp2 (mkConst ``Aexp.eval) (← elabTerm st none) t)
    else if (ty.constName == ``_root_.Bexp) then  -- Detect an embedded `Bexp` and turn it into `Bexp.eval st t`
      return (mkApp2 (mkConst ``Bexp.eval) (← elabTerm st none) t)
    else if ty.isMVar then -- This is a hack to guard against `Meta.isDefEq` assigning the type to be an `Assertion`
      return t
    else if (← Meta.isDefEq ty (mkConst ``_root_.Assertion)) then
      return mkApp t (← elabTerm st none)
    else
      return t
  | _ => throwUnsupportedSyntax

-- `: Assertion` guards that the resulting type is `State → Prop`.
macro_rules
  | `({{ $t }}) => `((fun st : _root_.State => assn(st; $t) : Assertion))

macro_rules
  | `(assn($st; ($P))) => ``((assn($st; $P)))
  | `(assn($st; $l = $r)) => ``(assn($st; $l) = assn($st; $r))
  | `(assn($st; $l + $r)) => ``(assn($st; $l) + assn($st; $r))
  | `(assn($st; $l - $r)) => ``(assn($st; $l) - assn($st; $r))
  | `(assn($st; $l * $r)) => ``(assn($st; $l) * assn($st; $r))
  | `(assn($st; $l ≤ $r)) => ``(assn($st; $l) ≤ assn($st; $r))
  | `(assn($st; $l < $r)) => ``(assn($st; $l) < assn($st; $r))
  | `(assn($st; $l ≥ $r)) => ``(assn($st; $l) ≥ assn($st; $r))
  | `(assn($st; $l > $r)) => ``(assn($st; $l) > assn($st; $r))
  | `(assn($st; $l ∧ $r)) => ``(assn($st; $l) ∧ assn($st; $r))
  | `(assn($st; $l ∨ $r)) => ``(assn($st; $l) ∨ assn($st; $r))
  | `(assn($st; $l → $r)) => ``(assn($st; $l) → assn($st; $r))
  | `(assn($st; $l ↔ $r)) => ``(assn($st; $l) ↔ assn($st; $r))
  | `(assn($st; ¬ $t)) => ``(¬ assn($st; $t))
  | `(assn($st; $f $args*)) => do
    let mut result := f
    for arg in args do
      result ← `($result assn($st; $arg))
    return result
end
```

:::dev "Niklas Halonen"
Mention (don't explain macro hygiene though) why
```
#check {{ st[X] = st[Y] }}
```
doesn't work, but instead one should write
```
#check {{ fun st => st[X] = st[Y] }}
```

And mention that when inside the brackets, one sees in the infoview
```
st✝ : State
```
but outside the brackets, one sees `fun st => st[X] = st[X] : State → Prop`

Also: should we introduce the terminology "pure" for embedding propositions into assertions that are constant functions?
:::

```lean
#check {{ 1 = 2 }}
#check {{ X = X }}
#check {{ X = 2 * X }} -- X is the constant "X" defined in Imp
#check_failure {{ X }} -- fails as expected
#check {{ True }}

#check {{ fun st => st[X] = st[Y] }}

variable (a : Aexp)
#check {{ X = a }}

variable (b : Bexp)
#check {{ b }}
#check {{ ¬ b }}
#check {{ b ∧ b }}

variable (P Q : Assertion)
#check {{ P ∧ Q }}

variable (f : Nat → Nat → Nat → Nat)
#check {{ f X Y X = 0 }}

end Assertion
open scoped Assertion
```

::::terse
Function applications inside assertions automatically interpret their
arguments in the current state:

`{{ f e1 ... en }}` stands for `(fun st => f (e1 st) ... (en st))`.
::::

::::full
Function applications inside assertions automatically interpret their
arguments in the current state.  Thus, `{{ f e1 ... en }}` stands for
`fun st => f (e1 st) ... (en st)`.
::::

::::full
Occasionally it is simpler to write an assertion directly as a Lean
function.  Such a function can be placed inside the assertion notation
without an escape marker.

For example, `{{ fun st => ∀ x, st[x] = 0 }}` indicates an assertion that
every variable maps to `0` in the given state.
::::

::::terse
We can place a raw Lean function directly inside assertion notation:

For example: `{{ fun st => ∀ x, st[x] = 0 }}`
::::

## Example Assertions

::::full
Here are some example assertions that take advantage of this
new notation.
::::

```lean
namespace ExamplePrettyAssertions

def assertion1 : Assertion := {{ X = 3 }}
def assertion2 : Assertion := {{ True }}
def assertion3 : Assertion := {{ False }}
def assertion4 : Assertion := {{ True ∨ False }}
def assertion5 : Assertion := {{ X ≤ Y }}
def assertion6 : Assertion := {{ X = 3 ∨ X ≤ Y }}
def assertion7 : Assertion := {{ Z = max X Y }}
def assertion8 : Assertion := {{ Z * Z ≤ X
                                 ∧ ¬ (((Nat.succ Z) * (Nat.succ Z)) ≤ X) }}
def assertion9 : Assertion := {{ Nat.add X Y > max Y X }}
variable {xs : List Nat}
-- #check {{ xs = X }}
/--
info: def ExamplePrettyAssertions.assertion8 : Assertion :=
fun st => st[Z] * st[Z] ≤ st[X] ∧ ¬st[Z].succ * st[Z].succ ≤ st[X]
-/
#guard_msgs in
#print assertion8

end ExamplePrettyAssertions
```

## Printing Assertions
%%%
tag := "assn-delaborators"
%%%

::::full
As in the {ref "imp-delaborators"}[Imp chapter], the assertion notation
above is _input_ only: Lean reads `{{ X ≤ 5 }}` but still prints the
underlying function, as `#print assertion8` just showed.  The delaborators
below close the loop for plain assertions: a state lambda whose body Lean
can rebuild is printed back in `{{ … }}` notation, and an assertion Lean
cannot rebuild falls back to the raw `fun st => …` form, which is exactly
this notation's escape syntax, so what you see is always valid input.  Each
time a new notation involving assertions appears below (implication, Hoare
triples, substitution), a small delaborator defined next to it will extend
this printing to cover it.  As before, there is no need to understand the
details.
::::

::::details "Notation encoding: printing assertions back"
```lean
namespace Assertion.Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Delab

/-- Rebuild the surface form of an assertion body, undoing the state
threading the `assn` elaborator performs: `st[X]` prints as `X`,
`Aexp.eval st a` as `a`, `Bexp.eval st b = true` as `b`, an applied
assertion `P st` as `P`, and a subterm that does not mention the state
prints as itself. -/
partial def delabBody (stId : FVarId) : DelabM Term := do
  let e ← getExpr
  if !e.containsFVar stId then
    delab
  else
    match_expr e with
    | MyGetElem.getElem _ _ _ _ st _ =>
      guard (st == .fvar stId)
      withNaryArg 5 delab
    | Aexp.eval st _ =>
      guard (st == .fvar stId)
      withAppArg delab
    | HAdd.hAdd _ _ _ _ _ _ =>
      `($(← withNaryArg 4 (delabBody stId)) + $(← withNaryArg 5 (delabBody stId)))
    | HSub.hSub _ _ _ _ _ _ =>
      `($(← withNaryArg 4 (delabBody stId)) - $(← withNaryArg 5 (delabBody stId)))
    | HMul.hMul _ _ _ _ _ _ =>
      `($(← withNaryArg 4 (delabBody stId)) * $(← withNaryArg 5 (delabBody stId)))
    | Eq _ l r =>
      -- `Bexp.eval st b = true` is the threaded form of a bare boolean `b`
      if r.isConstOf ``Bool.true && l.isAppOfArity ``Bexp.eval 2
          && l.appFn!.appArg! == .fvar stId then
        withNaryArg 1 <| withAppArg delab
      else
        `($(← withNaryArg 1 (delabBody stId)) = $(← withNaryArg 2 (delabBody stId)))
    | Ne _ _ _ =>
      `($(← withNaryArg 1 (delabBody stId)) ≠ $(← withNaryArg 2 (delabBody stId)))
    | LE.le _ _ _ _ =>
      `($(← withNaryArg 2 (delabBody stId)) ≤ $(← withNaryArg 3 (delabBody stId)))
    | LT.lt _ _ _ _ =>
      `($(← withNaryArg 2 (delabBody stId)) < $(← withNaryArg 3 (delabBody stId)))
    | GE.ge _ _ _ _ =>
      `($(← withNaryArg 2 (delabBody stId)) ≥ $(← withNaryArg 3 (delabBody stId)))
    | GT.gt _ _ _ _ =>
      `($(← withNaryArg 2 (delabBody stId)) > $(← withNaryArg 3 (delabBody stId)))
    | And _ _ =>
      `($(← withNaryArg 0 (delabBody stId)) ∧ $(← withNaryArg 1 (delabBody stId)))
    | Or _ _ =>
      `($(← withNaryArg 0 (delabBody stId)) ∨ $(← withNaryArg 1 (delabBody stId)))
    | Iff _ _ =>
      `($(← withNaryArg 0 (delabBody stId)) ↔ $(← withNaryArg 1 (delabBody stId)))
    | Not _ =>
      `(¬ $(← withAppArg (delabBody stId)))
    | _ =>
      if e.isArrow then
        `($(← withBindingDomain (delabBody stId)) →
          $(← withBindingBody `h (delabBody stId)))
      else if let .app f v := e then
        -- an applied assertion `P st` (or an applied escape lambda)
        guard (v == .fvar stId)
        guard !(f.containsFVar stId)
        withAppFn delab
      else
        failure

/-- Print an `Assertion`-valued term as it appears inside `{{ … }}`: a
state lambda is un-threaded; a term the printer cannot rebuild falls back
to the raw lambda, which is exactly this notation's escape form. -/
partial def delabAssn : DelabM Term := do
  if (← getExpr).isLambda then
    (withBindingBody' `st (pure ·.fvarId!) fun stId => delabBody stId)
      <|> Delaborator.delab
  else
    delab

/-- Print an assertion-position argument: a state lambda gets the
`{{ … }}` notation; any other term (a named assertion, a substitution)
already reads well bare. -/
def delabAssnArg (i : Nat) : DelabM Term := do
  if (← withNaryArg i getExpr).isLambda then
    `({{ $(← withNaryArg i delabAssn) }})
  else
    withNaryArg i Delaborator.delab

/-- Print a bare assertion lambda in `{{ … }}` notation.  Keyed on lambdas
at large, so the guards bail out cheaply unless the binder is a `State`
and the body is a proposition the printer can rebuild. -/
@[delab lam]
def delabAssertion : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.isLambda && e.bindingDomain!.isConstOf ``_root_.State
  let P ← withBindingBody' `st (pure ·.fvarId!) fun stId => do
    guard (← Meta.inferType (← getExpr)).isProp
    delabBody stId
  `({{ $P }})

end Assertion.Delab
```
::::

:::ignore
```lean -show
/-- info: {{X = 3 ∨ X ≤ Y}} : State → Prop -/
#guard_msgs in
#check {{ X = 3 ∨ X ≤ Y }}
```
:::

## Assertion Implication

Given two assertions `P` and `Q`, we say that `P` _implies_ `Q`,
written `P ->> Q`, if, whenever `P` holds in some state `st`, `Q`
also holds.

```lean
def AssertImplies (P Q : Assertion) : Prop :=
  ∀ st, P st → Q st
```

:::instructors
`AssertImplies` (unlike `ValidHoareTriple`) is semireducible on purpose: when we use the `apply_rules` tactic, it needs to see through the definition.
:::

Note that the notation for _assertion implication_ is analogous
to the "usual" Lean implication `→`.

```lean
notation:26 P:27 " ->> " Q:27 => AssertImplies P Q

theorem assertImplies_def {P Q : Assertion} : P ->> Q ↔ ∀ st, P st → Q st := by rfl
```

We'll also want the "iff" variant of implication between
assertions:

```lean
notation:26 P:27 " <<->> " Q:27 => AssertImplies P Q ∧ AssertImplies Q P

theorem assertIff_def {P Q : Assertion} : P <<->> Q ↔ AssertImplies P Q ∧ AssertImplies Q P
    := by rfl
```

::::full
The matching delaborators print implications and equivalences between
assertions back in `->>` and `<<->>` notation.
::::

::::details "Notation encoding: printing implications back"
```lean
namespace Assertion.Delab
open Lean PrettyPrinter Delaborator SubExpr

@[delab app.AssertImplies]
def delabAssertImplies : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``AssertImplies 2
  `($(← delabAssnArg 0) ->> $(← delabAssnArg 1))

/-- `<<->>` abbreviates a conjunction of two `AssertImplies`, so its
delaborator is keyed on `∧` and bails out unless the two conjuncts mirror
each other. -/
@[delab app.And]
def delabAssertIff : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.isAppOfArity ``And 2
  let l := e.appFn!.appArg!
  let r := e.appArg!
  guard <| l.isAppOfArity ``AssertImplies 2 && r.isAppOfArity ``AssertImplies 2
  guard <| l.appFn!.appArg! == r.appArg! && l.appArg! == r.appFn!.appArg!
  `($(← withNaryArg 0 <| delabAssnArg 0) <<->> $(← withNaryArg 0 <| delabAssnArg 1))

end Assertion.Delab
```
::::

:::ignore
```lean -show
/-- info: {{X < 4}} ->> {{X < 5}} : Prop -/
#guard_msgs in
#check ({{ X < 4 }} ->> {{ X < 5 }})

/-- info: {{X < 4}} <<->> {{X < 5}} : Prop -/
#guard_msgs in
#check ({{ X < 4 }} <<->> {{ X < 5 }})
```
:::

# Hoare Triples, Informally

A _Hoare triple_ is a claim about the state before and after executing a command.
A commond notation for Hoare triples, and the one we use in this book, is

```display
{{P}} c {{Q}}
```

meaning:

  - If command `c` begins execution in a state satisfying assertion `P`,
  - and if `c` eventually terminates in some final state,
  - then that final state will satisfy the assertion `Q`.

Assertion `P` is called the _precondition_ of the triple, and `Q` is
the _postcondition_.


:::slidebreak
:::

For example,

- The Hoare triple

```display
{{X = 0}} X := X + 1 {{X = 1}}
```

  states that command `X := X + 1` will transform a state in
  which `X = 0` to a state in which `X = 1`.

- On the other hand,

```display
∀ m, {{X = m}} X := X + 1 {{X = m + 1}}
```

is a _proposition_ stating that the Hoare triple `{{X = m}} X :=
X + 1 {{X = m + 1}}` is valid for any choice of `m`.  Note that
`m` in the two assertions is a reference to the _Lean_ variable
`m`, which is bound outside the Hoare triple.


::::quiz
Paraphrase the following in English.

```display
1) {{True}} c {{X = 5}}

2) ∀ m, {{X = m}} c {{X = m + 5}}

3) {{X ≤ Y}} c {{Y ≤ X}}

4) {{True}} c {{False}}

5) ∀ m,
     {{X = m}}
     c
     {{Y = real_fact m}}

6) ∀ m,
     {{X = m}}
     c
     {{(Z * Z) ≤ m ∧ ¬ ((Z + 1) * (Z + 1) ≤ m)}}
```

:::quizSolution
1) If command c terminates starting in an arbitrary state it produces a
   state where the value of X is equal to 5.
2) Starting in a state where the value of X is m, if c terminates the
   value of X is equal to m+5.
3) Starting in a state where the value of X less or equal than the
   value of Y, if c terminates then the value of Y is less or equal
   than the value of X.
4) c doesn't terminate on any starting state
5) If c terminates then Y contains as a value the factorial of the
   initial value of X.
6) If c terminates starting in a state in which the value of X is equal to,
   then Z contains the integer square root of the initial value of X.
:::
::::

::::quiz
Is the following Hoare triple _valid_ -- i.e., is the
claimed relation between `P`, `c`, and `Q` true?

```display
{{True}} X := 5 {{X = 5}}
```

(A) Yes

(B) No
::::

::::quiz
What about this one?

```display
{{X = 2}} X := X + 1 {{X = 3}}
```

(A) Yes

(B) No
::::

::::quiz
What about this one?

```display
{{True}} X := 5; Y := 0 {{X = 5}}
```

(A) Yes

(B) No
::::

::::quiz
What about this one?

```display
{{X = 2 ∧ X = 3}} X := 5 {{X = 0}}
```

(A) Yes

(B) No
::::

::::quiz
What about this one?

```display
{{True}} skip {{False}}
```

(A) Yes

(B) No
::::

::::quiz
What about this one?

```display
{{False}} skip {{True}}
```

(A) Yes

(B) No
::::

::::quiz
What about this one?

```display
{{True}} while true do skip end {{False}}
```

(A) Yes

(B) No
::::

::::quiz
This one?

```display
{{X = 0}}
  while X = 0 do X := X + 1 end
{{X = 1}}
```

(A) Yes

(B) No
::::

::::quiz
This one?

```display
{{X = 1}}
  while X ≠ 0 do X := X + 1 end
{{X = 100}}
```

(A) Yes

(B) No
::::

:::instructors
SOLUTION: All are valid except the 5th.
:::

::::::full
:::::exercise (rating := 1) (name := "valid_triples") (optional := true)
Which of the following Hoare triples are _valid_ -- i.e., the
claimed relation between `P`, `c`, and `Q` is true?

```display
1) {{True}} X := 5 {{X = 5}}

2) {{X = 2}} X := X + 1 {{X = 3}}

3) {{True}} X := 5; Y := 0 {{X = 5}}

4) {{X = 2 ∧ X = 3}} X := 5 {{X = 0}}

5) {{True}} skip {{False}}

6) {{False}} skip {{True}}

7) {{True}} while true do skip end {{False}}

8) {{X = 0}}
    while X = 0 do X := X + 1 end
  {{X = 1}}

9) {{X = 1}}
    while X ≠ 0 do X := X + 1 end
  {{X = 100}}
```

:::solution
All are valid except the 5th.
:::
:::::

::::::

# Hoare Triples, Formally

We formalize valid Hoare triples in Lean as follows:

```lean
open scoped HasEval

def ValidHoareTriple
    (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ {st st' : State},
    (st =[ c ]=> st') →
    P st →
    Q st'
```

:::dev "Niklas Halonen (xhalo32)"
Somethings strange is going on in `theorem if_example`, using `apply hoare_consequence_pre` followed by `· exact hoare_asgn` works, but `refine hoare_consequence_pre hoare_asgn ?_` or `apply hoare_consequence_pre hoare_asgn` don't.
The only solution I found was to mark `ValidHoareTriple` irreducible.

It has to do something with `apply` and `refine` looking inside the implication in `∀ {st st'}, ...`
:::

Notation for Hoare triples.  The command between the two assertions is
parsed with the same grammar as the `imp { … }` notation, so a command
that is a Lean variable (rather than concrete syntax) is spliced in with
`~c`, just as in the `st =[ c ]=> st'` notation.

:::instructors
This pattern of a generic notation with a notation typeclass plus a category-specific variant is from {name}`HasEval` in Imp.
It's a bit more complicated since `{{ }}`-notation is already used for assertions.

Since identifiers are terms and also in `imp_com`, we must mark the `imp_com` version with `priority := high`, otherwise e.g. `skip` is elaborated as a regular identifier.
:::

```lean
class HasTriple (Com : Type) where
  Triple : Assertion → Com → Assertion → Prop

namespace HasTriple

/-- Hoare triple: `{{ P }} c {{ Q }}` -/
scoped notation:lead "{{" P "}} " c:lead " {{" Q "}}" => Triple ({{ P }}) c ({{ Q }})

/-- Hoare triple with `imp_com` command syntax -/
scoped syntax:lead (priority := high) "{{" term "}} " imp_com:lead " {{" term "}}" : term
scoped macro_rules
  | `({{ $P }} $c:imp_com {{ $Q }}) =>
      ``(HasTriple.Triple ({{ $P }}) (imp { $c }) ({{ $Q }}))
end HasTriple

instance : HasTriple Com where
  Triple := ValidHoareTriple

open scoped HasTriple

theorem validHoareTriple_def {P : Assertion} {c : Com} {Q : Assertion} :
    {{ P }} ~c {{ Q }} ↔ ∀ {st st' : State},
      (st =[ c ]=> st') →
      P st →
      Q st' := by rfl

attribute [irreducible] ValidHoareTriple
```

::::hide
```lean
#check ({{ True }} skip {{ False }})
#check ({{ True }} X := 0 {{ False }})
#check ∀ c : Com, ({{ True }} ~c {{ False }})
```
::::

::::details "Notation encoding: printing triples back"
The delaborator is agnostic to the command type: it prints the command with
whatever printer is registered for its constructors and splices the result
into the triple, so a language-extension chapter only has to register a
printer for its own `Com`.
```lean
namespace Assertion.Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Delab
@[delab app.HasTriple.Triple]
def delabTriple : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``HasTriple.Triple 5
  let P ← withNaryArg 2 delabAssn
  let c ← withNaryArg 3 delab
  let Q ← withNaryArg 4 delabAssn
  match c with
  | `(imp { $c:imp_com }) => ``({{ $P }} $c:imp_com {{ $Q }})
  | c => ``({{ $P }} ~$c {{ $Q }})

end Assertion.Delab
```
::::

:::ignore
```lean -show
/-- info: {{X ≤ 5}} X := X + 1 {{X ≤ 7}} : Prop -/
#guard_msgs in
#check {{ X ≤ 5 }} X := X + 1 {{ X ≤ 7 }}

/--
info: {{X ≤ 5}}
  X := X;
  Y := Y {{X ≤ 7}} : Prop
-/
#guard_msgs in
#check {{ X ≤ 5 }} X := X; Y := Y {{ X ≤ 7 }}
```
:::

:::dev "Niklas Halonen (xhalo32)"
Is it possible to add a line break after the `Y := Y`?
:::

:::::exercise (rating := 1) (name := "hoare_post_true")
Prove that if `Q` holds in every state, then any triple with `Q`
as its postcondition is valid.

```lean
theorem hoare_post_true {P Q : Assertion} {c : Com} (h : ∀ st, Q st) :
    {{ P }} ~c {{ Q }} := by
  solution!
    rw [validHoareTriple_def]
    intro st st' hc hpre
    exact h st'
```
:::::

:::::exercise (rating := 1) (name := "hoare_pre_false") (optional := true)
Prove that if `P` holds in no state, then any triple with `P` as
its precondition is valid.

```lean
theorem hoare_pre_false {P Q : Assertion} {c : Com} (h : ∀ st, ¬ (P st)) :
    {{ P }} ~c {{ Q }} := by
  solution!
    rw [validHoareTriple_def]
    intro st st' hc hpre
    specialize h st
    contradiction
```
:::::

# Proof Rules

::::full
The goal of Hoare logic is to provide a _compositional_
method for proving the validity of specific Hoare triples.  That
is, we want the structure of a program's correctness proof to
mirror the structure of the program itself.  To this end, in the
sections below, we'll introduce a rule for reasoning about each of
the different syntactic forms of commands in Imp -- one for
assignment, one for sequencing, one for conditionals, etc. -- plus
a couple of "structural" rules for gluing things together.  We
will then be able to prove programs correct using these proof
rules, without ever unfolding the definition of `ValidHoareTriple`.
::::

::::terse
We want to be able to _prove_ Hoare triples formally.

Here's our plan:
  - introduce one "proof rule" for each Imp syntactic form
  - plus a couple of "structural rules" that help glue proofs
    together
  - prove these rules correct in terms of the definition of
    `ValidHoareTriple`
  - prove programs correct using these proof rules, without ever
    unfolding the definition of `ValidHoareTriple`
::::

## Skip

Since `skip` doesn't change the state, it preserves any
assertion `P`:

```display
--------------------  (hoare_skip)
{{ P }} skip {{ P }}
```

```lean
theorem hoare_skip {P : Assertion} :
    {{ P }} skip {{ P }} := by
  rw [validHoareTriple_def]
  intro st st' h hpre
  inversion h
  exact hpre
```

## Sequencing

If command `c1` takes any state where `P` holds to a state where
`Q` holds, and if `c2` takes any state where `Q` holds to one
where `R` holds, then doing `c1` followed by `c2` will take any
state where `P` holds to one where `R` holds:

```display
 {{ P }} c1 {{ Q }}
 {{ Q }} c2 {{ R }}
----------------------  (hoare_seq)
{{ P }} c1; c2 {{ R }}
```

```lean
theorem hoare_seq {P Q R : Assertion} {c1 c2 : Com}
    (h1 : {{ Q }} ~c2 {{ R }}) (h2 : {{ P }} ~c1 {{ Q }}) :
    {{ P }} ~c1; ~c2 {{ R }} := by
  rw [validHoareTriple_def]
  intro st st' h hpre
  inversion h with
  | seq st'' hc1 hc2 =>
    rw [validHoareTriple_def] at h1 h2
    exact h1 hc2 (h2 hc1 hpre)
```

::::full
Note that, in the formal rule `hoare_seq`, the premises are
given in backwards order (`c2` before `c1`).  This matches the
natural flow of information in many of the situations where we'll
use the rule, since the natural way to construct a Hoare-logic
proof is to begin at the end of the program (with the final
postcondition) and push postconditions backwards through commands
until we reach the beginning.
::::

## Assignment

::::full
The rule for assignment is the most fundamental of the Hoare
logic proof rules.  Here's how it works.

Consider this incomplete Hoare triple:

```display
{{ ??? }}  X := Y  {{ X = 1 }}
```

We want to assign `Y` to `X` and finish in a state where `X` is `1`.
What could the precondition be?

One possibility is `Y = 1`, because if `Y` is already `1` then
assigning it to `X` causes `X` to be `1`.  That leads to a valid
Hoare triple:

```display
{{ Y = 1 }}  X := Y  {{ X = 1 }}
```

It may seem as though coming up with that precondition must have
taken some clever thought.  But there is a mechanical way we could
have done it: if we take the postcondition `X = 1` and in it
replace `X` with `Y`---that is, replace the left-hand side of the
assignment statement with the right-hand side---we get the
precondition, `Y = 1`.
::::

::::terse
How can we complete this triple?

```display
{{ ??? }}  X := Y  {{ X = 1 }}
```

One natural possibility is:

```display
{{ Y = 1 }}  X := Y  {{ X = 1 }}
```

The precondition is just the postcondition, but with `X` replaced
by `Y`.
::::

::::full
That same idea works in more complicated cases.  For
example:

```display
{{ ??? }}  X := X + Y  {{ X = 1 }}
```

If we replace the `X` in `X = 1` with `X + Y`, we get `X + Y = 1`.
That again leads to a valid Hoare triple:

```display
{{ X + Y = 1 }}  X := X + Y  {{ X = 1 }}
```

Why does this technique work?  The postcondition identifies some
property `P` that we want to hold of the variable `X` being
assigned.  In this case, `P` is "equals `1`".  To complete the
triple and make it valid, we need to identify a precondition that
guarantees that property will hold of `X`.  Such a precondition
must ensure that the same property holds of _whatever is being
assigned to_ `X`.  So, in the example, we need "equals `1`" to
hold of `X + Y`.  That's exactly what the technique guarantees.
::::

:::slidebreak
:::

::::terse
How about this one?

```display
{{ ??? }}  X := X + Y  {{ X = 1 }}
```

Replace `X` with `X + Y`:

```display
{{ X + Y = 1 }}  X := X + Y  {{ X = 1 }}
```

This works because "equals 1" holding of `X` is guaranteed
by the property "equals 1" holding of whatever is being
assigned to `X`.
::::

:::slidebreak
:::

In general, the postcondition could be some arbitrary assertion
`Q`, and the right-hand side of the assignment could be some
arbitrary arithmetic expression `a`:

```display
{{ ??? }}  X := a  {{ Q }}
```

The precondition would then be `Q`, but with any occurrences of
`X` in it replaced by `a`.

:::slidebreak
:::

Let's introduce a notation for this idea of replacing occurrences:
Define `Q \[X ↦ a`\] to mean "`Q` where `a` is substituted in
place of `X`".

This yields the Hoare logic rule for assignment:

```display
{{ Q [X ↦ a] }}  X := a  {{ Q }}
```

One way of reading this rule is: If you want statement `X := a`
to terminate in a state that satisfies assertion `Q`, then it
suffices to start in a state that also satisfies `Q`, except
where `a` is substituted for every occurrence of `X`.

::::full
To many people, this rule seems "backwards" at first, because
it proceeds from the postcondition to the precondition.  Actually
it makes good sense to go in this direction: the postcondition is
often what is more important, because it characterizes what will be
true after running the code.

Nonetheless, it's also possible to formulate a "forward" assignment
rule.  We'll do that later in some exercises.
::::

:::slidebreak
:::

Here are some valid instances of the assignment rule:

```display
{{ (X ≤ 5) [X ↦ X + 1] }}         (that is, X + 1 ≤ 5)
  X := X + 1
{{ X ≤ 5 }}

{{ (X = 3) [X ↦ 3] }}              (that is, 3 = 3)
  X := 3
{{ X = 3 }}

{{ (0 ≤ X ∧ X ≤ 5) [X ↦ 3] }}.  (that is, 0 ≤ 3 ∧ 3 ≤ 5)
  X := 3
{{ 0 ≤ X ∧ X ≤ 5 }}
```

:::slidebreak
:::

To formalize the rule, we must first formalize the idea of
"substituting an expression for an Imp variable in an assertion",
which we refer to as assertion substitution, or `Assertion.subst`.

Intuitively, given a proposition `P`, a variable `X`, and an
arithmetic expression `a`, we want to derive another proposition
`P'` that is just the same as `P` except that `P'` should mention
`a` wherever `P` mentions `X`.

:::slidebreak
:::

This operation is related to the idea of substituting Imp
expressions for Imp variables that we saw in _Equiv_
(`subst_aexp` and friends). The difference is that, here,
`P` is an arbitrary Lean assertion, so we can't directly
"edit" its text.

:::slidebreak
:::

However, we can achieve the same effect by evaluating `P` in an
updated state, defined as follows:

```lean
def Assertion.subst (x : Ident) (a : Aexp) (P : Assertion) : Assertion :=
  fun (st : State) => P (x →ₜ a.eval st ; st)
```

:::dev PotentialImprovement
This concrete syntax is hard to read in comments because of
all the square brackets. Something like `P with X ↦ a` would be
much better. I guess the same will apply to the lambda-calculus
chapters...  BCP 25: I still think this is a good idea, and I had
a quick go at implementing it, but did not succeed yet.
:::

:::dev "One An @meluge" BeforeNextRelease
Introduce a notation typeclass for this (e.g. HasSubst)
:::

:::dev "Niklas Halonen (xhalo32)" PotentialImprovement
A lot of the substitutions use `[x ↦ ~a]`. Could we have syntax support for `[x ↦ a]`. A naive approach that adds `" [" ident " ↦ " term "]" ` leads to ambiguity.
:::

```lean
namespace Assertion

/-- Assertion substitution, written inside the braces: `{{ (P) [X ↦ a] }}`.
The substituted assertion is re-read with the same notation, so Imp
variables in it mean state lookups as usual; a named assertion is passed
through directly. -/
scoped syntax:max term:arg " [" ident " ↦ " imp_aexp "]" : term

macro_rules
  | `(assn($st; $P [$x ↦ $a:imp_aexp])) =>
    match P with
    | `($_:ident) => ``(Assertion.subst $x (aexp { $a }) $P $st)
    | _ => ``(Assertion.subst $x (aexp { $a }) ({{ $P }}) $st)

theorem subst_def {x : Ident} {a : Aexp} {P : Assertion} :
    Assertion.subst x a P = fun (st : State) => P (x →ₜ a.eval st ; st) := by rfl

@[simp]
theorem subst_apply {x : Ident} {a : Aexp} {P : Assertion} {st : State} :
    Assertion.subst x a P st ↔ P (x →ₜ a.eval st ; st) := by rfl

end Assertion
```

This notation allows us to write this operation as:

```display
P [ X ↦ a ]
```

```lean
#check (fun st => Assertion.subst X (aexp { 2 * X }) ({{ X ≤ 10 }}) st)
#check {{ (X ≤ 10) [X ↦ 2 * X] }}
#check (∀ st, ({{ (X ≤ 10) [X ↦ 2 * X] }}) st)
```

::::details "Notation encoding: printing substitutions back"
```lean
namespace Assertion.Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Delab

/-- Print an `Assertion.subst` back in `P [x ↦ a]` notation.  Emits the
bare inside-the-braces form: the generic application case of `delabBody`
picks it up inside an assertion body, and the enclosing printer supplies
the single pair of braces. -/
@[delab app.Assertion.subst]
def delabSub : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``Assertion.subst 3
  let `($x:ident) ← withNaryArg 0 delab | failure
  let a ← withNaryArg 1 delabAexpInner
  if (← withNaryArg 2 getExpr).isLambda then
    `(($(← withNaryArg 2 delabAssn)) [$x:ident ↦ $a:imp_aexp])
  else
    match ← withNaryArg 2 delab with
    | `($P:ident) => `($P:ident [$x:ident ↦ $a:imp_aexp])
    | P => `(($P) [$x:ident ↦ $a:imp_aexp])

end Assertion.Delab
```
::::

:::ignore
```lean -show
/-- info: {{(X ≤ 10) [X ↦ 2 * X]}} : State → Prop -/
#guard_msgs in
#check {{ (X ≤ 10) [X ↦ 2 * X] }}

/-- info: (X ≤ 10) [X ↦ 2 * X] : Assertion -/
#guard_msgs in
#check (Assertion.subst X (aexp { 2 * X }) ({{ X ≤ 10 }}))
```
:::

That is, `P [X ↦ a]` stands for an assertion -- let's call it
`P'` -- that behaves just like `P` except that, wherever `P` looks up
the variable `X` in the current state, `P'` instead uses the value
of the expression `a`.

::::full
To see how this works in more detail, let's calculate what happens with
a couple of examples.  First, suppose `P'` is `(X ≤ 5) [X ↦ 3]` --
that is, more formally, `P'` is the Lean expression

```display
fun st =>
  (fun st' => st'[X] ≤ 5)
  (X →ₜ Aexp.eval st 3 ; st),
```

which simplifies to

```display
fun st =>
  (fun st' => st'[X] ≤ 5)
  (X →ₜ 3 ; st)
```

and further simplifies to

```display
fun st =>
  ((X →ₜ 3 ; st)[X]) ≤ 5
```

and finally to

```display
fun st =>
  3 ≤ 5.
```

That is, `P'` is the assertion that `3` is less than or equal to
`5` (as expected).

For a more interesting example, suppose `P'` is `(X ≤ 5) [X ↦
X + 1]`.  Formally, `P'` is the Lean expression

```display
fun st =>
  (fun st' => st'[X] ≤ 5)
  (X →ₜ Aexp.eval st (aexp { X + 1 }) ; st),
```

which simplifies to

```display
fun st =>
  (X →ₜ Aexp.eval st (aexp { X + 1 }) ; st)[X] ≤ 5
```

and further simplifies to

```display
fun st =>
  (Aexp.eval st (aexp { X + 1 })) ≤ 5.
```

That is, `P'` is the assertion that `X + 1` is at most `5`.
::::

:::slidebreak
:::

We can demonstrate formally that we have captured intuitive meaning of
"assertion subsitution" by proving some example logical equivalences:

```lean
namespace ExampleAssertionSub
example :
    {{ (X ≤ 5) [X ↦ 3] }} <<->> {{ 3 ≤ 5 }} := by
  rw [assertIff_def]
  rw [assertImplies_def]
  constructor
  · intro st _
    simp
  · intro st h
    simp

example :
    {{ (X ≤ 5) [X ↦ X + 1] }} <<->> {{ (X + 1) ≤ 5 }} := by
  rw [assertIff_def]
  constructor
  · rw [assertImplies_def]
    intro st
    simp
  · rw [assertImplies_def]
    intro st
    simp

end ExampleAssertionSub
```

Most of the `simp` calls rely on {name}`Assertion.subst_apply`, {name}`TotalMap.update_eq` plus some `Aexp` characterizing lemmas like {name}`Aexp.eval_num`.
:::slidebreak
:::

Now, using the substitution operation we've just defined, we can
give the precise proof rule for assignment:

```display
---------------------------- (hoare_asgn)
{{Q [X ↦ a]}} X := a {{Q}}
```

We can prove formally that this rule is indeed valid.

```lean
theorem hoare_asgn {Q : Assertion} {x : Ident} {a : Aexp} :
    {{ Q [x ↦ ~a] }} x := ~a {{ Q }} := by
  rw [validHoareTriple_def]
  intro st st' hE hQ
  inversion hE with
  | asgn n h =>
    subst h
    rw [Assertion.subst_def] at hQ
    exact hQ
```

:::ignore
```lean -show
/--
info: @hoare_asgn : ∀ {Q : Assertion} {x : Ident} {a : Aexp}, {{Q [x ↦ ~a]}} x := ~a {{Q}}
-/
#guard_msgs in
#check @hoare_asgn
```
:::

:::slidebreak
:::

Here's a first formal proof of a Hoare triple using this rule.

```lean
theorem assertion_sub_example :
    {{ (X < 5) [X ↦ X + 1] }}
      X := X + 1
    {{ X < 5 }} := by
  exact hoare_asgn
```

:::slidebreak
:::

Of course, we'd probably prefer to work with this simpler triple:

```display
{{X < 4}} X := X + 1 {{X < 5}}
```

We will see how to do so in the next section.

Several proofs below use the facts about total-map updates
proved in the _Typeclasses_ chapter -- `TotalMap.update_eq`,
`TotalMap.update_neq`, `TotalMap.update_shadow`, `TotalMap.update_same`,
and `TotalMap.update_permute`.  Make sure you understand their statements.

::::::full
Complete these Hoare triples by providing an appropriate
precondition using `exists`, then prove then with `apply
hoare_asgn`. If you find that tactic doesn't suffice, double check
that you have completed the triple properly.

:::::exercise (rating := 2) (name := "hoare_asgn_examples1") (optional := true)
```lean
theorem hoare_asgn_examples1 :
    ∃ P : Assertion,
      {{ P }}
        X := 2 * X
      {{ X ≤ 10 }} := by
  solution!
    exists ({{ (X ≤ 10) [X ↦ 2 * X] }})
    exact hoare_asgn
```
:::::

:::::exercise (rating := 2) (name := "hoare_asgn_examples2") (optional := true)
```lean
theorem hoare_asgn_examples2 :
    ∃ P : Assertion,
      {{ P }}
        X := 3
      {{ 0 ≤ X ∧ X ≤ 5 }} := by
  solution!
    exists ({{ (0 ≤ X ∧ X ≤ 5) [X ↦ 3] }})
    exact hoare_asgn
```
:::::

:::::exercise (rating := 2) (name := "hoare_asgn_wrong")
The assignment rule looks backward to almost everyone the first
time they see it.  If it still seems puzzling to you, it may help
to think a little about alternative "forward" rules.  Here is a
seemingly natural one:

```display
------------------------------ (hoare_asgn_wrong)
{{ True }} X := a {{ X = a }}
```

Give a counterexample showing that this rule is incorrect and use
it to complete the proof below, showing that it is really a
counterexample.  (Hint: The rule universally quantifies over the
arithmetic expression `a`, so your counterexample needs to
exhibit an `a` for which the rule doesn't work.)

:::dev "Niklas Halonen (xhalo32)"
The following exercise provides explicit state arguments to a hypothesis:
```
apply hc (st := ∅) (st' := X →ₜ 1)
```
Should we demonstrate this with an example before this exercise?
:::

```lean
theorem hoare_asgn_wrong : ∃ a : Aexp,
    ¬ {{ True }} X := ~a {{ X = a }} := by
  solution!
    exists aexp { X + 1 }
    intro hc
    rw [validHoareTriple_def] at hc
    have h2 : (X →ₜ 1)[X] = (aexp { X + 1 }).eval (X →ₜ 1) := by
      apply hc (st := ∅) (st' := X →ₜ 1)
      · apply Com.EvalR.asgn; rfl
      · exact True.intro
    simp at h2
```

:::solution
If `a` itself mentions `X`, then the value of `a` may be different
in the final state because of this update. For example, if `a` is
`X + 1`, then setting `X` to `a` certainly does not achieve the
postcondition `X = X + 1`!  The underlying problem is that the
state in which the postcondition will be checked is different than
the state in which `a` was evaluated when it was assigned to `X`.
:::
:::::

:::dev "Michael Clarkson (clarksmr)" PotentialImprovement (year := 2020)
```
It sure would be great for the next two exercises
to use the updated notation.  However, I can't figure out how to
get the postcondition to work with it.  The problem is that the
substitution operator is defined on assertions, but I need a
version of it defined on expressions.
Lef 21: Gave it another unsuccessful go, seems like the same
issue as MRC'20.

  Theorem hoare_asgn_fwd :
         ∀ P m a,
           {{ P ∧ X = m }}
           X := a
           {{ P [X ↦ m] ∧ X = a }}.
```
:::


:::::exercise (rating := 3) (name := "hoare_asgn_fwd") (level := Advanced) (optional := true)
By using a _parameter_ `m` (a Lean number) to remember the
original value of `X` we can define a Hoare rule for assignment
that does, intuitively, "work forwards" rather than backwards.

```display
------------------------------------------ (hoare_asgn_fwd)
{{fun st => P st ∧ st[X] = m}}
  X := a
{{fun st => P (X →ₜ m ; st) ∧ st[X] = Aexp.eval (X →ₜ m ; st) a }}
```

Note that we need to write out the postcondition in "desugared"
form, because it needs to talk about two different states: we use
the original value of `X` to reconstruct the state `st'` before the
assignment took place.  (Also note that this rule is more complicated
than `hoare_asgn`!)

Prove that this rule is correct.

:::dev
HIDE: BCP 21: Could we make the precondition use compact
notation, at least?

HIDE: SAZ 2024 - this version of the syntax does let
us use the compact notation for the precondition, but it
comes at the cost of having to "escape" the function in
the postcondition.
:::

```lean
theorem hoare_asgn_fwd {m : Nat} {a : Aexp} {P : Assertion} :
    {{ P ∧ X = m }}
      X := ~a
    {{ fun st => P (X →ₜ m ; st)
         ∧ st[X] = a.eval (X →ₜ m ; st) }} := by
  solution!
    rw [validHoareTriple_def]
    intro st st' heval ⟨hp, hx⟩
    inversion heval with
    | asgn n h =>
      subst h hx
      rw [TotalMap.update_eq, TotalMap.update_shadow, TotalMap.update_same]
      exact ⟨hp, rfl⟩
```
:::::

:::::exercise (rating := 2) (name := "hoare_asgn_fwd_exists") (level := Advanced) (optional := true)
Another way to define a forward rule for assignment is to
existentially quantify over the previous value of the assigned
variable.  Prove that it is correct.

```display
------------------------------------ (hoare_asgn_fwd_exists)
{{fun st => P st}}
  X := a
{{fun st => ∃ m, P (X →ₜ m ; st) ∧
               st[X] = Aexp.eval (X →ₜ m ; st) a }}
```

:::instructors
This rule was proposed to BCP by Nick Giannarakis and
Zoe Paraskevopoulou.
APT: This is actually Floyd's original rule.  See Mike Gordon,
"Background reading on Hoare Logic," p.21
https://www.cl.cam.ac.uk/archive/mjcg/HL/Notes/Notes.pdf
:::

```lean
theorem hoare_asgn_fwd_exists (a : Aexp) (P : Assertion) :
    {{ P }}
      X := ~a
    {{ fun st => ∃ m, P (X →ₜ m ; st) ∧
         st[X] = a.eval (X →ₜ m ; st) }} := by
  solution!
    rw [validHoareTriple_def]
    intro st st' heval hpre
    inversion heval with
    | asgn n h =>
      subst h
      exists st[X]
      rw [TotalMap.update_eq, TotalMap.update_shadow, TotalMap.update_same]
      exact ⟨hpre, rfl⟩
```
:::::

::::::

::::hide
```
/- HIDE: BCP 19: This sequence of quizzes seems confusing /
confused. The "trivial" ones, as Robert points out, are NOT
trivial...  BCP 21: I'm going to hide all these quizzes for the
moment -- they seem worse than nothing in present form. -/
-- QUIZ
/- Here is the assignment rule again:
[[
      {{ Q [X ↦ a] }} X := a {{ Q }}
]]
    Is the following triple a valid instance of this rule?
[[
      {{ X = 5 }} X := X + 1 {{ X = 6 }}
]]

    (A) Yes

    (B) No -/
/- INSTRUCTORS: a trivial one, to warm up -/
/- HIDE: Robert Rand: Why is this a trivial one? In the precondition
we want [X + 1 = 6], instead we have the equivalent [X = 5]. This
seems like a good example of the problem we want to illustrate in
the last quiz. -/
-- /QUIZ

-- QUIZ
/- Here is the assignment rule again:
[[
      {{ Q [X ↦ a] }} X := a {{ Q }}
]]
    Is the following triple a valid instance of this rule?
[[
      {{ Y < Z }} X := Y {{ X < Z }}
]]

    (A) Yes

    (B) No -/
/- INSTRUCTORS: a slightly less trivial one, to get the juices flowing -/
-- /QUIZ

-- QUIZ
/- The assignment rule again:
[[
      {{ Q [X ↦ a] }} X := a {{ Q }}
]]
    Is the following triple a valid instance of this rule?
[[
      {{ X+1 < Y }} X := X + 1 {{ X < Y }}
]]

    (A) Yes

    (B) No -/
/- INSTRUCTORS: a less trivial one, to start thinking -/
-- /QUIZ

-- QUIZ
/- The assignment rule again:
[[
      {{ Q [X ↦ a] }} X := a {{ Q }}
]]
    Is the following triple a valid instance of this rule?
[[
      {{ X < Y }} X := X + 1 {{ X+1 < Y }}
]]

    (A) Yes

    (B) No -/
/- INSTRUCTORS: a wrong one (actually an invalid triple), to see if
they are paying attention -/
-- /QUIZ

-- QUIZ
/- The assignment rule again:
[[
      {{ Q [X ↦ a] }} X := a {{ Q }}
]]
    Is the following triple a valid instance of this rule?
[[
      {{ X < Y }} X := X + 1 {{ X < Y+1 }}
]]

    (A) Yes

    (B) No -/
/- INSTRUCTORS: another wrong one -- valid, but not an instance of the rule! -/
-- /QUIZ

-- QUIZ
/- The assignment rule again:
[[
      {{ Q [X ↦ a] }} X := a {{ Q }}
]]
    Is the following triple a valid instance of this rule?
[[
      {{ True }} X := 3 {{ X = 3 }}
]]

    (A) Yes

    (B) No -/
-- /QUIZ
/- INSTRUCTORS: Again, valid but not an instance of the rule.  This
leads into the discussion of the rule of consequence. -/
```
::::

## Consequence

Sometimes the preconditions and postconditions we get from the
Hoare rules won't quite be the ones we want in the particular
situation at hand -- they may be logically equivalent but have a
different syntactic form that fails to unify with the goal we are
trying to prove, or they actually may be logically weaker (for
preconditions) or stronger (for postconditions) than what we need.

:::slidebreak
:::

For instance,

```display
{{(X = 3) [X ↦ 3]}} X := 3 {{X = 3}},
```

follows directly from the assignment rule, but

```display
{{True}} X := 3 {{X = 3}}
```

does not.  This triple is valid, but it is not an instance of
`hoare_asgn` because `True` and `(X = 3) \[X ↦ 3`\] are not
syntactically equal assertions.

However, they are logically _equivalent_, so if one triple is
valid, then the other must certainly be as well.  We can capture
this observation with the following rule:

```display
   {{P'}} c {{Q}}
     P <<->> P'
---------------------
   {{P}} c {{Q}}
```

:::slidebreak
:::

Taking this line of thought a bit further, we can see that
strengthening the precondition or weakening the postcondition of a
valid triple always produces another valid triple. This
observation is captured by two _Rules of Consequence_.

```display
       {{P'}} c {{Q}}
          P ->> P'
-----------------------------   (hoare_consequence_pre)
       {{P}} c {{Q}}

       {{P}} c {{Q'}}
         Q' ->> Q
-----------------------------    (hoare_consequence_post)
       {{P}} c {{Q}}
```

:::slidebreak
:::

Here are the formal versions:

```lean
theorem hoare_consequence_pre {P P' Q : Assertion} {c : Com}
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply hhoare heval
  rw [assertImplies_def] at himp
  exact himp _ hpre

theorem hoare_consequence_post {P Q Q' : Assertion} {c : Com}
    (hhoare : {{ P }} ~c {{ Q' }}) (himp : Q' ->> Q) :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  rw [assertImplies_def] at himp
  apply himp
  exact hhoare heval hpre
```

:::slidebreak
:::

For example, we can use the first consequence rule like this:

```display
{{ True }} ->>
{{ (X = 1) [X ↦ 1] }}
  X := 1
{{ X = 1 }}
```

Or, formally...

:::instructors
BCP 20: Careful: this proof got messed up when I
tried it in class.
:::

```lean
theorem hoare_asgn_example1 :
    {{True}} X := 1 {{X = 1}} := by
  workinclass!
    apply hoare_consequence_pre (P' := {{ (X = 1) [X ↦ 1] }})
    · exact hoare_asgn
    · rw [assertImplies_def]
      intro st _
      simp
```

:::slidebreak
:::

We can also use it to prove the example mentioned earlier.

```display
{{ X < 4 }} ->>
{{ (X < 5)[X ↦ X + 1] }}
  X := X + 1
{{ X < 5 }}
```

Or, formally ...

:::instructors
This proof uses `simp` followed by `lia` which is a flexible tactic, so the `simp` is considered terminal.
:::

```lean
theorem assertion_sub_example2 :
    {{X < 4}}
      X := X + 1
    {{X < 5}} := by
  workinclass!
    apply hoare_consequence_pre (P' := {{ (X < 5) [X ↦ X + 1] }})
    · exact hoare_asgn
    · rw [assertImplies_def]
      intro st h
      simp_all
      lia
```

:::dev "Niklas Halonen (xhalo32)"
The above proof uses `simp_all` purely because `lia` can't see that `X` and `"X"` are the same (they are currently marked as `@[simp]` in Imp).
:::

:::slidebreak
:::

Finally, here is a combined rule of consequence that allows us to
vary both the precondition and the postcondition.

```display
       {{P'}} c {{Q'}}
          P ->> P'
          Q' ->> Q
-----------------------------   (hoare_consequence)
       {{P}} c {{Q}}
```

:::dev "Niklas Halonen (xhalo32)"
In the following proof, `(P' := P')` is not necessary, however it avoids having a metavariable in the first goal.
Another option is to just write `exact hoare_consequence_pre (hoare_consequence_post htriple hpost) hpre`.
:::

```lean
theorem hoare_consequence {P P' Q Q' : Assertion} {c : Com}
    (htriple : {{ P' }} ~c {{ Q' }}) (hpre : P ->> P') (hpost : Q' ->> Q) :
    {{ P }} ~c {{ Q }} := by
  apply hoare_consequence_pre (P' := P')
  · exact hoare_consequence_post htriple hpost
  · exact hpre
```

## Automation

Many of the proofs we have done so far with Hoare triples can be
streamlined using the automation techniques that we introduced in
the _Automation_ chapter of _Logical Foundations_.

Recall that `simp` rewrites with any lemmas we pass it.  The
definitions whose meaning we keep needing to expose in this chapter --
`ValidHoareTriple`, `AssertImplies`, and `Assertion.subst` -- each
come with a characterizing lemma (`validHoareTriple_def`,
`assertImplies_def`, `Assertion.subst_def`) restating the definition
as an equation.  Passing these lemmas to `simp` replaces the defined
notions by their meanings wherever they appear.  We'll do that
explicitly below (and shortly package the recipe up as a tactic of
our own).

:::dev "Claude"
The Rocq source here registers `Hint Unfold assert_implies assertion_sub
t_update : core` for `auto`.  That only widens `auto`'s search (unlike the
`Arguments /.` commands, it does not affect `simpl`), so its Lean
counterpart is the `assertion_auto` tactic's simp list below -- not global
`@[simp]` lemmas as for the notation wrappers, whose folded names carry no
meaning in goals the way `->>` and `Assertion.subst` do.
:::

:::dev "Niklas Halonen (xhalo32)" NOW
The following paragraph is outdated.
:::

::::full
The proof of `hoare_consequence_pre`, repeated below, looks
like an opportune place for automation, because all it does
is `unfold`, `intro`, and `apply`.  (It uses `assumption`, too,
but that's just application of a hypothesis.)
::::

:::slidebreak
:::

::::terse
Here's a good candidate for automation:
::::

```display
theorem hoare_consequence_pre (P P' Q : Assertion) (c : Com)
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply hhoare heval
  rw [assertImplies_def] at himp
  exact himp _ hpre
```

:::slidebreak
:::

Since `AssertImplies` is not marked `irreducible`, and `assertImplies_def` is a proof by definitional equality, we can skip the `rw [assertImplies_def] at himp` and use `P ->> P'` like an implication directly.

:::dev "Niklas Halonen (xhalo32)"
This needs a better explanation of when it's okay to use definitions without using their characterizing lemmas.
:::

```lean
theorem hoare_consequence_pre' (P P' Q : Assertion) (c : Com)
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply hhoare heval
  exact himp _ hpre
```

From now on, we will not usually rewrite `assertImplies_def` explicitly.

Since, after the `rw` and `intro`, the remaining steps just apply hypotheses to the goal (and each other), the
remaining proof can be compressed into a single tactic: {tactic}`apply_rules`.

```lean
theorem hoare_consequence_pre'' (P P' Q : Assertion) (c : Com)
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply_rules
```

:::slidebreak
:::

The same trick works for `hoare_consequence_post`.

```lean
theorem hoare_consequence_post' (P Q Q' : Assertion) (c : Com)
    (hhoare : {{ P }} ~c {{ Q' }}) (himp : Q' ->> Q) :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply_rules
```

:::slidebreak
:::

We can also leave a metavariable for `P'` in `hoare_asgn_example1`, that we did earlier as an example of using the consequence rule:

```lean
theorem hoare_asgn_example1' :
    {{True}} X := 1 {{X = 1}} := by
  apply hoare_consequence_pre -- not specifying `(P' := ...)` leaves a "hole" `?P'`
  · -- The goal is `{{?P'}} X := 1 {{X = 1}}`
    exact hoare_asgn -- Assigns `?P'` to `{{ (X = 1) [X ↦ 1] }}` (automatically closing `case P'`)
  · intro st _ -- Since `->>` is an implication, we can just use `intro` directly.
    simp
```

:::slidebreak
:::

The final bullet of that proof also looks like a candidate for
automation.

```lean
theorem hoare_asgn_example1'' :
    {{True}} X := 1 {{X = 1}} := by
  apply hoare_consequence_pre
  · exact hoare_asgn
  · simp [assertImplies_def]
```

Now we have quite a nice proof script: it simply identifies the
Hoare rules that need to be used and leaves the remaining
low-level details up to Lean to figure out.

::::full
By now it might be apparent that the _entire_ proof could be
automated by a more ambitious tactic that also knew about the Hoare
rules themselves.  We won't build one in this chapter, so that we
can get a better understanding of when and how the Hoare rules are
used.  In the next chapter, _Hoare2_, we'll dive deeper into
automating entire proofs of Hoare triples.
::::

:::slidebreak
:::

The other example of using consequence that we did earlier,
`hoare_asgn_example2`, requires a little more work to automate.
`simp` simplifies the assertion implication in the final bullet,
but cannot finish it: the leftover goal is arithmetic, so it needs
`lia`.

```lean
theorem assertion_sub_example2' :
    {{X < 4}}
      X := X + 1
    {{X < 5}} := by
  apply hoare_consequence_pre
  · exact hoare_asgn
  · simp [assertImplies_def] -- an arithmetic goal remains
    lia
```

:::slidebreak
:::

Let's introduce our own tactic to handle both that bullet and the
bullet from example 1.  A `macro` declaration gives a name to a
canned sequence of tactics:

:::dev "Niklas Halonen (xhalo32)"
It's unfortunate that we need to unfold `X, Y, Z, W` in `assertion_auto` as `simp` wouldn't otherwise reduce `X == Y` to `false`.
Note that `Ident` is an `abbrev`.
Making it an `implicit_reducible` def breaks `lia` for some reason and doesn't resolve the issue.
```
@[implicit_reducible]
def Ident := String
deriving BEq, ReflBEq, LawfulBEq, DecidableEq
```
:::

```lean
macro "assertion_auto" : tactic =>
  `(tactic| focus (simp +decide [assertImplies_def, assertIff_def, validHoareTriple_def,
                                Assertion.subst_def] at *
                  <;> lia))
```

:::slidebreak
:::

```lean
theorem assertion_sub_example2'' :
    {{X < 4}}
      X := X + 1
    {{X < 5}} := by
  apply hoare_consequence_pre
  · exact hoare_asgn
  · assertion_auto
```

:::slidebreak
:::

```lean
theorem hoare_asgn_example1''' :
    {{True}} X := 1 {{X = 1}} := by
  apply hoare_consequence_pre
  · exact hoare_asgn
  · assertion_auto
```

:::slidebreak
:::

Again, we have quite a nice proof script.  All the low-level
details of proofs about assertions have been taken care of
automatically. Of course, `assertion_auto` isn't able to prove
everything we could possibly want to know about assertions --
there's no magic here! But it's pretty good.

::::::full
:::::exercise (rating := 2) (name := "hoare_asgn_examples_2")
Prove these triples.  Try to make your proof scripts nicely
automated by following the examples above.

```lean
theorem assertion_sub_ex1' :
    {{ X ≤ 5 }}
      X := 2 * X
    {{ X ≤ 10 }} := by
  solution!
    apply hoare_consequence_pre
    · exact hoare_asgn
    · assertion_auto

theorem assertion_sub_ex2' :
    {{ 0 ≤ 3 ∧ 3 ≤ 5 }}
      X := 3
    {{ 0 ≤ X ∧ X ≤ 5 }} := by
  solution!
    apply hoare_consequence_pre
    · exact hoare_asgn
    · assertion_auto
```

:::gradeTheorem 1 assertion_sub_ex1' assertion_sub_ex2'
:::
:::::

:::dev PotentialImprovement
```
Note here about equivalent preconditions
[[
      {{ X + 1 ≤ 5 }}  X := X + 1  {{ X ≤ 5 }}

      {{ 3 = 3 }}  X := 3  {{ X = 3 }}

      {{ 0 ≤ 3 ∧ 3 ≤ 5 }}  X := 3  {{ 0 ≤ X ∧ X ≤ 5 }}
]]
```
:::
::::::

## Sequencing + Assignment

Here's an example of a program involving both sequencing and
assignment.  Note the use of `hoare_seq` in conjunction with
`hoare_consequence_pre` and `apply`'s metavariables.

```lean
theorem hoare_asgn_example3 (a : Aexp) (n : Nat) :
    {{a = n}}
      X := ~a;
      skip
    {{X = n}} := by
  apply hoare_seq
  · -- right part of seq
    exact hoare_skip
  · -- left part of seq
    apply hoare_consequence_pre
    · exact hoare_asgn
    · assertion_auto
```

:::slidebreak
:::

Informally, a nice way of displaying a proof using the sequencing
rule is as a "decorated program" where the intermediate assertion
`Q` is written between `c1` and `c2`:

```display
         {{ a = n }}
X := a
         {{ X = n }};    <--- decoration for Q
skip
         {{ X = n }}
```

We'll come back to the idea of decorated programs in much more
detail in the next chapter.

::::::full
:::::exercise (rating := 2) (name := "hoare_asgn_example4")
Translate this "decorated program" into a formal proof:

```display
               {{ True }} ->>
               {{ 1 = 1 }}
X := 1
               {{ X = 1 }} ->>
               {{ X = 1 ∧ 2 = 2 }};
Y := 2
               {{ X = 1 ∧ Y = 2 }}
```

Note the use of "`->>`" decorations, each marking a use of
`hoare_consequence_pre`.

We've started you off by providing a use of `hoare_seq` that
explicitly identifies `X = 1` as the intermediate assertion.

```lean
theorem hoare_asgn_example4 :
    {{ True }}
      X := 1;
      Y := 2
    {{ X = 1 ∧ Y = 2 }} := by
  apply hoare_seq (Q := {{ X = 1 }})
  · -- right part of seq
    solution!
      apply hoare_consequence_pre
      · exact hoare_asgn
      · assertion_auto
  · -- left part of seq
    solution!
      apply hoare_consequence_pre
      · exact hoare_asgn
      · assertion_auto
```
:::::

:::::exercise (rating := 3) (name := "swap_exercise")
Write an Imp program `c` that swaps the values of `X` and `Y` and
show that it satisfies the following specification:

```display
{{X ≤ Y}} c {{Y ≤ X}}
```

Your proof should not need to use `rw [validHoareTriple_def]`.

Hints:
   - Remember that Imp commands need to be enclosed in `imp { … }`
     brackets.
   - Remember that the assignment rule works best when it's
     applied "back to front," from the postcondition to the
     precondition.  So your proof will want to start at the end
     and work back to the beginning of your program.
   - Remember that `apply` is your friend.)

:::dev PotentialImprovement
One of the OPLSS students noticed that it is quite
confusing to try to write out the decorated program version of this
proof.
:::

:::dev
```
HIDE: CH: Here goes:
[[
  {{ X ≤ Y }}
    Z := X
            {{ Z ≤ Y }};
    X := Y
            {{ Z ≤ X }};
    Y := Z
  {{ Y ≤ X }}
]]
   The _only_ catch is that one needs to do it backwards, since that's
   how the hoare_asgn rule is defined.
   Maybe move this decorated program to the decorated programs
   section, since it's a good warm-up exercise.
```
:::

```lean
def swap_program : Com := solution!(imp { Z := X; X := Y; Y := Z })

theorem swap_exercise :
    {{X ≤ Y}}
      ~swap_program
    {{Y ≤ X}} := by
  solution!
    rw [swap_program]
    apply hoare_seq
    · apply hoare_seq
      · exact hoare_asgn
      · exact hoare_asgn
    · apply hoare_consequence_pre
      · exact hoare_asgn
      · assertion_auto
```
:::::

:::::exercise (rating := 4) (name := "invalid_triple") (level := Advanced)
:::dev "Michael Clarkson (clarksmr)" PotentialImprovement (year := 2020)
should this be 3 or 4 stars?
:::

:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement (year := 2020)
We got a LOT of questions about this problem this
year -- many students clearly find it puzzling.  I added the
extended hint below to try to help.
:::

Show that

```display
{{ a = n }} X := 3; Y := a {{ Y = n }}
```

is not a valid Hoare triple for some choices of `a` and `n`.

Conceptual hint: Invent a particular `a` and `n` for which the
triple in invalid, then use those to complete the proof.

Technical hint: Hypothesis `h` below begins `∀ a n, ...`.
You'll want to instantiate that with the particular `a` and `n`
you've invented.  You can do that with `have` and `apply`, but
you may remember (from the _Automation_ chapter of Logical Foundations)
that Lean offers an even easier tactic: `specialize`.  If you write

```display
specialize h your_a your_n
```

the hypothesis will be instantiated on `your_a` and `your_n`.

Having chosen your `a` and `n`, proceed as follows:
 - Use the (assumed) validity of the given hoare triple to derive
   a state `st'` in which `Y` has some value `y1`
 - Use the evaluation rules (`Com.EvalR.seq` and `Com.EvalR.asgn`) to show
   that `Y` has a _different_ value `y2` in the same final state `st'`
 - Since `y1` and `y2` are both equal to `st'[Y]`, they are equal
   to each other. But we chose them to be different, so this is a
   contradiction, which finishes the proof.

```lean
theorem invalid_triple : ¬ ∀ (a : Aexp) (n : Nat),
    {{ a = n }}
      X := 3; Y := ~a
    {{ Y = n }} := by
  intro h
  simp only [validHoareTriple_def] at h
  solution!
    specialize h (aexp { X }) 2 (st := X →ₜ 2) (st' := Y →ₜ 3 ; X →ₜ 3 ; X →ₜ 2) ?_
    · apply Com.EvalR.seq
      · apply Com.EvalR.asgn; rfl
      · apply Com.EvalR.asgn; rfl
    simp at h
```
:::::

::::::

## Conditionals

What sort of rule do we want for reasoning about conditional
commands?

Certainly, if the same assertion `Q` holds after executing
either of the branches, then it holds after the whole conditional.
So we might be tempted to write:

```display
        {{P}} c1 {{Q}}
        {{P}} c2 {{Q}}
---------------------------------
{{P}} if b then c1 else c2 {{Q}}
```

:::slidebreak
:::

However, this is rather weak. For example, using this rule,
we cannot show

```display
{{ True }}
  if X = 0
    then Y := 2
    else Y := X + 1
  end
{{ X ≤ Y }}
```

since the rule doesn't tell us enough about the state in which the
assignments take place in the "then" and "else" branches.

::::full
Fortunately, we can say something more precise.  In the
"then" branch, we know that the boolean expression `b` evaluates to
`true`, and in the "else" branch, we know it evaluates to `false`.
Making this information available in the premises of the rule gives
us more information to work with when reasoning about the behavior
of `c1` and `c2` (i.e., the reasons why they establish the
postcondition `Q`).
::::

:::slidebreak
:::

::::terse
Better:
::::

```display
{{P ∧   b}} c1 {{Q}}
{{P ∧ ¬ b}} c2 {{Q}}
------------------------------------  (hoare_if)
{{P}} if b then c1 else c2 end {{Q}}
```

:::slidebreak
:::

:::dev "Niklas Halonen (xhalo32)"
I have removed `bassertion` as it's an unnecessary abstraction and only adds overhead for the reader.

The following theorem is now unnecessary.
:::

```lean
theorem bexp_eval_false (b : Bexp) (st : State) (h : b.eval st = false) :
    ¬ ({{ b }}) st := by
  dsimp
  simp [h]
```

::::full
Here, we first reduce the expression to `¬Bexp.eval st b = true` with {tactic}`dsimp`, which is trivial after we instruct `simp` to rewrite `b.eval st` to `false`.
::::

:::dev "One An (meluge)"
The Rocq proof is the single tactic `congruence`. Using simp seems to work
but should we build our own `congruence` tactic?
:::

:::slidebreak
:::

Now we can formalize the Hoare proof rule for conditionals
and prove it correct.

The statement of the rule reads: given `htrue : {{ P ∧ b }} ~c1 {{Q}}`
and `hfalse : {{ P ∧ ¬b }} ~c2 {{Q}}`, we can conclude
`{{P}} if (~b) { ~c1 } else { ~c2 } {{Q}}`.

```lean
theorem hoare_if {P Q : Assertion} {b : Bexp} {c1 c2 : Com}
    (htrue : {{ P ∧ b }} ~c1 {{ Q }}) (hfalse : {{ P ∧ ¬ b }} ~c2 {{ Q }}) :
    {{ P }} if (~b) { ~c1 } else { ~c2 } {{ Q }} := by
  rw [validHoareTriple_def] at htrue hfalse ⊢
  intro st st' hE hpre
  inversion hE with
  | ifTrue hb hc1 =>
    exact htrue hc1 ⟨hpre, hb⟩
  | ifFalse hb hc =>
    rw [← Bool.not_eq_true] at hb
    exact hfalse hc ⟨hpre, hb⟩
```

### Example

::::full
Here is a formal proof that the program we used to motivate
the rule satisfies the specification we wanted.
::::

```lean
theorem if_example :
    {{True}}
      if (X = 0) {
        Y := 2
      } else {
        Y := X + 1
      }
    {{X ≤ Y}} := by
  apply hoare_if
  · -- Then
    apply hoare_consequence_pre
    · exact hoare_asgn
    · assertion_auto
  · -- Else
    apply hoare_consequence_pre
    · exact hoare_asgn
    · assertion_auto
```

:::slidebreak
:::

We can even shorten it a little bit more.

```lean
theorem if_example' :
    {{True}}
      if (X = 0) {
        Y := 2
      } else {
        Y := X + 1
      }
    {{X ≤ Y}} := by
  apply hoare_if <;> apply hoare_consequence_pre hoare_asgn (by assertion_auto)
```

::::::full
:::::exercise (rating := 2) (name := "if_minus_plus")
Prove the theorem below using `hoare_if`.  Do not use unfold `ValidHoareTriple`.  The `assertion_auto` tactic we just
defined may be useful.

```lean
theorem if_minus_plus :
    {{True}}
      if (X ≤ Y) {
        Z := Y - X
      } else {
        Y := X + Z
      }
    {{Y = X + Z}} := by
  solution!
    apply hoare_if <;> apply hoare_consequence_pre hoare_asgn (by assertion_auto)
```
:::::

::::::

### Exercise: One-sided conditionals

:::suppressPreviousHeaderWhenTerse
:::

:::dev
HIDE: Question from 2012, Midterm 2. One-sided conditionals.
:::

::::::full
In this exercise we consider extending Imp with "one-sided
conditionals" of the form `if1 (b) { c }`. Here `b` is a boolean
expression, and `c` is a command. If `b` evaluates to `true`, then
command `c` is evaluated. If `b` evaluates to `false`, then
`if1 (b) { c }` does nothing.

We recommend that you complete this exercise before attempting the
ones that follow, as it should help solidify your understanding of
the material.

The first step is to extend the syntax of commands and introduce
the usual notations.  (We've done this for you, in a separate
namespace to prevent polluting the global name space.  The `scoped`
notations below are active only inside `namespace If1`.)

```lean
namespace If1

inductive Com : Type where
  | skip : Com
  | asgn : Ident → Aexp → Com
  | seq : Com → Com → Com
  | cond : Bexp → Com → Com → Com
  | whileDo : Bexp → Com → Com
  | if1 : Bexp → Com → Com
```

:::instructors
We simply extend `imp_com` in the `If1` namespace with the `if1` syntax rather than defining a new syntax category.
This means we need to redefine the `macro_rules` with the new `Com`.
:::

```lean
/-- One-sided conditional -/
scoped syntax "if1 " "(" imp_bexp ")" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}") : imp_com

open Lean in
scoped macro_rules
  | `(imp { $x:ident }) =>
    if x.getId == `skip then `(Com.skip)
    else Macro.throwErrorAt x s!"expected 'skip', got '{x.getId}'"
  | `(imp { $c1; $c2 }) =>
    `(Com.seq (imp {$c1}) (imp {$c2}))
  | `(imp { $x:ident := $a }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c1} else {$c2} }) =>
    `(Com.cond (bexp {$b}) (imp {$c1}) (imp {$c2}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { if1 ($b) {$c} }) =>
    `(Com.if1 (bexp {$b}) (imp {$c}))
  | `(imp { ~$c }) =>
    pure c
```

The delaborators are re-instantiated the same way: the Imp printer is
parameterized over the namespace of the command constructors, so the
extended printer is that printer at `If1.Com` plus one case for `if1`.

::::details "Notation encoding: printing the extended commands back"
```lean
namespace Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Delab

/-- Rebuild `imp_com` syntax from an `If1.Com` term. -/
partial def delabComInner : DelabM (TSyntax `imp_com) :=
  delabComInnerFor ``Com do
    let e ← getExpr
    guard <| e.isAppOfArity ``Com.if1 2
    let b ← withAppFn <| withAppArg delabBexpInner
    let c ← withAppArg If1.Delab.delabComInner
    `(imp_com| if1 ($b) {$c})

@[delab app.If1.Com.skip, delab app.If1.Com.asgn, delab app.If1.Com.seq,
  delab app.If1.Com.cond, delab app.If1.Com.whileDo, delab app.If1.Com.if1]
partial def delabCom : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Com.skip => true
    | Com.asgn _ _ => true
    | Com.seq _ _ => true
    | Com.cond _ _ _ => true
    | Com.whileDo _ _ => true
    | Com.if1 _ _ => true
    | _ => false
  match ← delabComInner with
  | `(imp_com| ~$e) => pure e
  | e => `(term| imp { $e })

end Delab
```
::::

:::ignore
```lean -show
/-- info: imp {
  if1 (X = 0) {
    X := 1
  }
} : Com -/
#guard_msgs in
#check imp { if1 (X = 0) { X := 1 } }
```
:::

:::::exercise (rating := 2) (name := "if1_ceval")
Add two new evaluation rules to relation `Com.EvalR`, below, for
`if1`. Let the rules for `if` guide you.

```lean
inductive Com.EvalR : Com → State → State → Prop where
  | skip {st : State} :
      EvalR (imp {skip}) st st
  | asgn {st : State} (a : Aexp) {n : Nat} (x : Ident) (h : a.eval st = n) :
      EvalR (imp {x := ~a}) st (x →ₜ n ; st)
  | seq {c1 c2 : Com} (st st' st'' : State)
      (h1 : EvalR c1 st st') (h2 : EvalR c2 st' st'') :
      EvalR (imp {~c1; ~c2}) st st''
  | ifTrue {st st' : State} (b : Bexp) {c1 c2 : Com} (hb : b.eval st = true)
      (hc : EvalR c1 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st st'
  | ifFalse {st st' : State} (b : Bexp) {c1 c2 : Com} (hb : b.eval st = false)
      (hc : EvalR c2 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st st'
  | whileFalse {b : Bexp} (st : State) (c : Com) (hb : b.eval st = false) :
      EvalR (imp {while (~b) {~c} }) st st
  | whileTrue {st st' st'' : State} {b : Bexp} {c : Com}
      (hb : b.eval st = true) (hc : EvalR c st st')
      (hloop : EvalR (imp {while (~b) {~c} }) st' st'') :
      EvalR (imp {while (~b) {~c} }) st st''
-- SOLUTION
  | if1True {st st' : State} {b : Bexp} {c : Com} (hb : b.eval st = true)
      (hc : EvalR c st st') :
      EvalR (imp {if1 (~b) {~c} }) st st'
  | if1False {st : State} {b : Bexp} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {if1 (~b) {~c} }) st st
-- END SOLUTION

instance : HasEval Com State State where
  Eval := Com.EvalR

@[app_unexpander Com.EvalR]
def Com.unexpandEvalR : Lean.PrettyPrinter.Unexpander
  | `($_ $c $st0 $st1) => ``($st0 =[ ~$c ]=> $st1)
  | _ => throw ()
```

The following unit tests should be provable simply by applying your
new rules (plus `rfl` for the boolean side conditions) if you have
defined them correctly.

```lean
theorem if1true_test :
    ∅ =[ if1 (X = 0) { X := 1 } ]=> (X →ₜ 1) := by
  solution!
    apply Com.EvalR.if1True
    · rfl
    · apply Com.EvalR.asgn; rfl

theorem if1false_test :
    (X →ₜ 2) =[ if1 (X = 0) { X := 1 } ]=> (X →ₜ 2) := by
  solution!
    apply Com.EvalR.if1False
    rfl
```

:::gradeTheorem 1 if1true_test if1false_test
:::
:::::

:::dev
This is outdated. It should explain `HasTriple`
:::

Now we have to repeat the definition and notation of Hoare triples,
so that they will use the updated `Com` type.

```lean
def ValidHoareTriple
    (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ {st st' : State},
    (st =[ c ]=> st') →
    P st →
    Q st'

instance : HasTriple Com where
  Triple := ValidHoareTriple

theorem validHoareTriple_def {P : Assertion} {c : Com} {Q : Assertion} :
    {{ P }} ~c {{ Q }} ↔ ∀ {st st' : State},
      (st =[ c ]=> st') →
      P st →
      Q st' := by rfl

attribute [irreducible] ValidHoareTriple
```

:::ignore
```lean -show
/--
info: {{True}}
  if1 (X = 0) {
    skip
  } {{True}} : Prop
-/
#guard_msgs in
#check ({{ True }} if1 (X = 0) { skip } {{ True }})
```
:::

:::::exercise (rating := 2) (name := "hoare_if1") (manual := true)
Invent a Hoare logic proof rule for `if1`.  State and prove a
theorem named `hoare_if1` that shows the validity of your rule.
Use `hoare_if` as a guide. Try to invent a rule that is
_complete_, meaning it can be used to prove the correctness of as
many one-sided conditionals as possible.  Also try to keep your
rule _compositional_, meaning that any Imp command that appears
in a premise should syntactically be a part of the command
in the conclusion.

Hint: if you encounter difficulty getting Lean to parse part of
your rule as an assertion, try wrapping it in the `{{ … }}` brackets
or adding a type ascription.  For example, if you want `e` to be
parsed as an assertion, write it as `(e : Assertion)`.

```lean
-- SOLUTION
theorem hoare_if1 (b : Bexp) (c : Com) (P Q : Assertion)
    (htrue : {{ P ∧ b }} ~c {{ Q }})
    (hfalse : ({{ P ∧ ¬ b }}) ->> Q) :
    {{ P }} if1 (~b) { ~c } {{ Q }} := by
  rw [validHoareTriple_def] at htrue ⊢
  intro st st' heval hpre
  inversion heval with
  | if1True hb hc =>
    exact htrue hc ⟨hpre, hb⟩
  | if1False hb =>
    apply hfalse
    simp [hpre, hb]
-- END SOLUTION
```

For example (`hoare_if1_good`) your rule should be strong
enough to show the following Hoare triple is valid:

```display
{{ X + Y = Z }}
if1 (Y ≠ 0) {
  X := X + Y;
}
{{ X = Z }}
```

:::grade
`GRADE_MANUAL 2: hoare_if1`
:::
:::::

Before the next exercise, we need to restate the Hoare rules of
consequence (for preconditions) and assignment for the new `Com`
type.

```lean
theorem hoare_consequence_pre {P P' Q : Assertion} {c : Com}
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  exact hhoare heval (himp st hpre)

theorem hoare_asgn {Q : Assertion} {x : Ident} {a : Aexp} :
    {{Q [x ↦ ~a]}} x := ~a {{ Q }} := by
  rw [validHoareTriple_def]
  intro st st' heval hQ
  rw [Assertion.subst_apply] at hQ
  inversion heval with
  | asgn n h =>
    subst h
    exact hQ
```

:::::exercise (rating := 2) (name := "hoare_if1_good")
Use your `if1` rule to prove the following (valid) Hoare triple.

Hint: `assertion_auto` will once again get you most but not all
the way to a completely automated proof.  You can finish manually,
or tweak the tactic further.

Hint: If you see a message about failing to unify commands from the
top-level `Com` with commands from this namespace, it probably means
you are using a definition or theorem (e.g., `hoare_skip`) from
above this exercise without re-proving it for the new version of
Imp with `if1`.

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2021)
Not quite fair to give them a 2-point exercise
where our solution uses a custom Ltac...
:::

```lean
theorem hoare_if1_good :
    {{ X + Y = Z }}
      if1 (Y ≠ 0) {
        X := X + Y
      }
    {{ X = Z }} := by
  solution!
    apply hoare_if1
    · apply hoare_consequence_pre
      · exact hoare_asgn
      · assertion_auto
    · assertion_auto
```
:::::

```lean
end If1
```
::::::

## While Loops

The Hoare rule for `while` loops is based on the idea of a
_command invariant_ (or just _invariant_): an assertion whose
truth is guaranteed after executing a command, assuming it is true
before.

That is, an assertion `P` is a command invariant of `c` if

```display
{{P}} c {{P}}
```

holds.  Note that the command invariant might temporarily become
false in the middle of executing `c`, but by the end of `c` it
must be restored.

::::full
As a first attempt at a `while` rule, we could try:

```display
       {{P}} c {{P}}
---------------------------
{{P}} while b do c end {{P}}
```

This rule is valid: if `P` is a command invariant of `c`, as the
premise requires, then, no matter how many times the loop body
executes, `P` is going to be true when the loop finally finishes.

But the rule also omits two crucial pieces of information.  First,
the loop terminates when `b` becomes false.  So we can strengthen
the postcondition in the conclusion:

```display
        {{P}} c {{P}}
---------------------------------
{{P}} while b do c end {{P ∧ ¬b}}
```

Second, the loop body will be executed only if `b` is true.  So we
can also strengthen the precondition in the premise:

```display
      {{P ∧ b}} c {{P}}
--------------------------------- (hoare_while)
{{P}} while b do c end {{P ∧ ¬b}}
```
::::

:::slidebreak
:::

::::terse
The Hoare while rule combines the idea of a command invariant with
information about when guard `b` does or does not hold.

```display
      {{P ∧ b}} c {{P}}
--------------------------------- (hoare_while)
{{P}} while b do c end {{P ∧ ¬b}}
```
::::

::::full
That is the Hoare `while` rule.  Note how it combines
aspects of `skip` and conditionals:

- If the loop body executes zero times, the rule is like `skip` in
  that the precondition survives to become (part of) the
  postcondition.

- Like a conditional, we can assume guard `b` holds on entry to
  the subcommand.
::::

:::dev
HIDE: The big comment will not display nicely.  But I guess it's
folded...
:::

:::dev "Niklas Halonen (xhalo32)"
We need to explain the `generalize` tactic.
:::

```lean
theorem hoare_while {P : Assertion} {b : Bexp} {c : Com}
    (hhoare : {{P ∧ b}} ~c {{ P }}) :
    {{ P }} while (~b) { ~c } {{P ∧ ¬ b}} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  /- We proceed by induction on `heval`, because, in the "keep
  looping" case, its hypotheses talk about the whole loop instead
  of just `c`. We begin by generalizing over an
  arbitrary command, together with an equation remembering that the
  command is the original loop. The cases for commands other than
  `while` are dismissed because their equations are contradictory. -/
  generalize heq : (imp { while (~b) { ~c } }) = cmd at heval
  induction heval with
  | @whileFalse b0 s0 c0 hb =>
    injection heq with hbeq hceq
    simp_all
  | @whileTrue s0 s0' s0'' b0 c0 hb hc hloop ih1 ih2 =>
    injection heq with hbeq hceq
    subst hbeq hceq
    exact ih2 (hhoare hc ⟨hpre, hb⟩) rfl
  | skip | asgn | seq | ifTrue | ifFalse =>
    contradiction
```

:::slidebreak
:::

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2021)
This definition / discussion could be clearer.
:::

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2023)
```
Maja says: The wording of "we will never enter the
loop" could definitely be improved. As is, it suggests a situation
where the loop condition itself can never be satisfied. I suspect that
a previous draft included a discussion that explicitly placed {{ P }}
before the while, perhaps along the lines of "a loop invariant P of
[while b do c end] is also an invariant of [while b do c end]" (which
is, FWIW, a (somewhat obtuse) way of stating a weaker variant of
hoare_while, without the ~b in the postcondition). Combined with the
fact that it is supposed to justify a somewhat surprising and
unexpected fact — [X = 0] is not what I would intuitively consider an
invariant of this loop — this sentence ends up being quite confusing.
I only understood it when I came back to find this excerpt.
```
:::

We call `P` a _loop invariant_ of `while b do c end` if

```display
{{P ∧ b}} c {{P}}
```

is a valid Hoare triple.

This means that `P` will be true at the end of the loop body
whenever the loop body executes. If `P` contradicts `b`, this
holds trivially since the precondition is false.

For instance, `X = 0` is a loop invariant of

```display
while X = 2 do X := 1 end
```

since the program will never enter the loop.

::::quiz
Is the assertion

```display
Y = 0
```

a loop invariant of the following?

```display
while X < 100 do X := X + 1 end
```

(A) Yes

(B) No
::::

:::instructors
YES
:::

::::quiz
Is the assertion

```display
X = 0
```

a loop invariant of the following?

```display
while X < 100 do X := X + 1 end
```

(A) Yes

(B) No
::::

:::instructors
NO
:::

::::quiz
Is the assertion

```display
X < Y
```

a loop invariant of the following?

```display
while true do X := X + 1; Y := Y + 1 end
```

(A) Yes

(B) No
::::

:::instructors
Yes
:::

::::quiz
Is the assertion

```display
X = Y + Z
```

a loop invariant of the following?

```display
while Y > 10 do Y := Y - 1; Z := Z + 1 end
```

(A) Yes

(B) No
::::

:::instructors
YES
:::

:::dev BeforeNextRelease
This last quiz should be turned into a discussion in the
text, at least in the full version -- indeed, maybe all these
should be turned into a long discussion of what it means to be a
loop invariant -- I think that would be pretty helpful.
:::

::::full
The program

```display
while Y > 10 do Y := Y - 1; Z := Z + 1 end
```

admits an interesting loop invariant:

```display
X = Y + Z
```

Note that this doesn't contradict the loop guard but neither
is it a command invariant of

```display
Y := Y - 1; Z := Z + 1
```

since, if X = 5,
Y = 0 and Z = 5, running the command will set Y + Z to 6. The
loop guard `Y > 10` guarantees that this will not be the case.
We will see many such loop invariants in the following chapter.
::::

::::hide
```
/- For now, you have to accept on faith that the [hoare_while] rule
is "powerful enough". It can be shown that the proof rules we
develop here for Hoare logic are _complete_, in the sense that any
valid Hoare triple can be proved simply by application of these
theorems and an oracle for the underlying logic. In particular,
given any while loop and a valid Hoare triple for it, it is always
possible to find a loop invariant [P] that leads to the proof.

We are not going to prove completeness formally here, but the
exercises below should get you comfortable with identifying
loop invariants in practice. -/

/- Mukund: Possible motivation for [hoare_while]? -/

/- CH: Maybe the [while] could indeed be explained better, but ...
The examples you propose here are one order or magnitude more
complex than any of the examples considered in this whole file,
and they use language features that are beyond the scope of this
course (arrays). Also, you don't explain at all how to come up
with loop invariants, you just take extremely complicated
invariants out of the hat. Finally, this whole discussion about
loop invariants better belongs to the decorated programs section
where loop invariants are first used. -/

/- Let's look at the pseudo-code for two common procedures in
    introductory algorithms courses: insertion sort, and Euclid's GCD
    finding algorithm.

    Given: An array of n integers a[1...n].
    To calculate: Return an array A[1...n], containing the elements
      of a in sorted order.
    Do:
      Copy array a into A.
      Initialize i := 0.
      While i < n,
        Let j := i.
        While j > 0,
          Compare A[j] and A[j + 1].
          Swap if A[j] > A[j + 1].
        end
      end.

    Consider the following claim made of insertion sort. Always, just
    before the condition [i < n] is evaluated in the outer while loop,
    the following conditions hold:

    1. The elements A[1...i] are in sorted order.
    2. A[1...i] are a permutation of the elements a[1...i].
    3. The elements A[(i + 1)...n] are each equal to the elements of
       a[(i + 1)...n].
    4. i ≤ n.

    Observe that these conditions hold the first time the loop condition
    is evaluated. Also, if they hold before the loop body is evaluated,
    then they should hold afterwards. Thus, the conditions form a
    _loop invariant_.

    But why are they helpful? We now know that they hold after any finite
    number of iterations of the loop. In particular, they hold when
    (and if) the loop terminates. What happens then? Since the loop has
    terminated, we know that [i ~< n], and so [i = n]. Substituting n
    for i, we get that A[1...n] are a permutation of a[1...n], and in
    sorted order. And thus, (if insertion sort terminates), it is correct.

    Given: Two positive integers, a and b.
    To find: gcd(a, b)
    Do:
      Let A := a, B := b.
      If A = 0, return B.
      While B ~= 0,
        If A > B,
          A := A - B
        else
          B := B - A
        fi
      end
      Return A.

    We make the claim, just before the evaluation of the loop condition,
    the following condition always holds: "gcd(A, B) = gcd(a, b)".

    It is true at the beginning, and if they hold before executing the
    loop body, then they hold afterwards as well.

    This loop invariant allows us to prove the correctness of the algorithm:
    when the loop terminates, we know that gcd(A, B) = gcd(a, b), and that
    B = 0. But for all x, gcd(x, 0) = x, and so gcd(A, B) = gcd(A, 0) = A.
    Thus, A = gcd(a, b).

    In both cases, we did not answer the question: "Does this procedure
    always terminate?" But partial correctness is also a feature of Hoare
    logic -- we assume [st =[ c ]=> st'] before checking whether [st']
    satisfies the postcondition.

    The purpose of these two (extremely) informal proofs was to
    convince you that loop invariants are a common design pattern while
    proving the correctness of programs.

    We try to abstract this pattern into a Hoare rule.

    1. The loop invariant is itself an assertion [P]. Since it must
       hold at the beginning, [P] must be the precondition of the
       Hoare triple.
    2. The loop invariant is preserved by the loop body, but at termination,
       we know something more: recall how we finished the
       gcd-correctness proof -- "when the loop terminates, ..., and
       that B = 0. ..." Thus, the post-condition is [P ∧ ¬ b], where
       [b] is the loop condition.
    3. What do we demand of the loop body [c]? [{{ P }} c {{ P }}]
       might be a good first guess, since we want [P] to be
       invariant after [c]. But remember that we asserted [P] before evaluating
       the loop condition, and so we know that [b] must have
       evaluated to true. Thus, we want the loop body to satisfy
       the Hoare triple: [{{ P ∧ b }} c {{ P }}].

    Putting these together, we get the Hoare proof rule for while:

[[[
               {{P ∧ b}} c {{P}}
        ----------------------------------  (hoare_while)
        {{P}} while b do c end {{P ∧ ¬ b}}
]]] -/
```
::::

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2021)
What is this example doing here?? Needs some text.
:::

::::full
```lean
theorem while_example :
    {{X ≤ 3}}
      while (X ≤ 2) {
        X := X + 1
      }
    {{X = 3}} := by
  apply hoare_consequence_post
  · apply hoare_while
    apply hoare_consequence_pre
    · exact hoare_asgn
    · assertion_auto
  · assertion_auto
```
::::

:::dev
```
HIDE: CJC: Maybe also a good place to talk about the structure of
our logic - that we've set up the hoare_* lemmas and they are all
the reasoning about Hoare triples that they should have to use (in
both formal or informal proofs)?  Probably should talk about this
somewhere or else we'll get back lots of proofs that unfold
ValidHoareTriple and reason at a low level everywhere.

BCP 21: I think we do this now?
```
:::

::::hide
```
/- LATER: Next year, these should be moved up to the section on
valid Hoare triples and proved directly there (using, in the
second case, the fact that this loop does not terminate),
rather than using the while rule. -/
/- LATER: Point out the trick using intros to do the splitting. -/
theorem never_loop_hoare (P : Assertion) (c : Com) :
    {{ P }} while (false) { ~c } {{ P }} := by
  apply hoare_consequence_post
  · apply hoare_while
    -- loop body preserves loop invariant
    apply hoare_pre_false
    intro st ⟨_hP, hFalse⟩
    simp [bassertion] at hFalse
  · -- loop invariant and negation of guard imply postcondition
    intro st ⟨hinv, _hguard⟩
    assumption
```
::::

::::quiz
Is the assertion

```display
X > 0
```

a loop invariant of the following?

```display
while X = 0 do X := X - 1 end
```

(A) Yes

(B) No

:::instructors
```
BCP: According to how we defined the term, the answer
should be Yes!  The reason is that a loop invariant is defined as a
P that, _together with the fact that the guard is true_ implies
P.
```
:::
::::

::::quiz
Is the assertion

```display
X < 100
```

a loop invariant of the following?

```display
while X < 100 do X := X + 1 end
```

(A) Yes

(B) No
::::

:::instructors
NO
:::

::::quiz
Is the assertion

```display
X > 10
```

a loop invariant of the following?

```display
while X > 10 do X := X + 1 end
```

(A) Yes

(B) No
::::

:::instructors
YES
:::

::::full
If the loop never terminates, any postcondition will work.

:::instructors
This is good to work in class, but make sure you try
it yourself beforehand!  Getting it to work smoothly depends on
doing the right things at the beginning.

MRC'20: Maybe I'm an outlier, but a WORKINCLASS that surprises me
and maybe gets me stuck is not ideal. The truly interesting thing
about this example is that it's provable --not the actual proof.
I propose that it not be worked in class, but that the proof
be provided.

BCP 20: OK, fair enough.
:::

:::dev "Michael Clarkson (clarksmr)" PotentialImprovement (year := 2020)
It would be nice to automate the second bullet.
:::

```lean
theorem always_loop_hoare (Q : Assertion) :
    {{True}} while (true) { skip } {{ Q }} := by
  apply hoare_consequence_post
  · apply hoare_while
    apply hoare_post_true
    intro st
    exact True.intro
  · intro st ⟨_, hguard⟩
    simp at hguard
```
::::

::::hide
```lean
/- A different way through the proof... -/
theorem always_loop_hoare' (P Q : Assertion) :
    {{ P }} while (true) { skip } {{ Q }} := by
  apply hoare_consequence_pre (P' := {{ True }})
  · apply hoare_consequence_post
    · apply hoare_while
      -- Loop body preserves loop invariant
      apply hoare_post_true
      intro st
      exact True.intro
    · -- Loop invariant and negated guard imply postcondition
      intro st ⟨_, hguard⟩
      simp at hguard
  · -- Precondition implies loop invariant
    intro st _
    exact True.intro

/- And, of course, there is also the low-level way to do it, without using
Hoare logic... -/
theorem always_loop_hoare'' (P Q : Assertion) :
    {{ P }} while (true) { skip } {{ Q }} := by
  rw [validHoareTriple_def]
  intro st st' heval _hP
  have key : ∀ (cmd : Com) (s s' : State), (s =[ cmd ]=> s') →
      cmd = (imp { while (true) { skip } }) → Q s' := by
    intro cmd s s' hev
    induction hev with
    | whileFalse b0 s0 c0 hb =>
        intro heq
        injection heq with e1 _
        subst e1
        simp at hb
    | whileTrue s0 s0' s0'' b0 c0 hb hc hloop ih1 ih2 =>
        intro heq
        exact ih2 heq
    | skip s0 => intro heq; simp at heq
    | asgn s0 a n x h => intro heq; simp at heq
    | seq c1 c2 s0 s0' s0'' h1 h2 ih1 ih2 => intro heq; simp at heq
    | ifTrue s0 s0' b0 c1 c2 hb hc ih => intro heq; simp at heq
    | ifFalse s0 s0' b0 c1 c2 hb hc ih => intro heq; simp at heq
  exact key _ st st' heval rfl
/- ... But this really misses the point! -/
```
::::

::::full
Of course, this result is not surprising if we remember that
the definition of `ValidHoareTriple` asserts that the postcondition
must hold _only_ when the command terminates.  If the command
doesn't terminate, we can prove anything we like about the
post-condition.

Hoare rules that specify what happens _if_ commands terminate,
without proving that they do, are said to describe a logic of
_partial_ correctness.  It is also possible to give Hoare rules
for _total_ correctness, which additionally specifies that
commands must terminate. Total correctness is out of the scope of
this textbook.
::::

### Exercise: `repeat`

:::suppressPreviousHeaderWhenTerse
:::

:::dev
HIDE: I (BCP) think I see a much simpler way to do the 'for' stuff.
Instead of `for x from a to b do c` define `for x downfrom a do c`
that steps from a down to 0.  This will be much simpler to specify,
though still an interesting challenge. (CJC: This still seemed hard
to me, but I'm deleting it for now to get things looking right)

HIDE: Coming up with the precise rule for REPEAT is tricky, and so
is proving formally that the precise rule passes the litmus
test (at this point we only ask them to convince themselves
informally there).
:::

:::dev PotentialImprovement
PLW: Chapters Imp and Equiv have exercises based on extending
Imp with C-style FOR loops. Either this chapter should use C-style
for loops in place of repeat, or those chapters should use repeat
in place of C-style for loops.
:::

:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement (year := 2020)
I think this exercise is not actually very nice --
the hoare rule for repeat is really not that nice.  Let's do
replace with FOR-DOWNTO as suggested.
BCP 21: For the moment, I'm making it optional.
:::

::::::full
In this exercise, we'll add a new command to our language of
commands: `repeat { c } until (b)`. You will write the
evaluation rule for `repeat` and add a new Hoare rule to the
language for programs involving it.

```lean
namespace RepeatExercise

inductive Com : Type where
  | skip : Com
  | asgn : Ident → Aexp → Com
  | seq : Com → Com → Com
  | cond : Bexp → Com → Com → Com
  | whileDo : Bexp → Com → Com
  | repeatUntil : Com → Bexp → Com
```

`repeat` behaves like `while`, except that the loop guard is
checked _after_ each execution of the body, with the loop
repeating as long as the guard stays _false_.  Because of this,
the body will always execute at least once.

```lean
/-- Repeat loop -/
syntax "repeat" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}") " until " "(" imp_bexp ")" : imp_com

open Lean in
scoped macro_rules
  | `(imp { $x:ident }) =>
    if x.getId == `skip then `(Com.skip)
    else Macro.throwErrorAt x s!"expected 'skip', got '{x.getId}'"
  | `(imp { $c1; $c2 }) =>
    `(Com.seq (imp {$c1}) (imp {$c2}))
  | `(imp { $x:ident := $a }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c1} else {$c2} }) =>
    `(Com.cond (bexp {$b}) (imp {$c1}) (imp {$c2}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { repeat {$c} until ($b) }) =>
    `(Com.repeatUntil (imp {$c}) (bexp {$b}))
  | `(imp { ~$c }) =>
    pure c
```

::::::

::::::full
:::::exercise (rating := 4) (name := "hoare_repeat") (level := Advanced) (optional := true) (manual := true)
Add new rules for `repeat` to `Com.EvalR` below.  You can use the rules
for `while` as a guide, but remember that the body of a `repeat`
should always execute at least once, and that the loop ends when
the guard becomes true.

```lean
inductive Com.EvalR : Com → State → State → Prop where
  | skip {st : State} :
      EvalR (imp {skip}) st st
  | asgn {st : State} (a : Aexp) {n : Nat} (x : Ident) (h : a.eval st = n) :
      EvalR (imp {x := ~a}) st (x →ₜ n ; st)
  | seq {c1 c2 : Com} (st st' st'' : State)
      (h1 : EvalR c1 st st') (h2 : EvalR c2 st' st'') :
      EvalR (imp {~c1; ~c2}) st st''
  | ifTrue {st st' : State} (b : Bexp) {c1 c2 : Com} (hb : b.eval st = true)
      (hc : EvalR c1 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st st'
  | ifFalse {st st' : State} (b : Bexp) {c1 c2 : Com} (hb : b.eval st = false)
      (hc : EvalR c2 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st st'
  | whileFalse {b : Bexp} (st : State) (c : Com) (hb : b.eval st = false) :
      EvalR (imp {while (~b) {~c} }) st st
  | whileTrue {st st' st'' : State} {b : Bexp} {c : Com}
      (hb : b.eval st = true) (hc : EvalR c st st')
      (hloop : EvalR (imp {while (~b) {~c} }) st' st'') :
      EvalR (imp {while (~b) {~c} }) st st''
-- SOLUTION
  | repeatEnd {st st' : State} {b : Bexp} {c : Com} (hc : EvalR c st st')
      (hb : b.eval st' = true) :
      EvalR (imp {repeat {~c} until (~b) }) st st'
  | repeatLoop {st st' st'' : State} {b : Bexp} {c : Com}
      (hc : EvalR c st st') (hb : b.eval st' = false)
      (hloop : EvalR (imp {repeat {~c} until (~b) }) st' st'') :
      EvalR (imp {repeat {~c} until (~b) }) st st''
-- END SOLUTION

instance : HasEval Com State State where
  Eval := Com.EvalR

@[app_unexpander Com.EvalR]
def Com.unexpandEvalR : Lean.PrettyPrinter.Unexpander
  | `($_ $c $st0 $st1) => ``($st0 =[ ~$c ]=> $st1)
  | _ => throw ()
```

A couple of definitions from above, copied here so they use the
new `Com.EvalR`.

```lean
def ValidHoareTriple
    (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ {st st' : State},
    (st =[ c ]=> st') →
    P st →
    Q st'

instance : HasTriple Com where
  Triple := ValidHoareTriple

theorem validHoareTriple_def {P : Assertion} {c : Com} {Q : Assertion} :
    {{ P }} ~c {{ Q }} ↔ ∀ {st st' : State},
      (st =[ c ]=> st') →
      P st →
      Q st' := by rfl

attribute [irreducible] ValidHoareTriple
```

To make sure you've got the evaluation rules for `repeat` right,
prove that `ex1_repeat` evaluates correctly.

```lean
def ex1_repeat : Com :=
  imp {
    repeat {
      X := 1;
      Y := Y + 1
    } until (X = 1)
  }

theorem ex1_repeat_works :
    ∅ =[ ex1_repeat ]=> (Y →ₜ 1 ; X →ₜ 1) := by
  solution!
    apply Com.EvalR.repeatEnd
    · apply Com.EvalR.seq
      · apply Com.EvalR.asgn; rfl
      · apply Com.EvalR.asgn; rfl
    · simp +decide
```

:::dev "Niklas Halonen (xhalo32)"
Do we want to `open Com.EvalR` to make the previous proof easier to write?
:::

Now state and prove a theorem, `hoare_repeat`, that expresses an
appropriate proof rule for `repeat` commands.  Use `hoare_while`
as a model, and try to make your rule as precise as possible.

```lean
-- SOLUTION

/- Here is a very precise version of `hoare_repeat`. -/
/- LATER: A student in 2013 pointed out that this rule is OK as far
as it goes, but it isn't going to lead to a nice rule for decorated
programs, when we get to that, because it uses c twice, perhaps in
different ways! -/

theorem hoare_repeat {P Q : Assertion} {b : Bexp} {c : Com}
    (h1 : {{ P }} ~c {{ Q }}) (h2 : {{ Q ∧ ¬ b }} ~c {{ Q }}) :
    {{ P }} repeat { ~c } until (~b) {{ Q ∧ b }} := by
  rw [validHoareTriple_def] at h1 h2 ⊢
  intro st st' heval hpre
  generalize heq : (imp { repeat { ~c } until (~b) }) = cmd at heval
  induction heval generalizing P with
  | @repeatEnd s0 s0' b0 c0 hc hb ih =>
    injection heq with hceq hbeq
    subst hceq hbeq
    exact ⟨h1 hc hpre, hb⟩
  | @repeatLoop s0 s0' s0'' b0 c0 hc hb hloop ih1 ih2 =>
    injection heq with hceq hbeq
    subst hceq hbeq
    apply ih2 h2 _ rfl
    constructor
    · exact h1 hc hpre
    · simp [hb]
  | skip | asgn | seq | ifTrue | ifFalse | whileFalse | whileTrue =>
    contradiction
-- END SOLUTION
```

For full credit, make sure (informally) that your rule can be used
to prove the following valid Hoare triple:

```display
{{ X > 0 }}
repeat {
  Y := X;
  X := X - 1;
} until (X = 0)
{{ X = 0 ∧ Y > 0 }}
```

:::grade
`GRADE_MANUAL 6: hoare_repeat`
:::
:::::

:::dev "Claude"
The Rocq exercise region extends to End RepeatExercise. The directive
here covers only the part up to the litmus-test display because Verso
cannot compile the whole module as one block.
:::

::::::

::::::full
```lean
-- SOLUTION

/- Although it was not required by the exercise, we can show formally
that `hoare_repeat` can handle this litmus test: -/

def ex2_repeat : Com :=
  imp {
    repeat {
      Y := X;
      X := X - 1
    } until (X = 0)
  }

/- Before we can show anything about this program we need to repeat
the proofs of some more Hoare rules from above (remember we're in
a separate namespace, with a different definition of commands). -/

theorem hoare_asgn {Q : Assertion} {x : Ident} {a : Aexp} :
    {{Q [x ↦ ~a]}} x := ~a {{ Q }} := by
  rw [validHoareTriple_def]
  intro st st' hE hQ
  rw [Assertion.subst_apply] at hQ
  inversion hE with
  | asgn n h =>
    subst h
    exact hQ

theorem hoare_consequence {P P' Q Q' : Assertion} {c : Com}
    (hht : {{ P' }} ~c {{ Q' }}) (hPP' : P ->> P') (hQ'Q : Q' ->> Q) :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hht ⊢
  intro st st' hc hP
  apply_rules

theorem hoare_consequence_pre {P P' Q : Assertion} {c : Com}
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' hc hP
  apply_rules

theorem hoare_seq {P Q R : Assertion} {c1 c2 : Com}
    (h1 : {{ Q }} ~c2 {{R}}) (h2 : {{ P }} ~c1 {{ Q }}) :
    {{ P }} ~c1; ~c2 {{R}} := by
  rw [validHoareTriple_def] at h1 h2 ⊢
  intro st st' h12 pre
  inversion h12 with
  | seq st'' hc1 hc2 =>
    apply_rules

-- END SOLUTION
```
::::::

::::::full
```lean
-- SOLUTION
/- Now we are ready to show `ex2_repeat` correct using `hoare_repeat`. -/
/- NOTATION: IY -- I've noticed this oddity in previous lemmas, but
it's especially noticable here that an explicit state is given to
the conditional statements. -/
theorem ex2_repeat_hoare_repeat :
    {{ X > 0 }}
      ~ex2_repeat
    {{ X = 0 ∧ Y > 0 }} := by
  rw [ex2_repeat]
  apply hoare_consequence
  · apply hoare_repeat (Q := {{ Y > 0 }})
    · apply hoare_seq hoare_asgn hoare_asgn
    · apply hoare_seq hoare_asgn
      apply hoare_consequence_pre hoare_asgn
      assertion_auto
  · -- body of repeat if exiting right away
    assertion_auto
  · -- final postcondition
    assertion_auto

/- A sound but less precise variant of the `hoare_repeat` rule looks
like this: -/

/- NOTATION: Here, too, the printing isn't as we write the notation.
(As soon as we start the proof context). Is this intended? -/
theorem hoare_repeat' (P : Assertion) (b : Bexp) (c : Com)
    (h : {{ P }} ~c {{ P }}) :
    {{ P }} repeat { ~c } until (~b) {{ P ∧ b }} := by
  rw [validHoareTriple_def]
  intro st st' he hP
  have key : ∀ (cmd : Com) (s s' : State), (s =[ cmd ]=> s') →
      cmd = (imp { repeat { ~c } until (~b) }) → P s →
      P s' ∧ b.eval s' := by
    intro cmd s s' hev
    induction hev with
    | @repeatEnd s0 s0' b0 c0 hc hb =>
        intro heq hp
        injection heq with e1 e2
        subst e1 e2
        rw [validHoareTriple_def] at h
        exact ⟨h hc hp, hb⟩
    | @repeatLoop s0 s0' s0'' b0 c0 hc hb hloop ih1 ih2 =>
        intro heq hp
        injection heq with e1 e2
        subst e1 e2
        rw [validHoareTriple_def] at h
        exact ih2 rfl (h hc hp)
    | @skip s0 => intro heq; simp at heq
    | @asgn s0 a n x ha => intro heq; simp at heq
    | @seq c1 c2 s0 s0' s0'' hh1 hh2 ih1 ih2 => intro heq; simp at heq
    | @ifTrue s0 s0' b0 c1 c2 hb hc ih => intro heq; simp at heq
    | @ifFalse s0 s0' b0 c1 c2 hb hc ih => intro heq; simp at heq
    | @whileFalse b0 s0 c0 hb => intro heq; simp at heq
    | @whileTrue s0 s0' s0'' b0 c0 hb hc hloop ih1 ih2 =>
        intro heq; simp at heq
  exact key _ st st' he rfl hP

/- First, let's show that `hoare_repeat'` is implied by `hoare_repeat`. -/

theorem hoare_repeat_implies_hoare_repeat'
    (hoare_repeat : ∀ (P Q : Assertion) (b : Bexp) (c : Com),
      ({{ P }} ~c {{ Q }}) →
      ({{ Q ∧ ¬ b }} ~c {{ Q }}) →
      {{ P }} repeat { ~c } until (~b) {{ Q ∧ b }}) :
    ∀ (P : Assertion) (b : Bexp) (c : Com),
      ({{ P }} ~c {{ P }}) →
      {{ P }} repeat { ~c } until (~b) {{ P ∧ b }} := by
  intro P b c h
  apply hoare_repeat <;> try assumption
  apply hoare_consequence_pre
  · exact h
  · intro st ⟨hp, _⟩
    exact hp

-- END SOLUTION
```
::::::

::::::full
```lean
-- SOLUTION
/- However, we can't prove `ex2_repeat` correct using `hoare_repeat'`,
even with a stronger initial precondition on `Y`. Here is a first
failed proof attempt. -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example :
    {{ X > 0 ∧ Y > 0}}
      ~ex2_repeat
    {{ X = 0 ∧ Y > 0}} := by
  apply hoare_consequence
  · apply hoare_repeat' (P := {{ Y > 0 }})
    apply hoare_seq hoare_asgn
    apply hoare_consequence_pre hoare_asgn
    intro st hy
    simp
    -- loop invariant too weak on its own,
    -- we need the value of the previous guard
    sorry
  · -- initial precondition
    intro st ⟨_, hy⟩
    exact hy
    -- this only works with an additional Y > 0 precondition
  · -- final postcondition
    assertion_auto

/- Here is a second failed attempt trying stronger loop invariant, but
it is too strong. -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example :
    {{ X > 0 ∧ Y > 0}}
      ~ex2_repeat
    {{ X = 0 ∧ Y > 0}} := by
  apply hoare_consequence
  · apply hoare_repeat' (P := {{ X > 0 ∧ Y > 0 }})
    apply hoare_seq hoare_asgn
    apply hoare_consequence_pre hoare_asgn
    intro st ⟨hx, hy⟩
    simp
    -- loop invariant too strong
    sorry
  · -- initial precondition
    intro st hp
    exact hp
  · -- final postcondition
    assertion_auto

-- END SOLUTION
end RepeatExercise
```

::::::

# Summary

:::dev PotentialImprovement
Full version could use some more text.
:::

::::full
So far, we've introduced Hoare Logic as a tool for reasoning about
Imp programs.
::::

The rules of Hoare Logic are:

```display
       --------------------------- (hoare_asgn)
       {{Q [X ↦ a]}} X:=a {{Q}}

       --------------------  (hoare_skip)
       {{ P }} skip {{ P }}

         {{ P }} c1 {{ Q }}
         {{ Q }} c2 {{ R }}
        ----------------------  (hoare_seq)
        {{ P }} c1;c2 {{ R }}

        {{P ∧   b}} c1 {{Q}}
        {{P ∧ ¬ b}} c2 {{Q}}
------------------------------------  (hoare_if)
{{P}} if b then c1 else c2 end {{Q}}

         {{P ∧ b}} c {{P}}
  -----------------------------------  (hoare_while)
  {{P}} while b do c end {{P ∧ ¬ b}}

          {{P'}} c {{Q'}}
             P ->> P'
             Q' ->> Q
   -----------------------------   (hoare_consequence)
          {{P}} c {{Q}}
```

:::slidebreak
:::

Our main task in this chapter has been to _define_ the rules of
Hoare logic, and prove that the definitions are sound.  Having
done so, we can go on and work _within_ Hoare logic to prove that
particular programs satisfy particular Hoare triples.  In the next
chapter, we'll see how Hoare logic is can be used to prove that
more interesting programs satisfy interesting specifications of
their behavior.

Crucially, we will do so without ever again `unfold`ing the
definition of Hoare triples -- i.e., we will take the rules of
Hoare logic as a closed world for reasoning about programs.

# Additional Exercises

:::suppressPreviousHeaderWhenTerse
:::

:::dev PotentialImprovement
Possible exercise: Show that TRUE and FALSE are loop invariants
of every while loop.  Explain why this is not useful.

Another interesting problem that we could try to work out in detail:
total-correctness Hoare Logic.  The crucial rule would be something like this:

              T not in vars(c)
      `P ∧ b ∧ a = T` c `P ∧ a < T`
      --------------------------------
       `P` while b do c end `P ∧ ¬ b`

We could define TC-triples, ask them to prove this rule, and then in
Hoare2.v, as them to carry out some proofs as decorated programs.
(Asking them to prove this rule might be a bit much, though -- probably
requires some fanciness with Rocq...)
:::

## Havoc

:::suppressPreviousHeaderWhenTerse
:::

::::::full
In this exercise, we will derive proof rules for a `havoc`
command, which is similar to the nondeterministic `any` expression
from the the {ref "Imp"}[Imp] chapter.

First, we enclose this work in a separate namespace, and recall the
syntax and big-step semantics of Himp commands.

```lean
namespace Himp

inductive Com : Type where
  | skip : Com
  | asgn : Ident → Aexp → Com
  | seq : Com → Com → Com
  | cond : Bexp → Com → Com → Com
  | whileDo : Bexp → Com → Com
  | havoc : Ident → Com

/-- Havoc: set a variable to a nondeterministically chosen number
(`havoc x;`).  As with `skip`, the word `havoc` is not reserved: the
production accepts any identifier and the macro below rejects
everything except `havoc`. -/
scoped syntax ident ident : imp_com

open Lean in
scoped macro_rules
  | `(imp { $x:ident }) =>
    if x.getId == `skip then `(Com.skip)
    else Macro.throwErrorAt x s!"expected 'skip', got '{x.getId}'"
  | `(imp { $c1; $c2 }) =>
    `(Com.seq (imp {$c1}) (imp {$c2}))
  | `(imp { $x:ident := $a }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c1} else {$c2} }) =>
    `(Com.cond (bexp {$b}) (imp {$c1}) (imp {$c2}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { $h:ident $x:ident }) =>
    if h.getId == `havoc then `(Com.havoc $x)
    else Macro.throwErrorAt h s!"expected 'havoc', got '{h.getId}'"
  | `(imp { ~$c }) =>
    pure c

inductive Com.EvalR : Com → State → State → Prop where
  | skip {st : State} :
      EvalR (imp {skip}) st st
  | asgn {st : State} {a : Aexp} {n : Nat} {x : Ident} (h : a.eval st = n) :
      EvalR (imp {x := ~a}) st (x →ₜ n ; st)
  | seq {c1 c2 : Com} {st st' st'' : State}
      (h1 : EvalR c1 st st') (h2 : EvalR c2 st' st'') :
      EvalR (imp {~c1; ~c2}) st st''
  | ifTrue {st st' : State} {b : Bexp} {c1 c2 : Com} (hb : b.eval st = true)
      (hc : EvalR c1 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st st'
  | ifFalse {st st' : State} {b : Bexp} {c1 c2 : Com} (hb : b.eval st = false)
      (hc : EvalR c2 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st st'
  | whileFalse {b : Bexp} {st : State} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {while (~b) {~c} }) st st
  | whileTrue {st st' st'' : State} {b : Bexp} {c : Com}
      (hb : b.eval st = true) (hc : EvalR c st st')
      (hloop : EvalR (imp {while (~b) {~c} }) st' st'') :
      EvalR (imp {while (~b) {~c} }) st st''
  | havoc {st : State} {x : Ident} {n : Nat} :
      EvalR (imp {havoc x}) st (x →ₜ n ; st)

instance : HasEval Com State State where
  Eval := Com.EvalR

@[app_unexpander Com.EvalR]
def Com.unexpandEvalR : Lean.PrettyPrinter.Unexpander
  | `($_ $c $st0 $st1) => ``($st0 =[ ~$c ]=> $st1)
  | _ => throw ()
```

The definition of Hoare triples is exactly as before.

```lean
def ValidHoareTriple
    (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ {st st' : State},
    (st =[ c ]=> st') →
    P st →
    Q st'

instance : HasTriple Com where
  Triple := ValidHoareTriple

theorem validHoareTriple_def {P : Assertion} {c : Com} {Q : Assertion} :
    {{ P }} ~c {{ Q }} ↔ ∀ {st st' : State},
      (st =[ c ]=> st') →
      P st →
      Q st' := by rfl

attribute [irreducible] ValidHoareTriple
```

And the precondition consequence rule is exactly as before.

```lean
theorem hoare_consequence_pre {P P' Q : Assertion} {c : Com}
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st st' heval hpre
  apply_rules
```

:::::exercise (rating := 3) (name := "hoare_havoc") (level := Advanced)
:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2021)
This exercise turns out to be quite hard -- a lot
of people get stuck.  We should make it advanced the next time
through.  BCP 23: Made it advanced.  Can we also explain it better?
:::

Complete the Hoare rule for `havoc` commands below by defining
`havoc_pre`, and prove that the resulting rule is correct.

```lean
def havoc_pre (x : Ident) (Q : Assertion) (st : State) : Prop :=
  solution!(∀ (n : Nat), ({{ Q [x ↦ ~(.num n)] }}) st)

theorem hoare_havoc {Q : Assertion} {x : Ident} :
    {{ fun st => havoc_pre x Q st }} havoc x {{ Q }} := by
  solution!
    rw [validHoareTriple_def]
    intro st st' heval hpre
    rw [havoc_pre] at hpre
    inversion heval with
    | havoc n =>
      specialize hpre n
      simp only [Assertion.subst_apply, Aexp.eval_num] at hpre
      exact hpre
```
:::::

:::::exercise (rating := 3) (name := "havoc_post") (level := Advanced)
Complete the following proof without changing any of the provided
commands. If you find that it can't be completed, your definition of
`havoc_pre` is probably too strong. Find a way to relax it so that
`havoc_post` can be proved.

Hint: the `assertion_auto` tactics we've built won't help you here.
You need to proceed manually.

:::instructors
```
for example, {{ False }} havoc X {{ P }} would
be a sound but incomplete rule in which the precondition is
too strong.
```
:::

:::dev "Michael Clarkson (clarksmr)" PotentialImprovement (year := 2020)
sure would be nice to automate this better.
:::

:::instructors
can't unfold `havoc_pre` outside the ADMITTED block,
because its definition is admitted.
:::

:::dev BeforeNextRelease
This exercise is kind of weird.  Should probably be
optional.
:::

```lean
theorem havoc_post {P : Assertion} {x : Ident} :
    {{ P }}
    havoc x
    {{ fun st => ∃ (n : Nat), ({{ P [x ↦ ~(.num n)] }}) st }} := by
  apply hoare_consequence_pre
  · apply hoare_havoc
  · solution!
      intro st hpre n
      simp only [Assertion.subst_apply, Aexp.eval_num, TotalMap.update_shadow]
      exists st[x]
      rw [TotalMap.update_same]
      exact hpre
```
:::::

```lean
end Himp
```
::::::

## Assert and Assume

:::suppressPreviousHeaderWhenTerse
:::

::::::full
:::dev "Claude"
The Rocq exercise region extends to End HoareAssertAssume. The directive
here covers only the initial student tasks because Verso cannot compile the
whole module as one block.
:::

In this exercise, we will extend IMP with two commands, `assert`
and `assume`. Both commands are ways to indicate that a certain
assertion should hold any time this part of the program is
reached. However they differ as follows:

- If an `assert` statement fails, it causes the program to go into
  an error state and exit.

- If an `assume` statement fails, the program fails to evaluate at
  all. In other words, the program gets stuck and has no final
  state.

The new set of commands is:

```lean
namespace HoareAssertAssume

inductive Com : Type where
  | skip : Com
  | asgn : Ident → Aexp → Com
  | seq : Com → Com → Com
  | cond : Bexp → Com → Com → Com
  | whileDo : Bexp → Com → Com
  | assert : Bexp → Com
  | assume : Bexp → Com
```

:::dev
NOTATION: LATER: Reconsider these precedences
:::

```lean
/-- Assert / assume (`assert (b);`, `assume (b);`).  As with `skip`, the
words `assert` and `assume` are not reserved: the production accepts any
identifier and the macro below rejects everything else. -/
scoped syntax ident " (" imp_bexp ")" : imp_com

open Lean in
scoped macro_rules
  | `(imp { $x:ident }) =>
    if x.getId == `skip then `(Com.skip)
    else Macro.throwErrorAt x s!"expected 'skip', got '{x.getId}'"
  | `(imp { $h:ident ($b) }) =>
    if h.getId == `assert then `(Com.assert (bexp {$b}))
    else if h.getId == `assume then `(Com.assume (bexp {$b}))
    else Macro.throwErrorAt h s!"expected 'assert' or 'assume', got '{h.getId}'"
  | `(imp { $c1; $c2 }) =>
    `(Com.seq (imp {$c1}) (imp {$c2}))
  | `(imp { $x:ident := $a }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c1} else {$c2} }) =>
    `(Com.cond (bexp {$b}) (imp {$c1}) (imp {$c2}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { ~$c }) =>
    pure c
```

::::::

::::::full
To define the behavior of `assert` and `assume`, we need to add
notation for an error, which indicates that an assertion has
failed. We modify the `Com.EvalR` relation, therefore, so that
it relates a start state to either an end state or to `error`.
The `Result` type indicates the end value of a program,
either a state or an error:

```lean
inductive Result : Type where
  | normal (st : State) : Result
  | error : Result
```

Now we are ready to give you the evaluation relation for the new
language.

```lean
inductive Com.EvalR : Com → State → Result → Prop where
  /- Old rules, several modified -/
  | skip {st : State} :
      EvalR (imp {skip}) st (.normal st)
  | asgn {st : State} {a : Aexp} {n : Nat} {x : Ident} (h : a.eval st = n) :
      EvalR (imp {x := ~a}) st (.normal (x →ₜ n ; st))
  | seqNormal {c1 c2 : Com} {st st' : State} {r : Result}
      (h1 : EvalR c1 st (.normal st')) (h2 : EvalR c2 st' r) :
      EvalR (imp {~c1; ~c2}) st r
  | seqError {c1 c2 : Com} {st : State} (h : EvalR c1 st .error) :
      EvalR (imp {~c1; ~c2}) st .error
  | ifTrue {st : State} {r : Result} {b : Bexp} {c1 c2 : Com}
      (hb : b.eval st = true) (hc : EvalR c1 st r) :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st r
  | ifFalse {st : State} {r : Result} {b : Bexp} {c1 c2 : Com}
      (hb : b.eval st = false) (hc : EvalR c2 st r) :
      EvalR (imp {if (~b) {~c1} else {~c2} }) st r
  | whileFalse {b : Bexp} {st : State} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {while (~b) {~c} }) st (.normal st)
  | whileTrueNormal {st st' : State} {r : Result} {b : Bexp} {c : Com}
      (hb : b.eval st = true) (hc : EvalR c st (.normal st'))
      (hloop : EvalR (imp {while (~b) {~c} }) st' r) :
      EvalR (imp {while (~b) {~c} }) st r
  | whileTrueError {st : State} {b : Bexp} {c : Com}
      (hb : b.eval st = true) (hc : EvalR c st .error) :
      EvalR (imp {while (~b) {~c} }) st .error
  /- Rules for Assert and Assume -/
  | assertTrue {st : State} {b : Bexp} (hb : b.eval st = true) :
      EvalR (imp {assert (~b)}) st (.normal st)
  | assertFalse {st : State} {b : Bexp} (hb : b.eval st = false) :
      EvalR (imp {assert (~b)}) st .error
  | assume {st : State} {b : Bexp} (hb : b.eval st = true) :
      EvalR (imp {assume (~b)}) st (.normal st)

instance : HasEval Com State Result where
  Eval := Com.EvalR

@[app_unexpander Com.EvalR]
def Com.unexpandEvalR : Lean.PrettyPrinter.Unexpander
  | `($_ $c $st0 $st1) => ``($st0 =[ ~$c ]=> $st1)
  | _ => throw ()
```

We redefine hoare triples: Now, `{{ P }} c {{ Q }}` means that,
whenever `c` is started in a state satisfying `P`, and terminates
with result `r`, then `r` is not an error and the state of `r`
satisfies `Q`.

```lean
def ValidHoareTriple
    (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ {st : State} {r : Result},
    (st =[ c ]=> r) → P st →
    ∃ st', r = Result.normal st' ∧ Q st'

instance : HasTriple Com where
  Triple := ValidHoareTriple

theorem validHoareTriple_def {P : Assertion} {c : Com} {Q : Assertion} :
    {{ P }} ~c {{ Q }} ↔ ∀ {st : State} {r : Result},
      (st =[ c ]=> r) → P st →
      ∃ st', r = Result.normal st' ∧ Q st' := by rfl

attribute [irreducible] ValidHoareTriple
```

:::dev PotentialImprovement
I think the way I stated hoare triples may need cleaning
up.  It doesn't work very well for the proofs of hoare rules to
have `exists st'` in the conclusion.  BCP 10/18: Not sure what sort
of cleaning up would be useful...
:::

::::::

::::::full
:::::exercise (rating := 4) (name := "assert_vs_assume")
To test your understanding of this modification, give an example
precondition and postcondition that are satisfied by the `assume`
statement but not by the `assert` statement.

```lean
theorem assert_assume_differ : ∃ (P : Assertion) (b : Bexp) (Q : Assertion),
    ({{ P }} assume (~b) {{ Q }})
    ∧ ¬ ({{ P }} assert (~b) {{ Q }}) := by
  solution!
    exists {{ True }}, bexp { false }, ({{ False }})
    constructor
    · rw [validHoareTriple_def]
      intro st r heval _
      inversion heval with
      | assume hb => simp at hb
    · intro hC
      rw [validHoareTriple_def] at hC
      have h : ∅ =[ assert (false) ]=> Result.error := by
        apply Com.EvalR.assertFalse
        simp
      obtain ⟨st', h1, h2⟩ := hC h True.intro
      contradiction
```

:::dev "Niklas Halonen (xhalo32)"
For some reason, after `rw [validHoareTriple_def] at hC`, the existence turns into `Exists ({{r = Result.normal ∧ False}})`.
Maybe it's the assertion delaborator?
:::

:::gradeTheorem 1 assert_assume_differ
:::

Then prove that any triple for an `assert` also works when
`assert` is replaced by `assume`.

```lean
theorem assert_implies_assume (P : Assertion) (b : Bexp) (Q : Assertion)
    (hhoare : {{ P }} assert (~b) {{ Q }}) :
    {{ P }} assume (~b) {{ Q }} := by
  solution!
    rw [validHoareTriple_def] at hhoare ⊢
    intro st r heval hpre
    inversion heval with
    | assume hb =>
      exists st
      have h : st =[ assert (~b) ]=> Result.normal st := by
        apply Com.EvalR.assertTrue
        assumption
      obtain ⟨st', h1, h2⟩ := hhoare h hpre
      injection h1 with hsteq
      subst hsteq
      exact ⟨rfl, h2⟩
```

:::gradeTheorem 1 assert_implies_assume
:::
:::::
::::::

::::::full
Next, here are proofs for the old hoare rules adapted to the new
semantics.  You don't need to do anything with these.

```lean
theorem hoare_asgn {Q : Assertion} {x : Ident} {a : Aexp} :
    {{Q [x ↦ ~a]}} x := ~a {{ Q }} := by
  rw [validHoareTriple_def]
  intro st r heval hQ
  rw [Assertion.subst_apply] at hQ
  inversion heval with
  | asgn n h =>
    exists (x →ₜ n ; st)
    subst h
    exact ⟨rfl, hQ⟩

theorem hoare_consequence_pre {P P' Q : Assertion} {c : Com}
    (hhoare : {{ P' }} ~c {{ Q }}) (himp : P ->> P') :
    {{ P }} ~c {{ Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st r hc hpre
  apply_rules
```

:::dev PotentialImprovement
These proofs are a bit messy. Can it be made shorter?
:::

```lean
theorem hoare_consequence_post {P Q Q' : Assertion} {c : Com}
    (hhoare : {{ P }} ~c {{ Q' }}) (himp : Q' ->> Q) :
    {{ P }} ~c {{   Q }} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st r hc hpre
  obtain ⟨st', hr, hQ'⟩ := hhoare hc hpre
  exists st'
  exact ⟨hr, himp _ hQ'⟩

theorem hoare_seq {P Q R : Assertion} {c1 c2 : Com}
    (h1 : {{ Q }} ~c2 {{R}}) (h2 : {{ P }} ~c1 {{ Q }}) :
    {{ P }} ~c1; ~c2 {{R}} := by
  rw [validHoareTriple_def] at h1 h2 ⊢
  intro st r h12 hpre
  inversion h12 with
  | seqNormal st' hc1 hc2 =>
    apply h1 hc2
    specialize h2 hc1 hpre
    obtain ⟨st'', heq, hQ⟩ := h2
    injection heq with e
    subst e
    exact hQ
  | seqError hc1 =>
    -- Find contradictory assumption
    specialize h2 hc1 hpre
    obtain ⟨st', hC, _⟩ := h2
    contradiction
```

:::dev PotentialImprovement
HIDE
:::

::::::

::::::full
Here are the other proof rules (sanity check)

```lean
theorem hoare_skip {P : Assertion} :
    {{ P }} skip {{ P }} := by
  rw [validHoareTriple_def]
  intro st r h hpre
  inversion h
  exact ⟨st, rfl, hpre⟩

theorem hoare_if {P Q : Assertion} {b : Bexp} {c1 c2 : Com}
    (hTrue : {{ P ∧ b}} ~c1 {{ Q }}) (hFalse : {{ P ∧ ¬ b}} ~c2 {{ Q }}) :
    {{ P }} if (~b) { ~c1 } else { ~c2 } {{ Q }} := by
  rw [validHoareTriple_def] at hTrue hFalse ⊢
  intro st r hE hpre
  inversion hE with
  | ifTrue hb hc =>
    -- b is true
    apply_rules [And.intro]
  | ifFalse hb hc =>
    -- b is false
    apply hFalse hc
    exact ⟨hpre, by simp [hb]⟩

theorem hoare_while {P : Assertion} {b : Bexp} {c : Com}
    (hhoare : {{P ∧ b}} ~c {{ P }}) :
    {{ P }} while (~b) { ~c } {{ P ∧ ¬ b}} := by
  rw [validHoareTriple_def] at hhoare ⊢
  intro st r heval hpre
  generalize heq : (imp { while (~b) { ~c } }) = cmd at heval
  induction heval generalizing P with
  | @whileFalse b0 s0 c0 hb =>
    injection heq with hbeq hceq
    subst hbeq hceq
    exact ⟨s0, rfl, hpre, by simp [hb]⟩
  | @whileTrueNormal s0 s0' r0 b0 c0 hb hc hloop ih1 ih2 =>
    injection heq with hbeq hceq
    subst hbeq hceq
    apply ih2 hhoare _ rfl
    obtain ⟨s1, heq1, hs1⟩ := hhoare hc ⟨hpre, hb⟩
    injection heq1 with he
    subst he
    exact hs1
  | @whileTrueError s0 b0 c0 hb hc =>
    injection heq with hbeq hceq
    subst hbeq hceq
    obtain ⟨s1, heq1, hs1⟩ := hhoare hc ⟨hpre, hb⟩
    simp at heq1
  | skip | asgn | seqNormal | seqError | ifTrue | ifFalse | assertTrue | assertFalse | assume =>
    contradiction
```

::::::

::::::full
Finally, state Hoare rules for `assert` and `assume` and use them
to prove a simple program correct.  Name your rules `hoare_assert`
and `hoare_assume`.

```lean
-- SOLUTION
/- HIDE: Equivalently, we could make the postcondition Q ∧ b or the
precondition Q → b ... -/
theorem hoare_assert {Q : Assertion} {b : Bexp} :
    {{Q ∧ b}} assert (~b) {{ Q }} := by
  rw [validHoareTriple_def]
  intro st r heval hpre
  obtain ⟨hst, hb⟩ := hpre
  exists st
  inversion heval with
  | assertTrue hb' => exact ⟨rfl, hst⟩
  | assertFalse hb' => simp [hb'] at hb

/- Stating this in a backwards-direction friendly way. -/
/- HIDE: Equivalently, we could make the postcondition Q ∧ b... -/
theorem hoare_assume {Q : Assertion} {b : Bexp} :
    {{ b → Q }} assume (~b) {{ Q }} := by
  rw [validHoareTriple_def]
  intro st r heval hpre
  exists st
  inversion heval with
  | assume hb => exact ⟨rfl, hpre hb⟩
-- END SOLUTION
```

Use your rules to prove the following triple.

```lean
theorem assert_assume_example :
    {{True}}
      assume (X = 1);
      X := X + 1;
      assert (X = 2)
    {{True}} := by
  solution!
    apply hoare_consequence_pre
    · apply hoare_seq
      · apply hoare_seq
        · apply hoare_assert
        · exact hoare_asgn
      · apply hoare_assume
    · assertion_auto
```

:::gradeTheorem 4 assert_assume_example
:::

```lean
end HoareAssertAssume
```
::::::

::::hide
```
/- One An (meluge) : TODO translate this when `ThrowImp` becomes implemented in Imp. -/
/- LATER: A possible exercise on hoare logic with exceptions... -/
-- EX4A? (throw_hoare)
/- In the [exn_imp] exercise in chapter Imp of _Logical
Foundations_, we saw how to add a simple mechanism for raising and
handling exceptions to Imp.  We now consider how to extend Hoare
logic to reason about this language. -/
Module ThrowHoare.
Import ThrowImp.

Definition hoare_quad
           (P:Assertion) (c:com) (Q:Assertion) (S:Assertion) : Prop :=
  ∀ st st' s,
     st =[ c ]=> st' / s ->
     P st  ->
     (s = SNormal -> Q st') ∧ (s = SThrow -> S st').

Notation "{{ P }} c {{ Q }} {{ S }}" :=
  (hoare_quad P c Q S)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99, S custom assn at level 99)
    : hoare_spec_scope.

Theorem hoare_skip : ∀ P S,
     {{P}} skip {{P}} {{S}}.
Proof.
  solution!
    intros P S st st' s He HP. split; intros Hs; inversion He; subst.
    - assumption.
    - inversion H1.
  Qed.

Theorem hoare_seq : ∀ P Q R S c1 c2,
     {{Q}} c2 {{R}} {{S}} ->
     {{P}} c1 {{Q}} {{S}} ->
     {{P}} c1;c2 {{R}} {{S}}.
Proof.
  solution!
    intros P Q R S c1 c2 Hc2 Hc1 st st' s He Hp. split.
    - intros Hs. inversion He; subst.
      + destruct (Hc1 st st'0 SNormal); auto.
        destruct (Hc2 st'0 st' SNormal); auto.
      + inversion H2.
    - intros Hs. subst. inversion He; subst.
      + destruct (Hc1 st st'0 SNormal); auto.
        destruct (Hc2 st'0 st' SThrow); auto.
      + destruct (Hc1 st st' SThrow); auto.
  Qed.

Theorem hoare_stop : ∀ Q S,
     {{S}} throw {{Q}} {{S}}.
Proof.
  solution!
    intros Q S st st' s He HS. split.
    - inversion He. subst. intros C. inversion C.
    - intros Hs. inversion He. subst. assumption.
  Qed.

Lemma hoare_try : ∀ P Q S1 S2 c1 c2,
  {{P}} c1 {{Q}} {{S1}} ->
  {{S1}} c2 {{Q}} {{S2}} ->
  {{P}} try c1 catch c2 end {{Q}} {{S2}}.
Proof.
  solution!
    intros P Q S1 S2 c1 c2 Hc1 Hc2 st st' s He HP. split.
    - inversion He; subst; clear He; intros Hs.
      + apply (Hc1 st st' SNormal) in H4.
        * destruct H4. auto.
        * auto.
      + destruct (Hc1 st st'0 SThrow); subst; try auto.
        destruct (Hc2 st'0 st' SNormal); try auto.
    - intros Hs. inversion He; subst.
      + inversion H2.
      + destruct (Hc2 st'0 st' SThrow); try assumption.
        * apply (Hc1 st st'0 SThrow) in H1; try auto.
          apply (Hc2 st'0 st' SThrow) in H5; destruct H1; try auto.
        * auto.
  Qed.

Lemma hoare_while : ∀ P S (b:bexp) c,
  {{ P ∧ b}} c {{P}} {{S}} ->
  {{P}} while b do c end {{ P ∧ ~ b}} {{S}}.
Proof.
  solution!
    intros P S b c Hhoare st st' s He Hp. split; intros; subst.
    - remember <{while b do c end}> as wcom eqn:Heqwcom.
      remember SNormal as s.
      induction He; try (inversion Heqwcom).
      + (* E_WhileFalse *)
        subst. split.
        * assumption.
        * apply bexp_eval_false. assumption.
      + (* E_WhileTrue *)
        subst. apply IHHe2; try reflexivity. {
            destruct (Hhoare st st' SNormal); try assumption.
            - simpl. split; try assumption.
            - apply H0. reflexivity.
         }
      + (* E_WhileThrow *)
        inversion Heqs.
    - remember <{while b do c end}> as wcom eqn:Heqwcom.
      remember SThrow as s.
      induction He; try (inversion Heqwcom); subst; try (inversion Heqs).
      + (* E_WhileThrow *)
        clear IHHe Heqwcom.
        destruct (Hhoare st st' SThrow); try assumption.
        * simpl. split; try assumption.
        * auto.
  Qed.
End ThrowHoare.
-- []
```
::::

::::hide
```
/- One An (meluge) : TODO translate this exam scratch space (it needs its
own `swap`-extended command namespace, following the Himp/havoc pattern). -/
/- SAZ: Midterm 2 - 2022 scratch space. -/

/- ## Atomic Swap -/

From Stdlib Require Import ZArith.

Module Swap.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CSwap : string -> string -> com.

Notation "'swap' l m" := (CSwap l m)
                          (in custom com at level 60, l constr at level 0, m constr at level 0).
/- INSTRUCTORS: Copy of template com -/
Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99,
    format "'[v' 'while'  x  'do' '/  ' y '/' 'end' ']'") : com_scope.

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : ∀ st,
      st =[ skip ]=> st
  | E_Asgn  : ∀ st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x →ₜ n ; st)
  | E_Seq : ∀ c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : ∀ st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : ∀ st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : ∀ b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : ∀ st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_Swap : ∀ st x y,
      st =[ swap x y]=> (x →ₜ st y ; y →ₜ st x ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

/- The definition of Hoare triples is exactly as before. -/

Definition ValidHoareTriple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  ∀ st st', st =[ c ]=> st' -> P st -> Q st'.

Hint Unfold ValidHoareTriple : core.

Notation "{{ P }} c {{ Q }}" :=
  (ValidHoareTriple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

/- And the precondition consequence rule is exactly as before. -/

Theorem hoare_consequence_pre : ∀ (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof. eauto. Qed.

Definition swap_pre (X Y : string) (Q : Assertion) (st : total_map nat) :=
  ({{ (Q [X ↦ st Y] [Y ↦ st X]) }}) st.

Theorem hoare_swap : ∀ (Q : Assertion) (X Y : string),
  {{ $(swap_pre X Y Q) }} swap X Y {{ Q }}.
Proof.
  unfold ValidHoareTriple, swap_pre.
  intros Q X Y st st' Heval Hpre.
  inversion Heval; subst. apply Hpre.
Qed.

Theorem swap_post : ∀ (P : Assertion) (X Y : string),
  {{ P }} swap X Y {{ $(fun st => ({{ P [X ↦ st Y][Y ↦ st X] }}) st) }}.
Proof.
  intros P X Y. eapply hoare_consequence_pre.
  - apply hoare_swap.
  -
    solution!
      unfold swap_pre, AssertImplies, Assertion.sub.
      intros st HP.
      cbn.
      destruct (String.eqb_spec X Y).
      + subst. repeat rewrite TotalMap.update_eq. repeat rewrite TotalMap.update_same. assumption.
      +
        rewrite (@TotalMap.update_neq _ _ X Y _ n).
        rewrite TotalMap.update_eq.
        rewrite TotalMap.update_permute; auto.
        rewrite TotalMap.update_shadow.
        rewrite TotalMap.update_permute; auto.
        rewrite TotalMap.update_shadow.
        rewrite TotalMap.update_eq.
        repeat rewrite TotalMap.update_same.
        assumption.
Qed.

Definition Z_swap (x y : Z) :=
  (let x1 := x + y in
  let y1 := y - x1 in
  let y2 := 0 - y1 in
  let x2 := x1 + y1 in
  (x2, y2))%Z.

Lemma Z_swap_swaps: ∀ (x y : Z), Z_swap x y = (y, x).
Proof.
  intros.
  unfold Z_swap.
  assert ( (x + y + (y - (x + y)))%Z = y).
  { lia. }
  assert ((0 - (y - (x + y)))%Z = x).
  { lia. }
  rewrite H. rewrite H0. reflexivity.
Qed.

End Swap.
```
::::

::::hide
```
/- Local Variables: -/
/- fill-column: 70 -/
/- outline-regexp: "(\\*\\* \\*+\\|(\\* EX[1-5]..." -/
/- End: -/
/- mode: outline-minor -/
/- outline-heading-end-regexp: "\n" -/
```
::::
