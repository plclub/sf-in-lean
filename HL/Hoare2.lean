-- Initial chapter port prepared with GPT assistance and manually
-- reviewed against the Rocq source.

import SFLMeta
import HL.Hoare

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Hoare2: Hoare Logic, Part II" =>
%%%
tag := "Hoare2"
htmlSplit := .never
file := some "Hoare2"
%%%

```lean -show
open scoped Com MyGetElem Assertion HasTriple
```

:::dev BeforeNextRelease
BCP 23,25: There are a lot of questions about the flow of this
material.  Needs a deep look.  In particular:
  - One feels that it takes a rather circuitous route to get to
    formal decorated programs -- there might be a way to just go
    straight there.
    More importantly, it isn't very clear to me that the
    version of decorated programs that we wound up with is really
    the right one -- why spend all this time writing annotations
    that we then say are unnecessary?  Seems like we could define
    decorated programs with a lighter annotation burden (as in the
    exercise at the end) and just add optional annotations when we
    want to, to make particular examples clearer.
  - The rigidity of the Hoare rules as stated in the last chapter
    is also annoying here at many points.  Building the rules of
    consequence into all the other rules might make a lot of things
    smoother.  Would be a big change (also to Hoare.v), but definitely
    worth a try.

 And related...
:::

:::dev "Michael Clarkson (clarksmr)" BeforeNextRelease (year := 2020)
Here are a bunch of improvements I wanted to make but
didn't have time to get to.  Maybe next time if no one else gets to
them first.

- 1. This chapter feels largely disconnected from the style of the
     rest of the series, which is "100% Rocq script".  There's a
     significant amount of "just comments" here instead.  I think
     we could make this much better by introducing formal decorated
     programs right after we informally define them.  Then in the
     examples that follow do each informal decorated program (to
     get students to find the right assertions, more or less)
     followed immediately by a formal version, instead of delaying
     formal so far to the end. The `parity` exercise is a good
     example of one that already almost does this already. (BCP 21:
     Done!)
- 2. There are several places where we are verifying Imp program
     schemas, not actual programs.  We're mixing Rocq variables with
     Imp variables.  That's confusing.  One example is `two_loops`;
     I've tried to mark others as I come across them.  (BCP: I've
     added some quizzes and such to try to clarify the relation
     between programs / triples and program/triple schemas.
     BCP 25: I think this is a non-issue now.)
- 3. Weakest preconditions show up in this chapter as completely
     optional, then are revisited (and required) in HoareAsLogic.
     Consider moving the entire treatment to that chapter.  (BCP
     23: Yes, we should do that!)
- 4. It seems a shame that the SparseAnnotations section is not
     visible in the full version, but only in a solution.  It's
     fantastic!  It would be great to show it off.  (BCP 25: Yes!
     Indeed, perhaps it should even replace the current treatment!)
:::

:::dev PotentialImprovement
The vertical spacing of displays in HTML is particularly
bad in this chapter, especially displays within bulleted lists!

FOLD some more proofs

add some "why doesn't this invariant work?" exercises to the
invariant finding / decorated programs section; we could give them
many different wrong invariants for a program and ask them which of
the 3 conditions breaks for each of them

There are some more exercises in John Reynolds's books
(especially the old one).  One good one is fast exponentiation.

Maybe make an advanced exercise/example out of the GCD
decorated program at the end of this file (BCP: good idea but low
priority -- we have a lot of exercises)

-- we don't explain very well how to specify programs
   -- e.g., it might be worth adding an exercise in which they have
      to add a Rocq function / relation implementing / specifying
      the behavior of a given a piece of Imp code
   -- after this is properly explained we could hide (some of) the
      specifications that are now given to them in exercises, and
      ask them to find them out
   -- BCP 20: This would be great
:::

:::dev
HIDE: Some useful theorems about Imp are not being redefined for
the modified versions of Imp. We should either re-prove them or add
hints (or exercises!) about this.  BCP 20: Which ones???
:::

:::dev PotentialImprovement
```
HIDE: to be removed whenever they finally change the default definition
Ltac intuition_solver ::= auto.
```
:::

:::dev PotentialImprovement
Use informal mathematical notations everywhere we can!

```
Here's a very nice problem that Arthur proposed but that we
haven't found the time to write out in detail.

      {{ X = n /\ n > 1 }}
    P := 1;
    D := 2;
    while D < X AND P = 1 do
      Y := X;
      while Y >= D do
        Y := Y - D
      end;
      {{ exists q, X = q * D + Y }}
      if Y = 0 then
        P := 0
      else
        skip
      end;
      D := D + 1
    end
      {{ I /\ (D >= X \/ P <> 1) }} ->>
      {{ P = 1 -> (forall d, (exists q, n = d * q) -> d = 1 \/ d = n) }}

    I = (P = 1 -> (forall d, d <= D -> (exists q, X = d * q) -> d = 1 \/ d = n))
       /\ X = n /\ n > 1
```

```
A possible (harder, perhaps advanced or optional)
exercise -- nice because it has nested loops...

   {{ Y = n }}
   Z := 0;
   {{ I }}
   while Y > 0 do
     {{ I /\ Y>0 }}
     X := Y;
     while X > 0 do
       Z := Z + 1;
       X := X - 1
     end;
     Y := Y - 1
     {{ I }}
   end
   {{ I /\ ~(Y > 0) }}
   {{ Z = n*(n-1)/2 }}

   where I = Z + Y*(Y+1)/2 = n*(n+1)/2
```
:::

::::quiz
:::instructors
Pretty trivial, but still not without interest
:::

On a piece of paper (or whatever), write down a Hoare-triple
specification for the following program:

```display
X := 2;
Y := X + X
```
::::

::::quiz
:::instructors
More interesting, esp. because it offers a good
opportunity to talk about parameters (m).
:::

Write down a (useful) specification for the following program:

```display
X := X + 1; Y := X + 1
```

:::instructors
```
forall m, {{ X=m }} c {{ X = m+1 /\ Y = m+2 }}
vs {{ TRUE }} c {{ Y > X }}
```
:::
::::

::::quiz
:::instructors
```
Much more interesting: one obvious spec is
{{True}}c{{X<=Y}}, but this loses the fact that the final values
are either the same as the initial or else swapped, so then a spec
with parameters seems preferable.  There's also a potential
confusion about whether to say something about Z in the
postcondition.
```
:::

Write down a (useful) specification for the following program:

```display
if X <= Y then
  skip
else
  Z := X;
  X := Y;
  Y := Z
end
```
::::

::::quiz
:::instructors
Parameters can also appear within programs.
:::

Write down a (useful) specification for the following program:

```display
X := m;
Y := X + X
```
::::

::::quiz
Write down a (useful) specification for the following program:

```display
X := m;
Z := 0;
while X <> 0 do
  X := X - 2;
  Z := Z + 1
end
```
::::

# Decorated Programs

:::dev PotentialImprovement
Explain this better?...
:::

The beauty of Hoare Logic is that it is _syntax directed_: the
structure of proofs exactly follows the structure of programs.

We can record the essential ideas of a Hoare-logic proof —
omitting low-level calculational details — by "decorating" a
program with appropriate assertions on each of its commands.

Such a _decorated program_ carries within itself an argument for
its own correctness.

:::slidebreak
:::

For example, consider the program:

```display
X := m;
Z := p;
while X <> 0 do
  Z := Z - 1;
  X := X - 1
end
```

:::slidebreak
:::

Here is one possible specification for this program, in the
form of a Hoare triple:

```display
{{ True }}
X := m;
Z := p;
while X <> 0 do
  Z := Z - 1;
  X := X - 1
end
{{ Z = p - m }}
```

::::full
(Note the _parameters_ `m` and `p`, which stand for
fixed-but-arbitrary numbers.  Formally, they are simply Lean
variables of type `Nat`.)
::::

:::slidebreak
:::

Here is a decorated version of this program, embodying a
proof of this specification:

```display
{{ True }} ->>
{{ m = m }}
  X := m
                     {{ X = m }} ->>
                     {{ X = m /\ p = p }};
  Z := p;
                     {{ X = m /\ Z = p }} ->>
                     {{ Z - X = p - m }}
  while X <> 0 do
                     {{ Z - X = p - m /\ X <> 0 }} ->>
                     {{ (Z - 1) - (X - 1) = p - m }}
    Z := Z - 1
                     {{ Z - (X - 1) = p - m }};
    X := X - 1
                     {{ Z - X = p - m }}
  end
{{ Z - X = p - m /\ ~ (X <> 0) }} ->>
{{ Z = p - m }}
```

:::dev
```
HIDE: MRC'20: It bothers me a little in the proof above (and
similarly throughout the whole file really when it comes to guards)
that when we get to this part:
[[
 while X <> 0 do {{ Z - X = p - m /\ X <> 0 }} ->>
]]
we are inconsistent about [X <> 0] vs. [~(X=0)].  I admit they
evaluate the same (er, sort of---the former is a [bexp] whereas the
latter is an assertion), but they aren't syntactically the same.
Since what we're teaching here (mechanized Hoare logic) is fussy
about syntax, it strikes me as something we ought to be precise
about. But it's an annoying change to propagate through the file,
so I haven't done it. Is it worth a comment, or do others not get
bothered by this?  Another way to fix this would be to add the [<>]
operator to Imp, so that we can write the guard in the nicer way.

BCP 20: I think adding in a few more boolean operators at the
outside is the way to go...

BCP 21: ... and I've now done this: <> is available in formal
bexps (also >).
```
:::

Concretely, a decorated program consists of the program's text
interleaved with assertions (sometimes multiple assertions
separated by ->>).

:::slidebreak
:::

A decorated program can be viewed as a compact representation of a
proof in Hoare Logic: the assertions surrounding each command
specify the Hoare triple to be proved for that part of the program
using one of the Hoare Logic rules, and the structure of the
program itself shows how to assemble all these individual steps
into a proof for the whole program.

::::full
Our goal is to verify such decorated programs "mostly
automatically."  But, before we can verify anything, we need to be
able to _find_ a proof for a given specification, and for this we
need to discover the right assertions. This can be done in an
almost mechanical way, with the exception of finding loop
invariants. In the remainder of this section, we explain in detail
how to construct decorations for several short programs, all of
which are loop free or have simple loop invariants. We'll return
to finding more interesting loop invariants later in the chapter.
::::

## Example: Swapping

Consider the following program, which swaps the values of two
variables using addition and subtraction, instead of by assigning
to a temporary variable.

```display
X := X + Y;
Y := X - Y;
X := X - Y
```

We can give a proof, in the form of decorations, that this program is
correct — i.e., it really swaps `X` and `Y` — as follows.

::::terse
WORK IN CLASS
::::

::::full
```display
(1)    {{ X = m /\ Y = n }} ->>
(2)    {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
         X := X + Y
(3)                     {{ X - (X - Y) = n /\ X - Y = m }};
         Y := X - Y
(4)                     {{ X - Y = n /\ Y = m }};
         X := X - Y
(5)    {{ X = n /\ Y = m }}
```

The decorations can be constructed as follows:

  - We begin with the undecorated program (the unnumbered lines).

  - We add the specification — i.e., the outer precondition (1)
    and postcondition (5). In the precondition, we use parameters
    `m` and `n` to remember the initial values of variables `X`
    and `Y` so that we can refer to them in the postcondition (5).

  - We work backwards, mechanically, starting from (5) and
    proceeding until we get to (2). At each step, we obtain the
    precondition of the assignment from its postcondition by
    substituting the assigned variable with the right-hand-side of
    the assignment. For instance, we obtain (4) by substituting
    `X` with `X - Y` in (5), and we obtain (3) by substituting `Y`
    with `X - Y` in (4).

  - Finally, we verify that (1) logically implies (2) — i.e., that
    the step from (1) to (2) is a valid use of the law of
    consequence — by doing a bit of high-school algebra.
::::

:::dev
HIDE: BCP 21: This side comment seems too technical:
- (Note that we are working with natural numbers rather than
  fixed-width machine integers, so we don't need to worry about
  the possibility of arithmetic overflow anywhere in this
  argument.  This makes life quite a bit simpler!)

HIDE: A quick / optional exercise using just assignment here
would be good.
:::

## Example: Simple Conditionals

:::dev PotentialImprovement
This is not such an interesting example...
:::

::::terse
Here's a simple program using conditionals, along
with a possible specification:

```display
{{ True }}
  if X <= Y then
    Z := Y - X
  else
    Z := X - Y
  end
{{ Z + X = Y \/ Z + Y = X }}
```

Let's turn it into a decorated program...
::::

::::terse
WORK IN CLASS
::::

::::full
Here is a simple decorated program using conditionals:

```display
(1)   {{ True }}
        if X <= Y then
(2)                    {{ True /\ X <= Y }} ->>
(3)                    {{ (Y - X) + X = Y \/ (Y - X) + Y = X }}
          Z := Y - X
(4)                    {{ Z + X = Y \/ Z + Y = X }}
        else
(5)                    {{ True /\ ~(X <= Y) }} ->>
(6)                    {{ (X - Y) + X = Y \/ (X - Y) + Y = X }}
          Z := X - Y
(7)                    {{ Z + X = Y \/ Z + Y = X }}
        end
(8)   {{ Z + X = Y \/ Z + Y = X }}
```

These decorations can be constructed as follows:

  - We start with the outer precondition (1) and postcondition (8).

  - Following the format dictated by the `hoare_if` rule, we copy the
    postcondition (8) to (4) and (7). We conjoin the precondition (1)
    with the guard of the conditional to obtain (2). We conjoin (1)
    with the negated guard of the conditional to obtain (5).

  - In order to use the assignment rule and obtain (3), we substitute
    `Z` by `Y - X` in (4). To obtain (6) we substitute `Z` by `X - Y`
    in (7).

  - Finally, we verify that (2) implies (3) and (5) implies (6). Both
    of these implications crucially depend on the ordering of `X` and
    `Y` obtained from the guard. For instance, knowing that `X <= Y`
    ensures that subtracting `X` from `Y` and then adding back `X`
    produces `Y`, as required by the first disjunct of (3). Similarly,
    knowing that `~ (X <= Y)` ensures that subtracting `Y` from `X`
    and then adding back `Y` produces `X`, as needed by the second
    disjunct of (6). Note that `n - m + m = n` does _not_ hold for
    arbitrary natural numbers `n` and `m` (for example, \[3 - 5 + 5 =
    5\]).
::::

:::dev
NOTATION: LATER: The `~` in that paragraph will typeset wrong if
the space after it is removed.  Maybe it's better to give up on
all the unicode hacks in the generated HTML...?
:::

::::::full
:::::exercise (rating := 2) (name := "if_minus_plus_reloaded") (optional := Yes) (manual := true)
N.b.: Although this exercise is marked optional, it is an
excellent warm-up for the (non-optional) `if_minus_plus_correct`
exercise below!

Fill in valid decorations for the following program:

```display
{{ True }}
  if X <= Y then
            {{                         }} ->>
            {{                         }}
    Z := Y - X
            {{                         }}
  else
            {{                         }} ->>
            {{                         }}
    Y := X + Z
            {{                         }}
  end
{{ Y = X + Z }}
```

Briefly justify each use of `->>`.

:::solution
```display
{{ True }}
  if X <= Y then
       {{ True /\ X <= Y }} ->>
       {{ Y = X + (Y - X) }}
    Z := Y - X
       {{ Y = X + Z }}
  else
       {{ True /\ ~(X <= Y) }} ->>
       {{ X + Z = X + Z }}
    Y := X + Z
       {{ Y = X + Z }}
  end
{{ Y = X + Z }}
```

The second use of consequence is trivial, while the first
crucially depends on the `X <= Y` condition, which ensures that
subtracting `X` from `Y` and then adding back `X` produces `Y`.
:::
:::::

::::::

## Example: Reduce to Zero

::::terse
Here is a very simple `while` loop with a simple
specification:

```display
{{ True }}
  while (X <> 0) do
    X := X - 1
  end
{{ X = 0 }}
```
::::

::::terse
WORK IN CLASS
::::

::::full
Here is a `while` loop that is so simple that `True` suffices
as a loop invariant.

```display
(1)    {{ True }}
         while X <> 0 do
(2)                  {{ True /\ X <> 0 }} ->>
(3)                  {{ True }}
           X := X - 1
(4)                  {{ True }}
         end
(5)    {{ True /\ ~(X <> 0) }} ->>
(6)    {{ X = 0 }}
```

The decorations can be constructed as follows:

 - Start with the outer precondition (1) and postcondition (6).

 - Following the format dictated by the `hoare_while` rule, we copy
   (1) to (4). We conjoin (1) with the guard to obtain (2). We also
   conjoin (1) with the negation of the guard to obtain (5).

 - Because the final postcondition (6) does not syntactically match (5),
   we add an implication between them.

 - Using the assignment rule with assertion (4), we trivially substitute
   and obtain assertion (3).

 - We add the implication between (2) and (3).

Finally we check that the implications do hold; both are trivial.
::::

## Example: Division

:::instructors
```
Adapted from final 2012 (original exercise by
Loris). This is a good example to show before going into more
advanced discussions about _finding_ loop invariants. As a
consequence I've adapted this to keep the loop invariant as simple
and as close to the final postcondition as possible.
```
:::

Let's do one more example of simple reasoning about a loop.

The following Imp program calculates the integer quotient and
remainder of parameters `m` and `n`.

```display
X := m;
Y := 0;
while n <= X do
  X := X - n;
  Y := Y + 1
end;
```

If we replace `m` and `n` by concrete numbers and execute the program, it
will terminate with the variable `X` set to the remainder when `m`
is divided by `n` and `Y` set to the quotient.

:::slidebreak
:::

::::terse
Here's a possible specification:

```display
{{ True }}
  X := m;
  Y := 0;
  while n <= X do
    X := X - n;
    Y := Y + 1
  end
{{ n * Y + X = m /\ X < n }}
```
::::

::::terse
WORK IN CLASS
::::

::::full
In order to give a specification to this program we need to
remember that dividing `m` by `n` produces a remainder `X` and a
quotient `Y` such that `n * Y + X = m /\ X < n`.

It turns out that we get lucky with this program and don't have to
think very hard about the loop invariant: the loop invariant is just
the first conjunct, `n * Y + X = m`, and we can use this to
decorate the program.

```display
 (1)  {{ True }} ->>
 (2)  {{ n * 0 + m = m }}
        X := m;
 (3)                     {{ n * 0 + X = m }}
        Y := 0;
 (4)                     {{ n * Y + X = m }}
        while n <= X do
 (5)                     {{ n * Y + X = m /\ n <= X }} ->>
 (6)                     {{ n * (Y + 1) + (X - n) = m }}
          X := X - n;
 (7)                     {{ n * (Y + 1) + X = m }}
          Y := Y + 1
 (8)                     {{ n * Y + X = m }}
        end
 (9)  {{ n * Y + X = m /\ ~ (n <= X) }} ->>
(10)  {{ n * Y + X = m /\ X < n }}
```

Assertions (4), (5), (8), and (9) are derived mechanically from
the loop invariant and the loop's guard.  Assertions (8), (7), and (6)
are derived using the assignment rule going backwards from (8)
to (6).  Assertions (4), (3), and (2) are again backwards
applications of the assignment rule.

Now that we've decorated the program it only remains to check that
the uses of the consequence rule are correct — i.e., that (1)
implies (2), that (5) implies (6), and that (9) implies (10). This
is indeed the case:
  - (1) ->> (2):  trivial, by algebra.
  - (5) ->> (6):  because `n <= X`, we are guaranteed that the
    subtraction in (6) does not get zero-truncated.  We can
    therefore rewrite (6) as `n * Y + n + X - n` and cancel the
    `n`s, which results in the left conjunct of (5).
  - (9) ->> (10):  if `~ (n <= X)` then `X < n`.  That's
    straightforward from high-school algebra.
So, we have a valid decorated program.
::::

## From Decorated Programs to Formal Proofs

From an informal proof in the form of a decorated program, it is
"easy in principle" to read off a formal proof using the Lean
theorems corresponding to the Hoare Logic rules, but these proofs
can be a bit long and fiddly.

::::full
Note that we do _not_ unfold the definition of `ValidHoareTriple`
anywhere in this proof: the point of the game we're playing now
is to use the Hoare rules as a self-contained logic for reasoning
about programs.
::::

:::slidebreak
:::

For example...

```lean
def reduceToZero : Com :=
  imp {
    while (X ≠ 0) {
      X := X - 1
    }
  }
```

:::slidebreak
:::

```lean
theorem reduce_to_zero_correct' :
    {{ True }} ~reduceToZero {{ X = 0 }} := by
  -- First put the postcondition into the form expected by
  -- the while rule.
  sorry
```

:::slidebreak
:::

::::full
In {ref "Hoare"}[Hoare] we introduced a series of tactics named
`assertion_auto` to automate proofs involving assertions.

The following declaration introduces a more sophisticated tactic
that will help with proving assertions throughout the rest of this
chapter.  You don't need to understand the details, but briefly:
it introduces the available hypotheses, simplifies assertions,
maps, and arithmetic expressions, and then asks `lia` to solve
linear arithmetic goals. What's left after `verify_assertion` does
its work should be just the "interesting parts" of the proof
(which, if we're lucky, might be nothing at all!).
::::

::::terse
A little more (OK, quite a bit more) tactic fanciness for
helping deal with the boring parts of the process of proving
assertions:
::::

:::dev PotentialImprovement
Explain any other bits of it?
:::

```lean
macro "verify_assertion" : tactic =>
  `(tactic| assertion_auto)
```

:::slidebreak
:::

This makes it pretty easy to verify `reduce_to_zero`:

```lean
theorem reduce_to_zero_correct''' :
    {{ True }} ~reduceToZero {{ X = 0 }} := by
  sorry
```

:::slidebreak
:::

This example shows that it is conceptually straightforward to read
off the main elements of a formal proof from a decorated program.
Indeed, the process is so straightforward that it can be
automated, as we will see next.

# Formal Decorated Programs

:::dev PotentialImprovement
Now that this section has become standard material, the
writing could be improved :-)
:::

::::full
Our informal conventions for decorated programs amount to a
way of "displaying" Hoare triples, in which commands are annotated
with enough embedded assertions that checking the validity of a
triple is reduced to simple logical and algebraic calculations
showing that some assertions imply others.

In this section, we show that this presentation style can be made
completely formal — and indeed that checking the validity of
decorated programs can be largely automated.
::::

::::terse
With a little more work, we can _formalize_ the definition of
well-formed decorated programs and _automate_ the boring mechanical
steps in proving that the decorations are correct.
::::

## Syntax

The first thing we need to do is to formalize a variant of the
syntax of Imp commands that includes embedded assertions, which
we'll call "decorations."  We call the new commands _decorated
commands_, or `dcom`s.

The choice of exactly where to put assertions in the definition of
`dcom` is a bit subtle.  The simplest thing to do would be to
annotate every `dcom` with a precondition and postcondition —
something like this...

:::slidebreak
:::

```lean
namespace DComFirstTry

inductive DCom where
  | skip (pre : Assertion)
  | seq (pre : Assertion) (first : DCom)
      (middle : Assertion)
      (second : DCom) (post : Assertion)
  | asgn (x : Ident) (a : Aexp) (post : Assertion)
  | cond (pre : Assertion) (b : Bexp)
      (thenPre : Assertion) (thenBranch : DCom)
      (elsePre : Assertion) (elseBranch : DCom)
      (post : Assertion)
  | whileDo (pre : Assertion) (b : Bexp)
      (bodyPre : Assertion) (body : DCom)
      (bodyPost : Assertion) (post : Assertion)
  | strengthenPre (pre : Assertion) (body : DCom)
  | weakenPost (body : DCom) (post : Assertion)

end DComFirstTry
```

:::slidebreak
:::

But this would result in _very_ verbose decorated programs with a
lot of repeated annotations: a simple program like
`skip;skip` would be decorated like this,

```display
{{P}} ({{P}} skip {{P}}) ; ({{P}} skip {{P}}) {{P}}
```

with pre- and post-conditions around each `skip`, plus identical
pre- and post-conditions on the semicolon!

:::slidebreak
:::

In other words, we don't want both preconditions and
postconditions on each command, because a sequence of two commands
would contain redundant decorations — the postcondition of the
first likely being the same as the precondition of the second.

Instead, our formal syntax of decorated commands will omit
preconditions whenever possible and embed just postconditions.

:::slidebreak
:::

- The `skip` command, for example, is decorated only with its
postcondition

```display
skip {{ Q }}
```

on the assumption that the precondition will be provided by
somebody else.

We carry the same assumption through the other syntactic forms:
each decorated command is assumed to carry its own postcondition
within itself but take its precondition from its context in
which it is used.

:::slidebreak
:::

- Sequences `d1 ; d2` need no additional decorations.

Why?

Because inside `d2` there will be a postcondition, which also
serves as the postcondition of `d1;d2`.

Similarly, inside `d1` there will also be a postcondition, which
additionally serves as the _precondition_ for `d2`.

:::slidebreak
:::

- An assignment `X := a` is decorated only with its postcondition:

```display
X := a {{ Q }}
```

:::slidebreak
:::

- A conditional `if b then d1 else d2` is decorated with a
postcondition for the entire statement, as well as preconditions
for each branch:

```display
if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }}
```

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2025)
Maybe we need a note here about why we don't just
calculate P1 and P2 later, once we know the precondition of the
whole loop. Indeed, we could (and perhaps should, as discussed
elsewhere), but we are doing something simpler for the moment.
:::

:::slidebreak
:::

- A loop `while b do d end` is decorated with its final
postcondition plus a precondition for the body:

```display
while b do {{ P }} d end {{ Q }}
```

The postcondition embedded in `d` serves as the loop invariant.

:::slidebreak
:::

- Implications `->>` can be added as decorations either for a
precondition...

```display
->> {{ P }} d
```

...or for a postcondition:

```display
d ->> {{ Q }}
```

The former is waiting for another precondition to be supplied by
the context; the latter relies on the postcondition already
embedded in `d`.

:::slidebreak
:::

Putting this all together gives us the formal syntax of decorated
commands:

```lean
inductive DCom where
  | skip (post : Assertion)
  | seq (first second : DCom)
  | asgn (x : Ident) (a : Aexp) (post : Assertion)
  | cond (b : Bexp)
      (thenPre : Assertion) (thenBranch : DCom)
      (elsePre : Assertion) (elseBranch : DCom)
      (post : Assertion)
  | whileDo (b : Bexp) (bodyPre : Assertion) (body : DCom)
      (post : Assertion)
  | pre (pre : Assertion) (body : DCom)
  | post (body : DCom) (post : Assertion)
```

Lean keeps decorated-command notation in its own syntax category,
`dcom`, so it can coexist with the ordinary Imp command syntax.

::::details "Notation encoding: decorated commands"
```lean
declare_syntax_cat dcom

syntax:max "(" dcom ")" : dcom
syntax:max "skip" " {{" term "}}" : dcom
syntax:max ident " := " imp_aexp " {{" term "}}" : dcom
syntax:20 dcom:21 ";" ppLine dcom:20 : dcom
syntax:max "if " "(" imp_bexp ")" ppHardSpace "then" ppLine
  "{{" term "}}" ppLine dcom ppLine
  "else" ppLine "{{" term "}}" ppLine dcom ppLine
  "end" ppLine "{{" term "}}" : dcom
syntax:max "while " "(" imp_bexp ")" ppHardSpace "do" ppLine
  "{{" term "}}" ppLine dcom ppLine
  "end" ppLine "{{" term "}}" : dcom
syntax:5 "->>" " {{" term "}}" ppLine dcom:0 : dcom
syntax:5 dcom:6 ppLine "->>" " {{" term "}}" : dcom

syntax:min "dcom" ppHardSpace "{" ppLine dcom
  ppDedent(ppLine "}") : term

macro_rules
  | `(dcom { ($body:dcom) }) =>
      `(dcom { $body })
  | `(dcom { skip {{ $q }} }) =>
      `(DCom.skip ({{ $q }}))
  | `(dcom { $x:ident := $a:imp_aexp {{ $q }} }) =>
      `(DCom.asgn $x (aexp { $a }) ({{ $q }}))
  | `(dcom { $d1:dcom; $d2:dcom }) =>
      `(DCom.seq (dcom { $d1 }) (dcom { $d2 }))
  | `(dcom {
        if ($b:imp_bexp) then
          {{ $p1 }}
          $d1:dcom
        else
          {{ $p2 }}
          $d2:dcom
        end
          {{ $q }}
      }) =>
      `(DCom.cond (bexp { $b })
        ({{ $p1 }}) (dcom { $d1 })
        ({{ $p2 }}) (dcom { $d2 })
        ({{ $q }}))
  | `(dcom {
        while ($b:imp_bexp) do
          {{ $p }}
          $body:dcom
        end
          {{ $q }}
      }) =>
      `(DCom.whileDo (bexp { $b }) ({{ $p }})
        (dcom { $body }) ({{ $q }}))
  | `(dcom { ->> {{ $p }} $body:dcom }) =>
      `(DCom.pre ({{ $p }}) (dcom { $body }))
  | `(dcom { $body:dcom ->> {{ $q }} }) =>
      `(DCom.post (dcom { $body }) ({{ $q }}))
```
::::

::::terse
(We then need to redefine all our Notations to get nice
concrete syntax for `dcom`.)
::::

:::slidebreak
:::

To provide the initial precondition that goes at the very top of a
decorated program, we introduce a new type `decorated`:

```lean
structure Decorated where
  pre : Assertion
  body : DCom
```

:::slidebreak
:::

:::dev
HIDE: Add FOLD here
:::

:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement (year := 2021)
The above FOLD seems not to work, at least in the
terse version. :-(
:::

```lean
example : DCom :=
  .skip ({{ True }})

example : DCom :=
  .whileDo (bexp {true}) ({{ True }})
    (.skip ({{ True }})) ({{ True }})
```

To inspect the fully elaborated term behind this notation, put
`set_option pp.all true in` before a `#check` or `#print` command.

The formal definitions can use either constructors directly or the
decorated-command notation introduced above.

:::dev
HIDE: Add /FOLD here
:::

An example `decorated` program that decrements `X` to `0`:

```lean
def decWhile : Decorated where
  pre := ({{ True }})
  body := dcom {
    while (X ≠ 0) do
      {{ True ∧ ¬ X = 0 }}
      X := X - 1 {{ True }}
    end
      {{ True ∧ X = 0 }}
    ->> {{ X = 0 }}
  }
```

::::hide
```
Print dec0.
Print dec1.
Print dec_while.
```
::::

:::slidebreak
:::

It is easy to go from a `dcom` to a `com` by erasing all
annotations.

```lean
def DCom.erase (d : DCom) : Com :=
  match d with
  | .skip _ => .skip
  | .seq d1 d2 => .seq d1.erase d2.erase
  | .asgn x a _ => .asgn x a
  | .cond b _ d1 _ d2 _ => .cond b d1.erase d2.erase
  | .whileDo b _ body _ => .whileDo b body.erase
  | .pre _ body => body.erase
  | .post body _ => body.erase

def Decorated.erase (dec : Decorated) : Com :=
  dec.body.erase
```

:::instructors
the `unfold` isn't needed, but it lets us recall
what `dec_while` is without having to print it.
:::

::::full
```lean
example :
    decWhile.erase =
      (imp {
        while (X ≠ 0) {
          X := X - 1
        }
      }) := by
  rfl
```
::::

:::slidebreak
:::

It is also straightforward to extract the precondition and
postcondition from a decorated program.

```lean
def Decorated.precondition (dec : Decorated) : Assertion :=
  dec.pre
```

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2025)
```
It would be nice to use <{ ... }> notations
in this definition and the ones below...
     | <{ skip {{P}} }>        => P
     | <{ _; d2 }>             => post d2
     | <{ _ := _ {{Q}} }>      => Q
```
:::

```lean
def DCom.postcondition (d : DCom) : Assertion :=
  match d with
  | .skip q => q
  | .seq _ d2 => d2.postcondition
  | .asgn _ _ q => q
  | .cond _ _ _ _ _ q => q
  | .whileDo _ _ _ q => q
  | .pre _ body => body.postcondition
  | .post _ q => q

def Decorated.postcondition (dec : Decorated) : Assertion :=
  dec.body.postcondition
```

::::full
```lean
example : decWhile.precondition = {{ True }} := by
  funext st
  rfl

example : decWhile.postcondition = {{ X = 0 }} := by
  funext st
  rfl
```
::::

:::slidebreak
:::

We can then express what it means for a decorated program to be
correct as follows:

```lean
def Decorated.OuterTripleValid (dec : Decorated) : Prop :=
  ValidHoareTriple dec.precondition dec.erase
    dec.postcondition
```

For example:

```lean
example :
    decWhile.OuterTripleValid =
      {{ True }}
        while (X ≠ 0) {
          X := X - 1
        }
      {{ X = 0 }} := by
  rfl
```

:::slidebreak
:::

The outer Hoare triple of a decorated program is just a `Prop`;
thus, to show that it is _valid_, we need to produce a proof of
this proposition.

We will do this by extracting "proof obligations" from the
decorations sprinkled throughout the program.

These obligations are often called _verification conditions_,
because they are the facts that must be verified to see that the
decorations are locally consistent and thus constitute a proof of
validity of the outer triple.

## Extracting Verification Conditions

The function `DCom.VerificationConditions` takes a decorated command
`d` together with a precondition `P` and returns a _proposition_
that, if it can be proved, implies that the triple

```display
{{P}} d.erase {{d.postcondition}}
```

is valid.

It does this by walking over `d` and generating a big conjunction
that includes

- local consistency checks for each form of command, plus

- uses of `->>` to bridge the gap between the assertions found
  inside a decorated command and the assertions imposed by the
  external precondition; these uses correspond to applications
  of the consequence rule.

:::slidebreak
:::

_Local consistency_ is defined as follows...

- The decorated command

```display
skip {{Q}}
```

is locally consistent with respect to a precondition `P` if
`P ->> Q`.

:::slidebreak
:::

- The sequential composition of `d1` and `d2` is locally
consistent with respect to `P` if `d1` is locally consistent with
respect to `P` and `d2` is locally consistent with respect to
the postcondition of `d1`.

:::slidebreak
:::

- An assignment

```display
X := a {{Q}}
```

is locally consistent with respect to a precondition `P` if:

```display
P ->> Q [X |-> a]
```

:::slidebreak
:::

- A conditional

```display
if b then {{P1}} d1 else {{P2}} d2 end {{Q}}
```

is locally consistent with respect to precondition `P` if

   (1) `P /\ b ->> P1`

   (2) `P /\ ~b ->> P2`

   (3) `d1` is locally consistent with respect to `P1`

   (4) `d2` is locally consistent with respect to `P2`

   (5) `d1.postcondition ->> Q`

   (6) `d2.postcondition ->> Q`

:::slidebreak
:::

- A loop

```display
while b do {{Q}} d end {{R}}
```

is locally consistent with respect to precondition `P` if:

   (1) `P ->> d.postcondition`

   (2) `d.postcondition /\ b ->> Q`

   (3) `d.postcondition /\ ~b ->> R`

   (4) `d` is locally consistent with respect to `Q`

:::slidebreak
:::

- A command with an extra assertion at the beginning

```display
->> {{Q}} d
```

is locally consistent with respect to a precondition `P` if:

  (1) `P ->> Q`

  (2) `d` is locally consistent with respect to `Q`

:::slidebreak
:::

- A command with an extra assertion at the end

```display
d ->> {{Q}}
```

is locally consistent with respect to a precondition `P` if:

  (1) `d` is locally consistent with respect to `P`

  (2) `d.postcondition ->> Q`

:::slidebreak
:::

With all this in mind, we can write a _verification condition
generator_ that takes a decorated command and reads off a
proposition saying that all its decorations are locally
consistent.

Formally, since a decorated command is "waiting for its
precondition" the main VC generator takes a `dcom` plus a given
precondition as arguments.

:::dev
HIDE: There was some discussion in 2016 about whether the VC
generator should should use equivalence or implication in a few
places.  I (BCP) believe Phil (Wadler) changed some instances of
the former to the latter.

HIDE: MRC'20: a written explanation of each part of this would be
quite nice.  BCP 21: Agreed!!  (BCP 23: But it's kind of what's
just above...)
:::

```lean
def DCom.VerificationConditions
    (P : Assertion) (d : DCom) : Prop :=
  match d with
  | .skip Q =>
      P ->> Q
  | .seq d1 d2 =>
      d1.VerificationConditions P ∧
      d2.VerificationConditions d1.postcondition
  | .asgn x a Q =>
      P ->> {{ Q [x ↦ ~a] }}
  | .cond b P1 d1 P2 d2 Q =>
      ({{ P ∧ b }} ->> P1) ∧
      ({{ P ∧ ¬ b }} ->> P2) ∧
      (d1.postcondition ->> Q) ∧
      (d2.postcondition ->> Q) ∧
      d1.VerificationConditions P1 ∧
      d2.VerificationConditions P2
  | .whileDo b bodyPre body q =>
      -- The body's postcondition is both the loop invariant
      -- and the precondition for the first iteration.
      (P ->> body.postcondition) ∧
      ({{ body.postcondition ∧ b }} ->> bodyPre) ∧
      ({{ body.postcondition ∧ ¬ b }} ->> q) ∧
      body.VerificationConditions bodyPre
  | .pre P' body =>
      (P ->> P') ∧ body.VerificationConditions P'
  | .post body Q =>
      body.VerificationConditions P ∧
      (body.postcondition ->> Q)
```

:::slidebreak
:::

The following key theorem states that `DCom.VerificationConditions`
does its job correctly.  Not surprisingly, each of the Hoare Logic
rules plays a critical role at some point in the proof.

```lean
theorem verification_correct (d : DCom) (P : Assertion)
    (hvc : d.VerificationConditions P) :
    ValidHoareTriple P d.erase d.postcondition := by
  sorry
```

:::instructors
Note that the reverse implication (of the theorem
above) doesn't hold.
:::

:::slidebreak
:::

Now that all the pieces are in place, we can define what it means
to verify an entire program.

```lean
def Decorated.VerificationConditions
    (dec : Decorated) : Prop :=
  dec.body.VerificationConditions dec.pre
```

And this brings us to the main theorem of this section:

```lean
theorem verification_conditions_correct (dec : Decorated)
    (hvc : dec.VerificationConditions) :
    dec.OuterTripleValid := by
  exact verification_correct dec.body dec.pre hvc
```

## More Automation

The propositions generated by `DCom.VerificationConditions` are fairly
big and contain many conjuncts that are essentially trivial.

:::dev
```
HIDE: MRC'20: The conditions here used to be just [Eval]ed instead
of being duplicated in a comment.  They were actually incorrect
because of changes to notation.  Putting them in as an [Example]
will force us to keep them up-to-date. APT20: Yes, but but stating
this an equality completely misses the point about verify_assertion! So I
changed things back.
```
:::

```lean
example : decWhile.VerificationConditions := by
  unfold Decorated.VerificationConditions decWhile
  simp only [DCom.VerificationConditions,
    DCom.postcondition]
  sorry
```

:::slidebreak
:::

Fortunately, our `verify_assertion` tactic can generally take care of
most (or sometimes all) of them.

```lean
example : decWhile.VerificationConditions := by
  sorry
```

:::slidebreak
:::

To automate the overall process of verification, we can use
`verification_correct` to extract the verification conditions, use
`verify_assertion` to verify them as much as it can, and finally tidy
up any remaining bits by hand.

```lean
macro "verify" : tactic =>
  `(tactic|
    (apply verification_conditions_correct;
     verify_assertion))
```

:::slidebreak
:::

Here's the final, formal proof that `decWhile` is correct.

```lean
theorem dec_while_correct :
    decWhile.OuterTripleValid := by
  sorry
```

::::::full
Similarly, here is the formal decorated program for the "swapping
by adding and subtracting" example that we saw earlier.

```lean
def swapDec (m n : Nat) : Decorated where
  pre := ({{ X = m ∧ Y = n }})
  body := dcom {
    ->> {{ (X + Y) - ((X + Y) - Y) = n ∧ (X + Y) - Y = m }}
    X := X + Y {{ X - (X - Y) = n ∧ X - Y = m }};
    Y := X - Y {{ X - Y = n ∧ Y = m }};
    X := X - Y {{ X = n ∧ Y = m }}
  }

theorem swap_correct (m n : Nat) :
    (swapDec m n).OuterTripleValid := by
  sorry
```

And here is the formal decorated version of the "positive
difference" program from earlier:

```lean
def positiveDifferenceDec : Decorated where
  pre := ({{ True }})
  body := dcom {
    if (X ≤ Y) then
      {{ True ∧ X ≤ Y }}
      ->> {{ (Y - X) + X = Y ∨ (Y - X) + Y = X }}
      Z := Y - X {{ Z + X = Y ∨ Z + Y = X }}
    else
      {{ True ∧ ¬ X ≤ Y }}
      ->> {{ (X - Y) + X = Y ∨ (X - Y) + Y = X }}
      Z := X - Y {{ Z + X = Y ∨ Z + Y = X }}
    end
      {{ Z + X = Y ∨ Z + Y = X }}
  }

theorem positive_difference_correct :
    positiveDifferenceDec.OuterTripleValid := by
  sorry
```

:::::exercise (rating := 2) (name := "if_minus_plus_correct")
Here is a skeleton of the formal decorated version of the
`if_minus_plus` program that we saw earlier.  Replace all
occurrences of `FILL_IN_HERE` with appropriate assertions and fill
in the proof (which should be just as straightforward as in the
examples above).

```lean
def ifMinusPlusDec : Decorated where
  pre := ({{ True }})
  body := dcom {
    if (X ≤ Y) then
      {{ True ∧ X ≤ Y }}
      ->> {{ Y = X + (Y - X) }}
      Z := Y - X {{ Y = X + Z }}
    else
      {{ True ∧ ¬ X ≤ Y }}
      ->> {{ X + Z = X + Z }}
      Y := X + Z {{ Y = X + Z }}
    end
      {{ Y = X + Z }}
  }

theorem if_minus_plus_correct :
    ifMinusPlusDec.OuterTripleValid := by
  solution!
    sorry
```
:::::

:::::exercise (rating := 2) (name := "div_mod_outer_triple_valid") (optional := Yes)
Fill in appropriate assertions for the division program from above.

```lean
def divModDec (a b : Nat) : Decorated where
  pre := ({{ True }})
  body := dcom {
    ->> {{ b * 0 + a = a }}
    X := ~(Aexp.num a) {{ b * 0 + X = a }};
    Y := 0 {{ b * Y + X = a }};
    while (~(Aexp.num b) ≤ X) do
      {{ b * Y + X = a ∧ b ≤ X }}
      ->> {{ b * (Y + 1) + (X - b) = a }}
      X := X - ~(Aexp.num b) {{ b * (Y + 1) + X = a }};
      Y := Y + 1 {{ b * Y + X = a }}
    end
      {{ b * Y + X = a ∧ ¬ b ≤ X }}
    ->> {{ b * Y + X = a ∧ X < b }}
  }

theorem div_mod_outer_triple_valid (a b : Nat) :
    (divModDec a b).OuterTripleValid := by
  solution!
    sorry
```
:::::

::::::

# Finding Loop Invariants

::::full
Once the outermost precondition and postcondition are
chosen, the only creative part of a verifying program using Hoare
Logic is finding the right loop invariants.  The reason this is
difficult is the same as the reason that inductive mathematical
proofs are:

- Strengthening a _loop invariant_ means that you have a stronger
  assumption to work with when trying to establish the
  postcondition of the loop body, but it also means that the loop
  body's postcondition is harder to prove.

- Similarly, strengthening an _induction hypothesis_ means that
  you have a stronger assumption to work with when trying to
  complete the induction step of the proof, but it also means that
  the statement being proved inductively is harder to prove.

This section explains how to approach the challenge of finding
loop invariants through a series of examples and exercises.
::::

::::terse
Once the outer pre- and postcondition are chosen, the only
creative part in verifying programs using Hoare Logic is finding
the right loop invariants...
::::

## Example: Slow Subtraction

:::dev "Chris Henson (chenson2018)" PotentialImprovement
After the latest changes I'm no fully longer
convinced about the use of incrementality in this example (the
reasoning at the end can be done directly on the original
skeleton). Try to find another example in which the pre- +
postcondition are enough to derive the invariant?
:::

:::instructors
The formal decorated program for this is called
`subtract_slowly_dec`, and it's given as an example in the formal
decorated programs section below
:::

The following program subtracts the value of `X` from the value of
`Y` by repeatedly decrementing both `X` and `Y`.  We want to verify its
correctness with respect to the pre- and postconditions shown:

```display
{{ X = m /\ Y = n }}
  while X <> 0 do
    Y := Y - 1;
    X := X - 1
  end
{{ Y = n - m }}
```

:::slidebreak
:::

To verify this program, we need to find an invariant `Inv` for the
loop.  As a first step we can leave `Inv` as an unknown and build a
_skeleton_ for the proof by applying the rules for local
consistency, working from the end of the program to the beginning,
as usual, and without doing any thinking at all yet.

:::slidebreak
:::

This leads to the following skeleton:

```display
(1)    {{ X = m /\ Y = n }}  ->>                   (a)
(2)    {{ Inv }}
         while X <> 0 do
(3)              {{ Inv /\ X <> 0 }}  ->>          (c)
(4)              {{ Inv [X |-> X-1] [Y |-> Y-1] }}
           Y := Y - 1;
(5)              {{ Inv [X |-> X-1] }}
           X := X - 1
(6)              {{ Inv }}
         end
(7)    {{ Inv /\ ~ (X <> 0) }}  ->>                (b)
(8)    {{ Y = n - m }}
```

:::slidebreak
:::

Examining this skeleton, we can see that any valid `Inv` will
have to respect three conditions:
- (a) it must be _weak_ enough to be implied by the loop's
  precondition, i.e., (1) must imply (2);
- (b) it must be _strong_ enough to imply the program's postcondition,
  i.e., (7) must imply (8);
- (c) it must be _preserved_ by a single iteration of the loop, assuming
  that the loop guard also evaluates to true, i.e., (3) must imply (4).

:::dev PotentialImprovement
Here's another opportunity for a bad `~` (in the proof)...
:::

::::terse
WORK IN CLASS (by filling in the previous template)
::::

:::slidebreak
:::

::::full
These conditions are actually independent of the particular
program and specification we are considering: every loop
invariant has to satisfy them.

One way to find a loop invariant that simultaneously satisfies these
three conditions is by using an iterative process: start with a
"candidate" invariant (e.g., a guess or a heuristic choice) and
check the three conditions above; if any of the checks fails, try
to use the information that we get from the failure to produce
another — hopefully better — candidate invariant, and repeat.

For instance, in the reduce-to-zero example above, we saw that,
for a very simple loop, choosing `True` as a loop invariant did the
job.  Maybe it will work here too.  To find out, let's try
instantiating `Inv` with `True` in the skeleton above and
see what we get...

```display
(1)    {{ X = m /\ Y = n }} ->>                    (a - OK)
(2)    {{ True }}
         while X <> 0 do
(3)                   {{ True /\ X <> 0 }} ->>     (c - OK)
(4)                   {{ True }}
           Y := Y - 1;
(5)                   {{ True }}
           X := X - 1
(6)                   {{ True }}
         end
(7)    {{ True /\ ~(X <> 0) }} ->>                 (b - WRONG!)
(8)    {{ Y = n - m }}
```

While conditions (a) and (c) are trivially satisfied,
(b) is wrong: it is not the case that `True /\ X = 0` (7)
implies `Y = n - m` (8).  In fact, the two assertions are
completely unrelated, so it is very easy to find a counterexample
to the implication (say, `Y = X = m = 0` and `n = 1`).

If we want (b) to hold, we need to strengthen the loop invariant so
that it implies the postcondition (8).  One simple way to do
this is to let the loop invariant _be_ the postcondition.  So let's
return to our skeleton, instantiate `Inv` with `Y = n - m`, and
try checking conditions (a) to (c) again.

```display
(1)    {{ X = m /\ Y = n }} ->>                        (a - WRONG!)
(2)    {{ Y = n - m }}
         while X <> 0 do
(3)                     {{ Y = n - m /\ X <> 0 }} ->>  (c - WRONG!)
(4)                     {{ Y - 1 = n - m }}
           Y := Y - 1;
(5)                     {{ Y = n - m }}
           X := X - 1
(6)                     {{ Y = n - m }}
         end
(7)    {{ Y = n - m /\ ~(X <> 0) }} ->>                (b - OK)
(8)    {{ Y = n - m }}
```

This time, condition (b) holds trivially, but (a) and (c) are
broken. Condition (a) requires that (1) `X = m /\ Y = n`
implies (2) `Y = n - m`.  If we substitute `Y` by `n` we have to
show that `n = n - m` for arbitrary `m` and `n`, which is not
the case (for instance, when `m = n = 1`).  Condition (c) requires
that `n - m - 1 = n - m`, which fails, for instance, for `n = 1`
and `m = 0`. So, although `Y = n - m` holds at the end of the loop,
it does not hold from the start, and it doesn't hold on each
iteration; it is not a correct loop invariant.

This failure is not very surprising: the variable `Y` changes
during the loop, while `m` and `n` are constant, so the assertion
we chose didn't have much chance of being a loop invariant!

To do better, we need to generalize (7) to some statement that is
equivalent to (8) when `X` is `0`, since this will be the case
when the loop terminates, and that "fills the gap" in some
appropriate way when `X` is nonzero.  Looking at how the loop
works, we can observe that `X` and `Y` are decremented together
until `X` reaches `0`.  So, if `X = 2` and `Y = 5` initially,
after one iteration of the loop we obtain `X = 1` and `Y = 4`;
after two iterations `X = 0` and `Y = 3`; and then the loop stops.
Notice that the difference between `Y` and `X` stays constant
between iterations: initially, `Y = n` and `X = m`, and the
difference is always `n - m`.  So let's try instantiating `Inv` in
the skeleton above with `Y - X = n - m`.

```display
(1)    {{ X = m /\ Y = n }} ->>                            (a - OK)
(2)    {{ Y - X = n - m }}
         while X <> 0 do
(3)                    {{ Y - X = n - m /\ X <> 0 }} ->>   (c - OK)
(4)                    {{ (Y - 1) - (X - 1) = n - m }}
           Y := Y - 1;
(5)                    {{ Y - (X - 1) = n - m }}
           X := X - 1
(6)                    {{ Y - X = n - m }}
         end
(7)    {{ Y - X = n - m /\ ~(X <> 0) }} ->>                (b - OK)
(8)    {{ Y = n - m }}
```

Success!  Conditions (a), (b) and (c) all hold now.  (To
verify (c), we need to check that, under the assumption that
`X <> 0`, we have `Y - X = (Y - 1) - (X - 1)`; this holds for all
natural numbers `X` and `Y`.)

Here is the final version of the decorated program:

```lean
def subtractSlowlyDec (m n : Nat) : Decorated where
  pre := ({{ X = m ∧ Y = n }})
  body := dcom {
    ->> {{ Y - X = n - m }}
    while (X ≠ 0) do
      {{ Y - X = n - m ∧ ¬ X = 0 }}
      ->> {{ (Y - 1) - (X - 1) = n - m }}
      Y := Y - 1 {{ Y - (X - 1) = n - m }};
      X := X - 1 {{ Y - X = n - m }}
    end
      {{ Y - X = n - m ∧ X = 0 }}
    ->> {{ Y = n - m }}
  }

theorem subtract_slowly_outer_triple_valid (m n : Nat) :
    (subtractSlowlyDec m n).OuterTripleValid := by
  sorry
```
::::

## Exercise: Slow Assignment

:::suppressPreviousHeaderWhenTerse
:::

::::::full
:::::exercise (rating := 2) (name := "slow_assignment")
A roundabout way of assigning a number currently stored in `X` to
the variable `Y` is to start `Y` at `0`, then decrement `X` until
it hits `0`, incrementing `Y` at each step. Here is a program that
implements this idea.  Fill in decorations and prove the decorated
program correct. (The proof should be very simple.)

```lean
def slowAssignmentDec (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body := dcom {
    Y := 0 {{ solution!({{ X = m ∧ Y = 0 }}) }};
    (->> {{ solution!({{ Y + X = m }}) }}
      while (X ≠ 0) do
        {{ solution!({{ Y + X = m ∧ ¬ X = 0 }}) }}
        ->> {{ solution!({{ Y + (X - 1) + 1 = m }}) }}
        X := X - 1 {{ solution!({{ Y + X + 1 = m }}) }};
        (->> {{ solution!({{ Y + X + 1 = m }}) }}
          Y := Y + 1 {{ solution!({{ Y + X = m }}) }})
      end
        {{ solution!({{ Y + X = m ∧ X = 0 }}) }}
      ->> {{ Y = m }})
  }

theorem slow_assignment (m : Nat) :
    (slowAssignmentDec m).OuterTripleValid := by
  solution!
    sorry
```
:::::

::::::

## Example: Parity

:::suppressPreviousHeaderWhenTerse
:::

:::instructors
This is the simplest implementation we could find of
parity in Imp.
:::

::::::full
Here is a cute way of computing the parity of a value initially
stored in `X`, due to Daniel Cristofani.

```display
{{ X = m }}
  while 2 <= X do
    X := X - 2
  end
{{ X = parity m }}
```

The `parity` function used in the specification is defined in
Lean as follows:

```lean
def parity : Nat → Nat
  | 0 => 0
  | 1 => 1
  | Nat.succ (Nat.succ n) => parity n
```

:::slidebreak
:::

The postcondition does not hold at the beginning of the loop,
since `m = parity m` does not hold for an arbitrary `m`, so we
cannot hope to use that as a loop invariant.  To find a loop invariant
that works, let's think a bit about what this loop does.  On each
iteration it decrements `X` by `2`, which preserves the parity of `X`.
So the parity of `X` does not change, i.e., it is invariant.  The initial
value of `X` is `m`, so the parity of `X` is always equal to the
parity of `m`. Using `parity X = parity m` as an invariant we
obtain the following decorated program:

```display
{{ X = m }} ->>                                         (a - OK)
{{ parity X = parity m }}
  while 2 <= X do
               {{ parity X = parity m /\ 2 <= X }} ->>  (c - OK)
               {{ parity (X-2) = parity m }}
    X := X - 2
               {{ parity X = parity m }}
  end
{{ parity X = parity m /\ ~(2 <= X) }} ->>              (b - OK)
{{ X = parity m }}
```

With this loop invariant, conditions (a), (b), and (c) are all
satisfied. For verifying (b), we observe that, when `X < 2`, we
have `parity X = X` (we can easily see this in the definition of
`parity`).  For verifying (c), we observe that, when `2 <= X`, we
have `parity X = parity (X-2)`.

:::dev
```
HIDE: A more complexly phrased loop invariant for the same program
[[
        {{ X = m }}  ->>                        (a - OK)
        {{ ev X <-> ev m }}
      while 2 <= X do
          {{ ev X <-> ev m /\ 2 <= X }}  ->>    (c - OK)
          {{ ev (X-2) <-> ev m }}
        X := X - 2
          {{ ev X <-> ev m }}
      end
        {{ (ev X <-> ev m) /\ ~(2 <= X) }}  ->>     (b - OK)
        {{ X=0 <-> ev m }}
]]
```

```
HIDE: find_parity'_dec; more complicated phrasing of invariant
there is very little resemblance between the invariant and the
postcondition -- the implication is also non-obvious, and the
X <= m condition makes the invariant more complicated
[[
 {{ X = m }} ->>
 {{ X <= m /\ ev (m - X) }}
while 2 <= X do
   {{ X <= m /\ ev (m - X) /\ 2 <= X }} ->>
   {{ X - 2 <= m /\ ev (m - (X - 2)) }}
 X := X - 2
   {{ X <= m /\ ev (m - X) }}
end
 {{ X <= m /\ ev (m - X) /\ ~(2 <= X) }} ->>
 {{ X=0 <-> ev m }}
]]
```
:::

:::::exercise (rating := 3) (name := "parity") (optional := Yes)
Translate the above informal decorated program into a formal one
and prove it correct.

Hint: There are actually several possible loop invariants that all
lead to good proofs; one that leads to a particularly simple proof
is `parity X = parity m`. Ordinary Lean functions can be applied
directly to Imp variables inside assertions, so this can be written
as `{{ parity X = parity m }}`.

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2023)
```
Maya: In the parity exercise, I was getting annoyed
by the verify_assertion tactic unfolding the assumption [(2 <=?  st
X) = true] into a match on the first two layers of [st X]. I ended
up digging out the following incantation from the depths of the Rocq
manual:

   Arguments leb !n !m.

I'm not sure what level of automated tests you keep for the
exercises, so I wanted to point this struggle out. Perhaps
something changed in the Rocq library at some point.

BCP 23: Worth looking into!  (I tried just adding [Arguments leb !n
!m.] to the script, but that broke things.)
```
:::

```lean
def parityDec (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body :=
    let inv : Assertion :=
      solution!(fun st => parity st[X] = parity m)
    let guardedInv : Assertion :=
      solution!(fun st =>
        parity st[X] = parity m ∧ 2 ≤ st[X])
    let bodyPre : Assertion :=
      solution!(fun st => parity (st[X] - 2) = parity m)
    let exit : Assertion :=
      solution!(fun st =>
        parity st[X] = parity m ∧ ¬ 2 ≤ st[X])
    let post : Assertion :=
      fun st => st[X] = parity m
    dcom {
    ->> {{ inv }}
    while (2 ≤ X) do
      {{ guardedInv }}
      ->> {{ bodyPre }}
      X := X - 2 {{ inv }}
    end
      {{ exit }}
    ->> {{ post }}
  }
```

If you use the suggested loop invariant, you may find the following
two lemmas helpful.

```lean
theorem parity_ge_2 (x : Nat) (h : 2 ≤ x) :
    parity (x - 2) = parity x := by
  sorry

theorem parity_lt_2 (x : Nat) (h : ¬ 2 ≤ x) :
    parity x = x := by
  sorry

theorem parity_outer_triple_valid (m : Nat) :
    (parityDec m).OuterTripleValid := by
  solution!
    -- Simplification is too aggressive here; recover the
    -- folded guard before proving preservation and exit.
    sorry

-- SOLUTION
/- Here is another loop invariant — arguably a more natural
one —
which sadly leads to a rather long proof. -/
inductive Even : Nat → Prop where
  | zero : Even 0
  | addTwo {n : Nat} : Even n → Even (Nat.succ (Nat.succ n))

def findParityDec (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body :=
    let inv : Assertion :=
      fun st => st[X] ≤ m ∧ Even (m - st[X])
    let guardedInv : Assertion :=
      fun st => (st[X] ≤ m ∧ Even (m - st[X])) ∧ 2 ≤ st[X]
    let bodyPre : Assertion :=
      fun st => st[X] - 2 ≤ m ∧ Even (m - (st[X] - 2))
    let exit : Assertion :=
      fun st => (st[X] ≤ m ∧ Even (m - st[X])) ∧ st[X] < 2
    let post : Assertion := fun st => st[X] = 0 ↔ Even m
    dcom {
    ->> {{ inv }}
    while (2 ≤ X) do
      {{ guardedInv }}
      ->> {{ bodyPre }}
      X := X - 2 {{ inv }}
    end
      {{ exit }}
    ->> {{ post }}
  }

theorem find_parity_correct (m : Nat) :
    (findParityDec m).OuterTripleValid := by
  -- Simplification is too aggressive here; recover the
  -- folded guard before proving preservation and exit.
  -- At loop exit, X can only be 0 or 1.
  sorry

/- Here is a more intuitive way of writing the loop
invariant. -/
def findParityDec' (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body :=
    let inv : Assertion := fun st => Even st[X] ↔ Even m
    let guardedInv : Assertion :=
      fun st => (Even st[X] ↔ Even m) ∧ 2 ≤ st[X]
    let bodyPre : Assertion :=
      fun st => Even (st[X] - 2) ↔ Even m
    let exit : Assertion :=
      fun st => (Even st[X] ↔ Even m) ∧ ¬ 2 ≤ st[X]
    let post : Assertion := fun st => st[X] = 0 ↔ Even m
    dcom {
    ->> {{ inv }}
    while (2 ≤ X) do
      {{ guardedInv }}
      ->> {{ bodyPre }}
      X := X - 2 {{ inv }}
    end
      {{ exit }}
    ->> {{ post }}
  }

theorem find_parity_correct' (m : Nat) :
    (findParityDec' m).OuterTripleValid := by
  -- Simplification is too aggressive here; recover the
  -- folded guard before proving preservation and exit.
  -- At loop exit, X can only be 0 or 1.
  sorry

/- Finally, just for fun, here is an old-style
non-decorated-program proof. -/
theorem parity_correct (m : Nat) :
    {{ X = m }}
        while (2 ≤ X) {
          X := X - 2
        }
    {{ fun st => st[X] = parity m }} := by
  sorry
-- END SOLUTION
```
:::::

::::::

## Example: Finding Square Roots

:::suppressPreviousHeaderWhenTerse
:::

:::instructors
the main idea introduced here is preserving equalities for
variables that don't change, and it appears in its purest form here.
:::

::::::full
The following program computes the integer square root of `X`
by naive iteration:

```display
{{ X=m }}
  Z := 0;
  while (Z+1)*(Z+1) <= X do
    Z := Z+1
  end
{{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
```

WORK IN CLASS

As we did before, we can try to use the postcondition as a
candidate loop invariant, obtaining the following decorated program:

```display
(1)  {{ X=m }} ->>                  (a - second conjunct of (2) WRONG!)
(2)  {{ 0*0 <= m /\ m<(0+1)*(0+1) }}
        Z := 0
(3)            {{ Z*Z <= m /\ m<(Z+1)*(Z+1) }};
        while (Z+1)*(Z+1) <= X do
(4)            {{ Z*Z<=m /\ m<(Z+1)*(Z+1)
                         /\ (Z+1)*(Z+1)<=X }} ->>          (c - WRONG!)
(5)            {{ (Z+1)*(Z+1)<=m /\ m<((Z+1)+1)*((Z+1)+1) }}
          Z := Z+1
(6)            {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
        end
(7)  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) /\ ~((Z+1)*(Z+1)<=X) }} ->>    (b - OK)
(8)  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
```

This didn't work very well: conditions (a) and (c) both failed.
Looking at condition (c), we see that the second conjunct of (4)
is almost the same as the first conjunct of (5), except that (4)
mentions `X` while (5) mentions `m`. But note that `X` is never
assigned in this program, so we should always have `X=m`. We
didn't propagate this information from (1) into the loop
invariant, but we could!

Also, we don't need the second conjunct of (8), since we can
obtain it from the negation of the guard — the third conjunct
in (7) — again under the assumption that `X=m`.  This allows
us to simplify a bit.

So we now try `X=m /\ Z*Z <= m` as the loop invariant:

```display
{{ X=m }} ->>                                           (a - OK)
{{ X=m /\ 0*0 <= m }}
  Z := 0
             {{ X=m /\ Z*Z <= m }};
  while (Z+1)*(Z+1) <= X do
             {{ X=m /\ Z*Z<=m /\ (Z+1)*(Z+1)<=X }} ->>  (c - OK)
             {{ X=m /\ (Z+1)*(Z+1)<=m }}
    Z := Z + 1
             {{ X=m /\ Z*Z<=m }}
  end
{{ X=m /\ Z*Z<=m /\ ~((Z+1)*(Z+1)<=X) }} ->>            (b - OK)
{{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
```

This works, since conditions (a), (b), and (c) are now all
rather trivially satisfied.

Very often, when a variable is used in a loop in a read-only
fashion (i.e., it is referred to by the program or by the
specification, and it is not changed by the loop), it is necessary
to record the _fact_ that it doesn't change in the loop invariant.

:::::exercise (rating := 3) (name := "sqrt") (optional := Yes)
Translate the above informal decorated program into a formal one
and prove it correct.

Hint: The loop invariant here must ensure that `Z*Z` is consistently
less than or equal to X.

```lean
def sqrtDec (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body := dcom {
    ->> {{ solution!({{ X = m ∧ 0 * 0 ≤ m }}) }}
    Z := 0 {{ solution!({{ X = m ∧ Z * Z ≤ m }}) }};
    while ((Z + 1) * (Z + 1) ≤ X) do
      {{ solution!({{
        (X = m ∧ Z * Z ≤ m) ∧
        (Z + 1) * (Z + 1) ≤ X
      }}) }}
      ->> {{ solution!({{
        X = m ∧ (Z + 1) * (Z + 1) ≤ m
      }}) }}
      Z := Z + 1 {{ solution!({{ X = m ∧ Z * Z ≤ m }}) }}
    end
      {{ solution!({{
        (X = m ∧ Z * Z ≤ m) ∧
        ¬ (Z + 1) * (Z + 1) ≤ X
      }}) }}
    ->> {{ Z * Z ≤ m ∧ m < (Z + 1) * (Z + 1) }}
  }

theorem sqrt_correct (m : Nat) :
    (sqrtDec m).OuterTripleValid := by
  solution!
    sorry
```
:::::

::::::

## Example: Squaring

:::suppressPreviousHeaderWhenTerse
:::

:::instructors
using easier version of this: counting up, instead of
counting down...
:::

:::dev
HIDE: CH: it might make sense to show all the variants
for future exercise builders, together with some hints on how to
write programs that are easier to verify
:::

::::full
Here is a program that squares `X` by repeated addition:

```display
{{ X = m }}
  Y := 0;
  Z := 0;
  while Y <> X  do
    Z := Z + X;
    Y := Y + 1
  end
{{ Z = m*m }}
```

WORK IN CLASS

The first thing to note is that the loop reads `X` but doesn't
change its value. As we saw in the previous example, it can be a good idea
in such cases to add `X = m` to the loop invariant.  The other thing
that we know is often useful in the loop invariant is the postcondition,
so let's add that too, leading to the candidate loop invariant
`Z = m * m /\ X = m`.

```display
{{ X = m }} ->>                                       (a - WRONG)
{{ 0 = m*m /\ X = m }}
  Y := 0
               {{ 0 = m*m /\ X = m }};
  Z := 0
               {{ Z = m*m /\ X = m }};
  while Y <> X do
               {{ Z = m*m /\ X = m /\ Y <> X }} ->>   (c - WRONG)
               {{ Z+X = m*m /\ X = m }}
    Z := Z + X
               {{ Z = m*m /\ X = m }};
    Y := Y + 1
               {{ Z = m*m /\ X = m }}
  end
{{ Z = m*m /\ X = m /\ ~(Y <> X) }} ->>               (b - OK)
{{ Z = m*m }}
```

Conditions (a) and (c) fail because of the `Z = m*m` part.  While
`Z` starts at `0` and works itself up to `m*m`, we can't expect
`Z` to be `m*m` from the start.  If we look at how `Z` progresses
in the loop, after the 1st iteration `Z = m`, after the 2nd
iteration `Z = 2*m`, and at the end `Z = m*m`.  Since the variable
`Y` tracks how many times we go through the loop, this leads us to
derive a new loop invariant candidate: `Z = Y*m /\ X = m`.

```display
{{ X = m }} ->>                                        (a - OK)
{{ 0 = 0*m /\ X = m }}
  Y := 0
                {{ 0 = Y*m /\ X = m }};
  Z := 0
                {{ Z = Y*m /\ X = m }};
  while Y <> X do
                {{ Z = Y*m /\ X = m /\ Y <> X }} ->>   (c - OK)
                {{ Z+X = (Y+1)*m /\ X = m }}
    Z := Z + X
                {{ Z = (Y+1)*m /\ X = m }};
    Y := Y + 1
                {{ Z = Y*m /\ X = m }}
  end
{{ Z = Y*m /\ X = m /\ ~(Y <> X) }} ->>                (b - OK)
{{ Z = m*m }}
```

This new loop invariant makes the proof go through: all three
conditions are easy to check.

It is worth comparing the postcondition `Z = m*m` and the
`Z = Y*m` conjunct of the loop invariant. It is often the case
that one has to replace parameters with variables — or with
expressions involving both variables and parameters, like
`m - Y` — when going from postconditions to loop invariants.

:::dev
```
HIDE: the more complicated version from 2012's class

Here is a program that squares X by repeated addition:
[[
  X := n;
  Y := X;
  Z := 0;
  while Y <> 0 do
    Z := Z + X;
    Y := Y - 1
  end
]]

  Bob's simpler loop invariant for squaring [square_dec]:
  (a very similar invariant given as solution in 2011 final; exercise 3)

[[
  {{ True }}
  X := n;
  {{ X = n }}
  Y := X;
  {{ X = n /\ Y = n }}
  Z := 0;
  {{ X = n /\ Y = n /\ Z = 0}} ->>
  {{ Z + X * Y = n * n }}
  while Y <> 0 do
    {{ Z + X * Y = n * n /\ (Y <> 0)}} ->>
    {{ Z + X + X * (Y - 1) = n * n }}
    Z := Z + X;
    {{ Z + X * (Y - 1) = n * n }}
    Y := Y - 1
    {{ Z + X * Y = n * n }}
  end
  {{ Z + X * Y = n * n /\ ~(Y <> 0)}} ->>
  {{ Z = n * n }}
]]

The other loop invariant [square_dec']:
[[
  {{ True }}
  X := n;
  {{ X = n }}
  Y := X;
  {{ X = n /\ Y = n }}
  Z := 0;
  {{ X = n /\ Y = n /\ Z = 0}} ->>
  {{ Z = X * (X - Y) /\ X = n /\ Y <= X }}
  while Y <> 0 do
    {{ Z = X * (X - Y) /\ X = n /\ Y <= X /\ (Y <> 0)}} ->>
    {{ Z + X = X * (X - (Y - 1)) /\ X = n /\ (Y - 1) <= X }}
    Z := Z + X;
    {{ Z = X * (X - (Y - 1)) /\ X = n /\ (Y - 1) <= X }}
    Y := Y - 1
    {{ Z = X * (X - Y) /\ X = n /\ Y <= X }}
  end
  {{ Z = X * (X - Y) /\ X = n /\ Y <= X /\ ~(Y <> 0)}} ->>
  {{ Z = n * n }}
]]
```
:::
::::

::::hide
```
/- HIDE: Don't really see the point of making them type in the
decorations again. -/
-- EX3? (square)
/- Translate the above informal decorated program into a formal one
and prove it correct. -/

/- HIDE: Again, there are several ways of annotating the
squaring program.  The simplest variant we've found,
[square_simpler_dec], is given last. -/
        Definition square_dec (m : nat) : decorated :=
          <{
          {{ X = m }}
            Y := X
            {{ X = m /\ Y = m }};
            Z := 0
            {{ X = m /\ Y = m /\ Z = 0}} ->>
            {{ Z + X * Y = m * m }};
            while Y <> 0 do
              {{ Z + X * Y = m * m /\ Y <> 0 }} ->>
              {{ (Z + X) + X * (Y - 1) = m * m }}
              Z := Z + X
              {{ Z + X * (Y - 1) = m * m }};
              Y := Y - 1
              {{ Z + X * Y = m * m }}
            end
          {{ Z + X * Y = m * m /\ Y = 0 }} ->>
          {{ Z = m * m }} }>.

        Theorem square_outer_triple_valid : forall m,
          outer_triple_valid (square_dec m).
        Proof.
          verify.
          - (* loop invariant preserved *)
            destruct (st Y) as [| y'].
            + exfalso. auto.
            + simpl. rewrite sub_0_r.
            assert (G : forall n m, n * S m = n + n * m). {
              clear. intros. induction n.
              - reflexivity.
              - simpl. rewrite IHn. lia. }
            rewrite <- H. rewrite G. lia.
        Qed.

        Definition square_dec' (n : nat) : decorated :=
          <{
          {{ True }}
          X := n
          {{ X = n }};
          Y := X
          {{ X = n /\ Y = n }};
          Z := 0
          {{ X = n /\ Y = n /\ Z = 0 }} ->>
          {{ Z = X * (X - Y)
                       /\ X = n /\ Y <= X }};
          while Y <> 0 do
            {{ (Z = X * (X - Y)
                        /\ X = n /\ Y <= X)
                        /\  Y <> 0 }}
            Z := Z + X
            {{ Z = X * (X - (Y - 1))
                         /\ X = n /\ Y <= X }};
            Y := Y - 1
            {{ Z = X * (X - Y)
                         /\ X = n /\ Y <= X }}
          end
          {{ (Z = X * (X - Y)
                      /\ X = n /\ Y <= X)
                       /\ Y = 0 }} ->>
          {{ Z = n * n }} }>.

        Theorem square_dec'_correct : forall (n:nat),
          outer_triple_valid (square_dec' n).
        Proof.
          verify.
          /- loop invariant holds initially, proven by verify -/
          (* loop invariant preserved *) subst.
          rewrite mul_sub_distr_l.
          repeat rewrite mul_sub_distr_l. rewrite mul_1_r.
          assert (G : forall n m p,
                     m <= n -> p <= m -> n - (m - p) = n - m + p).
          { intros. lia. }
          rewrite G.
          - reflexivity.
          - apply mul_le_mono_l. assumption.
          - destruct (st Y).
            + exfalso. auto.
            + lia.
          /- loop invariant + negation of guard imply
          desired postcondition proven by [verify] -/
        Qed.

/- HIDE: Here's the main exercise... -/
    Definition square_simpler_dec (m : nat) : decorated :=
      <{
        {{ X = m }} ->>
        {{ (* SOL *) 0 = 0*m /\ X = m (* /SOL *)}}
          Y := 0
                       {{ 0 = Y*m /\ X = m }};
          Z := 0
                       {{ Z = Y*m /\ X = m }};
          while Y <> X do
                       {{ (* SOL *) (Z = Y*m /\ X = m) /\ Y <> X (* /SOL *) }} ->>
                       {{ (* SOL *) Z + X = (Y + 1)*m /\ X = m (* /SOL *) }}
            Z := Z + X
                       {{ (* SOL *) Z = (Y + 1)*m /\ X = m (* /SOL *) }};
            Y := Y + 1
                       {{ Z = Y*m /\ X = m }}
          end
        {{ (* SOL *) (Z = Y*m /\ X = m) /\ Y = X (* /SOL *) }} ->>
        {{ Z = m*m }}
      }>.

    Theorem square_simpler_outer_triple_valid : forall m,
      outer_triple_valid (square_simpler_dec m).
    Proof.
      solution!
        verify.
      Qed.
-- []
```
::::

## Exercise: Factorial

:::suppressPreviousHeaderWhenTerse
:::

:::dev BeforeNextRelease
Move this later?  Might be harder than some of the others.
:::

:::dev
```
HIDE: LY: Many are tempted to use division in their propositions here,
with the loop invariant [Y = m!/X!].
Informally, such a decorated program can be correct if we assume
they use real division (in Q or R). The issue is that formally in Rocq,
the notation / is also in scope and means integer division, so a pedantic
interpretation would mark those answers wrong, even though that is most
likely *not* what students intended (thus making the grading unfair).
Should we explicitly forbid use of division for this exercise?
(I added a note to that effect in the problem statement).

MRC'20: I strengthened your note so that it explicitly advises
against division (and subtraction).
```
:::

::::::full
:::::exercise (rating := 4) (name := "factorial_correct") (level := Advanced)
Recall that `n!` denotes the factorial of `n` (i.e., `n! =
1*2*...*n`).  We can define the factorial function recursively in
Lean as follows:

```lean
def fact : Nat → Nat
  | 0 => 1
  | Nat.succ n => Nat.succ n * fact n

#eval fact 5
```

First, write the Imp program `factorial` that calculates the factorial
of the number initially stored in the variable `X` and puts it in
the variable `Y`.

Using your definition `factorial` and `slowAssignmentDec` as a
guide, write a formal decorated program `factorialDec` that
implements the factorial function.  Ordinary Lean functions such as
`fact` can be applied directly to Imp variables inside assertions.

Fill in the blanks and finish the proof of correctness. Bear in mind
that we are working with natural numbers, for which both division
and subtraction can behave differently than with real numbers.
Excluding both operations from your loop invariant is advisable!

Then state a theorem named `factorial_correct` that says
`factorialDec` is correct, and prove the theorem.  If all goes
well, `verify` will leave you with just two subgoals, each of
which requires establishing some mathematical property of `fact`,
rather than proving anything about your program.

Hint: if those two subgoals become tedious to prove, give some
thought to how you could restate your assertions such that the
mathematical operations are more amenable to manipulation in Lean.
For example, recall that `1 + ...` is easier to work with than
`... + 1`.

```lean
def factorialDec (m : Nat) : Decorated := solution!({
  pre := ({{ X = m }})
  body := dcom {
    ->> {{ 1 * fact X = fact m }}
    Y := 1 {{ Y * fact X = fact m }};
    while (X ≠ 0) do
      {{ Y * fact X = fact m ∧ ¬ X = 0 }}
      ->> {{ (Y * X) * fact (X - 1) = fact m }}
      Y := Y * X {{ Y * fact (X - 1) = fact m }};
      X := X - 1 {{ Y * fact X = fact m }}
    end
      {{ Y * fact X = fact m ∧ X = 0 }}
    ->> {{ Y = fact m }}
  }
})

theorem fact_sub_one (m : Nat) (h : m ≠ 0) :
    m * fact (m - 1) = fact m := by
  solution!
    sorry

theorem factorial_correct (m : Nat) :
    (factorialDec m).OuterTripleValid := by
  solution!
    sorry
```

:::dev PotentialImprovement
```
Here's a variant that I (BCP) tried working out.  I'm not
sure I've got it quite right yet, but it's probably worth finishing
because it nicely illustrates the point that the way you write the
program often determines how hard it is to verify...

 {{ True }} ->>
 {{ m! = 1 * m!/0! /\ 0 <= m }}
Y := 1;
 {{ m! = Y * m!/0! /\ 0 <= m }}
X := 0;
 {{ m! = Y * m!/X! /\ X <= m }}
while X .< m do
   {{ m! = Y * m!/X! /\ X <= m /\ X < m }} ->>
   {{ ... needs work here! ... }} ->>
   {{ m! = (Y*(X+1)) * m!/(X+1)! /\ (X+1) <= m }} ->>
 X := X + 1;
   {{ m! = (Y*X) * m!/X! /\ X <= m }} ->>
 Y := Y * X
   {{ m! = Y * m!/X! /\ X <= m }}
end
 {{ m! = Y * m!/X! /\ X <= m /\ ~(X < m) }} ->>
 {{ Y = m! }}
```
:::

:::dev
HIDE: MRC'20: That's not really an Imp program though: it is a
schema for an Imp program.  `m` is not an Imp variable nor a
constant.  BCP 21: But we do that all over the place, no?

```
HIDE: LY: I saw one submission for [factorial_dec] use a program
like that instead of the one already given by the informal
exercise. I accepted it because the exercise does not require to
reuse the given program, and we did not strictly define what it
means to "implement" factorial in Imp.  This other one "implements"
factorial in the same way two_loops_dec "implements" the sum (a + b
+ c).
```
:::
:::::

::::::

## Exercise: Minimum

:::suppressPreviousHeaderWhenTerse
:::

::::hide
```
/- SAZ 2022: Double checking the loop invariant for 2020 midterm2 -/

Definition DONE : string := "DONE".

Definition LI m n (st:state) : Prop :=
  (~(st DONE = 0) /\ (st X) = min m n /\ (st Y) = max m n)
  \/
  ((st DONE = 0) /\ ((st X = m /\ st Y = n) \/ (m > n /\ st X = n /\ st Y = m)))
  .

Definition min_exam_question (m n : nat) : decorated :=
  <{
      {{ X = m /\ Y = n }}
        DONE := 0
                  {{ DONE = 0 /\ X = m /\ Y = n }} ;
        while DONE = 0 do
                  {{ DONE = 0 /\ $(LI m n)}}
                        if X > Y then
                          {{ X > Y /\ (DONE = 0 /\ ((Y = m /\ X = n) \/ (m > n /\ Y = n /\ X = m)) ) }} ->>
                          {{ (~(DONE = 0) /\ Y = #min m n /\ X = #max m n) \/
                                      (DONE = 0 /\ ((Y = m /\ X = n) \/ (m > n /\ Y = n /\ X = m))) }}
                          Z := Y
                                 {{ (~(DONE = 0) /\ Z = #min m n /\ X = #max m n) \/
                                      (DONE = 0 /\ ((Z = m /\ X = n) \/ (m > n /\ Z = n /\ X = m)))
                                 }} ;
                          Y := X
                                 {{ (~(DONE = 0) /\ Z = #min m n /\ Y = #max m n) \/
                                    (DONE = 0 /\ ((Z = m /\ Y = n) \/ (m > n /\ Z = n /\ Y = m)))
                                 }} ;
                          X := Z
                                 {{ $(LI m n) }}
                        else
                          {{ ~(X > Y) /\ X = #min m n /\ Y = #max m n }} ->>
                          {{ (~(1 = 0) /\ X = #min m n /\ Y = #max m n) }}
                          DONE := 1
                          {{ $(LI m n) }}
                  end
                  {{ $(LI m n) }}
                  end
     {{ ~(DONE = 0) /\ $(LI m n) }} ->>
      {{ X = #min m n /\ Y = #max m n }}
    }>.

Theorem min_exam_question_v1_correct : forall m n,
  outer_triple_valid (min_exam_question m n).
Proof.
  solution!
    unfold min_exam_question.
    unfold LI.
    verify.
  Qed.

  Definition LI2 m n (st:state) : Prop :=
    (~(st DONE = 0) /\ (st X) = min m n /\ (st Y) = max m n)
    \/
    ((st DONE = 0) /\ ((st X = m /\ st Y = n) \/ (st X = n /\ st Y = m)))
    .

  Definition min_exam_question2 (m n : nat) : decorated :=
    <{
        {{ X = m /\ Y = n }}
          DONE := 0
                    {{ DONE = 0 /\ X = m /\ Y = n }} ;
          while DONE = 0 do
                    {{ DONE = 0 /\ $(LI2 m n)}}
                          if X > Y then
                            {{ X > Y /\ (DONE = 0 /\ ((Y = m /\ X = n) \/ (Y = n /\ X = m)) ) }} ->>
                            {{ (~(DONE = 0) /\ Y = #min m n /\ X = #max m n) \/
                                        (DONE = 0 /\ ((Y = m /\ X = n) \/ (Y = n /\ X = m))) }}
                            Z := Y
                                   {{ (~(DONE = 0) /\ Z = #min m n /\ X = #max m n) \/
                                        (DONE = 0 /\ ((Z = m /\ X = n) \/ (Z = n /\ X = m)))
                                   }} ;
                            Y := X
                                   {{ (~(DONE = 0) /\ Z = #min m n /\ Y = #max m n) \/
                                      (DONE = 0 /\ ((Z = m /\ Y = n) \/ (Z = n /\ Y = m)))
                                   }} ;
                            X := Z
                                   {{ $(LI2 m n) }}
                          else
                            {{ ~(X > Y) /\ X = #min m n /\ Y = #max m n }} ->>
                            {{ (~(1 = 0) /\ X = #min m n /\ Y = #max m n) }}
                            DONE := 1
                            {{ $(LI2 m n) }}
                    end
                    {{ $(LI2 m n) }}
                    end
       {{ ~(DONE = 0) /\ $(LI2 m n) }} ->>
        {{ X = #min m n /\ Y = #max m n }}
      }>.

  Theorem min_exam_question_v2_correct : forall m n,
    outer_triple_valid (min_exam_question2 m n).
  Proof.
  -- ADMITTED
    unfold min_exam_question2.
    unfold LI2.
    verify.
  Qed.
```
::::

::::::full
:::::exercise (rating := 3) (name := "minimum_correct") (level := Advanced)
Fill in decorations for the following program and prove them
correct.  As with `factorial`, be careful about mathematical
reasoning involving natural numbers, especially subtraction.

Lean functions can be applied directly inside assertions.  For
example, the minimum of `a` and `b` can be written `Nat.min a b`.

:::dev
HIDE: MRC'20: It bothers me a bit that the `&&` in the guard below
becomes a `/\` in the assertion.  We've never explained that it's okay
to do a translation like that.
:::

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2025)
```
Maybe we should write /\ in assertions??
```
:::

```lean
def minimumDec (a b : Nat) : Decorated where
  pre := ({{ True }})
  body := dcom {
    ->> {{ solution!({{ 0 + Nat.min a b = Nat.min a b }}) }}
    X := ~(Aexp.num a) {{
      solution!({{ 0 + Nat.min X b = Nat.min a b }})
    }};
    Y := ~(Aexp.num b) {{
      solution!({{ 0 + Nat.min X Y = Nat.min a b }})
    }};
    Z := 0 {{
      solution!({{ Z + Nat.min X Y = Nat.min a b }})
    }};
    while (X ≠ 0 ∧ Y ≠ 0) do
      {{ solution!({{
        Z + Nat.min X Y = Nat.min a b ∧ (¬ X = 0 ∧ ¬ Y = 0)
      }}) }}
      ->> {{ solution!({{
        Z + 1 + Nat.min (X - 1) (Y - 1) = Nat.min a b
      }}) }}
      X := X - 1 {{
        solution!({{
          Z + 1 + Nat.min X (Y - 1) = Nat.min a b
        }})
      }};
      Y := Y - 1 {{
        solution!({{ Z + 1 + Nat.min X Y = Nat.min a b }})
      }};
      Z := Z + 1 {{
        solution!({{ Z + Nat.min X Y = Nat.min a b }})
      }}
    end
      {{ solution!({{
        Z + Nat.min X Y = Nat.min a b ∧
        ¬ (¬ X = 0 ∧ ¬ Y = 0)
      }}) }}
    ->> {{ Z = Nat.min a b }}
  }
```

:::dev PotentialImprovement
HIDE:

- The first implication follows by substitution and arithmetic.
- For the second, the loop guard says that `X` and `Y` are nonzero.
  Thus `Nat.min X Y` is nonzero, and
  `Nat.min (X - 1) (Y - 1) = Nat.min X Y - 1`. Natural-number
  subtraction therefore does not truncate the result to zero, and
  `Z + 1 + Nat.min (X - 1) (Y - 1)` can be rewritten as
  `Z + Nat.min X Y`.
- For the third, the negated loop guard says that at least one of `X`
  and `Y` is zero, so `Nat.min X Y = 0`.
:::

:::dev
HIDE: BCP 21: I'm sure there is a more elegant proof of this!!
:::

```lean
theorem minimum_correct (a b : Nat) :
    (minimumDec a b).OuterTripleValid := by
  solution!
    sorry
```

:::dev
```
HIDE: LY: in this exercise, many end up writing the following implication
after the while line:

  {{ Z = min a b - min X Y /\ ... }} ->>
  {{ Z+1 = min a b - min (X-1) (Y-1) /\ ... }}

that is invalid if you interpret [-] pedantically as [sub : nat ->
nat -> nat], which takes nonnegative values only. But if we are
more generous and interpret these informal proofs in more intuitive
domains (Z, Q, or R), then these proofs look fine. I made the
former choice in my grading because I assume at this point they
should know to be careful around [-] with [nat].  BCP 21: Should be
fixed now that the proofs are formal! :-)
```
:::
:::::

::::::

## Exercise: Two Loops

:::suppressPreviousHeaderWhenTerse
:::

:::dev
HIDE: Taken from midterm 2, 2012
:::

::::::full
:::::exercise (rating := 3) (name := "two_loops")
Here is a pretty inefficient way of adding 3 numbers:

```display
X := 0;
Y := 0;
Z := c;
while X <> a do
  X := X + 1;
  Z := Z + 1
end;
while Y <> b do
  Y := Y + 1;
  Z := Z + 1
end
```

Show that it does what it should by completing the
following decorated program.

```lean
def twoLoopsDec (a b c : Nat) : Decorated where
  pre := ({{ True }})
  body := dcom {
    ->> {{ solution!({{ c = 0 + c ∧ 0 = 0 }}) }}
    X := 0 {{ solution!({{ c = X + c ∧ 0 = 0 }}) }};
    Y := 0 {{ solution!({{ c = X + c ∧ Y = 0 }}) }};
    Z := ~(Aexp.num c) {{
      solution!({{ Z = X + c ∧ Y = 0 }})
    }};
    (while (X ≠ ~(Aexp.num a)) do
      {{ solution!({{ (Z = X + c ∧ Y = 0) ∧ ¬ X = a }}) }}
      ->> {{ solution!({{ Z + 1 = X + 1 + c ∧ Y = 0 }}) }}
      X := X + 1 {{
        solution!({{ Z + 1 = X + c ∧ Y = 0 }})
      }};
      Z := Z + 1 {{ solution!({{ Z = X + c ∧ Y = 0 }}) }}
    end
      {{ solution!({{ (Z = X + c ∧ Y = 0) ∧ X = a }}) }}
    ->> {{ solution!({{ Z = a + Y + c }}) }});
    while (Y ≠ ~(Aexp.num b)) do
      {{ solution!({{ Z = a + Y + c ∧ ¬ Y = b }}) }}
      ->> {{ solution!({{ Z + 1 = a + Y + 1 + c }}) }}
      Y := Y + 1 {{ solution!({{ Z + 1 = a + Y + c }}) }};
      Z := Z + 1 {{ solution!({{ Z = a + Y + c }}) }}
    end
      {{ solution!({{ Z = a + Y + c ∧ Y = b }}) }}
    ->> {{ Z = a + b + c }}
  }

theorem two_loops (a b c : Nat) :
    (twoLoopsDec a b c).OuterTripleValid := by
  solution!
    sorry
```

:::dev "Michael Clarkson (clarksmr)" PotentialImprovement (year := 2020)
```
Again, the above isn't an IMP program, but a program
schema.  What about using the following instead?
[[
    {{ X = a /\ Y = b /\ Z = c }}
  I := 0;
  while I <> X do
    I := I + 1;
    Z := Z + 1
  end;
  I := 0;
  while I <> Y do
    I := I + 1;
    Z := Z + 1
  end
    {{ Z = a + b + c }}
]]

BCP 21: I'm not so bothered by using a program schema instead of a
program, but if the latter makes you happier I don't object.
```
:::

:::solution
```
Solution:
[[
    {{ True }} ->>
    {{ c = 0 + c /\ 0 = 0 }}
  X := 0;
    {{ c = X + c /\ 0 = 0 }}
  Y := 0;
    {{ c = X + c /\ Y = 0 }}
  Z := c;
    {{ Z = X + c /\ Y = 0 }}
  while X <> a do
      {{ Z = X + c /\ Y = 0 /\ X <> a }} ->>
      {{ Z + 1 = X + 1 + c /\ Y = 0 }}
    X := X + 1;
      {{ Z + 1 = X + c /\ Y = 0 }}
    Z := Z + 1
      {{ Z = X + c /\ Y = 0 }}
  end;
    {{ Z = X + c /\ Y = 0 /\ ~(X <> a) }} ->>
    {{ Z = a + Y + c }}
  while Y <> b do
      {{ Z = a + Y + c /\ Y <> b }} ->>
      {{ Z + 1 = a + Y + 1 + c }}
    Y := Y + 1;
      {{ Z + 1 = a + Y + c }}
    Z := Z + 1
      {{ Z = a + Y + c }}
  end
    {{ Z = a + Y + c /\ ~(Y <> b) }} ->>
    {{ Z = a + b + c }}
]]

Another solution follows.  It doesn't require carrying an additional
[Y = 0] conjunct through the first loop, but instead carries an
additional [ + Y] term through it.

[[
      {{ True }} ->>
        {{ c = 0 + 0 + c }}
    X := 0;
        {{ c = X + 0 + c }}
    Y := 0;
        {{ c = X + Y + c }}
    Z := c;
        {{ Z = X + Y + c }}
    while X <> a do
        {{ Z = X + Y + c /\ X <> a }} ->>
        {{ Z + 1 = (X + 1) + Y + c }}
      X := X + 1;
        {{ Z + 1 = X + Y + c }}
      Z := Z + 1
        {{ Z = X + Y + c }}
    end;
      {{ Z = X + Y + c /\ ~(X <> a) }} ->>
      {{ Z = a + Y + c }}
    while Y <> b do
        {{ Z = a + Y + c /\ (Y <> b) }} ->>
        {{ Z + 1 = a + (Y + 1) + c }}
      Y := Y + 1;
        {{ Z + 1 = a + Y + c }}
      Z := Z + 1
        {{ Z = a + Y + c }}
    end
      {{ Z = a + Y + c /\ ~(Y <> b) }} ->>
      {{ Z = a + b + c }}
]]
```
:::
:::::

::::::

## Exercise: Power Series

:::suppressPreviousHeaderWhenTerse
:::

:::dev "Michael Clarkson (clarksmr)" BeforeNextRelease (year := 2020)
```
This is again a program schema rather than a program.  Why not...
[[
      {{ True }}
    X := 0;
    Y := 1;
    Z := 1;
    while X <> W do
      Z := 2 * Z;
      Y := Y + Z;
      X := X + 1
    end
      {{ Y = 2 ^ (W + 1) - 1 }}
]]
   ...?

   BCP 21: Ditto my response above.  IMO this is not a problem.
```
:::

::::::full
:::::exercise (rating := 4) (name := "dpow2") (optional := Yes)
Here is a program that computes the series:
`1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1`

```display
X := 0;
Y := 1;
Z := 1;
while X <> m do
  Z := 2 * Z;
  Y := Y + Z;
  X := X + 1
end
```

Turn this into a decorated program and prove it correct.

```lean
def pow2 : Nat → Nat
  | 0 => 1
  | Nat.succ n => 2 * pow2 n

def dpow2Dec (n : Nat) : Decorated where
  pre := ({{ True }})
  body := dcom {
    ->> {{ solution!({{
      1 = pow2 (0 + 1) - 1 ∧ 1 = pow2 0
    }}) }}
    X := 0 {{
      solution!({{ 1 = pow2 (X + 1) - 1 ∧ 1 = pow2 X }})
    }};
    Y := 1 {{
      solution!({{ Y = pow2 (X + 1) - 1 ∧ 1 = pow2 X }})
    }};
    Z := 1 {{
      solution!({{ Y = pow2 (X + 1) - 1 ∧ Z = pow2 X }})
    }};
    while (X ≠ ~(Aexp.num n)) do
      {{ solution!({{
        (Y = pow2 (X + 1) - 1 ∧ Z = pow2 X) ∧ ¬ X = n
      }}) }}
      ->> {{ solution!({{
        Y + 2 * Z = pow2 (X + 2) - 1 ∧
        2 * Z = pow2 (X + 1)
      }}) }}
      Z := 2 * Z {{
        solution!({{
          Y + Z = pow2 (X + 2) - 1 ∧ Z = pow2 (X + 1)
        }})
      }};
      Y := Y + Z {{
        solution!({{
          Y = pow2 (X + 2) - 1 ∧ Z = pow2 (X + 1)
        }})
      }};
      X := X + 1 {{
        solution!({{
          Y = pow2 (X + 1) - 1 ∧ Z = pow2 X
        }})
      }}
    end
      {{ solution!({{
        (Y = pow2 (X + 1) - 1 ∧ Z = pow2 X) ∧ X = n
      }}) }}
    ->> {{ Y = pow2 (n + 1) - 1 }}
  }
```

Some lemmas that you may find useful...

```lean
theorem pow2_add_one (n : Nat) :
    pow2 (n + 1) = pow2 n + pow2 n := by
  sorry

theorem one_le_pow2 (n : Nat) : 1 ≤ pow2 n := by
  sorry
```

The main correctness theorem:

```lean
theorem dpow2_down_correct (n : Nat) :
    (dpow2Dec n).OuterTripleValid := by
  solution!
    sorry
```
:::::

:::dev PotentialImprovement
```
Another nice problem (from 09-final):

For each of the while programs below, we have provided a precondition
and postcondition. In the blank before each loop, fill in a loop invariant
that would allow us to annotate the rest of the program. Assume X, Y
and Z are distinct program variables.
(a)
(b)
    X := ANum n;
    Y := A1;
    while (BNot (!X === A0)) do (
         Y := !Y *** A2;
         X := !X --- A1
    )
Answer: Y = 2^(n-X)
    X := ANum x;
    Y := ANum y;
    Z := A0
{ True }
{ _______________________________________ }
{ Y = 2^n }
{ True }
                                   { _______________________________________ }
    while (BAnd (BNot (!X === A0)) (BNot (!Y === A0))) do (
         X := !X --- A1;
         Y := !Y --- A1;
         Z := !Z +++ A1
)
(where min is the mathematical "minimum" function)
Answer: Z = min(x,y) - min(X,Y)
```
:::

:::dev
```
HIDE: Another (very) good exercise from 09-mid2 -- just needs typeset

The notion of weakest precondition has a natural dual : given a
precondition and a command, we can ask what is the strongest
postcondition of the command with respect to the
precondition. Formally, we can define it like this:

Q is the strongest postcondition of c for P if:

(a) {{P}} c {{Q}}, and

(b) if Q′ is an assertion such that {{P}}c{{Q′}},
    then Q st implies Q′ st, for all states st.

Q is the strongest (most difficult to satisfy) assertion that is
guaranteed to hold after c if P holds before. For example, the
strongest postcondition of the command skip with respect to the
precondition Y = 1 is Y = 1. Similarly, the postcondition in...

         {{ Y = y }}
           if !Y === A0 then X := A0 else Y := !Y *** A2
         {{ (Y = y = X = 0) ∨ (Y = 2*y ∧ y <> 0) }}

...is the strongest one.

Complete each of the following Hoare triples with the strongest
postcondition for the given command and precondition.

(a) {{Y=1}} X:=!Y+++A1 {{?}}
(b) {{True}} X:=A5 {{?}}
(c) {{ True }} skip {{ ? }}
(d) {{ True }} while true do skip {{ ? }}
(e) {{ X = x ∧ Y = y }}
    while BNot (!X === A0) do (
                    Y := !Y +++ A2;
                    X := !X --- A1
                  )
    {{ ? }}
```
:::

:::::exercise (rating := 2) (name := "fib_eqn") (level := Advanced) (optional := Yes)
The Fibonacci function is characterized by the equations

```display
fib 0 = 1
fib 1 = 1
fib (n + 2) = fib (n + 1) + fib n
```

This recurrence can be defined structurally in Lean as follows:

```lean
def fib : Nat → Nat
  | 0 => 1
  | Nat.succ 0 => 1
  | Nat.succ (Nat.succ n) => fib (Nat.succ n) + fib n
```

Prove that `fib` satisfies the following equation.  You will need this
as a lemma in the next exercise.

```lean
theorem fib_eqn (n : Nat) (h : n > 0) :
    fib n + fib (Nat.pred n) = fib (1 + n) := by
  solution!
    sorry
```
:::::

:::::exercise (rating := 4) (name := "fib") (level := Advanced) (optional := Yes)
The following Imp program leaves the value of `fib n` in the
variable `Y` when it terminates:

```display
X := 1;
Y := 1;
Z := 1;
while X <> 1 + n do
  T := Z;
  Z := Z + Y;
  Y := T;
  X := 1 + X
end
```

Fill in the following definition of `dfib` and prove that it
satisfies this specification:

```display
{{ True }} dfib {{ Y = fib n }}
```

Ordinary Lean function application can be used in the assertions.
If all goes well, your proof will be very brief.

```lean
def T : Ident := "T"

def dfib (n : Nat) : Decorated where
  pre := ({{ True }})
  body :=
    let init : Assertion :=
      solution!(fun _ =>
        1 = fib 0 ∧ 1 = fib (Nat.pred 0) ∧ 1 > 0)
    let afterX : Assertion :=
      solution!(fun st =>
        1 = fib st[X] ∧
        1 = fib (Nat.pred st[X]) ∧ st[X] > 0)
    let afterY : Assertion :=
      solution!(fun st =>
        1 = fib st[X] ∧
        st[Y] = fib (Nat.pred st[X]) ∧ st[X] > 0)
    let inv : Assertion :=
      solution!(fun st =>
        st[Z] = fib st[X] ∧
        st[Y] = fib (Nat.pred st[X]) ∧ st[X] > 0)
    let guardedInv : Assertion :=
      solution!(fun st =>
        st[Z] = fib st[X] ∧ st[Y] = fib (Nat.pred st[X]) ∧
        st[X] > 0 ∧ st[X] ≠ 1 + n)
    let bodyPre : Assertion :=
      solution!(fun st =>
        st[Z] + st[Y] = fib (1 + st[X]) ∧
        st[Z] = fib (Nat.pred (1 + st[X])) ∧ 1 + st[X] > 0)
    let afterT : Assertion :=
      solution!(fun st =>
        st[Z] + st[Y] = fib (1 + st[X]) ∧
        st[T] = fib (Nat.pred (1 + st[X])) ∧ 1 + st[X] > 0)
    let afterZ : Assertion :=
      solution!(fun st =>
        st[Z] = fib (1 + st[X]) ∧
        st[T] = fib (Nat.pred (1 + st[X])) ∧ 1 + st[X] > 0)
    let afterYBody : Assertion :=
      solution!(fun st =>
        st[Z] = fib (1 + st[X]) ∧
        st[Y] = fib (Nat.pred (1 + st[X])) ∧ 1 + st[X] > 0)
    let exit : Assertion :=
      solution!(fun st =>
        st[Z] = fib st[X] ∧ st[Y] = fib (Nat.pred st[X]) ∧
        st[X] > 0 ∧ st[X] = 1 + n)
    dcom {
      ->> {{ init }}
      X := 1 {{ afterX }};
      Y := 1 {{ afterY }};
      Z := 1 {{ inv }};
      while (X ≠ ~(Aexp.num (1 + n))) do
        {{ guardedInv }}
        ->> {{ bodyPre }}
        T := Z {{ afterT }};
        Z := Z + Y {{ afterZ }};
        Y := T {{ afterYBody }};
        X := 1 + X {{ inv }}
      end
        {{ exit }}
      ->> {{ Y = fib n }}
    }

theorem dfib_correct (n : Nat) :
    (dfib n).OuterTripleValid := by
  solution!
    sorry
```
:::::

::::::

::::hide
```
/- LATER: some potential additional examples and exercises;
sort them out at some point -/

/- ### Euclid's Greatest Common Divisor (GCD) Algorithm -/

/- LATER: CH: this might make a good advanced/optional
exercise. But what exactly can we ask the students to do?
Translating from informal to formal is trivial, and the only
hard to prove part are the 3 lemmas, which I didn't prove either
since they have nothing to do with Hoare logics -/

/- RECALL: The greatest common divisor (GCD) of two numbers [m] and
    [n], written [gcd m n], is the largest number that evenly divides
    both [m] and [n].

    SOME USEFUL FACTS:
    - If y1>y2 then gcd y1 y2 = gcd (y1-y2) y2
    - If y1<y2 then gcd y1 y2 = gcd y1 (y2-y1)
    - gcd n n = n

    Euclid's algorithm for calculating GCDs:
[[
    {{ X = m /\ Y = n }}
  while X <> Y do
    if Y <= X
      then
         X := X - Y
      else
         Y := Y - X
    end
  end
    {{ X = gcd m n }}
]]

    Informal decorated program:
[[
    {{ X = m /\ Y = n }} ->>
    {{ gcd m n = gcd X Y }}
  while X <> Y do
      {{ gcd m n = gcd X Y /\ X<>Y }}
    if Y <= X
      then
          {{ gcd m n = gcd X Y /\ X<>Y /\ Y<=X }} ->>
          {{ gcd m n = gcd (X-Y) Y }}
        X := X - Y
          {{ gcd m n = gcd X Y }}
      else
          {{ gcd m n = gcd X Y /\ X<>Y /\ ~(Y<=X) }} ->>
          {{ gcd m n = gcd X (Y-X) }}
        Y := Y - X
          {{ gcd m n = gcd X Y }}
    end
  end
    {{ gcd m n = gcd X Y /\ ~(X<>Y) }} ->>
    {{ gcd m n = gcd X Y /\ X=Y }} ->>
    {{ gcd m n = X }}
]]

    Formal decorated program: -/

/- LATER: Fix the concrete syntax, if we ever uncomment this! -/
Print gcd. (* this actually uses Euclid's algorithm internally;
              the more efficient version with mod not minus *)

Definition gcd_dec (m n:nat) : decorated :=
  <{
    {{ X = m /\ Y = n }} ->>
    {{ #gcd m n = #gcd X Y }}
  while BNot (BEq (AId X) (AId Y)) do
      {{ #gcd m n = #gcd X Y /\ X <> Y }}
    if (Y <= X)
      then
          {{ #gcd m n = #gcd X Y
                       /\ X <> Y /\  Y <= X }} ->>
          {{ #gcd m n = #gcd (X - Y) Y }}
        X := AMinus (AId X) (AId Y)
          {{ #gcd m n = #gcd X Y }}
      else

      {{ #gcd m n = #gcd X Y /\
                        X<> Y /\ ~(Y<=X) }} ->>
          {{ #gcd m n = #gcd X (Y - X) }}
        Y := AMinus (AId Y) (AId X)
          {{ #gcd m n = #gcd X Y }}
    end
      {{ #gcd m n = #gcd X Y }}
  end
    {{ #gcd m n = #gcd X Y /\ ~(X <> Y) }} ->>
    {{ #gcd m n = #gcd X Y /\ X =  Y }} ->>
    {{ #gcd m n =  X }} }>.

Lemma gcd_eq : forall n, gcd n n = n.
Proof.
  apply Nat.gcd_diag.
Qed.

Lemma gcd_gt1 : forall y1 y2,
  y1 > y2 ->
  gcd y1 y2 = gcd (y1 - y2) y2.
Proof.
  intros.
  rewrite Nat.gcd_comm.
  rewrite <- Nat.gcd_sub_diag_r.
  - apply Nat.gcd_comm.
  - lia.
Qed.

Lemma gcd_gt2 : forall y1 y2,
  y1 < y2 ->
  gcd y1 y2 = gcd y1 (y2 - y1).
Proof.
  intros.
  rewrite Nat.gcd_sub_diag_r; auto.
  lia.
Qed.

Theorem gcd_correct : forall m n,
  outer_triple_valid (gcd_dec m n).
Proof. verify.
  - (* 1 *) rewrite H. apply gcd_gt1. lia.
  - (* 2 *) rewrite H. apply gcd_gt2. lia.
  - (* 3 *) rewrite H. apply gcd_eq.
Qed.

/- ---------------------------------------------- -/
/- Absurdly slow multiplication -/

/- PROGRAM AND SPEC:

  { X = m } ->>
Z := 0;
while X <> 0 do
  W := n;
  while W <> 0 do
    Z := Z + 1;
    W := W - 1
  end;
  X := X - 1
end
  { Z = m * n }

DECORATED PROGRAM:

  { X = m } ->>
  { 0 = (m-X) * n /\ X<=m }
Z := 0;
  { Z = (m-X) * n /\ X<=m }
while X <> 0 do
    { Z = (m-X) * n /\ X<=m /\ X<>0 } ->>
    { Z = (m-X) * n + (n-n) /\ X<=m }
  W := n;
    { Z = (m-X) * n + (n-W) /\ X<=m /\ W<=n }
  while W <> 0 do
      { Z = (m-X) * n + (n-W) /\ X<=m /\ W<=n /\ W<>0 } ->>
      { Z + 1 = (m-X) * n + (n-W) + 1 /\ X<=m /\ W-1<=n /\ W<>0 } ->>
      { Z + 1 = (m-X) * n + (n-(W-1)) /\ X<=m /\ W-1<=n }
    Z := Z + 1;
      { Z = (m-X) * n + (n-(W-1)) /\ X<=m /\ W-1<=n }
    W := W - 1
      { Z = (m-X) * n + (n-W) /\ X<=m /\ W<=n }
  end;
    { Z = (m-X) * n + (n-W) /\ X<=m /\ W<=n /\ ~(W<>0) } ->>
    { Z = (m-X) * n + n /\ X<=m } ->>
    { Z = ((m-X)+1) * n /\ X<=m } ->>
    { Z = (m-(X-1)) * n /\ X<=m }
  X := X - 1
    { Z = (m-X) * n /\ X<=m }
end
  { Z = (m-X) * n /\ X<=m /\ ~(X<>0) } ->>
  { Z = (m-X) * n /\ X=0 } ->>
  { Z = m * n } -/

/- LATER: From 2009 final

Give the weakest precondition for each of the following commands.
(Use the informal notation for assertions rather than Rocq notation,
i.e., write X = 5, not fun st => st X = 5.)
(a) {{ ? }} X := (ANum 5) {{ X = 6 }}
Answer: False
(b) {{ ? }}
testif (BLe (AId X) (AId Y))
then skip
else Z := (AId Y); Y := (AId X); X := (AId Z)
{{ X <= Y }}
Answer: True
(c) {{ ? }} while BNot (BEq (AId Y) (ANum 5)) do Y := APlus (AId Y) (ANum 1) {{ Y = 5 }}
Answer: True
(d) {{ ? }} while BEq (AId X) (ANum 0) do Y := (ANum 1) {{ Y = 5 }}
Answer: X=0 \/ Y=5

--------------------

For each of the while programs below, we have provided a precondition
and postcondition. In the blank before each loop, in an invariant that
would allow us to annotate the rest of the program. Assume X, Y and Z
are distinct program variables.
(a) { True }
X := ANum n;
Y := (ANum 1);
{ _______________________________________ }
while (BNot (BEq (AId X) (ANum 0))) do (
Y := AMult (AId Y) (ANum 2);
X := AMinus (AId X) (ANum 1)
)
{ Y = 2^n }
Answer: Y = 2^(n-X)
(b) { True }
X := ANum m;
Y := ANum n;
Z := (ANum 0);
{ _______________________________________ }
while (BAnd (BNot (BEq (AId X) (ANum 0))) (BNot (BEq (AId Y) (ANum 0)))) do (
X := AMinus (AId X) (ANum 1);
Y := AMinus (AId Y) (ANum 1);
Z := APlus (AId Z) (ANum 1)
)
{ Z = min(m,n) }
(where min is the mathematical minimum function)
Answer: Z = min(m,n) - min(X,Y) -/
```
::::

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2021)
This exercise should really be expanded into its
own whole section.  Moreover, there is a proposal to make the
decorations in Hoare look more like the decorations earlier in the
present chapter.  All three should be aligned.
:::

::::::full
:::::exercise (rating := 5) (name := "improve_dcom") (level := Advanced) (optional := Yes)
The formal decorated programs defined above are intended
to look as similar as possible to the informal ones defined
earlier.  If we drop this requirement, we can eliminate almost all
annotations, just requiring final postconditions and loop
invariants to be provided explicitly.  Do this — i.e., define a
new version of `DCom` with as few annotations as possible and adapt
the rest of the formal development leading up to the
`verification_correct` theorem.

:::instructors
The syntax in the solution below follows the command and
decorated-command templates.
:::

```lean
namespace SparseAnnotations

-- SOLUTION
/- (This solution also allows optional post-condition
assertions at any point, since these are quite useful in
practice when debugging the results of automated VC
solvers.) -/

inductive DCom where
  | skip
  | seq (first second : DCom)
  | asgn (x : Ident) (a : Aexp)
  | cond (b : Bexp) (thenBranch elseBranch : DCom)
  | whileDo (b : Bexp) (invariant : Assertion) (body : DCom)
  | assert (assertion : Assertion)

structure Decorated where
  pre : Assertion
  body : DCom
  post : Assertion

declare_syntax_cat sparse_dcom

syntax:max "(" sparse_dcom ")" : sparse_dcom
syntax:max "skip" : sparse_dcom
syntax:max ident " := " imp_aexp : sparse_dcom
syntax:20 sparse_dcom:21 ";" ppLine
  sparse_dcom:20 : sparse_dcom
syntax:max "if " "(" imp_bexp ")" ppHardSpace "then" ppLine
  sparse_dcom ppLine "else" ppLine sparse_dcom ppLine
  "end" : sparse_dcom
syntax:max "while " "(" imp_bexp ")" ppHardSpace "do" ppLine
  "{{" term "}}" ppLine sparse_dcom ppLine
  "end" : sparse_dcom
syntax:max "assert" " {{" term "}}" : sparse_dcom

syntax:min "sdcom" ppHardSpace "{" ppLine
  sparse_dcom ppDedent(ppLine "}") : term

macro_rules
  | `(sdcom { ($body:sparse_dcom) }) =>
      `(sdcom { $body })
  | `(sdcom { skip }) =>
      `(DCom.skip)
  | `(sdcom { $x:ident := $a:imp_aexp }) =>
      `(DCom.asgn $x (aexp { $a }))
  | `(sdcom { $d1:sparse_dcom; $d2:sparse_dcom }) =>
      `(DCom.seq (sdcom { $d1 }) (sdcom { $d2 }))
  | `(sdcom {
        if ($b:imp_bexp) then
          $d1:sparse_dcom
        else
          $d2:sparse_dcom
        end
      }) =>
      `(DCom.cond (bexp { $b })
        (sdcom { $d1 }) (sdcom { $d2 }))
  | `(sdcom {
        while ($b:imp_bexp) do
          {{ $inv }}
          $body:sparse_dcom
        end
      }) =>
      `(DCom.whileDo (bexp { $b }) ({{ $inv }})
        (sdcom { $body }))
  | `(sdcom { assert {{ $p }} }) =>
      `(DCom.assert ({{ $p }}))

/- Here's how our decorated programs look now: -/

def decWhile : Decorated where
  pre := ({{ True }})
  body := sdcom {
    while (X ≠ 0) do
      {{ True }}
      X := X - 1
    end
  }
  post := ({{ X = 0 }})

/- It is easy to go from a `DCom` to a `Com` by erasing all
annotations. -/

def DCom.erase (d : DCom) : Com :=
  match d with
  | .skip => .skip
  | .seq d1 d2 => .seq d1.erase d2.erase
  | .asgn x a => .asgn x a
  | .cond b d1 d2 => .cond b d1.erase d2.erase
  | .whileDo b _ body => .whileDo b body.erase
  | .assert _ => .skip

/- We can express what it means for a decorated program to
be correct as follows: -/

def Decorated.OuterTripleValid (dec : Decorated) : Prop :=
  ValidHoareTriple dec.pre dec.body.erase dec.post

/- This VC generator is derived from Mike Gordon,
"Background reading on Hoare Logic,"
https://www.cl.cam.ac.uk/archive/mjcg/HL/Notes/Notes.pdf -/

def DCom.awp (post : Assertion) (d : DCom) : Assertion :=
  match d with
  | .skip => post
  | .seq d1 d2 => d1.awp (d2.awp post)
  | .asgn x a => {{ post [x ↦ ~a] }}
  | .cond b d1 d2 =>
      fun st =>
        (b.eval st = true ∧ d1.awp post st) ∨
        (b.eval st = false ∧ d2.awp post st)
  | .whileDo _ invariant _ => invariant
  | .assert assertion => fun st => assertion st ∧ post st

def DCom.VerificationConditions
    (post : Assertion) (d : DCom) : Prop :=
  match d with
  | .seq d1 d2 =>
      d1.VerificationConditions (d2.awp post) ∧
      d2.VerificationConditions post
  | .cond _ d1 d2 =>
      d1.VerificationConditions post ∧
      d2.VerificationConditions post
  | .whileDo b invariant body =>
      (∀ st, invariant st ∧ b.eval st ≠ true → post st) ∧
      (∀ st, invariant st ∧ b.eval st = true →
        body.awp invariant st) ∧
      body.VerificationConditions invariant
  | _ => True

theorem vc_correct (d : DCom) (post : Assertion)
    (hvc : d.VerificationConditions post) :
    ValidHoareTriple (d.awp post) d.erase post := by
  sorry

def Decorated.VerificationConditions
    (dec : Decorated) : Prop :=
  (dec.pre ->> dec.body.awp dec.post) ∧
  dec.body.VerificationConditions dec.post

theorem verification_correct (dec : Decorated)
    (hvc : dec.VerificationConditions) :
    dec.OuterTripleValid := by
  sorry

/- Let's redo all the examples to date. -/
/- LATER: Fix indentation. -/
theorem dec_while_correct :
    decWhile.OuterTripleValid := by
  sorry

def swapDec (m n : Nat) : Decorated where
  pre := ({{ X = m ∧ Y = n }})
  body := sdcom {
    X := X + Y;
    Y := X - Y;
    X := X - Y
  }
  post := ({{ X = n ∧ Y = m }})

theorem swap_correct (m n : Nat) :
    (swapDec m n).OuterTripleValid := by
  sorry

def ifMinusDec : Decorated where
  pre := ({{ True }})
  body := sdcom {
    if (X ≤ Y) then
      Z := Y - X
    else
      Z := X - Y
    end
  }
  post := ({{ Z + X = Y ∨ Z + Y = X }})

theorem if_minus_correct :
    ifMinusDec.OuterTripleValid := by
  sorry

def ifMinusPlusDec : Decorated where
  pre := ({{ True }})
  body := sdcom {
    if (X ≤ Y) then
      Z := Y - X
    else
      Y := X + Z
    end
  }
  post := ({{ Y = X + Z }})

theorem if_minus_plus_correct :
    ifMinusPlusDec.OuterTripleValid := by
  sorry

def divModDec (a b : Nat) : Decorated where
  pre := ({{ True }})
  body := sdcom {
    X := ~(Aexp.num a);
    Y := 0;
    while (~(Aexp.num b) ≤ X) do
      {{ b * Y + X = a }}
      X := X - ~(Aexp.num b);
      Y := Y + 1
    end
  }
  post := ({{ b * Y + X = a ∧ X < b }})

theorem div_mod_outer_triple_valid (a b : Nat) :
    (divModDec a b).OuterTripleValid := by
  sorry

def parityDec (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body := sdcom {
    while (2 ≤ X) do
      {{ parity X = parity m }}
      X := X - 2
    end
  }
  post := ({{ X = parity m }})

theorem parity_outer_triple_valid (m : Nat) :
    (parityDec m).OuterTripleValid := by
  sorry

def sqrtDec (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body := sdcom {
    Z := 0;
    while ((Z + 1) * (Z + 1) ≤ X) do
      {{ X = m ∧ Z * Z ≤ m }}
      Z := Z + 1
    end
  }
  post := ({{ Z * Z ≤ m ∧ m < (Z + 1) * (Z + 1) }})

theorem sqrt_correct (m : Nat) :
    (sqrtDec m).OuterTripleValid := by
  sorry

def squareDec (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body := sdcom {
    Y := X;
    Z := 0;
    while (Y ≠ 0) do
      {{ Z + X * Y = m * m }}
      Z := Z + X;
      Y := Y - 1
    end
  }
  post := ({{ Z = m * m }})

theorem square_outer_triple_valid (m : Nat) :
    (squareDec m).OuterTripleValid := by
  sorry

def squareDec' (n : Nat) : Decorated where
  pre := ({{ True }})
  body := sdcom {
    X := ~(Aexp.num n);
    Y := X;
    Z := 0;
    while (Y ≠ 0) do
      {{ Z = X * (X - Y) ∧ X = n ∧ Y ≤ X }}
      Z := Z + X;
      Y := Y - 1
    end
  }
  post := ({{ Z = n * n }})

theorem square_dec'_correct (n : Nat) :
    (squareDec' n).OuterTripleValid := by
  sorry

def squareSimplerDec (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body := sdcom {
    Y := 0;
    Z := 0;
    while (Y ≠ X) do
      {{ Z = Y * m ∧ X = m }}
      Z := Z + X;
      Y := Y + 1
    end
  }
  post := ({{ Z = m * m }})

theorem square_simpler_outer_triple_valid (m : Nat) :
    (squareSimplerDec m).OuterTripleValid := by
  sorry

def twoLoopsDec (a b c : Nat) : Decorated where
  pre := ({{ True }})
  body := sdcom {
    X := 0;
    Y := 0;
    Z := ~(Aexp.num c);
    (while (X ≠ ~(Aexp.num a)) do
      {{ Z = X + c ∧ Y = 0 }}
      X := X + 1;
      Z := Z + 1
    end);
    while (Y ≠ ~(Aexp.num b)) do
      {{ Z = a + Y + c }}
      Y := Y + 1;
      Z := Z + 1
    end
  }
  post := ({{ Z = a + b + c }})

theorem two_loops_correct (a b c : Nat) :
    (twoLoopsDec a b c).OuterTripleValid := by
  sorry

def subtractSlowlyDec (m p : Nat) : Decorated where
  pre := ({{ X = m ∧ Z = p }})
  body := sdcom {
    while (X ≠ 0) do
      {{ Z - X = p - m }}
      Z := Z - 1;
      X := X - 1
    end
  }
  post := ({{ Z = p - m }})

theorem subtract_slowly_correct (m p : Nat) :
    (subtractSlowlyDec m p).OuterTripleValid := by
  sorry

def dpow2Down (n : Nat) : Decorated where
  pre := ({{ True }})
  body := sdcom {
    X := 0;
    Y := 1;
    Z := 1;
    while (X ≠ ~(Aexp.num n)) do
      {{ Y = pow2 (X + 1) - 1 ∧ Z = pow2 X }}
      Z := 2 * Z;
      Y := Y + Z;
      X := X + 1
    end
  }
  post := ({{ Y = pow2 (n + 1) - 1 }})

theorem dpow2_down_correct (n : Nat) :
    (dpow2Down n).OuterTripleValid := by
  sorry

def factorialDec (m : Nat) : Decorated where
  pre := ({{ X = m }})
  body := sdcom {
    Y := 1;
    while (X ≠ 0) do
      {{ Y * fact X = fact m }}
      Y := Y * X;
      X := X - 1
    end
  }
  post := ({{ Y = fact m }})

theorem factorial_outer_triple_valid (m : Nat) :
    (factorialDec m).OuterTripleValid := by
  sorry

def T : Ident := "T"

def dfib (n : Nat) : Decorated where
  pre := ({{ True }})
  body := sdcom {
    X := 1;
    Y := 1;
    Z := 1;
    while (X ≠ ~(Aexp.num (1 + n))) do
      {{ Z = fib X ∧ Y = fib (Nat.pred X) ∧ X > 0 }}
      T := Z;
      Z := Z + Y;
      Y := T;
      X := 1 + X
    end
  }
  post := ({{ Y = fib n }})

theorem dfib_correct (n : Nat) :
    (dfib n).OuterTripleValid := by
  sorry

-- END SOLUTION

end SparseAnnotations
```
:::::

::::::

# Weakest Preconditions (Optional)

:::dev
HIDE: BCP 21: We talked about moving this stuff to the HoareAsLogic
chapter to lighten this chapter, but it fits awkwardly there, so
I'm leaving it here.  It's optional anyway.  We might consider
assigning one of the exercises as advanced-only though.
:::

::::full
Some preconditions are more interesting than others.
For example, the Hoare triple

```display
{{ False }}  X := Y + 1  {{ X <= 5 }}
```

is _not_ very interesting: although it is perfectly valid, it
tells us nothing useful.  Since the precondition isn't
satisfied by any state, it doesn't describe any situations where
we can use the command `X := Y + 1` to achieve the postcondition
`X <= 5`.

By contrast,

```display
{{ Y <= 4 /\ Z = 0 }}  X := Y + 1 {{ X <= 5 }}
```

has a useful precondition: it tells us that, if we can somehow
create a situation in which we know that `Y <= 4 /\ Z = 0`, then
running this command will produce a state satisfying the
postcondition.  However, this precondition is not as useful as it
could be, because the `Z = 0` clause in the precondition actually
has nothing to do with the postcondition `X <= 5`.

The _most_ useful precondition for this command is this one:

```display
{{ Y <= 4 }}  X := Y + 1  {{ X <= 5 }}
```

The assertion `Y <= 4` is called the _weakest precondition_ of
`X := Y + 1` with respect to the postcondition `X <= 5`.
::::

:::terse
A useless (though valid) Hoare triple:

```display
{{ False }}  X := Y + 1  {{ X <= 5 }}
```

A better precondition:

```display
{{ Y <= 4 /\ Z = 0 }}  X := Y + 1 {{ X <= 5 }}
```

The _best_ precondition:

```display
{{ Y <= 4 }}  X := Y + 1  {{ X <= 5 }}
```
:::

Assertion `Y <= 4` is a _weakest precondition_ of command
`X := Y + 1` with respect to postcondition `X <= 5`.  Think of _weakest_
here as meaning "easiest to satisfy": a weakest precondition is
one that as many states as possible can satisfy.

:::slidebreak
:::

`P` is a weakest precondition of command `c` for postcondition `Q`
if

  - `P` is a precondition, that is, `{{P}} c {{Q}}`; and
  - `P` is at least as weak as all other preconditions, that is,
    if `{{P'}} c {{Q}}` then `P' ->> P`.

Note that weakest preconditions need not be unique.  For
example, `Y <= 4` was a weakest precondition above, but so are the
logically equivalent assertions `Y < 5`, `Y <= 2 * 2`, etc.
It is easy to show that any two weakest preconditions `P` and `P'`
of a command `c` with respect to postcondition `Q` are logically
equivalent; that is, `P <<->> P'`.

```lean
def IsWp (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ValidHoareTriple P c Q ∧
  ∀ P' : Assertion, ValidHoareTriple P' c Q → P' ->> P
```

:::slidebreak
:::

:::dev PotentialImprovement
Make a quiz based on this!
:::

:::::exercise (rating := 1) (name := "wp") (optional := Yes)
What are weakest preconditions of the following commands
for the following postconditions?

```display
1) {{ ? }}  skip  {{ X = 5 }}

2) {{ ? }}  X := Y + Z {{ X = 5 }}

3) {{ ? }}  X := Y  {{ X = Y }}

4) {{ ? }}
 if X = 0 then Y := Z + 1 else Y := W + 2 end
 {{ Y = 5 }}

5) {{ ? }}
 X := 5
 {{ X = 0 }}

6) {{ ? }}
 while true do X := 0 end
 {{ X = 0 }}
```

:::solution
```display
1) X = 5
2) Y + Z = 5
3) True
4) (X = 0 /\ Z = 4) \/ (X <> 0 /\ W = 3)
5) False
6) True
```
:::
:::::

:::dev PotentialImprovement
```
Another similar problem:

For each of the following Hoare triples, give a weakest precondition
that makes the triple valid.
(a)
    {{ ? }}
while Y <= X do
X := X - 1 end
{{ Y > X }}
    {{ ? }}
if X .> 3 then Z := X else Z := Y end
{{ Z = W }}
    {{ ? }}
while IsCons X do
  N := N + 1;
  X := Tail(X)
end
{{ X = [ ] ∧ N = length l }}

---------
And:

In the Imp program below, we have provided a precondition and
postcondition. In the blank before the loop, fill in an invariant
that would allow us to annotate the rest of the program.
X := n
Y := X
Z := 0
while Y <> 0 do
    Z := Z + X;
Y := Y - 1 end
{ True }
{ _____________________________________________ }
{ Z = n*n }
```
:::

::::::full
:::::exercise (rating := 3) (name := "is_wp") (level := Advanced) (optional := Yes)
Prove formally, using the definition of `ValidHoareTriple`, that `Y <= 4`
is indeed a weakest precondition of `X := Y + 1` with respect to
postcondition `X <= 5`.

:::dev PotentialImprovement
Rocq requires parentheses around the three arguments to `is_wp` here
to avoid parsing them as a Hoare triple. Lean's `IsWp` syntax has no
corresponding ambiguity, so the reader-facing parsing note does not
carry over.
:::

```lean
theorem is_wp_example :
    IsWp ({{ Y ≤ 4 }}) (imp {X := Y + 1})
      ({{ X ≤ 5 }}) := by
  solution!
    sorry
```
:::::

:::::exercise (rating := 2) (name := "hoare_asgn_weakest") (level := Advanced) (optional := Yes)
Show that the precondition in the rule `hoare_asgn` is in fact the
weakest precondition.

```lean
theorem hoare_asgn_weakest
    (Q : Assertion) (x : Ident) (a : Aexp) :
    IsWp ({{ Q [x ↦ ~a] }}) (imp {x := ~a}) Q := by
  solution!
    sorry
```

:::gradeTheorem 2 hoare_asgn_weakest
:::
:::::

:::::exercise (rating := 2) (name := "hoare_havoc_weakest") (level := Advanced) (optional := Yes)
Show that your `havoc_pre` function from the `himp_hoare` exercise
in the {ref "Hoare"}[Hoare] chapter returns a weakest precondition.

```lean
namespace Himp2

theorem hoare_havoc_weakest (P Q : Assertion) (x : Ident)
    (h : Himp.ValidHoareTriple P (Himp.Com.havoc x) Q) :
    P ->> Himp.havoc_pre x Q := by
  solution!
    sorry

end Himp2
```
:::::

::::::
