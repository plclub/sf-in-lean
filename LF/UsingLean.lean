import SFLMeta

import LF.Basics
import LF.Induction

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "UsingLean: Using the Full Power of a Proof Assistant" =>
%%%
tag := "UsingLean"
htmlSplit := .never
file := some "UsingLean"
%%%

:::ignore
```lean -show
variable (n : Nat)
```
:::

:::instructors
This chapter introduces more idiomatic design patterns in Lean via
the standard library's natural numbers, and what Lean in the wild
might more resemble. Notable new tactics are {tactic}`calc`.
It is relatively short, and should take about 30 minutes to cover.
:::

In this chapter, we will learn to write more idiomatic Lean using its more
powerful tools. This includes the natural numbers from its standard library,
tactics which can search for lemmas from the standard library, namespaces for
organizing lemmas, and a new tactic, {tactic}`calc`,
which enables more readable and concise proofs.

# More Powerful Natural Numbers

Until now, we have been working with our own custom natural numbers, using the
`Nat` type that we defined in {ref "Basics"}[Basics].

However, Lean has a built-in type of natural numbers, which is more powerful
and comes with many useful features. They are very slightly different from our
custom `Nat`, but these differences are mostly superficial. The built-in
natural numbers are defined in the `Init` module, which is automatically
imported by Lean. We will refer to them as {name}`Nat` as well.

In Lean, programmers and mathematicians don't re-prove the basic properties of
natural numbers from scratch, nor do they tend to write out {tactic}`rewrite` steps
for basic properties of natural numbers by hand.

Previously, we did computation like this...

```lean
section OldNats
open NatPlayground.Nat
example : (two * two : NatPlayground.Nat) = four := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  rewrite [mul_succ, mul_succ, mul_zero]
  rewrite [add_succ, add_succ, add_zero]
  rewrite [add_succ, add_succ, add_zero]
  rfl
```

We made Lean enforce this pedagogical style using `attribute [irreducible]`
on definitions like {name}`mul`
and {name}`add`. This forced us to write proofs using tactics like {tactic}`rw`
rather than simplifying definitions.

This approach is useful in a textbook for understanding the structure of
natural numbers and for providing early practice with writing proofs. But it
is also tedious in the long term.

Instead of doing this, programmers and mathematicians use the built-in
{name}`Nat` and the powerful features of Lean to _automatically_ prove
properties about natural numbers and to compute with them.

```lean
end OldNats
-- Now, we are using Lean's built-in natural numbers.
example : (3 * 3 : Nat) = 9 := by rfl
```

The annotation `: Nat` tells Lean that we are using its built-in {name}`Nat` type.
In fact, from now on, we will use the built-in {name}`Nat` type and its powerful
features, writing `Nat.<theorem>` to reference Lean's version
of `<theorem>`. (By convention, theorems about a type live in the namespace of
that type, hence the need for the `Nat.` prefix.)

Definitions in the built-in {name}`Nat` library are _not_ marked `@[irreducible]`. This lets us use
more powerful _automatic simplification_ of functions on natural numbers,
which is appropriate when their low-level behaviors are not the primary focus of proofs.
This will be the case going forward.

## The {tactic}`rfl` Tactic and Computation with {name}`Nat`

With Lean's {name}`Nat`, much of the computation happens automatically,
and {tactic}`rfl` suffices to close any equality of computation on literals.

```lean
example : (2 * 3 + 4 * 5 : Nat) * 6 = 156 := by rfl
```

This quickly becomes necessary, as natural numbers quickly get large!

Of course, {tactic}`rfl` can't close more complicated goals where the values
of the terms are unknown.

```lean
example (n m : Nat) (h : n = m) : n = m := by
  -- `rfl` will not work here!
  -- First rewrite the goal with `h`; then the two sides are identical.
  rw [h]
```

We will continue to show more powerful tools for manipulating
the context and goal of a proof to bring them closer to what can be
solved with {tactic}`rfl`.

# Using the Standard Library

::::full
As part of using Lean's standard {name}`Nat` type, we will also begin
using theorems about {name}`Nat`s from the standard library. Because we
did not write or prove these theorems ourselves, we may not
know (or remember) all the available theorems.

Lean provides a few ways to search through the standard library to find theorems
that may be useful during a particular proof. The first way is the {tactic}`exact?`
tactic. This tactic searches the standard library for a theorem that can be applied,
along with the hypotheses in the context, to exactly close the current goal.
::::

::::terse
Use the {tactic}`exact?` tactic to search for relevant theorems in the standard library.
::::

```lean (name := exact?_add_comm)
example (n m : Nat) : n + m = m + n := by
  exact?
```

```leanOutput exact?_add_comm
Try this:
  [apply] exact Nat.add_comm n m
```

::::full
If you are using the Lean extension in VS Code, the InfoView will
have a blue `[apply]` button that shows the suggested theorem to
close the goal. Alternatively, VS Code may show an inline suggestion
(lightbulb) button above the {tactic}`exact?`. You can click either of
these buttons to replace the occurrence of {tactic}`exact?` with the tactic
it found to complete the proof; idiomatic Lean should not contain
{tactic}`exact?` tactics (or any other `?` tactics) in the finished
versions of proofs.

The {tactic}`exact?` tactic is useful when we just need a single library theorem to get us over
the finish line of a proof, but it is not so helpful when we are deep in the middle of a proof
or are wondering how to get started on one. Fortunately, there are other tactics
that can help in these cases.

The {tactic}`rw?` tactic works like {tactic}`exact?`, except that it searches for any theorems
that you could use to rewrite the current goal.
::::

::::terse
You can also use {tactic}`rw?` to look for theorems to rewrite by.
::::

```lean (name := rw?_add_comm)
example (n m : Nat) : n + m = m + n := by
  rw?
```

```leanOutput rw?_add_comm (allowDiff := 1)
Try this:
  [apply] rw [Nat.add_comm]
```

::::full
However, unlike {tactic}`exact?`, just because {tactic}`rw?` suggests
a theorem to you does not automatically imply that it will be useful.
In the example below, many of the theorems {tactic}`rw?` suggests
will not progress towards completing the proof; you will need to
carefully look through its suggestions to see which ones seem useful.
We strongly recommend against blindly using {tactic}`rw?` and
accepting its suggestions without due consideration! You will find
this a very slow and frustrating way to write proofs. Instead, we
suggest figuring out what you would like your next step to be,
conceptually, and then using {tactic}`rw?` to search for a theorem
that implements it. If no such theorem exists, that may be a sign
that you need to prove it yourself.
::::

:::terse
Just because {tactic}`rw?` suggests a theorem does not mean that it will be useful;
choose carefully from its suggestions (if at all).
:::

```lean +error
example (n m k : Nat) :
   (n + m) + k = m + (n + k) := by
  -- lots of suggestions to look through here!
  rw?
```

Prove the following theorems about {name}`Nat`s.
You should not need induction for any of these;
you can find the theorems you need using {tactic}`rw?` and {tactic}`exact?`.

```lean
theorem mul_three (n : Nat) :
    3 * n = n + n + n := by
  solution!
    rw [Nat.add_one_mul, Nat.two_mul]
```

:::gradeTheorem 1 mul_three
:::

```lean
theorem mul_three_beq (n : Nat) :
    (3 * n == n + n + n) = true := by
  solution!
    rw [Nat.beq_eq_true_eq]
    exact mul_three n
```

:::gradeTheorem 1 mul_three_beq
:::

# Structuring Proofs with {tactic}`calc`

:::suppressPreviousHeaderWhenTerse
:::

::::full
In Lean proofs, long {tactic}`rw` chains are useful, but they are sometimes
hard to read because the intermediate goals are invisible. Furthermore,
sometimes we _know_ exactly how we want to manipulate the terms of a proof, but
don't want to have the tactics like {name}`Nat.add_comm` and
{name}`Nat.add_assoc` "guess" which subterms to rewrite.

The {tactic}`calc` tactic writes down the intermediate goals of a proof, and
allows us to specify exactly which rewrite rules to apply at each step. It is designed
to mimic the style of proofs in mathematics textbooks, which will often look something like this:

```display
n + (m + k)
= (n + m) + k        ...   [by associativity of addition]
= (m + n) + k        ...   [by commutativity of addition]
= m + (n + k)        ...   [by associativity of addition]
```

Note how we can see each intermediate step of this proof when we
look at it this way. Let's look at how we might prove this theorem
(i.e., that `n + (m + k) = m + (n + k)`) in Lean.

First, a proof in the style we already know.
::::

::::terse
The {tactic}`calc` can be used to make long chains of rewrites easier to follow:
::::

```lean
example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]
```

Here we present the same theorem, written with {tactic}`calc`.
Note how each intermediate goal is visible in the source.

```lean
example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  calc n + (m + k) /- one side of the goal is the argument to `calc`...
       ... and each subsequent line is a transformation, with a tactic. -/
    n + (m + k) = (n + m) + k := by rw [Nat.add_assoc]
    (n + m) + k = (m + n) + k := by rw [Nat.add_comm n m]
    /- once a line matches the other side of the equality in the main goal
       (in this case `m + (n + k)`), the calc tactic succeeds. -/
    (m + n) + k = m + (n + k) := by rw [Nat.add_assoc]
```

We can also write the proof like this to be a bit more concise:

```lean
example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  calc n + (m + k)
    _ = (n + m) + k := by rw [Nat.add_assoc]
    _ = (m + n) + k := by rw [Nat.add_comm n m]
    _ = m + (n + k) := by rw [Nat.add_assoc]
```

Whereas before, the left-hand side of each equality in the
{tactic}`calc` tactic was repeated from the right-hand side of the
previous one, we can replace the left-hand side entirely with an `_`.
Now our Lean proof looks quite a bit like the textbook one we saw earlier!

:::dev "Niklas Halonen (xhalo32)"
How to grade that `succ_mul_succ'` uses `calc` without cheating?
:::

:::::exercise (rating := 1) (name := "succ_mul_succ")
```lean
theorem succ_mul_succ (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]
```

Given this proof with {tactic}`rw`, rewrite it with {tactic}`calc`.

```lean
theorem succ_mul_succ' (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  solution!
    calc (n + 1) * (m + 1)
      _ = n * (m + 1) + 1 * (m + 1) := by rw [Nat.add_mul]
      _ = n * (m + 1) + (m + 1)     := by rw [Nat.one_mul]
      _ = (n * m + n * 1) + (m + 1) := by rw [Nat.mul_add]
      _ = (n * m + n) + (m + 1)     := by rw [Nat.mul_one]
      _ = n * m + n + m + 1         := by rw [← Nat.add_assoc]
```

If you prefer {tactic}`rw` to {tactic}`calc`, that's fine! Each has particular
uses, and both will be tools in your ever-growing toolbox of tactics.
:::::


# Unfolding definitions with {tactic}`rw`

Here are some definitions about {name}`Nat`s:

```lean
def addTwice (n : Nat) : Nat := n + n
def addThrice (n : Nat) : Nat := n + n + n
```

A simple example of something we might wish to prove about these two things
is that adding `n` to `addTwice n` is the same as `addThrice n`. One might
hope to proceed by {tactic}`rfl`, but this doesn't quite work:

```lean +error (name := triple_error)
example (n : Nat) : addThrice n = n + addTwice n := by
  rfl
```

```leanOutput triple_error
Tactic `rfl` failed: The left-hand side
  addThrice n
is not definitionally equal to the right-hand side
  n + addTwice n

n✝ n : Nat
⊢ addThrice n = n + addTwice n
```

What happened here? If we are careful with our parentheses here,
we can write the goal we'd like to prove as `(addThrice n) = n + (addTwice n)`.
Unfolding definitions, we can see that this is equivalent to:

```display
n + n + n = n + (n + n)
```

which, when we are more explicit about parenthesization, is equivalent to:

```display
(n + n) + n = n + (n + n)
```

These two things are not definitionally equal, so we cannot use {tactic}`rfl` here, hence
our error from earlier. The next thing we might want to try is rewriting by {name}`Nat.add_assoc`;
which would give us a syntactically equal equality as our goal:


```lean +error (name := triple_comm_error)
example (n : Nat) : addThrice n = n + addTwice n := by
  rw [Nat.add_assoc]
```

```leanOutput triple_comm_error
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?n + ?m + ?k
in the target expression
  addThrice n = n + addTwice n

n✝ n : Nat
⊢ addThrice n = n + addTwice n
```

But again we encounter an error! The expression in which we are trying to rewrite
{name}`Nat.add_assoc` isn't of the form `n + m + k`, so we can't proceed. What then, should we do?
To proceed here, we need to reveal to Lean the underlying definitions of `addThrice` and `addTwice`,
so that {tactic}`rw`, which only operates on syntax, can see the addition.
We can do this by rewriting by those definitions:

```lean
example (n : Nat) : addThrice n = n + addTwice n := by
  -- `rw [addThrice]` unfolds `addThrice`, replacing it with its definition
  rw [addThrice]
  -- this likewise unfolds `addTwice`
  rw [addTwice]
  -- Now, proving our goal only requires associativity of additions
  rw [Nat.add_assoc]
```

Unfolding definitions in goals and hypotheses like this let us guide Lean into
simplifying expressions and allowing it to rewrite by more theorems in more places.

:::::exercise (rating := 2) (name := "rwUnfold")
Complete this proof, using {tactic}`rw` to unfold the definition of `addThrice` as appropriate.

```lean
theorem rwUnfold (n m : Nat) (h : m = n) : addThrice m = n + (n + n) := by
  solution!
    rw [h, addThrice, Nat.add_assoc]
```

:::gradeTheorem 2 rwUnfold
:::
:::::

Rewriting can also be used in places where {tactic}`rfl` can't, like hypotheses.

```lean
def square (n : Nat) : Nat := n * n

example (n : Nat) (h : square n = 16) : n * n = 16 := by
  rw [square] at h
  exact h
```

Aside: `rw? at h` also works on hypotheses:

```lean
example (n m : Nat) (h : 2 * n = m * 2) : n + n = m + m := by
  rw [Nat.mul_comm, Nat.mul_two, Nat.mul_two] at h
  exact h
```

But {tactic}`rw` rewrites only one instance of a definition at a time.
When a hypothesis or goal mentions the same function applied to different
arguments, each one needs its own rewrite.

```lean
example (n m k : Nat) (h : square n + square m + square k = 0) :
    n * n + m * m + k * k = 0 := by
  rw [square, square, square] at h
  exact h
```

::::full
We have previously seen the same issue with lemmas, leading to situations
in which we have to rewrite multiple times in a row by lemmas like `add_zero`.
To make this situation a bit better, we can use the {tactic}`repeat` tactic combinator,
which takes a tactic as its argument and repeats it as many times as it can:
::::

::::terse
Use {tactic}`repeat` to repeat a tactic multiple times:
::::

```lean
example (n m k : Nat) (h : square n + square m + square k = 0) :
    n * n + m * m + k * k = 0 := by
  repeat rw [square] at h
  exact h
```

::::full
With the ability to unfold definitions via rewriting, one may wonder why we need
characterizing lemmas anymore. Despite the power of unfolding, we encourage you to stick
to use characterizing lemmas wherever possible: it's better engineering practice and
help proofs stay robust against changes to definitions. This is
particularly important when dealing with definitions in Lean's standard library,
which are often implemented in ways that are more efficient, but less friendly to proofs.
Sticking to characterizing lemmas for these definitions will make your proofs simpler and
more elegant.
::::

## Definitional Simplification

::::full
Sometimes when you unfold a definition your hypothesis or goal may become hard to understand.
When that happens, it can be useful to simplify it.
To apply simplifications similar to those that {tactic}`rfl` does,
but without also trying to close an equality goal,
you can use the tactic `dsimp only` or `dsimp only at h`.
::::

::::terse
`dsimp only` can perform basic simplification:
::::

```lean
example : (fun x => x + 0) n = n := by
  dsimp only -- applies the function to its argument
  rw [Nat.add_zero]
```

If we did not simplify here before attempting to rewrite, we would get an error:

```lean +error (name := dsimp_error)
example : (fun x => x + 0) n = n := by
  rw [Nat.add_zero]
```

```leanOutput dsimp_error
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?n + 0
in the target expression
  (fun x => x + 0) n = n

n : Nat
⊢ (fun x => x + 0) n = n
```

## A First Step Towards Automation

:::suppressPreviousHeaderWhenTerse
:::

::::full
In the section on
{ref "Logical-Foundations--Basics___-Functional-Programming-in-Lean--Proof-by-Rewriting--Irreducibility___-Rewriting___-and-Proof-Engineering"}[Irreducibility, Rewriting, and Proof Engineering]
in {ref "Basics"}[Basics], we hinted at introducing more automated
tactics than {tactic}`rw` for writing proofs. By using Lean's
computation engine to automatically simplify terms
when using tactics like {tactic}`rfl` or after unfolding via {tactic}`rw`,
we allow Lean to introduce a small amount of its own automatic reasoning.

Later in the {ref "Automation"}[Automation] chapter, we will
introduce the more powerful automated tactic {tactic}`simp`,
which can sometimes solve complex goals by itself and is
accordingly extremely common in real-world Lean developments.
We'll also talk more about tactic combinators like {tactic}`repeat`.

But, using these tools now does not help (in fact, it hurts!) the
process of learning logical reasoning, formal theorem proving, and
Lean. Additionally, real Lean programmers are careful when using
automation: it can hurt the readability of a proof, and real-world
Lean is often used to _communicate_ a result as much as to prove
it. We will continue to use only simple tactics and {tactic}`rw`,
for most of this volume so that you have a firm
grasp of both the logic behind the proofs you are writing and the
ways to structure those proofs to make your logic clear.
::::

# Redefining Functions and Lemmas over Nats

::::full
Now that we've switched over to using Lean's standard library, we can
redefine some of the functions from the last few chapters on {name}`Nat`s.
Note that, for the built-in {name}`Nat` type, the patterns {lean}`0` and
{lean}`n + 1` correspond to {name}`Nat.zero` and {lean}`Nat.succ n`.
Likewise, the pattern {lean}`n + 2` is equivalent to {lean}`n + 1 + 1`.

Prove some of these theorems using the techniques we've discussed this chapter.
::::

::::terse
Let's redefine some functions on Lean's {name}`Nat`s and prove some theorems about them.
::::

```lean
def Nat.even (n : Nat) :=
  match n with
  | 0     => true
  | 1     => false
  | n + 2 => even n

def Nat.odd (n : Nat) := !(even n)

theorem Nat.odd_def (n : Nat) : n.odd = !(n.even) := rfl

def Nat.minusTwo (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | 1      => 0
  | n' + 2 => n'

def Nat.double (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => double n' + 2
```

::::full
Note that we defined these functions in the {name}`Nat` namespace;
Lean's naming conventions advise that functions on a type should be defined in that type's
namespace in almost all circumstances.

When we define functions this way,
something interesting happens to the way Lean's InfoView prints them. Take a look at
the InfoView inside the proof of this theorem before the {tactic}`rfl` tactic:
::::

::::terse
Defining functions in the {name}`Nat` namespace changes how they print:
::::

```lean
theorem Nat.even_add_three (n : Nat) : even (n + 3) = even (n + 1) := by
  rfl
```

::::full
Instead of printing the goal the way we wrote it in the theorem statement, Lean
prints {lean}`(n + 3).even = (n + 1).even`! This is an example of Lean's _field notation_,
whereby Lean prints functions inside the namespace of a type _after_ their first argument,
separated by a `.`. At first glance, this may appear similar to how object-oriented methods work,
but it's really just a syntactic variation on the normal function-application style
we've seen so far. That is, {lean}`Nat.even n` and {lean}`n.even` are just different ways to write
the exact same term.

In previous chapters we disabled this notation by putting `set_option pp.fieldNotation false`
at the top of each file, but from now on we will leave it enabled, since field notation
is recommended in idiomatic Lean developments.

As an example, observe the difference in how Lean prints the goal in the following two examples:
::::

::::terse
This printing style is called _field notation_ and can be enabled or disabled with the
`pp.fieldNotation` option.
::::

```lean
set_option pp.fieldNotation false

example (n : Nat) : Nat.double (n + 0) = Nat.double n := by
  rfl

set_option pp.fieldNotation true

example (n : Nat) : Nat.double (n + 0) = Nat.double n := by
  rfl
```

:::::exercise (rating := 2) (name := "even_succ") (optional := true)
One inconvenient aspect of our definition of `even n` is the
recursive call on `n'` when `n = n' + 2`. This makes proofs about `even n`
harder when done by induction on `n`, since we may need an
induction hypothesis about `n' + 2`, while induction just gives us one about `n' + 1`. The following lemma proves `even (n + 1)` flips the parity, which gives an
alternative characterization that works better with induction. We'll see uses of
this theorem in {ref "Lists"}[Lists].

```lean
theorem Nat.even_succ (n : Nat) :
    (n + 1).even = !(n.even) := by
  solution!
    induction n with
    | zero =>
      rfl
    | succ n' ih =>
      rw [even, ih, Bool.not_not]
```

:::gradeTheorem 2 Nat.even_succ
:::
:::::

We reprove here for Lean's {name}`Nat` some theorems about
{name}`Nat.even` and {name}`Nat.double`, which we had previously
proven for our custom {name}`NatPlayground.Nat`.

```lean
theorem Nat.even_zero : even 0 = true := by rfl
theorem Nat.double_zero : double 0 = 0 := by rfl
theorem Nat.double_succ (n : Nat) : (n + 1).double = n.double + 2 := by rfl
```

:::::exercise (rating := 2) (name := "double_add")
```lean
theorem Nat.double_add (n : Nat) : n.double = n + n := by
  solution!
    induction n with
    | zero =>
      rw [double_zero]
    | succ n' ih =>
      rw [double_succ, ih, succ_add n' (n' + 1), add_succ n' n']
```

:::gradeTheorem 2 Nat.double_add
:::
:::::

:::::exercise (rating := 2) (name := "double_mul")
```lean
theorem Nat.double_mul (n : Nat) : n.double = 2 * n := by
  solution!
    rw [double_add, Nat.two_mul]
```
:::::

:::gradeTheorem 2 Nat.double_mul
:::

In the remainder of the book, we use Lean's built-in natural numbers everywhere.
We also recommend using `rw?` and `exact?` to search for lemmas
(though these should not appear in finished proofs).

With these tools in hand, we
can begin to prove properties about more sophisticated forms of data, beginning with
{ref "Lists"}`Lists`.
