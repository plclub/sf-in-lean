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
powerful tools.

:::full
This includes the natural numbers from its standard library,
tactics which can search for lemmas from the standard library, namespaces for
organizing lemmas, and a new tactic, {tactic}`calc`,
which enables more readable and concise proofs.
:::

# More Powerful Natural Numbers

:::full
Until now, we have been working with our own custom natural numbers, using the
`Nat` type that we defined in {ref "Basics"}[Basics].

As you might have guessed, Lean has a built-in type of natural numbers, also called
{name}`Nat`, which is automatically imported into `.lean` files by default. Its definition
is essentially the same as our custom `Nat`, but it comes with a large library of useful theorems.
Programmers and mathematicians usually apply these _automatically_ rather than by writing out
{tactic}`rewrite` steps by hand. For example, here is a simple proof of equality using our
custom `Nat`s.
:::

:::terse
Whereas we performed manual {tactic}`rewrite` steps on our custom `Nat`s ...
:::

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

:::full
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
:::

:::terse
... we can simplify Lean's built-in {name}`Nat`s automatically.
:::

```lean
end OldNats
-- Now, we are using Lean's built-in natural numbers.
example : (2 * 2 : Nat) = 4 := by rfl
```

:::full
The annotation `: Nat` tells Lean that we are using its built-in {name}`Nat` type.
Definitions in the built-in {name}`Nat` library are not marked `@[irreducible]`, so we can
perform _automatic simplification_ of functions on natural numbers,
which is appropriate when their low-level behaviors are not the primary focus of proofs.
:::
Doing so is very helpful for large numbers — we would not want to write out
the hundreds or thousands of {tactic}`rewrite` steps needed for proving examples like the
following!

```lean
example : (2 * 3 + 4 * 5 : Nat) * 6 = 156 := by rfl
```

Of course, {tactic}`rfl` still can't close goals where the values of the terms are unknown.

```lean
example (n m : Nat) (h : n = m) : n = m := by
  -- `rfl` will not work here!
  -- First rewrite the goal with `h`; then the two sides are identical.
  rw [h]
```

From now on we will use the built-in {name}`Nat` type.
:::full
We will write `Nat.<theorem>` to reference Lean's version
of `<theorem>`; by convention, theorems about a type live in the namespace of
that type.
:::

# Searching for Standard Library Theorems

::::full
Because we
did not write or prove theorems for built-in {name}`Nat`s ourselves, we may not
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

::::full
```leanOutput exact?_add_comm
Try this:
  [apply] exact Nat.add_comm n m
```

If you are using the Lean extension in VS Code, the InfoView will
have a blue `[apply]` button that shows the suggested theorem to
close the goal. Alternatively, VS Code may show an inline suggestion
(lightbulb) button above the {tactic}`exact?`. You can click either of
these buttons to replace the occurrence of {tactic}`exact?` with the tactic
it found to complete the proof; idiomatic Lean should not contain
{tactic}`exact?` tactics (or any other `?` tactics) in the finished
versions of proofs.

The {tactic}`exact?` tactic is useful when we just need a single library theorem to get us over
the finish line, but it is not so helpful when we are deep in the middle of a proof
or wondering how to get started on one. Fortunately, there are other tactics
that can help.

The {tactic}`rw?` tactic searches for any theorems
that you could use to _rewrite_ (rather than _complete_) the current goal.
::::

::::terse
You can also use {tactic}`rw?` to look for theorems to rewrite by.
::::

```lean (name := rw?_add_comm)
example (n m : Nat) : n + m = m + n := by
  rw?
```

::::full
```leanOutput rw?_add_comm (allowDiff := 1)
Try this:
  [apply] rw [Nat.add_comm]
```

However, unlike {tactic}`exact?`, just because {tactic}`rw?` suggests
a theorem to you does not automatically imply that it will be useful.
In the example below, many of the theorems {tactic}`rw?` suggests
will not progress towards completing the proof; you will need to
carefully look through its suggestions to see which ones seem useful.
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

:::::full
We strongly recommend against blindly using {tactic}`rw?` and
accepting its suggestions without due consideration! You will find
this to be a slow and frustrating way to write proofs. Instead, we
suggest figuring out what you would like your next step to be,
conceptually, and then using {tactic}`rw?` to search for a theorem
that implements it. If no such theorem exists, you may need to prove it
yourself.

::::exercise (rating := 1) (name := "mul_three_beq")
Prove the following theorems about {name}`Nat`s.
You should not need induction;
find the theorems you need using {tactic}`rw?` and {tactic}`exact?`.

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
::::
:::::

# Structuring Proofs with {tactic}`calc`

In Lean proofs, long {tactic}`rw` chains are useful, but they are sometimes
hard to read because the intermediate goals are invisible.
::::full
Furthermore, sometimes we _know_ exactly how we want to manipulate the terms of a proof, but
don't want to have the tactics like {name}`Nat.add_comm` and
{name}`Nat.add_assoc` "guess" which subterms to rewrite.
::::

The {tactic}`calc` tactic writes down the intermediate goals of a proof, and
allows us to specify exactly which rewrite rules to apply at each step. It is designed
to mimic the style of proofs in mathematics textbooks, which will often look something like this:

```display
n + (m + k)
= (n + m) + k        ...   [by associativity of addition]
= (m + n) + k        ...   [by commutativity of addition]
= m + (n + k)        ...   [by associativity of addition]
```
::::full
Note how we can see each intermediate step of this proof when we
look at it this way. Let's look at how we might prove this theorem
(i.e., that `n + (m + k) = m + (n + k)`) in Lean.

First, a proof in the style we already know.
::::

```lean
example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]
```

Now, the same theorem written with {tactic}`calc`.
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

:::::full
Whereas before, the left-hand side of each equality in the
{tactic}`calc` tactic was repeated from the right-hand side of the
previous one, we can replace the left-hand side entirely with an `_`.
Now our Lean proof looks quite a bit like the textbook one we saw earlier!

::::exercise (rating := 1) (name := "succ_mul_succ")
Consider this proof, which uses {tactic}`rw`.
```lean
theorem succ_mul_succ (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]
```

Rewrite the proof using {tactic}`calc`.
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
::::
If you prefer {tactic}`rw` to {tactic}`calc`, that's fine! Each has particular
uses, and both will be tools in your ever-growing toolbox of tactics.
:::::

:::dev "Niklas Halonen (xhalo32)"
How to grade that `succ_mul_succ'` uses `calc` without cheating?
:::

# Unfolding definitions using {tactic}`rw`

Here are some definitions about {name}`Nat`s:

```lean
def addTwice (n : Nat) : Nat := n + n
def addThrice (n : Nat) : Nat := n + n + n
```

Suppose we wish to prove that `addThrice n` is equal to adding `n` to `addTwice n`.
We might hope to proceed by {tactic}`rfl`, but this doesn't work:

```lean +error (name := triple_error)
example (n : Nat) : (addThrice n) = n + (addTwice n) := by
  rfl
```

::::full
```leanOutput triple_error
Tactic `rfl` failed: The left-hand side
  addThrice n
is not definitionally equal to the right-hand side
  n + addTwice n

n✝ n : Nat
⊢ addThrice n = n + addTwice n
```
What happened?
::::
Consulting our definitions, what we are trying to prove amounts to
the following equation:

```display
(n + n) + n = n + (n + n)
```

These two things are not definitionally equal, so we cannot use {tactic}`rfl` alone.
::::full
A natural next step is to rewrite by {name}`Nat.add_assoc` so that {tactic}`rfl`
should work on the result.
::::
```lean +error (name := triple_comm_error)
example (n : Nat) : addThrice n = n + addTwice n := by
  rw [Nat.add_assoc]
```

::::full
This doesn't work either.

```leanOutput triple_comm_error
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?n + ?m + ?k
in the target expression
  addThrice n = n + addTwice n

n✝ n : Nat
⊢ addThrice n = n + addTwice n
```

The reason is that the expression in which we are trying to rewrite
{name}`Nat.add_assoc` isn't of the form `n + m + k` precisely; it is {lean}`addThrice n`.
::::
We need to unfold the underlying definitions of
{lean}`addThrice` and {lean}`addTwice` so that {tactic}`rw`, which only operates on syntax,
can see the addition.
We can do this using the {tactic}`rw` tactic.

```lean
example (n : Nat) : addThrice n = n + addTwice n := by
  -- `rw [addThrice]` unfolds `addThrice`, replacing it with its definition
  rw [addThrice]
  -- this likewise unfolds `addTwice`
  rw [addTwice]
  -- Now, proving our goal only requires associativity of additions
  rw [Nat.add_assoc]
```

:::::full
Since Lean does not unfold most definitions automatically, we use tactics
like {tactic}`rw` to do so selectively, in goals and hypotheses, in order to guide
how a proof is carried out.

::::exercise (rating := 1) (name := "rwUnfold")
Complete this proof, using {tactic}`rw` to unfold the definition of `addThrice` as appropriate.

```lean
theorem rwUnfold (n m : Nat) (h : m = n) : addThrice m = n + (n + n) := by
  solution!
    rw [h, addThrice, Nat.add_assoc]
```

:::gradeTheorem 1 rwUnfold
:::
::::
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
  -- use rw? to construct the proof
  workinclass!
    rw [Nat.mul_comm, Nat.mul_two, Nat.mul_two] at h
    exact h
```

::::full
With the ability to unfold definitions via rewriting, one may wonder why we need
simplification rules like `add_zero` and `add_succ`. As mentioned when motivating these
rules, they provide some engineering benefits: The rules tend to stay the same even
as definitions change, which helps avoid proof breakages. Avoiding such breakages
is particularly important with proofs using parts of Lean's standard library,
which are often implemented in ways that are very efficient but less friendly to proofs.
::::

::::terse
Unfolding should not be overused; simplification rules are (still) useful proof engineering.
::::

# Definitional Simplification with {tactic}`dsimp`

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

# A First Automation Tactic: {tactic}`repeat`

When {tactic}`rw` unfolds a definition, it does so one instance at time.
Thus each occurrence of a definition needs its own rewrite.

```lean
example (n m k : Nat) (h : square n + square m + square k = 0) :
    n * n + m * m + k * k = 0 := by
  rw [square, square, square] at h
  exact h
```

::::full
We have previously seen the same issue with lemmas like `add_zero`, leading to situations
in which we have to rewrite multiple times in a row.
To make this situation a bit better, we can use the {tactic}`repeat` tactic combinator,
which takes a tactic as its argument and repeats it as many times as it can.
::::

::::terse
Use {tactic}`repeat` to repeat a tactic multiple times.
::::

```lean
example (n m k : Nat) (h : square n + square m + square k = 0) :
    n * n + m * m + k * k = 0 := by
  repeat rw [square] at h
  exact h
```

::::full
The {tactic}`repeat` tactic is a simple source of proof
automation in Lean, as is the use of simplification via {tactic}`dsimp`
and {tactic}`rfl`. Lean's full tactic library, and tactic-writing
metaprogramming language, offer much more.
The {ref "Automation"}[Automation] chapter will
introduce the powerful, and commonly used, automated tactic {tactic}`simp`,
which can sometimes solve complex goals by itself.
We'll also talk about other tactic combinators like {tactic}`repeat`.

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

::::terse
There is much more to say about automation, covered in the
{ref "Automation"}[Automation] chapter.
::::

# Redefining Functions and Lemmas over Nats

::::full
Now that we've switched to using Lean's standard library, we can
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

:::::full
::::exercise (rating := 2) (name := "even_succ")
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
::::
:::::

We reprove here for Lean's {name}`Nat` some theorems about
{name}`Nat.even` and {name}`Nat.double`, which we had previously
proven for our custom {name}`NatPlayground.Nat`.

```lean
theorem Nat.even_zero : even 0 = true := by rfl
theorem Nat.double_zero : double 0 = 0 := by rfl
theorem Nat.double_succ (n : Nat) : (n + 1).double = n.double + 2 := by rfl
```

:::::full
::::exercise (rating := 2) (name := "double_add")
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
::::

::::exercise (rating := 2) (name := "double_mul")
```lean
theorem Nat.double_mul (n : Nat) : n.double = 2 * n := by
  solution!
    rw [double_add, Nat.two_mul]
```

:::gradeTheorem 2 Nat.double_mul
:::
::::

In the remainder of the book, we use Lean's built-in natural numbers everywhere.
We also recommend using `rw?` and `exact?` to search for lemmas
(though these should not appear in finished proofs).

With these tools in hand, we
can begin to prove properties about more sophisticated forms of data, beginning with
{ref "Lists"}`Lists`.
:::::
