prelude
import VersoManual
import VersoManual.InlineLean
import Illuminate
import SFLMeta.Bnf
import SFLMeta.DisplayMath
import SFLMeta.Ignore
import SFLMeta.Save
import SFLMeta.Comment
import SFLMeta.Epigraph
import SFLMeta.Exercise
import SFLMeta.Grade
import SFLMeta.Hide
import SFLMeta.Instructors
import SFLMeta.Quiz
import SFLMeta.SlideBreak
import SFLMeta.Solution
import SFLMeta.Terse
import LF.Basics
open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "Induction: Proof by Induction" =>
%%%
tag := "Induction"
htmlSplit := .never
file := some "Induction"
%%%

:::dev SOONER
```
Readers might expect us to add eqn:H annotations to uses of
induction, but this changes the shape of the IH in a nasty way! :-(
We should at least comment.  (BCP: Is this still relevant in Lean?)

SOONER: We should also consider adding more examples to clarify
the concepts introduced in this chapter. This could help in
reinforcing the understanding of induction principles.

LATER: In 3/22, MRC and BCP discussed "inlining" IndPrinciples
into earlier chapters, thus eliminating it as a chapter. This
chapter, Induction, is the first place a change would occur.  We
would present [nat_ind] here. Then in Lists/Poly we'd present
[list_ind], and the rest would go in IndProp and ProofObjects. The
main wrinkle is that we'd need to introduce [apply] here instead of
in Tactics if we want to preserve the presentation. The discussion
is preserved here: https://github.com/DeepSpec/sfdev/pull/471.

LATER: Now that we've added Steve's nice late-policy exercise in
Basics.v, the assignment for that chapter is probably hard enough.  Now
what about this chapter?  Can/should we make it a notch or two
harder?
```
:::

# Separate Compilation

:::dev "Benjamin Pierce (bcpierce00)"
```
This section will need some tidying and rewriting...
```
:::

:::terse
Lean will first need to compile `Basics.lean` so it can
be imported here -- detailed instructions are in the full version
of this chapter...
:::

::::full
Before getting started on this chapter, we need to import
all of our definitions from the previous chapter:
::::

```importBlock
import LF.Basics
```

::::full
For this `import` to work, Lean needs to be able to find a
compiled version of the previous chapter (`Basics.lean`).  This
compiled version, called `Basics.olean`, is analogous to the
`.class` files compiled from `.java` source files and the `.o`
files compiled from `.c` files.

When using Lake (Lean's build system), the `lakefile.lean` file
specifies dependencies and build configuration.  Running `lake build`
will compile all necessary files in the correct order.

If you are using VS Code with the Lean 4 extension, compilation
happens automatically in the background.  When you open a file, the
extension will compile its dependencies as needed.

Troubleshooting:

 - If you get complaints about missing imports, make sure you have
   run `lake build` from the project root directory at least once.

 - If you modify `Basics.lean`, VS Code will automatically
   recompile it when you save.  You may need to reopen this file
   or wait for recompilation to finish.

 - If you get errors that seem inconsistent with the source, try
   running `lake clean` followed by `lake build` to recompile
   everything from scratch.

 - If you are using the Lean 4 extension for VS Code,
   you can also restart the extension on the current file
   via the `Restart File` button in the InfoView. The extension
   will often prompt you do this if you change things upstream
   in the dependency tree.
::::

```lean
namespace NatPlayground.Nat
```

# Review

::::quiz
To prove the following theorem, which tactics will we need besides
`intro` and `rfl`?  (A) none, (B) `rewrite`, (C) `cases`, (D) both
`rewrite` and `cases`, or (E) can't be done with the tactics we've seen.

```display
    theorem review1 : (true || false) = true
```

:::answer
```
/- review1 -/
theorem review1 : (true || false) = true := by rfl
```
:::
::::

::::quiz
What about the next one?

```display
    theorem review2 : ∀ b, (true || b) = true
```

Which tactics do we need besides `intro` and `rfl`?  (A)
none (B) `rewrite`, (C) `cases`, (D) both `rewrite` and `cases`,
or (E) can't be done with the tactics we've seen.

:::answer
```
/- review2 -/
theorem review2 : ∀ b : Bool, (true || b) = true := by
  intro b
  rfl
```
:::
::::

::::quiz
What if we change the order of the arguments of `||`?

```display
    theorem review3 : ∀ b, (b || true) = true
```

Which tactics do we need besides `intro` and `rfl`?  (A)
none (B) `rewrite`, (C) `cases`, (D) both `rewrite` and `cases`,
or (E) can't be done with the tactics we've seen.

:::answer
```
/- review3 -/
theorem review3 : ∀ b : Bool, (b || true) = true := by
  intro b
  cases b with
  | false => rfl
  | true  => rfl
```
:::
::::

::::quiz
What about this one?  (Recall that in Lean, `Nat.add` recurses on the _second_
argument: `n + zero = n` by definition, and `n + (m + 1) = (n + m) + 1` by
definition.)

```display
    theorem review4 : ∀ n : Nat, n + zero = n
```

(A) none, (B) `rewrite`, (C) `cases`, (D) both `rewrite` and `cases`, or (E)
can't be done with the tactics we've seen.

:::answer
```
/- review4 -/
theorem review4 : ∀ n : Nat, n + zero = n := by
  intro n
  rewrite [add_zero]
  rfl
```
:::
::::

::::quiz
What about this?

```display
    theorem review5 : ∀ n : Nat, zero + n = n
```

(A) none, (B) `rewrite`, (C) `cases`, (D) both `rewrite` and `cases`,
or (E) can't be done with the tactics we've seen.

:::answer
```
/- review5 -/
/-
  This one CANNOT be proved by rfl, cases, or rewriting alone --
  it needs induction!  (We'll see why below.)
-/
```
:::
::::

:::dev "Daniel Sainati (dsainati1)" TODO
```
We use this theorem later,
   so let's make it into a review exercise here
```
:::

Prove the following theorem, using theorems from Basics:

```lean
theorem succ_eq_add_one : ∀ n : Nat, succ n = n + one := by
  solution!
    intro n
    rewrite [one_eq_succ_zero, add_succ, add_zero]
    rfl
```

## Proof by Induction

::::full
  We defined `add` to recurse on its _second_ argument:

```
  def add (n : Nat) (m : Nat) : Nat :=
    match m with
    | zero => n
    | succ m' => succ (add n m')
```

  This means `n + zero` reduces to `n` by definition, but `zero + n` does
  _not_.

  In `add_zero`, we were able to prove that `zero` is a neutral element
  for `+` on the _right_ using just `rfl`:

```
  theorem add_zero : forall (n : Nat), n + zero = n := by
    intro n
    rfl
```

But the proof that it is also a neutral element on the _left_
   can't be done in the same simple way.  Just applying `rfl` doesn't
   work, since the `n` in `zero + n` is an arbitrary unknown number, so
   the `match` in the definition of `+` can't be simplified.
::::

::::terse
But the proof that it is also a neutral element on the
   _left_ gets stuck...
::::

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∀ n : Nat, zero + n = n := by
  intro n
  -- `rfl` doesn't work here!
  sorry
```

:::slidebreak
:::

And reasoning by cases using `cases n` doesn't get us much
further: the branch of the case analysis where we assume `n = zero`
goes through just fine, but in the branch where `n = n' + 1` for
some `n'` we get stuck in exactly the same way.

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∀ n : Nat, zero + n = n := by
  intro n
  cases n with
  | zero => /- n = zero -/
    rewrite [add_zero]
    rfl
    -- so far so good...
  | succ n' =>   /- n = succ n' -/
    -- ...but we're stuck on zero + n'
    sorry
```

::::full
We could use `cases n'` to get a bit further, but,
since `n` can be arbitrarily large, we'll never get all the way
there if we just go on like this.
::::

:::slidebreak
:::

::::full
To prove interesting facts about numbers, lists, and other
inductively defined sets, we often need a more powerful reasoning
principle: _induction_.

Recall (from a discrete math course, probably) the _principle of
induction over natural numbers_: If `P(n)` is some proposition
involving a natural number `n` and we want to show that `P` holds for
all numbers `n`, we can reason like this:
- show that `P(zero)` holds;
- show that, for any `n'`, if `P(n')` holds, then so does
`P(succ n')`;
- conclude that `P(n)` holds for all `n`.

In Lean, the steps are the same: we begin with the goal of proving
`P(n)` for all `n` and use the `induction` tactic to break it down
into two separate subgoals: one where we must show `P(zero)` and another
where we must show `P(n') → P(succ n')`.  Here's how this works for
the theorem at hand...
::::

::::terse
We need a bigger hammer: the _principle of induction_ over
natural numbers...

- If `P(n)` is some proposition involving a natural number `n`,
and we want to show that `P` holds for _all_ numbers, we can
reason like this:

- show that `P(zero)` holds
- show that, if `P(n')` holds, then so does `P(succ n')`
- conclude that `P(n)` holds for all `n`.

For example...
::::

:::slidebreak
:::

```lean
theorem zero_add : ∀ n : Nat, zero + n = n := by
  intro n
  induction n with
  | zero => /- n = zero -/
    rewrite [add_zero]
    rfl
  | succ n' ih => /- n = succ n' -/
    /-
      Goal: zero + (succ n') = succ n'
      We can rewrite `zero + (succ n')` to `succ (zero + n')`.
      Then we can rewrite with the induction hypothesis.
    -/
    rewrite [add_succ, ih]
    rfl
```

::::full
Like `cases`, the `induction` tactic takes a `with` clause
that specifies the names of the variables to be introduced in the
subgoals.  Since there are two subgoals (for `zero` and `succ`),
the `with` clause has two branches.

In the first subgoal, `n` is replaced by `zero`. The goal becomes
`zero + zero = zero`, which follows by `rfl`.

In the second subgoal, `n` is replaced by `succ n'`, and the
induction hypothesis `ih : zero + n' = n'` is added to the context.
The goal becomes `zero + (succ n') = succ n'`. `add_succ` tells
us that `a + (succ b) = succ (a + b)`, so `rewrite [add_succ]`
transforms the goal to `succ (zero + n') = succ n'`. Then `rewrite [ih]`
rewrites `zero + n'` to `n'`, and the goal becomes `succ n' = succ n'`,
which closes with reflexivity.
::::

:::slidebreak
:::

::::terse
Let's try this one together:
::::

```lean
theorem beq_self : ∀ n : Nat,
    (n == n) = true := by
  workinclass!
    intro n
    induction n with
    | zero =>
      rewrite [zero_zero_beq_true]
      rfl
    | succ n' ih =>
      rewrite [succ_succ_beq]
      exact ih
```

:::dev "Roger Burtonpatel (rogerburtonpatel)"
```
We need to make sure this section below is true! It won't be once we switch
     to the indexed style.
```
:::

::::full
Up until this point, we have been explicitly writing out all the parameters
to theorems with ∀s, which makes us introduce them explicitly with `intro` before we
can use them. A more Lean-idiomatic way is to write them on the left side of the `:`
in the theorem statement, which introduces them automatically. So, the statement
of `beq_self` that we just wrote could also be:

`theorem beq_self (n : Nat) : (n == n) = true := by ...`

When written this way, we don't need to `intro n` at the start of the proof, as
`n` will already be in the context when we begin. We will prefer this style going forward.
::::

::::::full
:::::exercise (rating := 2) (name := "basic_induction")
Prove the following using induction. You might need previously
proven results.

```lean
theorem zero_mul (n : Nat) :
    zero * n = zero := by
  solution!
    induction n with
    | zero =>
      rewrite [mul_zero]
      rfl
    | succ n' ih =>
      rewrite [mul_succ, ih, add_zero]
      rfl
```

:::grade
```
GRADE_THEOREM 0.5: mul_zero_l
```
:::

```lean
theorem succ_add (n m : Nat) :
    (succ n) + m = succ (n + m) := by
  solution!
    induction m
    case zero =>
      rewrite [add_zero, add_zero]
      rfl
    case succ m' ih =>
      rewrite [add_succ, add_succ, ih]
      rfl
```

:::grade
```
GRADE_THEOREM 0.5: succ_add
```
:::
:::::

::::::

:::slidebreak
:::

::::terse
Here's another related fact about addition, which we'll
need later.  (The proof is left as an exercise.)
::::

```lean
theorem add_comm (n m : Nat) :
    n + m = m + n := by
  solution!
    induction m with
    | zero =>
      rewrite [add_zero, zero_add]
      rfl
    | succ m' ih =>
      rewrite [add_succ, ih, succ_add]
      rfl
```

:::grade
```
GRADE_THEOREM 0.5: add_comm
```
:::

```lean
theorem add_assoc (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  solution!
    induction p with
    | zero =>
      rewrite [add_zero, add_zero]
      rfl
    | succ p' ih =>
      rewrite [add_succ, add_succ, add_succ, ih]
      rfl
```

:::grade
```
GRADE_THEOREM 0.5: add_assoc
```
:::

:::::exercise (rating := 2) (name := "double_plus")
Consider the following function, which doubles its argument:

:::dev TODO
```
Rule rewrite

BCP: What is "ASSUME HIDDEN"??
ASSUME HIDDEN
```
:::

```lean
def double (n : Nat) : Nat :=
  match n with
  | zero    => zero
  | succ n' => succ (succ (double n'))
```


```lean
theorem double_zero : double zero = zero := by rfl
theorem double_succ : ∀ n, double (succ n) = succ (succ (double n)) := by
  intro n; rfl

attribute [irreducible] double
```

END ASSUME

:::dev "Benjamin Pierce (bcpierce00)"
```
We need better typesetting for displays like the following ones:
```
:::
:::::

## Tip: the `rw` tactic

  As you've probably noticed, a common pattern in Lean proofs is `rewrite [...]`
  followed by `rfl`. There is a tactic that combines these two steps: `rw [...]`
  will automatically close the goal if the rewrite makes the goal true by
  definition. For example, instead of writing

     `rewrite [double_zero]; rfl`

  We could write this:

    `rw [double_zero]`

  Using `rw` in your proofs is optional, but it will save you time
  (and is better style).

::::full
(One small caveat: `rw [...]` only performs a quick reflexivity check
after rewriting; it does not unfold every definition. So, in rare
cases, `rw` may leave a goal that is still solved immediately by `rfl`.)

```lean
def aliasOfTwo := two

example (n : Nat) (h : n = aliasOfTwo) : n = two := by
  rw [h]
  /- The remaining goal is `aliasOfTwo = two`. -/
  rfl
```
::::

::::terse
If `rw` leaves a goal that looks definitionally true, try adding `rfl`
after it.
::::

Use induction to prove this simple fact about `double`.
   Experiment with using `rw` instead of `rewrite` as well.

```lean
theorem double_add (n : Nat) : double n = n + n := by
  solution!
    induction n with
    | zero       => rw [add_zero, double_zero]
    | succ n' ih => rw [double_succ, ih, add_succ, succ_add]
```

:::::exercise (rating := 2) (name := "beq_refl")
The following theorem relates the computational equality `beq` on
`Nat` with the definitional equality `=` on `Bool`.

```lean
theorem beq_refl (n : Nat) :
    (n == n) = true := by
  solution!
    induction n with
    | zero       => rw [zero_zero_beq_true]
    | succ n' ih => rw [succ_succ_beq, ih]
```
:::::

::::hide
```
  Note: we might expect a similar property to hold on
  UNequal [nat]'s:
     Theorem beq_n_n' : forall n n' : nat,
          n ≠ n' ->
          n =? n' = false.
  But it will be a while before we get to terms with what
  [n ≠ n'] really means...
```
::::

::::::full
:::::exercise (rating := 2) (name := "even_succ")
Here's a useful theorem that proves `even (n + 1)` flips
the parity.  This will facilitate proofs by induction on `n`:

One inconvenient aspect of our definition of `even n` is the
recursive call on `n - two`. This makes proofs about `even n`
harder when done by induction on `n`, since we may need an
induction hypothesis about `n - two`. The following lemma gives an
alternative characterization of `even (succ n)` that works better
with induction:

(Tip: To expand the body of `even` in a proof, use `rewrite [even]` or
`rw [even]`.)

```lean
theorem even_succ (n : Nat) :
    even (succ n) = !even n := by
  solution!
    induction n with
    | zero =>
      rw [even_zero, even_one]
      rfl
    | succ n' ih =>
      rw [even, ih, not_involutive]
```

:::grade
```
GRADE_THEOREM 1: even_succ
```
:::
:::::

::::::

::::hide
```
-- QUIZ
/- We've seen that there are goals that `cases` can't solve but
    `induction` can. What about the other way around? Are there steps
    in a proof that can be solved by pure case analysis `cases`
    but not using `induction`?

    (A) No

    (B) Yes
-/
-- /QUIZ
```
::::

# Proofs Within Proofs

::::full
In Lean, as in informal mathematics, large proofs are often
broken into a sequence of theorems, with later proofs referring to
earlier theorems.  But sometimes a proof will involve some
miscellaneous fact that is too trivial and of too little general
interest to bother giving it its own top-level name.  In such
cases, it is convenient to be able to simply state and prove the
required fact "in place".  The `have` tactic allows us to do this.
::::

::::terse
New tactic: `have`.
::::

```lean
theorem mult_zero_plus' (n m : Nat) :
    ((zero + n) + zero) * m = n * m := by
  have h : (zero + n) + zero = n := by
    rw [zero_add, add_zero]
  rw [h]
```

::::full
The `have` tactic introduces a local lemma into the proof.
We prove it immediately, and then it's available as a hypothesis
for the rest of the proof.
::::

:::slidebreak
:::

::::full
As another example, suppose we want to prove that `(n + m)
+ (p + q) = (m + n) + (p + q)`. The only difference between the
two sides of the `=` is that the arguments `m` and `n` to the
first inner `+` are swapped, so it seems we should be able to use
the commutativity of addition (`add_comm`) to rewrite one into the
other.  However, the `rw` tactic is not very smart about _where_
it applies the rewrite.  There are three uses of `+` here, and
`rw [add_comm]` may affect the wrong one...
::::

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (n m p q : Nat) :
   (n + m) + (p + q) = (m + n) + (p + q) := by
  /-
    We just need to swap (n + m) for (m + n)... seems
    like add_comm should do the trick!
    But `rw [add_comm]` might rewrite the wrong `+`!
  -/
  rw [add_comm]
  sorry
```

:::slidebreak
:::

::::terse
To use `add_comm` at the point where we need it, we can supply
explicit arguments: `rw [add_comm n m]` tells Lean exactly which
`+` to rewrite.  (We can also use `have` to establish the specific
equation we want, then rewrite with it.)
::::

```lean
theorem plus_rearrange (n m p q : Nat) :
    (n + m) + (p + q) = (m + n) + (p + q) := by
  rw [add_comm n m]
```

# Formal vs. Informal Proof

:::epigraph
"Informal proofs are algorithms; formal proofs are code."
:::

::::full
What constitutes a successful proof of a mathematical claim?

The question has challenged philosophers for millennia, but a
rough and ready answer could be this: A proof of a mathematical
proposition `P` is a written (or spoken) text that instills in the
reader or hearer the certainty that `P` is true -- an unassailable
argument for the truth of `P`.  That is, a proof is an act of
communication.

Acts of communication may involve different sorts of readers.  On
one hand, the "reader" can be a program like Lean, in which case
the "belief" that is instilled is that `P` can be mechanically
derived from a certain set of formal logical rules, and the proof
is a recipe that guides the program in checking this fact.  Such
recipes are _formal_ proofs.

Alternatively, the reader can be a human being, in which case the
proof will probably be written in English or some other natural
language and will thus necessarily be _informal_.  Here, the
criteria for success are less clearly specified.  A "valid" proof
is one that makes the reader believe `P`.  But the same proof may
be read by many different readers, some of whom may be convinced
by a particular way of phrasing the argument, while others may not
be. Some readers may be particularly pedantic, inexperienced, or
just plain thick-headed; the only way to convince them will be to
make the argument in painstaking detail.  Other readers, more
familiar in the area, may find all this detail so overwhelming
that they lose the overall thread; all they want is to be told the
main ideas, since it is easier for them to fill in the details for
themselves than to wade through a written presentation of them.
Ultimately, there is no universal standard, because there is no
single way of writing an informal proof that will convince every
conceivable reader.

In practice, however, mathematicians have developed a rich set of
conventions and idioms for writing about complex mathematical
objects that -- at least within a certain community -- make
communication fairly reliable.  The conventions of this stylized
form of communication give a reasonably clear standard for judging
proofs good or bad.

Because we are using Lean in this course, we will be working
heavily with formal proofs.  But this doesn't mean we can
completely forget about informal ones!  Formal proofs are useful
in many ways, but they are _not_ very efficient ways of
communicating ideas between human beings.

For example, here is a proof that addition is associative
   (you might have written it yourself, earlier in this chapter!):

```lean
theorem add_assoc' (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  induction p with
  | zero       => rw [add_zero, add_zero]
  | succ p' ih => rw [add_succ, add_succ, add_succ, ih]
```

Lean is perfectly happy with this.  For a human, however, it
is difficult to make much sense of it.  We can
pass arguments to the `add_succ` theorems to show the structure more clearly...

:::dev "Jonathan Chan (ionathanch)"
```
This would be a great location to introduce `calc`!
```
:::

```lean
theorem add_assoc'' (n m p : Nat) :
    add n (add m p) = add (add n m) p := by
  induction p with
  | zero => /- p = zero -/
    rw [add_zero, add_zero]
  | succ p' ih => /- p = p' + 1 -/
    rw [add_succ m p', add_succ n (m + p'), add_succ (n + m) p', ih]
```

... and if you're used to Lean you might be able to step
through the tactics one after the other in your mind and imagine
the state of the context and goal stack at each point, but if the
proof were even a little bit more complicated this would be next
to impossible.

A (pedantic) mathematician might write the proof something like
this:

:::dev "Benjamin Pierce (bcpierce00)"
```
Again, the math displays need to be displayed!
```
:::

- _Theorem_: For any `n`, `m` and `p`,

```display
      n + (m + p) = (n + m) + p.
```

_Proof_: By induction on `p`.

- First, suppose `p = zero`.  We must show that

```display
        n + (m + zero) = (n + m) + zero.
```

This follows directly from the definition of `+`
(since `x + zero = x` for any `x`).

- Next, suppose `p = p' + 1`, where

```display
        n + (m + p') = (n + m) + p'.
```

We must now show that

```display
        n + (m + (p' + 1)) = (n + m) + (p' + 1).
```

By the definition of `+`, both sides reduce to

```display
        (n + (m + p')) + 1   and   ((n + m) + p') + 1
```

respectively, which are equal by the induction hypothesis.
_Qed_.
::::

::::hide
```
 MMG: the proof above makes no use of lemmas, so it's hard for
   students to know what to do.  It might be good to also give them a
   sample proof of mult_1_l so they know how to "invoke" things
   they've already proved.
```
::::

::::::full
The overall form of the proof is basically similar, and of
course this is no accident: Lean has been designed so that its
`induction` tactic generates the same sub-goals, in the same
order, as the bullet points that a mathematician would usually
write.  But there are significant differences of detail: the
formal proof is much more explicit in some ways (e.g., the use of
`rfl`) but much less explicit in others (in particular, the "proof
state" at any given point in the Lean proof is completely implicit,
whereas the informal proof reminds the reader several times where
things stand).

:::::exercise (rating := 2) (name := "add_comm_informal")
Translate your solution for `add_comm` into an informal proof:

Theorem: Addition is commutative.

Proof:

:::dev "Benjamin Pierce (bcpierce00)"
```
Somebody please check that this typesets nicely!  (I doubt it does...) Ditto below.
SOLUTION
```
:::

Let natural numbers `n` and `m` be given.  We show `n + m = m +
n` by induction on `m`.

- First, suppose `m = zero`.  We must show `n + zero = zero + n`.  By
the definition of `+`, `n + zero = n`.  We have already shown
(lemma `zero_add`) that `zero + n = n`.  Thus both sides equal
`n`.

- Next, suppose `m = m' + 1` for some `m'`, where `n + m' = m'
+ n`.  We must show that `n + (m' + 1) = (m' + 1) + n`.  By
the definition of `+`, `n + (m' + 1) = (n + m') + 1`.  By
`succ_add`, `(m' + 1) + n = (m' + n) + 1`.  By the induction
hypothesis, `n + m' = m' + n`, so both sides equal
`(m' + n) + 1`.

:::grade
```
GRADE_MANUAL 2: add_comm_informal
```
:::
:::::

:::::exercise (rating := 2) (name := "beq_refl_informal")
Write an informal proof of the following theorem, using the
informal proof of `add_assoc` as a model.  Don't just
paraphrase the Lean tactics into English!

Theorem: `(n == n) = true` for any `n`.

Proof:

:::solution
```
By induction on `n`.

- First, suppose `n = zero`.  We must show `(zero == zero) = true`.  This
follows directly from the definition of `beq`.

- Next, suppose `n = n' + 1`, where `(n' == n') = true`.  We
must show `(n' + 1 == n' + 1) = true`. This
follows directly from the induction hypothesis and the
definition of `beq`.
```
:::

:::grade
```
GRADE_MANUAL 2: beq_refl_informal
```
:::
:::::

::::::

# More Exercises

Tip: By default, `rewrite` and `rw` rewrite left to right, i.e.,
they transform the hypothesis or goal being rewritten from the form on
the left side of the equality to the right side. To rewrite from
right to left, use `rewrite [← h]` or `rw [← h]`, where `←` is entered
as `\l` or `\<-`.

:::::exercise (rating := 1) (name := "mul_one")
```lean
theorem mul_one (p : Nat) :
    one * p = p := by
  solution!
    induction p with
    | zero       => rw [mul_zero]
    | succ p' ih => rw [mul_succ, ih, succ_eq_add_one]
```

:::grade
```
GRADE_THEOREM 1: mul_one
```
:::
:::::

:::::exercise (rating := 2) (name := "mul_two")
```lean
theorem mul_two (p : Nat) :
    two * p = p + p := by
  solution!
    induction p with
    | zero => rw [mul_zero, add_zero]
    | succ p' ih =>
      rw [mul_succ, ih, two_eq_succ_one, succ_eq_add_one, succ_eq_add_one]
      rw [add_assoc, add_assoc, ←add_assoc p' p' one]
      rw [add_comm p' one, add_comm p']
```

:::grade
```
GRADE_THEOREM 1: mul_two
```
:::
:::::

::::terse
These exercises state facts that will be used in
later chapters.  We don't need to work them in class.
::::

:::::exercise (rating := 3) (name := "mul_comm")
Use `have` (or `rw` with explicit arguments) to help prove
`add_shuffle3`.  You don't need to use induction yet.

Note: By default, `rewrite` and `rw` rewrite left-to-right. To rewrite from
right to left, use `rw [← h]`, where `←` is typed as `\l` or `\<-`.

```lean
theorem add_shuffle3 : ∀ n m p : Nat,
    add (add n m) p = add (add n p) m := by
  solution!
    intro n m p
    rw [← add_assoc, add_comm m p, add_assoc]
```

:::grade
```
GRADE_THEOREM 1: add_shuffle3
```
:::

```lean
-- SOLUTION
theorem succ_mul (m n : Nat) :
    (succ n) * m = (n * m) + m := by
  induction m with
  | zero => rw [mul_zero, mul_zero, add_zero]
  | succ m ih =>
    rw [mul_succ, ih, add_succ, add_comm _ n,
        add_assoc n _ m, add_comm n, mul_succ, add_succ]
-- END SOLUTION
```

Now prove commutativity of multiplication.

```lean
theorem mul_comm (m n : Nat) :
    m * n = n * m := by
  solution!
    induction n with
    | zero =>
      rw [mul_zero, zero_mul]
    | succ n' ih =>
      rw [mul_succ, ih, succ_mul]
```

:::grade
```
GRADE_THEOREM 2: mul_comm
```
:::
:::::

:::dev "Benjamin Pierce (bcpierce00)"
```
This comment is placed a bit awkwardly: In the terse version, we
usually skim past these exercises, but now we'll need to pause and look
at how <;> works...
TERSE
```
:::

New tactic combinator: `t₁ <;> t₂` runs `t₁`, then runs `t₂` on every
subgoal produced by `t₁`.

::::full
Before moving on to the next batch of exercises, let's introduce one
small _tactic combinator_. A tactic combinator combines tactics to form
a larger tactic.

If `t₁` and `t₂` are tactics, then `t₁ <;> t₂` means: run `t₁`, then
run `t₂` on every subgoal produced by `t₁`.

This is useful when one tactic splits the goal into several subgoals
and all of them can be finished in the same way.
::::

```lean
example (b : Bool) : (b || true) = true := by
  cases b <;> rfl
```

::::full
This is short for:

```lean
example (b : Bool) : (b || true) = true := by
  cases b with
  | false => rfl
  | true  => rfl
```

We can also chain `<;>`s.  In the next example, `cases b` creates two
goals; in each of them, `cases c` splits the goal again; then `rfl`
solves all four remaining goals.

```lean
example (b c : Bool) : (b && c) = (c && b) := by
  cases b <;> cases c <;> rfl
```

Use `<;>` when the generated subgoals really do have the same proof.
If different branches need different arguments, it is usually clearer
to write the cases explicitly.
::::

:::::exercise (rating := 3) (name := "more_exercises")
Take a piece of paper.  For each of the following theorems, first
_think_ about whether (a) it can be proved using only
simplification and rewriting, (b) it also requires case
analysis (`cases`), or (c) it also requires induction.  Write
down your prediction.  Then fill in the proof.  (There is no need
to turn in your piece of paper; this is just to encourage you to
reflect before you hack!)
Some of these proofs can be shortened
with `<;>` when several generated subgoals have the same proof.

:::dev "Benjamin Pierce (bcpierce00)"
```
Is that the main reason for introducing <;> here?  Seems weak if so.
Could we consider moving it later?
```
:::

```lean
theorem ble_refl (n : Nat) :
    ble n n = true := by
  solution!
    induction n with
    | zero       => rw [zero_ble]
    | succ n' ih => rw [succ_ble_succ]; exact ih

theorem andb_false (b : Bool) :
    (b && false) = false := by
  solution!
    cases b with
    | false => rw [Bool.false_and]
    | true  => rw [Bool.true_and]

theorem all3_spec (b c : Bool) :
    (b && c) || ((!b) || (!c)) = true := by
  solution!
    cases b with
    | true  => cases c <;> rfl
    | false => rfl

theorem right_distrib (n m p : Nat) :
    (n + m) * p = (n * p) + (m * p) := by
  solution!
    induction p with
    | zero => rw [mul_zero, mul_zero, mul_zero, add_zero]
    | succ p' ih =>
      rw [mul_succ, mul_succ, mul_succ, ih]
      rw [add_assoc ((n * p') + (m * p')),
          add_shuffle3 (n * p') (m * p'),
          add_assoc ((n * p') + n)]

theorem left_distrib (n m p : Nat) :
    p * (n + m) = (p * n) + (p * m) := by
  solution!
    rw [mul_comm p, mul_comm p, mul_comm p]
    rw [right_distrib]

theorem mul_assoc (n m p : Nat) :
    n * (m * p) = (n * m) * p := by
  solution!
    induction p with
    | zero       => rw [mul_zero, mul_zero, mul_zero]
    | succ p' ih => rw [mul_succ, mul_succ, ← ih, left_distrib]
```
:::::

## Nat to Bin and Back to Nat

::::::full
```lean
namespace NatToBin
```

Recall the `Bin` type we defined in Basics:

```lean
inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)
```

Before you start working on the next exercise, replace the stub
definitions of `incr` and `binToNat`, below, with your solution
from Basics.  That will make it possible for this file to be graded
on its own.

```lean
def incr (m : Bin) : Bin
  := solution!(match m with
  | .z     => .b1 .z
  | .b0 m' => .b1 m'
  | .b1 m' => .b0 (incr m'))
```

```lean
theorem incr_z : incr .z = .b1 .z := solution!(by rfl)
theorem incr_b0 m : incr (.b0 m) = .b1 m := solution!(by rfl)
theorem incr_b1 m : incr (.b1 m) = .b0 (incr m) := solution!(by rfl)
```

```lean
def binToNat (m : Bin) : Nat
  := solution!(match m with
  | .z     => zero
  | .b0 m' => (binToNat m') * two
  | .b1 m' => ((binToNat m') * two) + one)

theorem binToNat_z : binToNat .z = zero := solution!(by rfl)
theorem binToNat_b0 m : binToNat (.b0 m) = mul (binToNat m) two := solution!(by rfl)
theorem binToNat_b1 m : binToNat (.b1 m) = add (mul (binToNat m) two) one := solution!(by rfl)

attribute [pp_nodot] Bin.b0 Bin.b1
```

In Basics, we did some unit testing of `binToNat`, but we
didn't prove its correctness. Now we'll do so.

:::::exercise (rating := 3) (name := "binary_commute")
:::dev "Daniel Sainati (dsainati1)" SOONER
```
This is a very category theoretic way to present
   this idea. Is this the most useful way to convey this to
   an audience who is presumably unfamiliar with commutative diagrams?

BCP: I think it's fine, though the english version could precede the diagram
instead of following it...
```
:::

  Prove that the following diagram commutes:

```display
       incr Bin ----------------------> Bin
           |                             |
binToNat   |                             |  binToNat
           |                             |
           v                             v
          Nat ------------------------> Nat
                      succ
```

  That is, incrementing a binary number and then converting it to
  a (unary) natural number yields the same result as first converting
  it to a natural number and then incrementing.

  If you want to change your previous definitions of `incr` or `binToNat`
  to make the property easier to prove, feel free!

```lean
theorem bin_to_nat_pres_incr (b : Bin) :
    binToNat (incr b) = (binToNat b) + one := by
  solution!
    induction b with
    | z =>
      rw [incr_z, binToNat_b1, binToNat_z]
      rw [zero_mul]
    | b0 b' ih =>
      rw [incr_b0, binToNat_b0, binToNat_b1]
    | b1 b' ih =>
      rw [incr_b1, binToNat_b1, binToNat_b0, ih]
      rw [mul_comm, mul_two, mul_comm, mul_two, add_assoc]
      rw [add_shuffle3 _ one]
```

:::grade
```
GRADE_THEOREM 3: bin_to_nat_pres_incr
```
:::
:::::

:::::exercise (rating := 3) (name := "nat_bin_nat")
Write a function to convert natural numbers to binary numbers.
  Also write some simplification lemmas for it.

```lean
def natToBin (n : Nat) : Bin := solution!(
  match n with
  | zero    => .z
  | succ n' => incr (natToBin n'))
```

:::dev "Daniel Sainati (dsainati1)" TODO
```
How to hide these theorem statements so that students can get practice writing them?
```
:::

From GitHub:
CH: David set it up so that if you put:
-- SOLUTION
-- END SOLUTION

in an exercise that it will turn into
  -- FILL IN HERE
in both student version of the Lean files and the generated HTML.

```lean
theorem natToBin_zero : natToBin zero = .z := solution!(by rfl)
theorem natToBin_succ m : natToBin (succ m) = incr (natToBin m) := solution!(by rfl)
```

:::dev "Benjamin Pierce (bcpierce00)"
```
Could these be moved later so that at least the reader has the chance to do the exercise
before encountering them?
```
:::

Prove that, if we start with any `Nat`, convert it to `Bin`, and
convert it back, we get the same `Nat` which we started with.

Hint: This proof should go through smoothly using the previous
exercise about `incr` as a lemma. If not, revisit your definitions
of the functions involved and consider whether they are more
complicated than necessary: the shape of a proof by induction will
match the recursive structure of the program being verified, so
make the recursions as simple as possible.

```lean
theorem nat_bin_nat (n : Nat) :
    binToNat (natToBin n) = n := by
  solution!
    induction n with
    | zero =>
      rw [natToBin_zero, binToNat_z]
    | succ n' ih =>
      rw [natToBin_succ, bin_to_nat_pres_incr, ih, ← succ_eq_add_one]
```

:::grade
```
GRADE_THEOREM 3: nat_bin_nat
```
:::
:::::

::::::

## Bin to Nat and Back to Bin (Advanced)

::::::full
The opposite direction -- starting with a `Bin`, converting to `Nat`,
then converting back to `Bin` -- turns out to be problematic. That
is, the following theorem does not hold.

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∀ b, natToBin (binToNat b) = b := by sorry
```

Let's explore why this theorem fails and how to prove a modified
version of it. We'll start with some lemmas that might seem
unrelated but will turn out to be relevant.

:::::exercise (rating := 2) (name := "double_bin")
Prove this lemma about `double`, which we defined earlier in the
chapter.

```lean
theorem double_incr (n : Nat) :
    double (succ n) = (double n) + two := by
  solution!
    rw [double_succ]
    rw [two_eq_succ_one, one_eq_succ_zero, add_succ, add_succ, add_zero]
```

:::grade
```
GRADE_THEOREM 0.5: double_incr
```
:::

Now define a similar doubling function for `Bin`.

```lean
def doubleBin (b : Bin) : Bin := solution!(
  match b with
  | .z => .z
  | _  => .b0 b)
```

:::dev "Daniel Sainati (dsainati1)" TODO
```
How to hide these theorem statements so that students can get practice writing them?
```
:::

```lean
theorem doubleBin_z : doubleBin .z = .z := solution!(by rfl)
theorem doubleBin_b0 m : doubleBin (.b0 m) = .b0 (.b0 m) := solution!(by rfl)
theorem doubleBin_b1 m : doubleBin (.b1 m) = .b0 (.b1 m) := solution!(by rfl)

```

Check that your function correctly doubles zero.

```lean
example : doubleBin .z = .z := solution!(by rfl)
```

:::grade
```
GRADE_THEOREM 0.5: double_bin_zero
```
:::

Prove this lemma, which corresponds to `double_incr`.

```lean
theorem double_incr_bin (b : Bin) :
    doubleBin (incr b) = incr (incr (doubleBin b)) := by
  solution!
    cases b with
    | z =>    rw [incr_z, doubleBin_b1, doubleBin_z, incr_z, incr_b1, incr_z]
    | b0 n => rw [incr_b0, doubleBin_b1, doubleBin_b0, incr_b0, incr_b1, incr_b0]
    | b1 n => rw [incr_b1, doubleBin_b0, doubleBin_b1, incr_b0, incr_b1, incr_b1]
```

:::grade
```
GRADE_THEOREM 1: double_incr_bin
```
:::
:::::

Let's return to our desired theorem:

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example b : natToBin (binToNat b) = b := by sorry
```

The theorem fails because there are some `Bin` such that we won't
necessarily get back to the _original_ `Bin`, but instead to an
"equivalent" `Bin`.  (We deliberately leave that notion undefined
here for you to think about.)

Explain in a comment, below, why this failure occurs. Your
explanation will not be graded, but it's important that you get it
clear in your mind before going on to the next part. If you're
stuck on this, think about alternative implementations of
`doubleBin` that might have failed to satisfy `double_bin_zero`
yet otherwise seem correct.

:::solution
```
The problem is that `zero` has many representations: it can be written
`.z`, `.b0 .z`, `.b0 (.b0 .z)`, and so on.  For these alternate
representations, if you do `binToNat` then `natToBin`, you
don't get back what you started with.

Any other number also has many representations, after applying
constructors to the multiple representations of zero.
```
:::

To solve that problem, we can introduce a _normalization_ function
that selects the simplest `Bin` out of all the equivalent
`Bin`. Then we can prove that the conversion from `Bin` to `Nat` and
back again produces that normalized, simplest `Bin`.

:::::exercise (rating := 4) (name := "bin_nat_bin")
Define `normalize`. You will need to keep its definition as simple
as possible for later proofs to go smoothly. Do not use
`binToNat` or `natToBin`, but do use `doubleBin`.

Hint: Structure the recursion such that it _always_ reaches the
end of the `Bin` and _only_ processes each bit once. Do not
try to "look ahead" at future bits.

```lean
def normalize (b : Bin) : Bin := solution!(
  match b with
  | .z     => .z
  | .b0 b' => doubleBin (normalize b')
  | .b1 b' => incr (doubleBin (normalize b')))
```

:::dev "Daniel Sainati (dsainati1)" TODO
```
How to hide these theorem statements so that students can get practice writing them?
```
:::

```lean
theorem normalize_z : normalize .z = .z := solution!(by rfl)
theorem normalize_b0 m : normalize (.b0 m) = doubleBin (normalize m) := solution!(by rfl)
theorem normalize_b1 m : normalize (.b1 m) = incr (doubleBin (normalize m)) := solution!(by rfl)

```

It would be wise to do some `example` proofs to check that your
definition of `normalize` works the way you intend before you
proceed. They won't be graded, but fill them in below.

```lean
-- SOLUTION
/- normalize_test_zero -/
example : normalize .z = .z := by rfl
/- normalize_test_1 -/
example : normalize (.b1 .z) = .b1 .z := by rfl
/- normalize_test_2 -/
example : normalize (.b0 .z) = .z := by rfl
/- normalize_test_3 -/
example : normalize (.b0 (.b0 .z)) = .z := by rfl
/- normalize_test_4 -/
example : normalize (.b1 (.b0 .z)) = .b1 .z := by rfl
-- END SOLUTION

attribute [irreducible] normalize doubleBin natToBin incr binToNat
```

Finally, prove the main theorem. The inductive cases could be a
bit tricky.

Hint: Start by trying to prove the main statement, see where you
get stuck, and see if you can find a lemma -- perhaps requiring
its own inductive proof -- that will allow the main proof to make
progress. We have one lemma for the `b0` case (which also makes
use of `double_incr_bin`) and another for the `b1` case.

```lean
-- SOLUTION
theorem incr_doubleBin (b : Bin) :
    incr (doubleBin b) = .b1 b := by
  cases b with
  | z    => rw [doubleBin_z, incr_z]
  | b0 n => rw [doubleBin_b0, incr_b0]
  | b1 n => rw [doubleBin_b1, incr_b0]

theorem natToBin_two_mul n :
    natToBin (mul n two) = doubleBin (natToBin n) := by
  induction n with
  | zero => rw [zero_mul, natToBin_zero, doubleBin_z]
  | succ n' ih =>
    /-
      2 * (n' + 1) = 2 * n' + 2 by Nat.mul_succ.
      natToBin (2 * n' + 2): since +2 is +(1+1), this unfolds to
      incr (incr (natToBin (2 * n'))).
      By ih: = incr (incr (doubleBin (natToBin n'))).
      RHS: doubleBin (natToBin (n' + 1)) = doubleBin (incr (natToBin n')).
      By double_incr_bin: = incr (incr (doubleBin (natToBin n'))). ✓
    -/
    rw [mul_comm, mul_two] at *
    rw [add_succ, succ_add]
    rw [natToBin_succ, natToBin_succ, natToBin_succ]
    rw [ih, ← double_incr_bin]
-- END SOLUTION

theorem bin_nat_bin (b : Bin) :
    natToBin (binToNat b) = normalize b := by
  solution!
    induction b with
    | z =>
      rw [binToNat_z, normalize_z, natToBin_zero]
    | b0 b' ih =>
      rw [binToNat_b0, normalize_b0]
      rw [natToBin_two_mul, ih]
    | b1 b' ih =>
      rw [binToNat_b1, normalize_b1]
      /- Goal: natToBin (binToNat b' * 2 + 1) = incr (doubleBin (normalize b')) -/
      rw [← succ_eq_add_one]
      rw [natToBin_succ]
      rw [natToBin_two_mul, ih]

end NatToBin
```

:::grade
```
GRADE_THEOREM 6: bin_nat_bin
```
:::
:::::

::::::

```lean
end NatPlayground.Nat
```

::::hide
```
  There is MUCH more that we could say about this topic.  We
  could do a similar example (and pair of exercises) involving
  [cases].  We could talk about references to external theorems.
  Basically, for each tactic, we could give people some guidance
  about how to lay out corresponding informal proofs...  But the
  current direction is to minimize the role of informal proofs (at
  least, the degree to which we try to get people to write them) in
  SF.
```
::::
