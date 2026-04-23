/- Induction: Proof by Induction -/


/-
  ######################################################################
  # Separate Compilation
-/


/-
  Before getting started on this chapter, we need to import
  all of our definitions from the previous chapter:
-/

import Basics

/-
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
-/

/-
  ######################################################################
  # Review
-/

/-
  To prove the following theorem, which tactics will we need besides
  `intro` and `rfl`?  (A) none, (B) `rw`, (C) `cases`, (D) both
  `rw` and `cases`, or (E) can't be done with the tactics we've seen.

      theorem review1 : (true || false) = true
-/

/-
  What about the next one?

      theorem review2 : ∀ b, (true || b) = true

  Which tactics do we need besides `intro` and `rfl`?  (A)
  none (B) `rw`, (C) `cases`, (D) both `rw` and `cases`,
  or (E) can't be done with the tactics we've seen.
-/

/-
  What if we change the order of the arguments of `||`?

      theorem review3 : ∀ b, (b || true) = true

  Which tactics do we need besides `intro` and `rfl`?  (A)
  none (B) `rw`, (C) `cases`, (D) both `rw` and `cases`,
  or (E) can't be done with the tactics we've seen.
-/

/-
  What about this one?  (Recall that in Lean, `Nat.add` recurses on
  the _second_ argument: `n + 0 = n` by definition, and
  `n + (m + 1) = (n + m) + 1` by definition.)

      theorem review4 : ∀ n : Nat, n + 0 = n

  (A) none, (B) `rw`, (C) `cases`, (D) both `rw` and `cases`,
  or (E) can't be done with the tactics we've seen.
-/

/-
  What about this?

      theorem review5 : ∀ n : Nat, 0 + n = n

  (A) none, (B) `rw`, (C) `cases`, (D) both `rw` and `cases`,
  or (E) can't be done with the tactics we've seen.
-/

/-
  ######################################################################
  ## Proof by Induction
-/

/-
  In Lean, `Nat.add` is defined to recurse on its _second_
  argument:

      protected def Nat.add : Nat → Nat → Nat
        | n, 0     => n
        | n, m + 1 => (Nat.add n m) + 1

  This means `n + 0` reduces to `n` by definition, but `0 + n` does
  _not_.

  We can prove that `0` is a neutral element for `+` on the _right_
   using just `rfl`:
-/

/- add_0_r_easy -/
example : ∀ n : Nat, n + 0 = n := by
  intro n; rfl


/- zero_add_firsttry -/
example : ∀ n : Nat, 0 + n = n := by
/- ... gets stuck. -/
/-
  ... can't be done in the same simple way.  Just applying
  `rfl` doesn't work, since the `n` in `0 + n` is an arbitrary
  unknown number, so the `match` in the definition of `+` can't be
  simplified.
-/
  intro n
  /- `rfl` doesn't work here! -/
  sorry

/- TERSE: *** -/

/-
  And reasoning by cases using `cases n` doesn't get us much
  further: the branch of the case analysis where we assume `n = 0`
  goes through just fine, but in the branch where `n = n' + 1` for
  some `n'` we get stuck in exactly the same way.
-/

/- zero_add_secondtry -/
example : ∀ n : Nat, 0 + n = n := by
  intro n
  cases n
  case zero => /- n = 0 -/
    rfl /- so far so good... -/
  case succ n' => /- n = n' + 1 -/
    /- 0 + (n' + 1) reduces to (0 + n') + 1 ...but we're stuck on 0 + n' -/
    sorry

/-
  We could use `cases n'` to get a bit further, but,
  since `n` can be arbitrarily large, we'll never get all the way
  there if we just go on like this.
-/

/- TERSE: *** -/

/-
  To prove interesting facts about numbers, lists, and other
  inductively defined sets, we often need a more powerful reasoning
  principle: _induction_.

  Recall (from a discrete math course, probably) the _principle of
  induction over natural numbers_: If `P(n)` is some proposition
  involving a natural number `n` and we want to show that `P` holds for
  all numbers `n`, we can reason like this:
  - show that `P(0)` holds;
  - show that, for any `n'`, if `P(n')` holds, then so does
  `P(n' + 1)`;
  - conclude that `P(n)` holds for all `n`.

  In Lean, the steps are the same: we begin with the goal of proving
  `P(n)` for all `n` and use the `induction` tactic to break it down
  into two separate subgoals: one where we must show `P(0)` and another
  where we must show `P(n') → P(n' + 1)`.  Here's how this works for
  the theorem at hand...
-/

/-
  We need a bigger hammer: the _principle of induction_ over
  natural numbers...

  - If `P(n)` is some proposition involving a natural number `n`,
  and we want to show that `P` holds for _all_ numbers, we can
  reason like this:

  - show that `P(0)` holds
  - show that, if `P(n')` holds, then so does `P(n' + 1)`
  - conclude that `P(n)` holds for all `n`.

  For example...
-/

/- TERSE: *** -/

theorem zero_add : ∀ n : Nat, 0 + n = n := by
  intro n
  induction n
  case zero => /- n = 0 -/
    rfl
  case succ n' ih => /- n = n' + 1 -/
    /-
      Goal: 0 + (n' + 1) = n' + 1
      By definition of +, `0 + (n' + 1)` reduces to `(0 + n') + 1`.
      Then we can rewrite with the induction hypothesis.
    -/
    rw [add_succ, ih]

/-
  Like `cases`, the `induction` tactic takes a `with` clause
  that specifies the names of the variables to be introduced in the
  subgoals.  Since there are two subgoals (for `zero` and `succ`),
  the `with` clause has two branches.

  In the first subgoal, `n` is replaced by `0`.  The goal becomes
  `0 + 0 = 0`, which follows by `rfl`.

  In the second subgoal, `n` is replaced by `n' + 1`, and the
  induction hypothesis `ih : 0 + n' = n'` is added to the context.
  The goal becomes `0 + (n' + 1) = n' + 1`.  `add_succ` tells
  us that `a + (b + 1) = (a + b) + 1`, so `rw [add_succ]`
  transforms the goal to `(0 + n') + 1 = n' + 1`.  Then `rw [ih]`
  rewrites `0 + n'` to `n'`, and the goal becomes `n' + 1 = n' + 1`,
  which closes automatically.
-/

/- *** -/
/- Let's try this one together: -/

theorem sub_self : ∀ n,
    n - n = 0 := by
  intro n
  induction n
  case zero =>
    rfl
  case succ n' ih =>
    rw [succ_sub_succ]; exact ih

/-
  (The use of the `intro` tactic in these proofs is actually
  redundant.  When applied to a goal that contains quantified
  variables, the `induction` tactic will automatically move them
  into the context as needed.)
-/

/-
  Prove the following using induction. You might need previously
  proven results.
-/

theorem zero_mul : ∀ n : Nat,
    0 * n = 0 := by
  intro n
  induction n
  case zero => rfl
  case succ n' ih =>
    rw [mul_succ]; rw [ih]

theorem succ_add : ∀ n m : Nat,
    (n + 1) + m = (n + m) + 1 := by
  intro n m
  induction m
  case zero => rfl
  case succ m' ih =>
    rw [add_succ (n + 1) m', add_succ n m', ih]
/- *** -/
/-
  Here's another related fact about addition, which we'll
  need later.  (The proof is left as an exercise.)
-/

theorem add_comm : ∀ n m : Nat,
    n + m = m + n := by
  intro n m
  induction m
  case zero =>
    dsimp [add]; rw [zero_add]
  case succ m' ih =>
    rw [add_succ, ih, succ_add]

theorem add_assoc : ∀ n m p : Nat,
    n + (m + p) = (n + m) + p := by
  intro n m p
  induction p
  case zero => rfl
  case succ p' ih =>
    rw [add_succ m p', add_succ n (m + p'), add_succ (n + m) p', ih]

/- Consider the following function, which doubles its argument: -/

def double (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => (double n') + 2

/- Use induction to prove this simple fact about `double`: -/

theorem double_add : ∀ n, double n = n + n := by
  intro n
  induction n
  case zero => rfl
  case succ n' ih =>
    dsimp [double]; rw [ih, add_succ (n' + 1), succ_add]

/- *** -/
/-
  The following theorem relates the computational equality `BEq` on
  `Nat` with the definitional equality `=` on `Bool`.
-/

theorem eqb_refl : ∀ n : Nat,
    (n == n) = true := by
  intro n
  induction n
  case zero => rfl
  case succ n' ih => rw [beq_succ, ih]


/-
  Here's a useful theorem that proves `even (n + 1)` flips
  the parity.  This will facilitate proofs by induction on `n`:
-/
/-
  One inconvenient aspect of our definition of `even n` is the
  recursive call on `n - 2`. This makes proofs about `even n`
  harder when done by induction on `n`, since we may need an
  induction hypothesis about `n - 2`. The following lemma gives an
  alternative characterization of `even (n + 1)` that works better
  with induction:
-/

theorem even_S : ∀ n : Nat,
    even (n + 1) = !even n := by
  intro n
  induction n
  case zero => rfl
  case succ n' ih =>
    dsimp [even]; rw [ih, notb_involutive]


/-
  ######################################################################
  # Proofs Within Proofs
-/

/-
  In Lean, as in informal mathematics, large proofs are often
  broken into a sequence of theorems, with later proofs referring to
  earlier theorems.  But sometimes a proof will involve some
  miscellaneous fact that is too trivial and of too little general
  interest to bother giving it its own top-level name.  In such
  cases, it is convenient to be able to simply state and prove the
  required fact "in place".  The `have` tactic allows us to do this.
-/
/- New tactic: `have`. -/

theorem mult_0_plus' : ∀ n m : Nat,
    ((n + 0) + 0) * m = n * m := by
  intro n m
  have h : (n + 0) + 0 = n := by rfl
  rw [h]
/- LATER: BCP 21: Changed 0+n to n+0+0 for a more interesting
   proof (with 0+n was provable just by reflexivity!).  The new one is
   still straightforward without the replace, but maybe not quite so
   obviously so! -/

/-
  The `have` tactic introduces a local lemma into the proof.
  We prove it immediately, and then it's available as a hypothesis
  for the rest of the proof.
-/

/- TERSE: *** -/

/-
  As another example, suppose we want to prove that `(n + m)
  + (p + q) = (m + n) + (p + q)`. The only difference between the
  two sides of the `=` is that the arguments `m` and `n` to the
  first inner `+` are swapped, so it seems we should be able to use
  the commutativity of addition (`add_comm`) to rewrite one into the
  other.  However, the `rw` tactic is not very smart about _where_
  it applies the rewrite.  There are three uses of `+` here, and
  `rw [add_comm]` may affect the wrong one...
-/


/- plus_rearrange_firsttry -/
example : ∀ n m p q : Nat,
    (n + m) + (p + q) = (m + n) + (p + q) := by
  intro n m p q
  /-
    We just need to swap (n + m) for (m + n)... seems
    like add_comm should do the trick!
    But `rw [add_comm]` might rewrite the wrong `+`!
  -/
  rw [add_comm]
  sorry

/-
  ***
  To use `add_comm` at the point where we need it, we can supply
  explicit arguments: `rw [add_comm n m]` tells Lean exactly which
  `+` to rewrite.  (We can also use `have` to establish the specific
  equation we want, then rewrite with it.)
-/

theorem plus_rearrange : ∀ n m p q : Nat,
    (n + m) + (p + q) = (m + n) + (p + q) := by
  intro n m p q
  rw [add_comm n m]

/-
  ######################################################################
  # Formal vs. Informal Proof
-/

/- "Informal proofs are algorithms; formal proofs are code." -/

/-
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
-/

/- For example, here is a proof that addition is associative: -/

/- add_assoc' -/
theorem add_assoc' : ∀ n m p : Nat,
    n + (m + p) = (n + m) + p := by
  intro n m p
  induction p
  case zero => rfl
  case succ p' ih =>
    rw [add_succ m p', add_succ n (m + p'), add_succ (n + m) p', ih]

/-
  Lean is perfectly happy with this.  For a human, however, it
  is difficult to make much sense of it.  We can use comments and
  focused cases to show the structure a little more clearly...
-/

/- add_assoc'' -/
theorem add_assoc'' : ∀ n m p : Nat,
    n + (m + p) = (n + m) + p := by
  intro n m p
  induction p
  case zero => /- p = 0 -/
    rfl
  case succ p' ih => /- p = p' + 1 -/
    rw [add_succ m p', add_succ n (m + p'), add_succ (n + m) p', ih]

/-
  ... and if you're used to Lean you might be able to step
  through the tactics one after the other in your mind and imagine
  the state of the context and goal stack at each point, but if the
  proof were even a little bit more complicated this would be next
  to impossible.

  A (pedantic) mathematician might write the proof something like
  this:
-/

/-
  - _Theorem_: For any `n`, `m` and `p`,

  n + (m + p) = (n + m) + p.

  _Proof_: By induction on `p`.

  - First, suppose `p = 0`.  We must show that

  n + (m + 0) = (n + m) + 0.

  This follows directly from the definition of `+`
  (since `x + 0 = x` for any `x`).

  - Next, suppose `p = p' + 1`, where

  n + (m + p') = (n + m) + p'.

  We must now show that

  n + (m + (p' + 1)) = (n + m) + (p' + 1).

  By the definition of `+`, both sides reduce to

  (n + (m + p')) + 1   and   ((n + m) + p') + 1

  respectively, which are equal by the induction hypothesis.
  _Qed_.
-/

/- MMG: the proof above makes no use of lemmas, so it's hard for
   students to know what to do.  It might be good to also give them a
   sample proof of mult_1_l so they know how to "invoke" things
   they've already proved.  -/

/-
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
-/

/-
  Translate your solution for `add_comm` into an informal proof:

  Theorem: Addition is commutative.

  Proof:
-/
/-
  Let natural numbers `n` and `m` be given.  We show `n + m = m +
  n` by induction on `m`.

  - First, suppose `m = 0`.  We must show `n + 0 = 0 + n`.  By
  the definition of `+`, `n + 0 = n`.  We have already shown
  (lemma `zero_add`) that `0 + n = n`.  Thus both sides equal
  `n`.

  - Next, suppose `m = m' + 1` for some `m'`, where `n + m' = m'
  + n`.  We must show that `n + (m' + 1) = (m' + 1) + n`.  By
  the definition of `+`, `n + (m' + 1) = (n + m') + 1`.  By
  `succ_add`, `(m' + 1) + n = (m' + n) + 1`.  By the induction
  hypothesis, `n + m' = m' + n`, so both sides equal
  `(m' + n) + 1`.
-/

/-
  Write an informal proof of the following theorem, using the
  informal proof of `add_assoc` as a model.  Don't just
  paraphrase the Lean tactics into English!

  Theorem: `(n == n) = true` for any `n`.

  Proof:
-/
/-
  By induction on `n`.

  - First, suppose `n = 0`.  We must show `(0 == 0) = true`.  This
  follows directly from the definition of `eqb`.

  - Next, suppose `n = n' + 1`, where `(n' == n') = true`.  We
  must show `(n' + 1 == n' + 1) = true`. This
  follows directly from the induction hypothesis and the
  definition of `eqb`.
-/

/-
  ######################################################################
  # More Exercises
-/

theorem mul_one : ∀ p : Nat,
    p * 1 = p := by
  intro p
  rw [add_zero_one, mul_succ, mul_zero, zero_add]

theorem mul_two : ∀ p : Nat,
    p * 2 = p + p := by
  intro p
  rw [mul_succ, mul_succ, mul_zero, zero_add]

/-
  These additional exercises state facts that will be used in
  later chapters.  We don't need to work them in class.
-/

/-
  Use `have` (or `rw` with explicit arguments) to help prove
  `add_shuffle3`.  You don't need to use induction yet.
-/

theorem add_shuffle3 : ∀ n m p : Nat,
    (n + m) + p = (n + p) + m := by
  intro n m p
  rw [← add_assoc, add_comm m p, add_assoc]


theorem succ_mul : ∀ m n : Nat,
    (n + 1) * m = (n * m) + m := by
  intro m n
  induction m
  case zero => rw [mul_zero, mul_zero, add_zero]
  case succ m ih =>
    calc (n + 1) * (m + 1)
    _ = ((n + 1) * m) + (n + 1) := by rw [mul_succ]
    _ = ((n * m) + m) + (n + 1) := by rw [ih]
    _ = ((n * m) + m) + n + 1   := by rw [add_succ]
    _ = n + ((n * m) + m) + 1   := by rw [add_comm _ n]
    _ = (n + (n * m)) + m + 1   := by rw [← add_assoc n _ m]
    _ = ((n * m) + n) + m + 1   := by rw [add_comm n]
    _ = (n * (m + 1)) + (m + 1) := by rw [mul_succ, add_succ _ m]

/-
  Now prove commutativity of multiplication.  You will probably want
  to look for (or define and prove) a "helper" theorem to be used in
  the proof of this one. Hint: what is `n * (1 + k)`?
-/

theorem mul_comm : ∀ m n : Nat,
    m * n = n * m := by
  intro m n
  induction n
  case zero =>
    rw [mul_zero, zero_mul]
  case succ n' ih =>
    rw [mul_succ, ih, succ_mul]

/-
  Take a piece of paper.  For each of the following theorems, first
  _think_ about whether (a) it can be proved using only
  simplification and rewriting, (b) it also requires case
  analysis (`cases`), or (c) it also requires induction.  Write
  down your prediction.  Then fill in the proof.  (There is no need
  to turn in your piece of paper; this is just to encourage you to
  reflect before you hack!)
-/

theorem leb_refl : ∀ n : Nat,
    n <=? n = true := by
  intro n
  induction n
  case zero => rfl
  case succ n' ih => dsimp [leb]; exact ih

theorem zero_ne_add_one : ∀ n : Nat,
    (0 == n + 1) = false := by
  intro n; rfl

theorem andb_false : ∀ b : Bool,
    (b && false) = false := by
  intro b; cases b <;> rfl

theorem add_one_ne_zero : ∀ n : Nat,
    (n + 1 == 0) = false := by
  intro n; rfl

theorem one_mul : ∀ n : Nat, 1 * n = n := by
  intro n
  induction n
  case zero => rfl
  case succ n' ih =>
    rw [mul_succ, ih, add_comm]

theorem all3_spec : ∀ b c : Bool,
    (b && c) || ((!b) || (!c)) = true := by
  intro b c; cases b
  case true => cases c <;> rfl
  case false => rfl

theorem right_distrib : ∀ n m p : Nat,
    (n + m) * p = n * p + m * p := by
  intro n m p
  induction p
  case zero => rfl
  case succ p' ih =>
    rw [mul_succ, mul_succ, mul_succ, ih]
    generalize n * p' = i
    generalize m * p' = j
    calc (i + j) + (n + m)
    _ = ((i + j) + n) + m := by rw [add_assoc (i + j)]
    _ = ((i + n) + j) + m := by rw [add_shuffle3 i j n]
    _ = (i + n) + (j + m) := by rw [add_assoc (i + n)]

theorem left_distrib : ∀ n m p : Nat,
    p * (n + m) = p * n + p * m := by
  intro n m p
  rw [mul_comm p, mul_comm p, mul_comm p]
  rw [right_distrib]

theorem mul_assoc : ∀ n m p : Nat,
    n * (m * p) = (n * m) * p := by
  intro n m p
  induction p
  case zero => rfl
  case succ p' ih =>
    rw [mul_succ, mul_succ, ← ih, left_distrib]

/- ## Nat to Bin and Back to Nat -/

namespace NatToBin

/- Recall the `Bin` type we defined in Basics: -/

inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)

/-
  Before you start working on the next exercise, replace the stub
  definitions of `incr` and `binToNat`, below, with your solution
  from Basics.  That will make it possible for this file to be graded
  on its own.
-/

def incr (m : Bin) : Bin
  := match m with
  | .z => .b1 .z
  | .b0 m' => .b1 m'
  | .b1 m' => .b0 (incr m')

def binToNat (m : Bin) : Nat
  := match m with
  | .z => 0
  | .b0 m' => binToNat m' * 2
  | .b1 m' => binToNat m' * 2 + 1

/-
  In Basics, we did some unit testing of `binToNat`, but we
  didn't prove its correctness. Now we'll do so.
-/

/-
  Prove that the following diagram commutes:

  incr
  Bin ----------------------> Bin
  |                           |
  binToNat   |                           |  binToNat
  |                           |
  v                           v
  Nat ----------------------> Nat
  + 1

  That is, incrementing a binary number and then converting it to
  a (unary) natural number yields the same result as first converting
  it to a natural number and then incrementing.

  If you want to change your previous definitions of `incr` or `binToNat`
  to make the property easier to prove, feel free to do so!
-/

/- SOONER (DHS): This is a very-category theoretic way to present
   this idea. Is this the most useful way to convey this to
   an audience who is presumably unfamiliar with commutative diagrams? -/

theorem bin_to_nat_pres_incr : ∀ b : Bin,
    binToNat (incr b) = binToNat b + 1 := by
  intro b
  induction b
  case z => rfl
  case b0 b' ih =>
    dsimp [incr, binToNat]
  case b1 b' ih =>
    dsimp [incr, binToNat]; rw [ih]
    rw [mul_two, mul_two, add_succ]
    rw [add_shuffle3 _ 1]


/- Write a function to convert natural numbers to binary numbers. -/

def natToBin (n : Nat) : Bin :=
  match n with
  | 0 => .z
  | n' + 1 => incr (natToBin n')

/-
  Prove that, if we start with any `Nat`, convert it to `Bin`, and
  convert it back, we get the same `Nat` which we started with.

  Hint: This proof should go through smoothly using the previous
  exercise about `incr` as a lemma. If not, revisit your definitions
  of the functions involved and consider whether they are more
  complicated than necessary: the shape of a proof by induction will
  match the recursive structure of the program being verified, so
  make the recursions as simple as possible.
-/

theorem nat_bin_nat : ∀ n : Nat,
    binToNat (natToBin n) = n := by
  intro n
  induction n
  case zero => rfl
  case succ n' ih =>
    dsimp [natToBin]
    rw [bin_to_nat_pres_incr, ih]


/- ## Bin to Nat and Back to Bin (Advanced) -/

/-
  The opposite direction -- starting with a `Bin`, converting to `Nat`,
  then converting back to `Bin` -- turns out to be problematic. That
  is, the following theorem does not hold.
-/

/- bin_nat_bin_fails -/
example : ∀ b, natToBin (binToNat b) = b := by sorry

/-
  Let's explore why that theorem fails, and how to prove a modified
  version of it. We'll start with some lemmas that might seem
  unrelated, but will turn out to be relevant.
-/


/-
  Prove this lemma about `double`, which we defined earlier in the
  chapter.
-/

/- double_incr -/
theorem double_incr : ∀ n : Nat,
    double (n + 1) = (double n) + 2 := by
  intro n; rfl

/- Now define a similar doubling function for `Bin`. -/

def doubleBin (b : Bin) : Bin :=
  match b with
  | .z => .z
  | _ => .b0 b

/- Check that your function correctly doubles zero. -/

/- double_bin_zero -/
example : doubleBin .z = .z := by rfl  -- ADMITTED

/- Prove this lemma, which corresponds to `double_incr`. -/

/- double_incr_bin -/
theorem double_incr_bin : ∀ b : Bin,
    doubleBin (incr b) = incr (incr (doubleBin b)) := by
  intro b
  cases b
  . rfl
  . rfl
  . rfl


/- Let's return to our desired theorem: -/

example : ∀ b, natToBin (binToNat b) = b := by sorry

/-
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
-/

/-
  The problem is that `0` has many representations: it can be written
  `.z`, `.b0 .z`, `.b0 (.b0 .z)`, and so on.  For these alternate
  representations, if you do `binToNat` then `natToBin`, you
  don't get back what you started with.

  Any other number also has many representations, after applying
  constructors to the multiple representations of zero.
-/

/-
  To solve that problem, we can introduce a _normalization_ function
  that selects the simplest `Bin` out of all the equivalent
  `Bin`. Then we can prove that the conversion from `Bin` to `Nat` and
  back again produces that normalized, simplest `Bin`.
-/


/-
  Define `normalize`. You will need to keep its definition as simple
  as possible for later proofs to go smoothly. Do not use
  `binToNat` or `natToBin`, but do use `doubleBin`.

  Hint: Structure the recursion such that it _always_ reaches the
  end of the `Bin` and _only_ processes each bit once. Do not
  try to "look ahead" at future bits.
-/

def normalize (b : Bin) : Bin :=
  match b with
  | .z => .z
  | .b0 b' => doubleBin (normalize b')
  | .b1 b' => incr (doubleBin (normalize b'))

/-
  It would be wise to do some `example` proofs to check that your
  definition of `normalize` works the way you intend before you
  proceed. They won't be graded, but fill them in below.
-/

/- normalize_test_0 -/
example : normalize .z = .z := by rfl
/- normalize_test_1 -/
example : normalize (.b1 .z) = .b1 .z := by rfl
/- normalize_test_2 -/
example : normalize (.b0 .z) = .z := by rfl
/- normalize_test_3 -/
example : normalize (.b0 (.b0 .z)) = .z := by rfl
/- normalize_test_4 -/
example : normalize (.b1 (.b0 .z)) = .b1 .z := by rfl

/-
  Finally, prove the main theorem. The inductive cases could be a
  bit tricky.

  Hint: Start by trying to prove the main statement, see where you
  get stuck, and see if you can find a lemma -- perhaps requiring
  its own inductive proof -- that will allow the main proof to make
  progress. We have one lemma for the `b0` case (which also makes
  use of `double_incr_bin`) and another for the `b1` case.
-/

theorem incr_doubleBin : ∀ b : Bin,
    incr (doubleBin b) = .b1 b := by
  intro b
  cases b
  . rfl
  . rfl
  . rfl

theorem natToBin_two_mul : ∀ n,
    natToBin (n * 2) = doubleBin (natToBin n) := by
  intro n
  induction n
  case zero => rfl
  case succ n' ih =>
    /-
      2 * (n' + 1) = 2 * n' + 2 by Nat.mul_succ.
      natToBin (2 * n' + 2): since +2 is +(1+1), this unfolds to
      incr (incr (natToBin (2 * n'))).
      By ih: = incr (incr (doubleBin (natToBin n'))).
      RHS: doubleBin (natToBin (n' + 1)) = doubleBin (incr (natToBin n')).
      By double_incr_bin: = incr (incr (doubleBin (natToBin n'))). ✓
    -/
    rw [mul_two] at *
    rw [add_succ, add_shuffle3 n']
    dsimp [natToBin]
    rw [ih, ← double_incr_bin]

theorem bin_nat_bin : ∀ b : Bin,
    natToBin (binToNat b) = normalize b := by
  intro b
  induction b
  case z => rfl
  case b0 b' ih =>
    dsimp [binToNat, normalize]
    rw [natToBin_two_mul, ih]
  case b1 b' ih =>
    dsimp [binToNat, normalize]
    /- Goal: natToBin (binToNat b' * 2 + 1) = incr (doubleBin (normalize b')) -/
    dsimp [natToBin]
    rw [natToBin_two_mul, ih]

end NatToBin


