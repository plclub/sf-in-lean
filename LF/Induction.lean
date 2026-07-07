/- Induction: Proof by Induction -/

-- SOONER: Readers might expect us to add eqn:H annotations to uses of
--   induction, but this changes the shape of the IH in a nasty way! :-(
--   We should at least comment.  (BCP: Is this still relevant in Lean?)
-- SOONER: We should also consider adding more examples to clarify
--   the concepts introduced in this chapter. This could help in
--   reinforcing the understanding of induction principles.
-- LATER: In 3/22, MRC and BCP discussed "inlining" IndPrinciples
--   into earlier chapters, thus eliminating it as a chapter. This
--   chapter, Induction, is the first place a change would occur.  We
--   would present [nat_ind] here. Then in Lists/Poly we'd present
--   [list_ind], and the rest would go in IndProp and ProofObjects. The
--   main wrinkle is that we'd need to introduce [apply] here instead of
--   in Tactics if we want to preserve the presentation. The discussion
--   is preserved here: https://github.com/DeepSpec/sfdev/pull/471.
-- LATER: Now that we've added Steve's nice late-policy exercise in
--   Basics.v, the assignment for that chapter is probably hard enough.  Now
--   what about this chapter?  Can/should we make it a notch or two
--   harder?

/-
  ######################################################################
  # Separate Compilation
-/

-- BCP: This section will need some tidying and rewriting...

-- TERSE: Lean will first need to compile `Basics.lean` so it can
-- be imported here -- detailed instructions are in the full version
-- of this chapter...

-- FULL
/-
  Before getting started on this chapter, we need to import
  all of our definitions from the previous chapter:
-/
-- /FULL

prelude
import LF.Basics

-- FULL
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
-- /FULL

namespace NatPlayground.Nat

-- TERSE
/-
  ######################################################################
  # Review
-/
-- /TERSE

-- QUIZ
/-
  To prove the following theorem, which tactics will we need besides
  `intro` and `rfl`?  (A) none, (B) `rewrite`, (C) `cases`, (D) both
  `rewrite` and `cases`, or (E) can't be done with the tactics we've seen.

      theorem review1 : (true || false) = true
-/
-- HIDE
/- review1 -/
theorem review1 : (true || false) = true := by rfl
-- /HIDE
-- /QUIZ

-- QUIZ
/-
  What about the next one?

      theorem review2 : ∀ b, (true || b) = true

  Which tactics do we need besides `intro` and `rfl`?  (A)
  none (B) `rewrite`, (C) `cases`, (D) both `rewrite` and `cases`,
  or (E) can't be done with the tactics we've seen.
-/
-- HIDE
/- review2 -/
theorem review2 : ∀ b : Bool, (true || b) = true := by
  intro b; rfl
-- /HIDE
-- /QUIZ

-- QUIZ
/-
  What if we change the order of the arguments of `||`?

      theorem review3 : ∀ b, (b || true) = true

  Which tactics do we need besides `intro` and `rfl`?  (A)
  none (B) `rewrite`, (C) `cases`, (D) both `rewrite` and `cases`,
  or (E) can't be done with the tactics we've seen.
-/
-- HIDE
/- review3 -/
theorem review3 : ∀ b : Bool, (b || true) = true := by
  intro b; cases b
  . rfl
  . rfl
-- /HIDE
-- /QUIZ

-- QUIZ
/-
  What about this one?  (Recall that in Lean, `Nat.add` recurses on the _second_
  argument: `n + zero = n` by definition, and `n + (m + 1) = (n + m) + 1` by
  definition.)

      theorem review4 : ∀ n : Nat, n + zero = n

  (A) none, (B) `rewrite`, (C) `cases`, (D) both `rewrite` and `cases`, or (E)
  can't be done with the tactics we've seen.
-/
-- HIDE
/- review4 -/
theorem review4 : ∀ n : Nat, n + zero = n := by
  intro n; rewrite [add_zero]; rfl
-- /HIDE
-- /QUIZ

-- QUIZ
/-
  What about this?

      theorem review5 : ∀ n : Nat, zero + n = n

  (A) none, (B) `rewrite`, (C) `cases`, (D) both `rewrite` and `cases`,
  or (E) can't be done with the tactics we've seen.
-/
-- HIDE
/- review5 -/
/-
  This one CANNOT be proved by rfl, cases, or rewriting alone --
  it needs induction!  (We'll see why below.)
-/
-- /HIDE
-- /QUIZ

/- TODO (DHS): We use this theorem later,
   so let's make it into a review exercise here -/
/- review6 -/
/- Prove the following theorem, using theorems from Basics: -/
theorem succ_eq_add_one : ∀ n : Nat, succ n = n + one := by
-- ADMITTED
  intro n
  rewrite [one_eq_succ_zero, add_succ, add_zero]
  rfl
-- /ADMITTED

/-
  ######################################################################
  ## Proof by Induction
-/

-- FULL
/-
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
  unseal add in
  theorem add_zero : forall (n : Nat), n + zero = n := by
    intro n
    rfl
```
-/
-- /FULL

/- FULL: But the proof that it is also a neutral element on the _left_
   can't be done in the same simple way.  Just applying `rfl` doesn't
   work, since the `n` in `zero + n` is an arbitrary unknown number, so
   the `match` in the definition of `+` can't be simplified. -/
/- TERSE: But the proof that it is also a neutral element on the
   _left_ gets stuck... -/
/- zero_add_firsttry -/
/-- warning: declaration uses `sorry` -/
#guard_msgs in
unseal add in
example : ∀ n : Nat, zero + n = n := by
  intro n
  -- `rfl` doesn't work here!
  sorry

/- TERSE: *** -/

/-
  And reasoning by cases using `cases n` doesn't get us much
  further: the branch of the case analysis where we assume `n = zero`
  goes through just fine, but in the branch where `n = n' + 1` for
  some `n'` we get stuck in exactly the same way.
-/

/- zero_add_secondtry -/
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∀ n : Nat, zero + n = n := by
  intro n
  cases n
  case zero => /- n = zero -/
    rewrite [add_zero]
    rfl
    -- so far so good...
  case succ n' =>   /- n = succ n' -/
    -- ...but we're stuck on zero + n'
    sorry

-- FULL
/-
  We could use `cases n'` to get a bit further, but,
  since `n` can be arbitrarily large, we'll never get all the way
  there if we just go on like this.
-/
-- /FULL

/- TERSE: *** -/

-- FULL
/-
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
-/
-- /FULL

-- TERSE
/-
  We need a bigger hammer: the _principle of induction_ over
  natural numbers...

  - If `P(n)` is some proposition involving a natural number `n`,
  and we want to show that `P` holds for _all_ numbers, we can
  reason like this:

  - show that `P(zero)` holds
  - show that, if `P(n')` holds, then so does `P(succ n')`
  - conclude that `P(n)` holds for all `n`.

  For example...
-/
-- /TERSE

/- TERSE: *** -/

theorem zero_add : ∀ n : Nat, zero + n = n := by
  intro n
  induction n
  case zero => /- n = zero -/
    rewrite [add_zero]
    rfl
  case succ n' ih => /- n = succ n' -/
    /-
      Goal: zero + (succ n') = succ n'
      We can rewrite `zero + (succ n')` to `succ (zero + n')`.
      Then we can rewrite with the induction hypothesis.
    -/
    rewrite [add_succ, ih]
    rfl

-- FULL
/-
  Like `cases`, the `induction` tactic takes a `with` clause
  that specifies the names of the variables to be introduced in the
  subgoals.  Since there are two subgoals (for `zero` and `succ`),
  the `with` clause has two branches.

  In the first subgoal, `n` is replaced by `zero`.  The goal becomes
  `zero + zero = zero`, which follows by `rfl`.

  In the second subgoal, `n` is replaced by `succ n'`, and the
  induction hypothesis `ih : zero + n' = n'` is added to the context.
  The goal becomes `zero + (succ n') = succ n'`.  `add_succ` tells
  us that `a + (succ b) = succ (a + b)`, so `rw [add_succ]`
  transforms the goal to `succ (zero + n') = succ n'`.  Then `rw [ih]`
  rewrites `zero + n'` to `n'`, and the goal becomes `succ n' = succ n'`,
  which closes with reflexivity.
-/
-- /FULL

-- TERSE
/- *** -/
-- /TERSE
-- TERSE
/- Let's try this one together: -/
-- /TERSE

unseal beq in
theorem beq_self : ∀ n : Nat,
    (n == n) = true := by
  -- WORKINCLASS
  intro n
  induction n
  case zero =>
    rewrite [zero_zero_beq_true]; rfl
  case succ n' ih =>
    rewrite [succ_succ_beq]; exact ih
-- /WORKINCLASS

-- FULL
/-
  Up until this point, we have been explicitly writing out all the parameters
  to theorems with ∀s, which makes us introduce them explicitly with `intro` before we
  can use them. A more Lean-idiomatic way is to write them on the left side of the `:`
  in the theorem statement, which introduces them automatically. So, the statement
  of `beq_self` that we just wrote could also be:

  `theorem beq_self (n : Nat) : (n == n) = true := by ...`

  When written this way, we don't need to `intro n` at the start of the proof, as
  `n` will already be in the context when we begin. We will prefer this style going forward.
-/
-- /FULL

-- FULL
-- EX2! (basic_induction)
/-
  Prove the following using induction. You might need previously
  proven results.
-/

theorem zero_mul (n : Nat) :
    zero * n = zero := by
  -- ADMITTED
  induction n
  case zero => rewrite [mul_zero]; rfl
  case succ n' ih =>
    rewrite [mul_succ, ih, add_zero]
    rfl
-- /ADMITTED
-- GRADE_THEOREM zero.5: mul_zero_l

theorem succ_add (n m : Nat) :
    (succ n) + m = succ (n + m) := by
  -- ADMITTED
  induction m
  case zero =>
    rewrite [add_zero, add_zero]
    rfl
  case succ m' ih =>
    rewrite [add_succ, add_succ, ih]
    rfl
-- /ADMITTED
-- GRADE_THEOREM zero.5: succ_add
-- /FULL
-- TERSE
/- *** -/
-- /TERSE
-- TERSE
/-
  Here's another related fact about addition, which we'll
  need later.  (The proof is left as an exercise.)
-/
-- /TERSE

theorem add_comm (n m : Nat) :
    n + m = m + n := by
  -- ADMITTED
  induction m
  case zero =>
    rewrite [add_zero, zero_add]
    rfl
  case succ m' ih =>
    rewrite [add_succ, ih, succ_add]
    rfl
-- /ADMITTED
-- GRADE_THEOREM zero.5: add_comm

theorem add_assoc (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  -- ADMITTED
  induction p
  case zero =>
    rewrite [add_zero, add_zero]
    rfl
  case succ p' ih =>
    rewrite [add_succ, add_succ, add_succ, ih]
    rfl
-- /ADMITTED
-- GRADE_THEOREM 0.5: add_assoc
-- []

-- EX2 (double_plus)
/- Consider the following function, which doubles its argument: -/

-- TODO Rule rewrite
-- ASSUME HIDDEN
@[irreducible]
def double (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ n' => succ (succ (double n'))

unseal double in
theorem double_zero : double zero = zero := by rfl

unseal double in
theorem double_succ : ∀ n, double (succ n) = succ (succ (double n)) := by
  intro n; rfl

-- END ASSUME


/- ## Tip: the `rw` tactic
  As you've probably noticed, a common pattern in Lean proofs is `rewrite [...]`
  followed by `rfl`. There is a tactic that combines these two steps: `rw [...]`
  will automatically close the goal if the rewrite makes the goal true by
  definition. For example, instead of writing

     rewrite [double_zero]; rfl

     We could write :

    rw [double_zero]

    Using `rw` in your proofs is optional, but it will save you time
    (and is better style!).  -/

/- Use induction to prove this simple fact about `double`.
   Experiment with using `rw` instead of `rewrite`as well. -/

theorem double_add (n : Nat) : double n = n + n := by
  -- ADMITTED
  induction n
  case zero =>
    rw [add_zero, double_zero]
  case succ n' ih =>
    rw [double_succ, ih, add_succ, succ_add]
-- /ADMITTED
-- []

-- EX2 (beq_refl)
/-
  The following theorem relates the computational equality `beq` on
  `Nat` with the definitional equality `=` on `Bool`.
-/

unseal beq in
theorem beq_refl (n : Nat) :
    (n == n) = true := by
  -- ADMITTED
  induction n
  case zero => rw [zero_zero_beq_true]
  case succ n' ih => rw [succ_succ_beq, ih]
-- /ADMITTED
-- []

-- HIDE
/-
  Note: we might expect a similar property to hold on
  UNequal [nat]'s:
     Theorem beq_n_n' : forall n n' : nat,
          n ≠ n' ->
          n =? n' = false.
  But it will be a while before we get to terms with what
  [n ≠ n'] really means...
-/
-- /HIDE

-- FULL
-- EX2? (even_succ)
-- TERSE
/-
  Here's a useful theorem that proves `even (n + 1)` flips
  the parity.  This will facilitate proofs by induction on `n`:
-/
-- /TERSE
-- FULL
/-
  One inconvenient aspect of our definition of `even n` is the
  recursive call on `n - two`. This makes proofs about `even n`
  harder when done by induction on `n`, since we may need an
  induction hypothesis about `n - two`. The following lemma gives an
  alternative characterization of `even (succ n)` that works better
  with induction:

  /- ## Tip: Rewriting by definitions
    To expand the body of `even`, use `rewrite [even]` or `rw [even]`. -/
-/
-- /FULL

unseal even in
theorem even_succ (n : Nat) :
    even (succ n) = !even n := by
  -- ADMITTED
  induction n
  case zero =>
    rw [even_zero, even_one]; rfl
  case succ n' ih =>
    rw [even, ih, notb_involutive]
-- /ADMITTED
-- GRADE_THEOREM 1: even_succ
-- []
-- /FULL

-- HIDE
-- QUIZ
/- We've seen that there are goals that [destruct] can't solve but
    [induction] can. What about the other way around? Are there steps
    in a proof that can be solved by pure case analysis ([destruct])
    but not using [induction]?

    (A) No

    (B) Yes
-/
-- /QUIZ
-- /HIDE

/-
  ######################################################################
  # Proofs Within Proofs
-/

-- FULL
/-
  In Lean, as in informal mathematics, large proofs are often
  broken into a sequence of theorems, with later proofs referring to
  earlier theorems.  But sometimes a proof will involve some
  miscellaneous fact that is too trivial and of too little general
  interest to bother giving it its own top-level name.  In such
  cases, it is convenient to be able to simply state and prove the
  required fact "in place".  The `have` tactic allows us to do this.
-/
-- /FULL
-- TERSE
/- New tactic: `have`. -/
-- /TERSE

theorem mult_zero_plus' (n m : Nat) :
    ((zero + n) + zero) * m = n * m := by
  have h : (zero + n) + zero = n := by
    rw [zero_add, add_zero]
  rw [h]

-- FULL
/-
  The `have` tactic introduces a local lemma into the proof.
  We prove it immediately, and then it's available as a hypothesis
  for the rest of the proof.
-/
-- /FULL

/- TERSE: *** -/

-- FULL
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
-- /FULL

/- plus_rearrange_firsttry -/
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

-- TERSE
/-
  ***
  To use `add_comm` at the point where we need it, we can supply
  explicit arguments: `rw [add_comm n m]` tells Lean exactly which
  `+` to rewrite.  (We can also use `have` to establish the specific
  equation we want, then rewrite with it.)
-/
-- /TERSE

theorem plus_rearrange (n m p q : Nat) :
    (n + m) + (p + q) = (m + n) + (p + q) := by
  rw [add_comm n m]

-- FULL
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


-- TODO (DHS): Wasn't this just an exercise? Why are we giving them the solution here?
/- add_assoc' -/
theorem add_assoc' (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  induction p
  case zero => rw [add_zero, add_zero]
  case succ p' ih =>
    rw [add_succ, add_succ, add_succ, ih]

/-
  Lean is perfectly happy with this.  For a human, however, it
  is difficult to make much sense of it.  We can use
  pass arguments to the `add_succ` theorems to show the structure more clearly...
-/
-- JC: This would be a great location to introduce `calc`!

/- add_assoc'' -/
theorem add_assoc'' (n m p : Nat) :
    add n (add m p) = add (add n m) p := by
  induction p
  case zero => /- p = zero -/
    rw [add_zero, add_zero]
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

  - First, suppose `p = zero`.  We must show that

  n + (m + zero) = (n + m) + zero.

  This follows directly from the definition of `+`
  (since `x + zero = x` for any `x`).

  - Next, suppose `p = p' + 1`, where

  n + (m + p') = (n + m) + p'.

  We must now show that

  n + (m + (p' + 1)) = (n + m) + (p' + 1).

  By the definition of `+`, both sides reduce to

  (n + (m + p')) + 1   and   ((n + m) + p') + 1

  respectively, which are equal by the induction hypothesis.
  _Qed_.
-/

-- HIDE
/- MMG: the proof above makes no use of lemmas, so it's hard for
   students to know what to do.  It might be good to also give them a
   sample proof of mult_1_l so they know how to "invoke" things
   they've already proved.  -/
-- /HIDE

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

-- EX2AM? (add_comm_informal)
/-
  Translate your solution for `add_comm` into an informal proof:

  Theorem: Addition is commutative.

  Proof:
-/
-- SOLUTION
/-
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
-/
-- /SOLUTION
-- GRADE_MANUAL 2: add_comm_informal
-- []

-- EX2M? (beq_refl_informal)
/-
  Write an informal proof of the following theorem, using the
  informal proof of `add_assoc` as a model.  Don't just
  paraphrase the Lean tactics into English!

  Theorem: `(n == n) = true` for any `n`.

  Proof:
-/
-- SOLUTION
/-
  By induction on `n`.

  - First, suppose `n = zero`.  We must show `(zero == zero) = true`.  This
  follows directly from the definition of `beq`.

  - Next, suppose `n = n' + 1`, where `(n' == n') = true`.  We
  must show `(n' + 1 == n' + 1) = true`. This
  follows directly from the induction hypothesis and the
  definition of `beq`.
-/
-- /SOLUTION
-- GRADE_MANUAL 2: beq_refl_informal
-- []

-- /FULL
-- TERSE
-- /TERSE
-- HIDEFROMADVANCED
/-

  ######################################################################
  # More Exercises

  Tip: By default, `rewrite` and `rw` rewrite left to right, i.e.,
  they transform the hypothesis or goal being rewritten from the form on
  the left side of the equality to the right side. To rewrite from
  right to left, use `rewrite [← h]` or `rw [← h]`, where `←` is entered
  as `\l` or `\<-`.
-/

-- EX1 (mul_one)
theorem mul_one (p : Nat) :
    one * p = p := by
  -- ADMITTED
  induction p
  case zero => rw [mul_zero]
  case succ p' ih =>
    rw [mul_succ, ih, succ_eq_add_one]
  -- /ADMITTED
-- GRADE_THEOREM 1: mul_one

-- EX2 (mul_one)
theorem mul_two (p : Nat) :
    two * p = p + p := by
  -- ADMITTED
  induction p
  case zero => rw [mul_zero, add_zero]
  case succ p' ih =>
    rw [mul_succ, ih, two_eq_succ_one, succ_eq_add_one, succ_eq_add_one]
    rw [add_assoc, add_assoc, ←add_assoc p' p' one]
    rw [add_comm p' one, add_comm p']
  -- /ADMITTED
  -- GRADE_THEOREM 1: mul_two

-- TERSE
/-
  These additional exercises state facts that will be used in
  later chapters.  We don't need to work them in class.
-/
-- /TERSE

-- EX3! (mul_comm)
/-
  Use `have` (or `rw` with explicit arguments) to help prove
  `add_shuffle3`.  You don't need to use induction yet.
-/


/- ::::full
Note: By default, `rewrite` and `rw` rewrites left-to-right. To rewrite from right
to left, use `rw [← h]`, where `←` is typed as `\l` or `\<-`.
::::
 -/

theorem add_shuffle3 : ∀ n m p : Nat,
    add (add n m) p = add (add n p) m := by
  -- ADMITTED
  intro n m p
  rw [← add_assoc, add_comm m p, add_assoc]
-- /ADMITTED
-- GRADE_THEOREM 1: add_shuffle3

-- QUIETSOLUTION
theorem succ_mul (m n : Nat) :
    (succ n) * m = (n * m) + m := by
  induction m
  case zero => rw [mul_zero, mul_zero, add_zero]
  case succ m ih =>
    rw [mul_succ, ih, add_succ, add_comm _ n,
        add_assoc n _ m, add_comm n, mul_succ, add_succ]
-- /QUIETSOLUTION

/-
  Now prove commutativity of multiplication.
-/

theorem mul_comm (m n : Nat) :
    m * n = n * m := by
  -- ADMITTED
  induction n
  case zero =>
    rw [mul_zero, zero_mul]
  case succ n' ih =>
    rw [mul_succ, ih, succ_mul]
-- /ADMITTED
-- GRADE_THEOREM 2: mul_comm
-- []

-- EX3? (more_exercises)
/-
  Take a piece of paper.  For each of the following theorems, first
  _think_ about whether (a) it can be proved using only
  simplification and rewriting, (b) it also requires case
  analysis (`cases`), or (c) it also requires induction.  Write
  down your prediction.  Then fill in the proof.  (There is no need
  to turn in your piece of paper; this is just to encourage you to
  reflect before you hack!)
-/


theorem ble_refl (n : Nat) :
    ble n n = true := by
  -- ADMITTED
  induction n
  case zero => rw [zero_ble]
  case succ n' ih => rw [succ_ble_succ]; exact ih
-- /ADMITTED

theorem andb_false (b : Bool) :
    (b && false) = false := by
  -- ADMITTED
  cases b
  case false =>
    rw [Bool.false_and]
  case true =>
    rw [Bool.true_and]
-- /ADMITTED

theorem all3_spec (b c : Bool) :
    (b && c) || ((!b) || (!c)) = true := by
  -- ADMITTED
  cases b
  case true => cases c <;> rfl
  case false => rfl
-- /ADMITTED

theorem right_distrib (n m p : Nat) :
    (n + m) * p = (n * p) + (m * p) := by
  -- ADMITTED
  induction p
  case zero => rw [mul_zero, mul_zero, mul_zero, add_zero]
  case succ p' ih =>
    rw [mul_succ, mul_succ, mul_succ, ih]
    rw [add_assoc ((n * p') + (m * p')),
        add_shuffle3 (n * p') (m * p') _,
        add_assoc ((n * p') + n)]
-- /ADMITTED

theorem left_distrib (n m p : Nat) :
    p * (n + m) = (p * n) + (p * m) := by
  -- ADMITTED
  rw [mul_comm p, mul_comm p, mul_comm p]
  rw [right_distrib]
-- /ADMITTED

theorem mul_assoc (n m p : Nat) :
    n * (m * p) = (n * m) * p := by
  -- ADMITTED
  induction p
  case zero => rw [mul_zero, mul_zero, mul_zero]
  case succ p' ih =>
    rw [mul_succ, mul_succ, ← ih, left_distrib]
-- /ADMITTED
-- []

-- FULL
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

@[irreducible]
def incr (m : Bin) : Bin
  -- ADMITDEF
  := match m with
  | .z => .b1 .z
  | .b0 m' => .b1 m'
  | .b1 m' => .b0 (incr m')
  -- /ADMITDEF

unseal incr
theorem incr_z : incr .z = .b1 .z := by rfl  -- ADMITTED
theorem incr_b0 m : incr (.b0 m) = .b1 m := by rfl  -- ADMITTED
theorem incr_b1 m : incr (.b1 m) = .b0 (incr m) := by rfl  -- ADMITTED
seal incr

@[irreducible]
def binToNat (m : Bin) : Nat
  -- ADMITDEF
  := match m with
  | .z => zero
  | .b0 m' => (binToNat m') * two
  | .b1 m' => ((binToNat m') * two) + one
  -- /ADMITDEF

unseal binToNat
theorem binToNat_z : binToNat .z = zero := by rfl  -- ADMITTED
theorem binToNat_b0 m : binToNat (.b0 m) = mul (binToNat m) two := by rfl  -- ADMITTED
theorem binToNat_b1 m : binToNat (.b1 m) = add (mul (binToNat m) two) one := by rfl  -- ADMITTED
seal binToNat

attribute [pp_nodot] Bin.b0 Bin.b1

/-
  In Basics, we did some unit testing of `binToNat`, but we
  didn't prove its correctness. Now we'll do so.
-/

-- EX3! (binary_commute)

/- SOONER (DHS): This is a very-category theoretic way to present
   this idea. Is this the most useful way to convey this to
   an audience who is presumably unfamiliar with commutative diagrams? -/

/-
  Prove that the following diagram commutes:

       incr Bin ----------------------> Bin
           |                             |
binToNat   |                             |  binToNat
           |                             |
           v                             v
          Nat ------------------------> Nat
                      succ

  That is, incrementing a binary number and then converting it to
  a (unary) natural number yields the same result as first converting
  it to a natural number and then incrementing.

  If you want to change your previous definitions of `incr` or `binToNat`
  to make the property easier to prove, feel free to do so!
-/

theorem bin_to_nat_pres_incr (b : Bin) :
    binToNat (incr b) = (binToNat b) + one := by
  -- ADMITTED
  induction b
  case z => rw [incr_z, binToNat_b1, binToNat_z]; rw [zero_mul]
  case b0 b' ih =>
    rw [incr_b0, binToNat_b0, binToNat_b1]
  case b1 b' ih =>
    rw [incr_b1, binToNat_b1, binToNat_b0, ih]
    rw [mul_comm, mul_two, mul_comm, mul_two, add_assoc]
    rw [add_shuffle3 _ one]
-- /ADMITTED
-- GRADE_THEOREM 3: bin_to_nat_pres_incr

-- []

-- EX3 (nat_bin_nat)

/- Write a function to convert natural numbers to binary numbers.
  Also write some simplification lemmas for it.
-/
@[irreducible]
def natToBin (n : Nat) : Bin :=
  -- ADMITDEF
  match n with
  | zero => .z
  | succ n' => incr (natToBin n')
  -- /ADMITDEF

-- TODO (DHS): How to hide these theorem statements so that students can get practice writing them?
/- From GitHub:
CH:
  David set it up so that if you put:
-- SOLUTION
-- END SOLUTION

in an exercise that it will turn into -- FILL IN HERE in both student version of the Lean files and the generated HTML.
BCP: Could they be moved later so that at least the reader has the chance to do the exercise before encountering them?
-/
unseal natToBin
theorem natToBin_zero : natToBin zero = .z := by rfl
theorem natToBin_succ m : natToBin (succ m) = incr (natToBin m) := by rfl
seal natToBin

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

theorem nat_bin_nat (n : Nat) :
    binToNat (natToBin n) = n := by
  -- ADMITTED
  induction n
  case zero =>
    rw [natToBin_zero, binToNat_z]
  case succ n' ih =>
    rw [natToBin_succ, bin_to_nat_pres_incr, ih, ← succ_eq_add_one]
-- /ADMITTED
-- GRADE_THEOREM 3: nat_bin_nat

-- []

/- ## Bin to Nat and Back to Bin (Advanced) -/

/-
  The opposite direction -- starting with a `Bin`, converting to `Nat`,
  then converting back to `Bin` -- turns out to be problematic. That
  is, the following theorem does not hold.
-/

/- bin_nat_bin_fails -/
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∀ b, natToBin (binToNat b) = b := by sorry

/-
  Let's explore why that theorem fails, and how to prove a modified
  version of it. We'll start with some lemmas that might seem
  unrelated, but will turn out to be relevant.
-/

-- EX2A (double_bin)

/-
  Prove this lemma about `double`, which we defined earlier in the
  chapter.
-/

/- double_incr -/
theorem double_incr (n : Nat) :
    double (succ n) = (double n) + two := by
  -- ADMITTED
  rw [double_succ]
  rw [two_eq_succ_one, one_eq_succ_zero, add_succ, add_succ, add_zero]
-- /ADMITTED
-- GRADE_THEOREM 0.5: double_incr

/- Now define a similar doubling function for `Bin`. -/

@[irreducible]
def doubleBin (b : Bin) : Bin :=
  -- ADMITDEF
  match b with
  | .z => .z
  | _ => .b0 b
  -- /ADMITDEF

-- TODO (DHS): How to hide these theorem statements so that students can get practice writing them?
unseal doubleBin
theorem doubleBin_z : doubleBin .z = .z := by rfl -- ADMITTED
theorem doubleBin_b0 m : doubleBin (.b0 m) = .b0 (.b0 m) := by rfl -- ADMITTED
theorem doubleBin_b1 m : doubleBin (.b1 m) = .b0 (.b1 m) := by rfl -- ADMITTED
seal doubleBin

/- Check that your function correctly doubles zero. -/

/- double_bin_zero -/
unseal doubleBin in
example : doubleBin .z = .z := by rfl  -- ADMITTED
-- GRADE_THEOREM zero.5: double_bin_zero

/- Prove this lemma, which corresponds to `double_incr`. -/

/- double_incr_bin -/
theorem double_incr_bin (b : Bin) :
    doubleBin (incr b) = incr (incr (doubleBin b)) := by
  -- ADMITTED
  cases b
  . rw [incr_z, doubleBin_b1, doubleBin_z, incr_z, incr_b1, incr_z]
  . rw [incr_b0, doubleBin_b1, doubleBin_b0, incr_b0, incr_b1, incr_b0]
  . rw [incr_b1, doubleBin_b0, doubleBin_b1, incr_b0, incr_b1, incr_b1]
-- /ADMITTED
-- GRADE_THEOREM 1: double_incr_bin

-- []

/- Let's return to our desired theorem: -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example b : natToBin (binToNat b) = b := by sorry

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

-- SOLUTION
/-
  The problem is that `zero` has many representations: it can be written
  `.z`, `.b0 .z`, `.b0 (.b0 .z)`, and so on.  For these alternate
  representations, if you do `binToNat` then `natToBin`, you
  don't get back what you started with.

  Any other number also has many representations, after applying
  constructors to the multiple representations of zero.
-/
-- /SOLUTION

/-
  To solve that problem, we can introduce a _normalization_ function
  that selects the simplest `Bin` out of all the equivalent
  `Bin`. Then we can prove that the conversion from `Bin` to `Nat` and
  back again produces that normalized, simplest `Bin`.
-/

-- EX4A (bin_nat_bin)

/-
  Define `normalize`. You will need to keep its definition as simple
  as possible for later proofs to go smoothly. Do not use
  `binToNat` or `natToBin`, but do use `doubleBin`.

  Hint: Structure the recursion such that it _always_ reaches the
  end of the `Bin` and _only_ processes each bit once. Do not
  try to "look ahead" at future bits.
-/

@[irreducible]
def normalize (b : Bin) : Bin :=
  -- ADMITDEF
  match b with
  | .z => .z
  | .b0 b' => doubleBin (normalize b')
  | .b1 b' => incr (doubleBin (normalize b'))
  -- /ADMITDEF

-- TODO (DHS): How to hide these theorem statements so that students can get practice writing them?
unseal normalize
theorem normalize_z : normalize .z = .z := by rfl -- ADMITTED
theorem normalize_b0 m : normalize (.b0 m) = doubleBin (normalize m) := by rfl -- ADMITTED
theorem normalize_b1 m : normalize (.b1 m) = incr (doubleBin (normalize m)) := by rfl -- ADMITTED
seal normalize

/-
  It would be wise to do some `example` proofs to check that your
  definition of `normalize` works the way you intend before you
  proceed. They won't be graded, but fill them in below.
-/

-- SOLUTION
/- normalize_test_zero -/
unseal normalize doubleBin incr
example : normalize .z = .z := by rfl
/- normalize_test_1 -/
example : normalize (.b1 .z) = .b1 .z := by rfl
/- normalize_test_2 -/
example : normalize (.b0 .z) = .z := by rfl
/- normalize_test_3 -/
example : normalize (.b0 (.b0 .z)) = .z := by rfl
/- normalize_test_4 -/
example : normalize (.b1 (.b0 .z)) = .b1 .z := by rfl
seal normalize doubleBin incr
-- /SOLUTION

/-
  Finally, prove the main theorem. The inductive cases could be a
  bit tricky.

  Hint: Start by trying to prove the main statement, see where you
  get stuck, and see if you can find a lemma -- perhaps requiring
  its own inductive proof -- that will allow the main proof to make
  progress. We have one lemma for the `b0` case (which also makes
  use of `double_incr_bin`) and another for the `b1` case.
-/

-- SOLUTION
theorem incr_doubleBin (b : Bin) :
    incr (doubleBin b) = .b1 b := by
  cases b
  . rw [doubleBin_z, incr_z]
  . rw [doubleBin_b0, incr_b0]
  . rw [doubleBin_b1, incr_b0]

theorem natToBin_two_mul n :
    natToBin (mul n two) = doubleBin (natToBin n) := by
  induction n
  case zero => rw [zero_mul, natToBin_zero, doubleBin_z]
  case succ n' ih =>
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
-- /SOLUTION

theorem bin_nat_bin (b : Bin) :
    natToBin (binToNat b) = normalize b := by
  -- ADMITTED
  induction b
  case z =>
    rw [binToNat_z, normalize_z, natToBin_zero]
  case b0 b' ih =>
    rw [binToNat_b0, normalize_b0]
    rw [natToBin_two_mul, ih]
  case b1 b' ih =>
    rw [binToNat_b1, normalize_b1]
    /- Goal: natToBin (binToNat b' * 2 + 1) = incr (doubleBin (normalize b')) -/
    rw [← succ_eq_add_one]
    rw [natToBin_succ]
    rw [natToBin_two_mul, ih]
-- /ADMITTED

end NatToBin

-- GRADE_THEOREM 6: bin_nat_bin
-- []
-- /FULL

-- /HIDEFROMADVANCED
-- TERSE
-- /TERSE

end NatPlayground.Nat


-- HIDE
/-
  There is MUCH more that we could say about this topic.  We
  could do a similar example (and pair of exercises) involving
  [cases].  We could talk about references to external theorems.
  Basically, for each tactic, we could give people some guidance
  about how to lay out corresponding informal proofs...  But the
  current direction is to minimize the role of informal proofs (at
  least, the degree to which we try to get people to write them) in
  SF.
-/
-- /HIDE
