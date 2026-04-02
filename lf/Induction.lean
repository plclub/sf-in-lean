-- Induction: Proof by Induction

-- INSTRUCTORS: This file and Basics.lean each take about an hour to
--    get through in a not-too-rushed fashion (with questions, etc.).

-- HIDEFROMHTML
-- FULL
-- REMINDER:
--
--          #####################################################
--          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
--          #####################################################
--
--   (See the [Preface] for why.)
-- /FULL
-- /HIDEFROMHTML

-- ######################################################################
-- * Separate Compilation

-- TERSE: Lean will first need to compile `Basics.lean` so it can be
--    imported here -- detailed instructions are in the full version of
--    this chapter...
-- FULL: Before getting started on this chapter, we need to import
--    all of our definitions from the previous chapter:

import lf.Basics

-- FULL: For this `import` to work, Lean needs to be able to find a
--    compiled version of the previous chapter (`Basics.lean`).  This
--    compiled version, called `Basics.olean`, is analogous to the
--    `.class` files compiled from `.java` source files and the `.o`
--    files compiled from `.c` files.
--
--    When using Lake (Lean's build system), the `lakefile.lean` file
--    specifies dependencies and build configuration.  Running `lake build`
--    will compile all necessary files in the correct order.
--
--    If you are using VS Code with the Lean 4 extension, compilation
--    happens automatically in the background.  When you open a file, the
--    extension will compile its dependencies as needed.
--
--    Troubleshooting:
--
--     - If you get complaints about missing imports, make sure you have
--       run `lake build` from the project root directory at least once.
--
--     - If you modify `Basics.lean`, VS Code will automatically
--       recompile it when you save.  You may need to reopen this file
--       or wait for recompilation to finish.
--
--     - If you get errors that seem inconsistent with the source, try
--       running `lake clean` followed by `lake build` to recompile
--       everything from scratch.
-- /FULL

-- TERSE:
-- ######################################################################
-- * Review
-- /TERSE
-- QUIZ
-- To prove the following theorem, which tactics will we need besides
-- `intro` and `rfl`?  (A) none, (B) `rw`, (C) `cases`, (D) both
-- `rw` and `cases`, or (E) can't be done with the tactics we've seen.
--
--     theorem review1 : (true || false) = true
--
-- HIDE
-- review1
theorem review1 : (true || false) = true := by rfl
-- /HIDE
-- /QUIZ
-- QUIZ
-- What about the next one?
--
--     theorem review2 : ∀ b, (true || b) = true
--
-- Which tactics do we need besides `intro` and `rfl`?  (A)
-- none (B) `rw`, (C) `cases`, (D) both `rw` and `cases`,
-- or (E) can't be done with the tactics we've seen.
--
-- HIDE
-- review2
theorem review2 : ∀ b, (true || b) = true := by
  intro b; rfl
-- /HIDE
-- /QUIZ
-- QUIZ
-- What if we change the order of the arguments of `||`?
--
--     theorem review3 : ∀ b, (b || true) = true
--
-- Which tactics do we need besides `intro` and `rfl`?  (A)
-- none (B) `rw`, (C) `cases`, (D) both `rw` and `cases`,
-- or (E) can't be done with the tactics we've seen.
--
-- HIDE
-- review3
theorem review3 : ∀ b, (b || true) = true := by
  intro b; cases b with
  | true => rfl
  | false => rfl
-- /HIDE
-- /QUIZ
-- QUIZ
-- What about this one?  (Recall that in Lean, `Nat.add` recurses on
-- the _second_ argument: `n + 0 = n` by definition, and
-- `n + (m + 1) = (n + m) + 1` by definition.)
--
--     theorem review4 : ∀ n : Nat, n + 0 = n
--
-- (A) none, (B) `rw`, (C) `cases`, (D) both `rw` and `cases`,
-- or (E) can't be done with the tactics we've seen.
--
-- HIDE
-- review4
theorem review4 : ∀ n : Nat, n + 0 = n := by
  intro n; rfl
-- /HIDE
-- /QUIZ
-- QUIZ
-- What about this?
--
--     theorem review5 : ∀ n : Nat, 0 + n = n
--
-- (A) none, (B) `rw`, (C) `cases`, (D) both `rw` and `cases`,
-- or (E) can't be done with the tactics we've seen.
--
-- HIDE
-- review5
-- This one CANNOT be proved by rfl, cases, or rewriting alone --
-- it needs induction!  (We'll see why below.)
-- /HIDE
-- /QUIZ

-- ######################################################################
-- * Proof by Induction

-- FULL: In Lean, `Nat.add` is defined to recurse on its _second_
-- argument:
--
--     protected def Nat.add : Nat → Nat → Nat
--       | n, 0     => n
--       | n, m + 1 => (Nat.add n m) + 1
--
-- This means `n + 0` reduces to `n` by definition, but `0 + n` does
-- _not_.  (This is the opposite of Rocq, where addition recurses on
-- the first argument.)
--
-- We can prove that `0` is a neutral element for `+` on the _right_
-- using just `rfl`:
-- /FULL

-- add_0_r_easy
example : ∀ n : Nat, n + 0 = n := by
  intro n; rfl

-- But the proof that `0` is also a neutral element on the _left_ ...

-- add_0_l_firsttry
theorem add_0_l_firsttry : ∀ n : Nat,
  0 + n = n := by
-- TERSE: ... gets stuck.
-- FULL:
-- ... can't be done in the same simple way.  Just applying
-- `rfl` doesn't work, since the `n` in `0 + n` is an arbitrary
-- unknown number, so the `match` in the definition of `+` can't be
-- simplified (because `+` pattern-matches on its second argument,
-- not its first).
-- /FULL
  intro n
  -- `rfl` doesn't work here!
  sorry

-- TERSE: ***

-- And reasoning by cases using `cases n` doesn't get us much
-- further: the branch of the case analysis where we assume `n = 0`
-- goes through just fine, but in the branch where `n = n' + 1` for
-- some `n'` we get stuck in exactly the same way.

-- add_0_l_secondtry
theorem add_0_l_secondtry : ∀ n : Nat,
  0 + n = n := by
  intro n
  cases n with
  | zero => -- n = 0
    rfl -- so far so good...
  | succ n' => -- n = n' + 1
    -- 0 + (n' + 1) reduces to (0 + n') + 1 ...but we're stuck on 0 + n'
    sorry

-- FULL: We could use `cases n'` to get a bit further, but,
-- since `n` can be arbitrarily large, we'll never get all the way
-- there if we just go on like this.

-- TERSE: ***

-- FULL: To prove interesting facts about numbers, lists, and other
-- inductively defined sets, we often need a more powerful reasoning
-- principle: _induction_.
--
-- Recall (from a discrete math course, probably) the _principle of
-- induction over natural numbers_: If `P(n)` is some proposition
-- involving a natural number `n` and we want to show that `P` holds for
-- all numbers `n`, we can reason like this:
--      - show that `P(0)` holds;
--      - show that, for any `n'`, if `P(n')` holds, then so does
--        `P(n' + 1)`;
--      - conclude that `P(n)` holds for all `n`.
--
-- In Lean, the steps are the same: we begin with the goal of proving
-- `P(n)` for all `n` and use the `induction` tactic to break it down
-- into two separate subgoals: one where we must show `P(0)` and another
-- where we must show `P(n') → P(n' + 1)`.  Here's how this works for
-- the theorem at hand...

-- TERSE: We need a bigger hammer: the _principle of induction_ over
-- natural numbers...
--
--   - If `P(n)` is some proposition involving a natural number `n`,
--     and we want to show that `P` holds for _all_ numbers, we can
--     reason like this:
--
--      - show that `P(0)` holds
--      - show that, if `P(n')` holds, then so does `P(n' + 1)`
--      - conclude that `P(n)` holds for all `n`.
--
-- For example...

-- TERSE: ***

-- Since `+` recurses on the second argument, it is natural to do
-- induction on `n` (the second argument of `0 + n`):

theorem add_0_l : ∀ n : Nat, 0 + n = n := by
  intro n
  induction n with
  | zero => -- n = 0
    rfl
  | succ n' ih => -- n = n' + 1
    -- Goal: 0 + (n' + 1) = n' + 1
    -- By definition of +, `0 + (n' + 1)` reduces to `(0 + n') + 1`.
    -- We can use `Nat.add_succ` to make this explicit, then rewrite
    -- with the induction hypothesis.
    rw [Nat.add_succ, ih]

-- FULL: Like `cases`, the `induction` tactic takes a `with` clause
-- that specifies the names of the variables to be introduced in the
-- subgoals.  Since there are two subgoals (for `zero` and `succ`),
-- the `with` clause has two branches.
--
-- In the first subgoal, `n` is replaced by `0`.  The goal becomes
-- `0 + 0 = 0`, which follows by `rfl`.
--
-- In the second subgoal, `n` is replaced by `n' + 1`, and the
-- induction hypothesis `ih : 0 + n' = n'` is added to the context.
-- The goal becomes `0 + (n' + 1) = n' + 1`.  `Nat.add_succ` tells
-- us that `a + (b + 1) = (a + b) + 1`, so `rw [Nat.add_succ]`
-- transforms the goal to `(0 + n') + 1 = n' + 1`.  Then `rw [ih]`
-- rewrites `0 + n'` to `n'`, and the goal becomes `n' + 1 = n' + 1`,
-- which closes automatically.

-- TERSE: ***
-- TERSE: Let's try this one together:

theorem minus_n_n : ∀ n,
  n - n = 0 := by
  -- WORKINCLASS
  intro n
  induction n with
  | zero =>
    rfl
  | succ n' ih =>
    -- Goal: (n' + 1) - (n' + 1) = 0
    -- By definition of Nat.sub, this reduces to n' - n' = 0,
    -- which is exactly our induction hypothesis.
    simp
-- /WORKINCLASS

-- FULL: (The use of the `intro` tactic in these proofs is actually
-- redundant.  When applied to a goal that contains quantified
-- variables, the `induction` tactic will automatically move them
-- into the context as needed.)

-- FULL
-- EX2! (basic_induction)
-- Prove the following using induction. You might need previously
-- proven results.

-- In Lean, `n * 0 = 0` is true by definition (since `Nat.mul` also
-- recurses on the second argument).  The interesting direction is
-- `0 * n = 0`:

theorem mul_0_l : ∀ n : Nat,
  0 * n = 0 := by
  -- ADMITTED
  intro n
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [Nat.mul_succ, ih]
-- /ADMITTED
-- GRADE_THEOREM 0.5: mul_0_l

-- Similarly, in Lean `n + (m + 1) = (n + m) + 1` is true by
-- definition (since `+` recurses on its second argument).  The
-- interesting direction is the reverse:

theorem succ_add : ∀ n m : Nat,
  (n + 1) + m = (n + m) + 1 := by
  -- ADMITTED
  intro n m
  induction m with
  | zero => rfl
  | succ m' ih =>
    -- Goal: (n + 1) + (m' + 1) = (n + (m' + 1)) + 1
    -- Both sides get a "+1" from the definition of +.
    -- `simp only` is like `simp` but uses ONLY the lemmas you list,
    -- rather than also trying everything in the default set.
    simp only [Nat.add_succ]
    rw [ih]
-- /ADMITTED
-- GRADE_THEOREM 0.5: succ_add
-- /FULL
-- TERSE: ***
-- TERSE: Here's another related fact about addition, which we'll
--    need later.  (The proof is left as an exercise.)

theorem add_comm : ∀ n m : Nat,
  n + m = m + n := by
  -- ADMITTED
  intro n m
  induction m with
  | zero =>
    -- n + 0 = 0 + n.  n + 0 = n by def.  0 + n = n by add_0_l.
    rw [Nat.add_zero, add_0_l]
  | succ m' ih =>
    -- n + (m' + 1) = (m' + 1) + n
    -- LHS reduces to (n + m') + 1. By ih, n + m' = m' + n.
    -- So LHS = (m' + n) + 1.  RHS = (m' + 1) + n = (m' + n) + 1 by succ_add.
    rw [Nat.add_succ, ih, succ_add]
-- /ADMITTED
-- GRADE_THEOREM 0.5: add_comm
-- FULL

theorem add_assoc : ∀ n m p : Nat,
  n + (m + p) = (n + m) + p := by
  -- ADMITTED
  intro n m p
  induction p with
  | zero => rfl
  | succ p' ih =>
    -- Goal: n + (m + (p' + 1)) = (n + m) + (p' + 1)
    -- By def of +, both m + (p' + 1) and (n + m) + (p' + 1) peel off a +1.
    rw [Nat.add_succ, Nat.add_succ, Nat.add_succ, ih]
-- /ADMITTED
-- GRADE_THEOREM 0.5: add_assoc
-- []

-- EX2 (double_plus)
-- Consider the following function, which doubles its argument:

def double (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => (double n') + 2

-- Use induction to prove this simple fact about `double`:

-- double_plus
theorem double_plus : ∀ n, double n = n + n := by
  -- ADMITTED
  intro n
  induction n with
  | zero => rfl
  | succ n' ih =>
    -- double (n' + 1) = (double n') + 2 by def.
    -- By ih: = (n' + n') + 2.
    -- Goal RHS: (n' + 1) + (n' + 1).
    -- By succ_add: (n' + 1) + (n' + 1) = (n' + (n' + 1)) + 1
    --           = ((n' + n') + 1) + 1 (by Nat.add_succ)
    --           = (n' + n') + 2 (definitionally).
    simp only [double, ih]
    rw [succ_add n' (n' + 1), Nat.add_succ n' n']
-- /ADMITTED
-- []
-- /FULL

-- TERSE: ***
-- EX2 (eqb_refl)
-- The following theorem relates the computational equality `BEq` on
-- `Nat` with the definitional equality `=` on `Bool`.

theorem eqb_refl : ∀ n : Nat,
  (n == n) = true := by
  -- ADMITTED
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => simp
-- /ADMITTED
-- []

-- FULL
-- EX2? (even_S)
-- TERSE: Here's a useful theorem that proves `even (n + 1)` flips
-- the parity.  This will facilitate proofs by induction on `n`:
-- FULL: One inconvenient aspect of our definition of `even n` is the
-- recursive call on `n - 2`. This makes proofs about `even n`
-- harder when done by induction on `n`, since we may need an
-- induction hypothesis about `n - 2`. The following lemma gives an
-- alternative characterization of `even (n + 1)` that works better
-- with induction:

theorem even_S : ∀ n : Nat,
  even (n + 1) = !even n := by
  -- ADMITTED
  intro n
  induction n with
  | zero => rfl
  | succ n' ih =>
    -- even ((n' + 1) + 1) = !even (n' + 1)
    -- (n' + 1) + 1 = n' + 2, so even (n' + 2) = even n' by def.
    -- !even (n' + 1) = !(!(even n')) = even n' by ih and Bool.not_not.
    simp [even, ih, Bool.not_not]
-- /ADMITTED
-- GRADE_THEOREM 1: even_S
-- []
-- /FULL

-- ######################################################################
-- * Proofs Within Proofs

-- FULL: In Lean, as in informal mathematics, large proofs are often
-- broken into a sequence of theorems, with later proofs referring to
-- earlier theorems.  But sometimes a proof will involve some
-- miscellaneous fact that is too trivial and of too little general
-- interest to bother giving it its own top-level name.  In such
-- cases, it is convenient to be able to simply state and prove the
-- required fact "in place".  The `have` tactic allows us to do this.
-- TERSE: New tactic: `have`.

theorem mult_0_plus' : ∀ n m : Nat,
  (n + 0 + 0) * m = n * m := by
  intro n m
  have h : n + 0 + 0 = n := by rfl
  rw [h]

-- FULL: The `have` tactic introduces a local lemma into the proof.
-- We prove it immediately, and then it's available as a hypothesis
-- for the rest of the proof.  This is similar in spirit to Rocq's
-- `replace` or `assert` tactics.

-- TERSE: ***

-- FULL: As another example, suppose we want to prove that `(n + m)
-- + (p + q) = (m + n) + (p + q)`. The only difference between the
-- two sides of the `=` is that the arguments `m` and `n` to the
-- first inner `+` are swapped, so it seems we should be able to use
-- the commutativity of addition (`add_comm`) to rewrite one into the
-- other.  However, the `rw` tactic is not very smart about _where_
-- it applies the rewrite.  There are three uses of `+` here, and
-- `rw [add_comm]` may affect the wrong one...

-- plus_rearrange_firsttry
theorem plus_rearrange_firsttry : ∀ n m p q : Nat,
  (n + m) + (p + q) = (m + n) + (p + q) := by
  intro n m p q
  -- We just need to swap (n + m) for (m + n)... seems
  -- like add_comm should do the trick!
  -- But `rw [add_comm]` might rewrite the wrong `+`!
  sorry

-- TERSE: ***
-- To use `add_comm` at the point where we need it, we can supply
-- explicit arguments: `rw [add_comm n m]` tells Lean exactly which
-- `+` to rewrite.  (We can also use `have` to establish the specific
-- equation we want, then rewrite with it.)

theorem plus_rearrange : ∀ n m p q : Nat,
  (n + m) + (p + q) = (m + n) + (p + q) := by
  intro n m p q
  rw [add_comm n m]

-- FULL
-- ######################################################################
-- * Formal vs. Informal Proof

-- "Informal proofs are algorithms; formal proofs are code."

-- What constitutes a successful proof of a mathematical claim?
--
-- The question has challenged philosophers for millennia, but a
-- rough and ready answer could be this: A proof of a mathematical
-- proposition `P` is a written (or spoken) text that instills in the
-- reader or hearer the certainty that `P` is true -- an unassailable
-- argument for the truth of `P`.  That is, a proof is an act of
-- communication.
--
-- Acts of communication may involve different sorts of readers.  On
-- one hand, the "reader" can be a program like Lean, in which case
-- the "belief" that is instilled is that `P` can be mechanically
-- derived from a certain set of formal logical rules, and the proof
-- is a recipe that guides the program in checking this fact.  Such
-- recipes are _formal_ proofs.
--
-- Alternatively, the reader can be a human being, in which case the
-- proof will probably be written in English or some other natural
-- language and will thus necessarily be _informal_.  Here, the
-- criteria for success are less clearly specified.  A "valid" proof
-- is one that makes the reader believe `P`.  But the same proof may
-- be read by many different readers, some of whom may be convinced
-- by a particular way of phrasing the argument, while others may not
-- be. Some readers may be particularly pedantic, inexperienced, or
-- just plain thick-headed; the only way to convince them will be to
-- make the argument in painstaking detail.  Other readers, more
-- familiar in the area, may find all this detail so overwhelming
-- that they lose the overall thread; all they want is to be told the
-- main ideas, since it is easier for them to fill in the details for
-- themselves than to wade through a written presentation of them.
-- Ultimately, there is no universal standard, because there is no
-- single way of writing an informal proof that will convince every
-- conceivable reader.
--
-- In practice, however, mathematicians have developed a rich set of
-- conventions and idioms for writing about complex mathematical
-- objects that -- at least within a certain community -- make
-- communication fairly reliable.  The conventions of this stylized
-- form of communication give a reasonably clear standard for judging
-- proofs good or bad.
--
-- Because we are using Lean in this course, we will be working
-- heavily with formal proofs.  But this doesn't mean we can
-- completely forget about informal ones!  Formal proofs are useful
-- in many ways, but they are _not_ very efficient ways of
-- communicating ideas between human beings.

-- For example, here is a proof that addition is associative:

-- add_assoc'
theorem add_assoc' : ∀ n m p : Nat,
  n + (m + p) = (n + m) + p := by
  intro n m p; induction p with
  | zero => rfl
  | succ p' ih =>
    rw [Nat.add_succ, Nat.add_succ, Nat.add_succ, ih]

-- Lean is perfectly happy with this.  For a human, however, it
-- is difficult to make much sense of it.  We can use comments and
-- focused cases to show the structure a little more clearly...

-- add_assoc''
theorem add_assoc'' : ∀ n m p : Nat,
  n + (m + p) = (n + m) + p := by
  intro n m p
  induction p with
  | zero => -- p = 0
    rfl
  | succ p' ih => -- p = p' + 1
    rw [Nat.add_succ, Nat.add_succ, Nat.add_succ, ih]

-- ... and if you're used to Lean you might be able to step
-- through the tactics one after the other in your mind and imagine
-- the state of the context and goal stack at each point, but if the
-- proof were even a little bit more complicated this would be next
-- to impossible.
--
-- A (pedantic) mathematician might write the proof something like
-- this:

-- - _Theorem_: For any `n`, `m` and `p`,
--
--       n + (m + p) = (n + m) + p.
--
--   _Proof_: By induction on `p`.
--
--   - First, suppose `p = 0`.  We must show that
--
--         n + (m + 0) = (n + m) + 0.
--
--     This follows directly from the definition of `+`
--     (since `x + 0 = x` for any `x`).
--
--   - Next, suppose `p = p' + 1`, where
--
--         n + (m + p') = (n + m) + p'.
--
--     We must now show that
--
--         n + (m + (p' + 1)) = (n + m) + (p' + 1).
--
--     By the definition of `+`, both sides reduce to
--
--         (n + (m + p')) + 1   and   ((n + m) + p') + 1
--
--     respectively, which are equal by the induction hypothesis.
--     _Qed_.

-- The overall form of the proof is basically similar, and of
-- course this is no accident: Lean has been designed so that its
-- `induction` tactic generates the same sub-goals, in the same
-- order, as the bullet points that a mathematician would usually
-- write.  But there are significant differences of detail: the
-- formal proof is much more explicit in some ways (e.g., the use of
-- `rfl`) but much less explicit in others (in particular, the "proof
-- state" at any given point in the Lean proof is completely implicit,
-- whereas the informal proof reminds the reader several times where
-- things stand).

-- EX2AM? (add_comm_informal)
-- Translate your solution for `add_comm` into an informal proof:
--
-- Theorem: Addition is commutative.
--
-- Proof: -- SOLUTION
--    Let natural numbers `n` and `m` be given.  We show `n + m = m +
--    n` by induction on `m`.
--
--    - First, suppose `m = 0`.  We must show `n + 0 = 0 + n`.  By
--      the definition of `+`, `n + 0 = n`.  We have already shown
--      (lemma `add_0_l`) that `0 + n = n`.  Thus both sides equal
--      `n`.
--
--    - Next, suppose `m = m' + 1` for some `m'`, where `n + m' = m'
--      + n`.  We must show that `n + (m' + 1) = (m' + 1) + n`.  By
--      the definition of `+`, `n + (m' + 1) = (n + m') + 1`.  By
--      `succ_add`, `(m' + 1) + n = (m' + n) + 1`.  By the induction
--      hypothesis, `n + m' = m' + n`, so both sides equal
--      `(m' + n) + 1`.
-- /SOLUTION
--
-- GRADE_MANUAL 2: add_comm_informal
-- []

-- EX2M? (eqb_refl_informal)
-- Write an informal proof of the following theorem, using the
-- informal proof of `add_assoc` as a model.  Don't just
-- paraphrase the Lean tactics into English!
--
-- Theorem: `(n == n) = true` for any `n`.
--
-- Proof: -- SOLUTION
--    By induction on `n`.
--
--    - First, suppose `n = 0`.  We must show `(0 == 0) = true`.  This
--      follows directly from the definition of `BEq` on `Nat`.
--
--    - Next, suppose `n = n' + 1`, where `(n' == n') = true`.  We
--      must show `(n' + 1 == n' + 1) = true`. This
--      follows directly from the induction hypothesis and the
--      definition of `BEq` on `Nat`.
-- /SOLUTION
--
-- GRADE_MANUAL 2: eqb_refl_informal
-- []

-- /FULL
-- TERSE: HIDEFROMHTML
-- HIDEFROMADVANCED
-- ######################################################################
-- * More Exercises

-- TERSE: These additional exercises state facts that will be used in
-- later chapters.  We don't need to work them in class.

-- EX3! (mul_comm)
-- Use `have` (or `rw` with explicit arguments) to help prove
-- `add_shuffle3`.  You don't need to use induction yet.

theorem add_shuffle3 : ∀ n m p : Nat,
  n + (m + p) = m + (n + p) := by
  -- ADMITTED
  intro n m p
  rw [add_assoc, add_comm n m, ← add_assoc]
-- /ADMITTED
-- GRADE_THEOREM 1: add_shuffle3
-- QUIETSOLUTION
theorem mult_m_Sn : ∀ m n : Nat,
  m * (n + 1) = m + (m * n) := by
  intro m n
  rw [Nat.mul_succ, add_comm]
-- /QUIETSOLUTION

-- Now prove commutativity of multiplication.  You will probably want
-- to look for (or define and prove) a "helper" theorem to be used in
-- the proof of this one. Hint: what is `n * (1 + k)`?

theorem mul_comm : ∀ m n : Nat,
  m * n = n * m := by
  -- ADMITTED
  intro m n
  induction n with
  | zero =>
    -- m * 0 = 0 * m.  m * 0 = 0 by def.  0 * m = 0 by mul_0_l.
    rw [Nat.mul_zero, mul_0_l]
  | succ n' ih =>
    -- m * (n' + 1) = (n' + 1) * m
    -- By Nat.mul_succ: m * (n' + 1) = m * n' + m
    -- By Nat.succ_mul (or our mult_m_Sn reversed):
    --   (n' + 1) * m = m + n' * m
    -- By ih: m * n' = n' * m, so m * n' + m = n' * m + m.
    -- Need: n' * m + m = m + n' * m.  That's add_comm.
    rw [Nat.mul_succ, Nat.succ_mul, ih]
-- /ADMITTED
-- GRADE_THEOREM 2: mul_comm
-- []

-- EX3? (more_exercises)
-- Take a piece of paper.  For each of the following theorems, first
-- _think_ about whether (a) it can be proved using only
-- simplification and rewriting, (b) it also requires case
-- analysis (`cases`), or (c) it also requires induction.  Write
-- down your prediction.  Then fill in the proof.  (There is no need
-- to turn in your piece of paper; this is just to encourage you to
-- reflect before you hack!)

theorem leb_refl : ∀ n : Nat,
  Nat.ble n n = true := by
  -- ADMITTED
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => simp [Nat.ble, ih]
-- /ADMITTED

theorem zero_neqb_S : ∀ n : Nat,
  (0 == (n + 1)) = false := by
  -- ADMITTED
  intro n; rfl
-- /ADMITTED

theorem andb_false_r : ∀ b : Bool,
  (b && false) = false := by
  -- ADMITTED
  intro b; cases b with
  | true => rfl
  | false => rfl
-- /ADMITTED

theorem S_neqb_0 : ∀ n : Nat,
  ((n + 1) == 0) = false := by
  -- ADMITTED
  intro n; rfl
-- /ADMITTED

theorem mult_1_l : ∀ n : Nat, 1 * n = n := by
  -- ADMITTED
  intro n
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [Nat.mul_succ, ih]
-- /ADMITTED

theorem all3_spec : ∀ b c : Bool,
  (b && c) || ((!b) || (!c)) = true := by
  -- ADMITTED
  intro b c; cases b with
  | true => cases c with
    | true => rfl
    | false => rfl
  | false => rfl
-- /ADMITTED

theorem mult_plus_distr_r : ∀ n m p : Nat,
  (n + m) * p = (n * p) + (m * p) := by
  -- ADMITTED
  intro n m p
  induction p with
  | zero => rfl
  | succ p' ih =>
    -- (n + m) * (p' + 1) = n * (p' + 1) + m * (p' + 1)
    -- By Nat.mul_succ on each:
    --   LHS = (n + m) * p' + (n + m)
    --   RHS = (n * p' + n) + (m * p' + m)
    -- By ih: (n + m) * p' = n * p' + m * p'.
    -- Need: (n * p' + m * p') + (n + m) = (n * p' + n) + (m * p' + m)
    rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_succ, ih]
    -- Rearrange: (n*p' + m*p') + (n + m) = (n*p' + n) + (m*p' + m)
    rw [← add_assoc (n * p') (m * p') (n + m)]
    rw [add_shuffle3 (m * p') n m]
    rw [add_assoc (n * p') n (m * p' + m)]
-- /ADMITTED

theorem mult_assoc : ∀ n m p : Nat,
  n * (m * p) = (n * m) * p := by
  -- ADMITTED
  intro n m p
  induction p with
  | zero => rfl
  | succ p' ih =>
    -- n * (m * (p' + 1)) = (n * m) * (p' + 1)
    -- By Nat.mul_succ: m * (p' + 1) = m * p' + m
    -- So LHS = n * (m * p' + m)
    -- By Nat.left_distrib: = n * (m * p') + n * m
    -- By ih: n * (m * p') = (n * m) * p'
    -- So LHS = (n * m) * p' + n * m
    -- By Nat.mul_succ: (n * m) * (p' + 1) = (n * m) * p' + (n * m). ✓
    rw [Nat.mul_succ, Nat.mul_succ, Nat.left_distrib, ih]
-- /ADMITTED
-- []

-- FULL
-- * Nat to Bin and Back to Nat

-- Recall the `Bin` type we defined in Basics:

-- (The `Bin` type, `incr`, and `binToNat` are imported from Basics.)

-- Before you start working on the next exercise, replace the stub
-- definitions of `incr` and `binToNat`, below, with your solution
-- from Basics.  That will make it possible for this file to be graded
-- on its own.
--
-- (In Lean, since we `import Basics`, these definitions are already
-- available.  No need to copy them.)

-- In Basics, we did some unit testing of `binToNat`, but we
-- didn't prove its correctness. Now we'll do so.

-- EX3! (binary_commute)
-- Prove that the following diagram commutes:
--
--                             incr
--               Bin ----------------------> Bin
--                |                           |
--     binToNat  |                           |  binToNat
--                |                           |
--                v                           v
--               Nat ----------------------> Nat
--                            + 1
--
-- That is, incrementing a binary number and then converting it to
-- a (unary) natural number yields the same result as first converting
-- it to a natural number and then incrementing.
--
-- If you want to change your previous definitions of `incr` or `binToNat`
-- to make the property easier to prove, feel free to do so!

theorem bin_to_nat_pres_incr : ∀ b : Bin,
  binToNat (incr b) = binToNat b + 1 := by
  -- ADMITTED
  intro b
  induction b with
  | z => rfl
  | b0 b' ih =>
    -- incr (.b0 b') = .b1 b'
    -- binToNat (.b1 b') = 1 + 2 * binToNat b'
    -- binToNat (.b0 b') + 1 = 2 * binToNat b' + 1
    -- Need: 1 + 2 * binToNat b' = 2 * binToNat b' + 1
    simp only [incr, binToNat]
    rw [Nat.add_comm]
  | b1 b' ih =>
    -- incr (.b1 b') = .b0 (incr b')
    -- binToNat (.b0 (incr b')) = 2 * binToNat (incr b')
    -- By ih: binToNat (incr b') = binToNat b' + 1
    -- So LHS = 2 * (binToNat b' + 1) = 2 * binToNat b' + 2
    -- RHS: binToNat (.b1 b') + 1 = (1 + 2 * binToNat b') + 1
    -- Need: 2 * binToNat b' + 2 = (1 + 2 * binToNat b') + 1
    simp only [incr, binToNat, ih, Nat.mul_succ]
    rw [Nat.add_comm 1 (2 * binToNat b')]
-- /ADMITTED
-- GRADE_THEOREM 3: bin_to_nat_pres_incr

-- []

-- EX3 (nat_bin_nat)

-- Write a function to convert natural numbers to binary numbers.

def natToBin (n : Nat) : Bin :=
  -- ADMITDEF
  match n with
  | 0 => .z
  | n' + 1 => incr (natToBin n')
  -- /ADMITDEF

-- Prove that, if we start with any `Nat`, convert it to `Bin`, and
-- convert it back, we get the same `Nat` which we started with.
--
-- Hint: This proof should go through smoothly using the previous
-- exercise about `incr` as a lemma. If not, revisit your definitions
-- of the functions involved and consider whether they are more
-- complicated than necessary: the shape of a proof by induction will
-- match the recursive structure of the program being verified, so
-- make the recursions as simple as possible.

theorem nat_bin_nat : ∀ n, binToNat (natToBin n) = n := by
  -- ADMITTED
  intro n
  induction n with
  | zero => rfl
  | succ n' ih =>
    -- natToBin (n' + 1) = incr (natToBin n')
    -- binToNat (incr (natToBin n')) = binToNat (natToBin n') + 1 by pres_incr
    -- = n' + 1 by ih.  ✓
    simp only [natToBin, bin_to_nat_pres_incr, ih]
-- /ADMITTED
-- GRADE_THEOREM 3: nat_bin_nat

-- []

-- * Bin to Nat and Back to Bin (Advanced)

-- The opposite direction -- starting with a `Bin`, converting to `Nat`,
-- then converting back to `Bin` -- turns out to be problematic. That
-- is, the following theorem does not hold.

-- bin_nat_bin_fails
-- theorem bin_nat_bin_fails : ∀ b, natToBin (binToNat b) = b := by sorry

-- Let's explore why that theorem fails, and how to prove a modified
-- version of it. We'll start with some lemmas that might seem
-- unrelated, but will turn out to be relevant.

-- EX2A (double_bin)

-- Prove this lemma about `double`, which we defined earlier in the
-- chapter.

-- double_incr
theorem double_incr : ∀ n : Nat, double (n + 1) = (double n) + 2 := by
  -- ADMITTED
  intro n; rfl
-- /ADMITTED
-- GRADE_THEOREM 0.5: double_incr

-- Now define a similar doubling function for `Bin`.

def doubleBin (b : Bin) : Bin :=
  -- ADMITDEF
  match b with
  | .z => .z
  | _ => .b0 b
  -- /ADMITDEF

-- Check that your function correctly doubles zero.

-- double_bin_zero
example : doubleBin .z = .z := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: double_bin_zero

-- Prove this lemma, which corresponds to `double_incr`.

-- double_incr_bin
theorem double_incr_bin : ∀ b,
    doubleBin (incr b) = incr (incr (doubleBin b)) := by
  -- ADMITTED
  intro b
  cases b with
  | z => rfl
  | b0 _ => rfl
  | b1 _ => rfl
-- /ADMITTED
-- GRADE_THEOREM 1: double_incr_bin

-- []

-- Let's return to our desired theorem:

-- bin_nat_bin_fails2
-- theorem bin_nat_bin_fails2 : ∀ b, natToBin (binToNat b) = b := by sorry

-- The theorem fails because there are some `Bin` such that we won't
-- necessarily get back to the _original_ `Bin`, but instead to an
-- "equivalent" `Bin`.  (We deliberately leave that notion undefined
-- here for you to think about.)
--
-- Explain in a comment, below, why this failure occurs. Your
-- explanation will not be graded, but it's important that you get it
-- clear in your mind before going on to the next part. If you're
-- stuck on this, think about alternative implementations of
-- `doubleBin` that might have failed to satisfy `double_bin_zero`
-- yet otherwise seem correct.

-- SOLUTION
-- The problem is that `0` has many representations: it can be written
-- `.z`, `.b0 .z`, `.b0 (.b0 .z)`, and so on.  For these alternate
-- representations, if you do `binToNat` then `natToBin`, you
-- don't get back what you started with.
--
-- Any other number also has many representations, after applying
-- constructors to the multiple representations of zero.
-- /SOLUTION

-- To solve that problem, we can introduce a _normalization_ function
-- that selects the simplest `Bin` out of all the equivalent
-- `Bin`. Then we can prove that the conversion from `Bin` to `Nat` and
-- back again produces that normalized, simplest `Bin`.

-- EX4A (bin_nat_bin)

-- Define `normalize`. You will need to keep its definition as simple
-- as possible for later proofs to go smoothly. Do not use
-- `binToNat` or `natToBin`, but do use `doubleBin`.
--
-- Hint: Structure the recursion such that it _always_ reaches the
-- end of the `Bin` and _only_ processes each bit once. Do not
-- try to "look ahead" at future bits.

def normalize (b : Bin) : Bin :=
  -- ADMITDEF
  match b with
  | .z => .z
  | .b0 b' => doubleBin (normalize b')
  | .b1 b' => incr (doubleBin (normalize b'))
  -- /ADMITDEF

-- It would be wise to do some `example` proofs to check that your
-- definition of `normalize` works the way you intend before you
-- proceed. They won't be graded, but fill them in below.

-- SOLUTION
-- normalize_test_0
example : normalize .z = .z := by rfl
-- normalize_test_1
example : normalize (.b1 .z) = .b1 .z := by rfl
-- normalize_test_2
example : normalize (.b0 .z) = .z := by rfl
-- normalize_test_3
example : normalize (.b0 (.b0 .z)) = .z := by rfl
-- normalize_test_4
example : normalize (.b1 (.b0 .z)) = .b1 .z := by rfl
-- /SOLUTION

-- Finally, prove the main theorem. The inductive cases could be a
-- bit tricky.
--
-- Hint: Start by trying to prove the main statement, see where you
-- get stuck, and see if you can find a lemma -- perhaps requiring
-- its own inductive proof -- that will allow the main proof to make
-- progress. We have one lemma for the `b0` case (which also makes
-- use of `double_incr_bin`) and another for the `b1` case.

-- QUIETSOLUTION
theorem incr_doubleBin : ∀ b, incr (doubleBin b) = .b1 b := by
  intro b
  cases b with
  | z => rfl
  | b0 _ => rfl
  | b1 _ => rfl

-- We need to relate `2 *` (used by binToNat) to `doubleBin` (used
-- by normalize).  The key connection goes through `natToBin`.
theorem natToBin_two_mul : ∀ n, natToBin (2 * n) = doubleBin (natToBin n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih =>
    -- 2 * (n' + 1) = 2 * n' + 2 by Nat.mul_succ.
    -- natToBin (2 * n' + 2): since +2 is +(1+1), this unfolds to
    --   incr (incr (natToBin (2 * n'))).
    -- By ih: = incr (incr (doubleBin (natToBin n'))).
    -- RHS: doubleBin (natToBin (n' + 1)) = doubleBin (incr (natToBin n')).
    -- By double_incr_bin: = incr (incr (doubleBin (natToBin n'))). ✓
    rw [Nat.mul_succ]
    simp only [natToBin, ih, ← double_incr_bin]
-- /QUIETSOLUTION

theorem bin_nat_bin : ∀ b, natToBin (binToNat b) = normalize b := by
  -- ADMITTED
  intro b
  induction b with
  | z => rfl
  | b0 b' ih =>
    simp only [binToNat, normalize]
    rw [natToBin_two_mul, ih]
  | b1 b' ih =>
    simp only [binToNat, normalize]
    -- Goal: natToBin (1 + 2 * binToNat b') = incr (doubleBin (normalize b'))
    -- Rewrite 1 + x to x + 1 so natToBin can unfold
    rw [Nat.add_comm 1 (2 * binToNat b')]
    simp only [natToBin, natToBin_two_mul, ih]
-- /ADMITTED

-- GRADE_THEOREM 6: bin_nat_bin
-- []
-- /FULL

-- /HIDEFROMADVANCED
-- TERSE: /HIDEFROMHTML
