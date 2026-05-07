/- Induction: Proof by Induction -/


/-
  ######################################################################
  # Separate Compilation
-/

/- Lean will first need to compile `Basics.lean` so it can be imported here -- detailed instructions are in the full version of this chapter... -/


import LF.Basics


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


/- add_0_r_easy -/
example : ∀ n : Nat, n + 0 = n := by
  intro n; rfl


/- zero_add_firsttry -/
example : ∀ n : Nat, 0 + n = n := by
/- ... gets stuck. -/
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


/- TERSE: *** -/


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


/- *** -/
/-
  Here's another related fact about addition, which we'll
  need later.  (The proof is left as an exercise.)
-/

theorem add_comm : ∀ n m : Nat,
    n + m = m + n := by
  sorry

/- *** -/
/-
  The following theorem relates the computational equality `BEq` on
  `Nat` with the definitional equality `=` on `Bool`.
-/

theorem eqb_refl : ∀ n : Nat,
    (n == n) = true := by
  sorry


theorem even_S : ∀ n : Nat,
    even (n + 1) = !even n := by
  sorry


/-
  ######################################################################
  # Proofs Within Proofs
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


/- TERSE: *** -/


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


