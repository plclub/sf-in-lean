-- Chapter goals:
-- Nats
-- dsimp
-- calc
-- maybe simp annotations
-- maybe typeclasses?

/- Lean: Using the full power of a proof assistant -/

-- INSTRUCTORS: This file is the bridge to Lean's natural numbers,
-- `dsimp`, `calc`, maybe, `simp` annotations, and maybe typeclasses.
-- It is relatively short, and should take about 30 minutes to cover.

-- HIDEFROMHTML
-- FULL
/-
  REMINDER:

           #####################################################
           ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
           #####################################################

    (See the [Preface] for why.)
-/

/-
  ######################################################################
  # More powerful Natural Numbers
-/
import LF.Basics
import LF.Induction

/-
  Until now, we have been working with our own custom natural numbers, using the
  `Nat` type that we defined in `Basics.lean`.

  However, Lean has a built-in type of natural numbers, which is more powerful
  and comes with many useful features. They are very slightly different from our
  custom `Nat`, but these differences are mostly superficial. The built-in
  natural numbers are defined in the `Init` module, which is automatically
  imported by Lean. We will refer to them as `Nat` as well, but they are not the
  same as the `Nat` we defined in `Basics.lean`.

  In Lean, programmers and mathematicians don't re-prove the basic properties of
  natural numbers from scratch, nor to they tend to write out `rewrite` steps
  for basic properties of natural numbers by hand.
-/


section long_example
open NatPlayground.Nat
/- Previously, we did computation like this... -/
theorem test_mult1' : (3 * 3 : NatPlayground.Nat) = 9 := by
  rewrite [three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
  rewrite [mul_succ, mul_succ, mul_succ, mul_zero]
  rewrite [add_succ, add_succ, add_succ, add_zero]
  rewrite [add_succ, add_succ, add_succ, add_zero]
  rewrite [add_succ, add_succ, add_succ, add_zero]
  rfl
end long_example

/- This approach is useful in a textbook for understanding the structure of
  natural numbers and for providing early practice with writing proofs. But it
  is also tedious in the long term.

  Instead of doing this, programmers and mathematicians use the built-in `Nat`
  and the powerful features of Lean to _automatically_ prove properties about
  natural numbers and to compute with them.
 -/

theorem test_mult1_nat : (3 * 3 : Nat) = 9 := by
  rfl

/- The annotation `: Nat` tells Lean that we are using its built-in `Nat` type. -/

/-
  In this chapter we will learn how to use the built-in `Nat` and some powerful
  features for computing with and proving properties about natural numbers.
  Specifically, we will learn about as `dsimp`, `calc`, and `simp` annotations,
  which enable more powerful and consise proofs.

  In fact, from now on, we will use the built-in `Nat` type and its powerful
  features.
-/



/-
  ## `rfl` and computation with `Nat`
 -/


/- With Lean's `Nat`, much of the computation happens automatically,
   and `rfl` suffices to close any equality of computation on literals. -/
theorem complicated_computation : (2 * 3 + 4 * 5 : Nat) * 6 = 156 := by
  rfl

/- This quickly becomes necessary, as natural numbers quickly get large! -/

/- Of course, `rfl` can't close more complicated goals where the values
   of the terms are unknown. -/

  theorem rfl_not_enough (n m : Nat) (h : n = m) : n = m := by
    fail_if_success rfl /- the `fail_if_success` tactic tells us `rfl` has failed. -/
    /- We need to use `h` to rewrite the goal, and then `rfl` will work. -/
    rewrite [h]
    rfl

/-
   We will continue to show more powerful tools for manipulating
   the context and goal of a proof to bring them closer to what can be
   solved with `rfl`.
-/


/-
  ######################################################################
  # Structuring proofs with `calc`
-/

/-
  In Lean proofs, long `rw` chains are useful, but they are sometimes hard to
  read because the intermediate goals are invisible. Furthermore, sometimes we
  _know_ exactly how we want to maniuplate the terms of a proof, but don't want
  to have the tactics like `add_comm` and `add_assoc` "guess" which subterms to
  rewrite.

  The `calc` writes down the intermediate goals of a proof, and allows us to
  specify exactly which rewrite rules to apply at each step. It is a powerful
  tool for structuring proofs, and is often more readable than long `rw` chains.
 -/

/- First, a proof in the style we already know. -/
theorem add_swap (a b c : Nat) : a + (b + c) = b + (a + c) := by
  rw [← Nat.add_assoc, Nat.add_comm a b, Nat.add_assoc]

/- Here we present the same theorem, written with `calc`.
   Note how each intermediate goal is visible in the source. -/
theorem add_swap' (a b c : Nat) : a + (b + c) = b + (a + c) := by
  calc a + (b + c) /- one side of the goal is the argument to `calc`... -/
    /- ... and each subsequent line is a transformation, with a tactic. -/
    _ = (a + b) + c := by rw [Nat.add_assoc]
    _ = (b + a) + c := by rw [Nat.add_comm a b]
    /- once a line matches the other side of the equality in the main goal
       (in this case `(b + (a + c)`), the calc tactic succeeds. -/
    _ = b + (a + c) := by rw [Nat.add_assoc]

-- EX1 (succ_mul_succ)
theorem succ_mul_succ (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]

/- Given this proof with `rw`, rewrite it with `calc`. -/

theorem succ_mul_succ' (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
-- ADMITTED
  calc (n + 1) * (m + 1)
    _ = n * (m + 1) + 1 * (m + 1) := by rw [Nat.add_mul]
    _ = n * (m + 1) + (m + 1)     := by rw [Nat.one_mul]
    _ = (n * m + n * 1) + (m + 1) := by rw [Nat.mul_add]
    _ = (n * m + n) + (m + 1)     := by rw [Nat.mul_one]
    _ = n * m + n + m + 1         := by rw [← Nat.add_assoc]
-- /ADMITTED

/-
  If you prefer `rw` to `calc`, that's fine! Each has particular uses, and both
  will be tools in your ever-growing toolbox of tactics.
-/

/-
  ######################################################################
  # Definitional simplification: `dsimp`
-/

/- Often, rather than rewriting by a known equation like

   `n + succ m = succ (n + m)` using `rw [add_succ]`,

  we just want to simplify the function (here `add`) automatically when we can.

  The `dsimp` tactic ("definitionally simplify") applies known facts
  and definitions to simplify the goal.  You can give it hints in
  square brackets: `dsimp [f]` tells it to unfold the definition
  of `f`.  You can also simplify a hypothesis `h` in the context
  by writing `dsimp [...] at h`. `dsimp` will also close goals by
  `rfl` when possible.
-/

def square (n : Nat) : Nat := n * n

def triple (n : Nat) : Nat := n + n + n

/-
  When the goal depends on a fact about an unknown value, `rfl` fails.
  Here, `dsimp` makes progress, exposing a goal the fact can close.
-/
 example (n m : Nat) (h : n + n = m) : triple n = m + n := by
  fail_if_success rfl
  dsimp [triple]
  /- the goal can now be rewritten by `h`. -/
  rw [h]

-- EX 2: Complete this proof, using `dsimp` as necessary.
example (n m : Nat) (h : m = n) : triple m = n + (n + n) := by
  -- ADMITTED
  rw [h]
  dsimp [triple]
  rw [Nat.add_assoc]
  -- /ADMITTED

/- `dsimp at h` also works on hypotheses, which rfl can't touch. -/
example (n : Nat) (h : square n = 16) : n * n = 16 := by
  dsimp [square] at h
  exact h

/- dsimp also takes definitional steps such as `+ 0`,
  so it can finish goals that rfl would close. -/
example (n : Nat) : square n + 0 = n * n := by
  dsimp [square]


/-
  ######################################################################
  # Basic Typeclasses (?)
-/

/-
  ######################################################################
  # Redefining Functions and Lemmas over Nats
-/

def even (n : Nat) :=
  match n with
  | .zero => true
  | .succ .zero => false
  | .succ (.succ n) => even n

def odd n := (not (even n))

def eqb (n m : Nat) :=
  match n, m with
  | 0, 0 => true
  | .succ _, 0 | 0, .succ _ => false
  | .succ n, .succ m => eqb n m

def minustwo (n : Nat) : Nat :=
  match n with
  | .zero => .zero
  | .succ (.zero) => .zero
  | .succ (.succ n') => n'

def double (n : Nat) : Nat :=
  match n with
  | .zero => 0
  | .succ n' => .succ (.succ (double n'))

theorem even_S : ∀ n : Nat,
    even (.succ n) = !even n := by
  -- ADMITTED
  intro n
  induction n
  case zero => rfl
  case succ n' ih =>
    rewrite [even, ih, NatPlayground.Nat.notb_involutive]; rfl

  -- TODO: talk about using Nat.add_zero and friends from now on.
