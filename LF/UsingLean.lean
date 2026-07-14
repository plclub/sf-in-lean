-- Chapter goals:
-- Nats
-- dsimp
-- calc
-- maybe simp annotations
-- maybe typeclasses?

/- Lean: Using the full power of a proof assistant -/

-- INSTRUCTORS: This chapter is the bridge to Lean's natural numbers,
-- `dsimp`, `calc`, maybe, `simp` annotations, and maybe typeclasses.
-- It is relatively short -- should take about 30 minutes to cover.

-- HIDEFROMHTML
-- FULL

/-
  ######################################################################
  # More powerful Natural Numbers
-/
import LF.Basics
import LF.Induction

import Batteries.CodeAction

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
  natural numbers from scratch, nor do they tend to write out `rewrite` steps
  for basic properties of natural numbers by hand.
-/

-- BCP: Just making a note that we need to explain the
-- `zero.succ.succ` notation someplace well before this file!
section long_example
open NatPlayground.Nat
/- Previously, we did computation like this... -/
theorem test_mult1' : (two * two : NatPlayground.Nat) = four := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  rewrite [mul_succ, mul_succ, mul_zero]
  rewrite [add_succ, add_succ, add_zero]
  rewrite [add_succ, add_succ, add_zero]
  rfl
end long_example
-- BCP: The info viewed in the InfoView during this proof is kind of
-- mysterious (to me) here.  Have we already given people enough help
-- to understand it here?

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
  Specifically, we will learn about `dsimp`, `calc`, and `simp` annotations,
  which enable more powerful and concise proofs.

  In fact, from now on, we will use the built-in `Nat` type and its powerful
  features. To do so, write `Nat.<theorem>` to reference Lean's version
  of `<theorem>`.
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
  -- rfl will not work here!
  /- First rewrite the goal with `h`; then the two sides are identical. -/
  rewrite [h]
  rfl

/-
  The same proof can be written more compactly with `rw`. In this example,
  `rw [h]` rewrites with `h` and then closes the resulting reflexive goal.
-/

theorem rfl_not_enough' (n m : Nat) (h : n = m) : n = m := by
  rw [h]

/-
   We will continue to show more powerful tools for manipulating
   the context and goal of a proof to bring them closer to what can be
   solved with `rfl`.
-/

/-
  ######################################################################
  # Using the Standard Library
-/

-- FULL
/-
  As part of using Lean's standard `Nat` type, we will also begin
  using theorems about `Nat`s from the standard library. Because we
  did not write or prove these theorems ourselves, however, we may not
  know all the available theorems off the top of our heads.

  Lean provides a few ways to search through the standard library to find theorems
  that may be useful during a particular proof. The first such way is the `exact?`
  tactic. This tactic searches the standard library for a theorem that can be applied,
  along with the hypotheses in the context, to exactly close the current goal.
-/
-- /FULL

-- TERSE
/- We can use the `exact?` tactic to search for relevant theorems in the standard library -/
-- /TERSE

/-- info: Try this:
  [apply] exact Nat.add_comm a b -/
#guard_msgs(info) in
example (a b : Nat) : a + b = b + a := by
  /- this will suggest that we use `exact Nat.add_comm a b` to close this goal -/
  exact?

-- FULL
/-
  If you are using the Lean 4 extension in VSCode, the InfoView will
  have a blue `[apply]` button that shows the suggested theorem to
  close the goal. Alternatively, VSCode may show an inline suggestion
  (light bulb) button above the `exact?`. You can click either of
  these buttons to replace the occurrence of `exact?` with the tactic
  it found to complete the proof; idiomatic Lean does not leave
  `exact?` tactics (or any other `?` tactics, as we will see shortly)
  in the finished versions of proofs and instead replaces them with
  the tactics they found during search.
-/
-- /FULL

-- FULL
/-
  The `exact?` tactic is useful when we just need a single library theorem to get us over
  the finish line of a proof, but it is not so helpful when we are deep in the middle of a proof
  or are wondering how to get started on one. Luckily, there are other tactics that will help us
  with this.

  The `rw?` tactic works like `exact?`, except that it searches for any theorems that you
  could use to rewrite the current goal.
-/
-- /FULL

-- TERSE
/- You can also use `rw?` to look for theorems to rewrite by -/
-- /TERSE


/-- info: Try this:
  [apply] rw [Nat.add_comm]
  -- no goals -/
#guard_msgs(info) in
example (a b : Nat) : a + b = b + a := by
  /- this will suggest that we use `rw [Nat.add_comm]` to close this goal -/
  rw?

-- FULL
/-
  However, unlike `exact?`, just because `rw?` suggests a theorem to
  you does not automatically imply that it will be useful. In the
  example below, many of the theorems `rw?` suggests will not progress
  towards completing the proof; you will need to carefully look
  through its suggestions to see which ones seem useful. We strongly
  recommend against blindly using `rw?` and accepting its suggestions
  without due consideration! You will find this a very slow and
  frustrating way to write proofs. Instead, we suggest figuring out
  what you would like your next step to be, conceptually, and then
  using `rw?` to search for a theorem that implements it. If no such
  theorem exists, that may be a sign that you need to prove it
  yourself.
-/
-- /FULL

#guard_msgs(drop all) in
example (n m q : Nat) :
   (n + m) + q = m + (n + q) := by
  -- lots of suggestions to look through here!
  rw?
  sorry

/- Prove the following theorems about `Nat`s. You should not need induction for any of these;
   you can find the theorems you need using `rw?` and `exact?`.  -/

theorem mul_three (p : Nat) :
    3 * p = p + p + p := by
  -- ADMITTED
  rw [Nat.add_one_mul, Nat.two_mul]
  -- /ADMITTED
  -- GRADE_THEOREM 1: mul_three

theorem mul_three_beq (p : Nat) :
    (3 * p == p + p + p) = true := by
  -- ADMITTED
  rw [Nat.beq_eq_true_eq]
  exact mul_three p
  -- /ADMITTED
  -- GRADE_THEOREM 1: mul_three_beq

/-
  ######################################################################
  # Structuring proofs with `calc`
-/

/-
  In Lean proofs, long `rw` chains are useful, but they are sometimes hard to
  read because the intermediate goals are invisible. Furthermore, sometimes we
  _know_ exactly how we want to manipulate the terms of a proof, but don't want
  to have the tactics like `add_comm` and `add_assoc` "guess" which subterms to
  rewrite.

  The `calc` tactic writes down the intermediate goals of a proof, and allows us to
  specify exactly which rewrite rules to apply at each step. It is a powerful
  tool for structuring proofs, and is often more readable than long `rw` chains.

  `calc` is designed to mimic the style of proofs in mathematics textbooks, which will
  often look something like this:

  a + (b + c)
  = (a + b) + c        ...   [by associativity of addition]
  = (b + a) + c        ...   [by commutativity of addition]
  = b + (a + c)        ...   [by associativity of addition]

  Note how we can see each intermediate step of this proof when we
  look at it this way. Let's look at how we might prove this theorem
  (i.e., that `a + (b + c) = b + (a + c)`) in Lean.
 -/

/- First, a proof in the style we already know. -/
theorem add_swap (a b c : Nat) : a + (b + c) = b + (a + c) := by
  rw [← Nat.add_assoc, Nat.add_comm a b, Nat.add_assoc]

/- Here we present the same theorem, written with `calc`.
   Note how each intermediate goal is visible in the source. -/
theorem add_swap' (a b c : Nat) : a + (b + c) = b + (a + c) := by
  calc a + (b + c) /- one side of the goal is the argument to `calc`... -/
    /- ... and each subsequent line is a transformation, with a tactic. -/
    a + (b + c) = (a + b) + c := by rw [Nat.add_assoc]
    (a + b) + c = (b + a) + c := by rw [Nat.add_comm a b]
    /- once a line matches the other side of the equality in the main goal
       (in this case `(b + (a + c)`), the calc tactic succeeds. -/
    (b + a) + c = b + (a + c) := by rw [Nat.add_assoc]

/- We can also write the proof like this to be a bit more concise:  -/
theorem add_swap'' (a b c : Nat) : a + (b + c) = b + (a + c) := by
  calc a + (b + c)
    _ = (a + b) + c := by rw [Nat.add_assoc]
    _ = (b + a) + c := by rw [Nat.add_comm a b]
    _ = b + (a + c) := by rw [Nat.add_assoc]
/- Whereas before, the left-hand side of each equality in the `calc`
   tactic was repeated from the right-hand side of the previous one,
   we can replace the left-hand side entirely with an `_`. Now our
   Lean proof looks quite a bit like the textbook one we saw earlier! -/

-- EX1 (succ_mul_succ)
theorem succ_mul_succ (n m : Nat) :
    (n + 1) * (m + 1) = n * m + n + m + 1 := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]

/- Given this proof with `rw`, rewrite it with `calc`. Reminder that you can use `rw?` to find
   appropriate rules to rewrite by. -/

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

  The `dsimp` tactic ("definitionally simplify") unfolds definitions
  and performs definitional simplifications. You can give it hints in
  square brackets: `dsimp [f]` tells it to unfold the definition of `f`.
  You can also simplify a hypothesis `h` in the context by writing
  `dsimp [...] at h`. `dsimp` will also close goals by `rfl` when possible.
-/

def square (n : Nat) : Nat := n * n

def triple (n : Nat) : Nat := n + n + n

/-
  When the goal depends on a fact about an unknown value, `rfl` fails.
  Here, `dsimp` makes progress, exposing a goal the fact can close.
-/
example (n m : Nat) (h : n + n = m) : triple n = m + n := by
  -- rfl will not work here!
  dsimp [triple]
  /- The goal can now be rewritten by `h`. -/
  rw [h]

/-
  As we have seen, `rw` can also unfold definitions. In this example,
  either style is fine: use `dsimp [triple]` when you want to emphasize
  definitional simplification, or `rw [triple, h]` when the proof is just
  a sequence of rewrites.
-/
example (n m : Nat) (h : n + n = m) : triple n = m + n := by
  /- `rw [triple]` unfolds `triple n`. -/
  rw [triple, h]

-- EX 2: Complete this proof, using `dsimp` or `rw` as appropriate.
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

/- Aside: `rw [...] at h` also works on hypotheses too, as does `rw? at h` -/
example (n m : Nat) (h : 2 * n = m * 2) : n + n = m + m := by
  rw [Nat.mul_comm, Nat.mul_two, Nat.mul_two] at h
  exact h

/- `dsimp` also takes definitional steps such as `+ 0`,
  so it can finish goals that rfl would close. -/
example (n : Nat) : square n + 0 = n * n := by
  dsimp [square]

/- Like `rw` and `exact`, `dsimp` also has a `?` version that searches for
   functions to simplify by. Many Lean tactics have `?` versions; try it out if you are unsure. -/

-- DEV
-- RAB : TODO- hard pointer needed to this section once we
-- versify. Also, we may want a pointer to where we introduce `simp`
-- (and _maybe_ `grind` in the next volume).
-- /DEV

-- FULL
/- ## A New Step Towards Automation -/

-- BCP: This section reference should be a live pointer, at least in the HTML.
/- In the section on `Irreducibility, Rewriting, and Proof
   Engineering` of `Basics.lean`, we hinted at introducing more
   automated tactics than `rewrite` for writing proofs. The
   first of these is `dsimp`: by using `dsimp`, we allow Lean to introduce a
   small amount of its own automatic reasoning using other basic
   tactics like `rfl`. If you're ever confused by what `dsimp` is
   doing, don't be afraid to switch back to `rewrite` to examine
   what's going on.

   Later in this volume, we will introduce the more powerful automated
   tactic `simp`, which can sometimes solve complex goals by itself and is
   accordingly extremely common in real-world Lean developments.

   But, using this tactic now does not help (in fact, it hurts!) the
   process of learning logical reasoning, formal theorem proving, and
   Lean. Additionally, real Lean programmers are careful when using
   automation: it can hurt the readability of a proof, and real-world
   Lean is often used to _communicate_ a result as much as to prove
   it. We will continue to use only simple tactics, like `dsimp` and
   `rw`, for most of this volume so that you have a firm grasp of both the
   logic behind the proofs you are writing and the ways to structure
   those proofs to make your logic clear.
 -/
-- /FULL

/-
  ######################################################################
  # Redefining Functions and Lemmas over Nats
-/

-- FULL
/-
  Now that we've switched over to using Lean's standard library, we can
  redefine some of the functions from the last few chapters on `Nat`s.

  Prove some of these theorems using the techniques we've discussed this chapter.
-/
-- /FULL

def even (n : Nat) :=
  match n with
  | .zero           => true
  | .succ .zero     => false
  | .succ (.succ n) => even n

def odd n := (not (even n))

def eqb (n m : Nat) :=
  match n, m with
  | 0, 0             => true
  | .succ _, 0
  | 0, .succ _       => false
  | .succ n, .succ m => eqb n m

def minustwo (n : Nat) : Nat :=
  match n with
  | .zero            => .zero
  | .succ (.zero)    => .zero
  | .succ (.succ n') => n'

def double (n : Nat) : Nat :=
  match n with
  | .zero    => 0
  | .succ n' => .succ (.succ (double n'))

theorem even_succ (n : Nat) :
    even (.succ n) = !even n := by
  -- ADMITTED
  induction n with
  | zero =>
    rfl
  | succ n' ih =>
    rw [even, ih, Bool.not_not]
  -- /ADMITTED
-- GRADE_THEOREM 1: even_succ

  -- TODO: talk about using `Nat.add_zero` and friends from now on.

  -- (OA) : added lemmas proved for our Nat for Lean's Nat to prevent
  --        later files from breaking.

theorem even_zero : even 0 = true := by rfl

theorem double_zero : double 0 = 0 := by rfl

theorem double_succ (n : Nat) : double (n + 1) = double n + 2 := by rfl

theorem double_add (n : Nat) : double n = n + n := by
  -- ADMITTED
  induction n with
  | zero =>
    rw [double_zero]
  | succ n' ih =>
    rw [double_succ, ih, Nat.succ_add n' (n' + 1), Nat.add_succ n' n']
  -- /ADMITTED
-- GRADE_THEOREM 1: double_add

theorem double_mul (n : Nat) : double n = 2 * n := by
  -- ADMITTED
  rw [double_add, Nat.two_mul]
  -- /ADMITTED
-- GRADE_THEOREM 1: double_mul

/-
  # Using Code Actions to Generate Match Skeletons
-/

/-
  Lean's language server can suggest _code actions_, which are
  small editor commands that modify the source code.
  In VSCode, a light-bulb icon appears on the left
  when a code action is available at your cursor.
  You can click the icon or open the code action menu with `Ctrl + .`
  on Windows/Linux or `Command + .` on macOS.


  For more information, see [Lean 4 VS Code extension manual](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md#code-actions).

  Some code actions can generate the explicit branches needed for pattern
  matching. This is especially useful when working with `match` expressions,
  or with tactics such as `cases` and `induction`, which we saw in previous chapters.

  Let's look at an example using `induction`.
-/

-- FULL
/-
  For example, suppose we start with the following incomplete proof:
-/
/--
error: unsolved goals
case zero
⊢ eqb 0 0 = true

case succ
n✝ : Nat
a✝ : eqb n✝ n✝ = true
⊢ eqb (n✝ + 1) (n✝ + 1) = true
-/
#guard_msgs(error) in
theorem foo (n : Nat) : eqb n n := by
  induction n

/-
  Put your cursor on `induction n` and open the code action menu.
  You should see
  "Generate an explicit pattern match for 'induction'." in the list.
  If you choose this action,
  Lean adds an explicit branch for each constructor:
-/
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (n : Nat) : eqb n n := by
  induction n with
  | zero => sorry
  | succ n _ => sorry

/-
  This gives us basic structure of the proof without requiring us to write each
  branch by hand. We can then cfocus on proving each case.

  One possible proof is:
-/
example (n : Nat) : eqb n n := by
  induction n with
  | zero      => rfl
  | succ n ih => rw [eqb, ih]

/-
  Note that Lean used `_` for the induction hypothesis in the generated `.succ` branch.
  At that point, Lean didn't know the unfinished proof would need to refer to the hypothesis.
  Since we use it in `rw`, we replace `_` with the name `ih`.

  In later chapters, we will see some tactics that can make such
  inaccessible names available again.
-/

/-
  The same trick also works work for `match` expressions.
  For example, suppose we start with

  ```lean
  def isZero (n : Nat) : Bool :=
    match n
  ```
-/

/- HIDE:
  @berberman: Incomplete `match` term would cause parse errors which `#guard_msgs` can't suppress.
  Use code block in docstring for now.
-/

/-
  Lean can generate the missing branches:
-/

/--
error: don't know how to synthesize placeholder
context:
n✝ n : Nat
⊢ Bool
---
error: don't know how to synthesize placeholder
context:
n : Nat
⊢ Bool
-/
#guard_msgs in
def isZero (n : Nat) : Bool :=
  match n with
  | 0 => _
  | n + 1 => _

/-
  Note that for the built-in {name}`Nat` type, the patterns `0` and `n + 1` correspond to
  `zero` and `succ n`.
-/

-- /FULL
