-- Tactics: More Basic Tactics

-- INSTRUCTORS: This material is a bit too much to cover in detail in
--    one 80-minute lecture.  90-100 minutes is more reasonable, but that
--    may still involve going a bit fast at the end.

-- FULL: This chapter introduces several additional proof strategies
-- and tactics that allow us to begin proving more interesting
-- properties of functional programs.
--
-- We will see:
-- - how to use auxiliary lemmas in both "forward-" and
--   "backward-style" proofs;
-- - how to reason about data constructors -- in particular, how to
--   use the fact that they are injective and disjoint;
-- - how to strengthen an induction hypothesis, and when such
--   strengthening is required; and
-- - more details on how to reason by case analysis.

-- HIDEFROMHTML
-- /HIDEFROMHTML
-- TERSE: HIDEFROMHTML
import Poly
-- TERSE: /HIDEFROMHTML

-- ######################################################################
-- * The `apply` Tactic

-- FULL: We often encounter situations where the goal to be proved is
-- _exactly_ the same as some hypothesis in the context or some
-- previously proved lemma.
-- TERSE: The `apply` tactic is useful when some hypothesis or an
-- earlier lemma exactly matches the goal:

-- silly1
theorem silly1 : ∀ (n m : Nat),
  n = m →
  n = m := by
  intro n m eq
  -- Here, we could finish with `rw [eq]` as we have done several times
  -- before.  Or we can finish in a single step by using `exact`:
  exact eq

-- FULL: The `exact` tactic also works with _conditional_ hypotheses
-- and lemmas: if the statement being applied is an implication, then
-- the premises of this implication will be added to the list of
-- subgoals needing to be proved.
-- TERSE: ***
-- `apply` also works with _conditional_ hypotheses:

-- silly2
theorem silly2 : ∀ (n m o p : Nat),
  n = m →
  (n = m → [n, o] = [m, p]) →
  [n, o] = [m, p] := by
  intro n m o p eq1 eq2
  apply eq2; exact eq1

-- HIDEFROMADVANCED
-- FULL: Typically, when we use `apply H`, the statement `H` will
-- begin with a `∀` that introduces some _universally quantified
-- variables_.
--
-- When Lean matches the current goal against the conclusion of `H`,
-- it will try to find appropriate values for these variables.  For
-- example, when we do `apply eq2` in the following proof, the
-- universal variable `q` in `eq2` gets instantiated with `n`, and
-- `r` gets instantiated with `m`.
-- TERSE: ***
-- TERSE: Observe how Lean picks appropriate values for the
-- `∀`-quantified variables of the hypothesis:

-- silly2a
theorem silly2a : ∀ (n m : Nat),
  (n, n) = (m, m) →
  (∀ (q r : Nat), (q, q) = (r, r) → [q] = [r]) →
  [n] = [m] := by
  intro n m eq1 eq2
  apply eq2; exact eq1

-- FULL
-- EX2? (silly_ex)
-- Complete the following proof using only `intro` and `apply`/`exact`.

-- silly_ex
theorem silly_ex : ∀ p,
  (∀ n, even n = true → even (n + 1) = false) →
  (∀ n, even n = false → odd n = true) →
  even p = true →
  odd (p + 1) = true := by
  -- ADMITTED
  intro p eq1 eq2 eq3
  apply eq2; apply eq1; exact eq3
-- /ADMITTED
-- []
-- /FULL

-- FULL: To use the `exact` tactic, the fact being applied must match
-- the goal exactly (perhaps after simplification) -- for example,
-- `exact` will not work if the left and right sides of the equality
-- are swapped.
-- TERSE: ***
-- TERSE: The goal must match the hypothesis _exactly_ for `exact` to
-- work:

-- silly3
theorem silly3 : ∀ (n m : Nat),
  n = m →
  m = n := by
  intro n m H
  -- Here we cannot use `exact` directly...
  -- ...but we can use `symm`, which switches the left
  -- and right sides of an equality in the goal.
  symm; exact H

-- FULL
-- EX2 (apply_exercise1)
-- You can use `apply` with previously defined theorems, not
-- just hypotheses in the context.  Use the `rev_involutive` theorem
-- from Poly.lean as part of your (relatively short) solution to this
-- exercise. You do not need `induction`.

-- rev_exercise1
theorem rev_exercise1 : ∀ (l l' : List Nat),
  l = l'.rev →
  l' = l.rev := by
  -- ADMITTED
  intro l l' eq
  rw [eq]
  symm
  exact rev_involutive l'
-- /ADMITTED
-- GRADE_THEOREM 2: rev_exercise1
-- []

-- EX1M? (apply_rewrite)
-- Briefly explain the difference between the tactics `apply`/`exact`
-- and `rw`:
--
-- `rw` is used to apply a known equality to modify the goal,
-- replacing occurrences of one side by the other.
--
-- `apply` uses a known implication to replace a goal that matches
-- the conclusion of the implication with subgoals, one for each premise.
-- `exact` is similar but closes the goal completely.
--
-- If the known fact is itself an equality (with no premises), then
-- either tactic can be used.
-- []
-- /FULL
-- /HIDEFROMADVANCED

-- ######################################################################
-- * The `apply ... with` Tactic / `calc` blocks

-- The following silly example uses two rewrites in a row to
-- get from `[a, b]` to `[e, f]`.

-- trans_eq_example
example : ∀ (a b c d e f : Nat),
     [a, b] = [c, d] →
     [c, d] = [e, f] →
     [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  rw [eq1]; exact eq2

-- TERSE: ***
-- Since this is a common pattern, we might like to pull it out as a
-- lemma that records, once and for all, the fact that equality is
-- transitive.

theorem trans_eq {α : Type} (x y z : α)
  (h1 : x = y) (h2 : y = z) : x = z := by
  rw [h1]; exact h2

-- FULL: Now, we should be able to use `trans_eq` to prove the above
-- example.  However, to do this we need to supply the intermediate
-- value explicitly.
-- TERSE: ***
-- TERSE: Applying this lemma to the example above requires supplying
-- the intermediate value:

-- trans_eq_example'
example : ∀ (a b c d e f : Nat),
     [a, b] = [c, d] →
     [c, d] = [e, f] →
     [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  -- We can use `apply` with named arguments to supply the intermediate value:
  exact trans_eq _ [c, d] _ eq1 eq2

-- TERSE: ***
-- FULL: Lean also has a `calc` block that accomplishes the same purpose,
-- letting us chain equalities step by step.

-- trans_eq_example''
example : ∀ (a b c d e f : Nat),
     [a, b] = [c, d] →
     [c, d] = [e, f] →
     [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  calc [a, b] = [c, d] := eq1
    _ = [e, f] := eq2

-- FULL
-- EX3? (trans_eq_exercise)
-- trans_eq_exercise
example : ∀ (n m o p : Nat),
     m = (minustwo o) →
     (n + p) = m →
     (n + p) = (minustwo o) := by
  -- ADMITTED
  intro n m o p eq1 eq2
  exact trans_eq _ m _ eq2 eq1
-- /ADMITTED
-- []
-- /FULL

-- ######################################################################
-- * Constructor Injectivity and Disjointness

-- FULL: Recall the definition of natural numbers:
--
--     inductive Nat : Type where
--       | zero
--       | succ (n : Nat)
--
-- It is obvious from this definition that every number has one of
-- two forms: either it is the constructor `zero` or it is built by
-- applying the constructor `succ` to another number.  But there is more
-- here than meets the eye: implicit in the definition are two
-- additional facts:
--
-- - The constructor `Nat.succ` is _injective_ (or _one-to-one_).
--   That is, if `Nat.succ n = Nat.succ m`, it must also be that `n = m`.
--
-- - The constructors `Nat.zero` and `Nat.succ` are _disjoint_.
--   That is, `0` is not equal to `Nat.succ n` for any `n`.

-- TERSE: The constructors of inductive types are _injective_ (or
-- _one-to-one_) and _disjoint_.
--
-- E.g., for `Nat`...
--
--    - if `n + 1 = m + 1` then it must be that `n = m`
--
--    - `0` is not equal to `n + 1` for any `n`

-- TERSE: ***
-- We can _prove_ the injectivity of `Nat.succ` by using the `Nat.pred`
-- function.

-- S_injective
theorem S_injective : ∀ (n m : Nat),
  n + 1 = m + 1 →
  n = m := by
  intro n m H1
  -- In Lean, `omega` handles this directly:
  omega

-- TERSE: ***

-- FULL: Lean's `omega` tactic handles the injectivity of `Nat.succ`
-- automatically.  For other inductive types, we can use pattern matching
-- or the `Nat.succ.inj` lemma.  Here is an alternate proof:

-- S_injective'
theorem S_injective' : ∀ (n m : Nat),
  n + 1 = m + 1 →
  n = m := by
  intro n m H
  exact Nat.succ.inj H

-- TERSE: ***
-- Here's a more interesting example that shows how we can derive
-- multiple equations at once from an equality of constructed values.

-- injection_ex1
theorem injection_ex1 : ∀ (n m o : Nat),
  [n, m] = [o, o] →
  n = m := by
  intro n m o H
  -- WORKINCLASS
  -- From `[n, m] = [o, o]` (i.e., `n :: m :: [] = o :: o :: []`),
  -- we can extract `n = o` and `m = o`.
  have H1 : n = o := List.cons.inj H |>.1
  have H2 : m = o := List.cons.inj (List.cons.inj H |>.2) |>.1
  rw [H1, H2]
  -- /WORKINCLASS

-- HIDEFROMADVANCED
-- FULL
-- EX3 (injection_ex3)
-- injection_ex3
example : ∀ {α : Type} (x y z : α) (l j : List α),
  x :: y :: l = z :: j →
  j = z :: l →
  x = y := by
  -- ADMITTED
  intro α x y z l j eq1 eq2
  have hxz : x = z := List.cons.inj eq1 |>.1
  have hyl_j : y :: l = j := List.cons.inj eq1 |>.2
  rw [eq2] at hyl_j
  have hyz : y = z := List.cons.inj hyl_j |>.1
  rw [hxz, hyz]
-- /ADMITTED
-- GRADE_THEOREM 3: injection_ex3
-- []
-- /FULL
-- /HIDEFROMADVANCED

-- So much for injectivity of constructors.  What about disjointness?

-- FULL: The principle of disjointness says that two terms beginning
-- with different constructors (like `0` and `Nat.succ`, or `true` and `false`)
-- can never be equal.  This means that, any time we find ourselves
-- in a context where we've _assumed_ that two such terms are equal,
-- we are justified in concluding anything we want, since the
-- assumption is nonsensical.

-- TERSE: Two terms beginning with different constructors (like
-- `0` and `Nat.succ`, or `true` and `false`) can never be equal!

-- TERSE: ***

-- In Lean, when we have a contradictory hypothesis involving
-- different constructors, we can use the `contradiction` tactic
-- (or `simp at H` / `omega`) to close the goal.  Some examples:

-- discriminate_ex1
theorem discriminate_ex1 : ∀ (n m : Nat),
  false = true →
  n = m := by
  intro n m contra
  contradiction

-- discriminate_ex2
theorem discriminate_ex2 : ∀ (n : Nat),
  n + 1 = 0 →
  2 + 2 = 5 := by
  intro n contra
  omega

-- These examples are instances of a logical principle known as the
-- _principle of explosion_, which asserts that a contradictory
-- hypothesis entails anything (even manifestly false things!).

-- FULL: If you find the principle of explosion confusing, remember
-- that these proofs are _not_ showing that the conclusion of the
-- statement holds.  Rather, they are showing that, _if_ the
-- nonsensical situation described by the premise did somehow hold,
-- _then_ the nonsensical conclusion would too -- because we'd be
-- living in an inconsistent universe where every statement is true.
--
-- We'll explore the principle of explosion in more detail in the
-- next chapter.

-- FULL
-- EX1 (discriminate_ex3)
-- discriminate_ex3
example :
  ∀ {α : Type} (x y z : α) (l j : List α),
    x :: y :: l = [] →
    x = z := by
  -- ADMITTED
  intro α x y z l j eq1
  contradiction
-- /ADMITTED
-- GRADE_THEOREM 1: discriminate_ex3
-- []
-- /FULL

-- TERSE: ***

-- For a more useful example, we can use `contradiction` (or `omega`)
-- to make a connection between the two different notions of equality
-- (`=` and `==`) that we have seen for natural numbers.

-- eqb_0_l
theorem eqb_0_l : ∀ n,
   Nat.beq 0 n = true → n = 0 := by
  intro n
  -- We can proceed by case analysis on `n`. The first case is trivial.
  cases n with
  | zero =>
    intro _H; rfl
  -- FULL: However, the second one doesn't look so simple: assuming
  -- `Nat.beq 0 (n' + 1) = true`, we must show `n' + 1 = 0`!  The way forward
  -- is to observe that the assumption itself is nonsensical:
  | succ n' =>
    simp [Nat.beq]
    -- FULL: `simp` simplifies the hypothesis to `False`, closing the goal.

-- ######################################################################
-- * Constructor equality

-- The injectivity of constructors allows us to reason that
-- `∀ (n m : Nat), n + 1 = m + 1 → n = m`.  The converse of this
-- implication is an instance of a more general fact about both
-- constructors and functions, which we will find useful below:

-- f_equal
theorem f_equal {α : Type} {β : Type} (f : α → β) (x y : α)
  (h : x = y) : f x = f y := by
  rw [h]

-- eq_implies_succ_equal
theorem eq_implies_succ_equal : ∀ (n m : Nat),
  n = m → n + 1 = m + 1 := by
  intro n m H
  exact congrArg (· + 1) H

-- FULL: Indeed, there is also a tactic named `congr` that can
-- prove such theorems directly.  Given a goal of the form `f a1
-- ... an = f b1 ... bn`, the tactic `congr` will produce subgoals
-- of the form `a1 = b1`, ..., `an = bn`.

-- TERSE: Lean also provides `congr` as a tactic.

-- eq_implies_succ_equal'
theorem eq_implies_succ_equal' : ∀ (n m : Nat),
  n = m → n + 1 = m + 1 := by
  intro n m H
  congr

-- ######################################################################
-- * Using Tactics on Hypotheses

-- FULL: By default, most tactics work on the goal formula and leave
-- the context unchanged.  However, most tactics also have a variant
-- that performs a similar operation on a statement in the context.
--
-- For example, the `simp at H` tactic performs simplification on
-- the hypothesis `H` in the context.
-- TERSE: Many tactics come with "`... at ...`" variants that work on
-- hypotheses instead of goals.

-- S_inj
theorem S_inj : ∀ (n m : Nat) (b : Bool),
  (Nat.beq (n + 1) (m + 1)) = b →
  (Nat.beq n m) = b := by
  intro n m b H
  simp [Nat.beq] at H
  exact H

-- FULL: Similarly, `have H' := f H` applies a function or lemma `f`
-- to a hypothesis `H` in the context.  Unlike ordinary `apply`
-- (which works on the goal), this gives us a form of "forward
-- reasoning": given `X → Y` and a hypothesis matching `X`, it
-- produces a hypothesis matching `Y`.
--
-- By contrast, `apply` is "backward reasoning": it says that if we
-- know `X → Y` and we are trying to prove `Y`, it suffices to prove
-- `X`.
-- TERSE: ***
-- TERSE: The ordinary `apply` tactic is a form of "backward
-- reasoning."  By contrast, `have` with an application is "forward
-- reasoning."

-- HIDEFROMADVANCED

-- silly4
theorem silly4 : ∀ (n m p q : Nat),
  (n = m → p = q) →
  m = n →
  q = p := by
  intro n m p q EQ H
  have H' : n = m := H.symm
  have H'' : p = q := EQ H'
  exact H''.symm

-- /HIDEFROMADVANCED
-- FULL: Forward reasoning starts from what is _given_ (premises,
-- previously proven theorems) and iteratively draws conclusions from
-- them until the goal is reached.  Backward reasoning starts from
-- the _goal_ and iteratively reasons about what would imply the
-- goal, until premises or previously proven theorems are reached.
--
-- The informal proofs seen in math or computer science classes tend
-- to use forward reasoning.  By contrast, idiomatic use of Lean
-- generally favors backward reasoning, though in some situations the
-- forward style can be easier to think about.

-- ######################################################################
-- * Specializing Hypotheses

-- Another handy tactic for manipulating hypotheses is `specialize`.
-- It is essentially just a combination of `have` and `apply`, but
-- it often provides a pleasingly smooth way to nail down overly
-- general assumptions.  It works like this:
--
-- If `H` is a quantified hypothesis in the current context -- i.e.,
-- `H : ∀ (x : T), P` -- then `specialize H e` will
-- change `H` so that it looks like `P` with `x` replaced by `e`.
--
-- For example:

-- specialize_example
theorem specialize_example : ∀ n,
     (∀ m, m * n = 0)
  → n = 0 := by
  intro n H
  specialize H 1
  simp [one_mul] at H
  exact H

-- FULL
-- EX3 (nth_error_always_none)

-- Use `specialize` to prove the following lemma. Do not use `induction`.
-- nth_error_always_none
theorem nth_error_always_none : ∀ (l : List Nat),
  (∀ i, nthError l i = none) →
  l = [] := by
  -- ADMITTED
  intro l H
  cases l with
  | nil => rfl
  | cons h t =>
    specialize H 0
    simp [nthError] at H
-- /ADMITTED
-- []
-- /FULL

-- Using `specialize` before `apply` gives us yet another way to
-- control where `apply` does its work.

-- trans_eq_example'''
example : ∀ (a b c d e f : Nat),
     [a, b] = [c, d] →
     [c, d] = [e, f] →
     [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  have H := trans_eq [a, b] [c, d] [e, f]
  apply H
  exact eq1
  exact eq2

-- Things to note:
-- - We can `specialize` facts from the global context, not just
--   local hypotheses.
-- - We supply the arguments directly to the lemma.

-- ######################################################################
-- * Varying the Induction Hypothesis

-- TERSE
-- Recall this function for doubling a natural number from the
-- Induction chapter:

-- (double is already defined in Induction.lean, but we repeat it here
-- since it only appears in the FULL version of that chapter.)

-- FULL: Sometimes it is important to control the exact form of the
-- induction hypothesis when carrying out inductive proofs in Lean.
-- In particular, we may need to be careful about which of the
-- assumptions we move (using `intro`) from the goal to the context
-- before invoking the `induction` tactic.
--
-- For example, suppose we want to show that `double` is injective --
-- i.e., that it maps different arguments to different results.
-- The way we start this proof is a bit delicate: if we begin it with
--     `intro n; induction n`
-- then all will be well.  But if we begin it with introducing _both_
-- variables
--     `intro n m; induction n`
-- we get stuck in the middle of the inductive case...
-- TERSE: ***
-- TERSE: Suppose we want to show that `double` is injective (i.e.,
-- it maps different arguments to different results).  The way we
-- _start_ this proof is a little bit delicate:

-- double_injective_FAILED
theorem double_injective_FAILED : ∀ n m,
  double n = double m →
  n = m := by
  intro n m
  induction n with
  | zero =>
    simp [double]
    intro eq
    cases m with
    | zero => rfl
    | succ m' => simp [double] at eq
  | succ n' _ih =>
    intro eq
    cases m with
    | zero => simp [double] at eq
    | succ m' =>
    -- At this point, the induction hypothesis (`_ih`) does _not_ give us
    -- `n' = m'` -- it's stuck with the original `m`, so the goal is
    -- not provable.
    sorry

-- TERSE: ***
-- HIDEFROMADVANCED

-- What went wrong?

-- FULL: The problem is that, at the point where we invoke the
-- induction hypothesis, we have already introduced `m` into the
-- context -- intuitively, we have told Lean, "Let's consider some
-- particular `n` and `m`..." and we now have to prove that, if
-- `double n = double m` for _these particular_ `n` and `m`, then
-- `n = m`.
--
-- The next tactic, `induction n` says to Lean: We are going to show
-- the goal by induction on `n`.  That is, we are going to prove, for
-- _all_ `n`, that the proposition
--
--   - `P n` = "if `double n = double m`, then `n = m`"
--
-- holds, by showing
--
--   - `P 0` and
--   - `P n → P (n + 1)`.
--
-- But this `P` is too specific: it talks about a _particular_ `m`.

-- Trying to carry out this proof by induction on `n` when `m` is
-- already in the context doesn't work because we are then trying to
-- prove a statement involving _every_ `n` but just a _particular_ `m`.
-- /HIDEFROMADVANCED

-- TERSE: ***
-- A successful proof of `double_injective` uses the `generalizing`
-- keyword in the `induction` tactic to keep `m` universally
-- quantified:

-- double_injective
theorem double_injective : ∀ n m,
  double n = double m →
  n = m := by
  intro n
  induction n with
  | zero =>
    intro m eq
    simp [double] at eq
    cases m with
    | zero => rfl
    | succ m' => simp [double] at eq
  | succ n' ih =>
    -- FULL
    -- Notice that both the goal and the induction hypothesis are
    -- different this time: the goal asks us to prove something more
    -- general (i.e., we must prove the statement for _every_ `m`), but
    -- the induction hypothesis `ih` is correspondingly more flexible,
    -- allowing us to choose any `m` we like when we apply it.
    -- /FULL
    intro m eq
    -- FULL
    -- Since we are doing a case analysis on `n`, we also need a case
    -- analysis on `m` to keep the two in sync.
    -- /FULL
    cases m with
    | zero =>
      -- FULL: The 0 case is trivial:
      simp [double] at eq
    | succ m' =>
      congr
      -- FULL
      -- Since we are now in the second branch, the `m'` mentioned in the
      -- context is the predecessor of the `m` we started out talking about.
      -- Applying the IH gives us exactly what we need.
      -- /FULL
      apply ih
      simp [double] at eq
      exact eq

-- HIDEFROMADVANCED
-- TERSE: ***
-- The thing to take away from all this is that you need to be
-- careful, when using induction, that you are not trying to prove
-- something too specific: When proving a property quantified over
-- variables `n` and `m` by induction on `n`, it is sometimes crucial
-- to leave `m` "generic."
-- /HIDEFROMADVANCED

-- FULL: The following exercise, which further strengthens the link between
-- `==` and `=`, follows the same pattern.
-- TERSE: The following theorem, which further strengthens the link between
-- `==` and `=`, follows the same pattern.
-- FULL
-- EX2 (eqb_true)
-- /FULL

-- eqb_true
theorem eqb_true : ∀ (n m : Nat),
  Nat.beq n m = true → n = m := by
-- FULL
  -- ADMITTED
-- /FULL
-- TERSE
  -- WORKINCLASS
-- /TERSE
  intro n
  induction n with
  | zero =>
    intro m
    cases m with
    | zero => intro _; rfl
    | succ m' => simp [Nat.beq]
  | succ n' ih =>
    intro m
    cases m with
    | zero => simp [Nat.beq]
    | succ m' =>
      simp only [Nat.beq]
      intro h
      have := ih m' h
      congr
-- TERSE
  -- /WORKINCLASS
-- /TERSE
-- FULL
-- /ADMITTED
-- GRADE_THEOREM 2: eqb_true
-- []

-- EX2AM? (eqb_true_informal)
-- Give a careful informal proof of `eqb_true`, stating the induction
-- hypothesis explicitly and being as explicit as possible about
-- quantifiers, everywhere.
-- GRADE_MANUAL 2: informal_proof
-- []

-- HIDEFROMADVANCED
-- EX3! (plus_n_n_injective)
-- TERSE: ***
-- In addition to being careful about how you use `intro`, practice
-- using `at` variants in this proof.

-- plus_n_n_injective
theorem plus_n_n_injective : ∀ (n m : Nat),
  n + n = m + m →
  n = m := by
  -- ADMITTED
  intro n
  induction n with
  | zero =>
    intro m eq
    simp at eq
    cases m with
    | zero => rfl
    | succ m' => omega
  | succ n' ih =>
    intro m eq
    cases m with
    | zero => omega
    | succ m' =>
      congr
      apply ih
      omega
-- /ADMITTED
-- GRADE_THEOREM 3: plus_n_n_injective
-- []
-- /HIDEFROMADVANCED
-- /FULL

-- TERSE: ***
-- The strategy of doing fewer `intro`s before an `induction` to
-- obtain a more general IH doesn't always work; sometimes some
-- _rearrangement_ of quantified variables is needed.  Suppose, for
-- example, that we wanted to prove `double_injective` by induction
-- on `m` instead of `n`.

-- double_injective_take2_FAILED
theorem double_injective_take2_FAILED : ∀ n m,
  double n = double m →
  n = m := by
  intro n m
  induction m with
  | zero =>
    simp [double]
    intro eq
    cases n with
    | zero => rfl
    | succ n' => simp [double] at eq
  | succ m' _ih =>
    intro eq
    cases n with
    | zero => simp [double] at eq
    | succ n' =>
      -- We are stuck here, just like before.
      sorry

-- TERSE: ***
-- The problem is that, to do induction on `m`, we must first
-- introduce `n`.  (If we simply say `induction m` without
-- introducing anything first, Lean will automatically introduce `n`
-- for us!)

-- HIDEFROMADVANCED
-- FULL: What can we do about this?  One possibility is to rewrite the
-- statement of the lemma so that `m` is quantified before `n`.  This
-- works, but it's not nice: We don't want to have to twist the
-- statements of lemmas to fit the needs of a particular strategy for
-- proving them!  Rather we want to state them in the clearest and
-- most natural way.
-- /HIDEFROMADVANCED

-- TERSE: ***
-- What we can do instead is to use the `generalizing` keyword in the
-- `induction` tactic.  In Lean, `induction m generalizing n` re-introduces
-- `n` into the goal before doing induction on `m`, giving us a
-- sufficiently general induction hypothesis.

-- double_injective_take2
theorem double_injective_take2 : ∀ n m,
  double n = double m →
  n = m := by
  intro n m
  -- `n` and `m` are both in the context
  -- Now use `generalizing n` to put `n` back in the goal:
  induction m generalizing n with
  | zero =>
    simp [double]
    intro eq
    cases n with
    | zero => rfl
    | succ n' => simp [double] at eq
  | succ m' ih =>
    intro eq
    cases n with
    | zero => simp [double] at eq
    | succ n' =>
      congr
      apply ih
      simp [double] at eq
      exact eq

-- ######################################################################
-- * Rewriting with conditional statements

-- Suppose that we want to show that `plus` is the inverse of
-- `minus`.  Since we are working with natural numbers, we need an
-- assumption to prevent `minus` from truncating its result.  With
-- this assumption, the induction hypothesis becomes
-- `∀ m, Nat.ble n' m = true → (m - n') + n' = m`.
-- The beginning of the proof uses techniques we have already seen --
-- in particular, notice how we induct on `n` before introducing `m`,
-- so that the induction hypothesis becomes sufficiently general.

-- sub_add_leb
theorem sub_add_leb : ∀ (n m : Nat), Nat.ble n m = true → (m - n) + n = m := by
  intro n
  induction n with
  | zero =>
    intro m _H
    simp
  | succ n' ih =>
    intro m H
    cases m with
    | zero => simp [Nat.ble] at H
    | succ m' =>
      -- The hypothesis `H : Nat.ble (n' + 1) (m' + 1) = true` simplifies
      -- to `Nat.ble n' m' = true`.
      simp_all [Nat.ble]
      -- FULL: At this point, we need to show `(m' - n') + n' + 1 = m' + 1`.
      -- TERSE: We can use the IH directly:
      omega

-- FULL
-- EX3! (gen_dep_practice)
-- Prove this by induction on `l`.

-- nth_error_after_last
theorem nth_error_after_last : ∀ (n : Nat) {α : Type} (l : List α),
  l.length = n →
  nthError l n = none := by
  -- ADMITTED
  intro n α l
  induction l generalizing n with
  | nil => intro _; simp [nthError]
  | cons x l' ih =>
    intro eq
    simp [List.length] at eq
    simp [nthError]
    rw [← eq]
    exact ih _ rfl
-- /ADMITTED
-- GRADE_THEOREM 3: nth_error_after_last
-- []
-- /FULL

-- ######################################################################
-- * Unfolding Definitions

-- It sometimes happens that we need to manually unfold a name that
-- has been introduced by a `def` so that we can manipulate
-- the expression it stands for.
--
-- For example, if we define...

def square (n : Nat) : Nat := n * n

-- ...and try to prove a simple fact about `square`...

-- square_mult
theorem square_mult : ∀ (n m : Nat), square (n * m) = square n * square m := by
  intro n m
  unfold square
  -- Now we have the goal: n * m * (n * m) = n * n * (m * m)
  -- We use associativity and commutativity of multiplication.
  calc n * m * (n * m)
      = n * (m * (n * m)) := by rw [Nat.mul_assoc]
    _ = n * (m * n * m) := by rw [Nat.mul_assoc]
    _ = n * (n * m * m) := by rw [Nat.mul_comm m n]
    _ = n * (n * (m * m)) := by rw [Nat.mul_assoc]
    _ = n * n * (m * m) := by rw [← Nat.mul_assoc]

-- TERSE: ***
-- At this point, a bit deeper discussion of unfolding and
-- simplification is in order.
--
-- We already have observed that tactics like `simp`, `rfl`,
-- and `apply` will often unfold the definitions of functions
-- automatically when this allows them to make progress.  For
-- example, if we define `foo m` to be the constant `5`...

def foo (x : Nat) : Nat := 5

-- .... then the `simp` in the following proof (or `rfl`,
-- if we omit the `simp`) will unfold `foo m` to `5`.

-- silly_fact_1
theorem silly_fact_1 : ∀ m, foo m + 1 = foo (m + 1) + 1 := by
  intro m
  simp [foo]

-- TERSE: ***
-- But this automatic unfolding is somewhat conservative.  For
-- example, if we define a slightly more complicated function
-- involving a pattern match...

def bar (x : Nat) : Nat :=
  match x with
  | 0 => 5
  | _ + 1 => 5

-- ...then the analogous proof needs help:

-- silly_fact_2_FAILED
-- (In Lean, `simp` can actually handle this, but let's illustrate
-- the issue with `unfold`.)

-- TERSE: ***
-- FULL: There are two ways to make progress.

-- First, we can use `cases m` to break the proof into two cases:

-- silly_fact_2
theorem silly_fact_2 : ∀ m, bar m + 1 = bar (m + 1) + 1 := by
  intro m
  cases m with
  | zero => simp [bar]
  | succ n => simp [bar]

-- This approach works, but it depends on our recognizing that the
-- `match` hidden inside `bar` is what was preventing us from making
-- progress.

-- TERSE: ***
-- A more straightforward way forward is to explicitly tell Lean to
-- unfold `bar`.

-- silly_fact_2'
theorem silly_fact_2' : ∀ m, bar m + 1 = bar (m + 1) + 1 := by
  intro m
  unfold bar
  -- Now it is apparent that we are stuck on the `match` expressions on
  -- both sides of the `=`, and we can use `cases` to finish the
  -- proof without thinking so hard.
  cases m with
  | zero => rfl
  | succ n => rfl

-- ######################################################################
-- * Using `cases` on Compound Expressions

-- FULL: We have seen many examples where `cases` is used to
-- perform case analysis of the value of some variable.  Sometimes we
-- need to reason by cases on the result of some _expression_.  We
-- can also do this with pattern matching.
--
-- Here are some examples:
-- TERSE: The `cases` tactic can be used on expressions as well as
-- variables:

def sillyfun (n : Nat) : Bool :=
  if n == 3 then false
  else if n == 5 then false
  else false

-- sillyfun_false
theorem sillyfun_false : ∀ (n : Nat),
  sillyfun n = false := by
  intro n
  simp [sillyfun]

-- FULL: After unfolding `sillyfun` in the above proof, `simp` can
-- handle the remaining `if-then-else` expressions automatically.
-- But in more complex cases, we might need to split on the
-- conditions manually.  We can do this with `split` or
-- `if h : ... then ... else ...` patterns.

-- FULL
-- EX3 (combine_split)
-- Here is an implementation of the `split` function mentioned in
-- chapter Poly (already defined in Poly.lean).
--
-- Prove that `split` and `combine` are inverses in the following
-- sense:

-- combine_split
theorem combine_split : ∀ {α : Type} {β : Type} (l : List (α × β)) l1 l2,
  split l = (l1, l2) →
  combine l1 l2 = l := by
  -- ADMITTED
  intro α β l
  induction l with
  | nil =>
    intro l1 l2 H
    simp [split] at H
    obtain ⟨rfl, rfl⟩ := H
    rfl
  | cons p l' ih =>
    intro l1 l2 H
    obtain ⟨x, y⟩ := p
    simp only [split] at H
    -- After unfolding split, we match on `split l'`
    generalize hspl : split l' = sp at H
    obtain ⟨lx, ly⟩ := sp
    simp only [Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    simp [combine]
    exact ih lx ly hspl
-- /ADMITTED
-- []
-- /FULL

-- TERSE: ***
-- FULL: The `eqn:` part of the `destruct` tactic in Rocq is handled
-- differently in Lean.  When we need to remember what case we're in
-- after splitting on a compound expression, we use `if h : ...` or
-- `match h : ... with` syntax.

-- For example, suppose we define a function `sillyfun1` like this:

def sillyfun1 (n : Nat) : Bool :=
  if n == 3 then true
  else if n == 5 then true
  else false

-- FULL: Now suppose that we want to convince Lean that `sillyfun1 n`
-- yields `true` only when `n` is odd.  If we just unfold, we need to
-- remember the case information.

-- sillyfun1_odd
theorem sillyfun1_odd : ∀ (n : Nat),
  sillyfun1 n = true →
  odd n = true := by
  intro n eq
  simp [sillyfun1] at eq
  -- `simp` processes the if-then-else chain and gives us
  -- `n = 3 ∨ n = 5`.  We can handle each case:
  rcases eq with rfl | rfl
  · rfl
  · rfl

-- FULL
-- EX2 (destruct_eqn_practice)
-- bool_fn_applied_thrice
theorem bool_fn_applied_thrice :
  ∀ (f : Bool → Bool) (b : Bool),
  f (f (f b)) = f b := by
  -- ADMITTED
  intro f b
  cases b with
  | true =>
    cases hft : f true with
    | true => rw [hft, hft]
    | false =>
      cases hff : f false with
      | true => exact hft
      | false => exact hff
  | false =>
    cases hff : f false with
    | true =>
      cases hft : f true with
      | true => exact hft
      | false => exact hff
    | false => rw [hff, hff]
-- /ADMITTED
-- GRADE_THEOREM 2: bool_fn_applied_thrice
-- []

-- #################################################################
-- * Review

-- FULL: We've now talked about many of Lean's most fundamental tactics.
-- We'll introduce a few more in the coming chapters, and later on
-- we'll see some more powerful _automation_ tactics that make Lean
-- help us with low-level details.  But basically we've got what we
-- need to get work done.
--
-- Here are the ones we've seen:
--
--   - `intro`: move hypotheses/variables from goal to context
--
--   - `rfl`: finish the proof (when the goal looks like `e = e`)
--
--   - `apply`: prove goal using a hypothesis, lemma, or constructor
--
--   - `exact`: close goal exactly using a term
--
--   - `have H := f H'`: apply a function/lemma to a hypothesis in
--     the context (forward reasoning)
--
--   - `specialize H e`: refine a hypothesis by fixing some of
--     its variables
--
--   - `simp`: simplify computations in the goal
--
--   - `simp at H`: ... or a hypothesis
--
--   - `rw`: use an equality hypothesis (or lemma) to rewrite
--     the goal
--
--   - `rw [...] at H`: ... or a hypothesis
--
--   - `symm`: changes a goal of the form `t = u` into `u = t`
--
--   - `calc`: prove a chain of equalities step by step
--
--   - `omega`: prove linear arithmetic goals
--
--   - `contradiction`: close a goal when hypotheses are contradictory
--
--   - `congr`: change a goal of the form `f x = f y` into `x = y`
--
--   - `unfold`: replace a defined constant by its right-hand side in
--     the goal
--
--   - `unfold ... at H`: ... or a hypothesis
--
--   - `cases ... with`: case analysis on values of inductively
--     defined types
--
--   - `induction ... with`: induction on values of inductively
--     defined types
--
--   - `induction ... generalizing`: strengthen the induction hypothesis
--     by generalizing over additional variables
-- /FULL

-- TERSE
-- ######################################################################
-- * Micro Sermon

-- Mindless proof-hacking is a terrible temptation...
--
-- Try to resist!
-- /TERSE

-- FULL
-- ######################################################################
-- * Additional Exercises

-- EX3 (eqb_sym)
-- eqb_sym
theorem eqb_sym : ∀ (n m : Nat),
  Nat.beq n m = Nat.beq m n := by
  -- ADMITTED
  intro n
  induction n with
  | zero =>
    intro m; cases m with
    | zero => rfl
    | succ m' => rfl
  | succ n' ih =>
    intro m; cases m with
    | zero => rfl
    | succ m' =>
      simp [Nat.beq]
      exact ih m'
-- /ADMITTED
-- GRADE_THEOREM 3: eqb_sym
-- []

-- EX3AM? (eqb_sym_informal)
-- Give an informal proof of this lemma that corresponds to your
-- formal proof above:
--
-- Theorem: For any `Nat`s `n` `m`, `(n == m) = (m == n)`.
--
-- Proof: By induction on `n`.
-- - Base case: `n = 0`. By cases on `m`:
--   - If `m = 0`, both sides are `true`.
--   - If `m = m' + 1`, both sides are `false`.
-- - Inductive case: `n = n' + 1`. By cases on `m`:
--   - If `m = 0`, both sides are `false`.
--   - If `m = m' + 1`, both sides reduce to `(n' == m')` and `(m' == n')`
--     respectively, which are equal by the induction hypothesis.
-- []
-- /FULL

-- FULL
-- EX3? (eqb_trans)
-- eqb_trans
theorem eqb_trans : ∀ (n m p : Nat),
  Nat.beq n m = true →
  Nat.beq m p = true →
  Nat.beq n p = true := by
  -- ADMITTED
  intro n m p Hnm Hmp
  have Hnm' := eqb_true n m Hnm
  rw [Hnm']
  exact Hmp
-- /ADMITTED
-- []
-- /FULL

-- FULL
-- EX3AM (split_combine)
-- We proved, in an exercise above, that `combine` is the inverse of
-- `split`.  Complete the definition of `split_combine_statement`
-- below with a property that states that `split` is the inverse of
-- `combine`. Then, prove that the property holds.
--
-- Hint: Take a look at the definition of `combine` in Poly.lean.
-- Your property will need to account for the behavior of `combine`
-- in its base cases, which possibly drop some list elements.

def split_combine_statement : Prop
  -- ADMITDEF
  := ∀ {α : Type} {β : Type} (l1 : List α) (l2 : List β),
    l1.length = l2.length → split (combine l1 l2) = (l1, l2)
  -- /ADMITDEF

-- split_combine
theorem split_combine : split_combine_statement := by
-- ADMITTED
  intro α β l1
  induction l1 with
  | nil =>
    intro l2 Heq
    cases l2 with
    | nil => rfl
    | cons y l2' => simp [List.length] at Heq
  | cons x l1' ih =>
    intro l2 Heq
    cases l2 with
    | nil => simp [List.length] at Heq
    | cons y l2' =>
      simp only [combine, split]
      have Heq' : l1'.length = l2'.length := by simpa [List.length] using Heq
      have := ih l2' Heq'
      rw [this]
-- /ADMITTED
-- GRADE_MANUAL 3: split_combine
-- []
-- /FULL

-- FULL
-- EX3A (filter_exercise)
-- filter_exercise
theorem filter_exercise : ∀ {α : Type} (test : α → Bool)
                                 (x : α) (l lf : List α),
  filter test l = x :: lf →
  test x = true := by
  -- ADMITTED
  intro α test x l
  induction l with
  | nil =>
    intro lf eq
    simp [filter] at eq
  | cons v' l' ih =>
    intro lf eq
    simp [filter] at eq
    split at eq
    · have heq := List.cons.inj eq
      rw [← heq.1]
      assumption
    · exact ih lf eq
-- /ADMITTED
-- GRADE_THEOREM 3: filter_exercise
-- []

-- EX4A! (forall_exists_challenge)
-- Define two recursive functions, `forallb` and `existsb`.  The
-- first checks whether every element in a list satisfies a given
-- predicate:
--
--       forallb odd [1, 3, 5, 7, 9] = true
--       forallb (!·) [false, false] = true
--       forallb (· % 2 == 0) [0, 2, 4, 5] = false
--       forallb (· == 5) [] = true
--
-- The second checks whether there exists an element in the list that
-- satisfies a given predicate:
--
--       existsb (· == 5) [0, 2, 3, 6] = false
--       existsb (· && true) [true, true, false] = true
--       existsb odd [1, 0, 0, 0, 0, 3] = true
--       existsb (· % 2 == 0) [] = false
--
-- Next, define a _nonrecursive_ version of `existsb` -- call it
-- `existsb'` -- using `forallb` and `!`.
--
-- Finally, prove a theorem `existsb_existsb'` stating that
-- `existsb'` and `existsb` have the same behavior.

-- ADMITDEF
def forallb {α : Type} (test : α → Bool) (l : List α) : Bool :=
  match l with
  | [] => true
  | x :: l' => test x && forallb test l'
-- /ADMITDEF

-- test_forallb_1
example : forallb odd [1, 3, 5, 7, 9] = true := by rfl  -- ADMITTED
-- test_forallb_2
example : forallb (!·) [false, false] = true := by rfl  -- ADMITTED
-- test_forallb_3
example : forallb (· % 2 == 0) [0, 2, 4, 5] = false := by rfl  -- ADMITTED
-- test_forallb_4
example : forallb (· == 5) ([] : List Nat) = true := by rfl  -- ADMITTED

-- ADMITDEF
def existsb {α : Type} (test : α → Bool) (l : List α) : Bool :=
  match l with
  | [] => false
  | x :: l' => test x || existsb test l'
-- /ADMITDEF

-- test_existsb_1
example : existsb (· == 5) [0, 2, 3, 6] = false := by rfl  -- ADMITTED
-- test_existsb_2
example : existsb (· && true) [true, true, false] = true := by rfl  -- ADMITTED
-- test_existsb_3
example : existsb odd [1, 0, 0, 0, 0, 3] = true := by rfl  -- ADMITTED
-- test_existsb_4
example : existsb (· % 2 == 0) ([] : List Nat) = false := by rfl  -- ADMITTED

-- ADMITDEF
def existsb' {α : Type} (test : α → Bool) (l : List α) : Bool :=
  !(forallb (fun x => !(test x)) l)
-- /ADMITDEF

-- existsb_existsb'
theorem existsb_existsb' : ∀ {α : Type} (test : α → Bool) (l : List α),
  existsb test l = existsb' test l := by
  -- ADMITTED
  intro α test l
  simp [existsb']
  induction l with
  | nil => rfl
  | cons x l' ih =>
    simp [existsb, forallb]
    cases test x with
    | true => simp
    | false => simp; exact ih
-- /ADMITTED

-- GRADE_THEOREM 6: existsb_existsb'
-- []
-- /FULL
