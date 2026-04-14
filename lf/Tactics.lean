-- Tactics: More Basic Tactics

-- INSTRUCTORS: This material is a bit too much to cover in detail in
--    one 80-minute lecture.  90-100 minutes is more reasonable, but that
--    may still involve going a bit fast at the end.

-- SOONER: This chapter could maybe use one or two more WORKINCLASS
--    tags...
-- SOONER: BCP 25: General comment: All the previous chapters have
--    felt pretty smooth. This one suddenly feels like we're throwing a
--    huge amount of information at them, with little scaffolding -- just
--    a bunch of miscellaneous tactics and examples.  Wish it flowed
--    better, somehow.

-- FULL: This chapter introduces several additional proof strategies
--    and tactics that allow us to begin proving more interesting
--    properties of functional programs.
--
--    We will see:
--    - how to use auxiliary lemmas in both "forward-" and
--      "backward-style" proofs;
--    - how to reason about data constructors -- in particular, how to
--      use the fact that they are injective and disjoint;
--    - how to strengthen an induction hypothesis, and when such
--      strengthening is required; and
--    - more details on how to reason by case analysis.

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
-- TERSE: HIDEFROMHTML
import Poly
-- TERSE: /HIDEFROMHTML

-- ######################################################################
-- * The `apply` Tactic

-- FULL: We often encounter situations where the goal to be proved is
--    _exactly_ the same as some hypothesis in the context or some
--    previously proved lemma.
-- TERSE: The `apply` tactic is useful when some hypothesis or an
--    earlier lemma exactly matches the goal:

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "Here, we could finish with `rewrite -> eq. reflexivity.` as we
--    have done several times before.  Or we can finish in a single step
--    by using `apply`:"
-- ADAPTED:
-- Here, we could finish with `rw [eq]` as we have done several times
-- before.  Or we can finish in a single step by using `exact`:

theorem silly1 : ∀ (n m : Nat),
    n = m →
    n = m := by
  intro n m eq
  exact eq

-- FULL: The `exact` tactic works when the goal matches a hypothesis
--    or lemma precisely.  Lean also provides `apply`, which is like
--    `exact` but also works with _conditional_ hypotheses and lemmas:
--    if the statement being applied is an implication, then the premises
--    of this implication will be added to the list of subgoals needing
--    to be proved.
-- TERSE: ***
-- `apply` also works with _conditional_ hypotheses:

theorem silly2 : ∀ (n m o p : Nat),
    n = m →
    (n = m → [n, o] = [m, p]) →
    [n, o] = [m, p] := by
  intro n m o p eq1 eq2
  apply eq2; exact eq1

-- HIDEFROMADVANCED
-- FULL: Typically, when we use `apply H`, the statement `H` will
--    begin with a `∀` that introduces some _universally quantified
--    variables_.
--
--    When Lean matches the current goal against the conclusion of `H`,
--    it will try to find appropriate values for these variables.  For
--    example, when we do `apply eq2` in the following proof, the
--    universal variable `q` in `eq2` gets instantiated with `n`, and
--    `r` gets instantiated with `m`.
-- TERSE: ***
-- TERSE: Observe how Lean picks appropriate values for the
--    `∀`-quantified variables of the hypothesis:

theorem silly2a : ∀ (n m : Nat),
    (n, n) = (m, m) →
    (∀ (q r : Nat), (q, q) = (r, r) → [q] = [r]) →
    [n] = [m] := by
  intro n m eq1 eq2
  apply eq2; exact eq1

-- FULL
-- EX2? (silly_ex)
-- Complete the following proof using only `intro` and `apply`/`exact`.
theorem silly_ex : ∀ p,
    (∀ n, even n = true → even (n + 1) = false) →
    (∀ n, even n = false → odd n = true) →
    even p = true →
    odd (p + 1) = true := by
  -- ADMITTED
  intro p eq1 eq2 eq3; apply eq2; apply eq1; exact eq3
-- /ADMITTED
-- []
-- /FULL

-- FULL: To use the `exact` tactic, the fact being applied must match
--    the goal exactly (perhaps after simplification) -- for example,
--    `exact` will not work if the left and right sides of the equality
--    are swapped.
-- TERSE: ***
-- TERSE: The goal must match the hypothesis _exactly_ for `exact` to
--    work:

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "Here we cannot use `apply` directly..."
-- ADAPTED:
-- Here we cannot use `exact` directly...

theorem silly3 : ∀ (n m : Nat),
    n = m →
    m = n := by
  intro n m H

  -- ...but we can use the `symm` tactic, which switches the left
  --    and right sides of an equality in the goal.

  symm; exact H

-- FULL
-- EX2 (apply_exercise1)
-- You can use `apply` with previously defined theorems, not
--    just hypotheses in the context.  Use that as part of your
--    (relatively short) solution to this exercise.  You do not need
--    `induction`.

theorem rev_exercise1 : ∀ (l l' : List Nat),
    l = rev l' →
    l' = rev l := by
  -- ADMITTED
  intro l l' eq; rw [eq]; symm; exact rev_involutive l'
-- /ADMITTED
-- GRADE_THEOREM 2: rev_exercise1
-- []

-- EX1M? (apply_rewrite)
-- Briefly explain the difference between the tactics `exact`/`apply` and
--    `rw`.  What are the situations where both can usefully be applied?

-- SOLUTION
-- The `rw` tactic is used to apply a known equality (a hypothesis from
-- the context or a previously proved lemma) to modify the goal, replacing
-- occurrences of one side by the other.
--
-- The `apply` tactic uses a known implication (a hypothesis from the
-- context, a previously proved lemma, or a constructor) to replace a
-- goal that matches the conclusion of the implication with subgoals,
-- one for each premise of the implication.  The `exact` tactic is
-- similar to `apply` but will not create new subgoals.
--
-- If the known fact is itself an equality (with no premises), then
-- either tactic can be used.  (We will see below that each tactic
-- can also be used to modify a hypothesis rather than the goal.)
-- /SOLUTION
-- []
-- /FULL
-- /HIDEFROMADVANCED

-- ######################################################################
-- * The `apply ... with` Tactic

-- HIDE: AAA dislikes the [...with...] variants of tactics, which he
--    feels don't work very well.  But we (Arthur and BCP) decided to
--    leave things alone for now, since removing [...with...] would
--    require changing MANY proofs.

-- The following silly example uses two rewrites in a row to
--    get from `[a, b]` to `[e, f]`.

theorem trans_eq_example : ∀ (a b c d e f : Nat),
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  rw [eq1]; exact eq2

-- TERSE: ***
-- Since this is a common pattern, we might like to pull it out as a
--    lemma that records, once and for all, the fact that equality is
--    transitive.

theorem trans_eq {α : Type} (x y z : α) :
    x = y → y = z → x = z := by
  intro eq1 eq2; rw [eq1]; exact eq2

-- FULL: Now, we should be able to use `trans_eq` to prove the above
--    example.  However, to do this we need a slight refinement of the
--    `apply` tactic.
-- TERSE: ***
-- TERSE: Applying this lemma to the example above requires a slight
--    refinement of `apply`:

theorem trans_eq_example' : ∀ (a b c d e f : Nat),
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
-- FULL

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "If we simply tell Rocq `apply trans_eq` at this point, it can
--    tell (by matching the goal against the conclusion of the lemma)
--    that it should instantiate `X` with `[nat]`, `x` with `[a,b]`, and
--    `z` with `[e,f]`.  However, the matching process doesn't determine
--    an instantiation for `y`: we have to supply one explicitly by
--    adding `with (y:=[c,d])` to the invocation of `apply`."
-- ADAPTED:
-- If we simply say `apply trans_eq` at this point, Lean can tell
--    (by matching the goal against the conclusion of the lemma) that it
--    should instantiate `x` with `[a, b]` and `z` with `[e, f]`.
--    However, the matching process doesn't determine an instantiation
--    for `y`: we have to supply one explicitly using `(y := [c, d])`:

-- /FULL
-- TERSE

  -- Doing `apply trans_eq` doesn't work!  But...

-- /TERSE
  apply trans_eq _ [c, d]
-- TERSE
  -- does.
-- /TERSE
  · exact eq1
  · exact eq2

-- FULL: Actually, we don't always need to supply the argument by name.
--    In Lean, we can use `_` for arguments that can be inferred and
--    provide positional arguments.

-- TERSE: ***
-- FULL: Lean also has `calc` blocks, which provide a more natural way
--    to chain equalities and are often preferred in practice.  But
--    we've already seen `calc` in the \CHAP{Induction} chapter, and
--    `apply` with explicit arguments is useful for more general
--    reasoning as well.

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "Rocq also has a built-in tactic `transitivity` that
--    accomplishes the same purpose as applying `trans_eq`."
-- ADAPTED:
-- In Lean, the `calc` block is the idiomatic way to chain equalities.
-- We can also use `Trans.trans` directly:

-- TERSE: `calc` blocks or `Trans.trans` can also be used directly.

theorem trans_eq_example'' : ∀ (a b c d e f : Nat),
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  exact Trans.trans eq1 eq2

-- FULL
-- EX3? (trans_eq_exercise)
theorem trans_eq_exercise : ∀ (n m o p : Nat),
    m = (minustwo o) →
    (n + p) = m →
    (n + p) = (minustwo o) := by
  -- ADMITTED
  intro n m o p eq1 eq2
  exact Trans.trans eq2 eq1
-- /ADMITTED
-- []
-- /FULL

-- ######################################################################
-- * The `injection` and `contradiction` Tactics

-- HIDE: Should we explain `contradiction` without an argument?  BCP 25: No.

-- NOTE: The following section heading was adapted from the Rocq original:
-- ORIGINAL: "The `injection` and `discriminate` Tactics"
-- ADAPTED: (changed `discriminate` to `contradiction` since that's the Lean equivalent)

-- FULL: Recall the definition of natural numbers:
--
--     inductive Nat : Type where
--       | zero : Nat
--       | succ (n : Nat) : Nat
--
--    It is obvious from this definition that every number has one of
--    two forms: either it is the constructor `zero` or it is built by
--    applying the constructor `succ` to another number.  But there is
--    more here than meets the eye: implicit in the definition are two
--    additional facts:
--
--    - The constructor `succ` is _injective_ (or _one-to-one_).  That
--      is, if `n + 1 = m + 1`, it must also be that `n = m`.
--
--    - The constructors `zero` and `succ` are _disjoint_.  That is, `0`
--      is not equal to `n + 1` for any `n`.

-- FULL: Similar principles apply to every inductively defined type:
--    all constructors are injective, and the values built from distinct
--    constructors are never equal.  For lists, the `cons` constructor
--    is injective and the empty list `[]` is different from every
--    non-empty list.  For booleans, `true` and `false` are different.
--    (Since `true` and `false` take no arguments, their injectivity is
--    neither here nor there.)  And so on.

-- TERSE: The constructors of inductive types are _injective_ (or
--    _one-to-one_) and _disjoint_.
--
--    E.g., for `Nat`...
--
--       - if `n + 1 = m + 1` then it must be that `n = m`
--
--       - `0` is not equal to `n + 1` for any `n`

-- TERSE: ***
-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "We can _prove_ the injectivity of `S` by using the `pred`
--    function defined in `Basics.v`."
-- ADAPTED:
-- We can _prove_ the injectivity of `succ` by using the `pred`
-- function defined in `Basics.lean`.

theorem succ_injective : ∀ (n m : Nat),
    n + 1 = m + 1 →
    n = m := by
  intro n m H1
  have H2 : ∀ k, Nat.pred (k + 1) = k := by intro k; rfl
  rw [← H2 n, H1, H2]

-- TERSE: ***

-- LATER: FSR'25 - I wrote an explanation for `assert` here,
--    though I feel its inclusion here breaks the flow.

-- FULL: Lean's `have` tactic, used above, adds the given hypothesis
--    to the context, but it first requires you to prove the hypothesis
--    as a new goal.
--
--    This technique for injectivity can be generalized to any constructor
--    by writing the equivalent of `pred` -- i.e., writing a function that
--    "undoes" one application of the constructor.
--
--    As a convenient alternative, Lean provides a tactic called
--    `injection` that allows us to exploit the injectivity of any
--    constructor.  Here is an alternate proof of the above theorem
--    using `injection`:

-- TERSE: As a convenience, the `injection` tactic allows us to
--    exploit injectivity of any constructor (not just `succ`).

theorem succ_injective' : ∀ (n m : Nat),
    n + 1 = m + 1 →
    n = m := by
  intro n m H
-- FULL

-- By writing `injection H` at this point, we are asking Lean to
--    generate all equations that it can infer from `H` using the
--    injectivity of constructors (in the present example, the equation
--    `n = m`).  The `with` clause lets us name the resulting hypothesis.

-- /FULL
  injection H

-- TERSE: ***
-- Here's a more interesting example that shows how `injection` can
--    derive multiple equations at once.

theorem injection_ex1 : ∀ (n m o : Nat),
    [n, m] = [o, o] →
    n = m := by
  intro n m o H
  -- WORKINCLASS
  injection H with H1 H2
  injection H2 with H3
  rw [H1, H3]
-- /WORKINCLASS

-- TERSE: ***

-- HIDEFROMADVANCED
-- FULL
-- EX3 (injection_ex3)
theorem injection_ex3 : ∀ (α : Type) (x y z : α) (l j : List α),
    x :: y :: l = z :: j →
    j = z :: l →
    x = y := by
  -- ADMITTED
  intro α x y z l j eq1 eq2
  injection eq1 with Hxz Hyl_j
  have Hyl_zl : y :: l = z :: l := by
    exact Trans.trans Hyl_j eq2
  injection Hyl_zl with Hyz
  rw [Hxz, Hyz]
-- /ADMITTED
-- GRADE_THEOREM 3: injection_ex3
-- []
-- /FULL
-- /HIDEFROMADVANCED

-- So much for injectivity of constructors.  What about disjointness?

-- FULL: The principle of disjointness says that two terms beginning
--    with different constructors (like `0` and `succ`, or `true` and
--    `false`) can never be equal.  This means that, any time we find
--    ourselves in a context where we've _assumed_ that two such terms
--    are equal, we are justified in concluding anything we want, since
--    the assumption is nonsensical.

-- TERSE: Two terms beginning with different constructors (like
--    `0` and `succ`, or `true` and `false`) can never be equal!

-- TERSE: ***

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "The `discriminate` tactic embodies this principle: It is used
--    on a hypothesis involving an equality between different
--    constructors (e.g., `false = true`), and it solves the current
--    goal immediately."
-- ADAPTED:
-- The `contradiction` tactic embodies this principle: It looks for a
--    hypothesis that is obviously impossible (such as an equality between
--    different constructors like `false = true`), and it solves the
--    current goal immediately.  Some examples:

theorem discriminate_ex1 : ∀ (n m : Nat),
    false = true →
    n = m := by
  intro n m contra; contradiction

theorem discriminate_ex2 : ∀ (n : Nat),
    n + 1 = 0 →
    2 + 2 = 5 := by
  intro n contra; contradiction

-- These examples are instances of a logical principle known as the
--    _principle of explosion_, which asserts that a contradictory
--    hypothesis entails anything (even manifestly false things!).

-- FULL: If you find the principle of explosion confusing, remember
--    that these proofs are _not_ showing that the conclusion of the
--    statement holds.  Rather, they are showing that, _if_ the
--    nonsensical situation described by the premise did somehow hold,
--    _then_ the nonsensical conclusion would too -- because we'd be
--    living in an inconsistent universe where every statement is true.
--
--    We'll explore the principle of explosion in more detail in the
--    next chapter.

-- FULL
-- EX1 (discriminate_ex3)
theorem discriminate_ex3 :
    ∀ (α : Type) (x y z : α) (l _j : List α),
    x :: y :: l = [] →
    x = z := by
  -- ADMITTED
  intro α x y z l _j eq1; contradiction
-- /ADMITTED
-- GRADE_THEOREM 1: discriminate_ex3
-- []
-- /FULL

-- TERSE: ***

-- TERSE
-- QUIZ
-- Recall our RGB and Color types:
--
-- inductive RGB : Type where | red | green | blue
-- inductive Color : Type where | black | white | primary (p: RGB)
--
-- Suppose Lean's proof state looks like
--
--          x : RGB
--          y : RGB
--          H : Color.primary x = Color.primary y
--          ============================
--           y = x
--
--    and we apply the tactic `injection H with Hxy`.  What will happen?
--
--    (1) "No more subgoals."
--
--    (2) The tactic fails.
--
--    (3) Hypothesis `H` becomes `Hxy : x = y`.
--
--    (4) None of the above.
--
-- HIDE
theorem quiz0 : ∀ (x y : RGB), Color.primary x = Color.primary y → y = x := by
  intro x y H; injection H with Hxy; symm; exact Hxy
-- /HIDE
-- /QUIZ
-- QUIZ
-- Suppose Lean's proof state looks like
--
--          x : Bool
--          y : Bool
--          H : !x = !y
--          ============================
--           y = x
--
--    and we apply the tactic `injection H with Hxy`.  What will happen?
--
--    (A) "No more subgoals."
--
--    (B) The tactic fails.
--
--    (C) Hypothesis `H` becomes `Hxy : x = y`.
--
--    (D) None of the above.
--
-- HIDE
-- NOTE: In Lean, `!x` is `not x` which is a function application, not a
-- constructor application, so `injection` won't work here (same as Rocq).
-- /HIDE
-- /QUIZ
-- QUIZ
-- Now suppose Lean's proof state looks like
--
--          x : Nat
--          y : Nat
--          H : x + 1 = y + 1
--          ============================
--           y = x
--
--    and we apply the tactic `injection H with Hxy`.  What will happen?
--
--    (A) "No more subgoals."
--
--    (B) The tactic fails.
--
--    (C) Hypothesis `H` becomes `Hxy : x = y`.
--
--    (D) None of the above.
--
-- HIDE
-- NOTE: In Lean, `x + 1` is `Nat.succ x` which IS a constructor
-- application, so `injection H` DOES work here, unlike Rocq where
-- `x + 1` doesn't reduce to `S x` because addition recurses on the
-- first argument.
-- /HIDE
-- /QUIZ
-- /TERSE

-- TERSE: ***
-- The injectivity of constructors allows us to reason that `∀
--    (n m : Nat), n + 1 = m + 1 → n = m`.  The converse of this
--    implication is an instance of a more general fact about both
--    constructors and functions, which we will find useful below:

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "Theorem f_equal ..."
-- ADAPTED: In Lean this is already available as `congrArg`, but we
-- prove it here for illustration.

theorem f_equal {α β : Type} (f : α → β) (x y : α) :
    x = y → f x = f y := by
  intro eq; rw [eq]

theorem eq_implies_succ_equal : ∀ (n m : Nat),
    n = m → n + 1 = m + 1 := by
  intro n m H; exact f_equal (· + 1) n m H

-- FULL: Indeed, there is also a tactic named `congr` that can prove
--    such theorems directly.  Given a goal of the form `f a1 ... an =
--    f b1 ... bn`, the tactic `congr` will produce subgoals of the
--    form `a1 = b1`, ..., `an = bn`.  At the same time, any of these
--    subgoals that are simple enough (e.g., immediately provable by
--    `rfl`) will be automatically discharged.

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "Rocq also provides `f_equal` as a tactic."
-- ADAPTED:
-- Lean provides `congr` as a tactic.

theorem eq_implies_succ_equal' : ∀ (n m : Nat),
    n = m → n + 1 = m + 1 := by
  intro n m H; congr

-- ######################################################################
-- * Using Tactics on Hypotheses

-- FULL: By default, most tactics work on the goal formula and leave
--    the context unchanged.  However, most tactics also have a variant
--    that performs a similar operation on a statement in the context.
--
--    For example, the tactic `simp at H` performs simplification on
--    the hypothesis `H` in the context.

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "Many tactics come with `... in ...` variants that work on
--    hypotheses instead of goals."
-- ADAPTED:
-- Many tactics come with `... at ...` variants that work on
--    hypotheses instead of goals.

theorem succ_inj : ∀ (n m : Nat) (b : Bool),
    ((n + 1) == (m + 1)) = b →
    (n == m) = b := by
  intro n m b H; dsimp [BEq.beq, beq] at H; exact H

-- FULL: Similarly, `apply L at H` (or more commonly, writing
--    `have H' := L H`) matches some conditional statement `L`
--    (of the form `X → Y`, say) against a hypothesis `H` in the
--    context.  Unlike ordinary `apply` (which rewrites a goal matching
--    `Y` into a subgoal `X`), this gives us a form of "forward
--    reasoning": given `X → Y` and a hypothesis matching `X`, it
--    produces a hypothesis matching `Y`.
--
--    By contrast, `apply L` is "backward reasoning": it says that if we
--    know `X → Y` and we are trying to prove `Y`, it suffices to prove
--    `X`.
--
--    Here is a variant of a proof from above, using forward reasoning
--    throughout instead of backward reasoning.
-- TERSE: ***
-- TERSE: The ordinary `apply` tactic is a form of "backward
--    reasoning."  It says "We're trying to prove `X` and we know
--    `Y → X`, so if we can prove `Y` we'll be done."
--
--    By contrast, forward reasoning says "We know `Y` and we know
--    `Y → X`, so we also know `X`."
--    In Lean, we can do forward reasoning with `have` or by using
--    `apply ... at ...`.
-- HIDEFROMADVANCED

theorem silly4 : ∀ (n m p q : Nat),
    (n = m → p = q) →
    m = n →
    q = p := by
  intro n m p q EQ H
  symm at H; have H' := EQ H; symm; exact H'

-- /HIDEFROMADVANCED
-- FULL: Forward reasoning starts from what is _given_ (premises,
--    previously proven theorems) and iteratively draws conclusions from
--    them until the goal is reached.  Backward reasoning starts from
--    the _goal_ and iteratively reasons about what would imply the
--    goal, until premises or previously proven theorems are reached.
--
--    The informal proofs seen in math or computer science classes tend
--    to use forward reasoning.  By contrast, idiomatic use of Lean
--    generally favors backward reasoning, though in some situations the
--    forward style can be easier to think about.

-- ######################################################################
-- * Specializing Hypotheses

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "Another handy tactic for manipulating hypotheses is `specialize`.
--    ... If `H` is a quantified hypothesis in the current context -- i.e.,
--    `H : forall (x:T), P` -- then `specialize H with (x := e)` will
--    change `H` so that it looks like `P` with `x` replaced by `e`."
-- ADAPTED:
-- Another handy tactic for manipulating hypotheses is `specialize`.
--    It works like this:
--
--    If `H` is a quantified hypothesis in the current context -- i.e.,
--    `H : ∀ (x : T), P` -- then `specialize H e` will change `H` so
--    that it looks like `P` with `x` replaced by `e`.
--
--    For example:

theorem specialize_example : ∀ n,
    (∀ m, m * n = 0) →
    n = 0 := by
  intro n H
  specialize H 1
  rw [one_mul] at H
  exact H

-- FULL
-- EX3 (nth_error_always_none)

-- Use `specialize` to prove the following lemma, following the
--    model of `specialize_example` above. Do not use `induction`.
theorem nth_error_always_none : ∀ (l : List Nat),
    (∀ i, nthError l i = none) →
    l = [] := by
  -- ADMITTED
  intro l H; cases l
  case nil => rfl
  case cons h l' =>
    specialize H 0
    dsimp [nthError] at H
    contradiction
-- /ADMITTED
-- []
-- /FULL

-- Using `specialize` before `apply` gives us yet another way to
--    control where `apply` does its work.
theorem trans_eq_example''' : ∀ (a b c d e f : Nat),
    [a, b] = [c, d] →
    [c, d] = [e, f] →
    [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  have H := trans_eq _ [c, d] _ eq1 eq2
  exact H

-- Things to note:
--    - We can use previously proved theorems (like `trans_eq`) as
--      functions, applying them directly to arguments.
--    - In Lean, we can also use `have` to name intermediate results.

-- ######################################################################
-- * Varying the Induction Hypothesis

-- TERSE
-- Recall this function for doubling a natural number from the
--    \CHAP{Induction} chapter:

-- HIDE: Needs to be repeated here because double only appears in the
--    FULL version of Induction.lean!
-- (double is already imported from Induction.lean, so we don't
--    redefine it here)
-- /TERSE

-- FULL: Sometimes it is important to control the exact form of the
--    induction hypothesis when carrying out inductive proofs in Lean.
--    In particular, we may need to be careful about which of the
--    assumptions we move (using `intro`) from the goal to the context
--    before invoking the `induction` tactic.
--
--    For example, suppose we want to show that `double` is injective --
--    i.e., that it maps different arguments to different results:
--
--        theorem double_injective: ∀ n m,
--          double n = double m →
--          n = m.
--
--    The way we start this proof is a bit delicate: if we begin it with
--
--        intro n; induction n
--
--    then all will be well.  But if we begin it with introducing _both_
--    variables
--
--        intro n m; induction n
--
--    we get stuck in the middle of the inductive case...
-- TERSE: ***
-- TERSE: Suppose we want to show that `double` is injective (i.e.,
--    it maps different arguments to different results).  The way we
--    _start_ this proof is a little bit delicate:

theorem double_injective_FAILED : ∀ (n m : Nat),
    double n = double m →
    n = m := by
  intro n m; induction n
  case zero =>
    dsimp [double]; intro eq; cases m
    case zero => rfl
    case succ m' => dsimp [double] at eq; contradiction
  case succ n' IHn' =>
    intro eq; cases m
    case zero => dsimp [double] at eq; contradiction
    case succ m' =>
      congr

-- At this point, the induction hypothesis (`IHn'`) does _not_ give us
--    `n' = m'` -- there is an extra `succ` in the way -- so the goal is
--    not provable.

      sorry

-- TERSE: ***
-- HIDEFROMADVANCED

-- What went wrong?

-- FULL: The problem is that, at the point where we invoke the
--    induction hypothesis, we have already introduced `m` into the
--    context -- intuitively, we have told Lean, "Let's consider some
--    particular `n` and `m`..." and we now have to prove that, if
--    `double n = double m` for _these particular_ `n` and `m`, then
--    `n = m`.
--
--    The next tactic, `induction n` says to Lean: We are going to show
--    the goal by induction on `n`.  That is, we are going to prove, for
--    _all_ `n`, that the proposition
--
--      - `P n` = "if `double n = double m`, then `n = m`"
--
--    holds, by showing
--
--      - `P 0`
--
--         (i.e., "if `double 0 = double m` then `0 = m`") and
--
--      - `P n → P (n + 1)`
--
--        (i.e., "if `double n = double m` then `n = m`" implies "if
--        `double (n + 1) = double m` then `n + 1 = m`").
--
--    If we look closely at the second statement, it is saying something
--    rather strange: that, for a _particular_ `m`, if we know
--
--      - "if `double n = double m` then `n = m`"
--
--    then we can prove
--
--       - "if `double (n + 1) = double m` then `n + 1 = m`".
--
--    To see why this is strange, let's think of a particular `m` --
--    say, `5`.  The statement is then saying that, if we know
--
--      - `Q` = "if `double n = 10` then `n = 5`"
--
--    then we can prove
--
--      - `R` = "if `double (n + 1) = 10` then `n + 1 = 5`".
--
--    But knowing `Q` doesn't give us any help at all with proving `R`!
--    If we tried to prove `R` from `Q`, we would start with something
--    like "Suppose `double (n + 1) = 10`..." but then we'd be stuck:
--    knowing that `double (n + 1)` is `10` tells us nothing helpful
--    about whether `double n` is `10` (indeed, it strongly suggests
--    that `double n` is _not_ `10`!!), so `Q` is useless.

-- Trying to carry out this proof by induction on `n` when `m` is
--    already in the context doesn't work because we are then trying to
--    prove a statement involving _every_ `n` but just a _particular_ `m`.
-- /HIDEFROMADVANCED

-- TERSE: ***
-- A successful proof of `double_injective` keeps `m` universally
--    quantified in the goal statement at the point where the
--    `induction` tactic is invoked on `n`:

theorem double_injective : ∀ (n m : Nat),
    double n = double m →
    n = m := by
  intro n; induction n
  case zero =>
    intro m eq; dsimp [double] at eq; cases m
    case zero => rfl
    case succ m' => dsimp [double] at eq; contradiction
  case succ n' IHn' =>
-- FULL

-- Notice that both the goal and the induction hypothesis are
--    different this time: the goal asks us to prove something more
--    general (i.e., we must prove the statement for _every_ `m`), but
--    the induction hypothesis `IHn'` is correspondingly more flexible,
--    allowing us to choose any `m` we like when we apply it.

-- /FULL
    intro m eq
-- FULL

-- Now we've chosen a particular `m` and introduced the assumption
--    that `double n = double m`.  Since we are doing a case analysis on
--    `n`, we also need a case analysis on `m` to keep the two in sync.

-- /FULL
    cases m
    case zero =>
-- FULL

-- The 0 case is trivial:

-- /FULL
      dsimp [double] at eq; contradiction
    case succ m' =>
      congr
-- FULL

-- Since we are now in the second branch of the `cases m`, the
--    `m'` mentioned in the context is the predecessor of the `m` we
--    started out talking about.  Since we are also in the `succ` branch of
--    the induction, this is perfect: if we instantiate the generic `m`
--    in the IH with the current `m'` (this instantiation is performed
--    automatically by `apply` in the next step), then `IHn'` gives
--    us exactly what we need to finish the proof.

-- /FULL
      apply IHn'; dsimp [double] at eq; omega

-- HIDEFROMADVANCED
-- TERSE: ***
-- The thing to take away from all this is that you need to be
--    careful, when using induction, that you are not trying to prove
--    something too specific: When proving a property quantified over
--    variables `n` and `m` by induction on `n`, it is sometimes crucial
--    to leave `m` "generic."

-- /HIDEFROMADVANCED
-- FULL: The following exercise, which further strengthens the link between
--    `==` and `=`, follows the same pattern.
-- TERSE: The following theorem, which further strengthens the link between
--    `==` and `=`, follows the same pattern.
-- FULL
-- EX2 (eqb_true)
-- /FULL
theorem eqb_true : ∀ (n m : Nat),
    (n == m) = true → n = m := by
-- FULL
  -- ADMITTED
-- /FULL
-- TERSE
  -- WORKINCLASS
-- /TERSE
  intro n; induction n
  case zero =>
    intro m; cases m
    case zero => intro _; rfl
    case succ m' => dsimp [BEq.beq, beq]; intro contra; contradiction
  case succ n' IHn' =>
    intro m; cases m
    case zero => dsimp [BEq.beq, beq]; intro contra; contradiction
    case succ m' =>
      dsimp [BEq.beq, beq]; intro H
      congr; exact IHn' m' H
-- TERSE
  -- /WORKINCLASS
-- /TERSE
-- FULL
-- /ADMITTED
-- GRADE_THEOREM 2: eqb_true
-- []

-- EX2AM? (eqb_true_informal)
-- Give a careful informal proof of `eqb_true`, stating the induction
--    hypothesis explicitly and being as explicit as possible about
--    quantifiers, everywhere.

-- SOLUTION
-- _Theorem_: For all natural numbers `n` and `m`, if `(n == m) =
--       true`, then `n = m`.
--
--    _Proof_: We argue by induction on `n`.
--
--      - Base case: `n = 0`.  We must show, for all natural numbers
--        `m`, that `(0 == m) = true` implies `0 = m`.  We proceed by
--        cases on `m`.
--
--          - If `m = 0`, we must show that `(0 == 0) = true` implies
--            `0 = 0`, which holds by reflexivity.
--
--          - If `m = m' + 1` for some `m'`, we must show that
--            `(0 == (m' + 1)) = true` implies `0 = m' + 1`.  But
--            `(0 == (m' + 1))` evaluates to `false`, so the antecedent
--            of this implication is `false = true`, which is absurd,
--            and hence the whole implication is true.
--
--      - Inductive case: `n = n' + 1`.  We must show that for all
--        natural numbers `m`, `((n' + 1) == m) = true` implies
--        `n' + 1 = m`.
--
--        We may assume the induction hypothesis: for all natural
--        numbers `m`, `(n' == m) = true` implies `n' = m`.
--
--        We again proceed by cases on `m`.
--
--          - If `m = 0`, we must show that `((n' + 1) == 0) = true`
--            implies `n' + 1 = m`.  But `((n' + 1) == 0)` evaluates to
--            `false`, so the antecedent of this implication is again
--            absurd, and hence the whole implication is true.
--
--          - If `m = m' + 1` for some `m'`, we must show that
--            `((n' + 1) == (m' + 1)) = true` implies `n' + 1 = m' + 1`.
--            So let us assume `((n' + 1) == (m' + 1)) = true`.  This
--            simplifies to `(n' == m') = true`.  Hence we can apply the
--            induction hypothesis (with `m` instantiated to `m'`) to
--            obtain `n' = m'`.  Hence, to show `n' + 1 = m' + 1` it
--            suffices to show `n' + 1 = n' + 1`, which is true by
--            reflexivity. []
-- /SOLUTION

-- GRADE_MANUAL 2: informal_proof
-- []

-- HIDEFROMADVANCED
-- EX3! (plus_n_n_injective)
-- TERSE: ***
-- In addition to being careful about how you use `intro`, practice
--    using `at` variants in this proof.  (Hint: use `succ_add`.)
theorem plus_n_n_injective : ∀ (n m : Nat),
    n + n = m + m →
    n = m := by
  -- ADMITTED
  intro n; induction n
  case zero =>
    intro m; intro eq; cases m
    case zero => rfl
    case succ m' => simp at eq
  case succ n' IHn' =>
    intro m eq; cases m
    case zero => simp at eq
    case succ m' =>
      congr; apply IHn'
      rw [succ_add, succ_add] at eq
      omega
-- /ADMITTED
-- GRADE_THEOREM 3: plus_n_n_injective
-- []
-- /HIDEFROMADVANCED
-- /FULL

-- TERSE: ***
-- The strategy of doing fewer `intro`s before an `induction` to
--    obtain a more general IH doesn't always work; sometimes some
--    _rearrangement_ of quantified variables is needed.  Suppose, for
--    example, that we wanted to prove `double_injective` by induction
--    on `m` instead of `n`.

theorem double_injective_take2_FAILED : ∀ (n m : Nat),
    double n = double m →
    n = m := by
  intro n m; induction m
  case zero =>
    dsimp [double]; intro eq; cases n
    case zero => rfl
    case succ n' => dsimp [double] at eq; contradiction
  case succ m' IHm' =>
    intro eq; cases n
    case zero => dsimp [double] at eq; contradiction
    case succ n' =>
      congr
      -- We are stuck here, just like before.
      sorry

-- TERSE: ***
-- The problem is that, to do induction on `m`, we must first
--    introduce `n`.  (If we simply say `induction m` without
--    introducing anything first, Lean will automatically introduce `n`
--    for us!)

-- HIDEFROMADVANCED
-- FULL: What can we do about this?  One possibility is to rewrite the
--    statement of the lemma so that `m` is quantified before `n`.  This
--    works, but it's not nice: We don't want to have to twist the
--    statements of lemmas to fit the needs of a particular strategy for
--    proving them!  Rather we want to state them in the clearest and
--    most natural way.

-- /HIDEFROMADVANCED
-- TERSE: ***

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "What we can do instead is to first introduce all the quantified
--    variables and then _re-generalize_ one or more of them, selectively
--    taking variables out of the context and putting them back at the
--    beginning of the goal.  The `generalize dependent` tactic does this."
-- ADAPTED:
-- What we can do instead is to first introduce all the quantified
--    variables and then _re-generalize_ one or more of them, selectively
--    taking variables out of the context and putting them back at the
--    beginning of the goal.  Lean's `revert` tactic does this.

theorem double_injective_take2 : ∀ (n m : Nat),
    double n = double m →
    n = m := by
  intro n m
  -- `n` and `m` are both in the context
  revert n
  -- Now `n` is back in the goal and we can do induction on
  --    `m` and get a sufficiently general IH.
  induction m
  case zero =>
    intro n eq; dsimp [double] at eq; cases n
    case zero => rfl
    case succ n' => dsimp [double] at eq; contradiction
  case succ m' IHm' =>
    intro n eq; cases n
    case zero => dsimp [double] at eq; contradiction
    case succ n' =>
      congr; apply IHm'
      dsimp [double] at eq; omega

-- FULL: Let's look at an informal proof of this theorem.  Note that
--    the proposition we prove by induction leaves `n` quantified,
--    corresponding to the use of `revert` in our formal proof.
--
--    _Theorem_: For any nats `n` and `m`, if `double n = double m`,
--      then `n = m`.
--
--    _Proof_: Let `m` be a `Nat`. We prove by induction on `m` that,
--      for any `n`, if `double n = double m` then `n = m`.
--
--      - First, suppose `m = 0`, and suppose `n` is a number such
--        that `double n = double m`.  We must show that `n = 0`.
--
--        Since `m = 0`, by the definition of `double` we have
--        `double n = 0`.  There are two cases to consider for `n`.  If
--        `n = 0` we are done, since `m = 0 = n`, as required.
--        Otherwise, if `n = n' + 1` for some `n'`, we derive a
--        contradiction: by the definition of `double`, we can calculate
--        `double n = (double n') + 2`, but this contradicts the
--        assumption that `double n = 0`.
--
--      - Second, suppose `m = m' + 1` and that `n` is again a number
--        such that `double n = double m`.  We must show that
--        `n = m' + 1`, with the induction hypothesis that for every
--        number `s`, if `double s = double m'` then `s = m'`.
--
--        By the fact that `m = m' + 1` and the definition of `double`,
--        we have `double n = (double m') + 2`.  There are two cases to
--        consider for `n`.
--
--        If `n = 0`, then by definition `double n = 0`, a contradiction.
--
--        Thus, we may assume that `n = n' + 1` for some `n'`, and again
--        by the definition of `double` we have
--        `(double n') + 2 = (double m') + 2`, which implies by
--        injectivity that `double n' = double m'`.  Instantiating the
--        induction hypothesis with `n'` thus allows us to conclude that
--        `n' = m'`, and it follows immediately that
--        `n' + 1 = m' + 1`.  Since `n' + 1 = n` and `m' + 1 = m`,
--        this is just what we wanted to show. []

-- ######################################################################
-- * Rewriting with conditional statements

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "Suppose that we want to show that `plus` is the inverse of
--    `minus`.  Since we are working with natural numbers, we need an
--    assumption to prevent `minus` from truncating its result."
-- ADAPTED:
-- Suppose that we want to show that addition is the inverse of
--    subtraction.  Since we are working with natural numbers, we need an
--    assumption to prevent subtraction from truncating its result.  With
--    this assumption, the induction hypothesis becomes
--    `∀ m, (n' <=? m) = true → (m - n') + n' = m`.  The beginning of
--    the proof uses techniques we have already seen -- in particular,
--    notice how we induct on `n` before introducing `m`, so that the
--    induction hypothesis becomes sufficiently general.

theorem sub_add_leb : ∀ (n m : Nat), (n <=? m) = true → (m - n) + n = m := by
  intro n; induction n
  case zero =>
    -- n = 0
    intro m H; cases m
    case zero => rfl
    case succ m' => rfl
  case succ n' IHn' =>
    -- n = n' + 1
    intro m H; cases m
    case zero =>
      -- m = 0
      dsimp [leb] at H; contradiction
    case succ m' =>
      -- m = m' + 1
      dsimp [leb] at H
      rw [succ_sub_succ]
-- FULL: At this point, we need to show `(m' - n') + (n' + 1) = m' + 1`
--    from the assumption `(n' <=? m') = true`.  We could use the `have`
--    tactic to prove `(m' - n') + n' = m'` from the induction
--    hypothesis.  However, we can also just use `rw` directly: if we
--    rewrite with a conditional statement of the form `P → a = b`, then
--    Lean tries to rewrite with `a = b`, and then asks us to prove `P`
--    in a new subgoal.  If the statement has more than one assumption,
--    then we get one subgoal for each assumption.
-- TERSE: We could use the `have` tactic to prove `(m' - n') + n' = m'`
--    from the IH. However, we can also just use `rw` directly...
      rw [add_succ]; congr 1; exact IHn' m' H

-- FULL
-- EX3! (gen_dep_practice)
-- Prove this by induction on `l`.

theorem nth_error_after_last : ∀ (n : Nat) (α : Type) (l : List α),
    l.length = n →
    nthError l n = none := by
  -- ADMITTED
  intro n α l; revert n; induction l
  case nil => intro n _; rfl
  case cons x l' IHl' =>
    intro n eq; dsimp [List.length] at eq; dsimp [nthError]
    rw [← eq]; exact IHl' l'.length rfl
-- /ADMITTED
-- GRADE_THEOREM 3: nth_error_after_last
-- []
-- /FULL

-- ######################################################################
-- * Unfolding Definitions

-- It sometimes happens that we need to manually unfold a name that
--    has been introduced by a `def` so that we can manipulate
--    the expression it stands for.
--
--    For example, if we define...

def square (n : Nat) : Nat := n * n

-- ...and try to prove a simple fact about `square`...

theorem square_mult : ∀ (n m : Nat), square (n * m) = square n * square m := by
  intro n m
  -- `dsimp` or `simp` doesn't simplify enough here

-- ...we appear to be stuck: we haven't proved any other facts about
--    `square`, so there is nothing we can `apply` or `rw` with.

-- TERSE: ***
-- To make progress, we can manually `unfold` the definition of
--    `square`:

  unfold square

-- Now we have plenty to work with: both sides of the equality are
--    expressions involving multiplication, and we have lots of facts
--    about multiplication at our disposal.  In particular, we know that
--    it is commutative and associative, and from these it is not hard
--    to finish the proof.

  rw [mul_assoc]
  have H : n * m * n = n * n * m := by
    rw [mul_comm (n * m) n, mul_assoc]
  rw [H, mul_assoc]

-- TERSE: ***
-- At this point, a bit deeper discussion of unfolding and
--    simplification is in order.
--
--    We already have observed that tactics like `dsimp`, `rfl`,
--    and `apply` will often unfold the definitions of functions
--    automatically when this allows them to make progress.  For
--    example, if we define `foo m` to be the constant `5`...

def foo (_x : Nat) : Nat := 5

-- .... then the `dsimp` in the following proof (or the
--    `rfl`, if we omit the `dsimp`) will unfold `foo m` to
--    `(fun x => 5) m` and further simplify this expression to just
--    `5`.

theorem silly_fact_1 : ∀ m, foo m + 1 = foo (m + 1) + 1 := by
  intro m
  dsimp [foo]

-- TERSE: ***
-- But this automatic unfolding is somewhat conservative.  For
--    example, if we define a slightly more complicated function
--    involving a pattern match...

def bar (x : Nat) : Nat :=
  match x with
  | 0 => 5
  | _ + 1 => 5

-- ...then the analogous proof will get stuck:

theorem silly_fact_2_FAILED : ∀ m, bar m + 1 = bar (m + 1) + 1 := by
  intro m
  dsimp [bar] -- Does nothing useful with bar!
  sorry

-- FULL: The reason that `dsimp` doesn't make progress here is that
--    `bar m` involves a `match` whose scrutinee, `m`, is a variable,
--    so the `match` cannot be simplified further.  It is not smart
--    enough to notice that the two branches of the `match` are
--    identical, so it gives up on unfolding `bar m` and leaves it alone.

-- TERSE: ***
-- FULL: At this point, there are two ways to make progress.  One is to use
--    `cases m` to break the proof into two cases, each focusing on a
--    more concrete choice of `m` (`0` vs `_ + 1`).  In each case, the
--    `match` inside of `bar` can now make progress, and the proof is
--    easy to complete.
-- TERSE: There are now two ways make progress.
--
--    First, we can use `cases m` to break the proof into two cases:

theorem silly_fact_2 : ∀ m, bar m + 1 = bar (m + 1) + 1 := by
  intro m
  cases m
  case zero => rfl
  case succ m' => rfl

-- This approach works, but it depends on our recognizing that the
--    `match` hidden inside `bar` is what was preventing us from making
--    progress.

-- TERSE: ***
-- A more straightforward way forward is to explicitly tell Lean to
--    unfold `bar`.

theorem silly_fact_2' : ∀ m, bar m + 1 = bar (m + 1) + 1 := by
  intro m
  unfold bar

-- Now it is apparent that we are stuck on the `match` expressions on
--    both sides of the `=`, and we can use `cases` to finish the
--    proof without thinking so hard.

  cases m
  case zero => rfl
  case succ m' => rfl

-- ######################################################################
-- * Using `cases` on Compound Expressions

-- NOTE: The following section heading was adapted from the Rocq original:
-- ORIGINAL: "Using `destruct` on Compound Expressions"
-- ADAPTED: (changed `destruct` to `cases` since that's the Lean equivalent)

-- FULL: We have seen many examples where `cases` is used to
--    perform case analysis of the value of some variable.  Sometimes we
--    need to reason by cases on the result of some _expression_.  We
--    can also do this with `cases`.
--
--    Here are some examples:
-- TERSE: The `cases` tactic can be used on expressions as well as
--    variables:

def sillyfun (n : Nat) : Bool :=
  if n == 3 then false
  else if n == 5 then false
  else false

theorem sillyfun_false : ∀ (n : Nat),
    sillyfun n = false := by
  intro n; unfold sillyfun
  -- NOTE: The following comment was adapted from the Rocq original:
  -- ORIGINAL: "destruct (n =? 3) eqn:E1"
  -- ADAPTED: In Lean, we can use `split` to handle if-then-else,
  --    or use `cases` with `Decidable` instances. Here we use `split`
  --    which creates one subgoal per branch of the `if`.
  split
  case isTrue h => rfl
  case isFalse h =>
    split
    case isTrue h' => rfl
    case isFalse h' => rfl

-- FULL: After unfolding `sillyfun` in the above proof, we find that
--    we are stuck on `if (n == 3) then ... else ...`.  We use `split`
--    (which handles if-then-else by case-splitting on the condition)
--    to let us reason about both cases.
--
--    In general, `split` can be used to handle any match or if-then-else
--    expression in the goal.

-- FULL
-- EX3 (combine_split)
-- Here is an implementation of the `split` function from
--    chapter \CHAP{Poly} (already imported).  Prove that `split` and
--    `combine` are inverses in the following sense:

theorem combine_split : ∀ (α β : Type) (l : List (α × β)) (l1 : List α) (l2 : List β),
    split l = (l1, l2) →
    combine l1 l2 = l := by
  -- ADMITTED
  intro α β l; induction l
  case nil =>
    intro l1 l2 H
    dsimp [split] at H
    injection H with h1 h2; rw [← h1, ← h2]; rfl
  case cons p l' IHl' =>
    intro l1 l2 H
    obtain ⟨x, y⟩ := p
    dsimp [split] at H
    -- split the result of the recursive call
    match hsplit : split l' with
    | (lx, ly) =>
      rw [hsplit] at H
      injection H with h1 h2
      rw [← h1, ← h2]; dsimp [combine]
      congr 1; exact IHl' lx ly hsplit
-- /ADMITTED
-- []
-- /FULL

-- TERSE: ***
-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: "The `eqn:` part of the `destruct` tactic is optional; although
--    we've chosen to include it most of the time, for the sake of
--    documentation, it can often be omitted without harm."
-- ADAPTED:
-- When doing case analysis in Lean, we can use `match ... with` to
--    pattern match on compound expressions while keeping the relevant
--    equalities in scope.  This is important when we need to remember
--    what case we're in.

-- FULL: For example, suppose we define a function `sillyfun1` like
--    this:

def sillyfun1 (n : Nat) : Bool :=
  if n == 3 then true
  else if n == 5 then true
  else false

-- FULL: Now suppose that we want to convince Lean that `sillyfun1 n`
--    yields `true` only when `n` is odd.

theorem sillyfun1_odd : ∀ (n : Nat),
    sillyfun1 n = true →
    odd n = true := by
  intro n eq; unfold sillyfun1 at eq
  split at eq
  case isTrue h =>
    -- n == 3 = true
    have h' := eqb_true n 3 h
    rw [h']; rfl
  case isFalse h =>
    split at eq
    case isTrue h' =>
      -- n == 5 = true
      have h'' := eqb_true n 5 h'
      rw [h'']; rfl
    case isFalse h' =>
      -- false = true, contradiction
      contradiction

-- FULL
-- EX2 (destruct_eqn_practice)
theorem bool_fn_applied_thrice :
    ∀ (f : Bool → Bool) (b : Bool),
    f (f (f b)) = f b := by
  -- ADMITTED
  intro f b
  cases b
  case true =>
    cases hft : f true
    case true => rw [hft, hft]
    case false =>
      cases hff : f false
      case true => exact hft
      case false => exact hff
  case false =>
    cases hff : f false
    case true =>
      cases hft : f true
      case true => exact hft
      case false => exact hff
    case false => rw [hff, hff]
-- /ADMITTED
-- GRADE_THEOREM 2: bool_fn_applied_thrice
-- []

-- ################################################################
-- * Review

-- LATER: NDS'25 This list is getting pretty long; maybe it should be
--    further divided into categories (I'd suggest: Basic hypotheses/goal
--    manipulation, equality, inductive types, others)

-- NOTE: The following comment was adapted from the Rocq original:
-- ORIGINAL: listing of Rocq tactics like `intros`, `reflexivity`, `apply`,
--    `simpl`, `rewrite`, `symmetry`, `transitivity`, `unfold`, `destruct`,
--    `induction`, `injection`, `discriminate`, `replace`, `assert`,
--    `generalize dependent`, `f_equal`.
-- ADAPTED:
-- We've now talked about many of Lean's most fundamental tactics.
--    We'll introduce a few more in the coming chapters, and later on
--    we'll see some more powerful _automation_ tactics that make Lean
--    help us with low-level details.  But basically we've got what we
--    need to get work done.
--
--    Here are the ones we've seen:
--
--      - `intro` / `intros`: move hypotheses/variables from goal to context
--
--      - `rfl`: finish the proof (when the goal looks like `e = e`)
--
--      - `exact`: prove goal using a hypothesis, lemma, or constructor
--        that matches the goal exactly
--
--      - `apply`: like `exact`, but can leave subgoals for remaining
--        premises of an implication or universally quantified statement
--
--      - `have H := L H'`: apply a lemma `L` to hypothesis `H'` and
--        name the result (forward reasoning)
--
--      - `specialize H e`: refine a universally quantified hypothesis
--        by providing a specific argument
--
--      - `dsimp` / `unfold`: simplify or unfold definitions in the goal
--
--      - `dsimp ... at H` / `unfold ... at H`: ... or a hypothesis
--
--      - `rw`: use an equality hypothesis (or lemma) to rewrite
--        the goal
--
--      - `rw ... at H`: ... or a hypothesis
--
--      - `symm`: changes a goal of the form `t = u` into `u = t`
--
--      - `symm at H`: changes a hypothesis of the form `t = u` into
--        `u = t`
--
--      - `calc`: chain a sequence of equalities (transitivity)
--
--      - `unfold`: replace a defined constant by its right-hand side in
--        the goal
--
--      - `unfold ... at H`: ... or a hypothesis
--
--      - `cases`: case analysis on values of inductively defined types
--
--      - `split`: case-split on if-then-else or match expressions in
--        the goal
--
--      - `split at H`: ... or a hypothesis
--
--      - `induction`: induction on values of inductively defined types
--
--      - `injection ... with ...`: reason by injectivity on equalities
--        between values of inductively defined types
--
--      - `contradiction`: reason by disjointness of constructors (or
--        any other contradictory hypothesis)
--
--      - `congr`: change a goal of the form `f x = f y` into `x = y`
--
--      - `have`: introduce a "local lemma" and prove it
--
--      - `revert x`: move the variable `x` (and anything else that
--        depends on it) from the context back to the goal formula
-- /FULL

-- TERSE
-- ######################################################################
-- * Micro Sermon

-- Mindless proof-hacking is a terrible temptation...
--
--    Try to resist!

-- /TERSE
-- FULL
-- ######################################################################
-- * Additional Exercises

-- EX3 (eqb_sym)
theorem eqb_sym : ∀ (n m : Nat),
    (n == m) = (m == n) := by
  -- ADMITTED
  intro n; induction n
  case zero =>
    intro m; cases m
    case zero => rfl
    case succ m' => rfl
  case succ n' IHn' =>
    intro m; cases m
    case zero => rfl
    case succ m' => dsimp [BEq.beq, beq]; exact IHn' m'
-- /ADMITTED
-- GRADE_THEOREM 3: eqb_sym
-- []

-- EX3AM? (eqb_sym_informal)
-- Give an informal proof of this lemma that corresponds to your
--    formal proof above:
--
--    Theorem: For any `Nat`s `n` `m`, `(n == m) = (m == n)`.
--
--    Proof:
-- SOLUTION
--
--    Let an arbitrary nat `n` be given.  Proceed by induction
--    on `n`.
--
--    - For the base case, we have `n = 0`.  Let `m` be given.
--      We must show that
--
--        (0 == m) = (m == 0)
--
--      Either `m = 0` or not.
--
--      - If `m = 0`, we must show `(0 == 0) = (0 == 0)`,
--        which is true by reflexivity.
--
--      - Otherwise, `m = m' + 1` for some `m'`, and we must show
--        `(0 == (m' + 1)) = ((m' + 1) == 0)`. By the definition
--        of `beq`, both sides are `false`.
--
--    - In the inductive case, we have `n = n' + 1` for some
--      `n'` such that, for any `m`,
--
--        (n' == m) = (m == n')
--
--      Let `m` be given.  Again, `m` is either zero or nonzero.
--
--      - Suppose first `m = 0`.  It's
--        enough to show `((n' + 1) == 0) = (0 == (n' + 1))`.
--        By the definition of `beq`, both sides are `false`.
--
--      - Otherwise, `m = m' + 1` for some `m'`.  By the
--        assumption, it's enough to show:
--
--          ((n' + 1) == (m' + 1)) = ((m' + 1) == (n' + 1))
--
--        And, by the definition of `beq`, this reduces to showing:
--
--          (n' == m') = (m' == n')
--
--        which is exactly the induction hypothesis.
-- /SOLUTION
-- []
-- /FULL

-- FULL
-- EX3? (eqb_trans)
theorem eqb_trans : ∀ (n m p : Nat),
    (n == m) = true →
    (m == p) = true →
    (n == p) = true := by
  -- ADMITTED
  intro n m p Hnm Hmp
  have Hnm' := eqb_true n m Hnm
  rw [Hnm']; exact Hmp
-- /ADMITTED
-- []
-- /FULL

-- FULL
-- EX3AM (split_combine)
-- We proved, in an exercise above, that `combine` is the inverse of
--    `split`.  Complete the definition of `split_combine_statement`
--    below with a property that states that `split` is the inverse of
--    `combine`. Then, prove that the property holds.
--
--    Hint: Take a look at the definition of `combine` in \CHAP{Poly}.
--    Your property will need to account for the behavior of `combine`
--    in its base cases, which possibly drop some list elements.

def split_combine_statement : Prop
  -- (": Prop" means that we are giving a name to a
  --    logical proposition here.)
  -- ADMITDEF
  :=
  ∀ (α β : Type) (l1 : List α) (l2 : List β),
    l1.length = l2.length → split (combine l1 l2) = (l1, l2)
-- /ADMITDEF

theorem split_combine : split_combine_statement := by
-- ADMITTED
  intro α β; intro l1; induction l1
  case nil =>
    intro l2 Heq; cases l2
    case nil => rfl
    case cons y l2' => contradiction
  case cons x l1' IHl1' =>
    intro l2 Heq; cases l2
    case nil => contradiction
    case cons y l2' =>
      dsimp [combine, split]
      dsimp [List.length] at Heq; injection Heq with Heq'
      rw [IHl1' l2' Heq']
-- /ADMITTED
-- GRADE_MANUAL 3: split_combine
-- []
-- /FULL

-- FULL
-- EX3A (filter_exercise)
theorem filter_exercise : ∀ (α : Type) (test : α → Bool)
    (x : α) (l lf : List α),
    filter test l = x :: lf →
    test x = true := by
  -- ADMITTED
  intro α test x l; induction l
  case nil => intro lf eq; dsimp [filter] at eq; contradiction
  case cons v' l' IHl' =>
    intro lf eq; dsimp [filter] at eq
    split at eq
    case isTrue h =>
      injection eq with eqhead _; rw [← eqhead]; exact h
    case isFalse h =>
      exact IHl' lf eq
-- /ADMITTED
-- GRADE_THEOREM 3: filter_exercise
-- []

-- EX4A! (forall_exists_challenge)
-- Define two recursive functions, `forallb` and `existsb`.  The
--    first checks whether every element in a list satisfies a given
--    predicate:
--
--      forallb odd [1, 3, 5, 7, 9] = true
--      forallb (! ·) [false, false] = true
--      forallb even [0, 2, 4, 5] = false
--      forallb (· == 5) [] = true
--
--    The second checks whether there exists an element in the list that
--    satisfies a given predicate:
--
--      existsb (· == 5) [0, 2, 3, 6] = false
--      existsb (· && true) [true, true, false] = true
--      existsb odd [1, 0, 0, 0, 0, 3] = true
--      existsb even [] = false
--
--    Next, define a _nonrecursive_ version of `existsb` -- call it
--    `existsb'` -- using `forallb` and `not`.
--
--    Finally, prove a theorem `existsb_existsb'` stating that
--    `existsb'` and `existsb` have the same behavior.

def forallb {α : Type} (test : α → Bool) (l : List α) : Bool :=
  -- ADMITDEF
  match l with
  | [] => true
  | x :: l' => (test x) && (forallb test l')
  -- /ADMITDEF

example : forallb odd [1, 3, 5, 7, 9] = true := by rfl  -- ADMITTED
example : forallb (! ·) [false, false] = true := by rfl  -- ADMITTED
example : forallb even [0, 2, 4, 5] = false := by rfl  -- ADMITTED
example : forallb (· == 5) ([] : List Nat) = true := by rfl  -- ADMITTED

def existsb {α : Type} (test : α → Bool) (l : List α) : Bool :=
  -- ADMITDEF
  match l with
  | [] => false
  | x :: l' => (test x) || (existsb test l')
  -- /ADMITDEF

example : existsb (· == 5) [0, 2, 3, 6] = false := by rfl  -- ADMITTED
example : existsb (· && true) [true, true, false] = true := by rfl  -- ADMITTED
example : existsb odd [1, 0, 0, 0, 0, 3] = true := by rfl  -- ADMITTED
example : existsb even ([] : List Nat) = false := by rfl  -- ADMITTED

def existsb' {α : Type} (test : α → Bool) (l : List α) : Bool :=
  -- ADMITDEF
  !(forallb (fun x => !(test x)) l)
  -- /ADMITDEF

theorem existsb_existsb' : ∀ (α : Type) (test : α → Bool) (l : List α),
    existsb test l = existsb' test l := by
  -- ADMITTED
  intro α test l; unfold existsb'; induction l
  case nil => rfl
  case cons x l' IHl' =>
    dsimp [existsb, forallb]
    cases h : test x
    case true => rfl
    case false => simp; exact IHl'
-- /ADMITTED

-- GRADE_THEOREM 6: existsb_existsb'
-- []
-- /FULL
