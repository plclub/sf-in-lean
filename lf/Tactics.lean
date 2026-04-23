-- Tactics: More Basic Tactics

/- INSTRUCTORS: This material is a bit too much to cover in detail in
   one 80-minute lecture.  90-100 minutes is more reasonable, but that
   may still involve going a bit fast at the end. -/

/- SOONER: This chapter could maybe use one or two more WORKINCLASS
   tags... -/
/- SOONER: BCP 25: General comment: All the previous chapters have
   felt pretty smooth. This one suddenly feels like we're throwing a
   huge amount of information at them, with little scaffolding -- just
   a bunch of miscellaneous tactics and examples.  Wish it flowed
   better, somehow. -/

/-  FULL: This chapter introduces several additional proof strategies
    and tactics that allow us to begin proving more interesting
    properties of functional programs.

    We will see:
    * how to use auxiliary lemmas in both "forward-" and
      "backward-style" proofs;
    * how to reason about data constructors -- in particular, how to
      use the fact that they are injective and disjoint;
    * how to strengthen an induction hypothesis, and when such
      strengthening is required; and
    * more details on how to reason by case analysis. -/

-- HIDEFROMHTML

import Poly

-- ######################################################
-- # The `apply` Tactic *

/- FULL: We often encounter situations where the goal to be proved is
    _exactly_ the same as some hypothesis in the context or some
    previously proved lemma. -/
/- TERSE: The `apply` tactic is useful when some hypothesis or an
    earlier lemma exactly matches the goal: -/

theorem silly1 : forall (n m : Nat), n = m -> n = m := by
  intro n m eq
  /- Here, we could finish with `rw [eq]` as we
    have done several times before.  Or we can finish
    by using `apply`: -/
  apply eq

/- FULL: The `apply` tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. -/
-- TERSE: ***
/- `apply` also works with _conditional_ hypotheses: -/

theorem silly2 : forall (n m o p : Nat),
  n = m ->
  (n = m -> [n, o] = [m, p]) ->
  [n, o] = [m, p] := by
  intro n m o p eq1 eq2
  apply eq2
  apply eq1

-- HIDEFROMADVANCED
/- FULL: Typically, when we use `apply h`, the statement `h` will
    begin with a `forall` that introduces some _universally quantified variables_.

    When Lean matches the current goal against the conclusion of `h`,
    it will try to find appropriate values for these variables.  For
    example, when we do `apply eq2` in the following proof, the
    universal variable `q` in `eq2` gets instantiated with `n`, and
    `r` gets instantiated with `m`. -/
-- TERSE: ***
/- TERSE: Observe how Lean picks appropriate values for the
    `forall`-quantified variables of the hypothesis: -/

theorem silly2a : forall (n m : Nat),
  (n,n) = (m,m)  ->
  (forall (q r : Nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m] := by

  intro n m eq1 eq2
  apply eq2
  apply eq1

-- FULL
-- EX2? (silly_ex)
/- Complete the following proof using only `intros` and `apply`. -/
theorem silly_ex : forall p,
  (forall n, even n = true -> even (n + 1) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (p + 1) = true := by
  -- ADMITTED
  intro p eq1 eq2 eq3
  apply eq2; apply eq1; apply eq3
  -- /ADMITTED
-- []
-- /FULL

/- FULL: To use the `apply` tactic, the (conclusion of the) fact
    being applied must match the goal exactly (perhaps after
    simplification) -- for example, `apply` will not work if the left
    and right sides of the equality are swapped. -/
-- TERSE:
/- TERSE: The goal must match the hypothesis _exactly_ for `apply` to
    work: -/

theorem silly3 : forall (n m : Nat),
  n = m ->
  m = n := by
  intro n m H
  -- Here we cannot use `apply` directly...
  /- ...but we can use the `symm` tactic, which switches the left
      and right sides of an equality in the goal. -/
  symm; apply H

/- FULL -/
-- EX2 (apply_exercise1)
/- You can use `apply` with previously defined theorems, not
    just hypotheses in the context.  Use a
    previously-defined theorem about `rev` from \CHAP{Poly}.  Use
    that theorem as part of your (relatively short) solution to this
    exercise. You do not need `induction`. -/

theorem rev_exercise1 : forall α (l l' : List α),
  l = l'.rev ->
  l' = l.rev := by
  intro α l l' eq
  rw [eq]; symm
  apply rev_involutive
  -- /ADMITTED
-- GRADE_THEOREM 2: rev_exercise1
-- []

-- EX1M? (apply_rewrite)
/- Briefly explain the difference between the tactics `apply` and
    `rewrite`.  What are the situations where both can usefully be
    applied? -/

-- SOLUTION
/- The `rewrite` tactic is used to apply a known equality (a
    hypothesis from the context or a previously proved lemma) to
    modify the goal, replacing all occurrences of one side by the
    other.

    The `apply` tactic uses a known implication (a hypothesis from the
    context, a previously proved lemma, or a constructor) to replace a
    goal that matches the conclusion of the implication with subgoals,
    one for each premise of the implication.

    If the known fact is itself an equality (with no premises), then
    either tactic can be used.  (We will see below that each tactic
    can also be used to modify a hypothesis rather than the goal.) -/
-- /SOLUTION
-- []
-- /FULL
-- /HIDEFROMADVANCED

-- ###################################################### --
-- ## Supplying arguments to `apply`

/- HIDE: AAA dislikes the [...with...] variants of tactics, which he
   feels don't work very well.  But we (Arthur and BCP) decided to
   leave things alone for now, since removing [...with...] would
   require changing MANY proofs. -/

/- The following silly example uses two rewrites in a row to
    get from [[a;b]] to [[e;f]]. -/

theorem trans_eq_example : forall (a b c d e f : Nat),
     [a, b] = [c, d] ->
     [c, d] = [e, f] ->
     [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  rw [eq1, eq2]

-- TERSE: ***
/- Since this is a common pattern, we might like to pull it out as a
    lemma that records, once and for all, the fact that equality is
    transitive. -/

/- HIDE: Robert Rand: I found using m, n and o throughout this discussion
   super confusing -- m doesn't come between n and o! Rocq's eq_trans uses
   x, y and z, which is what I wanted to change this too anyhow. -/

theorem trans_eq : forall (α : Type) (x y z : α),
    x = y -> y = z -> x = z := by
  intro X x y z eq1 eq2
  rw [eq1, eq2]

/- FULL: Now, we should be able to use [trans_eq] to prove the above
    example.  However, to do this we need a slight refinement of the
    [apply] tactic. -/
-- TERSE: ***
/- TERSE: Applying this lemma to the example above requires a slight
    refinement of `apply`: -/

/- HIDE: Robert Rand: This one makes a nice workinclass. You can show
   the various ways around the problem, including named "with",
   unnamed "with", and (if you desire), explicitly providing the
   arguments to trans_eq. -/

theorem trans_eq_example' : forall (a b c d e f : Nat),
    [a, b] = [c, d] ->
    [c, d] = [e, f] ->
    [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
-- FULL
/- If we simply tell Lean `apply trans_eq` at this point, it can
    tell (by matching the goal against the conclusion of the lemma)
    that it should instantiate `α` with `List Nat`, `x` with `[a, b]`, and
    `z` with `[e,f]`.  However, the matching process doesn't determine
    an instantiation for `y`: we have to supply one explicitly by
    supplying arguments to `trans_eq` in the invocation of `apply` -/
-- /FULL
-- TERSE

/- Doing [apply trans_eq] doesn't work!  But... -/
-- /TERSE
  apply trans_eq (List Nat) [a, b] [c, d]
-- TERSE
-- ...does.

-- /TERSE
  apply eq1
  apply eq2

/- TODO: (DHS) This and below are new (my addition), thoughts? -/
/- In the previous example, we had to specify the `α` and `x` arguments
   to `trans_eq` before we could supply `[c, d]` for `y`. However,
   we just said that Lean was able to infer these arguments, so it's
   a bit redundant (and wordy) for us to do that. Thankfully,
   Lean allows us to use `_`s for positional arguments that it is able to infer. -/
theorem trans_eq_example'' : forall (a b c d e f : Nat),
    [a, b] = [c, d] ->
    [c, d] = [e, f] ->
    [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  apply trans_eq _ _ [c, d]
  apply eq1
  apply eq2

/- In fact, we can be even more concise. If we know the name of
   the argument we are supplying (in this case `y`), we can
   just name it directly, and avoid typing all those `_`s. -/
theorem trans_eq_example''' : forall (a b c d e f : Nat),
    [a, b] = [c, d] ->
    [c, d] = [e, f] ->
    [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  apply trans_eq (y := [c, d])
  apply eq1
  apply eq2

-- TERSE:
/- TODO: (DHS) if we decide we want to introduce `calc` earlier, we can
   remove this explanation or tweak it. -/
/- FULL: Lean also has a built-in tactic `calc` that
    accomplishes the same purpose as applying `trans_eq`.
    The tactic allows us to specify the in-between states
    of any transitive relation. -/
/- TERSE: `calc` is also available as a tactic. -/
theorem trans_eq_example'''' : forall (a b c d e f : Nat),
    [a, b] = [c, d] ->
    [c, d] = [e, f] ->
    [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  calc [a, b]
  _ = [c, d] := by rw [eq1]
  _ = [e, f] := by rw [eq2]

-- FULL
-- EX3? (trans_eq_exercise)
theorem trans_eq_exercise : forall (n m o p : Nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o) := by
  -- ADMITTED
  intro n m o p eq1 eq2
  calc (n + p)
  _ = m := by rw [eq2]
  _ = minustwo o := by rw [eq1]
-- /ADMITTED
-- []
-- /FULL


-- ######################################################
-- # The `injection` and `discriminate` Tactics
/- HIDE: Should we explain `discriminate` without an argument?  BCP 25: No. -/

/- FULL: Recall the definition of natural numbers:

     inductive Nat : Type :=
       | zero
       | succ (n : Nat).

    It is obvious from this definition that every number has one of
    two forms: either it is the constructor `0` or it is built by
    applying the constructor `.succ` to another number.  But there is more
    here than meets the eye: implicit in the definition are two
    additional facts:

    - The constructor `.succ` is _injective_ (or _one-to-one_).  That is,
      if `n + 1 = m + 1`, it must also be that `n = m`.

    - The constructors `0` and `.succ` are _disjoint_.  That is, `0` is not
      equal to `n + 1` for any `n`. -/

/- FULL: Similar principles apply to every inductively defined type:
    all constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the `cons` constructor
    is injective and the empty list `nil` is different from every
    non-empty list.  For booleans, `true` and `false` are different.
    (Since `true` and `false` take no arguments, their injectivity is
    neither here nor there.)  And so on. -/

/- TERSE: The constructors of inductive types are _injective_ (or
    _one-to-one_) and _disjoint_.

    E.g., for [Nat]...

       - if `n + 1 = m + 1` then it must be that `n = m`

       - `0` is not equal to `n + 1` for any `n`
-/

-- TERSE
/- We can _prove_ the injectivity of `succ` by using the `pred` function -/

theorem succ_injective : forall (n m : Nat),
  n + 1 = m + 1 ->
  n = m := by

  intros n m h1
  have h2 : n = Nat.pred (n + 1) := by rfl
  rewrite [h2, h1]
  rfl

/- LATER: FSR'25 - I wrote an explanation for `have` here,
    though I feel its inclusion here breaks the flow. -/

/- FULL: Rocq's `have` tactic, used above, adds the given hypothesis
    to the context, but it first requires you to prove the hypothesis
    as a new goal.

    This technique for injectivity can be generalized to any constructor
    by writing the equivalent of `pred` -- i.e., writing a function that
    "undoes" one application of the constructor.

    As a convenient alternative, Rocq provides a tactic called
    `injection` that allows us to exploit the injectivity of any
    constructor.  Here is an alternate proof of the above theorem
    using `injection`: -/

/- TERSE: As a convenience, the `injection` tactic allows us to
    exploit injectivity of any constructor (not just `succ`). -/

theorem succ_injective' : forall (n m : Nat),
  n + 1 = m + 1 ->
  n = m := by
  intro n m h
-- FULL
/- By writing `injection h with hmn` at this point, we are asking Lean
   to generate all equations that it can infer from `h` using the
   injectivity of constructors (in the present example, the equation
   `n = m`). This equation is added as a hypothesis (called
   `hmn` in this case) into the context. Because this equation is exactly our goal,
   in this case the `injection` tactic is able to automatically close the goal. -/

-- /FULL
  injection h with hmn

-- TERSE: ***
/- Here's a more interesting example that shows how `injection` can
    derive multiple equations at once. -/
theorem injection_ex1 : forall (n m o : Nat),
  [n, m] = [o, o] ->
  n = m := by
  intro n m o h
  -- WORKINCLASS
  injection h with h1 h2
  injection h2 with h3
  rw [h1, h3]
  -- /WORKINCLASS

/- There is also a related tactic, `injections`, that applies the `injection`
   tactic to all your hypotheses at once, as many times in a row as it can. Using this
   tactic can avoid needing to repeatedly use `injection` on lists, for example. -/
theorem injection_ex2 : forall (n m o : Nat),
  [n, m] = [o, o] ->
  n = m := by
  intro n m o h
  -- WORKINCLASS
  injections h1 _ h3
  rw [h1, h3]
  -- /WORKINCLASS

-- HIDEFROMADVANCED
-- FULL
-- EX3 (injection_ex3)
theorem injection_ex3 : forall (α : Type) (x y z : α) (l j : List α),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y := by

  intro α x y z l j eq1 eq2
  injections hxz hyl_j
  have hyl_zl : y :: l = z :: l := by rw [hyl_j, eq2]
  injections hyz
  rw [hxz, hyz]
-- /ADMITTED
-- GRADE_THEOREM 3: injection_ex3
-- []
-- HIDE

-- EX1 (injection_ex3')
theorem injection_ex3' : forall (α : Type) (x y z w : α) (l j : List α),
  x :: y :: l = w :: z :: j ->
  x :: l = z :: [] ->
  x = y := by
  intro α x y z w l j eq1 eq2
  injections _ _ hyz _ hxz _
  rw [hxz, hyz]
-- /ADMITTED
-- []
-- /HIDE
-- /FULL
-- /HIDEFROMADVANCED


/- So much for injectivity of constructors.  What about disjointness? -/

/- FULL: The principle of disjointness says that two terms beginning
    with different constructors (like `0` and `succ`, or `true` and `false`)
    can never be equal.  This means that, any time we find ourselves
    in a context where we've _assumed_ that two such terms are equal,
    we are justified in concluding anything we want, since the
    assumption is nonsensical. -/

/- TERSE: Two terms beginning with different constructors (like
    `0` and `succ`, or `true` and `false`) can never be equal! -/

-- TERSE: ***

/- The `contradiction` tactic, which we've already seen for handling
   cases where we have assumed `False`, also embodies this principle:
   if we have a a hypothesis involving an equality between different
   constructors (e.g., `false = true`), `contradiction` solves the current
   goal immediately.  Some examples: -/

theorem disjoint_ex1 : forall (n m : Nat),
  false = true ->
  n = m := by
  intro n m contra
  contradiction

theorem disjoint_ex2 : forall (n : Nat),
  n + 1 = 0 ->
  2 + 2 = 5 := by
  intro n contra
  contradiction


/- These examples are instances of a logical principle known as the
    _principle of explosion_, which asserts that a contradictory
    hypothesis entails anything (even manifestly false things!). -/

/-  FULL: If you find the principle of explosion confusing, remember
    that these proofs are _not_ showing that the conclusion of the
    statement holds.  Rather, they are showing that, _if_ the
    nonsensical situation described by the premise did somehow hold,
    _then_ the nonsensical conclusion would too -- because we'd be
    living in an inconsistent universe where every statement is true.

    We'll explore the principle of explosion in more detail in the
    next chapter. -/

-- FULL
/- EX1 (disjoint_ex3) -/
theorem disjoint_ex3 :
  forall (α : Type) (x y z : α) (l : List α),
    x :: y :: l = [] ->
    x = z := by
  -- ADMITTED
  intros X x y z l eq1
  contradiction
-- /ADMITTED
-- GRADE_THEOREM 1: disjoint_ex3
-- []
-- /FULL

-- TERSE: ***

/- For a more useful example, we can use `contradiction` to make a
    connection between the two different notions of equality (`=` and
    `==`) that we have seen for natural numbers. -/
theorem eqb_0_l : forall (n : Nat),
    (0 == n) = true ->
    n = 0 := by
  intro n h
/- FULL: We can proceed by case analysis on `n`. The first case is
    trivial. -/
  cases n
  -- n = 0
  . case zero =>
    rfl

/- FULL: However, the second one doesn't look so simple: assuming
    `(0 == n' + 1) = true`, we must show `n' + 1 = 0`!  The way forward
    is to observe that the assumption itself is nonsensical: -/

  -- n = n' + 1
  . case succ n' =>
/- FULL: If we use `contradiction` here, Lean confirms
    that the subgoal we are working on is impossible and removes it
    from further consideration. -/
    contradiction


/- HIDE: APT: Could add an advanced exercise asking them to show
   somthing like [true = false -> 0 = 1] using [rewrite] and a
   function definition and using [discriminate].  BCP: This might be
   nice, but not sure this is a critical point to make. -/
/- HIDE: "There should be more discussion and practice with how to
   deal with subexpressions that do not allow application of
   hypotheses, for example how to deal with the [S m] in [m + (S m)].
   Again, I sort of understand what to do with [destruct] and
   induction, but it would help to have more exercises that break down
   the process of making this connection."  BCP 9/18: Not sure exactly
   what to add, but if anybody has good ideas... -/

-- TERSE
/- HIDE: This relies on the fact that [injection] only works with
   constructors. Should this be discussed earlier? Or is this the
   right place to mention it briefly?  BCP 20: I think here is OK,
   though a longer explanation (including a remark on why you would
   not want this in general!) would be welcome... -/
/- HIDE: Robert Rand: I think it's nice to start them off with a
   easy question and also to use more datatypes than nat and bool. -/

-- QUIZ
/- Recall our rgb and color types:

inductive RGB : Type where
  | red | green | blue
inductive Color : Type where |
  black | white | primary (p: RGB)

Suppose Lean's proof state looks like
    x : RGB
    y : RGB
    h : .primary x = .primary y

    ⊢ y = x
    and we apply the tactic `injection h with hxy`.  What will happen?

    (1) "No goals."

    (2) The tactic fails.

    (3) Hypothesis `h` becomes `hxy : x = y`.

    (4) None of the above.
-/

-- HIDE
theorem quiz0 : forall (x y : RGB),
  Color.primary x = Color.primary y ->
  x = y := by
  intro x y h
  injection h
-- /HIDE
-- /QUIZ

-- QUIZ
/- Suppose Lean's proof state looks like
      x : bool
      y : bool
      h : !x = !y

      ⊢ y = x
    and we apply the tactic `injection h with hxy`  What will happen?

    (A) "No more goals."

    (B) The tactic fails.

    (C) Hypothesis `h` becomes `hxy : x = y`.

    (D) None of the above.
-/
-- HIDE
/-- error: Tactic `injection` failed: equality of constructor applications expected

x y : Bool
h : (!decide (x = !y)) = true
⊢ y = x -/
#guard_msgs in
theorem quiz1 : forall x y : Bool, !x = !y -> y = x := by
  intro x y h
  injection h with hxy
-- /HIDE
-- /QUIZ

-- QUIZ
/- Now suppose Lean's proof state looks like

        x : Nat
        y : Nat
        h : x + 1 = y + 1

        ⊢ y = x

    and we apply the tactic `injection h with hxy`.  What will happen?

    (A) "No more goals."

    (B) The tactic fails.

    (C) Hypothesis `h` becomes `hxy : x = y`.

    (D) None of the above.
-/
-- HIDE
theorem quiz2 : forall x y : Nat, x + 1 = y + 1 -> y = x := by
  intro x y h
  injection h with hxy
  symm
  assumption
-- /HIDE
-- /QUIZ

-- QUIZ
/- Finally, suppose Lean's proof state looks like

         x : Nat
         y : Nat
         h : 1 + x = 1 + y

         ⊢ y = x

    and we apply the tactic `injection h with hxy`.  What will happen?

    (A) "No more goals."

    (B) The tactic fails.

    (C) Hypothesis `h` becomes `hxy : x = y`.

    (D) None of the above.
-/
-- HIDE
/-- error: Tactic `injection` failed: equality of constructor applications expected

x y : Nat
h : 1 + x = 1 + y
⊢ y = x -/
#guard_msgs in
theorem quiz3 : forall x y : Nat, 1 + x = 1 + y -> y = x := by
  intro x y h
  injection h with hxy
-- /HIDE
-- /QUIZ
-- /TERSE

/- HIDE: BCP 9/16: Not sure this theorem is pulling its weight in SF!
   It's used relatively few places, and there is nothing too
   interesting to say about it here -- indeed it kind of disrupts the
   flow.  BCP 9/18: I actually found it useful several times in the
   lecture on this chapter, so I think it's best to leave it. -/
-- TERSE: ***
/- The injectivity of constructors allows us to reason that
   `forall (n m : Nat), n + 1 = m + 1 -> n = m`.  The converse of this
    implication is an instance of a more general fact about both
    constructors and functions, which we will find useful below: -/

theorem function_congruence : forall (α β : Type) (f: α -> β) (x y: α),
  x = y -> f x = f y := by
  intro α β f x y eq
  rw [eq]

theorem eq_implies_succ_equal : forall (n m : Nat),
  n = m -> n + 1 = m + 1 := by
  intro n m eq
  rw [eq]

-- TODO: (DHS) can someone double check me on this? I think `congr` works this way
-- but I want to be sure
/- FULL: Indeed, there is also a tactic named `congr` that can
    prove such theorems directly.  Given a goal of the form
    `f a1 ... an = g b1 ... bn`, the tactic `congr` will produce subgoals
    of the form `f = g`, `a1 = b1`, ..., `an = bn`. At the same time,
    any of these subgoals that are simple enough (e.g., immediately
    provable by `rfl`) will be automatically discharged. -/

-- TERSE: Rocq also provides `congr` as a tactic.

theorem eq_implies_succ_equal' : forall (n m : Nat),
  n = m -> n + 1 = m + 1 := by

  intro n m eq
  congr

/- TODO: (DHS) We need to explain the numerical argument to `congr`.
   `congr 1` works in this proof but `congr` does not -/
theorem eq_implies_proj_equal : forall (a b c d : Nat),
  a = b -> c = d -> (a, c + 1) = (b, 1 + d) := by
  intro a b c d eq1 eq2
  -- congr here would not work! would generate false goals
  congr 1
  rw [add_comm]
  congr

-- ######################################################
-- * Using Tactics on Hypotheses *

/- FULL: By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic "[simpl in H]" performs simplification on
    the hypothesis [H] in the context. -/
/- TERSE: Many tactics come with "[... in ...]" variants that work on
    hypotheses instead of goals. -/
