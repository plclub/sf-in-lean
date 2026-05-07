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

import LF.Poly
import LF.CustomTactics

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
    `rw`.  What are the situations where both can usefully be
    applied? -/

-- SOLUTION
/- The `rw` tactic is used to apply a known equality (a
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

theorem trans_eq : forall {α : Type} (x y z : α),
    x = y -> y = z -> x = z := by
  intro α x y z eq1 eq2
  rw [eq1, eq2]

/- Now, we should be able to use [trans_eq] to prove the above
    example.  -/

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
    `z` with `[e,f]`. However, the matching process doesn't determine
    an instantiation for `y`, nor does it know which hypothese to use
    for the premises to `trans_eq`. As we saw earlier, `apply` would generate
    new goals for these premises, and we could finish the proof
    by explicitly applying these hypotheses to those new goals. But,
    we can also be more direct by supplying those hypotheses directly to
    `apply`. -/
-- /FULL
-- TERSE

/- Doing [apply trans_eq] doesn't finish the proof!  But... -/
-- /TERSE
  apply trans_eq [a, b] [c, d] [e, f] eq1 eq2
-- TERSE
-- ...does.

-- /TERSE

/- TODO: (DHS) This and below are new (my addition), thoughts? -/
/- In the previous example, we had to specify the `x` and `z` arguments
   to `trans_eq` before we could supply `[c, d]` for `y` or `eq1` and `eq2` for
   the premises. However, we just said that Lean was able to infer these arguments, so it's
   a bit redundant (and wordy) for us to do that. Thankfully,
   Lean allows us to use `_`s for positional arguments that it is able to infer. -/
theorem trans_eq_example'' : forall (a b c d e f : Nat),
    [a, b] = [c, d] ->
    [c, d] = [e, f] ->
    [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  apply trans_eq _ _ _ eq1 eq2

/- As an aside: if we know the name of
   the argument we are supplying (in this case `y`), we can
   just name it directly, and avoid typing any `_`s. -/
theorem trans_eq_example''' : forall (a b c d e f : Nat),
    [a, b] = [c, d] ->
    [c, d] = [e, f] ->
    [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  apply trans_eq (y := [c, d])
  apply eq1
  apply eq2

/-
  FULL: Like any other kind of software, there are conventions and best practices associated
  with writing proofs in Lean. One of these conventions concerns the use of the `exact`
  tactic. When fully applying another theorem like in the previous examples,
  it is considered good practice to use the `exact` tactic instead of `apply`. This signals to
  a reader of the proof that the proof is "exactly" an instance of another lemma, and that nothing
  of particular interest is happening here. This achieves a similar goal as when
  a mathematician says that one result is "just" an instance of another.
-/
/- TERSE: By convention, we use `exact` for situations when we can completely finish the proof
          with a single application  -/
theorem trans_eq_example_exact : forall (a b c d e f : Nat),
    [a, b] = [c, d] ->
    [c, d] = [e, f] ->
    [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  exact trans_eq _ _ _ eq1 eq2

/- TODO: (DHS) if we decide we want to introduce `calc` earlier, we can
   remove this explanation or tweak it. -/
/- FULL: Lean also has a built-in tactic `calc` that
    accomplishes the same purpose as applying `trans_eq`.
    The tactic allows us to specify the in-between states
    of any transitive relation. The notation is reminiscent of
    the proofs you might see in a mathematics textbook.
    -/
/- TERSE: `calc` is also available as a tactic. -/
theorem trans_eq_example'''' : forall (a b c d e f : Nat),
    [a, b] = [c, d] ->
    [c, d] = [e, f] ->
    [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  calc
  [a, b] = [c, d] := by rw [eq1]
  [c, d] = [e, f] := by rw [eq2]

-- FULL
-- EX3? (trans_eq_exercise)
theorem trans_eq_exercise : forall (n m o p : Nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o) := by
  -- ADMITTED
  intro n m o p eq1 eq2
  calc
  _ = m := by rw [eq2]
  _ = minustwo o := by rw [eq1]
-- /ADMITTED
-- []
-- /FULL

-- ######################################################
-- # The `injection` and `contradiction` Tactics

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

/- FULL: Lean's `have` tactic, used above, adds the given hypothesis
    to the context, but it first requires you to prove the hypothesis
    as a new goal.

    This technique for injectivity can be generalized to any constructor
    by writing the equivalent of `pred` -- i.e., writing a function that
    "undoes" one application of the constructor.

    As a convenient alternative, Lean provides a tactic called
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
theorem beq_0_l : forall (n : Nat),
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
   hypotheses, for example how to deal with the `.succ m` in `m + (.succ m)`.
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
   easy question and also to use more datatypes than Nat and Bool. -/

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
      x : Bool
      y : Bool
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

-- TERSE: Lean also provides `congr` as a tactic.

theorem eq_implies_succ_equal' : forall (n m : Nat),
  n = m -> n + 1 = m + 1 := by

  intro n m eq
  congr

/- TODO: (DHS) how is this explanation of `congr`.

   FULL: The `congr` tactic also accepts a numerical argument,
   which tells Lean how deeply to decompose the goal.
   So, given a goal like `((a, b), (c, d)) = ((e, f), (g, h))`,
   `congr 1` only applies `congr` once to the goal, and would produce
   two subgoals: `(a, b) = (e, f)` and `(c, d) = (g, h)`.
   `congr 2`, meanwhile, would apply `congr` again to
   both these subgoals, and produce four subgoals: `a = e`, `b = f`,
   `c = g` and `d = h`. Using `congr` without an argument always
   decomposes the goal as deeply as possible.

   Why does Lean provide this level of flexibility? Depending
   on what we are trying to prove, deeper applications
   of `congr` may make our goal unprovable. Consider
   this example:
-/

/- TERSE: We can specify the recursion-depth with `congr n`. -/

/-- warning: declaration uses `sorry` -/
#guard_msgs(warning) in
example : forall (a b c d : Nat),
  a = b -> c = d -> (a, c + 1) = (b, 1 + d) := by
  intro a b c d eq1 eq2
  congr
  /- We now have three goals: `c = 1`, `1 = d`, and `1 = d`,
     but these are not provable from our hypotheses! `congr`
     has gone too deep. -/
  sorry
  sorry
  sorry

theorem eq_implies_succ_proj_equal : forall (a b c d : Nat),
  a = b -> c = d -> (a, c + 1) = (b, 1 + d) := by
  intro a b c d eq1 eq2
  /- Only shallowly using `congr` here allows us to complete the proof -/
  congr 1
  rw [add_comm]
  congr

-- ######################################################
-- * Using Tactics on Hypotheses *

/- FULL: By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic "`dsimp at H`" performs simplification on
    the hypothesis `H` in the context. -/
/- TERSE: Many tactics come with "`... at ...`" variants that work on
    hypotheses instead of goals. -/

theorem succ_inj : ∀ (n m : Nat) ,
  Nat.succ n == Nat.succ m -> n == m := by
  intro n m h
  dsimp [beq] at h
  exact h

/-  FULL: Similarly, `apply L at H` matches some conditional statement
    `L` (of the form `X -> Y`, say) against a hypothesis `H` in the
    context.  However, unlike ordinary `apply` (which rewrites a goal
    matching `Y` into a subgoal `X`), `apply L at H` matches `H`
    against `X` and, if successful, replaces it with `Y`.

    In other words, `apply L at H` gives us a form of "forward
    reasoning": given `X -> Y` and a hypothesis matching `X`, it
    produces a hypothesis matching `Y`.

    By contrast, `apply L` is "backward reasoning": it says that if we
    know `X -> Y` and we are trying to prove `Y`, it suffices to prove
    `X`.

    Here is a variant of a proof that uses forward reasoning
    throughout instead of backward reasoning. -/

/- TERSE: *** -/
/- TERSE: The ordinary `apply` tactic is a form of "backward
    reasoning."  It says "We're trying to prove `X` and we know
    `Y -> X`, so if we can prove `Y` we'll be done."

    By contrast, the variant `apply... at...` is "forward reasoning":
    it says "We know `Y` and we know `Y -> X`, so we also know `X`." -/

/- HIDE: Robert Rand: I find the behavior of `apply in` to be hideous.
   If I have H1 : A and H2: A -> B, I don't want to change H1 to B
   (leaving me with an entirely redundant H2), I want to change H2 to
   B, leaving me with H1 : A, H2 : B. I tend to point this out and
   show that `specialize (EQ H)` gives us what we want. This makes for
   a nice segue to the next section. -/

-- /HIDEFROMADVANCED

theorem silly4 : ∀ (n m p q : Nat),
  (n = m → p = q) →
  n = m →
  p = q := by
  intro n m p q eq1 eq2
  apply eq1 at eq2
  exact eq2

-- /HIDEFROMADVANCED

/- FULL: Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_ and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.

    The informal proofs seen in math or computer science classes tend
    to use forward reasoning.  By contrast, idiomatic use of Lean
    generally favors backward reasoning, though in some situations the
    forward style can be easier to think about.

    You may be interested to know that the `apply ... at ...` tactic
    is not part of Lean's base set of tactics. However, Lean makes it
    very easy for users to define new tactics that suit their
    particular proof style, and so the developers of the popular
    Mathlib library defined the `apply ... at ...` tactic to
    better enable forward reasoning. Mathlib is a very large development,
    so we won't import the whole thing here, but we have
    provided you `apply ... at ...` because it is quite useful.
-/

/- TODO: (DHS) this part has been changed
   from the original Rocq, let me know what you think -/
-- ######################################################
-- Specializing Hypotheses

/- We've already seen how we can use `have` to do
   forward reasoning, by letting us state and prove useful facts
   that get us closer to the main goal we're trying to prove. Often,
   though, these facts are just special cases of more general hypotheses
   we already have.

   If `h` is a quantified hypothesis in the current context -- i.e.,
   `h : forall (x : α), P` -- then `have h := h (x := e)` will
   change `h` so that it looks like `P` with `x` replaced by `e`.

   For example: -/

theorem have_example: forall m,
  (forall n, m * n = 0)
  -> m = 0 := by
/- HIDE: Robert Rand: I found this very useful because not all
   students realize I can get a specific case from the forall in the
   hypotheses. I've shortened the proof a bit. -/
  intro m h
  have h := h (n := 1)
  rw [mul_one] at h
  exact h

/- You may notice that in the above proof, after using `have`
   we were left with a leftover hypothesis in the context,
   the old `h`, so to speak. Often we don't care to keep
   this old hypothesis around, and so we can use the `replace`
   tactic instead. It behaves the same as `have`, except
   it gets rid of the old hypothesis afterwards: -/
theorem replace_example: forall m,
  (forall n, m * n = 0)
  -> m = 0 := by
  intro m h
  replace h := h (n := 1)
  rw [mul_one] at h
  exact h

-- FULL
-- EX3 (nth_error_always_none)

/- Use `have` or `replace` to prove the the following lemma, following the
    model of the examples above. Do not use `induction`. -/
theorem nth_error_always_none: forall (l : List Nat),
  (forall i, nthError l i = none) ->
  l = [] := by
-- ADMITTED
  intro l h
  cases l
  case nil => rfl
  case cons hd tl =>
    have h := h (i := 0)
    dsimp [nthError] at h
    contradiction
-- /ADMITTED
-- []
-- /FULL

/- Tactics like `have` and `replace` can also be used with lemmas and
   theorems we've already proven, not just things in our context.
   Using these tactis before `apply` gives us yet another way to
   control where `apply` does its work. -/
theorem trans_eq_example''''' : forall (a b c d e f : Nat),
     [a, b] = [c, d] ->
     [c, d] = [e, f] ->
     [a, b] = [e, f] := by
  intros a b c d e f eq1 eq2
  have h := trans_eq (y:= [c, d])
  apply h
  /- This tactic closes a goal if it appears anywhere in the context.
     In this case we could also write `exact eq1` ... -/
  assumption
  /- .. and here we could also write `exact eq2` -/
  assumption

-- ######################################################
/- Varying the Induction Hypothesis -/

-- TERSE
/- Recall this function for doubling a natural number from the
    \CHAP{Arithmetic} chapter:

    def double (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | .succ n' => (double n') + 2
-/
-- /TERSE

/- FULL: Sometimes it is important to control the exact form of the
    induction hypothesis when carrying out inductive proofs in Lean.
    In particular, we may need to be careful about which of the
    assumptions we move (using `intro`) from the goal to the context
    before invoking the `induction` tactic.

    For example, suppose we want to show that `double` is injective --
    i.e., that it maps different arguments to different results:
[[
       theorem double_injective: forall n m,
         double n = double m ->
         n = m
]]
    The way we start this proof is a bit delicate: if we begin it with
[[
       intro n; induction n
]]
    then all will be well.  But if we begin it with introducing _both_
    variables
[[
       intros n m; induction n
]]
    we get stuck in the middle of the inductive case... -/
-- TERSE: ***
/- TERSE: Suppose we want to show that `double` is injective (i.e.,
    it maps different arguments to different results).  The way we
    _start_ this proof is a little bit delicate: -/

/-- warning: declaration uses `sorry` -/
#guard_msgs(warning) in
example : forall n m,
  double n = double m ->
  n = m := by

  intro n m
  induction n
  -- n = 0
  . case zero =>
    dsimp [double]
    intro eq
    cases m
    -- m = 0
    . case zero => rfl
    -- m = succ m'
    . case succ _ => contradiction
  -- n = succ n'
  . case succ n' ih =>
    intro eq
    cases m
    --  m = O
    . case zero => contradiction
    -- m = succ m' =>
    . case succ m' =>
      congr
      /- At this point, the induction hypothesis `ih` does _not_ give us
      `n' = m'` -- there is an extra `succ` in the way -- so the goal is
      not provable. -/
      sorry

-- TERSE: ***
-- HIDEFROMADVANCED

-- What went wrong?

/-  FULL: The problem is that, at the point where we invoke the
    induction hypothesis, we have already introduced `m` into the
    context -- intuitively, we have told Lean, "Let's consider some
    particular `n` and `m`..." and we now have to prove that, if
    `double n = double m` for _these particular_ `n` and `m`, then
    `n = m`.

    The next tactic, `induction n` says to Lean: We are going to show
    the goal by induction on `n`.  That is, we are going to prove, for
    _all_ `n`, that the proposition

      - `P n` = "if `double n = double m`, then `n = m`"

    holds, by showing

      - `P 0`

         (i.e., "if `double 0 = double m` then `0 = m`") and

      - `P n -> P (.succ n)`

        (i.e., "if `double n = double m` then `n = m`" implies "if
        `double (.succ n) = double m` then `.succ n = m`").

    If we look closely at the second statement, it is saying something
    rather strange: that, for a _particular_ [m], if we know

      - "if `double n = double m` then `n = m`"

    then we can prove

       - "if `double (.succ n) = double m` then `.succ n = m`".

    To see why this is strange, let's think of a particular `m` --
    say, `5`.  The statement is then saying that, if we know

      - `Q` = "if `double n = 10` then `n = 5`"

    then we can prove

      - `R` = "if `double (.succ n) = 10` then `.succ n = 5`".

    But knowing `Q` doesn't give us any help at all with proving `R`!
    If we tried to prove `R` from `Q`, we would start with something
    like "Suppose `double (.succ n) = 10`..." but then we'd be stuck:
    knowing that `double (.succ n)` is `10` tells us nothing helpful about
    whether `double n` is `10` (indeed, it strongly suggests that
    `double n` is _not_ `10`!!), so `Q` is useless. -/

/- Trying to carry out this proof by induction on `n` when `m` is
    already in the context doesn't work because we are then trying to
    prove a statement involving _every_ `n` but just a _particular_
    `m`. -/
-- /HIDEFROMADVANCED

-- TERSE: ***
/- A successful proof of `double_injective` keeps `m` universally
    quantified in the goal statement at the point where the
    `induction` tactic is invoked on `n`.  -/

theorem double_injective : forall (n m : Nat),
  double n = double m ->
  n = m := by
  intro n
  induction n
  . case zero =>
    dsimp [double]
    intro m eq
    cases m
    -- m = 0
    . case zero => rfl
    -- m = .succ m'
    . case succ _ => contradiction
-- FULL
  . case succ n' ih =>
/- Notice that both the goal and the induction hypothesis are
    different this time: the goal asks us to prove something more
    general (i.e., we must prove the statement for _every_ `m`), but
    the induction hypothesis `ih` is correspondingly more flexible,
    allowing us to choose any `m` we like when we apply it. -/

-- /FULL
  intro m eq
-- FULL

/- Now we've introduced the assumption that `double n = double m`.
   Since we are doing a case analysis on `n`,
   we also need a case analysis on `m` to keep the two in sync. -/

-- /FULL
  cases m
  -- m = 0
  . case zero =>
-- FULL

-- The 0 case is trivial:

-- /FULL
    contradiction
  . case succ m' =>
  -- m = .succ m'
    congr
-- FULL

/- Since we are now in the second branch of the `cases m`, the
    `m'` mentioned in the context is the predecessor of the `m` we
    started out talking about.  Since we are also in the `succ` branch of
    the induction, this is perfect: if we instantiate the generic `m`
    in the IH with the current `m'` (this instantiation is performed
    automatically by the `apply` in the next step), then `ih` gives
    us exactly what we need to finish the proof. -/

    apply ih; dsimp [double] at eq; injections
-- /FULL *)

/- HIDE: Robert Rand: I found jumping straight to "what if we want to
   do induction on the second argument" via double_injective_take2_FAILED
   to be much more natural here. -/

-- HIDEFROMADVANCED
-- TERSE: ***
/-  The thing to take away from all this is that you need to be
    careful, when using induction, that you are not trying to prove
    something too specific: When proving a property quantified over
    variables [n] and [m] by induction on [n], it is sometimes crucial
    to leave [m] "generic." -/


-- /HIDEFROMADVANCED
/- FULL: The following exercise, which further strengthens the link between
    `==` and `=`, follows the same pattern. -/
/- TERSE: The following theorem, which further strengthens the link between
    `==` and `=`, follows the same pattern. -/
-- FULL
-- EX2 (beq_eq)
-- /FULL
theorem beq_eq : forall (n m : Nat),
  (n == m) = true -> n = m := by
  -- FULL
  -- ADMITTED
  -- /FULL
  -- TERSE
  -- WORKINCLASS
  -- /TERSE
  intro n
  induction n
  . case zero =>
    intro m eq; cases m
    . case zero => rfl
    . case succ m' =>
      contradiction
  . case succ n' ih =>
    intro m eq; cases m
    . case zero => contradiction
    . case succ m' =>
      congr
      apply ih
      rw [beq_succ] at eq
      assumption
-- TERSE
  -- /WORKINCLASS
-- /TERSE
-- FULL
-- /ADMITTED
-- GRADE_THEOREM 2: beq_eq
-- []


-- EX2AM? (beq_eq_informal)
/- Give a careful informal proof of `beq_eq`, stating the induction
    hypothesis explicitly and being as explicit as possible about
    quantifiers, everywhere. -/

-- SOLUTION
/- _Theorem_: For all natural numbers `n` and `m`, if [n == m =
      true], then `n = m`.

    _Proof_ (more pedantic, arguably less clear): We argue by
    induction on `n`.

      - Base case: `n = 0`.  We must show, for all natural numbers
        `m`, that `0 == m = true` implies `0 = m`.  We proceed by
        cases on `m`.

          - If `m = 0`, we must show that `0 == 0 = true` implies [0 =
            0], which holds by reflexivity.

          - If `m = .succ m'` for some `m'`, we must show that [0 == .succ m'
            = true] implies `0 = .succ m'`.  But `0 == .succ m'` evaluates to
            `false`, so the antecedent of this implication is [false =
            true], which is absurd, and hence the whole implication is
            true.

      - Inductive case: `n = .succ n'`. We must show that for all natural
        numbers `m`, `.succ n' == m = true` implies `.succ n' = m`.

        We may assume the induction hypothesis: for all natural
        numbers `m`, `n' == m = true`, implies `n' = m`.

        We again proceed by cases on `m`.

          - If `m = 0`, we must show that `.succ n' == 0 = true` implies
            `.succ n' = m`. But `.succ n' == 0` evaluates to `false`, so the
            antecedent of this implies is again absurd, and hence the
            whole implication is true.

          - If `m = .succ m'` for some `m'`, we must show that [.succ n' == .succ
            m' = true] implies `.succ n' = .succ m'`.  So let us assume the [.succ
            n' == .succ m' = true].  This simplifies to [n' == m' =
            true]. Hence we can apply the induction hypothesis (with
            `m` instantiated to `m'`) to obtain `n' = m'`.  Hence, to
            show `.succ n' = .succ m'` it suffices to show `.succ n' = .succ n'`,
            which is true by reflexivity. []

    _Alternate proof_ (in a more natural style):
    By induction on `n`.

      - Suppose `n = 0`.  We must show that if `0 == m = true` then [0
        = m]. Now if `m` were of the form `.succ m'` for some `m'`, then
        we would have `0 == .succ m' = true`, which is absurd. So `m` must
        indeed be 0.

      - Otherwise, we have `n = .succ n'`. The induction hypothesis states
        that for all m, if `n' == m = true`, then `n' = m`; and on the
        assumption `.succ n' == m = true`, we must show that `.succ n' = m`.
        In this case `m` must have the form `.succ m'` for some `m'`, for
        if `m` were 0, our assumption would be `.succ n' == 0 = true`,
        which is absurd.  So our assumption has the form [.succ n' == .succ m'
        = true], which simplifies to `n' == m' = true`. Applying the
        induction hypothesis to the assumption (with `m` instantiated
        to `m'`) gives us that `n' = m'`, which directly implies our
        goal `.succ n' = .succ m'`. [] -/
-- /SOLUTION

-- GRADE_MANUAL 2: informal_proof
-- []

-- HIDEFROMADVANCED
-- EX3! (plus_n_n_injective)
-- TERSE: ***
/- In addition to being careful about how you use `intro`, practice
    using "at" variants in this proof.  (Hint: use `plus_n_Sm`.) -/
theorem plus_n_n_injective : forall (n m : Nat),
  n + n = m + m ->
  n = m := by
  -- ADMITTED
  intro n
  induction n
  . case zero =>
    intro m eq; cases m
    . case zero => rfl
    . case succ => dsimp at eq; contradiction
  . case succ n' ih =>
    intro m eq; cases m
    . case zero => dsimp at eq; contradiction
    . case succ m' =>
      rw [add_succ, add_succ (m' + 1)] at eq
      injection eq with eq
      rw [add_comm, add_comm (m' + 1)] at eq
      injections eq; congr; exact ih _ eq
-- /ADMITTED
-- GRADE_THEOREM 3: plus_n_n_injective
-- []
-- /HIDEFROMADVANCED
-- /FULL

-- TERSE: ***
/- The strategy of doing fewer `intros` before an `induction` to
    obtain a more general IH doesn't always work; sometimes some
    _rearrangement_ of quantified variables is needed.  Suppose, for
    example, that we wanted to prove `double_injective` by induction
    on `m` instead of `n`. -/
/-- warning: declaration uses `sorry` -/
#guard_msgs(warning) in
theorem double_injective_take2_FAILED : forall n m,
  double n = double m ->
  n = m := by
  intro n m
  induction m
  -- m = O
  . intro eq; cases n
    -- n = O
    . rfl
    -- n = .succ n'
    . contradiction
  -- m = .succ m'
  . intro eq; cases n
    -- n = 0
    . contradiction
    -- n = .succ n'
    . congr
    -- We are stuck here, just like before.
      sorry

-- TERSE: ***
/- The problem is that, to do induction on `m`, we must first
    introduce `n`. -/

-- HIDEFROMADVANCED
/- FULL: What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that `m` is quantified before `n`.  This
    works, but it's not nice: We don't want to have to twist the
    statements of lemmas to fit the needs of a particular strategy for
    proving them!  Rather we want to state them in the clearest and
    most natural way. -/

-- /HIDEFROMADVANCED
-- TERSE:
/- What we can do instead is to first introduce all the quantified
    variables and then explicitly generalize one or more of them
    The `generalizing` option for the `induction` tactic does this. -/

theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m := by
  intro n m eq
  -- `n` and `m` are both in the context
  -- This lets us do induction on `m` and get a sufficiently general IH
  induction m generalizing n
  . case zero =>
    cases n
    . rfl
    . contradiction
  . case succ _ ih =>
    cases n
    . contradiction
    . congr; injections _ eq; exact ih _ eq

/- LATER: Somewhere (in this file? in Poly?), we might want to include
   a more careful discussion of the way generalized IHs are handled in
   informal proofs.  Basically, the practice seems to be to assume
   we're working with a "general enough" IH, but seldom to bother
   saying exactly what it is! -/

/- FULL: Let's look at an informal proof of this theorem.  Note that
    the proposition we prove by induction leaves `n` quantified,
    corresponding to the use of generalize dependent in our formal
    proof.

    _Theorem_: For any nats `n` and `m`, if `double n = double m`, then
      `n = m`.

    _Proof_: Let `m` be a `Nat`. We prove by induction on `m` that, for
      any `n`, if `double n = double m` then `n = m`.

      - First, suppose `m = 0`, and suppose `n` is a number such
        that `double n = double m`.  We must show that `n = 0`.

        Since `m = 0`, by the definition of `double` we have [double n =
        0].  There are two cases to consider for `n`.  If `n = 0` we are
        done, since `m = 0 = n`, as required.  Otherwise, if `n = .succ n'`
        for some `n'`, we derive a contradiction: by the definition of
        `double`, we can calculate `double n = .succ (.succ (double n'))`, but
        this contradicts the assumption that `double n = 0`.

      - Second, suppose `m = .succ m'` and that `n` is again a number such
        that `double n = double m`.  We must show that `n = .succ m'`, with
        the induction hypothesis that for every number `s`, if [double s =
        double m'] then `s = m'`.

        By the fact that `m = .succ m'` and the definition of `double`, we
        have `double n = .succ (.succ (double m'))`.  There are two cases to
        consider for `n`.

        If `n = 0`, then by definition `double n = 0`, a contradiction.

        Thus, we may assume that `n = .succ n'` for some `n'`, and again by
        the definition of `double` we have
        `.succ (.succ (double n')) = .succ (.succ (double m'))`,
        which implies by injectivity that `double n' = double m'`.
        Instantiating the induction hypothesis with `n'` thus
        allows us to conclude that `n' = m'`, and it follows immediately
        that `.succ n' = .succ m'`.  Since `.succ n' = n` and `.succ m' = m`, this is just
        what we wanted to show. [] -/

/- LATER: Maybe we should put one more good example to round out this section? -/

-- ######################################################
-- Rewriting with conditional statements

/- Suppose that we want to show that `add` is the inverse of
    `sub`.  Since we are working with natural numbers, we need an
    assumption to prevent `sub` from truncating its result. With
    this assumption, the induction hypothesis becomes
    `forall m, n' <== m = true -> (m - n') + n' = m`.  The beginning of the proof
    uses techniques we have already seen -- in particular, notice how
    we induct on `n` before introducing `m`, so that the induction
    hypothesis becomes sufficiently general. -/

theorem sub_add_leb : forall n m, n ≤? m = true -> (m - n) + n = m := by
  intro n
  induction n
  . case zero =>
    intro m h; rw [add_zero]; cases m
    . case zero => rfl
    . case succ => rfl
  . case succ n' ih =>
    intro m h; cases m
    . case zero => contradiction
    . case succ m' =>
      dsimp [leb] at h
      rw [succ_sub_succ, add_succ]
/- FULL: At this point, we need to show `(m' - n') + n' + 1 = m' + 1` from
    the assumption `(n' <= m') = true`.  We could use the `assert`
    tactic to prove `(m' - n') + n' = m'` from the induction
    hypothesis. However, we can also just use `rw` directly: if
    we rewrite with a conditional statement of the form `P -> a = b`,
    then Lean tries to rewrite with `a = b`, and then asks us to prove
    `P` in a new subgoal.  If the statement has more than one
    assumption, then we get one subgoal for each assumption. -/
/- TERSE: We could use the `have` tactic to prove `(m' - n') + n' = m'`
    from the IH. However, we can also just use `rw` directly... -/
      rw [ih]
      assumption

-- FULL
-- EX3! (gen_dep_practice)
-- Prove this by induction on `l`.

theorem nth_error_after_last: forall (n : Nat) (α : Type) (l : List α),
  l.length = n ->
  nthError l n = none := by
-- ADMITTED
  intros n α l hlen
  induction l generalizing n
  case nil => rfl
  case cons hd tl ih =>
    dsimp [nthError]; dsimp [List.length] at hlen
    rw [←hlen]
    dsimp; apply ih _; rfl
-- /ADMITTED
-- GRADE_THEOREM 3: nth_error_after_last
-- []
-- HIDE

/- LATER: BCP 9/16: Hiding the following three exercises, which
   need some fixing or moving elsewhere... -/
-- EX3? (app_length_cons)
/- Prove this by induction on `l1`, without using `app_length`
    from `Lists`. -/

theorem app_length_cons : forall {α : Type} (l1 l2 : List α)
                                 (x : α) (n : Nat),
  (l1 ++ (x :: l2)).length = n ->
  .succ ((l1 ++ l2).length) = n := by
-- ADMITTED
  intro α l1 l2 x n heq
  induction l1 generalizing n
  case nil =>
    assumption
  case cons hd tl ih =>
    dsimp; dsimp [List.length] at heq
    rw [←heq]
    have h : .succ (tl ++ l2).length = (tl ++ x :: l2).length := by apply ih _; rfl
    dsimp at h; rw [h]
-- /ADMITTED
-- []

-- EX4? (app_length_twice)
/- Prove this by induction on `l`, without using `app_length` from `Lists`. -/
/- LATER: This might be a little bit hard??
   There are a couple of tricky little points!
   APT: Yes: the nested induction is a first, I think. And it would
     be good to have seen rewrite with an applied term; otherwise
     a kludgy forward `assert` or `pose proof` seems needed. -/
/- LATER: no need for a _nested_ induction per se -- side lemmas will
   do the trick, too, and students have been exposed to that
   already. -/
/- LATER: APT: Yes, but the lemma above is terribly ad-hoc, as well
   as ill-suited for its use here!
   I realize that the pedagogical point here has nothing to do with
   developing sensible lemmas for lists, but these seem pretty distorted. -/

theorem app_length_twice : forall (α:Type) (n:Nat) (l:List α),
  l.length = n ->
  (l ++ l).length = n + n := by
  -- ADMITTED
  intros X n l heq
  induction l generalizing n
  case nil => dsimp; rw [←heq]; rfl
  case cons hd tl ih =>
    dsimp; dsimp at heq
    have h : .succ (tl ++ tl).length = (tl ++ hd :: tl).length := by
      apply app_length_cons _ _ hd _; rfl
    dsimp at h
    rw [←heq, ←h, ih tl.length, add_assoc]
    congr 1
    rw [←add_assoc, ←add_assoc]
    congr 1
    rw [add_comm]
    rfl
-- /ADMITTED
-- []

-- EX3? (diagonal_induction)
/- LATER: Uses `Prop`, which has not been introduced.  This
   exercise should be moved to another chapter. -/
-- Prove the following principle of induction over two naturals.

theorem diagonal_induction: forall (P : Nat -> Nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (.succ m) 0) ->
  (forall n, P 0 n -> P 0 (.succ n)) ->
  (forall m n, P m n -> P (.succ m) (.succ n)) ->
  forall m n, P m n := by
  intro P H00 HS0 H0S HSS m n
  induction m generalizing n
  case zero =>
    induction n
    case zero => exact H00
    case succ _ ih => exact H0S _ ih
  case succ _ ih =>
    cases n
    . exact HS0 _ (ih _)
    . exact HSS _  _ (ih _ )

-- /ADMITTED
-- []
-- /HIDE
-- /FULL

/- TODO: (DHS) This should all move to Induction.lean, probably, but that
   means we will need to redo the examples here. Keeping the original
   Rocq here for posterity

(* ###################################################### *)
(** * Unfolding Definitions *)

(** It sometimes happens that we need to manually unfold a name that
    has been introduced by a `Definition` so that we can manipulate
    the expression it stands for.

    For example, if we define... *)

Definition square n := n * n.

(** ...and try to prove a simple fact about `square`... *)

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.

(** ...we appear to be stuck: `simpl` doesn't simplify anything, and
    since we haven't proved any other facts about `square`, there is
    nothing we can `apply` or `rewrite` with. *)

(** TERSE: *** *)
(** To make progress, we can manually `unfold` the definition of
    `square`: *)

  unfold square.

(** Now we have plenty to work with: both sides of the equality are
    expressions involving multiplication, and we have lots of facts
    about multiplication at our disposal.  In particular, we know that
    it is commutative and associative, and from these it is not hard
    to finish the proof. *)

  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

(** TERSE: *** *)
(** At this point, a bit deeper discussion of unfolding and
    simplification is in order.

    We already have observed that tactics like `simpl`, `reflexivity`,
    and `apply` will often unfold the definitions of functions
    automatically when this allows them to make progress.  For
    example, if we define `foo m` to be the constant `5`... *)

Definition foo (x: Nat) := 5.

(** .... then the `simpl` in the following proof (or the
    `reflexivity`, if we omit the `simpl`) will unfold `foo m` to
    `(fun x => 5) m` and further simplify this expression to just
    `5`. *)

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(** TERSE: *** *)
(** But this automatic unfolding is somewhat conservative.  For
    example, if we define a slightly more complicated function
    involving a pattern match... *)

Definition bar x :=
  match x with
  | 0 => 5
  | .succ _ => 5
  end.

(** ...then the analogous proof will get stuck: *)

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

(** FULL: The reason that `simpl` doesn't make progress here is that it
    notices that, after tentatively unfolding `bar m`, it is left with
    a match whose scrutinee, `m`, is a variable, so the `match` cannot
    be simplified further.  It is not smart enough to notice that the
    two branches of the `match` are identical, so it gives up on
    unfolding `bar m` and leaves it alone.

    Similarly, tentatively unfolding `bar (m+1)` leaves a `match`
    whose scrutinee is a function application (that cannot itself be
    simplified, even after unfolding the definition of `+`), so
    `simpl` leaves it alone. *)

(** TERSE: *** *)
(** FULL: At this point, there are two ways to make progress.  One is to use
    `destruct m` to break the proof into two cases, each focusing on a
    more concrete choice of `m` (`O` vs `.succ _`).  In each case, the
    `match` inside of `bar` can now make progress, and the proof is
    easy to complete. *)
(** TERSE: There are now two ways make progress.

    First, we can use `destruct m` to break the proof into two cases: *)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** This approach works, but it depends on our recognizing that the
    `match` hidden inside `bar` is what was preventing us from making
    progress. *)

(** TERSE: *** *)
(** A more straightforward way forward is to explicitly tell Rocq to
    unfold `bar`. *)

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.

(** Now it is apparent that we are stuck on the `match` expressions on
    both sides of the `=`, and we can use `destruct` to finish the
    proof without thinking so hard. *)

  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed. -/

-- ######################################################
-- Using `cases` on Compound Expressions

/- HIDE: CH: If eqn is only useful for compound expressions and those
   are only discussed here, why has eqn been introduced before this
   point? It seems that so far its only use was for documentation, and
   while one might argue that it's good practice to always use eqn,
   that's not the case, as illustrated by its disappearance in Logics.
   BCP '19: Fixed Logic.v -- I do think it's good documentation! -/

/- FULL: We have seen many examples where `cases` is used to
    perform case analysis of the value of some variable.  Sometimes we
    need to reason by cases on the result of some _expression_.  We
    can also do this with `cases`.

    Here are some examples: -/
/- TERSE: The `cases` tactic can be used on expressions as well as
    variables: -/

def sillyfun (n : Nat) : Bool :=
  if n == 3 then false
  else if n == 5 then false
  else false

theorem sillyfun_false : forall (n : Nat),
  sillyfun n = false := by
  intro n
  unfold sillyfun
  cases (n == 3)
  case false =>
    dsimp; cases (n == 5)
    case false => rfl
    case true => rfl
  case true => rfl

/- FULL: After unfolding `sillyfun` in the above proof, we find that
    we are stuck on `if (n == 3) then ... else ...`.  But either
    `n` is equal to `3` or it isn't, so we can use [cases (n == 3)] to let us reason about the two cases.

    In general, the `cases` tactic can be used to perform case
    analysis of the results of arbitrary computations.  If `e` is an
    expression whose type is some inductively defined type `T`, then,
    for each constructor `c` of `T`, `cases e` generates a subgoal
    in which all occurrences of `e` (in the goal and in the context)
    are replaced by `c`. -/

-- ######################################################
-- Destructing Tuples

/- `cases` is useful when we are dealing with inductively defined types
   that can be one thing or another; a `Bool` is either a `false` or a `true`,
   and a `Nat` is either `0` or `succ n`. When we want more information about
   inductively defined types that are products of multiple things, we instead
   want a way to get the pieces of that value out from it.

   When we have a value `v : α × β` in our context, we can
   get the first and second projections of `v` using this tactic:
      `let ⟨a, β⟩ := v`
-/

-- FULL
-- EX3 (combine_split) *)
/- Here is an implementation of the `unzip` function mentioned in
   chapter \CHAP{Poly}. We'll call it `split` so as not to
   confuse Lean. -/

def split {α β : Type} (l : List (α × β)) : (List α) × (List β) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)

/- Prove that `split` and `zip` are inverses in the following sense: -/
theorem split_zip : forall α β  (l : List (α × β)) l1 l2,
  split l = (l1, l2) ->
  zip l1 l2 = l := by
-- ADMITTED
  intro α β l l1 l2 h
  induction l generalizing l1 l2
  case nil =>
    injections h1 h2
    rw [←h1, ←h2]
    rfl
  case cons hd tl ih =>
    let ⟨a, b⟩ := hd
    dsimp [split] at h
    injections h1 h2
    rw [←h1, ←h2]
    dsimp [zip]
    rw [ih]
    rfl
-- /ADMITTED
-- []
-- /FULL

-- TERSE:
/- When using `cases`, we can specify to Lean that it should
   remember an equality between a compound expression and what
   we are decomposing it into, using `cases h: ...` syntax.
   This information can actually be critical,
   and, if we leave it out, we might lack information we need to complete a proof. *)
-- FULL: For example, suppose we define a function `sillyfun1` like
    this: -/

def sillyfun1 (n : Nat) : Bool :=
  if n == 3 then true
  else if n == 5 then true
  else false

/- FULL: Now suppose that we want to convince Lean that `sillyfun1 n`
    yields `true` only when `n` is odd.  If we start the proof like
    this (with no `h:` on the `cases`)... -/
/-- warning: declaration uses `sorry` -/
#guard_msgs(warning) in
example : forall (n : Nat),
  sillyfun1 n = true ->
  odd n = true := by
  intro n eq
  unfold sillyfun1 at eq
  cases (n == 3)
  . case false =>
    sorry
  . sorry

/- FULL: ... then we are stuck at this point because the context does
    not contain enough information to prove the goal!
    Because `n == 3` appears in our hypothesis, rather than in our
    goal, `cases (n == 3)` does not automatically replace the expression
    with `false` or `true` like it did during the proof of `sillyfun_false`.
    We want to add an equation to the context that records which case we are in.
    This is precisely what the
    `h:` qualifier does. -/
-- TERSE: ***
-- TERSE: Adding the `h:` qualifier saves this information so we can use it. *)

theorem sillyfun1_odd : forall (n : Nat),
  sillyfun1 n = true ->
  odd n = true := by

  intro n eq
  unfold sillyfun1 at eq
  cases h: (n == 3)
  . case false =>
-- FULL
  /- Now we have the same state as at the point where we got
      stuck above, except that the context contains an extra
      equality assumption, which is exactly what we need to
      make progress. -/
    rw [h] at eq; dsimp at eq
    cases h': (n == 5)
    . case false =>
      rw [h'] at eq; dsimp at eq
      contradiction
    . case true =>
      apply beq_eq at h'
      rw [h']; rfl
-- /FULL
-- FULL
   /- When we come to the second equality test in the body
      of the function we are reasoning about, we can use
      `h:` again in the same way, allowing us to finish the
      proof. -/
-- /FULL
  . case true =>
    apply beq_eq at h
    rw [h]; rfl

-- FULL
-- EX2 (destruct_eqn_practice)
theorem bool_fn_applied_thrice :
  forall (f : Bool -> Bool) (b : Bool),
  f (f (f b)) = f b := by
-- ADMITTED
  intro f b
  cases b
  . case false =>
    cases heqffalse : (f false)
    . case false =>
      rw [heqffalse, heqffalse]
    . case true =>
      cases heqftrue : (f true)
      . case false => assumption
      . case true => assumption
  . case true =>
    cases heqftrue : (f true)
    . case false =>
      cases heqffalse : (f false)
      . case false => assumption
      . case true => assumption
    . case true =>
        rw [heqftrue, heqftrue]
-- /ADMITTED
-- GRADE_THEOREM 2: bool_fn_applied_thrice
-- []

-- ##################################################################
-- * Review

/- LATER: NDS'25 This list is getting pretty long; maybe it should be
   further divided into catgories (I'd suggest: Basic hypotheses/goal
   manipulation, equality, indutive types, others) -/

/- We've now talked about many of Lean's most fundamental tactics.
    We'll introduce a few more in the coming chapters, and later on
    we'll see some more powerful _automation_ tactics that make Lean
    help us with low-level details.  But basically we've got what we
    need to get work done.

    Here are the ones we've seen:

      - `intro`: move hypotheses/variables from goal to context

      - `rfl`: finish the proof (when the goal looks like [e =
        e])

      - `apply`: prove goal using a hypothesis, lemma, or constructor

      - `apply... at H`: apply a hypothesis, lemma, or constructor to
        a hypothesis in the context (forward reasoning)

      - `apply... with...`: explicitly specify values for variables
        that cannot be determined by pattern matching

      - `replace h (x:= ...)`: refine a hypothesis by fixing some of
        its variables

      - `dsimp`: simplify computations in the goal

      - `dsimp at H`: ... or a hypothesis

      - `rw`: use an equality hypothesis (or lemma) to rewrite the goal

      - `rw ... at H`: ... or a hypothesis

      - `symm`: changes a goal of the form `t=u` into `u=t`

      - `symm at H`: changes a hypothesis of the form `t=u` into
        `u=t`

      - `calc`: prove a goal about a transitive relation via a number of intermediate steps

      - `unfold`: replace a defined constant by its right-hand side in
        the goal

      - `unfold... at H`: ... or a hypothesis

      - `cases ...`: case analysis on values of inductively defined types

      - `cases h:...`: specify the name of an equation to be
        added to the context, recording the result of the case
        analysis

      - `induction ...`: induction on values of inductively
        defined types

      - `induction ... generalizing ...`: hold some variables general while doing induction

      - `injection ... with ...`: reason by injectivity on an equality between values of inductively defined types

      - `injections ... `: reason by injectivity on all the equalities in the context

      - `contradiction`: conclude a proof when there's a false hypothesis in the context

      - `have h : e := ... ` : introduce a "local lemma" `e` and call it `h`

      - `congr`: change a goal of the form `f x = f y` into `x = y` -/
-- /FULL

-- TERSE
-- ######################################################
-- Micro Sermon

/- Mindless proof-hacking is a terrible temptation...

    Try to resist!
-/

-- /TERSE
-- FULL
/- ###################################################### -/
/- Additional Exercises -/

-- EX3 (beq_symm)
theorem beq_symm : forall (n m : Nat),
  (n == m) = (m == n) := by

  intro n m
  induction n generalizing m
  . cases m
    . rfl
    . rfl
  . case succ n' ih =>
    cases m
    . rfl
    . rw [beq_succ, beq_succ]
      exact ih _
-- ADMITTED
-- /ADMITTED
-- GRADE_THEOREM 3: beq_symm
-- []

-- EX3AM? (beq_symm_informal)
/- Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any `Nat`s `n` `m`, `(n == m) = (m == n)`.

   Proof: -/
-- SOLUTION
/-
   Let an arbitrary Nat `n` be given.  Proceed by induction
   on `n`.

   - For the base case, we have `n = 0`.  Let `m` be given.
     We must show that
[[
       0 == m = m == 0
]]
     Either `m = 0` or not.

     - If `m = 0`, we must show `0 == 0 = 0 == 0`
       which is true by reflexivity.

     - Otherwise, `m = .succ m'` for some `m'`, and we must show
       `0 == (.succ m') = (.succ m') == 0`. By the definition
       of `beq`, both sides are `false`.

   - In the inductive case, we have `n = .succ n'` for some
     `n'` such that, for any `m`,
[[
       n' == m = m == n'
]]
     Let `m` be given.  Again, `m` is either zero or nonzero.

     - Suppose first `m = 0`.  It's
       enough to show `(.succ n') == 0 = 0 == (.succ n')`.
       By the definition of `beq`, both sides are `false`.

     - Otherwise, `m = .succ m'` for some `m'`.  By the
       assumption, it's enough to show:
[[
         (.succ n') == (.succ m') = (.succ m') == (.succ n')
]]
       And, by the definition of `beq`, this reduces to
       showing:
[[
         m' == n' = n' == m'.
]]
       which is exactly the induction hypothesis.  -/
-- /SOLUTION
-- []
-- /FULL

-- FULL
-- EX3? (beq_trans)
theorem beq_trans : forall (n m p : Nat),
  (n == m) = true ->
  (m == p) = true ->
  (n == p) = true := by
-- ADMITTED
  intros n m p hnm hmp
  apply beq_eq at hnm
  rw [hnm, hmp]
-- /ADMITTED
-- []
-- /FULL

-- FULL
-- EX3AM (split_combine)
/- We proved, in an exercise above, that `combine` is the inverse of
    `split`.  Complete the definition of `split_combine_statement`
    below with a property that states that `split` is the inverse of
    `combine`. Then, prove that the property holds.

    Hint: Take a look at the definition of `combine` in \CHAP{Poly}.
    Your property will need to account for the behavior of `combine`
    in its base cases, which possibly drop some list elements. -/

def split_combine_statement : Prop :=
  /- ("`: Prop`" means that we are giving a name to a
     logical proposition here.) -/
-- ADMITDEF
  forall (α β :Type) (l1 : List α) (l2 : List β),
    l1.length = l2.length ->
    split (zip l1 l2) = (l1, l2)
-- /ADMITDEF

theorem split_combine : split_combine_statement := by
-- ADMITTED
  intros α β l1 l2 h
  induction l1 generalizing l2
  case nil =>
    cases l2
    . rfl
    . contradiction
  case cons hd tl ih =>
    cases l2
    . contradiction
    . case cons hd' tl' =>
      dsimp [split, zip]
      rw [ih]
      injections
-- /ADMITTED
-- QUIETSOLUTION

/- Here are more approaches -/

theorem split_combine' : forall (α β :Type) l (l1 : List α) (l2 : List β),
  (l1, l2) = split l -> split (zip l1 l2) = (l1, l2) := by

  intro α β l l1 l2 h
  induction l generalizing l1 l2
  . case nil =>
    dsimp [split] at h
    injections h1 h2
    rw [h1, h2]
    rfl
  . case cons hd tl ih =>
    let ⟨a, b⟩ := hd
    dsimp [split] at h
    injections h1 h2
    rw [h1, h2]
    dsimp [zip, split]
    rw [ih]
    rfl

/- Theorem split_combine''_equiv :
  forall (X Y:Type) l (l1 : list X) (l2 : list Y),
    (split l = (l1, l2) -> split (combine l1 l2) = (l1, l2))
    <-> (split l = (l1, l2) -> combine l1 l2 = l).
Proof.
  intros X Y.
  induction l; intros; split; intros;
    try solve [inversion H0; auto].
  - inversion H0. destruct x.
    destruct (split l). inversion H2; subst. simpl.
    f_equal. apply IHl; auto. apply H in H0.
    inversion H0. destruct (split (combine x0 y0)).
    inversion H3; subst; auto.
  - pose proof H0. apply H in H0. rewrite H0; auto.
Qed.

Theorem combine_split' : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  induction l as [| [x y] l' IHl'].
  - (* l = [] *) intros l1 l2 Heq.
    simpl in Heq. injection Heq as l2mt l1mt.
    rewrite <- l2mt. rewrite <- l1mt. reflexivity.
  - (* l = (x,y) :: l' *) intros l1 l2 Heq.
    simpl in Heq. destruct (split l') as [l1' l2'].
    injection Heq as l2in l1in.
    rewrite <- l2in. rewrite <- l1in. simpl. rewrite IHl'.
    reflexivity. reflexivity.  Qed. -/
-- /QUIETSOLUTION
-- GRADE_MANUAL 3: split_combine
-- []
-- /FULL

-- FULL
-- EX3A (filter_exercise)
theorem filter_exercise : forall (α : Type) (test : α -> Bool)
                                 (a : α) (l lf : List α),
  filter test l = a :: lf ->
  test a = true := by
-- ADMITTED
  intro α test a l lf h
  induction l generalizing a lf test
  . contradiction
  . case cons hd tl ih =>
    dsimp [filter] at h
    cases h' : (test hd)
    . rw [h'] at h; dsimp at h
      exact ih _ _ _ h
    . rw [h'] at h; dsimp at h
      injections h1 h2
      rw [←h1]
      assumption
-- /ADMITTED
-- GRADE_THEOREM 3: filter_exercise
-- []

-- EX4A! (forall_exists_challenge)
/- Define two recursive `Fixpoints`, `forallb` and `existsb`.  The
    first checks whether every element in a list satisfies a given
    predicate:
[[
      forallb odd [1,3,5,7,9] = true
      forallb negb [false,false] = true
      forallb even [0,2,4,5] = false
      forallb (beq 5) [] = true
]]
    The second checks whether there exists an element in the list that
    satisfies a given predicate:
[[
      existsb (beq 5) [0,2,3,6] = false
      existsb (andb true) [true,true,false] = true
      existsb odd [1,0,0,0,0,3] = true
      existsb even [] = false
]]
    Next, define a _nonrecursive_ version of `existsb` -- call it
    `existsb'` -- using `forallb` and `negb`.

    Finally, prove a theorem `existsb_existsb'` stating that
    `existsb'` and `existsb` have the same behavior.
-/

def forallb {α : Type} (test : α -> Bool) (l : List α) : Bool :=
-- ADMITDEF
  match l with
    | [] => true
    | x :: l' => (test x) && (forallb test l')
-- /ADMITDEF

example : forallb odd [1,3,5,7,9] = true := by rfl
example : forallb not [false,false] = true := by rfl
example : forallb even [0,2,4,5] = false := by rfl
example : forallb (· == 5) [] = true := by rfl

def existsb {α : Type} (test : α -> Bool) (l : List α) : Bool :=
-- ADMITDEF
  match l with
  | [] => false
  | x :: l' => (test x) || (existsb test l')
-- /ADMITDEF

example : existsb (· == 5) [0,2,3,6] = false := by rfl
example : existsb (· && true) [true,true,false] = true := by rfl
example : existsb odd [1,0,0,0,0,3] = true := by rfl
example : existsb even [] = false := by rfl

def existsb' {α : Type} (test : α -> Bool) (l : List α) : Bool :=
-- ADMITDEF
  !(forallb (fun x => !(test x)) l)
-- /ADMITDEF

theorem existsb_existsb' : forall (α : Type) (test : α -> Bool) (l : List α),
  existsb test l = existsb' test l := by
-- Admitted
  intro α test l
  induction l generalizing test
  . case nil => rfl
  . case cons hd tl ih =>
      dsimp [existsb]
      rw [ih]
      dsimp [existsb', forallb]
      rw [Bool.not_and, Bool.not_not]
-- /Admitted

-- GRADE_THEOREM 6: existsb_existsb'
-- []

/- LATER: Another nice exercise would be to show how to
   define forallb in terms of fold, as in...
      Complete the following definition of `every` as a recursive function:
         Definition forallb' (X:Type) (p:X -> Bool) (l:list X) : Bool :=
           fold _ _
             (fun x acc => both_yes _________  __________) ________  _________.
-/

-- HIDE
-- Solutions to the above.

def forallbF {X : Type} (test : X -> Bool) (l : List X) : Bool
  := fold (fun x b => (test x) && b) l true

def existsbF {X : Type} (test : X -> Bool) (l : List X) : Bool
  := fold (fun x b => (test x) || b) l false

theorem existsbF_existsb : forall (X : Type) (test : X -> Bool) (l : List X),
  existsbF test l = existsb test l := by

  intro X test l
  unfold existsbF
  induction l
  . rfl
  . case cons hd tl ih =>
    dsimp [existsb, fold]
    rw [ih]
-- /HIDE
-- /FULL
-- HIDE

-- Local Variables:
-- fill-column: 70
-- End:
-- /HIDE
