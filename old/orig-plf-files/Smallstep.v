(** * Smallstep: Small-step Operational Semantics *)

(* SOONER: In this and later chapters, we are not very consistent
   about presenting computation rules first and congruence rules
   after... *)
(* INSTRUCTORS: This chapter is meaty, but quite short -- probably too
   short for a whole week of class (though long enough that it will
   probably spill into part of a second 80-minute lecture).  Some of
   the material from Types.v (maybe even the whole thing) can be
   included in the same week (and perhaps the same homework
   assignment). *)
(* INSTRUCTORS: We've tried to be consistent about terminology here
   and in following chapters:
     - "steps" for the single-step relation;
     - "reduces", "executes", or "normalizes" for multi-step;
     - "evaluates" for big-step.

   One caveat for lecturers: the intuition of "abstract virtual
   machines" is fine but doesn't work well if you overdo it.  For
   example, real VMs don't generally spin off other VMs recursivly, as
   our smallstep rules do!

*)
(* HIDE: Sometime in the early 2010s, we did some mining past exams
   for exercises...
   - Loris: No interesting exercise in Finals of 2007-2009-2010-2011.
     Nothing in second midterms except for 2011.
   - 2011 midterm proposes the following exercise: give the small step
     relation of FLIP X (alternatively HAVOC, ANYTHING).  We could
     then ask to extend the proof of equivalence of big step vs small
     step (personally don't like it too much).
   - Maybe we can ask how they would adapt the definition of Hoare
     triple to small step (maybe in the exam). *)
(* HIDE: BCP: I also have a bunch of slides from earlier offerings of
   CIS500 that might be good additions to the TERSE notes. *)
(* HIDE: Possible major restructuring: This chapter might better be
   postponed to later in the course.  A big-step presentation of
   STLC (and maybe even some of the extensions like subtyping?), could
   come first.  However, this would invite a much bigger change, where
   *all* the variants of STLC (with refs, with subtyping, ...) are
   done in big-step style.  This requires more thought... *)
(* HIDE: Wonder whether it would be interesting to show them how to
   make a correspondence with a "real abstract machine" at a lower
   level...?  There's a start at an exercise along these lines
   below. *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden".
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.

Definition FILL_IN_HERE := <{True}>.
(* TERSE: /HIDEFROMHTML *)

(* TERSE *)
(** ** Big-step Evaluation *)
(* /TERSE *)
(** TERSE: Our semantics for Imp is written in the so-called
    "big-step" style...

    Evaluation rules take an expression (or command) to a final answer
    "all in one step":
[[
      2 + 2 + 3 * 4 ==> 16
]]

  But big-step semantics makes it hard to talk about what
  happens _along the way_...
*)

(* TERSE *)
(** ** Small-step Evaluation *)
(* /TERSE *)
(** TERSE: _Small-step_ style: Alternatively, we can show how to "reduce"
    an expression to a simpler form by performing a single step
    of computation:
[[
      2 + 2 + 3 * 4
      --> 2 + 2 + 12
      --> 4 + 12
      --> 16
]]
    Advantages of the small-step style include:

        - Finer-grained "abstract machine", closer to real
          implementations

        - Extends smoothly to concurrent languages and languages
          with other sorts of _computational effects_.

        - Separates _divergence_ (nontermination) from
          _stuckness_ (run-time error)

*)
(** FULL: The evaluators we have seen so far (for [aexp]s, [bexp]s,
    commands, ...) have been formulated in a "big-step" style: they
    specify how a given expression can be evaluated to its final
    value (or a how command plus a store can be evaluated to a final
    store) "all in one big step."

    This style is simple and natural for many purposes -- indeed,
    Gilles Kahn, who popularized it, called it _natural semantics_.
    But there are some things it does not do well.  In particular, it
    does not give us a convenient way of talking about _concurrent_
    programming languages, where the semantics of a program -- the
    essence of how it behaves -- includes not just which input states
    get mapped to which output states, but also the intermediate
    states that it passes through along the way; this is crucial,
    since these states can also be observed by concurrently executing
    code.

    Another shortcoming of the big-step style is more technical but
    equally critical in many situations.

    Suppose we want to define a variant of Imp where variables could
    hold _either_ numbers _or_ lists of numbers.  In the syntax of
    this extended language, it will be possible to write strange
    expressions like [2 + nil], and our semantics for arithmetic
    expressions will then need to say something about how such
    expressions behave.  One possibility is to maintain the convention
    that every arithmetic expression evaluates to some number by
    choosing some way of viewing a list as a number -- e.g., by
    specifying that a list should be interpreted as [0] when it occurs
    in a context expecting a number.  But this would be a bit of a
    hack.

    A much more natural approach is simply to say that the behavior of
    the expression [2+nil] is _undefined_ -- i.e., it doesn't evaluate
    to any result at all.  And we can easily do this: we just have to
    formulate [aeval] and [beval] as [Inductive] propositions rather
    than [Fixpoint]s, so that we can make them partial functions
    instead of total ones.

    Now, however, we encounter a serious deficiency.  In this
    language, a command might fail to map a given starting state to
    any ending state for _two quite different reasons_: either because
    the execution gets into an infinite loop or because, at some
    point, the program tries to do an operation that makes no sense,
    such as adding a number to a list, so that none of the evaluation
    rules can be applied.

    These two outcomes -- nontermination vs. getting stuck in an
    erroneous configuration -- should not be confused.  In particular,
    we want to _allow_ the first (because permitting the possibility
    of infinite loops is the price we pay for the convenience of
    programming with general looping constructs like [while]) but
    _prevent_ the second (which is just wrong), for example by adding
    some form of _typechecking_ to the language.  Indeed, this will be
    a major topic in the rest of the course.  As a first step, we need
    a way of presenting the semantics that allows us to distinguish
    nontermination from erroneous "stuck states."

    So, for lots of reasons, we'd like to have a finer-grained way of
    defining and reasoning about program behaviors.  This is the topic
    of the present chapter.  Our goal is to replace the "big-step"
    [eval] relation with a "small-step" relation that specifies, for a
    given program, how its atomic steps of computation are
    performed. *)

(* ########################################################### *)
(** * A Toy Language *)

(** FULL: To save space in the discussion, let's start with an
    incredibly simple language containing just constants and
    addition.  (We use single letters -- [C] and [P] (for Constant and
    Plus) -- as constructor names, for brevity.)  At the end of the
    chapter, we'll see how to apply the same techniques to the full
    Imp language.  *)
(** TERSE: The world's simplest programming language: *)

Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)

(** FULL: Here is a standard evaluator for this language, written in
    the big-step style that we've been using up to this point. *)
(** TERSE: *** Big-step evaluation as a function *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.

(** FULL: Here is the same evaluator, written in exactly the same
    style, but formulated as an inductively defined relation.
    We use the notation [t ==> n] for "[t] evaluates to [n]." *)
(** TERSE: *** Big-step evaluation as a relation *)
(**
[[[
                               ---------                               (E_C)
                               C n ==> n

                               t1 ==> n1
                               t2 ==> n2
                           -------------------                         (E_P)
                           P t1 t2 ==> n1 + n2
]]]
*)

(* TERSE: HIDEFROMHTML *)
Reserved Notation " t '==>' n " (at level 50, left associativity).
(* TERSE: /HIDEFROMHTML *)

Inductive eval : tm -> nat -> Prop :=
  | E_C : forall n,
      C n ==> n
  | E_P : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)

(* TERSE: HIDEFROMHTML *)
where " t '==>' n " := (eval t n).
(* TERSE: /HIDEFROMHTML *)

(* TERSE: HIDEFROMHTML *)
Module SimpleArith1.
(* TERSE: /HIDEFROMHTML *)

(** FULL: Now, here is the corresponding _small-step_ evaluation relation. *)
(** TERSE: *** Small-step evaluation relation *)
(** [[[
                     -------------------------------                (ST_PCC)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_P1)
                         P t1 t2 --> P t1' t2

                              t2 --> t2'
                      ----------------------------                   (ST_P2)
                      P (C n1) t2 --> P (C n1) t2'
]]]
*)
(** TERSE: Notice:

       - each step reduces the _leftmost_ [P] node that is ready to go

             - first rule tells how to rewrite this node

             - second and third rules tell where to find it

       - constants are not related to anything -- i.e., they do not step
         to anything
*)
(** TERSE: *** Small-step evaluation in Rocq *)

(* TERSE: HIDEFROMHTML *)
Reserved Notation " t '-->' t' " (at level 40).
(* TERSE: /HIDEFROMHTML *)

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'

(* TERSE: HIDEFROMHTML *)
  where " t '-->' t' " := (step t t').
(* TERSE: /HIDEFROMHTML *)

(** FULL: Things to notice:

    - We are defining a single reduction step, in which just one [P]
      node is replaced by its value.

    - Each step finds the _leftmost_ [P] node that is ready to
      go (both of its operands are constants) and rewrites it in
      place.  The first rule tells how to rewrite this [P] node
      itself; the other two rules tell how to find it.

    - A term that is just a constant cannot take a step. *)

(** TERSE: *** Examples *)
(** FULL: Let's pause and check a couple of examples of reasoning with
    the [step] relation... *)

(** If [t1] can take a step to [t1'], then [P t1 t2] steps
    to [P t1' t2]: *)

Example test_step_1 :
      P
        (P (C 1) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C 4)
        (P (C 2) (C 4)).
(* FOLD *)
Proof.
  apply ST_P1. apply ST_PCC.  Qed.
(* /FOLD *)

(* FULL *)
(* EX1 (test_step_2) *)
(** Right-hand sides of sums can take a step only when the
    left-hand side is finished: if [t2] can take a step to [t2'],
    then [P (C n) t2] steps to [P (C n) t2']: *)

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 1) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C 4)).
Proof.
  (* ADMITTED *)
  apply ST_P2. apply ST_P2. apply ST_PCC. Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)
(* QUIZ *)
(** To what does the following term step?

[[
    P (P (C 1) (C 2)) (P (C 1) (C 2))
]]

    (A) [C 6]

    (B) [P (C 3) (P (C 1) (C 2))]

    (C) [P (P (C 1) (C 2)) (C 3)]

    (D) [P (C 3) (C 3)]

    (E) None of the above
[[
_________________________________________________
Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'
]]
*)
(* /QUIZ *)
(* QUIZ *)
(** What about this one?

[[
    C 1
]]

    (A) [C 1]

    (B) [P (C 0) (C 1)]

    (C) None of the above
[[
_________________________________________________
Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'
]]
*)
(* /QUIZ *)

(* TERSE: HIDEFROMHTML *)
End SimpleArith1.
(* TERSE: /HIDEFROMHTML *)

(* ########################################################### *)
(** * Relations *)

(** FULL: We will be working with several different single-step
    relations, so it is helpful to generalize a bit and state a few
    definitions and theorems about relations in general.  (The
    optional chapter [Rel.v] in _Logical Foundations_ develops some of
    these ideas in a bit more detail; reviewing that chapter may be
    useful if the treatment here feels too terse.) *)

(** A _binary relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)

(** LATER: Should we be getting this (and deterministic, multi, etc.)
    from the standard library?  Arguably yes, though the naming in the
    library is awkward in places. *)
Definition relation (X : Type) := X -> X -> Prop.

(** TERSE: The step relation [-->] is an example of a relation on [tm]. *)

(** FULL: Our main examples of such relations in this chapter will be
    the single-step reduction relation, [-->], and its multi-step
    variant, [-->*], defined below, but there are many other
    examples -- e.g., the "equals," "less than," "less than or equal
    to," and "is the square of" relations on numbers, and the "prefix
    of" relation on lists and strings. *)

(** TERSE: *** Determinism *)

(** One simple property of the [-->] relation is that, like the
    big-step evaluation relation for Imp, it is _deterministic_.

    _Theorem_: For each [t], there is at most one [t'] such that [t]
    steps to [t'] ([t --> t'] is provable). *)

(** FULL: _Proof sketch_: We show that if [x] steps to both [y1] and
    [y2], then [y1] and [y2] are equal, by induction on a derivation
    of [step x y1].  There are several cases to consider, depending on
    the last rule used in this derivation and the last rule in the
    given derivation of [step x y2].

      - If both are [ST_PCC], the result is immediate.

      - The cases when both derivations end with [ST_P1] or
        [ST_P2] follow by the induction hypothesis.

      - It cannot happen that one is [ST_PCC] and the other
        is [ST_P1] or [ST_P2], since this would imply that [x]
        has the form [P t1 t2] where both [t1] and [t2] are
        constants (by [ST_PCC]) _and_ one of [t1] or [t2]
        has the form [P _].

      - Similarly, it cannot happen that one is [ST_P1] and the
        other is [ST_P2], since this would imply that [x] has the
        form [P t1 t2] where [t1] has both the form [P t11 t12] and the
        form [C n]. [] *)

(** Formally: *)

(* INSTRUCTORS: Potential gotcha: this name makes sense in this
   context, but the usual name for this property of relations is
   "functional". *)
Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(* TERSE: HIDEFROMHTML *)
Module SimpleArith2.
Import SimpleArith1.
(* TERSE: /HIDEFROMHTML *)

Theorem step_deterministic:
  deterministic step.
(** TERSE: *** *)
Proof.
  unfold deterministic. intros x y1 y2 Hy1.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - (* ST_PCC *) inversion Hy2; subst.
    + (* ST_PCC *) reflexivity.
    + (* ST_P1 *) inversion H2.
    + (* ST_P2 *) inversion H2.
  - (* ST_P1 *) inversion Hy2; subst.
    + (* ST_PCC *)
      inversion Hy1.
    + (* ST_P1 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
    + (* ST_P2 *)
      inversion Hy1.
  - (* ST_P2 *) inversion Hy2; subst.
    + (* ST_PCC *)
      inversion Hy1.
    + (* ST_P1 *) inversion H2.
    + (* ST_P2 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

(* TERSE: HIDEFROMHTML *)
End SimpleArith2.
(* TERSE: /HIDEFROMHTML *)

(** FULL: There is some annoying repetition in this proof.  Each use of
    [inversion Hy2] results in three subcases, only one of which is
    relevant (the one that matches the current case in the induction
    on [Hy1]).  The other two subcases need to be dismissed by finding
    the contradiction among the hypotheses and doing inversion on it.

    The following custom tactic, called [solve_by_inverts], can be
    helpful in such cases.  It will solve the goal if it can be solved
    by inverting some hypothesis; otherwise, it fails. *)
(** TERSE: *** *)
(** TERSE: Automation digression...

    Let's define a little tactic to decrease annoying repetition in
    this proof: *)

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

(** FULL: The details of how this works are not important, but it
    illustrates the power of Rocq's [Ltac] language for
    programmatically defining special-purpose tactics.  It looks
    through the current proof state for a hypothesis [H] (the first
    [match]) of type [Prop] (the second [match]) such that performing
    inversion on [H] (followed by a recursive invocation of the same
    tactic, if its argument [n] is greater than one) completely solves
    the current goal.  If no such hypothesis exists, it fails.

    We will usually want to call [solve_by_inverts] with argument
    [1] (especially as larger arguments can lead to very slow proof
    checking), so we define [solve_by_invert] as a shorthand for this
    case. *)

Ltac solve_by_invert :=
  solve_by_inverts 1.

(** TERSE: *** *)
(** The proof of the previous theorem can now be simplified... *)

(* TERSE: HIDEFROMHTML *)
Module SimpleArith3.
Import SimpleArith1.
(* TERSE: /HIDEFROMHTML *)

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - (* ST_PCC *) reflexivity.
  - (* ST_P1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_P2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

(* TERSE: HIDEFROMHTML *)
End SimpleArith3.
(* TERSE: /HIDEFROMHTML *)

(* ########################################################### *)
(** ** Values *)

(** FULL: Next, it will be useful to slightly reformulate the
    definition of single-step reduction by stating it in terms of
    "values." *)

(** It can be useful to think of the [-->] relation as defining an
    _abstract machine_:

      - At any moment, the _state_ of the machine is a term.

      - A _step_ of the machine is an atomic unit of computation --
        here, a single "add" operation.

      - The _halting states_ of the machine are ones where there is no
        more computation to be done. *)
(** TERSE: *** *)

(** We can then _execute_ a term [t] as follows:

      - Take [t] as the starting state of the machine.

      - Repeatedly use the [-->] relation to find a sequence of
        machine states, starting with [t], where each state steps to
        the next.

      - When no more reduction is possible, "read out" the final state
        of the machine as the result of execution. *)

(** TERSE: *** *)
(** FULL: Intuitively, it is clear that the final states of our
    machine are always terms of the form [C n] for some [n].
    We call such terms _values_. *)
(** TERSE: Final states of our machine are terms of the form
    [C n] for some [n].  We call such terms _values_. *)

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n).

(** FULL: Having introduced the idea of values, we can use it in the
    definition of the [-->] relation to write [ST_P2] rule in a
    slightly more elegant way: *)
(** TERSE: *** *)

(** TERSE: This gives a more elegant way of writing the [ST_P2] rule: *)
(** [[[
                     -------------------------------                (ST_PCC)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_P1)
                         P t1 t2 --> P t1' t2

                               value v1
                              t2 --> t2'
                         --------------------                        (ST_P2)
                         P v1 t2 --> P v1 t2'
]]]
 *)

(** FULL: Again, the variable names in the informal presentation carry
    important information: by convention, [v1] ranges only over
    values, while [t1] and [t2] range over arbitrary terms.

    (Given this convention, the explicit [value] hypothesis is
    arguably redundant, since the naming convention tells us where to
    add it when translating the informal rule to Rocq.  We'll keep it
    for now, to maintain a close correspondence between the informal
    and Rocq versions of the rules, but later on we'll drop it in
    informal rules for brevity.) *)
(** TERSE: *** *)
(** TERSE: Again, variable names carry important information:
       - [v1] ranges only over values
       - [t1] and [t2] range over arbitrary terms

    So the [value] hypothesis in the last rule is actually redundant
    in the informal presentation: The naming convention tells us where
    to add it when translating the informal rule to Rocq.  We'll keep
    it for now, but in later chapters we'll elide it. *)

(** TERSE: *** *)
(**  Here are the formal rules: *)

(* TERSE: HIDEFROMHTML *)
Reserved Notation " t '-->' t' " (at level 40).
(* TERSE: /HIDEFROMHTML *)

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
          P (C n1) (C n2)
      --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_P2 : forall v1 t2 t2',
        value v1 ->                     (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

(* TERSE: HIDEFROMHTML *)
  where " t '-->' t' " := (step t t').
(* TERSE: /HIDEFROMHTML *)

(* FULL *)
(* EX3! (redo_determinism) *)
(** As a sanity check on this change, let's re-verify determinism.
    Here's an informal proof:

    _Proof sketch_: We must show that if [x] steps to both [y1] and
    [y2], then [y1] and [y2] are equal.  Consider the final rules used
    in the derivations of [step x y1] and [step x y2].

    - If both are [ST_PCC], the result is immediate.

    - The cases when both derivations end with [ST_P1] or
      [ST_P2] follow by the induction hypothesis.

    - It cannot happen that one is [ST_PCC] and the other
      is [ST_P1] or [ST_P2], since this would imply that [x] has
      the form [P t1 t2] where both [t1] and [t2] are constants (by
      [ST_PCC]) _and_ one of [t1] or [t2] has the form [P
      _].

    - Similarly, it cannot happen that one is [ST_P1] and the other
      is [ST_P2], since this would imply that [x] has the form [P
      t1 t2] where [t1] both has the form [P t11 t12] and is a
      value (hence has the form [C n]). [] *)

(** Most of this proof is the same as the one above.  But to get
    maximum benefit from the exercise you should try to write your
    formal version from scratch and just use the earlier one if you
    get stuck. *)

Theorem step_deterministic :
  deterministic step.
Proof.
  (* ADMITTED *)
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros; inversion Hy2; subst; try (solve_by_inverts 2).
  - reflexivity.
  - apply IHHy1 in H2. rewrite H2. reflexivity.
  - apply IHHy1 in H4. rewrite H4. reflexivity.
Qed.
(* GRADE_THEOREM 3: step_deterministic *)
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* ########################################################### *)
(** ** Strong Progress and Normal Forms *)

(** FULL: The definition of single-step reduction for our toy language
    is fairly simple, but for a larger language it would be easy to
    forget one of the rules and accidentally create a situation where
    some term cannot take a step even though it has not been
    completely reduced to a value.  The following theorem shows that
    we did not, in fact, make such a mistake here. *)

(** _Theorem_ (_Strong Progress_): If [t] is a term, then either [t]
    is a value or else there exists a term [t'] such that [t --> t']. *)

(** FULL: _Proof_: By induction on [t].

    - Suppose [t = C n]. Then [t] is a value.

    - Suppose [t = P t1 t2], where (by the IH) [t1] either is a value
      or can step to some [t1'], and where [t2] is either a value or
      can step to some [t2']. We must show [P t1 t2] is either a value
      or steps to some [t'].

      - If [t1] and [t2] are both values, then [t] can take a step, by
        [ST_PCC].

      - If [t1] is a value and [t2] can take a step, then so can [t],
        by [ST_P2].

      - If [t1] can take a step, then so can [t], by [ST_P1].  []

   Or, formally: *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
(* FOLD *)
Proof.
  induction t.
  - (* C case *) left. apply v_C.
  - (* P case *) right. destruct IHt1 as [IHt1 | [t1' Ht1] ].
    + (* t1 is a value *) destruct IHt2 as [IHt2 | [t2' Ht2] ].
      * (* t2 is a value *) inversion IHt1. inversion IHt2.
        exists (C (n + n0)).
        apply ST_PCC.
      * (* t2 steps *)
        exists (P t1 t2').
        apply ST_P2; auto.
    + (* t1 steps *)
      exists (P t1' t2).
      apply ST_P1. apply Ht1.
Qed.
(* /FOLD *)

(** FULL: This important property is called _strong progress_, because
    every term either is a value or can "make progress" by stepping to
    some other term.  (The qualifier "strong" distinguishes it from a
    more refined version that we'll see in later chapters, called
    simply _progress_.) *)

(** TERSE: *** Normal forms *)

(** The idea of "making progress" can be extended to tell us something
    interesting about values in this language: they are exactly the
    terms that do _not_ make progress in this sense.

    To state this observation formally, let's begin by giving a name
    to "terms that cannot make progress."  We'll call them _normal
    forms_.  *)

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(* FULL *)
(** Note that this definition specifies what it is to be a normal form
    for an _arbitrary_ relation [R] over an arbitrary set [X], not
    just for the particular single-step reduction relation over terms
    that we are interested in at the moment.  We'll re-use the same
    terminology for talking about other relations later in the
    course. *)
(* /FULL *)

(** TERSE: *** Values vs. Normal Forms *)

(* QUIZ *)
(** What is a _value_ in this language?

    What is a _normal form_?
*)
(* /QUIZ *)

(** FULL: We can use this terminology to generalize the observation we
    made in the strong progress theorem: in this language (though not
    necessarily, in general), normal forms and values are actually the
    same thing. *)
(** TERSE: In this language, normal forms and values coincide: *)

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
(* FOLD *)
Proof.
  unfold normal_form. intros v H contra.
  destruct contra. destruct H. inversion H0.
Qed.
(* /FOLD *)

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
(* FOLD *)
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t --> t').
  { apply strong_progress. }
  destruct G as [G | G].
  - (* l *) apply G.
  - (* r *) contradiction.
Qed.
(* /FOLD *)

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
(* FOLD *)
Proof.
  split.
  - apply nf_is_value.
  - apply value_is_nf.
Qed.
(* /FOLD *)

(** Why is this interesting?

    Because [value] is a syntactic concept -- it is defined by looking
    at the way a term is written -- while [normal_form] is a semantic
    one -- it is defined by looking at how the term steps.

    It is not obvious that these concepts should characterize the same
    set of terms!  *)

(** TERSE: *** *)
(** Indeed, we could easily have written the definitions (incorrectly)
    so that they would _not_ coincide... *)

(* FULL *)
(* EX3? (value_not_same_as_normal_form1) *)
(* /FULL *)
(** We might, for example, define [value] so that it
    includes some terms that are not finished reducing: *)
(** FULL: (Even if you don't work this exercise and the following ones
    in Rocq, make sure you can think of an example of such a term.) *)

(* TERSE: HIDEFROMHTML *)
Module Temp1.
(* TERSE: /HIDEFROMHTML *)

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n)
  | v_funny : forall t1 n,
                value (P t1 (C n)).              (* <--- *)

(* HIDEFROMHTML *)
Reserved Notation " t '-->' t' " (at level 40).
(* /HIDEFROMHTML *)
(* TERSE: HIDEFROMHTML *)
Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').
(* TERSE: /HIDEFROMHTML *)
(* QUIZ *)
(** Using this wrong definition of [value], to how many different values
    does the following term reduce in zero or more steps?
[[
       P
         (P (C 1) (C 2))
         (C 3)

  ________________________________________
      Inductive value : tm -> Prop :=
        | v_C : forall n, value (C n)
        | v_funny : forall t1 n,
                      value (P t1 (C n)).
]]

*)
(* INSTRUCTORS: Three:
   P (P (C 1) (C 2)) (C 3) itself is a value.
   P (C 3) (C 3) is a value.
   C 6 is a value.
*)
(* HIDE *)
Lemma testval1 : value (P (P (C 1) (C 2)) (C 3)).
Proof. apply v_funny. Qed.
Lemma testval2 : (P (P (C 1) (C 2)) (C 3)) --> P (C 3) (C 3) /\ value (P (C 3) (C 3)).
Proof.
  split.
  - apply ST_P1. apply ST_PCC.
  - apply v_funny. Qed.
Lemma testval3 : P (C 3) (C 3) --> (C 6) /\ value (C 6).
Proof.
  split.
  - apply ST_PCC.
  - apply v_C. Qed.
(* /HIDE *)

(* /QUIZ *)
(* QUIZ *)
(** To how many different terms does the following term [step]
    (in one step)?
[[
       P (P (C 1) (C 2)) (P (C 3) (C 4))

  ________________________________________
      Inductive value : tm -> Prop :=
        | v_C : forall n, value (C n)
        | v_funny : forall t1 n,
                      value (P t1 (C n)).
]]
*)
(* INSTRUCTORS: Two: P (C 3) (P (C 3) (C 4)) via ST_P1 and
                     P (P (C 1) (C 2)) (C 7) via ST_P2 *)
(* /QUIZ *)

(** TERSE: *** *)

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
(* FOLD *)
Proof.
  (* ADMITTED *)
  exists (P (C 0) (C 0)).
  split.
  - (* l *) apply v_funny.
  - (* r *) unfold normal_form. unfold not. intros H. apply H.
    exists (C (0 + 0)).
    apply ST_PCC.
Qed.
(* /ADMITTED *)
(* /FOLD *)
(* TERSE: HIDEFROMHTML *)
End Temp1.
(* TERSE: /HIDEFROMHTML *)

(* FULL *)
(** [] *)
(* /FULL *)

(* ##################################################### *)
(** TERSE: *** *)
(* FULL *)
(* EX2? (value_not_same_as_normal_form2) *)
(* /FULL *)
(** Or we might (again, wrongly) define [step] so that it permits
    something designated as a value to reduce further. *)

(* TERSE: HIDEFROMHTML *)
Module Temp2.
(* TERSE: /HIDEFROMHTML *)

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n).         (* Original definition *)

(* TERSE: HIDEFROMHTML *)
Reserved Notation " t '-->' t' " (at level 40).
(* TERSE: /HIDEFROMHTML *)

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n --> P (C n) (C 0)                  (* <--- NEW *)
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

(* TERSE: HIDEFROMHTML *)
  where " t '-->' t' " := (step t t').
(* TERSE: /HIDEFROMHTML *)

(* QUIZ *)
(** With this definition, to how many different terms does
    the following term step (in exactly one step)?
[[
      P (C 1) (C 3)

   _______________________________________
     Inductive step : tm -> tm -> Prop :=
       | ST_Funny : forall n,
           C n --> P (C n) (C 0)
       | ST_PCC : forall n1 n2,
           P (C n1) (C n2) --> C (n1 + n2)
       | ST_P1 : forall t1 t1' t2,
           t1 --> t1' ->
           P t1 t2 --> P t1' t2
       | ST_P2 : forall v1 t2 t2',
           value v1 ->
           t2 --> t2' ->
           P v1 t2 --> P v1 t2'

]]
*)
(* /QUIZ *)
(* INSTRUCTORS: Three: ST_PCC yields (C 4) and
                       ST_P1 with ST_funny yields P (P (C 1) (C 0)) (C 3)
                       ST_P2 with ST_funny yields P (C 1) (P (C 3) (C 0)) *)
(* TERSE *)
(** TERSE: *** *)
(** And we again lose the property that values are the same as
    normal forms: *)

(* /TERSE *)
Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
(* FOLD *)
Proof.
  (* ADMITTED *)
  exists (C 5).
  split.
  - (* l *) apply v_C.
  - (* r *) unfold normal_form. unfold not. intros H. apply H.
    exists (P (C 5) (C 0)).
    apply ST_Funny.
Qed.
(* /ADMITTED *)

(* /FOLD *)
(* TERSE: HIDEFROMHTML *)
End Temp2.
(* TERSE: /HIDEFROMHTML *)
(* FULL *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)
(* FULL *)
(* EX3? (value_not_same_as_normal_form3) *)
(* /FULL *)
(** FULL: Finally, we might define [value] and [step] so that there is some
    term that is not a value but that cannot take a step in the [step]
    relation.  Such terms are said to be _stuck_.  In this case, this is
    caused by a mistake in the semantics, but we will also see
    situations where, even in a correct language definition, it makes
    sense to allow some terms to be stuck. *)
(** TERSE: Finally, we might define [value] and [step] so that there is some
    term that is _not_ a value but that _also_ cannot take a step.

    Such terms are said to be _stuck_. *)

(* TERSE: HIDEFROMHTML *)
Module Temp3.
(* TERSE: /HIDEFROMHTML *)

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n).

(* TERSE: HIDEFROMHTML *)
Reserved Notation " t '-->' t' " (at level 40).
(* TERSE: /HIDEFROMHTML *)

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2

(* TERSE: HIDEFROMHTML *)
  where " t '-->' t' " := (step t t').
(* TERSE: /HIDEFROMHTML *)

(** (Note that [ST_P2] is missing.) *)

(* QUIZ *)
(** With this definition, to how many terms does the
    following term step (in one step)?

[[
    P (C 1) (P (C 1) (C 2))

  _________________________________________
    Inductive step : tm -> tm -> Prop :=
      | ST_PCC : forall n1 n2,
          P (C n1) (C n2) --> C (n1 + n2)
      | ST_P1 : forall t1 t1' t2,
          t1 --> t1' ->
          P t1 t2 --> P t1' t2
]]
*)
(* /QUIZ *)
(* INSTRUCTORS: none! *)

(* TERSE *)
(** TERSE: *** *)
(** And, once again: *)

(* /TERSE *)
Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
(* FOLD *)
Proof.
  (* ADMITTED *)
  exists (P (C 1) (P (C 1) (C 2))).
  split.
  - (* l *) intros H. inversion H.
  - (* r *) unfold normal_form. unfold not. intros H. destruct H.
    inversion H. subst. inversion H3.
Qed.
(* /ADMITTED *)
(* /FOLD *)

(* TERSE: HIDEFROMHTML *)
End Temp3.
(* TERSE: /HIDEFROMHTML *)
(* FULL *)
(** [] *)
(* /FULL *)

(* FULL *)
(* ########################################################### *)
(** *** Additional Exercises *)

Module Temp4.

(** Here is another very simple language whose terms, instead of being
    just addition expressions and numbers, are just the booleans true
    and false plus a conditional expression... *)

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_tru : value tru
  | v_fls : value fls.

(* HIDEFROMHTML *)
Reserved Notation " t '-->' t' " (at level 40).
(* /HIDEFROMHTML *)

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').

(* EX1M? (smallstep_bools) *)
(** Which of the following propositions are provable?  (This is just a
    thought exercise, but for an extra challenge feel free to prove
    your answers in Rocq.) *)

Definition bool_step_prop1 :=
  fls --> fls.

(* SOLUTION *)
(** No -- no rule applies. *)

Lemma not_bool_step_prop1 :
  ~ bool_step_prop1.
Proof.
  unfold bool_step_prop1.
  intros C. inversion C.  Qed.
(* /SOLUTION *)

Definition bool_step_prop2 :=
     test
       tru
       (test tru tru tru)
       (test fls fls fls)
  -->
     tru.

(* SOLUTION *)
(** No -- it takes two steps to do that; first it steps to [test
    tru tru tru]*)

Lemma not_bool_step_prop2 :
  ~ bool_step_prop2.
Proof.
  unfold bool_step_prop2.
  intros C. inversion C.
Qed.
(* /SOLUTION *)

Definition bool_step_prop3 :=
     test
       (test tru tru tru)
       (test tru tru tru)
       fls
   -->
     test
       tru
       (test tru tru tru)
       fls.

(* SOLUTION *)
(** Yes, using [ST_If] followed by [ST_IfTrue]. *)

Lemma bool_step_prop3_pf :
  bool_step_prop3.
Proof.
  unfold bool_step_prop3.
  eapply ST_If. apply ST_IfTrue.
Qed.
(* /SOLUTION *)

(* GRADE_MANUAL 1: smallstep_bools *)
(** [] *)

(* EX3? (strong_progress_bool) *)
(** Just as we proved a progress theorem for plus expressions, we can
    do so for boolean expressions as well. *)

Theorem strong_progress_bool : forall t,
  value t \/ (exists t', t --> t').
Proof.
  (* ADMITTED *)
  induction t.
  - (* tru *) left. apply v_tru.
  - (* fls *) left. apply v_fls.
  - (* test *) right.
    destruct IHt1 as [IHt1 | [t1' Ht1] ].
    + (* left *)
      destruct IHt1; eexists.
      * apply ST_IfTrue.
      * apply ST_IfFalse.
    + (* right *)
      eexists. eapply ST_If. eassumption.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2? (step_deterministic) *)
Theorem step_deterministic : deterministic step.
Proof.
  (* ADMITTED *)
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2; induction Hy1;
  intros y2 H; inversion H; subst;
  try solve_by_invert; try reflexivity.
  (* only case left is ST_If, St_If *)
  apply IHHy1 in H4. rewrite H4. reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)

Module Temp5.

(* EX2 (smallstep_bool_shortcut) *)
(** Suppose we want to add a "short circuit" to the step relation for
    boolean expressions, so that it can recognize when the [then] and
    [else] branches of a conditional are the same value (either
    [tru] or [fls]) and reduce the whole conditional to this
    value in a single step, even if the guard has not yet been reduced
    to a value. For example, we would like this proposition to be
    provable:
[[
         test
            (test tru tru tru)
            fls
            fls
     -->
         fls.
]]
*)

(** Write an extra clause for the step relation that achieves this
    effect and prove [bool_step_prop4]. *)

(* HIDEFROMHTML *)
Reserved Notation " t '-->' t' " (at level 40).
(* /HIDEFROMHTML *)

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3
  (* SOLUTION *)
  | ST_ShortCircuit : forall t1 v2,
      value v2 ->
      test t1 v2 v2 --> v2
(* /SOLUTION *)

  where " t '-->' t' " := (step t t').

Definition bool_step_prop4 :=
         test
            (test tru tru tru)
            fls
            fls
     -->
         fls.

Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  (* ADMITTED *)
  unfold bool_step_prop4.
  apply ST_ShortCircuit. apply v_fls.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: bool_step_prop4_holds *)
(** [] *)

(* EX3M? (properties_of_altered_step) *)
(** It can be shown that the determinism and strong progress theorems
    for the step relation in the lecture notes also hold for the
    definition of [step] given above.

    After we add the clause [ST_ShortCircuit]...

    - Is the [step] relation still deterministic?  Write yes or no and
      briefly (1 sentence) explain your answer.

      Optional: prove your answer correct in Rocq. *)

(* SOLUTION *)
(** Here is a counterexample:
[[
     t = test (test tru tru tru) tru tru
]]
   can step to
[[
     test tru tru tru)
]]
or [tru].
*)
Theorem step_nondeterministic :
  ~ deterministic step.
Proof.
  unfold deterministic.
  intros C.
  remember (test (test tru tru tru) tru tru) as t.
  assert (t --> test tru tru tru) as HS1.
  { subst t. eapply ST_If. apply ST_IfTrue. }
  assert (t --> tru) as HS2.
  { subst t. apply ST_ShortCircuit. apply v_tru. }
  assert (test tru tru tru = tru) as Absurd.
  { eapply C.
    - apply HS1.
    - assumption. }
  discriminate Absurd.
Qed.
(* /SOLUTION *)
(**
   - Does a strong progress theorem hold? Write yes or no and
     briefly (1 sentence) explain your answer.

     Optional: prove your answer correct in Rocq.
*)

(* SOLUTION *)
(** Yes, it holds -- we're never _compelled_ to use
    [ST_ShortCircuit]. We can even use the same proof script! *)

Theorem strong_progress_bool : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - (* tru *) left. apply v_tru.
  - (* fls *) left. apply v_fls.
  - (* test *) right.
    destruct IHt1 as [IHt1 | [t1' Ht1] ].
    + (* left *)
      destruct IHt1; eexists.
      * apply ST_IfTrue.
      * apply ST_IfFalse.
    + (* right *)
      eexists. eapply ST_If. eassumption.
Qed.
(* /SOLUTION *)
(**
   - In general, is there any way we could cause strong progress to
     fail if we took away one or more constructors from the original
     step relation? Write yes or no and briefly (1 sentence) explain
     your answer.

(* SOLUTION *)
  Taking away constructors can cause strong progress to fail -- note
  that each ES rule is used in the proof -- if any one of them is
  missing, the proof won't work!
(* /SOLUTION *)
*)
(* GRADE_MANUAL 3: properties_of_altered_step *)
(** [] *)

End Temp5.
End Temp4.
(* /FULL *)

(* ########################################################### *)
(** * Multi-Step Reduction *)

(* FULL *)
(** We've been working so far with the _single-step reduction_
    relation [-->], which formalizes the individual steps of an
    abstract machine for executing programs.

    We can use the same machine to reduce programs to completion -- to
    find out what final result they yield.  This can be formalized as
    follows:

    - First, we define a _multi-step reduction relation_ [-->*], which
      relates terms [t] and [t'] if [t] can reach [t'] by any number
      (including zero) of single reduction steps.

    - Then we define a "result" of a term [t] as a normal form that
      [t] can reach by multi-step reduction. *)
(* /FULL *)
(* TERSE *)
(** We can now use the single-step relation and the concept of value
    to formalize an entire _execution_ of the abstract machine.

    First, we define a _multi-step reduction relation_ [-->*] that
    relates a starting term to _every_ term that it can reach by
    some number of reduction steps (including zero). *)
(* /TERSE *)

(* ########################################################### *)
(** TERSE: *** *)

(* SOONER: The explanation here might not be good enough for students
   that are not very familiar with relations.  (Definitely not --
   needs more. -BCP) *)
(** Since we'll want to reuse the idea of multi-step reduction many
    times with many different single-step relations, let's pause and
    define the concept generically.

    Given a relation [R] (e.g., the step relation [-->]), we define a
    new relation [multi R], called the _multi-step closure of [R]_ as
    follows. *)

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

(** FULL: (In the \CHAPV1{Rel} chapter of _Logical Foundations_ and in
    the Rocq standard library, this relation is called
    [clos_refl_trans_1n].  We give it a shorter name here for the sake
    of readability.) *)

(** TERSE: *** *)
(** The effect of this definition is that [multi R] relates two
    elements [x] and [y] if

       - [x = y], or
       - [R x y], or
       - there is some nonempty sequence [z1], [z2], ..., [zn] such that
[[
           R x z1
           R z1 z2
           ...
           R zn y.
]]
    Intuitively, if [R] describes a single-step of computation, then
    [z1] ... [zn] are the intermediate steps of computation that get
    us from [x] to [y]. *)

(** TERSE: *** *)
(** We write [-->*] for the [multi step] relation on terms. *)

Notation " t '-->*' t' " := (multi step t t') (at level 40).

(** TERSE: *** *)
(** The relation [multi R] has several crucial properties.

    First, it is obviously _reflexive_ (that is, [forall x, multi R x
    x]).  In the case of the [-->*] (i.e., [multi step]) relation, the
    intuition is that a term can execute to itself by taking zero
    steps of reduction. *)

(** TERSE: *** *)
(** Second, it contains [R] -- that is, single-step reductions are a
    particular case of multi-step executions.  (It is this fact that
    justifies the word "closure" in the term "multi-step closure of
    [R].") *)

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
(* FOLD *)
Proof.
  intros X R x y H.
  apply multi_step with y.
  - apply H.
  - apply multi_refl.
Qed.
(* /FOLD *)

(** TERSE: *** *)

(** Third, [multi R] is _transitive_. *)

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
(* FOLD *)
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y.
      + assumption.
      + apply IHG. assumption.
Qed.
(* /FOLD *)

(** In particular, for the [multi step] relation on terms, if
    [t1 -->* t2] and [t2 -->* t3], then [t1 -->* t3]. *)

(* QUIZ *)
(** Which of the following relations on numbers _cannot_ be expressed
    as [multi R] for some [R]?

    (A) less than or equal

    (B) strictly less than

    (C) equal

    (D) none of the above
*)
(* /QUIZ *)

(* FULL *)
(* ########################################################### *)
(** ** Examples *)
(* /FULL *)
(** TERSE: *** *)
(** Here's a specific instance of the [multi step] relation: *)

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
(* FOLD *)
Proof.
  apply multi_step with
            (P (C (0 + 3))
               (P (C 2) (C 4))).
  { apply ST_P1. apply ST_PCC. }
  apply multi_step with
            (P (C (0 + 3))
               (C (2 + 4))).
  { apply ST_P2.
    - apply v_C.
    - apply ST_PCC. }
  apply multi_R.
  apply ST_PCC.
Qed.
(* /FOLD *)

(* FULL *)
(** Here's an alternate proof of the same fact that uses [eapply] to
    avoid explicitly constructing all the intermediate terms. *)

Lemma test_multistep_1':
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
  -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  eapply multi_step. { apply ST_P1. apply ST_PCC. }
  eapply multi_step. { apply ST_P2.
                       - apply v_C.
                       - apply ST_PCC. }
  eapply multi_step. { apply ST_PCC. }
  apply multi_refl.
Qed.
(* /FULL *)

(* FULL *)
(* EX1? (test_multistep_2) *)
Lemma test_multistep_2:
  C 3 -->* C 3.
Proof.
  (* ADMITTED *)
  apply multi_refl.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX1? (test_multistep_3) *)
Lemma test_multistep_3:
      P (C 0) (C 3)
   -->*
      P (C 0) (C 3).
Proof.
  (* ADMITTED *)
  apply multi_refl.   Qed.
(* /ADMITTED *)
(** [] *)

(* EX2 (test_multistep_4) *)
Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  -->*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  (* ADMITTED *)
  apply multi_step with
         (P
            (C 0)
            (P
              (C 2)
              (C (0 + 3)))).
  { apply ST_P2.
    - apply v_C.
    - apply ST_P2.
      + apply v_C.
      + apply ST_PCC. }
  apply multi_R.
  { apply ST_P2.
    - apply v_C.
    - apply ST_PCC. }
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* ########################################################### *)
(** ** Normal Forms Again *)

(** If [t] reduces to [t'] in zero or more steps and [t'] is a
    normal form, we say that "[t'] is a normal form of [t]." *)

Definition normal_form_of {X : Type} (R : relation X)  (t t' : X) :=
  ((multi R) t t' /\ normal_form R t').

(** FULL: We have already seen that, for our language, single-step
    reduction is deterministic -- i.e., a given term can take a single
    step in at most one way.  It follows from this that, if [t] can
    reach a normal form, then this normal form is unique.

    In other words, we can actually pronounce [normal_form t t'] as
    "[t'] is _the_ normal form of [t]." *)

(** TERSE: *** *)

(** TERSE: Notice:

      - single-step reduction is deterministic;

      - so, if [t] can reach a normal form, then this normal form is unique;

      - so we can pronounce [normal_form t t'] as "[t'] is _the_
        normal form of [t]." *)
(* LATER: YOTAM: The proof can be given for the general case, i.e. that
   determinism of a relation implies the determinism of its [normal_form_of]
   induced counterpart. BCP 23: That would be a nice improvement. *)

(* EX3? (normal_forms_unique) *)
Theorem normal_forms_unique:
  deterministic (normal_form_of step).
(* FOLD *)
Proof.
  (* We recommend using this initial setup as-is! *)
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  (* ADMITTED *)
  induction P11; inversion P21; subst.
  - (* multi_refl, multi_refl *) reflexivity.
  - (* multi_refl, multi_step *)
    exfalso. apply P12. exists y. apply H.
  - (* multi_step, multi_refl *)
    exfalso. apply P22. exists y. apply H.
  - (* multi_step, multi_step *)
    apply IHP11.
    + assumption.
    + assert (y = y0).
      * apply (step_deterministic x); assumption.
      * rewrite H2. assumption. Qed.
(* /ADMITTED *)
(* /FOLD *)
(** [] *)

(** FULL: Indeed, something stronger is true for this language (though
    not for all the languages we will see): the reduction of _any_
    term [t] will eventually reach a normal form in a finite number of steps-- i.e.,
    [normal_form_of] is a _total_ function.  We say the [step]
    relation is _normalizing_. *)

(** TERSE: *** *)
(** TERSE: Indeed, something stronger is true for this language:

       - the reduction of _any_ term [t] will eventually reach a
         normal form in a finite number of steps

    We say the [step] relation is _normalizing_. *)

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t', normal_form_of R t t'.

(** FULL: To prove that [step] is normalizing, we need a couple of lemmas.
    First, we observe that, if [t] reduces to [t'] in many steps, then
    the same sequence of reduction steps within [t] is also possible
    when [t] appears as the first argument to [P], and
    similarly when [t] appears as the second argument to [P]
    (and the first argument is a value). *)

(** TERSE: *** *)
(** TERSE: To prove that [step] is normalizing, we need a couple of lemmas. *)

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.
(* FOLD *)
Proof.
  intros t1 t1' t2 H. induction H.
  - (* multi_refl *) apply multi_refl.
  - (* multi_step *) apply multi_step with (P y t2).
    + apply ST_P1. apply H.
    + apply IHmulti.
Qed.
(* /FOLD *)

(* FULL *)
(* EX2 (multistep_congr_2) *)
(* /FULL *)
Lemma multistep_congr_2 : forall v1 t2 t2',
     value v1 ->
     t2 -->* t2' ->
     P v1 t2 -->* P v1 t2'.
(* FOLD *)
Proof.
  (* ADMITTED *)
  intros v1 t2 t2' Hv H. induction H.
  - (* multi_refl *) apply multi_refl.
  - (* multi_step *) apply multi_step with (P v1 y).
    + apply ST_P2.
      * apply Hv.
      * apply H.
    + apply IHmulti.
Qed.
(* /ADMITTED *)
(* /FOLD *)
(* FULL *)
(** [] *)
(* /FULL *)

(** FULL: With these lemmas in hand, the main proof is a straightforward
    induction.

    _Theorem_: The [step] function is normalizing -- i.e., for every
    [t] there exists some [t'] such that [t] reduces to [t'] and [t']
    is a normal form.

    _Proof sketch_: By induction on terms.  There are two cases to
    consider:

    - [t = C n] for some [n].  Here [t] doesn't take a step, and we
      have [t' = t].  We can derive the left-hand side by reflexivity
      and the right-hand side by observing (a) that values are normal
      forms (by [nf_same_as_value]) and (b) that [t] is a value (by
      [v_C]).

    - [t = P t1 t2] for some [t1] and [t2].  By the IH, [t1] and [t2]
      reduce to normal forms [t1'] and [t2'].  Recall that normal
      forms are values (by [nf_same_as_value]); we therefore know that
      [t1' = C n1] and [t2' = C n2], for some [n1] and [n2].  We can
      combine the [-->*] derivations for [t1] and [t2] using
      [multi_congr_1] and [multi_congr_2] to prove that [P t1 t2]
      reduces in many steps to [t' = C (n1 + n2)].

      Finally, [C (n1 + n2)] is a value, which is in turn a normal
      form by [nf_same_as_value]. [] *)

Theorem step_normalizing :
  normalizing step.
(* FOLD *)
Proof.
  unfold normalizing.
  induction t.
  - (* C case *)
    exists (C n).
    split.
    + (* l *) apply multi_refl.
    + (* r *)
      (* We can use [rewrite] with "iff" statements, not
           just equalities: *)
      apply nf_same_as_value. apply v_C.

  - (* P case *)
    destruct IHt1 as [t1' [Hsteps1 Hnormal1] ].
    destruct IHt2 as [t2' [Hsteps2 Hnormal2] ].
    apply nf_same_as_value in Hnormal1.
    apply nf_same_as_value in Hnormal2.
    destruct Hnormal1 as [n1].
    destruct Hnormal2 as [n2].
    exists (C (n1 + n2)).
    split.
    + (* l *)
      apply multi_trans with (P (C n1) t2).
      * apply multistep_congr_1. apply Hsteps1.
      * apply multi_trans with (P (C n1) (C n2)).
        { apply multistep_congr_2.
          - apply v_C.
          - apply Hsteps2. }
        apply multi_R. apply ST_PCC.
    + (* r *)
      apply nf_same_as_value. apply v_C.
Qed.
(* /FOLD *)

(* ########################################################### *)
(** ** Equivalence of Big-Step and Small-Step *)
(* LATER: We could really use more informal proofs in this section, at
   least in the solutions! *)

(** Having defined the operational semantics of our tiny programming
    language in two different ways (big-step and small-step), it makes
    sense to ask whether these definitions actually define the same
    thing! *)

(** FULL: They do, though it takes a little work to show it.  The
    details are left as an exercise. *)
(** We consider the two implications separately. *)

(* FULL *)
(* EX3 (eval__multistep) *)
(* /FULL *)
Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.

(** TERSE: *** *)
(** The key ideas in the proof can be seen in the following picture:
[[
       P t1 t2 -->            (by ST_P1)
       P t1' t2 -->           (by ST_P1)
       P t1'' t2 -->          (by ST_P1)
       ...
       P (C n1) t2 -->        (by ST_P2)
       P (C n1) t2' -->       (by ST_P2)
       P (C n1) t2'' -->      (by ST_P2)
       ...
       P (C n1) (C n2) -->    (by ST_PCC)
       C (n1 + n2)
]]
    That is, the multi-step reduction of a term of the form [P t1 t2]
    proceeds in three phases:
       - First, we use [ST_P1] some number of times to reduce [t1]
         to a normal form, which must (by [nf_same_as_value]) be a
         term of the form [C n1] for some [n1].
       - Next, we use [ST_P2] some number of times to reduce [t2]
         to a normal form, which must again be a term of the form [C
         n2] for some [n2].
       - Finally, we use [ST_PCC] one time to reduce [P (C
         n1) (C n2)] to [C (n1 + n2)]. *)

(** FULL: To formalize this intuition, you'll need to use the congruence
    lemmas from above (you might want to review them now, so that
    you'll be able to recognize when they are useful), plus some basic
    properties of [-->*] (that it is reflexive, transitive, and
    includes [-->]). *)

(* TERSE: FOLD *)
Proof.
  (* ADMITTED *)
  intros t n HE.
  induction HE.
  - (* E_C *)
    apply multi_refl.
  - (* E_P *)
    assert (P t1 t2 -->* P (C n1) t2) as HS1.
    { apply multistep_congr_1. assumption. }
    assert (P (C n1) t2 -->* P (C n1) (C n2)) as HS2.
    { apply multistep_congr_2.
      - apply v_C.
      - assumption. }
    assert (P (C n1) (C n2) -->* C (n1 + n2)) as HS3.
    { eapply multi_step.
      - apply ST_PCC.
      - apply multi_refl. }
    eapply multi_trans. { apply HS1. }
    eapply multi_trans. { apply HS2. }
    apply HS3.
Qed.
(* SOONER: Why not do it a bit more automated?
      intros. induction H. constructor.
      eapply multistep_congr_1 in IHeval1.
      eapply multistep_congr_2 in IHeval2.
      eapply multi_trans.
      eauto.
      eapply multi_trans.
      eauto.
      eapply multi_step. constructor. constructor. constructor.
  Or indeed a lot more automated, by putting most of this in the hint db? *)
(* /ADMITTED *)
(* TERSE: /FOLD *)
(* FULL *)
(** [] *)
(* /FULL *)

(* FULL *)
(* EX3AM? (eval__multistep_inf) *)
(** Write a detailed informal version of the proof of [eval__multistep].

(* SOLUTION *)
   _Theorem_: forall [t] [n], if [t ==> n] then [t -->* C n].

   _Proof_: By induction on a derivation of [t ==> n].

   - Suppose the final rule used to show [t ==> n] is [E_C].  Then
     [t = C n].  We must show [multistep (C n) (C n)].  This holds by
     [multi_refl].

   - Suppose the final rule used to show [t ==> n] is [E_P].  Then
     [t = P t1 t2], and we know that [t1 ==> C n1] and [t2 ==> C n2]
     for some [n1] and [n2], with [n = n1 + n2].  The IH tells us that
     [t1 -->* C n1] and [t2 -->* C n2].  We must show that
     [P t1 t2 -->* C (n1 + n2)].

     First, notice that
[[
       P t1 t2 -->* P (C n1) t2
]]
     by [multistep_congr_1] and the [multistep] derivation for
     [t1].  Observing that [C n1] is a value, we also
     notice
[[
       P (C n1) t2 -->*
       P (C n1) (C n2)
]]
     by [multistep_congr_2] and the [multistep] derivation for
     [t2].  It's also easy to see by [ST_PCC] that
[[
       P (C n1) (C n2) -->
       C (n1 + n2)
]]
     and so, by [multi_step] and [multi_refl], that the same is true for
     [-->*].  We can now use transitivity of [-->*] to stitch these
     derivations, proving
[[
       P t1 t2 -->* C (n1 + n2)
]]
(* /SOLUTION *)
*)

(* GRADE_MANUAL 3: eval__multistep_inf *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)
(** For the other direction, we need one lemma, which establishes a
    relation between single-step reduction and big-step evaluation. *)

(* FULL *)
(* EX3 (step__eval) *)
(* /FULL *)
Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t  ==> n.
(* TERSE: FOLD *)
Proof.
  intros t t' n Hs. generalize dependent n.
  (* ADMITTED *)
  induction Hs; intros n HE; inversion HE; subst.
  - (* ST_PCC *)
    apply E_P; apply E_C.
  - (* ST_P1 *)
    apply E_P.
    + apply IHHs. assumption.
    + assumption.
  - (* ST_P2 *)
    apply E_P.
    + assumption.
    + apply IHHs. assumption. Qed.
(* /ADMITTED *)
(* TERSE: /FOLD *)
(* FULL *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)

(** The fact that small-step reduction implies big-step evaluation is now
    straightforward to prove.

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)

(** FULL: Make sure you understand the statement before you start to
    work on the proof.  *)

(* FULL *)
(* EX3 (multistep__eval) *)
(* /FULL *)
Theorem multistep__eval : forall t t',
  normal_form_of step t t' -> exists n, t' = C n /\ t ==> n.
(* TERSE: FOLD *)
Proof.
  (* ADMITTED *)
  intros t t' Hnorm.
  unfold normal_form_of in Hnorm.
  destruct Hnorm as [Hs Hnf].
  (* t' is a normal form -> t' = C n for some n *)
  rewrite nf_same_as_value in Hnf.
  inversion Hnf as [n H]. clear Hnf.
  exists n. split.
  - reflexivity.
  - induction Hs; subst.
    + (* multi_refl *)
      apply E_C.
    + (* multi_step *)
      eapply step__eval. { eassumption. }
      apply IHHs. reflexivity.
Qed.
(* /ADMITTED *)
(* TERSE: /FOLD *)
(* FULL *)
(** [] *)
(* /FULL *)

(* LATER: MRC: I would have thought this is how to state and prove
   the theorem:

Theorem multistep__eval' : forall t n, t -->* (C n) -> t ==> n.
Proof.
  intros t n Hsteps. remember (C n) as HC.  induction Hsteps; subst.
  - (* multi_refl *) constructor.
  - (* multi_step *) apply step__eval with (t':=y). assumption.  apply
    IHHsteps. reflexivity.
Qed.

   MRC: It's simpler to prove this version of the theorem---no
   reasoning about normal forms is needed---and the statement itself
   is now clearly the converse of eval__multistep.  So you could now
   get a corollary stating an equivalence between big and small step
   semantics:

Corollary eval_equiv_multistep : forall t n, t ==> n <-> t -->* (C n).
Proof.
  split. apply eval__multistep. apply multistep__eval'.
Qed.

   MRC: And that seems to finish the subsection on a much stronger
   note.

   BCP 10/18: The new proof is attractively short, but I'm not 100%
   convinced that this is what we really want to show.  (It assumes
   that all normal forms have the shape (C n), no?)

   LY: The formulation as an equivalence looks nice, but it needs to
   be paired with the result that every normal form is a (C n),
   which is indeed proved earlier (nf_is_value), but that point
   seems too subtle to make for this course.
*)

(* FULL *)
(* ########################################################### *)
(** ** Additional Exercises *)

(* EX3? (interp_tm) *)
(** Remember that we also defined big-step evaluation of terms as a
    function [evalF].  Prove that it is equivalent to the existing
    semantics.  (Hint: we just proved that [eval] and [multistep] are
    equivalent, so logically it doesn't matter which you choose.
    One will be easier than the other, though!) *)

Theorem evalF_eval : forall t n,
  evalF t = n <-> t ==> n.
Proof.
  (* ADMITTED *)
  split; generalize dependent n.
  - (* -> *)
    induction t; intros n' Hi.
    + (* C case *)
      simpl in Hi. subst. apply E_C.
    + (* P case *)
      simpl in Hi.
      rewrite <- Hi.
      eapply E_P.
      * apply IHt1; reflexivity.
      * apply IHt2; reflexivity.
  - (* <- *)
    induction t; intros n' HE;
       inversion HE; subst.
    + (* C case *)
      reflexivity.
    + (* P case *)
      simpl.
      rewrite <- (IHt1 n1 H1).
      rewrite <- (IHt2 n2 H3).
      reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)

(** We've considered arithmetic and conditional expressions
    separately.  This exercise explores how the two interact. *)
Module Combined.

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n)
  | v_tru : value tru
  | v_fls : value fls.

(* HIDEFROMHTML *)
Reserved Notation " t '-->' t' " (at level 40).
(* /HIDEFROMHTML *)

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').


(** Earlier, we separately proved for both plus- and if-expressions...

    - that the step relation was deterministic, and

    - a strong progress lemma, stating that every term is either a
      value or can take a step.

    Formally prove or disprove these two properties for the combined
    language. *)

(* EX3 (combined_step_deterministic) *)
Theorem combined_step_deterministic: (deterministic step) \/ ~ (deterministic step).
Proof.
  (* ADMITTED *)
  left.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros; inversion Hy2; subst;
  try (solve_by_inverts 2); try reflexivity.
  - apply IHHy1 in H2. rewrite H2. reflexivity.
  - apply IHHy1 in H4. rewrite H4. reflexivity.
  - apply IHHy1 in H3. rewrite H3. reflexivity.
Qed.
(* /ADMITTED *)

(** [] *)

(* EX3 (combined_strong_progress) *)
Theorem combined_strong_progress :
  (forall t, value t \/ (exists t', t --> t'))
  \/ ~ (forall t, value t \/ (exists t', t --> t')).
Proof.
  (* ADMITTED *)
  right.
  intros C.
  remember (P tru tru) as t.
  assert (value t \/ (exists t', t --> t')) by apply C.
  inversion H as [Hv | [t' Hs] ]; subst.
  - (* t is a value *)
    inversion Hv.
  - (* t takes a step *)
    inversion Hs.
    + inversion H3.
    + inversion H4.
Qed.
(* /ADMITTED *)
(** [] *)

End Combined.

(* HIDE *)

(* ---------------------------------------------------------------------- *)
(* ANOTHER PROBLEM...
Suppose we extend the language of question \ref{progress} with a new
primitive @flip t@ that can step, nondeterministically, to either @0@ or
@t@.  So, for example,
#*P (tflip 1) (C 1)
normalizes (in multiple steps) to either @C 1@ or @C 2@, and
#*P (tflip 3) (tflip 4)
normalizes to @C 0@, @C 3@, @C 4@, or @C 7@.

We begin by extending the syntax of terms:
#{*}
Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | tflip : tm -> tm.
#{@}

\begin{enumerate}
\item What rule or rules do we need to add to the definition of the @step@
relation from question \ref{progress} to formalize this behavior?

\finish{Answer needed (it's a bit tricky -- there are different ways,
  depending on the order of evaluation)}

\item What are the possible normal forms of @tflip (tflip (tflip 1))@?

\finish{@C 0@ and @C 1@}

\item Is @P (tflip 1) (tflip 1)@ more likely to normalize to @0@
or to @1@?  [Poor phrasing!]

\answer{Neither: the operational semantics talks only about the {\em
    possibility} of outcomes; there's no notion of probability.}
\end{enumerate} *)

(* ---------------------------------------------------------------------- *)
(* /HIDE *)
(* /FULL *)

(* ########################################################### *)
(** * Small-Step Imp *)

(** Now for a more serious example: a small-step version of the Imp
    operational semantics. *)

(** TERSE: *** *)
(** FULL: The small-step reduction relations for arithmetic and
    boolean expressions are straightforward extensions of the tiny
    language we've been working up to now.  To make them easier to
    read, we introduce the symbolic notations [-->a] and [-->b] for
    the arithmetic and boolean step relations. *)

(* LATER: Robert Rand: aval looks enough like "eval" that I'd
   recommend changing it.  BCP 19: To what? RNR: a_val or nval? *)

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

(** FULL: We are not actually going to bother to define boolean
    values, since they aren't needed in the definition of [-->b]
    below (why?), though they might be if our language were a bit
    more complicated (why?). *)

(** TERSE: *** Small-step evaluation relation for arithmetic expressions *)
(* INSTRUCTORS: Warn students about the notational confusion with
   rules AS_P, etc. *)
(* HIDE: CH: Not sure whether this was covered by the warning above,
   but there was a lot of notational confusion happening here starting
   with [st i] not being an arithmetic expression. The confusion was
   so bad it was not clear from the informal listing below what was
   the type of the thing after the [-->] symbol, and the informal
   definition is the only thing that we show on the slides. I added
   explicit ANum constructors instead of hidden coercions, since I
   think that actually helps understanding and matching this to the
   definition of [aval] and the previous definition of step for [tm]. *)

(* HIDE: CH: Another issue here that I didn't know how to explain well
   in class is that [astep] and [bstep] don't have the type of a
   binary [relation] we introduced and heavily discussed above. All I
   could tell students is no worries, all the work above wasn't
   completely useless, since [cstep] below will match the general
   definitions above. So it feels that informally we should start with
   [cstep] in class? *)

(** TERSE:[[[
                             ---------------------                     (AS_Id)
                             i / st --> ANum (st i)

                              a1 / st --> a1'
                         -------------------------                   (AS_P1)
                         a1 + a2 / st --> a1' + a2

                        aval v1       a2 / st --> a2'
                    -------------------------------------            (AS_P2)
                          v1 + a2 / st --> v1 + a2'

                        -------------------------------               (AS_P)
                        v1 + v2 / st --> ANum (v1 + v2)

                              a1 / st --> a1'
                          -------------------------                 (AS_Minus1)
                          a1 - a2 / st --> a1' - a2

                        aval v1       a2 / st --> a2'
                        ----------------------------                (AS_Minus2)
                           v1 - a2 / st --> v1 - a2'

                        -------------------------------              (AS_Minus)
                        v1 - v2 / st --> ANum (v1 - v2)

                              a1 / st --> a1'
                          -------------------------                  (AS_Mult1)
                          a1 * a2 / st --> a1' * a2

                        aval v1       a2 / st --> a2'
                        ----------------------------                 (AS_Mult2)
                           v1 * a2 / st --> v1 * a2'

                        -------------------------------               (AS_Mult)
                        v1 * v2 / st --> ANum (v1 * v2)
]]]
*)

(* INSTRUCTORS: the associativity is a red herring: it is only here in order not
   to conflict with the standard library's notation for division(?) *)
(* HIDEFROMHTML *)
Reserved Notation " a '/' st '-->a' a' "
                  (at level 40, st at next level, left associativity).
(* /HIDEFROMHTML *)
(* TERSE: HIDEFROMHTML *)
(* LATER: change to (state * aexp) -> aexp (and similarly for bools).
   BCP (11/16): I've forgotten why we thought we needed to do this.
   :-| But since the difference are mostly hidden behind notations, I
   also wonder how important it is... *)
(* HIDE: ORI: 05/20: I moved the state to be
   a parameter, which I think is a better practice -
   it should give a better induction principle *)
Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      i / st -->a ANum (st i)
  | AS_P1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 + a2 }> / st -->a <{ a1' + a2 }>
  | AS_P2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 + a2 }>  / st -->a <{ v1 + a2' }>
  | AS_P : forall (v1 v2 : nat),
      <{ v1 + v2 }> / st -->a ANum (v1 + v2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 - a2 }> / st -->a <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 - a2 }>  / st -->a <{ v1 - a2' }>
  | AS_Minus : forall (v1 v2 : nat),
      <{ v1 - v2 }> / st -->a ANum (v1 - v2)
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 * a2 }> / st -->a <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 * a2 }>  / st -->a <{ v1 * a2' }>
  | AS_Mult : forall (v1 v2 : nat),
      <{ v1 * v2 }> / st -->a ANum (v1 * v2)

    where " a '/' st '-->a' a' " := (astep st a a').
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** Small-step evaluation relation for boolean expressions *)
(** TERSE:[[[
                          a1 / st --> a1'
                     -------------------------                     (BS_Eq1)
                     a1 = a2 / st --> a1' = a2

                    aval v1       a2 / st --> a2'
                    -----------------------------                  (BS_Eq2)
                      v1 = a2 / st --> v1 = a2'

      -------------------------------------------------------      (BS_Eq)
      v1 = v2 / st --> (if (v1 =? v2) then BTrue else BFalse)

                            a1 / st --> a1'
                      ---------------------------                  (BS_LtEq1)
                      a1 <= a2 / st --> a1' <= a2

                    aval v1       a2 / st --> a2'
                   ------------------------------                  (BS_LtEq2)
                    v1 <= a2 / st --> v1 <= a2'

      ---------------------------------------------------------    (BS_LtEq)
      v1 <= v2 / st --> (if (v1 <=? v2) then BTrue else BFalse)

                           b1 / st --> b1'
                          -----------------                        (BS_NotStep)
                          ~b1 / st --> ~b1'

                        ---------------------                      (BS_NotTrue)
                        ~ true / st --> false

                        ---------------------                      (BS_NotFalse)
                        ~ false / st --> true

                            b1 / st --> b1'
                      ---------------------------                  (BS_AndStep)
                      b1 && b2 / st --> b1' && b2

                           b2 / st --> b2'
                    -------------------------------                (BS_AndTrueStep)
                    true && b2 / st --> true && b2'

                      --------------------------                   (BS_AndFalse)
                      false && b2 / st --> false

                      --------------------------                   (BS_AndTrueTrue)
                      true && true / st --> true

                     ----------------------------                  (BS_AndTrueFalse)
                     true && false / st --> false
]]]
*)
(* HIDEFROMHTML *)
Reserved Notation " b '/' st '-->b' b' "
                  (at level 40, st at next level, left associativity).
(* /HIDEFROMHTML *)
(* TERSE: HIDEFROMHTML *)
Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 = a2 }> / st -->b <{ a1' = a2 }>
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 = a2 }> / st -->b <{ v1 = a2' }>
| BS_Eq : forall (v1 v2 : nat),
    <{ v1 = v2 }> / st -->b
    (if (v1 =? v2) then BTrue else BFalse)
| BS_LtEq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 <= a2 }> / st -->b <{ a1' <= a2 }>
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 <= a2 }> / st -->b <{ v1 <= a2' }>
| BS_LtEq : forall (v1 v2 : nat),
    <{ v1 <= v2 }> / st -->b
    (if (v1 <=? v2) then BTrue else BFalse)
| BS_NotStep : forall b1 b1',
    b1 / st -->b b1' ->
    <{ ~ b1 }> / st -->b <{ ~ b1' }>
| BS_NotTrue  : <{ ~ true }> / st  -->b <{ false }>
| BS_NotFalse : <{ ~ false }> / st -->b <{ true }>
| BS_AndStep : forall b1 b1' b2,
    b1 / st -->b b1' ->
    <{ b1 && b2 }> / st -->b <{ b1' && b2 }>
| BS_AndTrueStep : forall b2 b2',
    b2 / st -->b b2' ->
    <{ true && b2 }> / st -->b <{ true && b2' }>
| BS_AndFalse : forall b2,
    <{ false && b2 }> / st -->b <{ false }>
| BS_AndTrueTrue  : <{ true && true  }> / st -->b <{ true }>
| BS_AndTrueFalse : <{ true && false }> / st -->b <{ false }>

where " b '/' st '-->b' b' " := (bstep st b b').
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)

(** The semantics of commands is the interesting part.  We need two
    small tricks to make it work:

       - We use [skip] as a "command value" -- i.e., a command that
         has reached a normal form.

            - An assignment command reduces to [skip] (and an updated
              state).

            - The sequencing command waits until its left-hand
              subcommand has reduced to [skip], then throws it away so
              that reduction can continue with the right-hand
              subcommand.

       - We reduce a [while] command a single step by transforming it
         into a conditional followed by the same [while]. *)

(** FULL: (There are other ways of achieving the effect of the latter
    trick, but they all share the feature that the original [while]
    command is stashed away somewhere while a single copy of the loop body is
    being reduced.) *)

(** TERSE: *** Small-step evaluation relation for commands *)
(** TERSE:[[[
                              a1 / st --> a1'
                     ------------------------------                           (CS_AsgnStep)
                     i := a1 / st --> i := a1' / st

                   --------------------------------------                     (CS_Asgn)
                   i := n / st --> skip / (i !-> n ; st)

                           c1 / st --> c1' / st'
                     -------------------------------                          (CS_SeqStep)
                     c1 ; c2 / st --> c1' ; c2 / st'

                        --------------------------                            (CS_SeqFinish)
                        skip ; c2 / st --> c2 / st

                              b1 / st --> b1'
               ---------------------------------------------------            (CS_IfStep)
               if b1 then c1 else c2 end / st -->
                                   if b1' then c1 else c2 end / st

              ---------------------------------------------                   (CS_IfTrue)
              if true then c1 else c2 end / st --> c1 / st

              ----------------------------------------------                  (CS_IfFalse)
              if false then c1 else c2 end / st --> c2 / st

              -----------------------------------------------------------------    (CS_While)
              while b1 do c1 end / st -->
                         if b1 then (c1; while b1 do c1 end) else skip end / st
]]]
*)

(* HIDEFROMHTML *)
Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at next level, t' at next level, left associativity).
(* /HIDEFROMHTML *)
(* TERSE: HIDEFROMHTML *)
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).
(* TERSE: /HIDEFROMHTML *)

(* QUIZ *)
(** The (small-step) semantics of Imp satisfies (1) / does not satisfy (2)
    the following properties (choose 1 for Yes, 2 for No):

      - determinism

      - strong progress (remember we use [skip] as a "command value")

      - values and normal forms coincide (i.e. there are no "stuck" terms)

      - the step relation is normalizing (i.e. Imp programs are terminating)
*)
(* INSTRUCTORS: Yes for all but the last one (Imp programs can loop). *)
(* /QUIZ *)


(* HIDE *)

Definition cequiv_bad (c1 c2 : com) : Prop :=
  forall st st',
    (forall c1', multi cstep (c1, st) (c1', st') -> exists c2', multi cstep (c2, st) (c2', st'))
    /\
      (forall c2', multi cstep (c2, st) (c2', st') -> exists c1', multi cstep (c1, st) (c1', st')).

Lemma mult_while_h : forall st st' c0 c,
    c0 = <{ while true do skip end }>
    \/ c0 = <{ if true then skip; while true do skip end else skip end }>
    \/ c0 = <{ skip; while true do skip end }>
    ->
    multi cstep (c0, st) (c, st') -> st = st'.
Proof.
  intros st st' c0 c HE H.
    remember (c0, st) as X eqn:EQX.
    remember (c, st') as Y eqn:EQY.
    revert st st' c0 HE c EQX EQY.
    induction H; intros st st' c0 HE c EQX EQY; destruct x; inversion EQX; inversion EQY; subst.
  - reflexivity.
  - clear EQX H1.
    destruct HE as [HE | [HE | HE]]; subst.
    + inversion H; subst.
      inversion H0; subst; try reflexivity.
      inversion H1; subst.
      * inversion H8.
      * eapply IHmulti.
        -- right. left. reflexivity.
        -- reflexivity.
        -- reflexivity.
    + inversion H; subst.
      * inversion H6.
      * inversion H0; subst; try reflexivity.
        inversion H1; subst.
        -- inversion H7.
        -- eapply IHmulti.
           ** right.  right. reflexivity.
           ** reflexivity.
           ** reflexivity.
    + inversion H; subst.
      * inversion H5.
      * eapply IHmulti.
        -- left. reflexivity.
        -- reflexivity.
        -- reflexivity.
Qed.

Lemma multi_while : forall st st' c,
    multi cstep (<{ while true do skip end }>, st) (c, st') -> st = st'.
Proof.
  intros. eapply mult_while_h.
  2 : { apply H. }
  left. reflexivity.
Qed.

Lemma undesirable : cequiv_bad <{ skip }> <{ while true do skip end }>.
Proof.
  unfold cequiv_bad.
  intros st st'.
  split.
  - intros c1 H.
    inversion H; subst.
    + exists <{ while true do skip end }>. apply multi_refl.
    + inversion H0.
  - intros c2 H.
    assert (st = st').
    { eapply multi_while. apply H. }
    subst.
    exists <{ skip }>. apply multi_refl.
Qed.

(* ####################################### *)

(* LATER: Maybe turn this into an optional challenge problem... "Show
   that this is equivalent to the big-step presentation."  (Note that
   there are some ADMITTED bits...!)*)

Definition amultistep st := multi (astep st).
Definition bmultistep st := multi (bstep st).
Definition cmultistep    := multi cstep.
(* NOTATION: should these also get a notation (e.g. '-->a*')? *)
(* ceval -> cmultistep dir: *)

Lemma astep_cong_P1 : forall (st : state) a1 a1' a2,
  amultistep st a1 a1' ->
  amultistep st (APlus a1 a2) (APlus a1' a2).
Proof.
  intros. induction H.
  - apply multi_refl.
  - eapply multi_step. { apply AS_P1. apply H. }
    assumption.
Qed.

Lemma astep_cong_P2 : forall (st : state) a1 a2 a2',
  aval a1 ->
  amultistep st a2 a2' ->
  amultistep st (APlus a1 a2) (APlus a1 a2').
Proof.
  intros. induction H0.
  - apply multi_refl.
  - eapply multi_step. { apply AS_P2.
                         - assumption.
                         - apply H0. }
    assumption.
Qed.

Lemma aeval__amultistep : forall (st : state) (a : aexp),
 (amultistep st) a (ANum (aeval st a)).
Proof.
 intros st a. induction a; simpl;
    try apply multi_refl.

 - (* AId *) eapply multi_step.
   + apply AS_Id.
   + apply multi_refl.
 - (* APlus *)
   apply multi_trans with (APlus (ANum (aeval st a1)) a2).
   + apply astep_cong_P1. assumption.
   + apply multi_trans with (APlus (ANum (aeval st a1))
                                 (ANum (aeval st a2))).
     * apply astep_cong_P2.
       -- apply av_num.
       -- assumption.
     * eapply multi_step.
       -- apply AS_P.
       -- apply multi_refl.
 - (* AMinus *) admit.
 - (* AMult *) admit.
Admitted.

Lemma beval__bmultistep : forall (st : state) (b : bexp),
  bmultistep st b (if beval st b then <{true}> else <{false}>).
Proof.
Admitted.

Lemma cstep_cong_Asgn : forall st i a a',
  amultistep st a a' ->
  cmultistep (<{i := a}>,st) (<{i := a'}>,st).
Proof.
  intros st i a a' H.
  induction H.
  - (* multi_refl *) apply multi_refl.
  - (* multi_step *) apply multi_step with (<{i:=y}>,st).
    + apply CS_AsgnStep. assumption.
    + apply IHmulti.
Qed.

Lemma cstep_cong_Seq : forall st1 c1 st1' c1' c2,
  cmultistep (c1, st1) (c1', st1') ->
  cmultistep (<{c1;c2}>, st1) (<{c1';c2}>, st1').
Proof.
Admitted.

Lemma cstep_cong_If : forall st b b' c1 c2,
  bmultistep st b b' ->
  cmultistep (<{ if b then c1 else c2 end }>, st)
             (<{ if b' then c1 else c2 end }>, st).
Proof.
Admitted.

Theorem ceval__cmultistep : forall st c st_final,
    ceval c st st_final ->
    cmultistep (c,st) (<{skip}>, st_final).
Proof.
  intros st c st_final Hceval. induction Hceval.
  - (* E_Skip *) apply multi_refl.
  - (* E_Asgn *)
    apply multi_trans with (<{x := n}>, st).
    + apply cstep_cong_Asgn.  rewrite <- H.
      apply aeval__amultistep.
    + apply multi_step with (<{skip}>, (x !-> n ; st)).
      * apply CS_Asgn.
      * apply multi_refl.
  - (* E_Seq *)
    apply multi_trans with (<{skip;c2}>, st').
    + apply cstep_cong_Seq. assumption.
    + apply multi_step with (c2,st').
      * apply CS_SeqFinish.
      * assumption.
  - (* E_IfTrue *)
    apply multi_trans with (<{if true then c1 else c2 end}>,st).
    + assert (BTrue = if beval st b then <{true}> else <{false}>) as H1.
      { rewrite H. reflexivity. }
      rewrite H1.
      apply cstep_cong_If.
      apply beval__bmultistep.
    + apply multi_step with (c1,st).
      * apply CS_IfTrue.
      * assumption.
  - (* E_IfFalse *)
    apply multi_trans with (<{if false then c1 else c2 end}>,st).
    + assert (BFalse = if beval st b then <{true}> else <{false}>) as H1.
      { rewrite H. reflexivity. }
      rewrite H1.
      apply cstep_cong_If.
      apply beval__bmultistep.
    + apply multi_step with (c2,st).
      * apply CS_IfFalse.
      * assumption.
  - (* E_WhileFalse *)
    apply multi_step with
    (<{if b then (c; (while b do c end)) else skip end}>,st).
    + apply CS_While.
    + apply multi_trans with
    (<{if BFalse then (c; (while b do c end)) else skip end}>,st).
      * assert (BFalse = if beval st b then <{true}> else <{false}>) as H1.
        { rewrite H. reflexivity. }
        rewrite H1.
        apply cstep_cong_If.
        apply beval__bmultistep.
      * apply multi_step with (<{skip}>,st).
        -- apply CS_IfFalse.
        -- apply multi_refl.
  - (* E_WhileTrue *)
    apply multi_step with
    (<{if b then (c; (while b do c end)) else skip end}>,st).
    + apply CS_While.
    + apply multi_trans with
        (<{if true then (c; (while b do c end)) else skip end}>,st).
      * assert (BTrue = if beval st b then <{true}> else <{false}>) as H1.
        { rewrite H. reflexivity. }
        rewrite H1.
        apply cstep_cong_If.
        apply beval__bmultistep.
      * apply multi_step with (<{c; while b do c end}>,st).
        -- apply CS_IfTrue.
        -- apply multi_trans with (<{skip; while b do c end}>,st').
           ++ apply cstep_cong_Seq.
              assumption.
           ++ apply multi_step with (<{while b do c end}>,st').
              ** apply CS_SeqFinish.
              ** assumption.
Qed.

(* cmultistep -> ceval dir: *)
Lemma aeval_step : forall st a a',
  astep st a a' ->
  aeval st a = aeval st a'.
Proof.
  intros st a a' H.
  (induction H); simpl;
    try rewrite IHastep;
    reflexivity.
Qed.

Lemma beval_step : forall st b b',
  bstep st b b' ->
  beval st b = beval st b'.
Proof.
  intros st b b' H.
  induction H; simpl;
      try rewrite IHbstep;
      try reflexivity.
  - rewrite (aeval_step _ _ _ H). reflexivity.
  - rewrite (aeval_step _ _ _ H0). reflexivity.
  - destruct (v1 =? v2); reflexivity.
  - rewrite (aeval_step _ _ _ H). reflexivity.
  - rewrite (aeval_step _ _ _ H0). reflexivity.
  - destruct (v1 <=? v2); reflexivity.
Qed.

Lemma ceval_step : forall stc stc',
  cstep stc stc' ->
  forall st_final,
    let (c,st) := stc in
    let (c',st') := stc' in
    ceval c' st' st_final ->
    ceval c st st_final.
Proof.
  intros stc stc' H.
  induction H; intros st_final Heval.
  - inversion Heval; subst. rewrite <- (aeval_step _ _ _ H). apply E_Asgn. reflexivity.
  - inversion Heval; subst. apply E_Asgn. reflexivity.
  - inversion Heval; subst. apply IHcstep in H2. apply E_Seq with (st'0); assumption.
  - apply E_Seq with st.
    + apply E_Skip.
    + assumption.
  - inversion Heval; subst.
    + apply E_IfTrue.
      * rewrite (beval_step _ _ _ H). assumption.
      * assumption.
    + apply E_IfFalse.
      * rewrite (beval_step _ _ _ H). assumption.
      * assumption.
  - apply E_IfTrue.
    + reflexivity.
    + assumption.
  - apply E_IfFalse.
    + reflexivity.
    + assumption.
  - inversion Heval; subst; inversion H5; subst.
    + apply E_WhileTrue with st'; assumption.
    + apply E_WhileFalse. assumption.
Qed.

Lemma ceval_multistep : forall stc stc',
  cmultistep stc stc' ->
  forall st_final,
    let (c,st) := stc in
    let (c',st') := stc' in
      ceval c' st' st_final ->
      ceval c st st_final.
Proof.
  intros stc stc' H.
  induction H as [ [st c] | [st c] [st' c'] [st'' c''] ].
  - (* multi_refl *)
    intros; assumption.
  - (* multi_step *)
    intros.
    apply (ceval_step (st,c) (st',c')).
    + assumption.
    + apply IHmulti. assumption.
Qed.

Theorem cmultistep__ceval : forall st c st',
  cmultistep (c,st) (<{skip}>,st') ->
  ceval c st st'.
Proof.
  intros.
  apply (ceval_multistep (c,st) (<{skip}>,st')).
  - assumption.
  - apply E_Skip.
Qed.
(* /HIDE *)
(* LATER: A nice challenge problem: Add a C-style assignment
   expression.  This requires changing the type of the astep relation.
   Having done this, we can really distinguish between different
   evaluation orders, and between deterministic and nondeterministic
   evaluation definitions. *)

(* HIDE *)
(* ###################################################### *)
(* In progress: BCP's CCS formalization *)

Module CCS.

Definition chan := nat.

Inductive proc : Type :=
  | p_skip     : proc
  | p_send     : chan -> proc -> proc
  | p_recv     : chan -> proc -> proc
  | p_par      : proc -> proc -> proc
  | p_restrict : chan -> proc -> proc
  | p_repl     : proc -> proc.

Inductive action : Type :=
  | a_input    : chan -> action
  | a_output   : chan -> action
  | a_internal : action.

Inductive cstep : proc -> proc -> action -> Prop :=
  | ST_send : forall c p,
      cstep (p_send c p) p (a_output c)
(* STOPPED HERE *)
.

End CCS.
(* /HIDE *)

(* ########################################################### *)
(** * Concurrent Imp *)

(** FULL: Finally, to show the power of this definitional style, let's
    enrich Imp with a new form of command that runs two subcommands in
    parallel and terminates when both have terminated.  To reflect the
    unpredictability of scheduling, the actions of the subcommands may
    be interleaved in any order, but they share the same memory and
    can communicate by reading and writing the same variables. *)
(** TERSE: Finally, let's define a _concurrent_ extension of Imp, to
    show off the power of our new tools... *)

(** TERSE: *** *)

(** For example:
     - This program sets [X] to [0] in one thread and [1] in another,
       leaving it set to either [0] or [1] at the end:
[[
          X := 0 || X := 1
]]
     - This one leaves [X] set to one of [0], [1], [2], or [3] at the
       end:
[[
          X := 0; (X := X+2 || X := X+1 || X := 0)
]]
*)

(** TERSE: *** *)

(* TERSE: HIDEFROMHTML *)

Module CImp.
(* TERSE: /HIDEFROMHTML *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.         (* <--- NEW: c1||c2 *)

(* TERSE: HIDEFROMHTML *)
Notation "x '||' y" := (CPar x y)
  (in custom com at level 100, right associativity,
    format "'[v'   x '/' '||' '/ '  y ']'").
(* INSTRUCTORS: Copy of template com *)
Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99,
    format "'[v' 'while'  x  'do' '/  ' y '/' 'end' ']'") : com_scope.

(* TERSE: /HIDEFROMHTML *)

(* HIDE *)

(* NOTATION: this is not great, but
   1) Such programs never show up in the chapter
   2) It is still readable
   May be possible to fix this using recursive notations, but is it really
   worth it?
  *)

Check
  <{
      while (Y = 0) do X := X + 1 end
    ||
      Y := 1
    ||
      while (Y = 0) do X := X + 1 end
   }>.
(* /HIDE *)

(** TERSE: *** New small-step evaluation relation for commands *)

(** TERSE: Same rules as before, plus:
[[[

                           c1 / st --> c1' / st'
                     ---------------------------------                       (CS_Par1)
                     c1 || c2 / st --> c1' || c2 / st'

                           c2 / st --> c2' / st'
                     ---------------------------------                       (CS_Par2)
                     c1 || c2 / st --> c1 || c2' / st'


                     --------------------------------                        (CS_ParDone)
                     skip || skip / st --> skip / st
]]]
*)
(* TERSE: HIDEFROMHTML *)
Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part: *)
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      <{ c1 || c2 }> / st --> <{ c1' || c2 }> / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      <{ c1 || c2 }> / st --> <{ c1 || c2' }> / st'
  | CS_ParDone : forall st,
      <{ skip || skip }> / st --> <{ skip }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at next level, t' at next level, left associativity).
(* TERSE: /HIDEFROMHTML *)
(* NOTATION: NDS'25
   It is unclear to me if we should also introduce line-breaks in these
   notations. IMO the lack of line-breaks is not really an issue in this
   file, so I did not add any.
   *)

(* HIDE: CH: The first quizzes below are very helpful, in particular
   for illustrating that in this language sequential composition [;]
   acts as a barrier by waiting for the threads spawned by the first
   command to finish. May want to also make this point in the FULL
   version. *)

(* QUIZ *)
(** Which state _cannot_ be obtained as a result of executing the
    following program (from any starting state)?
[[
       (Y := 1 || Y := 2);
       X := Y
]]

    (A) [Y=0] and [X=0]

    (B) [Y=1] and [X=1]

    (C) [Y=2] and [X=2]

    (D) None of the above

*)
(* /QUIZ *)
(* INSTRUCTORS: (A) is the (obvious) answer. *)
(* QUIZ *)
(** Which state(s) _cannot_ be obtained as a result of executing the
    following program (from any starting state)?
[[
       (Y := 1 || Y := Y + 1);
       X := Y
]]

    (A) [Y=1] and [X=1]

    (B) [Y=0] and [X=1]

    (C) [Y=2] and [X=2]

    (D) [Y=n] and [X=n] for any [n >= 3]

    (E) B and D above

    (6) None of the above

*)
(* /QUIZ *)
(* INSTRUCTORS: (B) is the answer.
   (D) is possible. Assuming Y is originally larger than 2, we can
   reduce Y + 1 to a value n in the right branch before evaluating
   Y := 1. We can then finish evaluating Y := n. *)
(* QUIZ *)
(** How about this one?
[[
      ( Y := 0; X := Y + 1 )
   ||
      ( Y := Y + 1; X := 1 )
]]

    (A) [Y=0] and [X=1]

    (B) [Y=1] and [X=1]

    (C) [Y=0] and [X=0]

    (D) [Y=4] and [X=1]

    (E) None of the above

*)
(* /QUIZ *)
(* INSTRUCTORS: (3) is the answer. *)
(** TERSE: *** *)
(** Among the many interesting properties of this language is the fact
    that the following program can terminate with the variable [X] set
    to any value. *)

Definition par_loop : com :=
  <{
      Y := 1
    ||
      while (Y = 0) do X := X + 1 end
   }>.

(* FULL *)
(** In particular, it can terminate with [X] set to [0]: *)

Example par_loop_example_0:
  exists st',
       par_loop / empty_st  -->* <{skip}> / st'
    /\ st' X = 0.
(* FOLD *)
Proof.
  unfold par_loop.
  eexists. split.
  - eapply multi_step.
    + apply CS_Par1.  apply CS_Asgn.
    + eapply multi_step.
      * apply CS_Par2. apply CS_While.
      * eapply multi_step.
        -- apply CS_Par2. apply CS_IfStep.
           apply BS_Eq1. apply AS_Id.
        -- eapply multi_step.
           ++ apply CS_Par2. apply CS_IfStep.
              apply BS_Eq.
           ++ simpl. eapply multi_step.
              ** apply CS_Par2. apply CS_IfFalse.
              ** eapply multi_step.
               --- apply CS_ParDone.
               --- eapply multi_refl.
  - reflexivity.
Qed.
(* /FOLD *)

(** It can also terminate with [X] set to [2]: *)

(** The following proofs are particularly "deep" -- they require
    following the small step semantics in a particular strategy to
    exhibit the desired behavior. For that reason, they are a bit
    awkward to write with "forced bullets". Nevertheless, we keep them
    because they emphasize that the witness for an evaluation by
    small-step semantics has a size that is proportional to the number
    of steps taken.  It would be an interesting exercise to write Rocq
    tactics that can help automate the construction of such proofs,
    but such a tactic would need to "search" among the many
    possibilities. *)

Example par_loop_example_2:
  exists st',
       par_loop / empty_st -->* <{skip}> / st'
    /\ st' X = 2.
(* FOLD *)
Proof.
  unfold par_loop.
  eexists. split.
  - eapply multi_step.
    + apply CS_Par2. apply CS_While.
    + eapply multi_step.
      * apply CS_Par2. apply CS_IfStep.
        apply BS_Eq1. apply AS_Id.
      * eapply multi_step.
        -- apply CS_Par2. apply CS_IfStep.
           apply BS_Eq.
        -- simpl. eapply multi_step.
           ++ apply CS_Par2. apply CS_IfTrue.
           ++ eapply multi_step.
              ** apply CS_Par2. apply CS_SeqStep.
                 apply CS_AsgnStep. apply AS_P1. apply AS_Id.
              ** eapply multi_step.
                 --- apply CS_Par2. apply CS_SeqStep.
                     apply CS_AsgnStep. apply AS_P.
                 --- eapply multi_step.
                     +++ apply CS_Par2. apply CS_SeqStep.
                         apply CS_Asgn.
                     +++ eapply multi_step.
                         *** apply CS_Par2. apply CS_SeqFinish.
                         *** eapply multi_step.
                             ---- apply CS_Par2. apply CS_While.
                             ---- eapply multi_step.
                                  ++++ apply CS_Par2. apply CS_IfStep.
                                       apply BS_Eq1. apply AS_Id.
                                  ++++ eapply multi_step.
                                       **** apply CS_Par2. apply CS_IfStep.
                                            apply BS_Eq.
                                       **** simpl.
                                            eapply multi_step.
                                            ----- apply CS_Par2. apply CS_IfTrue.
                                            ----- eapply multi_step.
                                            +++++ apply CS_Par2. apply CS_SeqStep.
                                            apply CS_AsgnStep. apply AS_P1. apply AS_Id.
                                            +++++ eapply multi_step.
                                            ***** apply CS_Par2. apply CS_SeqStep.
                                            apply CS_AsgnStep. apply AS_P.
                                            ***** eapply multi_step.
                                            ------ apply CS_Par2. apply CS_SeqStep.
                                            apply CS_Asgn.
                                            ------ eapply multi_step.
                                            ++++++ apply CS_Par1. apply CS_Asgn.
                                            ++++++ eapply multi_step.
                                            ****** apply CS_Par2. apply CS_SeqFinish.
                                            ****** eapply multi_step.
                                            ------- apply CS_Par2. apply CS_While.
                                            ------- eapply multi_step.
                                            +++++++ apply CS_Par2. apply CS_IfStep.
                                            apply BS_Eq1. apply AS_Id.
                                            +++++++ eapply multi_step.
                                            ******* apply CS_Par2. apply CS_IfStep.
                                            apply BS_Eq.
                                            ******* simpl. eapply multi_step.
                                            -------- apply CS_Par2. apply CS_IfFalse.
                                            -------- eapply multi_step.
                                            ++++++++ apply CS_ParDone.
                                            ++++++++ eapply multi_refl.
  - reflexivity. Qed.
(* /FOLD *)

(** More generally... *)

(* EX3? (par_body_n__Sn) *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st -->* par_loop / (X !-> S n ; st).
Proof.
  (* ADMITTED *)
  intros n st [HX HY].
  eapply multi_step.
  - apply CS_Par2. apply CS_While.
  - eapply multi_step.
    + apply CS_Par2. apply CS_IfStep.
      apply BS_Eq1. apply AS_Id.
    + rewrite HY. eapply multi_step.
      * apply CS_Par2. apply CS_IfStep.
        apply BS_Eq.
      * eapply multi_step.
        -- apply CS_Par2. apply CS_IfTrue.
        -- eapply multi_step.
           ++ apply CS_Par2. apply CS_SeqStep.
              apply CS_AsgnStep. apply AS_P1. apply AS_Id.
           ++ rewrite HX. eapply multi_step.
              ** apply CS_Par2. apply CS_SeqStep.
                 apply CS_AsgnStep. apply AS_P.
              ** eapply multi_step.
                 --- apply CS_Par2. apply CS_SeqStep.
                     apply CS_Asgn.
                 --- replace (n+1) with (S n); try lia.
                     eapply multi_step.
                     +++ apply CS_Par2. apply CS_SeqFinish.
                     +++ apply multi_refl. Qed.
(* /ADMITTED *)
(** [] *)

(* EX3? (par_body_n) *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st -->*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  (* ADMITTED *)
  intros n st [HX HY]. induction n as [| n'].
  - (* n = 0 *) exists st. split.
    + apply multi_refl.
    + split; assumption.
  - (* n = S n' *)
    inversion IHn' as [st' [HStep [HX' HY'] ] ]; clear IHn'.
    exists (X !-> (S n') ; st' ). split.
    + apply multi_trans with (par_loop, st').
      * assumption.
      * apply par_body_n__Sn. split; assumption.
    + split.
      * reflexivity.
      * rewrite t_update_neq.
        -- assumption.
        -- intros H. discriminate.
Qed.
(* /ADMITTED *)
(** [] *)

(** ... the above loop can exit with [X] having any value
    whatsoever. *)

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_st -->*  <{skip}> / st'
    /\ st' X = n.
(* FOLD *)
Proof.
  intros n.
  destruct (par_body_n n empty_st).
  - split; reflexivity.
  - rename x into st.
  inversion H as [H' [HX HY] ]; clear H.
  exists (Y !-> 1 ; st). split.
    + eapply multi_trans with (par_loop,st).
      * apply H'.
      * eapply multi_step.
        -- apply CS_Par1. apply CS_Asgn.
        -- eapply multi_step.
           ++ apply CS_Par2. apply CS_While.
           ++ eapply multi_step.
              ** apply CS_Par2. apply CS_IfStep.
                 apply BS_Eq1. apply AS_Id.
              ** rewrite t_update_eq.
                 eapply multi_step.
                 --- apply CS_Par2. apply CS_IfStep.
                     apply BS_Eq.
                 --- simpl. eapply multi_step.
                     +++ apply CS_Par2. apply CS_IfFalse.
                     +++ eapply multi_step.
                         *** apply CS_ParDone.
                         *** apply multi_refl.
    + rewrite t_update_neq.
      * assumption.
      * intro X; inversion X.
Qed.
(* /FOLD *)

(* /FULL *)
(* TERSE: HIDEFROMHTML *)
End CImp.
(* TERSE: /HIDEFROMHTML *)

(* HIDE *)
(* AAA: sketch for possible exercise compiling CImp to Imp by
   converting par to SEQ. Looks really heavy for now, hopefully
   there's a better way of doing it... or perhaps we can split it into
   separate exercises. *)

Inductive lin : com -> CImp.com -> Prop :=
| L_Skip : lin CSkip CImp.CSkip
| L_Asgn : forall i a1, lin (CAsgn i a1) (CImp.CAsgn i a1)
| L_Seq : forall c1 c2 cc1 cc2,
            lin c1 cc1 -> lin c2 cc2 ->
            lin (CSeq c1 c2) (CImp.CSeq cc1 cc2)
| L_If : forall b1 c1 c2 cc1 cc2,
           lin c1 cc1 -> lin c2 cc2 ->
           lin (CIf b1 c1 c2) (CImp.CIf b1 cc1 cc2)
| L_While : forall b1 c1 cc,
              lin c1 cc ->
              lin (CWhile b1 c1) (CImp.CWhile b1 cc)
| L_ParSeq : forall c1 c2 cc1 cc2,
               lin c1 cc1 -> lin c2 cc2 ->
               lin (CSeq c1 c2) (CImp.CPar cc1 cc2)
| L_ParSkip : forall c1 cc,
                lin c1 cc ->
                lin c1 (CImp.CPar CImp.CSkip cc).

Theorem cimp_par_congr_l : forall cc2 p p',
                             multi CImp.cstep p p' ->
                             multi CImp.cstep (CImp.CPar (fst p) cc2, snd p)
                                              (CImp.CPar (fst p') cc2, snd p').
Proof.
  intros.
  induction H.
  - constructor.
  - eapply multi_step; eauto.
    constructor. destruct x. destruct y. auto.
Qed.

Theorem cimp_par_congr_r : forall cc1 p p',
                             multi CImp.cstep p p' ->
                             multi CImp.cstep (CImp.CPar cc1 (fst p), snd p)
                                              (CImp.CPar cc1 (fst p'), snd p').
Proof.
  intros.
  induction H.
  - constructor.
  - eapply multi_step; eauto.
    constructor. destruct x. destruct y. auto.
Qed.

Theorem cimp_seq_congr_l : forall cc2 p p',
                             multi CImp.cstep p p' ->
                             multi CImp.cstep (CImp.CSeq (fst p) cc2, snd p)
                                              (CImp.CSeq (fst p') cc2, snd p').
Proof.
  intros.
  induction H.
  - constructor.
  - eapply multi_step; eauto.
    constructor. destruct x. destruct y. auto.
Qed.

Theorem lin_skip : forall cc,
                     lin CSkip cc ->
                     forall st, multi CImp.cstep (cc, st) (CImp.CSkip, st).
Proof.
  intros cc H.
  remember CSkip as c eqn:Heqc.
  induction H; try solve [inversion Heqc]; intros.
  - apply multi_refl.
  - apply IHlin with st in Heqc. clear IHlin.
    eapply cimp_par_congr_r in Heqc.
    eapply multi_trans.
    + eauto.
    + simpl. apply multi_R. constructor.
Qed.

Theorem lin_step : forall c cc,
                     lin c cc ->
                     forall st st' c',
                       cstep (c, st) (c', st') ->
                       exists cc', multi CImp.cstep (cc, st) (cc', st') /\
                                   lin c' cc'.
Proof.
  intros c cc H.
  induction H.
  - (* Skip *) intros. inversion H.
  - (* Asgn *)
    intros.
    inversion H; subst; clear H;
    eexists; split; try apply multi_R; try econstructor; eauto.
  - (* Seq *)
    intros.
    inversion H1; subst; clear H1.
    + (* c1 steps *)
      apply IHlin1 in H3.
      clear H IHlin1 IHlin2.
      destruct H3 as [cc1' [H1 H2] ].
      eapply cimp_seq_congr_l in H1. simpl in H1.
      eexists. split; eauto.
      constructor; auto.
    + (* c1 = skip *)
      eapply lin_skip in H.
      eexists.
      split; eauto.
      eapply multi_trans.
      * eapply cimp_seq_congr_l in H. simpl in H.
        eauto.
      * apply multi_R. constructor.
  - (* If *)
    intros.
    inversion H1; subst; clear H1; eexists; split;
    try apply multi_R; eauto; constructor; eauto.
  - (* While *)
    intros.
    inversion H0; subst; clear H0.
    eexists.
    split; try apply multi_R; repeat (constructor; eauto).
  - (* ParSeq *)
    intros.
    inversion H1; subst; clear H1.
    + (* c1 steps *)
      apply IHlin1 in H3.
      clear H IHlin1 IHlin2.
      destruct H3 as [cc1' [H1 H2] ].
      eapply cimp_par_congr_l in H1. simpl in H1.
      eexists. split; eauto.
      constructor; auto.
    + (* c1 = skip *)
      eapply lin_skip in H.
      eexists. apply L_ParSkip in H0.
      split; eauto.
      eapply cimp_par_congr_l in H. simpl in H.
      eauto.
  - (* ParSkip *)
    intros.
    apply IHlin in H0. clear IHlin.
    destruct H0 as [cc' [H1 H2] ].
    eexists.
    eapply L_ParSkip in H2.
    split; eauto.
    eapply cimp_par_congr_r in H1. simpl in H1.
    eauto.
Qed.

Theorem lin_multistep : forall p p' cc,
                          multi cstep p p' ->
                          lin (fst p) cc ->
                          exists cc', multi CImp.cstep (cc, snd p) (cc', snd p').
Proof.
  intros p p' cc H Hlin.
  generalize dependent cc.
  induction H.
  - eexists. constructor.
  - destruct x as [c st]. destruct y as [c' st'].
    simpl in *.
    intros cc Hlin. eapply lin_step in Hlin; eauto.
    destruct Hlin as [cc' [H1 H2] ].
    apply IHmulti in H2.
    destruct H2 as [cc'' H2].
    eexists. eapply multi_trans; eauto.
Qed.

Module compile.

Fixpoint compile (c : CImp.com) : com :=
  match c with
    | CImp.CSkip => CSkip
    | CImp.CAsgn i a => CAsgn i a
    | CImp.CSeq cc1 cc2 => CSeq (compile cc1) (compile cc2)
    | CImp.CIf b cc1 cc2 => CIf b (compile cc1) (compile cc2)
    | CImp.CWhile b c => CWhile b (compile c)
    | CImp.CPar cc1 cc2 => CSeq (compile cc1) (compile cc2)
  end.

Theorem compile_lin : forall cc, lin (compile cc) cc.
Proof.
  induction cc; simpl; intros; constructor; auto.
Qed.

Theorem compile_correct : forall c' cc st st',
                            multi cstep (compile cc, st) (c', st') ->
                            exists cc', multi CImp.cstep (cc, st) (cc', st').
Proof.
  intros c' cc st st' Hstep.
  eapply lin_multistep in Hstep; simpl; try apply compile_lin.
  auto.
Qed.

End compile.
(* /HIDE *)

(* FULL *)
(* ########################################################### *)
(** * A Small-Step Stack Machine *)

(** Our last example is a small-step semantics for the stack machine
    example from the \CHAPV1{Imp} chapter of _Logical Foundations_. *)

Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step (st : state) : prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall stk n p,
    stack_step st (SPush n :: p, stk)      (p, n :: stk)
  | SS_Load : forall stk i p,
    stack_step st (SLoad i :: p, stk)      (p, st i :: stk)
  | SS_P : forall stk n m p,
    stack_step st (SPlus :: p, n::m::stk)  (p, (m+n)::stk)
  | SS_Minus : forall stk n m p,
    stack_step st (SMinus :: p, n::m::stk) (p, (m-n)::stk)
  | SS_Mult : forall stk n m p,
    stack_step st (SMult :: p, n::m::stk)  (p, (m*n)::stk).

Theorem stack_step_deterministic : forall st,
  deterministic (stack_step st).
(* FOLD *)
Proof.
  unfold deterministic. intros st x y1 y2 H1 H2.
  induction H1; inversion H2; reflexivity.
Qed.
(* /FOLD *)

Definition stack_multistep st := multi (stack_step st).

(* HIDE *)
    Definition stack_normal_form st := normal_form (stack_step st).

    Inductive stack_value : prog * stack -> Prop :=
      | VStack : forall stk, stack_value ([],stk).

    Lemma stack_value__normal_form : forall st p stk,
      stack_value (p,stk) -> stack_normal_form st (p,stk).
    (* TERSE: FOLD *)
    Proof.
      (* ADMITTED *)
      intros. inversion H; subst; clear H.
      unfold stack_normal_form, normal_form.
      intros contra.
      destruct contra as [t' H]. inversion H.
    Qed.
    (* /ADMITTED *)
    (* TERSE: /FOLD *)

    Definition stack_normal_form_of st p p' :=
      stack_multistep st p p' /\ stack_normal_form st p'.

    (* LATER: Very strange: if I remove "unfold s_execute", the following
       proof succeeds in the main directory but fails when executed in the
       "full" directory (if we un-HIDE this section)... Ah, GOT IT: this
       is because in the FULL version the body of s_execute is just admit! *)
    Theorem stack_step__execute : forall st p stk1 stk2,
      stack_multistep st (p, stk1) ([], stk2) -> s_execute st stk1 p = stk2.
    (* TERSE: FOLD *)
    Proof.
      (* ADMITTED *)
      intros. generalize dependent stk1.
      induction p as [|i p']; intros stk1 H.
      - (* p = [] *) inversion H; subst.
        + (* multi_refl *) reflexivity.
        + (* multi_step *) inversion H0.
      - (* p = i :: p' *) inversion H; subst.
        destruct i; simpl;
          try (apply IHp'; inversion H0; subst; assumption); (* Push, Load *)
          try (destruct stk1; inversion H0; destruct stk1; inversion H0;
               apply IHp'; inversion H0; subst; assumption). (* Arithmetic *)
    Qed.
    (* /ADMITTED *)
    (* TERSE: /FOLD *)

    Lemma stack_normal_form_of_step : forall st p1 p2 p2',
      stack_step st p1 p2 -> stack_normal_form_of st p2 p2' ->
        stack_normal_form_of st p1 p2'.
    (* TERSE: FOLD *)
    Proof.
      (* ADMITTED *)
      intros. inversion H0 as [H1 H2]; clear H0.
      unfold stack_normal_form_of. split.
      - (* multistep *)
        eapply multi_step; eassumption.
      - (* normal_form *)
        assumption.
    Qed.
    (* /ADMITTED *)
    (* TERSE: /FOLD *)

    Theorem execute__stack_step : forall st stk1 p stk2,
      s_execute st stk1 p = stk2 ->
      exists p' stk',
      stack_normal_form_of st (p,stk1) (p',stk') /\
        (stack_value (p',stk') -> stk' = stk2).
    (* TERSE: FOLD *)
    Proof.
      (* ADMITTED *)
      intros st stk1 p stk2 H.
      generalize dependent stk1.
      induction p as [|i p2]; intros stk1 H.
      - (* p = [] *)
        simpl in H. exists [], stk1. split.
        + unfold stack_normal_form_of. split.
          * apply multi_refl.
          * apply stack_value__normal_form. apply VStack.
        + auto.
      - (* p = i :: p2 *)
         destruct i; try (
           simpl in H; apply IHp2 in H;
           inversion H as [p2' [stk2' [H1 H2] ] ];
           exists p2'; exists stk2';
           split; [ eapply stack_normal_form_of_step;
                      [ constructor | assumption ]
                  | assumption ]);  (* Push, Load *)

           try (
           simpl in H; destruct stk1;
           [ eexists; eexists; split;
               [ split;
                 [ apply multi_refl
                 | intros contra; inversion contra as [t' H']; inversion H' ]
               | intros Hcontra; inversion Hcontra ]

           | destruct stk1;
             [ eexists; eexists; split;
               [ split;
                 [ apply multi_refl
                 | intros contra; inversion contra as [t' H']; inversion H' ]
               | intros Hcontra; inversion Hcontra ]

             | apply IHp2 in H; inversion H as [p2' [stk2' [H1 H2] ] ];
               exists p2'; exists stk2'; split;
                 [ eapply stack_normal_form_of_step;
                   [ constructor | assumption ]
                 | assumption ]
             ]
           ]).  (* Arithmetic *)
    Qed.
     (* /ADMITTED *)

(* /HIDE *)
(* EX3A (compiler_is_correct) *)
(** Remember the definition of [compile] for [aexp] given in the
    \CHAPV1{Imp} chapter of _Logical Foundations_. We want now to
    prove [s_compile] correct with respect to the stack machine.

    Copy your definition of [s_compile] from Imp here, then state
    what it means for the compiler to be correct according to the
    stack machine small step semantics, and then prove it. *)

(* ...Put your definition of s_compile here... *)

(* SOONER: BCP 25 -- this is pretty hard!  And is this even the
   most correct answer?  Seems like it should be an iff... *)
Definition compiler_is_correct_statement : Prop
  (* ADMITDEF *) :=
forall (st : state) (e : aexp),
  stack_multistep st (s_compile e, []) ([], [ aeval st e ]).
(* /ADMITDEF *)
(* QUIETSOLUTION *)

Theorem s_compile_aux : forall (e : aexp) (t: prog) (st : state) (stk1 : stack),
  stack_multistep st (s_compile e ++ t, stk1) (t, aeval st e :: stk1).
Proof.
  induction e; intros;
    try (apply multi_R; constructor);
    try (simpl; eapply multi_trans;
          [repeat (rewrite <- app_assoc); eapply IHe1 |];
           eapply multi_trans; [eapply IHe2 |]; apply multi_R; constructor).
Qed.

(* /QUIETSOLUTION *)
Theorem compiler_is_correct : compiler_is_correct_statement.
Proof.
(* ADMITTED *)
  unfold compiler_is_correct_statement.
  intros.
  rewrite <- (app_nil_r (s_compile e)).
  eapply s_compile_aux.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* ###################################################################### *)
(** * Aside: A [normalize] Tactic *)

(** FULL: When experimenting with definitions of programming languages
    in Rocq, we often want to see what a particular concrete term steps
    to -- i.e., we want to find proofs for goals of the form [t -->*
    t'], where [t] is a completely concrete term and [t'] is unknown.
    These proofs are quite tedious to do by hand.  Consider, for
    example, reducing an arithmetic expression using the small-step
    relation [astep]. *)
(** TERSE: Proofs that one expression multisteps to another can be
    tedious... *)

Example step_example1 :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  apply multi_step with (P (C 3) (C 7)).
  - apply ST_P2.
    + apply v_C.
    + apply ST_PCC.
  - apply multi_step with (C 10).
    + apply ST_PCC.
    + apply multi_refl.
Qed.

(** TERSE: *** *)

(** Proofs that one term normalizes to another must repeatedly apply
    [multi_step] until the term reaches a normal form.  Fortunately,
    the sub-proofs for the intermediate steps are simple enough that
    [auto], with appropriate hints, can solve them. *)

Hint Constructors step value : core.
Example step_example1' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  eapply multi_step; auto. simpl.
  eapply multi_step; auto. simpl.
  apply multi_refl.
Qed.

(** TERSE: *** *)

(** The following custom [Tactic Notation] definition captures this
    pattern.  In addition, before each step, we print out the current
    goal, so that we can follow how the term is being reduced. *)

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | simpl]);
  apply multi_refl.

(** TERSE: *** *)

(* LATER: This example is not especially enlightening -- something
   with more reduction steps, and perhaps involving commands, would be
   more interesting... *)
Example step_example1'' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  normalize.
  (* The [print_goal] in the [normalize] tactic shows
     a trace of how the expression reduced...
         (P (C 3) (P (C 3) (C 4)) -->* C 10)
         (P (C 3) (C 7) -->* C 10)
         (C 10 -->* C 10)
  *)
Qed.

(** TERSE: *** *)

(** The [normalize] tactic also provides a simple way to calculate the
    normal form of a term, by starting with a goal with an existentially
    bound variable. *)

Example step_example1''' : exists e',
  (P (C 3) (P (C 3) (C 4)))
  -->* e'.
Proof.
  eexists. normalize.
Qed.
(** This time, the trace is:
[[
       (P (C 3) (P (C 3) (C 4)) -->* ?e')
       (P (C 3) (C 7) -->* ?e')
       (C 10 -->* ?e')
]]
   where [?e'] is the variable ``guessed'' by eapply. *)

(* FULL *)
(* EX1 (normalize_ex) *)
Theorem normalize_ex : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
  (* ADMITTED *)
  eexists. split.
  - normalize.
  - constructor.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX1? (normalize_ex') *)
(** For comparison, prove it using [apply] instead of [eapply]. *)

Theorem normalize_ex' : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
  (* ADMITTED *)
  exists (C 6). split.
  - normalize.
  - constructor.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(\\*\\* \\*+\\|(\\* EX[1-5]..." *)
(* End: *)
(* mode: outline-minor *)
(* outline-heading-end-regexp: "\n" *)
(* /HIDE *)
