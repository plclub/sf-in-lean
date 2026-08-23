(** * Auto: More Automation *)

(* SOONER: Exercises REALLY badly needed in this file!! *)
(* LATER: Explain a bit more about info_auto? *)
(* INSTRUCTORS: "in *" should not be typeset as "in \times", but this
   appears to be a behavior of the standard coqdoc... *)
(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.String.
From LF Require Import Maps.
From LF Require Import Imp.
(* TERSE: /HIDEFROMHTML *)

(** FULL: Up to now, we've used the manual part of Rocq's tactic
    facilities.  In this chapter, we'll learn more about some of
    Rocq's powerful automation features: proof search via the [auto]
    tactic, automated forward reasoning via the [Ltac] hypothesis
    matching machinery, and deferred instantiation of existential
    variables using [eapply] and [eauto].  Using these features
    together with Ltac's scripting facilities will enable us to make
    some of our proofs startlingly short!  Used properly, they can
    also make proofs more maintainable and robust to changes in
    underlying definitions.  A deeper treatment of [auto] and [eauto]
    can be found in the [UseAuto] chapter in _Programming Language
    Foundations_.

    (There's one other major category of automation we haven't
    discussed much yet, namely built-in decision procedures for
    specific kinds of problems: [lia] is one example, but there are
    others.  This topic will be deferred for a while longer.)

    Our motivating example will be the following proof, repeated with
    just a few small changes from the \CHAP{Imp} chapter.  We will
    simplify this proof in several stages. *)

(** TERSE: Consider the proof below, showing that [ceval] is
    deterministic.

    Notice all the repetition and near-repetition... *)

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b evaluates to true *)
    apply IHE1. assumption.
  - (* b evaluates to false (contradiction) *)
    rewrite H in H5. discriminate.
  (* E_IfFalse *)
  - (* b evaluates to true (contradiction) *)
    rewrite H in H5. discriminate.
  - (* b evaluates to false *)
    apply IHE1. assumption.
  (* E_WhileFalse *)
  - (* b evaluates to false *)
    reflexivity.
  - (* b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.

(** * The [auto] Tactic *)

(** Thus far, our proof scripts mostly apply relevant hypotheses or
    lemmas by name, and only one at a time. *)

(* FULL *)
Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.
(* /FULL *)

(** The [auto] tactic tries to free us from this drudgery by _searching_
    for a sequence of applications that will prove the goal: *)

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

(** TERSE: *** *)
(** The [auto] tactic solves goals that are solvable by any combination of
    [intros] and [apply]. *)

(** FULL: Using [auto] is always "safe" in the sense that it will
    never fail and will never change the proof state: either it
    completely solves the current goal, or it does nothing. *)

(** Here is a larger example showing [auto]'s power: *)

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

(** TERSE: *** *)
(** Proof search could, in principle, take an arbitrarily long time,
    so there is a limit to how deep [auto] will search by default. *)

(** If [auto] is not solving our goal as expected we can use [debug auto]
    to see a trace. *)
Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* When it cannot solve the goal, [auto] does nothing *)
  auto.

  (* Let's see where [auto] gets stuck using [debug auto] *)
  debug auto.

  (* Optional argument to [auto] says how deep to search
     (default is 5) *)
  auto 6.
Qed.

(** TERSE: *** *)

(** TERSE: The [auto] tactic considers the hypotheses in the current
    context together with a _hint database_ of other lemmas and
    constructors.

    Some common facts about equality and logical operators are
    installed in the hint database by default. *)

(** FULL: When searching for potential proofs of the current goal,
    [auto] considers the hypotheses in the current context together
    with a _hint database_ of other lemmas and constructors.  Some
    common lemmas about equality and logical operators are installed
    in this hint database by default. *)

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.

(** TERSE: *** *)
(** If we want to see which facts [auto] is using, we can use
    [info_auto] instead. *)

Example auto_example_5: 2 = 2.
Proof.
  info_auto.
Qed.

(* INSTRUCTORS: auto subsumes reflexivity because eq_refl is in hint
   database *)

Example auto_example_5' : forall (P Q R S T U W: Prop),
  (U -> T) ->
  (W -> U) ->
  (R -> S) ->
  (S -> T) ->
  (P -> R) ->
  (U -> T) ->
  P ->
  T.
Proof.
  intros.
  info_auto.
Qed.

(** TERSE: *** *)
(** We can extend the hint database just for the purposes of one
    application of [auto] by writing "[auto using ...]". *)

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. lia. Qed.

Example auto_example_6 : forall n m p q : nat,
  (p = q -> (n <= m /\ m <= n)) ->
  p = q ->
  n = m.
Proof.
  auto using le_antisym.
Qed.

(** TERSE: *** *)

(** TERSE: We can also _permanently_ extend the hint database:

      - [Hint Resolve T : core.]

        Add a theorem or constructor [T] to the global database

      - [Hint Constructors c : core.]

        Add _all_ constructors of [c] to the global database

      - [Hint Unfold d : core.]

        Automatically expand defined symbol [d] during [auto] *)
(** FULL: Of course, in any given development there will probably be
    some specific constructors and lemmas that are used very often in
    proofs.  We can add these to the global hint database by writing
[[
      Hint Resolve T : core.
]]
    at the top level, where [T] is a top-level theorem or a
    constructor of an inductively defined proposition (i.e., anything
    whose type is an implication).  As a shorthand, we can write
[[
      Hint Constructors c : core.
]]
    to tell Rocq to do a [Hint Resolve] for _all_ of the constructors
    from the inductive definition of [c].

    It is also sometimes necessary to add
[[
      Hint Unfold d : core.
]]
    where [d] is a defined symbol, so that [auto] knows to unfold uses
    of [d], thus enabling further possibilities for applying lemmas that
    it knows about. *)

(** It is also possible to define specialized hint databases (besides
    [core]) that can be activated only when needed; indeed, it is good
    style to create your own hint databases instead of polluting
    [core].

    See the Rocq reference manual for details. *)

(* SOONER: BCP 25: We say it is good style not to pollute [core] but
   then we do it! *)

(** TERSE: *** *)
Hint Resolve le_antisym : core.

Example auto_example_6' : forall n m p q : nat,
  (p = q -> (n <= m /\ m <= n)) ->
  p = q ->
  n = m.
Proof.
  auto. (* picks up hint from database *)
Qed.

(** TERSE: *** *)
Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  (* does nothing *)
Abort.

Hint Unfold is_fortytwo : core.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto. (* try also: info_auto. *)
Qed.

(** FULL: Note that the [Hint Unfold is_fortytwo] command above the
    example is needed because, unlike the normal [apply] tactic, the
    [simple apply] steps that are performed by [auto] do not do any
    automatic unfolding. *)

(** TERSE: *** *)

(** Let's take a first pass over [ceval_deterministic], using [auto]
    to simplify the proof script. *)

Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
    induction E1; intros st2 E2; inversion E2; subst;
    auto.             (* <---- here's one good place for auto *)
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.             (* <---- here's another *)
  - (* E_IfTrue *)
    rewrite H in H5. discriminate.
  - (* E_IfFalse *)
    rewrite H in H5. discriminate.
  - (* E_WhileFalse *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, with b false *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, with b true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto.             (* <---- and another *)
Qed.

(* FULL *)
(** When we are using a particular tactic many times in a proof, we
    can use a variant of the [Proof] command to make that tactic into
    a default within the proof.  Saying [Proof with t] (where [t] is
    an arbitrary tactic) allows us to use [t1...] as a shorthand for
    [t1;t] within the proof.  As an illustration, here is an alternate
    version of the previous proof, using [Proof with auto]. *)
(* LATER: BCP 3/16: AAA doesn't like this style and is beginning to
   convince me too. *)

Theorem ceval_deterministic'_alt: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
(* FOLD *)
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
       intros st2 E2; inversion E2; subst...
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *...
  - (* E_IfTrue *)
    rewrite H in H5. discriminate.
  - (* E_IfFalse *)
    rewrite H in H5. discriminate.
  - (* E_WhileFalse *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, with b false *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, with b true *)
    rewrite (IHE1_1 st'0 H3) in *...
Qed.
(* /FOLD *)
(* /FULL *)

(** * Searching For Hypotheses *)

(** FULL: The proof has become simpler, but there is still an annoying
    degree of repetition. Let's start by tackling the contradiction
    cases. Each of them occurs in a situation where we have both
[[
      H1: beval st b = false
]]
    and
[[
      H2: beval st b = true
]]
    as hypotheses.  The contradiction is evident, but demonstrating it
    is a little complicated: we have to locate the two hypotheses [H1]
    and [H2] and do a [rewrite] following by a [discriminate].  We'd
    like to automate this process.

    (In fact, Rocq has a built-in tactic [congruence] that will do the
    job in this case.  We'll ignore this tactic for now, in order to
    demonstrate how to build forward-search tactics by hand.)

    As a first step, we can abstract out the piece of script in
    question by writing a little function in Ltac. *)

(** TERSE: The proof has become simpler, but there is still an annoying
    amount of repetition.

    Let's first tackle the contradiction cases.  Each occurs where we
    have hypothesis of the form
[[
      H1: beval st b = false
]]
    as well as:
[[
      H2: beval st b = true
]]

    First step: abstracting out that piece as a script in Ltac. *)

Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.

(** TERSE: *** *)
(** TERSE: Using [rwd]... *)

Theorem ceval_deterministic'': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - (* E_IfTrue *)
    rwd H H5.                 (* <----- *)
  - (* E_IfFalse *)
    rwd H H5.                 (* <----- *)
  - (* E_WhileFalse *)
    rwd H H2.                 (* <----- *)
  - (* E_WhileTrue - b false *)
    rwd H H4.                 (* <----- *)
  - (* EWhileTrue - b true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto. Qed.

(** TERSE: *** *)

(** That's a bit better, but we really want Rocq to discover the
    relevant hypotheses for us.  We can do this by using the [match
    goal] facility of Ltac. *)

Ltac find_rwd :=
  match goal with
    H1: ?E = true, H2: ?E = false |- _
       =>
    rwd H1 H2
  end.

(** FULL: This [match goal] looks for two distinct hypotheses that
    have the form of equalities, with the same arbitrary expression
    [E] on the left and with conflicting boolean values on the right.
    If such hypotheses are found, it binds [H1] and [H2] to their
    names and applies the [rwd] tactic to [H1] and [H2].

    Adding this tactic to the ones that we invoke in each case of the
    induction handles all of the contradictory cases. *)

(** TERSE: The [match goal] tactic looks for hypotheses matching the
    pattern specified. In this case, we're looking for two equalities
    [H1] and [H2] equating the same expression [?E] to both [true] and
    [false]. *)

(** TERSE: *** *)
Theorem ceval_deterministic''': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst;
       try find_rwd;                                  (* <------ *)
       auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - (* E_WhileTrue - b true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto. Qed.

(** TERSE: *** *)

(** Let's see about the remaining cases. Each of them involves
    rewriting a hypothesis after feeding it with the required
    condition. We can automate the task of finding the relevant
    hypotheses to rewrite with. *)

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _
    => rewrite (H1 X H2) in *
  end.

(** FULL: The pattern [forall x, ?P x -> ?L = ?R] matches any hypothesis of
    the form "for all [x], _some property of [x]_ implies _some
    equality_."  The property of [x] is bound to the pattern variable
    [P], and the left- and right-hand sides of the equality are bound
    to [L] and [R].  The name of this hypothesis is bound to [H1].
    Then the pattern [?P ?X] matches any hypothesis that provides
    evidence that [P] holds for some concrete [X].  If both patterns
    succeed, we apply the [rewrite] tactic (instantiating the
    quantified [x] with [X] and providing [H2] as the required
    evidence for [P X]) in all hypotheses and the goal. *)

(* HIDE: MRC'20: The text below is not wrong about how [repeat] could
   be used to try rewriting with many pairs of hypotheses.  But, _that
   is not what happens in this proof_.  Each time only one rewrite is
   needed, and that is with [IHE1_1] as can be seen in the proof above
   of [ceval_deterministic''''].  So [try find_eqn] suffices: [repeat
   find_eqn] is overkill.  I have therefore hidden the text and
   changed the proof to use [try]. *)
(* HIDE:
    One problem remains: in general, there may be several pairs of
    hypotheses that have the right general form, and it seems tricky
    to pick out the ones we actually need.  A key trick is to realize
    that we can _try them all_!  Here's how this works:

    - each execution of [match goal] will keep trying to find a valid
      pair of hypotheses until the tactic on the RHS of the match
      succeeds; if there are no such pairs, it fails;
    - [rewrite] will fail given a trivial equation of the form [X = X];
    - we can wrap the whole thing in a [repeat], which will keep doing
      useful rewrites until only trivial ones are left. *)

(** TERSE: *** *)
(** TERSE: Now we can make use of [find_eqn] to repeatedly rewrite
    with the appropriate hypothesis, wherever it may be found. *)

(* HIDE: MRC'20: hidden for same reason as above. *)
(* HIDE:
    In our example proof, we [repeat find_eqn], which will repeatedly
    rewrite until only trivial rewrites are available (since [rewrite]
    fails when given a trivial equation). *)

Theorem ceval_deterministic'''': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst;
    try find_rwd;
    try find_eqn;    (* <------- *)
    auto.
Qed.

(** TERSE: *** *)

(** The big payoff in this approach is that the new proof script is
    more robust in the face of changes to our language.  To test this,
    let's try adding a [REPEAT] command to the language. *)

(* ADVANCED: HIDEFROMHTML *)
Module Repeat.
(* ADVANCED: /HIDEFROMHTML *)

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (c : com) (b : bexp).

(** [REPEAT] behaves like [while], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

(** TERSE: *** *)

Notation "'repeat' x 'until' y 'end'" :=
         (CRepeat x y)
            (in custom com at level 0,
             x at level 99, y at level 99).
(* INSTRUCTORS: Copy of template com *)
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

(** TERSE: *** *)
(* INSTRUCTORS: Copy of template eval *)
Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_RepeatEnd : forall st st' b c,
      st  =[ c ]=> st' ->
      beval st' b = true ->
      st  =[ repeat c until b end ]=> st'
  | E_RepeatLoop : forall st st' st'' b c,
      st  =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ repeat c until b end ]=> st'' ->
      st  =[ repeat c until b end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** TERSE: *** *)

(** Our first attempt at the determinacy proof does not quite succeed:
    the [E_RepeatEnd] and [E_RepeatLoop] cases are not handled by our
    previous automation. *)
(* SOONER: BCP 23: Maybe we should just swap them earlier -- not sure this
   little detour into ltac debugging is very helpful... *)

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inversion E2; subst; try find_rwd; try find_eqn; auto.
  - (* E_RepeatEnd *)
    + (* b evaluates to false (contradiction) *)
       find_rwd.
       (* oops: why didn't [find_rwd] solve this for us already?
          answer: we did things in the wrong order. *)
  - (* E_RepeatLoop *)
     + (* b evaluates to true (contradiction) *)
        find_rwd.
Qed.

(** TERSE: *** *)

(* SOONER: It would be even better (rhetorically) to just silently do
   the swap, up above! The story gets a bit muddy here.

   MRC'20: As a different perspective, let me suggest that it's helpful
   to see this issue and its solution.  It's happened to me before---even
   in the middle of a lecture! *)
(** Fortunately, to fix this, we just have to swap the invocations of
    [find_eqn] and [find_rwd]. *)

Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inversion E2; subst; try find_eqn; try find_rwd; auto.
Qed.

(* ADVANCED: HIDEFROMHTML *)
End Repeat.
(* ADVANCED: /HIDEFROMHTML *)

(** FULL: These examples just give a flavor of what "hyper-automation"
    can achieve in Rocq.  The details of [match goal] are a bit
    tricky (and debugging scripts using it is, frankly, not very
    pleasant).  But it is well worth adding at least simple uses to
    your proofs, both to avoid tedium and to "future proof" them. *)

(** * The [eapply] and [eauto] tactics *)
(* SOONER: Marc Bezem 2022:

  7. Auto.v and AltAuto.v: I think the explanation of eapply is much
  better in AltAuto.v than in Auto.v (minor: position 3 (referred to
  later) is missing on line 812, AltAuto.v).  *)

(** FULL: To close the chapter, let's look at one more convenience
    feature of Rocq: its ability to delay instantiation of
    quantifiers.  To motivate this feature, recall this example from
    the \CHAP{Imp} chapter: *)

(** TERSE: Recall this example from the \CHAP{Imp} chapter: *)

Example ceval_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We supply the intermediate state [st']... *)
  apply E_Seq with (X !-> 2).
  - apply E_Asgn. reflexivity.
  - apply E_IfFalse. reflexivity. apply E_Asgn. reflexivity.
Qed.

(** TERSE: *** *)
(** TERSE: In the first step of the proof, we had to explicitly provide
    the intermediate state [X !-> 2], due to the "hidden" argument [st']
    to the [E_Seq] constructor:
[[
          E_Seq : forall c1 c2 st st' st'',
            st  =[ c1 ]=> st'  ->
            st' =[ c2 ]=> st'' ->
            st  =[ c1 ; c2 ]=> st''
]]
*)

(** TERSE: If we leave out the [with], this step fails, because Rocq
    cannot find an instance for the variable [st']. But this is silly,
    since the appropriate value for [st'] will become obvious in the
    very next step. *)

(** TERSE: *** *)
(** TERSE: With [eapply], we can eliminate this silliness: *)
(** FULL: In the first step of the proof, we had to explicitly provide a
    longish expression to help Rocq instantiate a "hidden" argument to
    the [E_Seq] constructor.  This was needed because the definition
    of [E_Seq]...
[[
          E_Seq : forall c1 c2 st st' st'',
            st  =[ c1 ]=> st'  ->
            st' =[ c2 ]=> st'' ->
            st  =[ c1 ; c2 ]=> st''
]]
   is quantified over a variable, [st'], that does not appear in its
   conclusion, so unifying its conclusion with the goal state doesn't
   help Rocq find a suitable value for this variable.  If we leave
   out the [with], this step fails ("Error: Unable to find an
   instance for the variable [st']").

   What's silly about this error is that the appropriate value for
   [st'] will actually become obvious in the very next step, where we
   apply [E_Asgn].  If Rocq could just wait until we get to this step,
   there would be no need for us to give the value explicitly.  This
   is exactly what the [eapply] tactic allows: *)

(* HIDE: The numbers are a bit confusing in the terse version. *)
Example ceval'_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* 1 *) eapply E_Seq.
  - (* 2 *) apply E_Asgn.
    (* 3 *) reflexivity.
  - (* 4 *) apply E_IfFalse. reflexivity. apply E_Asgn. reflexivity.
Qed.

(** FULL: The [eapply H] tactic behaves just like [apply H] except
    that, after it finishes unifying the goal state with the
    conclusion of [H], it skips checking whether all the variables
    that were introduced in the process have been given concrete
    values during unification.

    If you step through the proof above, you'll see that the goal
    state at position [1] mentions the _existential variable_ [?st']
    in both of the generated subgoals.  The next step (which gets us
    to position [2]) replaces [?st'] with a concrete value.  This new
    value contains a new existential variable [?n], which is
    instantiated in its turn by the following [reflexivity] step,
    position [3].  When we start working on the second subgoal
    (position [4]), we observe that the occurrence of [?st'] in this
    subgoal has been replaced by the value that it was given during
    the first subgoal. *)

(** Several of the tactics that we've seen so far, including [exists],
    [constructor], and [auto], have similar variants. The [eauto]
    tactic works like [auto], except that it uses [eapply] instead of
    [apply].  Tactic [info_eauto] shows us which tactics [eauto] uses
    in its proof search.

    Below is an example of [eauto].  Before using it, we need to give
    some hints to [auto] about using the constructors of [ceval]
    and the definitions of [state] and [total_map] as part of its
    proof search. *)

Hint Constructors ceval : core.
(* SOONER: Explain (and differentiate from Hint Unfold). *)
Hint Transparent state total_map : core.

Example eauto_example : exists s',
  (Y !-> 1 ; X !-> 2) =[
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  ]=> s'.
Proof. info_eauto. Qed.
(* HIDE: (BCP/AAA 12/15) And why doesn't [eexists. info_auto.] work
   here?? It used to, but something changed when we reworked total
   maps... some bug with existentials?  Note that removing the [Hint
   Transparent total_map] above causes it to fail. *)

(* SOONER: Can this be deleted? *)
(** The [eauto] tactic works just like [auto], except that it uses
    [eapply] instead of [apply]; [info_eauto] shows us which facts
    [eauto] uses. *)

(** TERSE: *** *)
(** FULL: Pro tip: One might think that, since [eapply] and [eauto]
    are more powerful than [apply] and [auto], we should just use them
    all the time.  Unfortunately, they are also significantly slower
    -- especially [eauto].  Rocq experts tend to use [apply] and [auto]
    most of the time, only switching to the [e] variants when the
    ordinary variants don't do the job. *)

(* SOONER: Perhaps another / better example? *)

(* FULL *)
(** * Constraints on Existential Variables *)

(** In order for [Qed] to succeed, all existential variables need to
    be determined by the end of the proof. Otherwise Rocq
    will (rightly) refuse to accept the proof. Remember that the Rocq
    tactics build proof objects, and proof objects containing
    existential variables are not complete. *)

Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP. Unshelve. exact 0.
(** Rocq gives a warning after [apply HP]: "All the remaining goals
    are on the shelf," means that we've finished all our top-level
    proof obligations but along the way we've put some aside to be
    done later, and we have not finished those.  Trying to close the
    proof with [Qed] would yield an error. (Try it!) *)
Abort.
(* INSTRUCTORS:
   Marc Bezem 2022:
   In Auto.v, line 667, I don't understand why the proof of Lemma
   silly1 cannot be completed. The final proof state before aborting
   asks to "prove" nat in the empty context. This is exactly how it
   should be, and one such "proof" is 0. I tried exact 0 and
   constructor but nothing worked. So here I don't understand Rocq, as
   the tactics can also be used to construct elements, functions
   etc. and not just proofs.  BCP 25: [Unshelve. exact 0.] is what you want here. *)

(** An additional constraint is that existential variables cannot be
    instantiated with terms containing ordinary variables that did not
    exist at the time the existential variable was created.  (The
    reason for this technical restriction is that allowing such
    instantiation would lead to inconsistency of Rocq's logic.) *)
(* HIDE: What's maybe still missing is explaining of _why_ allowing to
   instantiate existential using variables that didn't exist when the
   existential was created would lead to inconsistency.  APT: could
   use this example from Chlipala: could "prove" exists (n:nat),
   forall (m:nat), n = m by: econstructor; intro; reflexivity.  BCP: I
   think this is getting too technical and we should leave it as it
   is. *)

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].
  Fail apply HP'.

(** The error we get, with some details elided, is:
[[
      cannot instantiate "?y" because "y" is not in its scope
]]
    In this case there is an easy fix: doing [destruct HP] _before_
    doing [eapply HQ]. *)
Abort.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. apply HP'.
Qed.

(** The [apply HP'] in the last step unifies the existential variable
    in the goal with the variable [y].

    Note that the [assumption] tactic doesn't work in this case, since
    it cannot handle existential variables.  However, Rocq also
    provides an [eassumption] tactic that solves the goal if one of
    the premises matches the goal up to instantiations of existential
    variables. We can use it instead of [apply HP'] if we like. *)

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

(** The [eauto] tactic will use [eapply] and [eassumption], streamlining
    the proof even further. *)

Lemma silly2_eauto : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eauto.
Qed.
(* /FULL *)
