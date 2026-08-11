(** * ImpCEvalFun: An Evaluation Function for Imp *)

(** We saw in the \CHAP{Imp} chapter how a naive approach to defining a
    function representing evaluation for Imp runs into difficulties.
    There, we adopted the solution of changing from a functional to a
    relational definition of evaluation.  In this optional chapter, we
    consider strategies for getting the functional approach to
    work. *)

(* #################################### *)
(** * A Broken Evaluator *)
(* TERSE: HIDEFROMHTML *)

Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
Import Nat.
From Stdlib Require Import EqNat.
From LF Require Import Imp Maps.
Local Open Scope com_scope.
(* TERSE: /HIDEFROMHTML *)

(** Here was our first try at an evaluation function for commands,
    omitting [while]. *)
(* HIDE: Called [ceval_fun_no_while] there... *)

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ l := a1 }> =>
        (l !-> aeval st a1 ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | <{ if b then c1 else c2 end }> =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | <{ while b1 do c1 end }> =>
        st  (* bogus *)
  end.

(* SOONER: Some more words around here (the whole section, actually)
   would be useful...  Also, the text is a verbatim copy of what's in
   Imp -- boring. *)

(** TERSE: *** *)
(** As we remarked in chapter \CHAP{Imp}, in a traditional functional
    programming language like ML or Haskell we could write the while
    case as follows:
<<
    | while b1 do c1 end =>
        if (beval st b1) then
          ceval_step1 st <{ c1; while b1 do c1 end }>
        else st
>>
    Rocq doesn't accept such a definition ([Error: Cannot guess
    decreasing argument of fix]) because the function we want to
    define is not guaranteed to terminate. Indeed, the changed
    [ceval_step1] function applied to the [loop] program from [Imp.v]
    would never terminate. Since Rocq is not just a functional
    programming language, but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is an
    invalid(!) Rocq program showing what would go wrong if Rocq allowed
    non-terminating recursive functions:
<<
     Fixpoint loop_false (n : nat) : False := loop_false n.
>>
    That is, propositions like [False] would become
    provable (e.g., [loop_false 0] would be a proof of [False]), which
    would be a disaster for Rocq's logical consistency.

    Thus, because it doesn't terminate on all inputs, the full version
    of [ceval_step1] cannot be written in Rocq -- at least not without
    one additional trick... *)

(* #################################### *)
(** * A Step-Indexed Evaluator *)

(** The trick we need is to pass an _additional_ parameter to the
    evaluation function that tells it how long to run.  Informally, we
    start the evaluator with a certain amount of "gas" in its tank,
    and we allow it to run until either it terminates in the usual way
    _or_ it runs out of gas, at which point we simply stop evaluating
    and say that the final result is the empty memory.  (We could also
    say that the result is the current state at the point where the
    evaluator runs out of gas -- it doesn't really matter because the
    result is going to be wrong in either case!) *)

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_st
  | S i' =>
    match c with
      | <{ skip }> =>
          st
      | <{ l := a1 }> =>
          (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

(** FULL: _Note_: It is tempting to think that the index [i] here is
    counting the "number of steps of evaluation."  But if you look
    closely you'll see that this is not the case: for example, in the
    rule for sequencing, the same [i] is passed to both recursive
    calls.  Understanding the exact way that [i] is treated will be
    important in the proof of [ceval__ceval_step], which is given as
    an exercise below.

    One thing that is not so nice about this evaluator is that we
    can't tell, from its result, whether it stopped because the
    program terminated normally or because it ran out of gas.  Our
    next version returns an [option state] instead of just a [state],
    so that we can distinguish between normal and abnormal
    termination. *)

Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Proof. reflexivity. Qed.

(* FULL *)
(* HIDE: Note that this is a duplicate from Imp! *)
(* EX1? (pup_to_n) *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive -- i.e., [1 + 2 + ... + X]) in the variable [Y].  Make
   sure your solution satisfies the test that follows. *)

Definition pup_to_n : com
  (* ADMITDEF *) :=
  <{ Y := 0;
     while ~(X = 0) do
       Y := Y + X ;
       X := X - 1
     end }>.
(* /ADMITDEF *)

Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
(* ADMITTED *)
(* /ADMITTED *)
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
Proof. reflexivity. Qed.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(** [] *)

(* EX2? (peven) *)
(** Write an [Imp] program that sets [Z] to [0] if [X] is even and
    sets [Z] to [1] otherwise.  Use [test_ceval] to test your
    program. *)

(* SOLUTION *)
Definition peven : com :=
  <{ while (2 <= X) do
       X := X - 2
     end;
     if (X = 0)
       then Z := 0
       else Z := 1
     end }>.

Example peven_2 :
  test_ceval (X !-> 2) peven
  = Some (0, 0, 0).
Proof. reflexivity. Qed.

Example peven_5 :
  test_ceval (X !-> 5) peven
  = Some (1, 0, 1).
Proof. reflexivity. Qed.
(* /SOLUTION *)
(** [] *)
(* LATER: The spec for this program is somewhat challenging; it might
   make a good guided exercise or a challenging design problem. *)
(* /FULL *)

(* ################################################################ *)
(** * Relational vs. Step-Indexed Evaluation *)

(** FULL: As for arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation would actually
    amount to the same thing in the end.  This section shows that this
    is the case. *)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
(* FOLD *)
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  - (* i = 0 -- contradictory *)
    intros c st st' H. discriminate H.

  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* skip *) apply E_Skip.
      + (* := *) apply E_Asgn. reflexivity.

      + (* ; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (* Evaluation of r1 terminates normally *)
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. assumption.
        * (* Otherwise -- contradiction *)
          discriminate H1.

      + (* if *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      + (* while *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r1 = Some s *)
           apply E_WhileTrue with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. assumption. }
         { (* r1 = None *) discriminate H1. }
        * (* r = false *)
          injection H1 as H2. rewrite <- H2.
          apply E_WhileFalse. apply Heqr. Qed.
(* /FOLD *)
(* SOONER: From Marc Bezem 2022:

   Theorem ceval_step__ceval: forall c st st',
         (exists i, ceval_step st c i = Some st') ->
         st =[ c ]=> st'.

   The first six lines of the proof lead to the initial proof state
   of the following equivalent formulation:

   Theorem ceval_step__ceval_curried: forall i c st st',
         ceval_step st c i = Some st' -> st =[ c ]=> st'.
   Proof. induction i as [|i']; intros c st st' H. discriminate H.
     destruct c; simpl in H; inversion H; subst; clear H.
     (* induction step i = S i' as in original *) ...

   The final theorem can still be formulated as is:

   Theorem ceval_and_ceval_step_coincide: forall c st st',
         st =[ c ]=> st'
     <-> exists i, ceval_step st c i = Some st'.

   Just the proof from right to left uses one half of the following
   lemma, that is interesting in itself (could be an exercise in Logic.v):

   Lemma currying : forall (X:Type) (P : X -> Prop) (Q : Prop),
     (forall x, P x -> Q) <-> ((exists x,  P x) -> Q).
   Proof. split.
     - intros HallPQ HexP. destruct HexP. apply (HallPQ x H).
     - intros HexPQ x HPx. apply HexPQ. exists x. assumption.
   Qed.
*)

(* FULL *)
(* EX4AM (ceval_step__ceval_inf) *)
(** Write an informal proof of [ceval_step__ceval], following the
    usual template.  (The template for case analysis on an inductively
    defined value should look the same as for induction, except that
    there is no induction hypothesis.)  Make your proof communicate
    the main ideas to a human reader; do not simply transcribe the
    steps of the formal proof. *)

(* SOLUTION *)
(**
 THEOREM: For all [c], [st], and [st'], if there exists an [i] such
 that [ceval_step st c i = Some st'] then [st =[ c ]=> st'].

 PROOF: Suppose we are given such an [i].  Proceed by induction on [i].

 - Suppose [i = 0], with [ceval_step st c 0 = Some st'].  We must show
   that [st =[ c ]=> st'].

   This is a contradiction: [ceval_step st c 0] = [None] for all [st]
   and [c].

 - Suppose [i = S i'], with [ceval_step st c (S i') = Some st'] and,
   for all [st], [c], and [st'], if [ceval_step st c i' = Some st'],
   then [st =[ c ]=> st'].  We must show [ceval_step st c st'].

   Proceed by case analysis on the command [c].

   - Suppose [c = SKIP], where [ceval_step st SKIP (S i') = Some st'].
     We must show [st =[ SKIP ]=> st'].

     By the definition of [ceval_step], we know that [st = st']; by
     [E_Skip], we can derive [st =[ SKIP ]=> st], as required.

   - Suppose [c = X ::= a], where [ceval_step st (X ::= a) (S i') =
     Some st'].  We must show [st =[ X ::= a ]=> st'].

     By the definition of [ceval_step], [st' = t_update st X (aeval st
     a)].  By [E_Asgn], we can derive [st =[ X ::= a ]=> (t_update st
     X (aeval st a))].

   - Suppose [c = c1 ;; c2 ], where [ceval_step st (c1 ;; c2) (S i') =
     Some st'].  We must show [st =[ c1 ;; c2 ]=> st'].

     Since we know [ceval_step st (c1 ;; c2) (S i') = Some st'], it
     follows from the definition of [ceval_step] that [ceval_step st
     c1 i' = Some st1] and [ceval_step st1 c2 i' = Some st'].  By the
     IH, we can derive [st =[ c1 ]=> st1] and [st1 =[ c2 ]=> st'].
     Finally, the [E_Seq] rule gives us [st =[ c1 ;; c2 ]=> st'].

   - Suppose [c = TEST b THEN c1 ELSE c2], where [ceval_step st (TEST b
     THEN c1 ELSE c2) (S i') = Some st'].  We must show [ceval st (TEST
     b THEN c1 ELSE c2) st'].

     There are two cases to consider, depending on the result of
     [beval st b].

     - Suppose [beval st b = true].  In this case,
[[
           ceval_step st (TEST b THEN c1 ELSE c2) (S i')
         = ceval_step st c1 i'
         = Some st'
]]
       By the IH, this means that [st =[ c1 ]=> st']; by [E_IfTrue],
       we obtain [st =[ TEST b THEN c1 ELSE c2 ]=> st'].

     - Suppose [beval st b = false].  This case is the same as the
       previous, with [c2] for [c1] and [E_IfFalse] for [E_IfTrue].

   - Suppose [c = while b do c end], where [ceval_step st (while b do
     c end) (S i') = Some st'].  We must show [st =[ while b do c end
     ]=> st'].

     As in the case for conditionals, there are two cases to consider,
     depending on the result of [beval st b].

     - Suppose [beval st b = true].  In this case, we can derive the
       following from the definition of the [while] case in
       [ceval_step]:
[[
          ceval_step st c i' = Some st1
          ceval_step st1 (while b do c end) i' = Some st'
]]
       The IH gives us:
[[
          st  =[ c ]=> st1
          st1 =[ while b do c end ]=> st'
]]
       which let us show, by [E_WhileTrue], that [st =[ while b do c
       end ]=> st'].

     - Suppose [beval st b = false].  In this case, we can infer from
       the definition of [ceval_step] that [st = st'].  We can then
       see, by [E_WhileFalse], that [st =[ while b do c end ]=> st].
 *)
(* /SOLUTION *)

(* GRADE_MANUAL 6: ceval_step__ceval_inf *)
(** [] *)
(* /FULL *)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by lia.
    destruct c.
    + (* skip *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* := *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        discriminate Hceval.

    + (* if *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.

    + (* while *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        simpl in Hceval. discriminate Hceval.  Qed.

(* FULL *)
(* EX3! (ceval__ceval_step) *)
(** Finish the following proof.  You'll need [ceval_step_more] in a
    few places, as well as some basic facts about [<=] and [plus]. *)

(* /FULL *)
Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  (* ADMITTED *)
  - (* E_Skip *)
    exists 1. reflexivity.
  - (* E_Asgn *)
    exists 1. simpl. subst. reflexivity.
  - (* E_Seq *)
    inversion IHHce1 as [i1 Hcef1].
    inversion IHHce2 as [i2 Hcef2].
    exists (S (i1 + i2)). simpl.
    apply ceval_step_more with (i2 := i1 + i2) in Hcef1.
    apply ceval_step_more with (i2 := i2 + i1) in Hcef2.
      rewrite Hcef1. simpl. rewrite add_comm. assumption.
      lia. lia.
  - (* E_IfTrue *)
    inversion IHHce as [i1 Hcef1].
    exists (S i1). simpl. rewrite -> H. assumption.
  - (* E_IfFalse *)
    inversion IHHce as [i1 Hcef1].
    exists (S i1). simpl. rewrite -> H. assumption.
  - (* E_WhileFalse *)
    exists 1. simpl. rewrite -> H. reflexivity.
  - (* E_WhileTrue *)
    inversion IHHce1 as [i1 Hcef1].
    inversion IHHce2 as [i2 Hcef2].
    exists (S (i1 + i2)). simpl.
    apply ceval_step_more with (i2 := i1 + i2) in Hcef1.
    apply ceval_step_more with (i2 := i2 + i1) in Hcef2.
      rewrite -> H. rewrite Hcef1. simpl. rewrite add_comm. assumption.
      lia. lia. Qed.
(* /ADMITTED *)
(* FULL *)
(** [] *)
(* /FULL *)

Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* ####################################################### *)
(** * Determinism of Evaluation Again *)

(** Using the fact that the relational and step-indexed definition of
    evaluation are the same, we can give a slicker proof that the
    evaluation _relation_ is deterministic. *)

Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
(* FOLD *)
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  lia. lia.  Qed.
(* /FOLD *)
