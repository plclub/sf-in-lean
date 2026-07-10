(** * StlcProp: Properties of STLC *)

(* INSTRUCTORS: This is a good lecture to do mostly at the board (and
   therefore not much work has gone into the TERSE version).  It may
   be useful to distribute a one-page handout with all the STLC rules for
   typing and the step relation, to avoid too much jumping back and
   forth on the screen.

   Here's a possible cheat sheet: *)
(* TERSE: HIDEFROMHTML *)
(* TERSE:
                  THE SIMPLY TYPED LAMBDA CALCULUS

    Syntax:

       t ::= x                         variable
           | \x:T,t                    abstraction
           | t t                       application
           | true                      constant true
           | false                     constant false
           | if t then t else t        conditional


    Values:

       v ::= \x:T,t
           | true
           | false


    Substitution:

       [x:=s]x               = s
       [x:=s]y               = y                      if x <> y
       [x:=s](\x:T, t)       = \x:T, t
       [x:=s](\y:T, t)       = \y:T, [x:=s]t          if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)
       [x:=s]true            = true
       [x:=s]false           = false
       [x:=s](if t1 then t2 else t3) =
                       if [x:=s]t1 then [x:=s]t2 else [x:=s]t3


    Small-step operational semantics:

                               value v2
                     ---------------------------                    (ST_AppAbs)
                     (\x:T2,t1) v2 --> [x:=v2]t1

                              t1 --> t1'
                           ----------------                           (ST_App1)
                           t1 t2 --> t1' t2

                              value v1
                              t2 --> t2'
                           ----------------                           (ST_App2)
                           v1 t2 --> v1 t2'

                    --------------------------------                (ST_IfTrue)
                    (if true then t1 else t2) --> t1

                    ---------------------------------              (ST_IfFalse)
                    (if false then t1 else t2) --> t2

                              t1 --> t1'
         ----------------------------------------------------           (ST_If)
         (if t1 then t2 else t3) --> (if t1' then t2 else t3)


    Typing:

                              Gamma x = T1
                            ------------------                          (T_Var)
                            Gamma |-- x \in T1

                        x |-> T2 ; Gamma |-- t1 \in T1
                        ------------------------------                  (T_Abs)
                         Gamma |-- \x:T2,t1 \in T2->T1

                         Gamma |-- t1 \in T2->T1
                           Gamma |-- t2 \in T2
                         -----------------------                        (T_App)
                         Gamma |-- t1 t2 \in T1

                         -----------------------                        (T_True)
                         Gamma |-- true \in Bool

                         ------------------------                       (T_False)
                         Gamma |-- false \in Bool

    Gamma |-- t1 \in Bool    Gamma |-- t2 \in T1   Gamma |-- t3 \in T1
    ------------------------------------------------------------------  (T_If)
                  Gamma |-- if t1 then t2 else t3 \in T1
*)
(* TERSE: /HIDEFROMHTML *)
(* INSTRUCTORS: Ori 2020: we have slightly simplified the preservation
   proof.  We still need the substitution lemma, but the latter is
   proved using weakening. *)
(* SOONER: BCP 21: The stlc_arith exercise needs cleaning up --
   instead of asking people to copy stuff over, we should give the
   headers of all the definitions and just ask them to complete them. *)
(* SOONER: BCP 22: In Wadler's "PLF in Agda", he defines an "animator"
   for STLC terms using the proof terms for progress + preservation.
   This would be a FANTASTIC example (or, perhaps better, exercise!)
   for this chapter. *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Stlc.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".
Module STLCProp.
Import STLC.
(* TERSE: /HIDEFROMHTML *)

(** In this chapter, we develop the fundamental theory of the Simply
    Typed Lambda Calculus -- in particular, the type safety
    theorem. *)

(* ###################################################################### *)
(** * Canonical Forms *)

(* HIDEFROMADVANCED *)
(** FULL: As we saw for the very simple language in the \CHAP{Types}
    chapter, the first step in establishing basic properties of
    reduction and types is to identify the possible _canonical
    forms_ (i.e., well-typed values) belonging to each type.  For
    [Bool], these are again the boolean values [true] and [false]; for
    arrow types, they are lambda-abstractions. *)

(** Formally, we will need these lemmas only for terms that are not
    only well typed but _closed_ -- i.e., well typed in the empty
    context. *)

(* /HIDEFROMADVANCED *)
Lemma canonical_forms_bool : forall t,
  <{ empty |-- t \in Bool }> ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
(* FOLD *)
Proof.
  intros t HT HVal.
  destruct HVal; auto.
  inversion HT.
Qed.
(* /FOLD *)

Lemma canonical_forms_fun : forall t T1 T2,
  <{ empty |-- t \in T1 -> T2 }> ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
(* FOLD *)
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal as [x ? t1| |] ; inversion HT; subst.
  exists x, t1. reflexivity.
Qed.
(* /FOLD *)

(* ###################################################################### *)
(** * Progress *)

(* HIDEFROMADVANCED *)
(** FULL: The _progress_ theorem tells us that closed, well-typed
    terms are not stuck: either a well-typed term is a value, or it
    can take a reduction step.  The proof is a relatively
    straightforward extension of the progress proof we saw in the
    \CHAP{Types} chapter.  We give the proof in English first, then
    the formal version. *)
(** TERSE: The _progress_ theorem tells us that closed, well-typed
    terms are not stuck. *)

(* /HIDEFROMADVANCED *)
Theorem progress : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.
(* FULL *)

(** _Proof_: By induction on the derivation of [|-- t \in T].

    - The last rule of the derivation cannot be [T_Var], since a
      variable is never well typed in an empty context.

    - The [T_True], [T_False], and [T_Abs] cases are trivial, since in
      each of these cases we can see by inspecting the rule that [t]
      is a value.

    - If the last rule of the derivation is [T_App], then [t] has the
      form [t1 t2] for some [t1] and [t2], where [|-- t1 \in T2 -> T]
      and [|-- t2 \in T2] for some type [T2].  The induction hypothesis
      for the first subderivation says that either [t1] is a value or
      else it can take a reduction step.

        - If [t1] is a value, then consider [t2], which by the
          induction hypothesis for the second subderivation must also
          either be a value or take a step.

            - Suppose [t2] is a value.  Since [t1] is a value with an
              arrow type, it must be a lambda abstraction; hence [t1
              t2] can take a step by [ST_AppAbs].

            - Otherwise, [t2] can take a step, and hence so can [t1
              t2] by [ST_App2].

        - If [t1] can take a step, then so can [t1 t2] by [ST_App1].

    - If the last rule of the derivation is [T_If], then [t = if
      t1 then t2 else t3], where [t1] has type [Bool].  The first IH
      says that [t1] either is a value or takes a step.

        - If [t1] is a value, then since it has type [Bool] it must be
          either [true] or [false].  If it is [true], then [t] steps to
          [t2]; otherwise it steps to [t3].

        - Otherwise, [t1] takes a step, and therefore so does [t] (by
          [ST_If]). *)
(* /FULL *)
(* FOLD *)
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
  (* auto solves all three cases in which t is a value *)
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an
       empty context *)
    discriminate H.

  - (* T_App *)
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        eapply canonical_forms_fun in Ht1; [|assumption].
        destruct Ht1 as [x [t0 H1]]. subst.
        exists (<{ [x:=t2]t0 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists (<{t1 t2'}>)...

    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists (<{t1' t2}>)...

  - (* T_If *)
    right. destruct IHHt1...

    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.

    + (* t1 also steps *)
      destruct H as [t1' Hstp]. exists <{if t1' then t2 else t3}>...
Qed.
(* /FOLD *)

(* FULL *)
(* EX3A (progress_from_term_ind) *)
(* GRADE_THEOREM 3: progress' *)
(** Show that progress can also be proved by induction on terms
    instead of induction on typing derivations. *)

Theorem progress' : forall t T,
     <{ empty |-- t \in T }> ->
     value t \/ exists t', t --> t'.
Proof.
  intros t.
  induction t; intros T Ht; auto.
  (* ADMITTED *)
  - (* var *)
    inversion Ht. subst. discriminate H1.
  - (* app *)
    right.
    inversion Ht; clear Ht; subst.
    destruct (IHt1 _ H2).
      + (* t1 is a value *)
        apply canonical_forms_fun in H2; [|assumption].
        destruct H2 as [x [t H2]]; subst.
        destruct (IHt2 _ H4).
        * (* ... and t2 is a value *) eauto.
        * (* ... and t2 can step *) destruct H0 as [t' H0]. eauto.
      + (* t1 can step *)
        destruct H as [t' H]. eauto.
  - (* if *)
    right.
    inversion Ht; clear Ht; subst.
    destruct (IHt1 _ H3).
      + (* t1 is a value *)
        apply canonical_forms_bool in H3; [|assumption].
        destruct H3; subst; eauto.
      + (* t1 can step *)
        destruct H as [t' H]. eauto.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* ###################################################################### *)
(** * Preservation *)

(** FULL: The other half of the type soundness property is the
    preservation of types during reduction.  For this part, we'll need
    to develop some technical machinery for reasoning about variables
    and substitution.  Working from top to bottom (from the high-level
    property we are actually interested in to the lowest-level
    technical lemmas that are needed by various cases of the more
    interesting proofs), the story goes like this:

      - The _preservation theorem_ is proved by induction on a typing
        derivation and case analysis on the step relation,
        pretty much as we did in the \CHAP{Types} chapter.
        The one case that is significantly different is the one for
        the [ST_AppAbs] rule, whose definition uses the substitution
        operation.  To see that this step preserves typing, we need to
        know that the substitution itself does.  So we prove a...

      - _substitution lemma_, stating that substituting a (closed,
        well-typed) term [s] for a variable [x] in a term [t]
        preserves the type of [t].  The proof goes by induction on the
        form of [t] and requires looking at all the different cases in
        the definition of substitition.  This time, for the variables
        case, we discover that we need to deduce from the fact that a
        term [s] has type S in the empty context the fact that [s] has
        type S in every context. For this we prove a...

      - _weakening_ lemma, showing that typing is preserved under
        "extensions" to the context [Gamma].

   To make Rocq happy, though, we need to formalize the story in the
   opposite order, starting with weakening... *)
(* TERSE *)
(** For preservation, we need some technical machinery for reasoning
    about variables and substitution.

      - The _preservation theorem_ is proved by induction on a typing
        derivation and case analysis on the step relation,
        pretty much as we did in the \CHAP{Types} chapter.

        Main novelty: [ST_AppAbs] uses the substitution operation.

        To see that this step preserves typing, we need to know that
        the substitution itself does.  So we prove a... *)
(** *** *)
(**   - _substitution lemma_, stating that substituting a (closed,
        well-typed) term [s] for a variable [x] in a term [t]
        preserves the type of [t].

        The proof goes by induction on the form of [t] and requires
        looking at all the different cases in the definition of
        substitition.

        Tricky case: variables.

        In this case, we need to deduce from the fact that a term [s]
        has type S in the empty context the fact that [s] has type S
        in every context.

        For this we prove a...*)
(** *** *)
(**   - _weakening_ lemma, showing that typing is preserved under
        "extensions" to the context [Gamma]. *)
(** *** *)
(** To make Rocq happy, we need to formalize all this in the opposite
    order... *)
(* /TERSE *)

(* ###################################################################### *)
(** ** The Weakening Lemma *)

(** First, we show that typing is preserved under "extensions" to the
    context [Gamma].  (Recall the definition of "includedin" from
    Maps.v.) *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     <{ Gamma  |-- t \in T }>  ->
     <{ Gamma' |-- t \in T }>.
(* FOLD *)
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.
(* /FOLD *)

(** TERSE: *** *)
(** The following simple corollary is what we actually need below. *)

Lemma weakening_empty : forall Gamma t T,
     <{ empty |-- t \in T }> ->
     <{ Gamma |-- t \in T }>.
(* FOLD *)
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.
(* /FOLD *)

(* ###################################################################### *)
(** ** The Substitution Lemma *)

(** Now we come to the conceptual heart of the proof that reduction
    preserves types -- namely, the observation that _substitution_
    preserves types. *)

(** FULL: Formally, the so-called _substitution lemma_ says this:
    Suppose we have a term [t] with a free variable [x], and suppose
    we've assigned a type [T] to [t] under the assumption that [x] has
    some type [U].  Also, suppose that we have some other term [v] and
    that we've shown that [v] has type [U].  Then, since [v] satisfies
    the assumption we made about [x] when typing [t], we can
    substitute [v] for each of the occurrences of [x] in [t] and
    obtain a new term that still has type [T]. *)
(** TERSE: The _substitution lemma_ says:

    - Suppose we have a term [t] with a free variable [x], and
      suppose we've been able to assign a type [T] to [t] under the
      assumption that [x] has some type [U].

    - Also, suppose that we have some other term [v] and that we've
      shown that [v] has type [U].

    - Then we can substitute [v] for each of the occurrences of
      [x] in [t] and obtain a new term that still has type [T]. *)

(** TERSE: *** *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ empty |-- v \in U }>  ->
  <{ Gamma |-- [x:=v]t \in T }>.
(* TERSE: HIDEFROMHTML *)
(* FULL *)

(** FULL: The substitution lemma can be viewed as a kind of "commutation
    property."  Intuitively, it says that substitution and typing can
    be done in either order: we can either assign types to the terms
    [t] and [v] separately (under suitable contexts) and then combine
    them using substitution, or we can substitute first and then
    assign a type to [ [x:=v] t ]; the result is the same either
    way.

    _Proof_: We show, by induction on [t], that for all [T] and
    [Gamma], if [x|->U; Gamma |-- t \in T] and [|-- v \in U], then
    [Gamma |-- [x:=v]t \in T].

      - If [t] is a variable there are two cases to consider,
        depending on whether [t] is [x] or some other variable.

          - If [t = x], then from the fact that [x|->U; Gamma |-- x \in
            T] we conclude that [U = T].  We must show that [[x:=v]x =
            v] has type [T] under [Gamma], given the assumption that
            [v] has type [U = T] under the empty context.  This
            follows from the weakening lemma.

          - If [t] is some variable [y] that is not equal to [x], then
            we need only note that [y] has the same type under [x|->U;
            Gamma] as under [Gamma].

      - If [t] is an abstraction [\y:S, t0], then [T = S->T1] and
        the IH tells us, for all [Gamma'] and [T0], that if [x|->U;
        Gamma' |-- t0 \in T0], then [Gamma' |-- [x:=v]t0 \in T0].
        Moreover, by inspecting the typing rules we see it must be
        the case that [y|->S; x|->U; Gamma |-- t0 \in T1].

        The substitution in the conclusion behaves differently
        depending on whether [x] and [y] are the same variable.

        First, suppose [x = y].  Then, by the definition of
        substitution, [[x:=v]t = t], so we just need to show [Gamma |--
        t \in T].  Using [T_Abs], we need to show that [y|->S; Gamma
        |-- t0 \in T1]. But we know [y|->S; x|->U; Gamma |-- t0 \in T1],
        and the claim follows since [x = y].

        Second, suppose [x <> y]. Again, using [T_Abs],
        we need to show that [y|->S; Gamma |-- [x:=v]t0 \in T1].
        Since [x <> y], we have
        [y|->S; x|->U; Gamma = x|->U; y|->S; Gamma]. So
        we have [x|->U; y|->S; Gamma |-- t0 \in T1]. Then, the
        the IH applies (taking [Gamma' = y|->S; Gamma]), giving us
        [y|->S; Gamma |-- [x:=v]t0 \in T1], as required.

      - If [t] is an application [t1 t2], the result follows
        straightforwardly from the definition of substitution and the
        induction hypotheses.

      - The remaining cases are similar to the application case. *)
(* /FULL *)

(* FOLD *)
Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.
(* /FOLD *)

(* FULL *)
(** One technical subtlety in the statement of the above lemma is that
    we assume [v] has type [U] in the _empty_ context -- in other
    words, we assume [v] is closed.  (Since we are using a simple
    definition of substition that is not capture-avoiding, it doesn't
    make sense to substitute non-closed terms into other terms.
    Fortunately, closed terms are all we need!)
 *)
(* /FULL *)

(* FULL *)
(* EX3A (substitution_preserves_typing_from_typing_ind) *)
(* GRADE_THEOREM 3: substitution_preserves_typing_from_typing_ind *)
(** Show that substitution_preserves_typing can also be
    proved by induction on typing derivations instead
    of induction on terms. *)
Lemma substitution_preserves_typing_from_typing_ind : forall Gamma x U t v T,
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ empty |-- v \in U }>   ->
  <{ Gamma |-- [x:=v]t \in T }>.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
 (* ADMITTED *)
  - (* T_Var *)
    rename x0 into y.
    destruct (eqb_spec x y) as [Hxy|Hxy]; subst.
    + (* x = y *)
      rewrite update_eq in H.
      injection H as H. subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var.
      rewrite update_neq in H; assumption.
  - (* T_Abs *)
    rename x0 into y. subst.
    destruct (eqb_spec x y) as [Hxy|Hxy]; apply T_Abs.
    + (* x=y *)
      subst. rewrite update_shadow in Ht. assumption.
    + (* x <> y *)
      subst. apply IHHt.
      rewrite update_permute; auto.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** ** Main Theorem *)

(* HIDEFROMADVANCED *)
(** We now have the ingredients we need to prove preservation: if a
    closed, well-typed term [t] has type [T] and takes a step to [t'],
    then [t'] is also a closed term with type [T].  In other words,
    the small-step reduction relation preserves types. *)

(* /HIDEFROMADVANCED *)
Theorem preservation : forall t t' T,
  <{ empty |-- t \in T }> ->
  t --> t'  ->
  <{ empty |-- t' \in T }>.

(** FULL: _Proof_: By induction on the derivation of [|-- t \in T].

    - We can immediately rule out [T_Var], [T_Abs], [T_True], and
      [T_False] as final rules in the derivation, since in each of these
      cases [t] cannot take a step.

    - If the last rule in the derivation is [T_App], then [t = t1 t2],
      and there are subderivations showing that [|-- t1 \in T2->T] and
      [|-- t2 \in T2] plus two induction hypotheses: (1) [t1 --> t1']
      implies [|-- t1' \in T2->T] and (2) [t2 --> t2'] implies [|-- t2'
      \in T2].  There are now three subcases to consider, one for
      each rule that could be used to show that [t1 t2] takes a step
      to [t'].

        - If [t1 t2] takes a step by [ST_App1], with [t1] stepping to
          [t1'], then, by the first IH, [t1'] has the same type as
          [t1] ([|-- t1' \in T2->T]), and hence by [T_App] [t1' t2] has
          type [T].

        - The [ST_App2] case is similar, using the second IH.

        - If [t1 t2] takes a step by [ST_AppAbs], then [t1 =
          \x:T0,t0] and [t1 t2] steps to [[x0:=t2]t0]; the desired
          result now follows from the substitution lemma.

    - If the last rule in the derivation is [T_If], then [t = if
      t1 then t2 else t3], with [|-- t1 \in Bool], [|-- t2 \in T1], and
      [|-- t3 \in T1], and with three induction hypotheses: (1) [t1 -->
      t1'] implies [|-- t1' \in Bool], (2) [t2 --> t2'] implies [|-- t2'
      \in T1], and (3) [t3 --> t3'] implies [|-- t3' \in T1].

      There are again three subcases to consider, depending on how [t]
      steps.

        - If [t] steps to [t2] or [t3] by [ST_IfTrue] or
          [ST_IfFalse], the result is immediate, since [t2] and [t3]
          have the same type as [t].

        - Otherwise, [t] steps by [ST_If], and the desired
          conclusion follows directly from the first induction
          hypothesis. *)

(* FOLD *)
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
Qed.
(* /FOLD *)

(* FULL *)
(* EX2M! (subject_expansion_stlc) *)
(** An exercise in the \CHAP{Types} chapter asked about the _subject
    expansion_ property for the simple language of arithmetic and
    boolean expressions.  This property did not hold for that language,
    and it also fails for STLC.  That is, it is not always the case that,
    if [t --> t'] and [empty |-- t' \in T], then [empty |-- t \in T].
    Show this by giving a counter-example that does _not involve
    conditionals_. *)

(* SOLUTION *)
(*  For example,
    [((\a:Bool->Bool, \y:Bool, y) true)] is ill typed, but it evaluates
    to the well-typed term [\y:Bool, y], *)
(* /SOLUTION *)

Theorem not_subject_expansion:
  exists t t' T, t --> t' /\ <{ empty |-- t' \in T }> /\ ~ <{ empty |-- t \in T }>.
Proof.
  (* Note: Write "exists <{ ... }>" to use STLC term notation and
     exists <{{ ... }}> to use STCL type notation.
   *)
  (* ADMITTED *)
  exists <{ (\x:(Bool -> Bool), \y:Bool, y) true }>.
  exists <{ \y:Bool, y }>.
  exists <{{ Bool -> Bool }}>.
  split; [ | split].
  * apply ST_AppAbs. apply v_true.
  * apply T_Abs. apply T_Var. reflexivity.
  * intro HT. inversion HT; subst.
    inversion H2; subst.
    inversion H4.
Qed.
(* /ADMITTED *)

(* HIDE *)
(* Alternative formulation. *)
Theorem not_subject_expansion_alt:
  ~ (forall t t' T, t --> t' /\ <{ empty |-- t' \in T }> -> <{ empty |-- t \in T }>).
Proof.
  (* ADMITTED *)
  intro HSE.
  assert (HT: <{ empty |-- (\x:(Bool -> Bool), \y:Bool, y) true \in Bool -> Bool}> ).
  { apply HSE with (t' := <{ \y:Bool, y }>).
    split.
    { apply ST_AppAbs. apply v_true. }
    { apply T_Abs. apply T_Var. reflexivity. } }
  inversion HT.
  inversion H2.
  rewrite <- H10 in H4.
  inversion H4.
Qed.
(* /ADMITTED *)
(* /HIDE *)

(* GRADE_MANUAL 2: subject_expansion_stlc *)
(** [] *)
(* /FULL *)

(* FULL *)
(* ###################################################################### *)
(** * Type Soundness *)

(* EX2? (type_soundness) *)
(** Put progress and preservation together and show that a well-typed
    term can _never_ reach a stuck state.  *)

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary type_soundness : forall t t' T,
  <{ empty |-- t \in T }> ->
  t -->* t' ->
  ~(stuck t').
(* FOLD *)
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  (* ADMITTED *)
  - (* multi_refl *)
    apply progress in Hhas_type.
    destruct Hhas_type; auto.
  - (* multi_step *)
    eapply preservation in Hhas_type.
    + apply IHHmulti; eassumption.
    + assumption. Qed.
(* /ADMITTED *)
(* /FOLD *)
(** [] *)

(* ###################################################################### *)
(** * Uniqueness of Types *)

(* EX3 (unique_types) *)
(** Another nice property of the STLC is that types are unique: a
    given term (in a given context) has at most one type. *)

Theorem unique_types : forall Gamma e T T',
  <{ Gamma |-- e \in T }> ->
  <{ Gamma |-- e \in T' }> ->
  T = T'.
Proof.
  (* ADMITTED *)
  intros Gamma e T T' Htyp. generalize dependent T'.
  induction Htyp; intros T' Htyp'; inversion Htyp'; subst; auto.
  - (* T_Var *)
    rewrite H in H2. injection H2 as H2. assumption.
  - (* T_Abs *)

    apply IHHtyp in H4. subst. reflexivity.
  - (* T_App *)
    apply IHHtyp1 in H2. injection H2 as H2. assumption.
Qed.
(* /ADMITTED *)
(** [] *)

(* INSTRUCTORS: Since weakening suffices for the preservation theorem,
   this whole section got demoted to optional when we changed to the
   weakening presentation. But it introduces some useful terminology,
   so keeping it as such. *)
(* ###################################################################### *)
(** * Context Invariance (Optional) *)

(** Another standard technical lemma associated with typed languages
    is _context invariance_. It states that typing is preserved under
    "inessential changes" to the context [Gamma] -- in particular,
    changes that do not affect any of the free variables of the
    term. In this section, we establish this property for our system,
    introducing some other standard terminology on the way.  *)

(** First, we need to define the _free variables_ in a term -- i.e.,
    variables that are used in the term in positions that are _not_ in
    the scope of an enclosing function abstraction binding a variable
    of the same name.

    More technically, a variable [x] _appears free in_ a term _t_ if
    [t] contains some occurrence of [x] that is not under an
    abstraction labeled [x]. For example:
      - [y] appears free, but [x] does not, in [\x:T->U, x y]
      - both [x] and [y] appear free in [(\x:T->U, x y) x]
      - no variables appear free in [\x:T->U, \y:T, x y]

      Formally: *)

Inductive appears_free_in (x : string) : tm -> Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 t2}>
  | afi_app2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 t2}>
  | afi_abs : forall y T1 t1,
      y <> x  ->
      appears_free_in x t1 ->
      appears_free_in x <{\y:T1, t1}>
  | afi_if1 : forall t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if2 : forall t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if3 : forall t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x <{if t1 then t2 else t3}>.

Hint Constructors appears_free_in : core.

(** The _free variables_ of a term are just the variables that appear
    free in it.  This gives us another way to define _closed_ terms --
    arguably a better one, since it applies even to ill-typed
    terms.  Indeed, this is the standard definition of the term
    "closed." *)

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(** Conversely, an _open_ term is one that may contain free
    variables.  (I.e., every term is an open term; the closed terms
    are a subset of the open ones.  "Open" precisely means "possibly
    containing free variables.") *)

(* EX1? (afi) *)
(** (Officially optional, but strongly recommended!) In the space
    below, write out the rules of the [appears_free_in] relation in
    informal inference-rule notation.  (Use whatever notational
    conventions you like -- the point of the exercise is just for you
    to think a bit about the meaning of each rule.)  Although this is
    a rather low-level, technical definition, understanding it is
    crucial to understanding substitution and its properties, which
    are really the crux of the lambda-calculus. *)

(* SOLUTION *)
(* (no solution yet) *)
(* LATER: Fill in an official solution *)
(* /SOLUTION *)

(* GRADE_MANUAL 1: afi *)
(** [] *)

(** Next, we show that if a variable [x] appears free in a term [t],
    and if we know [t] is well typed in context [Gamma], then it
    must be the case that [Gamma] assigns a type to [x]. *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   <{ Gamma |-- t \in T }> ->
   exists T', Gamma x = Some T'.

(** _Proof_: We show, by induction on the proof that [x] appears free
    in [t], that, for all contexts [Gamma], if [t] is well typed under
    [Gamma], then [Gamma] assigns some type to [x].

    - If the last rule used is [afi_var], then [t = x], and from the
      assumption that [t] is well typed under [Gamma] we have
      immediately that [Gamma] assigns a type to [x].

    - If the last rule used is [afi_app1], then [t = t1 t2] and [x]
      appears free in [t1].  Since [t] is well typed under [Gamma], we
      can see from the typing rules that [t1] must also be, and the IH
      then tells us that [Gamma] assigns [x] a type.

    - Almost all the other cases are similar: [x] appears free in a
      subterm of [t], and since [t] is well typed under [Gamma], we
      know the subterm of [t] in which [x] appears is well typed under
      [Gamma] as well, and the IH gives us exactly the conclusion we
      want.

    - The only remaining case is [afi_abs].  In this case [t =
      \y:T1,t1] and [x] appears free in [t1], and we also know that
      [x] is different from [y].  The difference from the previous
      cases is that, whereas [t] is well typed under [Gamma], its body
      [t1] is well typed under [y|->T1; Gamma], so the IH allows us
      to conclude that [x] is assigned some type by the extended
      context [y|->T1; Gamma].  To conclude that [Gamma] assigns a
      type to [x], we appeal to lemma [update_neq], noting that [x]
      and [y] are different variables. *)

(* EX2 (free_in_context) *)
(** Complete the following proof. *)

Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  induction H as [| | |y T1 t1 H H0 IHappears_free_in| | |];
         intros; try solve [inversion H0; eauto].
  (* ADMITTED *)
  - (* afi_abs *)
    inversion H1; subst; clear H1.
    apply IHappears_free_in in H7.
    rewrite update_neq in H7; assumption. Qed.
(* /ADMITTED *)
(** [] *)

(** From the [free_in_context] lemma, it immediately follows that any
    term [t] that is well typed in the empty context is closed (it has
    no free variables). *)

(* EX2? (typable_empty__closed) *)
Corollary typable_empty__closed : forall t T,
    <{ empty |-- t \in T }> ->
    closed t.
Proof.
  (* ADMITTED *)
  intros. unfold closed. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' Hc].
  discriminate Hc.  Qed.
(* /ADMITTED *)
(** [] *)

(** Finally, we establish _context_invariance_.  It is useful in cases
    when we have a proof of some typing relation [Gamma |-- t \in T],
    and we need to replace [Gamma] by a different context [Gamma'].
    When is it safe to do this?  Intuitively, it must at least be the
    case that [Gamma'] assigns the same types as [Gamma] to all the
    variables that appear free in [t]. In fact, this is the only
    condition that is needed. *)

Lemma context_invariance : forall Gamma Gamma' t T,
     <{ Gamma |-- t \in T }> ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     <{ Gamma' |-- t \in T }>.

(** _Proof_: By induction on the derivation of [Gamma |-- t \in T].

    - If the last rule in the derivation was [T_Var], then [t = x] and
      [Gamma x = T].  By assumption, [Gamma' x = T] as well, and hence
      [Gamma' |-- t \in T] by [T_Var].

    - If the last rule was [T_Abs], then [t = \y:T2, t1], with [T =
      T2 -> T1] and [y|->T2; Gamma |-- t1 \in T1].  The induction
      hypothesis states that for any context [Gamma''], if [y|->T2;
      Gamma] and [Gamma''] assign the same types to all the free
      variables in [t1], then [t1] has type [T1] under [Gamma''].
      Let [Gamma'] be a context which agrees with [Gamma] on the free
      variables in [t]; we must show [Gamma' |-- \y:T2, t1 \in T2 -> T1].

      By [T_Abs], it suffices to show that [y|->T2; Gamma' |-- t1 \in
      T1].  By the IH (setting [Gamma'' = y|->T2;Gamma']), it
      suffices to show that [y|->T2;Gamma] and [y|->T2;Gamma'] agree
      on all the variables that appear free in [t1].

      Any variable occurring free in [t1] must be either [y] or some
      other variable.  [y|->T2; Gamma] and [y|->T2; Gamma'] clearly
      agree on [y].  Otherwise, note that any variable other than [y]
      that occurs free in [t1] also occurs free in [t = \y:T2, t1],
      and by assumption [Gamma] and [Gamma'] agree on all such
      variables; hence so do [y|->T2; Gamma] and [y|->T2; Gamma'].

    - If the last rule was [T_App], then [t = t1 t2], with [Gamma |--
      t1 \in T2 -> T] and [Gamma |-- t2 \in T2].  One induction
      hypothesis states that for all contexts [Gamma'], if [Gamma']
      agrees with [Gamma] on the free variables in [t1], then [t1] has
      type [T2 -> T] under [Gamma']; there is a similar IH for [t2].
      We must show that [t1 t2] also has type [T] under [Gamma'],
      given the assumption that [Gamma'] agrees with [Gamma] on all
      the free variables in [t1 t2].  By [T_App], it suffices to show
      that [t1] and [t2] each have the same type under [Gamma'] as
      under [Gamma].  But all free variables in [t1] are also free in
      [t1 t2], and similarly for [t2]; hence the desired result
      follows from the induction hypotheses. *)

(* EX3? (context_invariance) *)
(** Complete the following proof. *)
Proof.
  intros.
  generalize dependent Gamma'.
  induction H as [| ? x0 ????? | | | |]; intros; auto.
  (* ADMITTED *)
  - (* T_Var *)
    apply T_Var. rewrite <- H0; auto.
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... *)
    destruct (eqb_spec x0 x1); subst.
    + rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + rewrite update_neq; [| assumption].
      rewrite update_neq; [| assumption].
      auto.
  - (* T_App *)
    apply T_App with T2; auto. Qed.
(* /ADMITTED *)
(** [] *)

(** The context invariance lemma can actually be used in place of the
    weakening lemma to prove the crucial substitution lemma stated
    earlier. *)
(* HIDE: BCP 20: Maybe this deserves an exercise?  BCP 21: Nah. People
   can just try it if they really want. *)

(* ###################################################################### *)
(** * Additional Exercises *)

(* EX1? (progress_preservation_statement) *)
(** (Officially optional, but strongly recommended!) Without peeking
    at their statements above, write down the progress and
    preservation theorems for the simply typed lambda-calculus (as Rocq
    theorems).  You can write [Admitted] for the proofs. *)
(* SOONER: At least one person was confused by what to name these. We
   could simplify life by giving the names explicitly and just
   omitting the bodies.  Indeed, once we do that we could autograde
   this by demanding that what they write be identical to what we
   wrote above! Maybe a better way to solve this would be to have the
   following template.  BCP 21: Yes, do this!! *)

(* HIDE *)
(*   Theorem progress' :
    FILL IN HERE
   Proof. apply progress. Qed.
*)
(* /HIDE *)

(* SOLUTION *)
(* See progress and preservation from before. *)
(* /SOLUTION *)

(* GRADE_MANUAL 1: progress_preservation_statement *)
(** [] *)

(* EX2M (stlc_variation1) *)
(** Suppose we add a new term [zap] with the following reduction rule
[[[
                         ---------                  (ST_Zap)
                         t --> zap
]]]
and the following typing rule:
[[[
                      -------------------           (T_Zap)
                      Gamma |-- zap \in T
]]]
    Which of the following properties of the STLC remain true in
    the presence of these rules?  For each property, write either
    "remains true" or "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* SOLUTION *)
        - Becomes false. For instance [(if true then false else true) --> false]
          and [(if true then false else true) --> zap].
(* /SOLUTION *)
      - Progress
(* SOLUTION *)
        - Remains true. Every term (including [zap]) can take a step to [zap].
(* /SOLUTION *)
      - Preservation
(* SOLUTION *)
        - Remains true. [zap] can have any type.
(* /SOLUTION *)
*)

(* GRADE_MANUAL 2: stlc_variation1 *)
(** [] *)

(* EX2M (stlc_variation2) *)
(** Suppose instead that we add a new term [foo] with the following
    reduction rules:
[[[
                       -----------------                (ST_Foo1)
                       (\x:A, x) --> foo

                         ------------                   (ST_Foo2)
                         foo --> true
]]]
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* SOLUTION *)
        - Becomes false. The term [(\x:Bool, x) true] might step
          to either [true] by the rule ST_AppAbs or
          to [foo true] by the rule ST_App1 and ST_Foo1.
(* /SOLUTION *)
      - Progress
(* SOLUTION *)
        - Remains true. We are only adding to the step relation, and
          this can never damage progress.
(* /SOLUTION *)
      - Preservation
(* SOLUTION *)
        - Becomes false. For example,
          [|-- \x:Bool,x \in Bool->Bool] and [(\x:Bool,x) --> foo] by (ST_Foo1),
          but, since we have no typing rules for foo, we cannot prove that
          [|-- foo \in Bool->Bool].
(* /SOLUTION *)
*)

(* GRADE_MANUAL 2: stlc_variation2 *)
(** [] *)

(* EX2M (stlc_variation3) *)
(** Suppose instead that we remove the rule [ST_App1] from the [step]
    relation. Which of the following properties of the STLC remain
    true in the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* SOLUTION *)
        - Remains true. Removing reduction rules can only make [step]
          more deterministic.
(* /SOLUTION *)
      - Progress
(* SOLUTION *)
        - Becomes false. For example,
          [((\x:Bool->Bool, \y:Bool->Bool, x) (\z:Bool,z)) (\z:Bool,z)]
          is well typed, but stuck.
(* /SOLUTION *)
      - Preservation
(* SOLUTION *)
        - Remains true. Removing reduction rules can't break preservation.
(* /SOLUTION *)
*)

(* GRADE_MANUAL 2: stlc_variation3 *)
(** [] *)

(* EX2? (stlc_variation4) *)
(** Suppose instead that we add the following new rule to the
    reduction relation:
[[[
            ----------------------------------        (ST_FunnyIfTrue)
            (if true then t1 else t2) --> true
]]]
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* SOLUTION *)
        - Becomes false, for instance:
          [(if true then false else false) --> false] and
          [(if true then false else false) --> true]
(* /SOLUTION *)
      - Progress
(* SOLUTION *)
        - Remains true. We are only adding to the step relation, and
          this can never damage progress.
(* /SOLUTION *)
      - Preservation
(* SOLUTION *)
        - Becomes false. For example,
          [|-- if true then (\x:Bool,x) else (\x:Bool,x) \in Bool->Bool]
          and [(if true then (\x:Bool,x) else (\x:Bool,x)) --> true]
          but it's not the case that [|-- true \in Bool -> Bool].
(* /SOLUTION *)
*)
(** [] *)

(* EX2? (stlc_variation5) *)
(** Suppose instead that we add the following new rule to the typing
    relation:
[[[
                 Gamma |-- t1 \in Bool->Bool->Bool
                     Gamma |-- t2 \in Bool
                 ---------------------------------       (T_FunnyApp)
                    Gamma |-- t1 t2 \in Bool
]]]
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* SOLUTION *)
        - Remains true. We are only adding to the typing relation, and
          this can never damage determinism of [step].
(* /SOLUTION *)
      - Progress
(* SOLUTION *)
        - Remains true. Since the new rule still requires that [t1] is
          a function we can still apply ST_AppAbs to show progress.
(* /SOLUTION *)
      - Preservation
(* SOLUTION *)
        - Becomes false. For example,
          [|-- \x:Bool, \y:Bool, x true \in Bool]
          and [(\x:Bool, \y:Bool, x) true --> \y:Bool, true]
          but it's not the case that [|-- \y:Bool, true \in Bool]
(* /SOLUTION *)
*)
(** [] *)

(* EX2? (stlc_variation6) *)
(** Suppose instead that we add the following new rule to the typing
    relation:
[[[
                    Gamma |-- t1 \in Bool
                    Gamma |-- t2 \in Bool
                    ------------------------            (T_FunnyApp')
                    Gamma |-- t1 t2 \in Bool
]]]
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* SOLUTION *)
        - Remains true. We are not changing the [step] relation.
(* /SOLUTION *)
      - Progress
(* SOLUTION *)
        - Becomes false. For instance, [true true] is a term that
          becomes typable (at type [Bool]), but which is stuck.
(* /SOLUTION *)
      - Preservation
(* SOLUTION *)
        - Remains true. There are 3 ways [t1 t2] can reduce. For
          [ST_App1] and [ST_App2] we can still apply the induction
          hypothesis. In order to reduce [t1 t2] using [ST_AppAbs]
          [t1] would need to be a function, but functions don't have
          type [Bool].
(* /SOLUTION *)
*)
(** [] *)

(* EX2? (stlc_variation7) *)
(** Suppose we add the following new rule to the typing relation
    of the STLC:
[[[
                         ---------------------- (T_FunnyAbs)
                         |-- \x:Bool,t \in Bool
]]]
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* SOLUTION *)
        - Remains true. We're not changing the [step] relation.
(* /SOLUTION *)
      - Progress
(* SOLUTION *)
        - Becomes false. For instance [if (\x:Bool,false) then false
          else false] is a term that would become typable, although it
          is stuck.
(* /SOLUTION *)
      - Preservation
(* SOLUTION *)
        - Remains true. [\x:Bool,t] doesn't step.
(* /SOLUTION *)
*)
(** [] *)
(* HIDE *)
Module StlcVar1.

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      <{ Gamma |-- x \in T1 }>
  | T_Abs : forall Gamma x T2 T1 t1,
      <{ x |-> T2 ; Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- \x:T2, t1 \in T2 -> T1 }>
  | T_App : forall T1 T2 Gamma t1 t2,
      <{ Gamma |-- t1 \in T2 -> T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- t1 t2 \in T1 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall t1 t2 t3 T1 Gamma,
      <{ Gamma |-- t1 \in Bool }> ->
      <{ Gamma |-- t2 \in T1 }> ->
      <{ Gamma |-- t3 \in T1 }> ->
      <{ Gamma |-- if t1 then t2 else t3 \in T1 }>
  | T_Strange : forall x t1,
      <{ empty |-- \x:Bool, t1 \in Bool }>

where "<{ Gamma '|--' t '\in' T }>"  := (has_type Gamma t T).

Hint Constructors has_type : core.

Theorem no_progress : exists t T,
     <{ empty |-- t \in T }> /\
     ~value t /\ ~(exists t', t --> t').
Proof.
  exists <{if (\x:Bool, false) then false else false}>.
  exists <{{ Bool }}>. split; [| split].
  - (* has_type *) eauto.
  - (* ~value *) intro Hc. inversion Hc.
  - (* ~steps *) intro Hc. destruct Hc as [x Hx].
    inversion Hx. subst.
    inversion H3.
Qed.

End StlcVar1.
(* /HIDE *)
(* /FULL *)

(* TERSE: HIDEFROMHTML *)
End STLCProp.
(* TERSE: /HIDEFROMHTML *)

(* FULL *)
(* ###################################################################### *)
(* ###################################################################### *)
(** ** Exercise: STLC with Arithmetic *)

(* SOONER: There is a better version of this whole exercise in the Git
   repo commit c54534533ff94cc5869e768b78d126deab91214c.  Copy it over! *)
(* SOONER: BCP 21: It's a shame that there are no binding constructs here! *)

(** To see how the STLC might function as the core of a real
    programming language, let's extend it with a concrete base
    type of numbers and some constants and primitive
    operators. *)

Module STLCArith.
Import STLC.

(** To types, we add a base type of natural numbers (and remove
    booleans, for brevity). *)

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty.

(** To terms, we add natural number constants, along with
    successor, predecessor, multiplication, and zero-testing. *)

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_const  : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0 : tm -> tm -> tm -> tm.

(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template stlc_ty *)
(* INSTRUCTORS: allow (global) identifiers,
  e.g. just a local variable or Fooo.bar.baz to appear as types. *)
(* INSTRUCTORS: quotation for shifting into stlc_ty parsing mode *)
Notation "<{{ x }}>" := x (x custom stlc_ty).

Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) : stlc_scope.
(* INSTRUCTORS: to extend this template, add new type constructs below. *)

(* NOTATION: SAZ 2024 - I recommend following the pattern below for all grammars *)
(* INSTRUCTORS: escape to arbitrary Rocq constr notation *)
Notation "$( t )" := t (in custom stlc_ty at level 0, t constr) : stlc_scope.
(* INSTRUCTORS: End Definition of template stlc_ty *)
(* INSTRUCTORS: ------------------------------------------------------------- *)

(* INSTRUCTORS: stcl_tm ----------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template stlc_tm *)
Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.

Notation "x y" := (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.
(* INSTRUCTORS: End Definition of template stlc_tm *)
(* INSTRUCTORS: ------------------------------------------------------------- *)

(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template stlc_nat *)
Notation "'Nat'" := Ty_Nat (in custom stlc_ty at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc_tm at level 10,
                                     x custom stlc_tm at level 0) : stlc_scope.
Notation "'pred' x" := (tm_pred x) (in custom stlc_tm at level 10,
                                     x custom stlc_tm at level 0) : stlc_scope.
Notation "x * y" := (tm_mult x y) (in custom stlc_tm at level 95,
                                      right associativity) : stlc_scope.
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc_tm at level 0,
                    x custom stlc_tm at level 0,
                    y custom stlc_tm at level 0,
                    z custom stlc_tm at level 0) : stlc_scope.

Coercion tm_const : nat >-> tm.
(* INSTRUCTORS: End Definition of template stlc_nat *)
(* INSTRUCTORS: ------------------------------------------------------------- *)

(* HIDE *)
Check <{ \x : Nat, x }>.
Check <{ if0 x then x else x }>.
Check <{ if0 y x then x else x }>.
Check <{ if0 (y x) then x else x }>.
Check <{ x * y * z }>.
Check <{ succ pred x }>.
Check <{ succ x y }>.
Check <{ x (succ y) }>.
Check <{ x * y z}>.
Check <{ x * y (succ z)}>.
Check <{ z x y }>.
Check <{ z x * y }>.
(* /HIDE *)

(** In this extended exercise, your job is to finish formalizing the
    definition and properties of the STLC extended with arithmetic.
    Specifically:

    Fill in the core definitions for STLCArith, by starting with the rules
    and terms which are the same as STLC.  Then prove the key lemmas and
    theorems we provide.  You will need to define and prove helper lemmas,
    as before.

    It will be necessary to also fill in "Reserved Notation", "Notation",
    and "Hint Constructors".

    Hint: If you get an error "STLC.tm" found instead of term "tm" then Rocq
    is picking up the old notation for ie: subst instead of the new
    notation for STLCArith, so you need to overwrite the old with the
    notation before you can use it.

    Make sure Rocq accepts the whole file before submitting. *)


(* EX5 (STLCArith.subst) *)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm
  (* ADMITDEF *) :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x := s] t1}>
  | <{t1 t2}> =>
    <{ ([x := s] t1) ([x := s] t2) }>
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
    <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).
(* /ADMITDEF *)

(** (You'll need to remove the period at the end of this
    definition and add
<<
    where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).
>>
    when you fill it in.) *)

Inductive value : tm -> Prop :=
  (* SOLUTION *)
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>

  (* Numbers are values: *)
  | v_nat : forall n : nat,
      value <{n}>
(* /SOLUTION *)
.

Hint Constructors value : core.

(* HIDEFROMHTML *)
Reserved Notation "t '-->' t'" (at level 40).
(* /HIDEFROMHTML *)

Inductive step : tm -> tm -> Prop :=
  (* SOLUTION *)
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  (* numbers *)
  | ST_Succ : forall t1 t1',
         t1 --> t1' ->
         <{succ t1}> --> <{succ t1'}>
  | ST_SuccNat : forall n : nat,
(* SOONER: BCP 20: At least one student had trouble with this exercise
   because they didn't understand how to put in the extra {...} in the
   next line... We need, at a minimum, some better explanation
   someplace!  BCP 21: And maybe we should consider backporting the
   {...} antiquoting syntax to the Hoare chapters...!
   SAZ 2024: I ported this to use the new antiquoting syntax and
   did backport it to Hoare.
 *)
         <{succ n}> --> <{ $(1 + n) }>
  | ST_Pred : forall t1 t1',
         t1 --> t1' ->
         <{pred t1}> --> <{pred t1'}>
  | ST_PredNat : forall n:nat,
         <{pred n}> --> <{ $(n - 1) }>
  | ST_Mulconsts : forall n1 n2 : nat,
         <{n1 * n2}> --> <{ $(n1 * n2) }>
  | ST_Mult1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 * t2}> --> <{t1' * t2}>
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 * t2}> --> <{v1 * t2'}>
  | ST_If0 : forall t1 t1' t2 t3,
         t1 --> t1' ->
         <{if0 t1 then t2 else t3}> --> <{if0 t1' then t2 else t3}>
  | ST_If0_Zero : forall t2 t3,
         <{if0 $(0) then t2 else t3}> --> t2
  | ST_If0_Nonzero : forall n t2 t3,
         <{if0 $(S n) then t2 else t3}> --> t3
  (* /SOLUTION *)
where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

(* An example *)

Example Nat_step_example : exists t,
<{(\x: Nat, \y: Nat, x * y ) $(3) $(2) }> -->* t.
Proof. (* ADMITTED *)
  eexists; normalize.
Qed.
(* /ADMITTED *)

(* SOONER *)
(* ########################################### *)
(* Reduction Example: *)

(* SOONER: something to replace fact *)
(* /SOONER *)

(* ########################################### *)

(* Typing *)

Definition context := partial_map ty.

Inductive has_type : context -> tm -> ty -> Prop :=
  (* SOLUTION *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1  ->
      <{ Gamma |-- x \in T1 }>
  | T_Abs : forall Gamma x T1 T2 t1,
      <{ x |-> T2 ; Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- \x:T2, t1 \in T2 -> T1 }>
  | T_App : forall T1 T2 Gamma t1 t2,
      <{ Gamma |-- t1 \in T2 -> T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- t1 t2 \in T1 }>
  (* typing rules for arithmetic expressions *)
  | T_Nat : forall Gamma (n : nat),
      <{ Gamma |-- n \in Nat }>
  | T_Succ : forall Gamma t1,
      <{ Gamma |-- t1 \in Nat }> ->
      <{ Gamma |-- succ t1 \in Nat }>
  | T_Pred : forall Gamma t1,
      <{ Gamma |-- t1 \in Nat }> ->
      <{ Gamma |-- pred t1 \in Nat }>
  | T_Mult : forall Gamma t1 t2,
      <{ Gamma |-- t1 \in Nat }> ->
      <{ Gamma |-- t2 \in Nat }> ->
      <{ Gamma |-- t1 * t2 \in Nat }>
  | T_If0 : forall Gamma t1 t2 t3 T0,
      <{ Gamma |-- t1 \in Nat }> ->
      <{ Gamma |-- t2 \in T0 }> ->
      <{ Gamma |-- t3 \in T0 }> ->
      <{ Gamma |-- if0 t1 then t2 else t3 \in T0 }>
  (* /SOLUTION *)
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T).

Hint Constructors has_type : core.

(* An example *)

Example Nat_typing_example :
   <{ empty |-- ( \x: Nat, \y: Nat, x * y ) $(3) $(2) \in Nat }>.
Proof.
  (* ADMITTED *)
  eauto 10.
Qed.
(* /ADMITTED *)

(** [] *)

(* ###################################################################### *)
(** ** The Technical Theorems *)

(** The next lemmas are proved _exactly_ as before. *)

(* EX4 (STLCArith.weakening) *)
Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     <{ Gamma  |-- t \in T }> ->
     <{ Gamma' |-- t \in T }>.
Proof. (* ADMITTED *)
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed. (* /ADMITTED *)

(* SOLUTION *)
Lemma weakening_empty : forall Gamma t T,
     <{ empty |-- t \in T }>  ->
     <{ Gamma |-- t \in T }>.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ empty |-- v \in U }>  ->
  <{ Gamma |-- [x:=v]t \in T }>.
Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into T.
    destruct (eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.
(* /SOLUTION *)

(** [] *)

(* ############################################ *)
(* Preservation *)
(* Hint: You will need to define and prove the same helper lemmas we used before *)

(* EX4 (STLCArith.preservation) *)
Theorem preservation : forall t t' T,
  <{ empty |-- t \in T }> ->
  t --> t'  ->
  <{ empty |-- t' \in T }>.
Proof with eauto. (* ADMITTED *)
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
Qed. (* /ADMITTED *)

(** [] *)

(* ############################################### *)
(* Progress *)

(* LATER: auto can do even more if we "Hint Constructors ex", but
   maybe it's cleaner not to? *)
(* EX4 (STLCArith.progress) *)
Theorem progress : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.
Proof with eauto. (* ADMITTED *)
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma...
  - (* T_Var *)
    discriminate H.
  - (* T_App *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t1 is a value *)
        (* since t1 is a value and has an arrow type,
           it must be an abs *)
        destruct H; subst...
        (* and therefore can't be a nat *)
        inversion Ht1.
      * (* t2 steps *)
        destruct H0 as [t2' Hstp].
        exists <{t1 t2'}>...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      exists <{t1' t2}>...
  - (* T_Succ *)
    right. destruct IHHt...
    + (* t is a value *)
      destruct H; subst.
      * inversion Ht.
      * exists (tm_const (S n))...
    + (* t steps *)
      destruct H as [t' Hstp]. exists <{succ t'}>...
  - (* T_Pred *)
    right. destruct IHHt...
    + (* t is a value *)
      destruct H; subst.
      * inversion Ht.
      * exists (tm_const (n - 1))...
    + (* t steps *)
      destruct H as [t' Hstp]. exists <{pred t'}>...
  - (* T_Mult *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is a value *)
        destruct H; subst.
        -- inversion Ht1.
        -- destruct H0; subst.
           ++ inversion Ht2.
           ++ exists (tm_const (mult n n0))...
      * (* t2 steps *)
        destruct H0 as [t' Hstp]. exists <{t1*t'}>...
    + (* t1 steps *)
      destruct H as [t' Hstp]. exists <{t'*t2}>...
  - (* T_If0 *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct H; subst.
      * inversion Ht1.
      * destruct n as [|n'].
        -- (* n = 0 *) exists t2...
        -- (* n = S n' *) exists t3...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      exists <{if0 t1' then t2 else t3}>...  Qed.
(* /ADMITTED *)
(** [] *)

End STLCArith.
(* /FULL *)

(* LATER:

    (a) Is there a type T that makes
    x:T |-- if0 ((\x:nat, pred x) x,fst) then x.snd else (x.fst, x.fst) : (nat * nat)
    provable? If so, what is it?
    Answer: Yes: T = nat * (nat * nat).
    (b) Are there types S and T that make
    empty |-- \x:T, \y:T, x y : S
    provable? If so, what are they?
    Answer: No; it would have to be the case that T = T -> S, but there can be no such (nite) type
    T.

    -----------------------

    (a) Suppose we add a term foo with the following evaluation rules:
    (\x:A, x) --> foo (ST_Foo1)
    foo --> 0 (ST_Foo2)
    Do progress and preservation continue to hold after this change, or does one (or do both) fail?
    Why?
    Answer: Preservation fails, since we have no typing rules for foo but \x:A, x has type A!A.
    Progress still holds: we are only adding to the step relation, and this can never damage progress.
    (b) Suppose we add a term zap, with the following evaluation rule
    t --> zap (ST_Zap)
    and the following typing rule:
    Gamma |-- zap : T (T_Zap)
    Do progress and preservation continue to hold after this change, or does one (or do both) fail?
    Why?
    Answer: Both properties continue to hold. Progress holds trivially: every term can take a step to
    zap! Preservation holds because zap can have any type.
    (c) Suppose we change ST_AppAbs to the following rule:
    (\x:T, t12) t2 --> [x:=t2]t12 (ST_AppAbs')
    Do progress and preservation continue to hold after this change, or does one (or do both) fail?
    Why?
    Answer: Both properties continue to hold. (Substitution preserves typing irrespective of whether
    the term being substituted into another term is a value or not.)
*)
