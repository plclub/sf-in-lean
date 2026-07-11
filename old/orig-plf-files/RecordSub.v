(** * RecordSub: Subtyping with Records *)

(* SOONER: From jesper.oqvist@cs.lth.se

Hi Professor Pierce,

I have been working through the exercises in Software Foundations and
completed the main chapters last week. I have learned a lot from the
book, and am very grateful that you share it freely online! Thank you!

In the RecordSub chapter I was intrigued by the comment about removing
the well-formedness conditions for records, so I tried it. To my
surprise it worked without much difficulty. Did I misunderstand the
exercise? I just commented out record_ty, record_tm, well_formed_ty,
subtype__wf, wf_rcd_lookup, has_type__wf, step_preserves_record_tm, and
then deleted the few uses of them, and made some small adjustments to
the proofs to make the go through. Did I delete too much? I have
attached my initial solution in case you want to take a look at it.

[His solution file is in BCP's email :-)]
*)
(** In this chapter, we combine two significant extensions of the pure
    STLC -- records (from chapter \CHAP{Records}) and subtyping (from
    chapter \CHAP{Sub}) -- and explore their interactions.  Most of the
    concepts have already been discussed in those chapters, so the
    presentation here is somewhat terse.  We just comment where things
    are nonstandard. *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
(* TERSE: /HIDEFROMHTML *)

Module RecordSub.

(* ###################################################### *)
(** * Core Definitions *)

(* ################################### *)
(** *** Syntax *)

Inductive ty : Type :=
  (* proper types *)
  | Ty_Top   : ty
  | Ty_Base  : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  (* record types *)
  | Ty_RNil : ty
  | Ty_RCons : string -> ty -> ty -> ty.

Inductive tm : Type :=
  (* proper terms *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_rproj : tm -> string -> tm
  (* record terms *)
  | tm_rnil :  tm
  | tm_rcons : string -> tm -> tm -> tm.

Declare Custom Entry stlc.
Declare Custom Entry stlc_ty.

(* INSTRUCTORS: Begin Modified Copy of template stlc_fun (modified to use grammar stlc_ty) *)
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.
(* INSTRUCTORS: End Modified Copy of template stlc_fun *)

(* INSTRUCTORS: Begin Copy of template stlc_constr *)
Notation "{ x }" := x (in custom stlc at level 1, x constr).
(* INSTRUCTORS: End Copy of template stlc_constr *)

(* INSTRUCTORS: Begin Modified Copy of stlc_base (modified to us stlc_ty) *)
Notation "'Base' x" := (Ty_Base x) (in custom stlc_ty at level 0).
(* INSTRUCTORS: End Copy of stlc_base(modified to us stlc_ty) *)

(* INSTRUCTORS: Begin Copy of stlc_record *)
Notation "  l ':' t1  '::' t2" := (Ty_RCons l t1 t2) (in custom stlc_ty at level 3, right associativity).
Notation " l := e1 '::' e2" := (tm_rcons l e1 e2) (in custom stlc at level 3, right associativity).
Notation "'nil'" := (Ty_RNil) (in custom stlc_ty).
Notation "'nil'" := (tm_rnil) (in custom stlc).
Notation "o --> l" := (tm_rproj o l) (in custom stlc at level 0).
(* INSTRUCTORS: End Copy of stlc_record *)

(* INSTRUCTORS: Begin Modified Copy of stlc_top (modified to use grammar stlc_ty) *)
Notation "'Top'" := (Ty_Top) (in custom stlc_ty at level 0).
(* INSTRUCTORS: End Modified Copy of stlc_top *)


(* ################################### *)
(** *** Well-Formedness *)

(** The syntax of terms and types is a bit too loose, in the sense
    that it admits things like a record type whose final "tail" is
    [Top] or some arrow type rather than [Nil].  To avoid such cases,
    it is useful to assume that all the record types and terms that we
    see will obey some simple well-formedness conditions. *)

(* SOONER: An interesting technical question is whether the basic properties
    of the system -- progress and preservation -- remain true if we
    drop these conditions.  I believe they do, and I would encourage
    motivated readers to try to check this by dropping the conditions
    from the definitions of typing and subtyping and adjusting the
    proofs in the rest of the chapter accordingly.  This is not a
    trivial exercise (or I'd have done it!), but it should not involve
    changing the basic structure of the proofs.  If someone does do
    it, please let me know. --BCP 5/16. *)

Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty <{{ nil }}>
  | RTcons : forall i T1 T2,
        record_ty <{{ i : T1 :: T2 }}>.

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm <{ nil }>
  | rtcons : forall i t1 t2,
        record_tm <{ i := t1 :: t2 }>.

Inductive well_formed_ty : ty -> Prop :=
  |  wfTop :
        well_formed_ty <{{ Top }}>
  | wfBase : forall (i : string),
        well_formed_ty <{{ Base i }}>
  | wfArrow : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty <{{ T1 -> T2 }}>
  | wfRNil :
        well_formed_ty <{{ nil }}>
  | wfRCons : forall i T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        record_ty T2 ->
        well_formed_ty <{{ i : T1 :: T2 }}>.

Hint Constructors record_ty record_tm well_formed_ty : core.

(* ################################### *)
(** *** Substitution *)

(** Substitution and reduction are as before. *)

(* TERSE: HIDEFROMHTML *)
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
(* TERSE: /HIDEFROMHTML *)

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{ t1 --> i }> =>
      <{ ( [x := s] t1) --> i }>
  | <{ nil }> =>
      <{ nil }>
  | <{ i := t1 :: tr }> =>
     <{ i :=  [x := s] t1 :: ( [x := s] tr) }>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ################################### *)
(** *** Reduction *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value  <{ \ x : T2, t1 }>
  | v_rnil : value <{ nil }>
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value <{ i := v1 :: vr }>.

Hint Constructors value : core.

Fixpoint Tlookup (i:string) (Tr:ty) : option ty :=
  match Tr with
  | <{{ i' : T :: Tr' }}> =>
      if String.eqb i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Fixpoint tlookup (i:string) (tr:tm) : option tm :=
  match tr with
  | <{ i' := t :: tr' }> =>
      if String.eqb i i' then Some t else tlookup i tr'
  | _ => None
  end.

(* HIDEFROMHTML *)
Reserved Notation "t '-->' t'" (at level 40).
(* /HIDEFROMHTML *)

Inductive step : tm -> tm -> Prop :=
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
  | ST_Proj1 : forall t1 t1' i,
        t1 --> t1' ->
        <{ t1 --> i }> --> <{ t1' --> i }>
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi ->
        <{ tr --> i }> --> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 --> t1' ->
        <{ i := t1 :: tr2 }> --> <{ i := t1' :: tr2 }>
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 --> tr2' ->
        <{ i := v1 :: tr2 }> --> <{ i := v1 :: tr2' }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(* ###################################################################### *)
(** * Subtyping *)

(** Now we come to the interesting part, where the features we've
    added start to interact.  We begin by defining the subtyping
    relation and developing some of its important technical
    properties. *)

(* ################################### *)
(** ** Definition *)

(** The definition of subtyping is essentially just what we sketched
    in the discussion of record subtyping in chapter \CHAP{Sub}, but we
    need to add well-formedness side conditions to some of the rules.
    Also, we replace the "n-ary" width, depth, and permutation
    subtyping rules by binary rules that deal with just the first
    field. *)

(* HIDEFROMHTML *)
Reserved Notation "T '<:' U" (at level 40).
(* /HIDEFROMHTML *)

Inductive subtype : ty -> ty -> Prop :=
  (* Subtyping between proper types *)
  | S_Refl : forall T,
    well_formed_ty T ->
    T <: T
  | S_Trans : forall S U T,
    S <: U ->
    U <: T ->
    S <: T
  | S_Top : forall S,
    well_formed_ty S ->
    S <: <{{ Top }}>
  | S_Arrow : forall S1 S2 T1 T2,
    T1 <: S1 ->
    S2 <: T2 ->
    <{{ S1 -> S2 }}> <: <{{ T1 -> T2 }}>
  (* Subtyping between record types *)
  | S_RcdWidth : forall i T1 T2,
    well_formed_ty <{{ i : T1 :: T2 }}> ->
    <{{ i : T1 :: T2 }}> <: <{{ nil }}>
  | S_RcdDepth : forall i S1 T1 Sr2 Tr2,
    S1 <: T1 ->
    Sr2 <: Tr2 ->
    record_ty Sr2 ->
    record_ty Tr2 ->
    <{{ i : S1 :: Sr2 }}> <: <{{ i : T1 :: Tr2 }}>
  | S_RcdPerm : forall i1 i2 T1 T2 Tr3,
    well_formed_ty <{{ i1 : T1 :: i2 : T2 :: Tr3 }}> ->
    i1 <> i2 ->
       <{{ i1 : T1 :: i2 : T2 :: Tr3 }}>
    <: <{{ i2 : T2 :: i1 : T1 :: Tr3 }}>

where "T '<:' U" := (subtype T U).

Hint Constructors subtype : core.

(* ############################################### *)
(** ** Examples *)

Module Examples.
Open Scope string_scope.

Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation j := "j".
Notation k := "k".
Notation i := "i".
Notation A := <{{ Base "A" }}>.
Notation B := <{{ Base "B" }}>.
Notation C := <{{ Base "C" }}>.

Definition TRcd_j  :=
  <{{ j  : (B -> B) :: nil }}>.     (* {j:B->B} *)
Definition TRcd_kj :=
  <{{ k : (A -> A) :: TRcd_j }}>.      (* {k:C->C,j:B->B} *)

Example subtyping_example_0 :
  <{{ C -> TRcd_kj }}> <: <{{ C -> nil }}>.
Proof.
  apply S_Arrow.
    apply S_Refl. auto.
    unfold TRcd_kj, TRcd_j. apply S_RcdWidth; auto.
Qed.

(** The following facts are mostly easy to prove in Rocq.  To get full
    benefit, make sure you also understand how to prove them on
    paper! *)

(* EX2 (subtyping_example_1) *)
Example subtyping_example_1 :
  TRcd_kj <: TRcd_j.
(* {k:A->A,j:B->B} <: {j:B->B} *)
Proof with eauto.
  (* ADMITTED *)
  unfold TRcd_kj, TRcd_j.
  eapply S_Trans.
    apply S_RcdPerm...
    intro X; inversion X.
    apply S_RcdDepth...
Qed.
(* /ADMITTED *)
(** [] *)

(* EX1 (subtyping_example_2) *)
Example subtyping_example_2 :
  <{{ Top -> TRcd_kj }}> <:
          <{{ (C -> C) -> TRcd_j }}>.
Proof with eauto.
  (* ADMITTED *)
  unfold TRcd_kj, TRcd_j.
  apply S_Arrow...
    apply subtyping_example_1.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX1 (subtyping_example_3) *)
Example subtyping_example_3 :
  <{{ nil -> (j : A :: nil) }}> <:
          <{{ (k : B :: nil) -> nil }}>.
(* {}->{j:A} <: {k:B}->{} *)
Proof with eauto.
  (* ADMITTED *)
  apply S_Arrow...
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2 (subtyping_example_4) *)
Example subtyping_example_4 :
  <{{ x : A :: y : B :: z : C :: nil }}> <:
  <{{ z : C :: y : B :: x : A :: nil }}>.
Proof with eauto.
  (* ADMITTED *)
  eapply S_Trans.
    apply S_RcdPerm...  intro X; inversion X.
    eapply S_Trans.
      eapply S_RcdDepth. apply S_Refl... apply S_RcdPerm...  intro X; inversion X.
      eauto. eauto.
      apply S_RcdPerm... intro X; inversion X.
Qed.
(* /ADMITTED *)
(** [] *)

End Examples.

(* ###################################################################### *)
(** ** Properties of Subtyping *)

(** *** Well-Formedness *)

(** To get started proving things about subtyping, we need a couple of
    technical lemmas that intuitively (1) allow us to extract the
    well-formedness assumptions embedded in subtyping derivations
    and (2) record the fact that fields of well-formed record types
    are themselves well-formed types.  *)

Lemma subtype__wf : forall S T,
  subtype S T ->
  well_formed_ty T /\ well_formed_ty S.
(* FOLD *)
Proof with eauto.
  intros S T Hsub.
  induction Hsub;
    intros; try (destruct IHHsub1; destruct IHHsub2)...
  - (* S_RcdPerm *)
    split... inversion H. subst. inversion H5...  Qed.
(* /FOLD *)

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
(* FOLD *)
Proof with eauto.
  intros i T.
  induction T; intros; try solve_by_invert.
  - (* RCons *)
    inversion H. subst. unfold Tlookup in H0.
    destruct (String.eqb i s)...  inversion H0; subst...  Qed.
(* /FOLD *)

(** *** Field Lookup *)

(** The record matching lemmas get a little more complicated in the
    presence of subtyping, for two reasons.  First, record types no
    longer necessarily describe the exact structure of the
    corresponding terms.  And second, reasoning by induction on typing
    derivations becomes harder in general, because typing is no longer
    syntax directed. *)

Lemma rcd_types_match : forall S T i Ti,
  subtype S T ->
  Tlookup i T = Some Ti ->
  exists Si, Tlookup i S = Some Si /\ subtype Si Ti.
(* FOLD *)
Proof with (eauto using wf_rcd_lookup).
  intros S T i Ti Hsub Hget. generalize dependent Ti.
  induction Hsub; intros Ti Hget;
    try solve_by_invert.
  - (* S_Refl *)
    exists Ti...
  - (* S_Trans *)
    destruct (IHHsub2 Ti) as [Ui Hui]... destruct Hui.
    destruct (IHHsub1 Ui) as [Si Hsi]... destruct Hsi.
    exists Si...
  - (* S_RcdDepth *)
    rename i0 into k.
    unfold Tlookup. unfold Tlookup in Hget.
    destruct (String.eqb i k)...
    + (* i = k -- we're looking up the first field *)
      inversion Hget. subst. exists S1...
  - (* S_RcdPerm *)
    exists Ti. split.
    + (* lookup *)
      unfold Tlookup. unfold Tlookup in Hget.
      destruct (eqb_spec i i1)...
      * (* i = i1 -- we're looking up the first field *)
        destruct (eqb_spec i i2)...
        (* i = i2 -- contradictory *)
        destruct H0.
        subst...
    + (* subtype *)
      inversion H. subst. inversion H5. subst...  Qed.
(* /FOLD *)

(* LATER: I'd like to typeset this better, but first Rocqdoc has to be
   fixed to allow multi-paragraph list items!  (Maybe it does now?) *)

(* EX3M (rcd_types_match_informal) *)
(** Write a careful informal proof of the [rcd_types_match]
    lemma. *)

(* SOLUTION *)
(* An informal proof...

   THEOREM: If [S], [T], and [Ti] are types and [i] is a label
   such that [S <: T] and [Tlookup i T = Some Ti], then there
   exists a subtype [Si] of [Ti] such that [Tlookup i S = Some
   Si].

   PROOF: Let types [S] and [T] be given as decribed.  We proceed by
   induction on the derivation of [S <: T] leaving [Ti] general.
   Cases [S_Top], [S_Arrow] and [S_RcdWidth] are immediately
   contradictory because [Tlookup] always returns [None] when
   called on [Top], an arrow type, or [RNil].

   - If the last step of the derivation is by [S_Refl], then S =
     T and we know [well_formed_ty T].  In this case, Ti itself
     satisfies the theorem.  We know [Tlookup i T = Some Ti],
     and [Ti <: Ti] follows by [S_Refl] and lemma [wf_rcd_lookup]

   - If the last step of the derivation is by [S_Trans], then
     there is some type [U] such that [S <: U] and [U <: T].
     Picking [Ti] for [Ti] in the IH for the [U <: T]
     subderivation yields that there exists a type [Ui] such that
     [Ui <: Ti] and [Tlookup i U = Some Ui].

     Then picking [Ui] for [Ti] in the IH for the [S <: U]
     subderivation yields that there exists a type [Si] such that
     [Si <: Ui] and [Tlookup i S = Some Si].  Thus, [Si] satisfies
     the theorem - [Si <: Ti] follows directly by [S_Trans].

   - If the last step of the derivation is by [S_RcdDepth] then
     there exist types [S1], [T1], [Sr2] and [Tr2] and a label
     [k] such that [S = {k:S1, Sr2}], [T = {k:T1, Tr2}] and such
     that [S1 <: T1] and [Sr2 <: Tr2].

     There are two cases: either [i = k] or not.  In the first
     case, by the definition of [Tlookup], we have [Ti = T1],
     so that [S1] satisfies the theorem.  In the second case,
     the result follows immediately by the definition of
     [Tlookup] and the IH for the [Sr2 <: Tr2] subderivation.

   - If the last step of the derivation is by [S_RcdPerm] then
     there exist types [T1], [T2] and [Tr3] and labels [i1] and
     [i2] such that [S = {i1:T1, i2:T2, Tr3}],
     [T = {i2:T2, i1:T1, Tr3}] and [i1 <> i2].  Here, [Ti]
     satisfies the theorem.  [Ti <: Ti] follows by [S_Refl] and
     the [well_formed] side condition of the original derivation.

     It remains to show [Tlookup i {i1:T1, i2:T2, Tr3} = Some Ti].
     Either [i = i1] or not.
     - If so, then [i <> i2], so our [Tlookup] hypothesis and
       the definition of [Tlookup] imply that [Ti = T1].  The
       conclusion then follows immediately.
     - So suppose not.  Then either [i = i2] or not.  If so, then
       the [Tlookup] hypothesis implies that [Ti = T2].  Since
       [i1 <> i2], the conclusion is immediate.  If not, then
       the conclusion and our [Tlookup] assumption both reduce
       to [Tlookup i Tr3 = Some Ti], so the theorem holds. *)
(* /SOLUTION *)

(* GRADE_MANUAL 3: rcd_types_match_informal *)
(** [] *)

(** *** Inversion Lemmas *)

(* LATER: I made this an exercise to avoid giving away the solution to
   the exercise in Subtyping.v.  But it doesn't really make sense. *)
(* EX3? (sub_inversion_arrow) *)
Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{{ V1 -> V2 }}> ->
     exists U1 U2,
       (U= <{{ U1 -> U2 }}> ) /\ (V1 <: U1) /\ (U2 <: V2).
(* FOLD *)
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{{ V1 -> V2 }}> as V.
  generalize dependent V2. generalize dependent V1.
  (* ADMITTED *)
  induction Hs; subst; intros; try solve_by_invert.
    - (* S_Refl *)
      exists V1, V2. subst. inversion H...
    - (* S_Trans *)
      apply IHHs2 in HeqV. destruct HeqV as [U1 [U2 [HeqS [HU1 HU2]]]].
      apply IHHs1 in HeqS. destruct HeqS as [S1 [S2 [HeqS [HS1 HS2]]]].
      exists S1, S2. subst...
    - (* S_Arrow *)
      exists S1, S2. inversion HeqV; subst...  Qed.
(* /ADMITTED *)
(** [] *)
(* /FOLD *)

(* ###################################################################### *)
(** * Typing *)

Definition context := partial_map ty.

(* HIDEFROMHTML *)
Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc at level 99, T custom stlc_ty at level 0).
(* /HIDEFROMHTML *)

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma (x : string) T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |-- x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      (x |-> T11; Gamma) |-- t12 \in T12 ->
      Gamma |-- (\ x : T11, t12) \in (T11 -> T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T1 -> T2) ->
      Gamma |-- t2 \in T1 ->
      Gamma |-- t1 t2 \in T2
  | T_Proj : forall Gamma i t T Ti,
      Gamma |-- t \in T ->
      Tlookup i T = Some Ti ->
      Gamma |-- t --> i \in Ti
  (* Subsumption *)
  | T_Sub : forall Gamma t S T,
      Gamma |-- t \in S ->
      subtype S T ->
      Gamma |-- t \in T
  (* Rules for record terms *)
  | T_RNil : forall Gamma,
      Gamma |-- nil \in nil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |-- t \in T ->
      Gamma |-- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |-- i := t :: tr \in (i : T :: Tr)

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

(* ############################################### *)
(** ** Typing Examples *)

Module Examples2.
Import Examples.

(* LATER: This would be more interesting if it used subsumption *)
(* EX1 (typing_example_0) *)
Definition trcd_kj :=
  <{ k := (\z : A, z) :: j := (\z : B, z) :: nil }>.

Example typing_example_0 :
  empty |-- trcd_kj \in TRcd_kj.
(* empty |-- {k=(\z:A.z), j=(\z:B.z)} : {k:A->A,j:B->B} *)
(* FOLD *)
Proof.
  (* ADMITTED *)
  unfold TRcd_kj, TRcd_j, trcd_kj; auto.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FOLD *)

(* EX2 (typing_example_1) *)
Example typing_example_1 :
  empty |-- (\x : TRcd_j, x --> j) trcd_kj \in (B -> B).
(* empty |-- (\x:{k:A->A,j:B->B}, x.j)
              {k=(\z:A,z), j=(\z:B,z)}
         : B->B *)
(* FOLD *)
Proof with eauto.
  (* ADMITTED *)
  unfold TRcd_j, trcd_kj.
    eapply T_App.
    apply T_Abs...
    apply T_Sub with TRcd_kj.
      apply typing_example_0.
      apply subtyping_example_1.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FOLD *)

(* EX2? (typing_example_2) *)
Example typing_example_2 :
  empty |-- (\ z : (C -> C) -> TRcd_j, (z (\ x : C, x) ) --> j )
            ( \z : (C -> C), trcd_kj ) \in (B -> B).
(* empty |-- (\z:(C->C)->{j:B->B}, (z (\x:C,x)).j)
              (\z:C->C, {k=(\z:A,z), j=(\z:B,z)})
           : B->B *)
(* FOLD *)
Proof with eauto.
  (* ADMITTED *)
  unfold TRcd_j, trcd_kj.
  eapply T_App.
  + apply T_Abs...
    eapply T_Proj.
    - eapply T_App.
      * apply T_Var. unfold update, t_update. simpl. auto. auto.
      (* SOONER: Ori: I don't really understand what goes wrong with automation
      here. "apply T_Var; auto." worked in previous versions. *)
      * apply T_Abs...
    - auto.
  + apply T_Sub with <{{ (C -> C) -> TRcd_kj }}>.
      unfold TRcd_kj, TRcd_j.
      apply T_Abs...
        apply T_RCons...
      apply S_Arrow...
        apply subtyping_example_1.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FOLD *)

End Examples2.

(* ###################################################################### *)
(** ** Properties of Typing *)

(** *** Well-Formedness *)

Lemma has_type__wf : forall Gamma t T,
  has_type Gamma t T -> well_formed_ty T.
(* FOLD *)
Proof with eauto.
  intros Gamma t T Htyp.
  induction Htyp...
  - (* T_App *)
    inversion IHHtyp1...
  - (* T_Proj *)
    eapply wf_rcd_lookup...
  - (* T_Sub *)
    apply subtype__wf in H.
    destruct H...
Qed.
(* /FOLD *)

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr --> tr' ->
  record_tm tr'.
(* FOLD *)
Proof.
  intros tr tr' Hrt Hstp.
  inversion Hrt; subst; inversion Hstp; subst; eauto.
Qed.
(* /FOLD *)

(** *** Field Lookup *)

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |-- v \in T ->
  Tlookup i T = Some Ti ->
  exists vi, tlookup i v = Some vi /\ empty |-- vi \in Ti.
(* FOLD *)
Proof with eauto.
  remember empty as Gamma.
  intros t T i Ti Hval Htyp. generalize dependent Ti.
  induction Htyp; intros; subst; try solve_by_invert.
  - (* T_Sub *)
    apply (rcd_types_match S) in H0...
    destruct H0 as [Si [HgetSi Hsub]].
    eapply IHHtyp in HgetSi...
    destruct HgetSi as [vi [Hget Htyvi]]...
  - (* T_RCons *)
    simpl in H0. simpl. simpl in H1.
    destruct (String.eqb i i0).
    + (* i is first *)
      injection H1 as H1. subst. exists t...
    + (* i in tail *)
      eapply IHHtyp2 in H1...
      inversion Hval...  Qed.
(* /FOLD *)

(* ########################################## *)
(** *** Progress *)

(* SOONER: ditto *)
(* EX3 (canonical_forms_of_arrow_types) *)
Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
     Gamma |-- s \in (T1 -> T2) ->
     value s ->
     exists x S1 s2,
        s = <{ \ x  : S1, s2 }>.
(* FOLD *)
Proof with eauto.
  (* ADMITTED *)
  intros Gamma s T1 T2 Hty Hv.
  remember <{{ T1 -> T2 }}> as T.
  generalize dependent T2. generalize dependent T1.
  induction Hty; intros; try solve_by_invert.
  - (* T_Abs *)
    exists x, T11, t12...
  - (* T_Sub *)
    subst.
    destruct (sub_inversion_arrow S T1 T2) as
      [S1 [S2 [HeqS [Hsub1 Hsub2]]]]...  Qed.
(* /ADMITTED *)
(** [] *)
(* /FOLD *)

(* SOONER: How do we escape without a canonical forms lemma for records? *)
Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
(* FOLD *)
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  revert HeqGamma.
  induction Ht;
    intros HeqGamma; subst...
  - (* T_Var *)
    inversion H.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
          as [x [S1 [t12 Heqt1]]]...
        subst. exists <{ [x:=t2] t12 }>...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }> ...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_Proj *)
    right. destruct IHHt...
    + (* rcd is value *)
      destruct (lookup_field_in_value t T i Ti)
        as [t' [Hget Ht']]...
    + (* rcd_steps *)
      destruct H0 as [t' Hstp]. exists <{ t' --> i }>...
  - (* T_RCons *)
    destruct IHHt1...
    + (* head is a value *)
      destruct IHHt2...
      * (* tail steps *)
        right. destruct H2 as [tr' Hstp].
        exists <{ i := t :: tr' }>...
    + (* head steps *)
      right. destruct H1 as [t' Hstp].
      exists <{ i := t' :: tr}>...  Qed.
(* /FOLD *)

(* SOONER: Need to recheck the treatment of well-formedness here...  I
   think what's here may be fine, since we're rebuilding a step
   derivation, not typing. *)
(** _Theorem_ : For any term [t] and type [T], if [empty |-- t : T]
    then [t] is a value or [t --> t'] for some term [t'].

    _Proof_: Let [t] and [T] be given such that [empty |-- t : T].  We
    proceed by induction on the given typing derivation.

      - The cases where the last step in the typing derivation is
        [T_Abs] or [T_RNil] are immediate because abstractions and
        [{}] are always values.  The case for [T_Var] is vacuous
        because variables cannot be typed in the empty context.

      - If the last step in the typing derivation is by [T_App], then
        there are terms [t1] [t2] and types [T1] [T2] such that [t =
        t1 t2], [T = T2], [empty |-- t1 : T1 -> T2] and [empty |-- t2 :
        T1].

        The induction hypotheses for these typing derivations yield
        that [t1] is a value or steps, and that [t2] is a value or
        steps.

        - Suppose [t1 --> t1'] for some term [t1'].  Then [t1 t2 -->
          t1' t2] by [ST_App1].

        - Otherwise [t1] is a value.

          - Suppose [t2 --> t2'] for some term [t2'].  Then [t1 t2 -->
            t1 t2'] by rule [ST_App2] because [t1] is a value.

          - Otherwise, [t2] is a value.  By Lemma
            [canonical_forms_for_arrow_types], [t1 = \x:S1,s2] for
            some [x], [S1], and [s2].  But then [(\x:S1,s2) t2 -->
            [x:=t2]s2] by [ST_AppAbs], since [t2] is a value.

      - If the last step of the derivation is by [T_Proj], then there
        are a term [tr], a type [Tr], and a label [i] such that [t =
        tr.i], [empty |-- tr : Tr], and [Tlookup i Tr = Some T].

        By the IH, either [tr] is a value or it steps.  If [tr -->
        tr'] for some term [tr'], then [tr.i --> tr'.i] by rule
        [ST_Proj1].

        If [tr] is a value, then Lemma [lookup_field_in_value] yields
        that there is a term [ti] such that [tlookup i tr = Some ti].
        It follows that [tr.i --> ti] by rule [ST_ProjRcd].

      - If the final step of the derivation is by [T_Sub], then there
        is a type [S] such that [S <: T] and [empty |-- t : S].  The
        desired result is exactly the induction hypothesis for the
        typing subderivation.

      - If the final step of the derivation is by [T_RCons], then
        there exist some terms [t1] [tr], types [T1 Tr] and a label
        [t] such that [t = {i=t1, tr}], [T = {i:T1, Tr}], [record_ty
        tr], [record_tm Tr], [empty |-- t1 : T1] and [empty |-- tr :
        Tr].

        The induction hypotheses for these typing derivations yield
        that [t1] is a value or steps, and that [tr] is a value or
        steps.  We consider each case:

        - Suppose [t1 --> t1'] for some term [t1'].  Then [{i=t1, tr}
          --> {i=t1', tr}] by rule [ST_Rcd_Head].

        - Otherwise [t1] is a value.

          - Suppose [tr --> tr'] for some term [tr'].  Then [{i=t1,
            tr} --> {i=t1, tr'}] by rule [ST_Rcd_Tail], since [t1] is
            a value.

          - Otherwise, [tr] is also a value.  So, [{i=t1, tr}] is a
            value by [v_rcons]. *)

(* ########################################## *)
(** *** Inversion Lemma *)

(* HIDE *)
Lemma typing_inversion_var : forall Gamma (x : string) T,
  Gamma |-- x \in T ->
  exists S,
    Gamma x = Some S /\ S <: T.
(* FOLD *)
Proof with eauto.
  intros Gamma x T Hty.
  remember (tm_var x) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_Var *)
    exists T...
  - (* T_Sub *)
    destruct IHHty as [U [Hctx HsubU]]... Qed.
(* /FOLD *)
(* /HIDE *)

(* HIDE *)
Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |-- t1 t2 \in T2 ->
  exists T1,
    Gamma |-- t1 \in (T1 -> T2) /\
    Gamma |-- t2 \in T1.
(* FOLD *)
Proof with eauto.
  intros Gamma t1 t2 T2 Hty.
  remember <{ t1 t2 }> as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_App *)
    exists T1...
  - (* T_Sub *)
    destruct IHHty as [U1 [Hty1 Hty2]]...
    assert (Hwf := has_type__wf _ _ _ Hty2).
    exists U1...  Qed.
(* /FOLD *)
(* /HIDE *)

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |-- \ x : S1, t2 \in T ->
     (exists S2, <{{ S1 -> S2 }}> <: T
              /\ (x |-> S1; Gamma) |-- t2 \in S2).
(* FOLD *)
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember <{ \ x : S1, t2 }> as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    assert (Hwf := has_type__wf _ _ _ H0).
    exists T12...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
    Qed.
(* /FOLD *)

(* HIDE *)
Lemma typing_inversion_proj : forall Gamma i t1 Ti,
  Gamma |-- t1 --> i \in Ti ->
  exists T Si,
    Tlookup i T = Some Si /\ Si <: Ti /\ Gamma |-- t1 \in T.
(* FOLD *)
Proof with eauto.
  intros Gamma i t1 Ti H.
  remember <{ t1 --> i }> as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Proj *)
    assert (well_formed_ty Ti) as Hwf.
    { (* pf of assertion *)
      apply (wf_rcd_lookup i T Ti)...
      apply has_type__wf in H... }
    exists T, Ti...
  - (* T_Sub *)
    destruct IHhas_type as [U [Ui [Hget [Hsub Hty]]]]...
    exists U, Ui...  Qed.
(* /FOLD *)

Lemma typing_inversion_rcons : forall Gamma i ti tr T,
  Gamma |-- i := ti :: tr \in T ->
  exists Si Sr,
    <{{ i : Si :: Sr }}> <: T /\ Gamma |-- ti \in Si /\
    record_tm tr /\ Gamma |-- tr \in Sr.
(* FOLD *)
Proof with eauto.
  intros Gamma i ti tr T Hty.
  remember <{ i := ti :: tr }> as t.
  induction Hty;
    inversion Heqt; subst...
  - (* T_Sub *)
    apply IHHty in H0.
    destruct H0 as [Ri [Rr [HsubRS [HtypRi HtypRr]]]].
    exists Ri, Rr...
  - (* T_RCons *)
    assert (well_formed_ty <{{ i : T :: Tr }}> ) as Hwf.
    { (* pf of assertion *)
      apply has_type__wf in Hty1.
      apply has_type__wf in Hty2... }
    exists T, Tr...  Qed.
(* /FOLD *)
(* /HIDE *)

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |-- \x : S1, s2 \in (T1 -> T2) ->
     T1 <: S1
  /\ (x |-> S1) |-- s2 \in T2.
(* FOLD *)
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst...  Qed.
(* /FOLD *)

(* ########################################## *)
(** ** Weakening *)

(** The weakening lemma is proved as in pure STLC. *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* HIDE *)
(* SOONER: BCP 20: This can all be deleted now, since we've switched
   to weakending, yes? *)
(* ########################################## *)
(** *** Context Invariance *)

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x <{ x }>
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x <{ t1 t2 }>
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x <{ t1 t2 }>
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x <{ \y : T11, t12 }>
  | afi_proj : forall x t i,
      appears_free_in x t ->
      appears_free_in x <{ t --> i }>
  | afi_rhead : forall x i t tr,
      appears_free_in x t ->
      appears_free_in x <{ i := t :: tr }>
  | afi_rtail : forall x i t tr,
      appears_free_in x tr ->
      appears_free_in x <{ i := t :: tr }>.

Hint Constructors appears_free_in : core.

Lemma context_invariance : forall Gamma Gamma' t S,
     has_type Gamma t S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     Gamma' |-- t \in S.
(* FOLD *)
Proof with eauto.
  intros. generalize dependent Gamma'.
  induction H;
    intros Gamma' Heqv...
  - (* T_Var *)
    apply T_Var... rewrite <- Heqv...
  - (* T_Abs *)
    apply T_Abs... apply IHhas_type. intros y Hafi.
    destruct (eqb_spec x y); subst.
    + repeat rewrite update_eq. reflexivity.
    + repeat rewrite update_neq; auto.
  - (* T_App *)
    apply T_App with T1...
  - (* T_RCons *)
    apply T_RCons...  Qed.
(* /FOLD *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |-- t \in T ->
   exists T', Gamma x = Some T'.
(* FOLD *)
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; subst; inversion Hafi; subst...
  - (* T_Abs *)
    destruct (IHHtyp H5) as [T Hctx]. exists T.
    rewrite update_neq in Hctx...  Qed.
(* /FOLD *)
(* /HIDE *)

(* ########################################## *)
(** *** Preservation *)

(* NOTATION: NOWISH: why (x |-> U ; Gamma) and not x |-> U ; Gamma ? *)
Lemma substitution_preserves_typing : forall Gamma x U t v T,
   (x |-> U ; Gamma) |-- t \in T ->
   empty |-- v \in U   ->
   Gamma |-- [x:=v]t \in T.
Proof.
(* FOLD *)
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - (* T_Var *)
    rename x0 into y.
    destruct (eqb_spec x y) as [Hxy|Hxy]; subst.
    + (* x = y *)
      rewrite update_eq in H.
      injection H as H. subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var; [|assumption].
      rewrite update_neq in H; assumption.
  - (* T_Abs *)
    rename x0 into y. subst.
    destruct (eqb_spec x y) as [Hxy|Hxy]; apply T_Abs; try assumption.
    + (* x=y *)
      subst. rewrite update_shadow in Ht. assumption.
    + (* x <> y *)
      subst. apply IHHt.
      rewrite update_permute; auto.
      - (* rcons *)   (* <=== only new case compared to pure STLC *)
      apply T_RCons; eauto.
      inversion H0; subst; simpl; auto.
Qed.
(* /FOLD *)

Theorem preservation : forall t t' T,
     empty |-- t \in T  ->
     t --> t'  ->
     empty |-- t' \in T.
(* FOLD *)
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; eauto].
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T0...
  - (* T_Proj *)
    inversion HE; subst...
    destruct (lookup_field_in_value _ _ _ _ H2 HT H)
      as [vi [Hget Hty]].
    rewrite H4 in Hget. inversion Hget. subst...
  - (* T_RCons *)
    inversion HE; subst...
    eauto using step_preserves_record_tm.  Qed.
(* /FOLD *)

(* SOONER: This proof may not be as careful as it should be about
   well-formedness side conditions.  Recheck! *)
(** _Theorem_: If [t], [t'] are terms and [T] is a type such that
     [empty |-- t : T] and [t --> t'], then [empty |-- t' : T].

    _Proof_: Let [t] and [T] be given such that [empty |-- t : T].  We go
     by induction on the structure of this typing derivation, leaving
     [t'] general.  Cases [T_Abs] and [T_RNil] are vacuous because
     abstractions and [{}] don't step.  Case [T_Var] is vacuous as well,
     since the context is empty.

     - If the final step of the derivation is by [T_App], then there
       are terms [t1] [t2] and types [T1] [T2] such that [t = t1 t2],
       [T = T2], [empty |-- t1 : T1 -> T2] and [empty |-- t2 : T1].

       By inspection of the definition of the step relation, there are
       three ways [t1 t2] can step.  Cases [ST_App1] and [ST_App2]
       follow immediately by the induction hypotheses for the typing
       subderivations and a use of [T_App].

       Suppose instead [t1 t2] steps by [ST_AppAbs].  Then
       [t1 = \x:S,t12] for some type [S] and term [t12], and
       [t' = [x:=t2]t12].

       By Lemma [abs_arrow], we have [T1 <: S] and [x:S1 |-- s2 : T2].
       It then follows by lemma [substitution_preserves_typing] that
       [empty |-- [x:=t2] t12 : T2] as desired.

     - If the final step of the derivation is by [T_Proj], then there
       is a term [tr], type [Tr] and label [i] such that [t = tr.i],
       [empty |-- tr : Tr], and [Tlookup i Tr = Some T].

       The IH for the typing derivation gives us that, for any term
       [tr'], if [tr --> tr'] then [empty |-- tr' Tr].  Inspection of
       the definition of the step relation reveals that there are two
       ways a projection can step.  Case [ST_Proj1] follows
       immediately by the IH.

       Instead suppose [tr --> i] steps by [ST_ProjRcd].  Then [tr] is a
       value and there is some term [vi] such that
       [tlookup i tr = Some vi] and [t' = vi].  But by lemma
       [lookup_field_in_value], [empty |-- vi : Ti] as desired.

     - If the final step of the derivation is by [T_Sub], then there
       is a type [S] such that [S <: T] and [empty |-- t : S].  The
       result is immediate by the induction hypothesis for the typing
       subderivation and an application of [T_Sub].

     - If the final step of the derivation is by [T_RCons], then there
       exist some terms [t1] [tr], types [T1 Tr] and a label [t] such
       that [t = i:=t1 :: tr}], [T = i:T1 :: Tr], [record_ty tr],
       [record_tm Tr], [empty |-- t1 : T1] and [empty |-- tr : Tr].

       By the definition of the step relation, [t] must have stepped
       by [ST_Rcd_Head] or [ST_Rcd_Tail].  In the first case, the
       result follows by the IH for [t1]'s typing derivation and
       [T_RCons].  In the second case, the result follows by the IH
       for [tr]'s typing derivation, [T_RCons], and a use of the
       [step_preserves_record_tm] lemma. *)

End RecordSub.

(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(\\*\\* \\*+\\|(\\* EX[1-5]..." *)
(* End: *)
(* mode: outline-minor *)
(* outline-heading-end-regexp: "\n" *)
(* /HIDE *)
