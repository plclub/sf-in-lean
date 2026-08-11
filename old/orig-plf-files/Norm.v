(** * Norm: Normalization of STLC *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import List.
From Stdlib Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

Hint Constructors multi : core.
(* TERSE: /HIDEFROMHTML *)

(* Chapter written and maintained by Andrew Tolmach *)

(* SOONER: Would be nice to autograde the exercises.  (Should not be
   hard; just needs doing.)  *)
(* LATER: Would be nice to have some more exercises... *)
(* HIDE: CH: Showing students complex finished proofs won't teach them
   how to prove such things themselves. In particular, giving them the
   "right" induction hypothesis on a plate won't teach them how to
   strengthen it in their own proofs. I think there should be a much
   more incremental way of presenting this proof that includes failed
   attempts to guide the search for the "right" invariants. *)

(** This optional chapter is based on chapter 12 of _Types and
    Programming Languages_ (Pierce).  It may be useful to look at the
    two together, as that chapter includes explanations and informal
    proofs that are not repeated here.

    In this chapter, we consider another fundamental theoretical
    property of the simply typed lambda-calculus: the fact that the
    evaluation of a well-typed program is guaranteed to halt in a
    finite number of steps---i.e., every well-typed term is
    _normalizable_.

    Unlike the type-safety properties we have considered so far, the
    normalization property does not extend to full-blown programming
    languages, because these languages nearly always extend the simply
    typed lambda-calculus with constructs, such as general
    recursion (see the \CHAP{MoreStlc} chapter) or recursive types, that
    can be used to write nonterminating programs.  However, the issue
    of normalization reappears at the level of _types_ when we
    consider the metatheory of polymorphic versions of the lambda
    calculus such as System F-omega: in this system, the language of
    types effectively contains a copy of the simply typed
    lambda-calculus, and the termination of the typechecking algorithm
    will hinge on the fact that a "normalization" operation on type
    expressions is guaranteed to terminate.

    Another reason for studying normalization proofs is that they are
    some of the most beautiful---and mind-blowing---mathematics to be
    found in the type theory literature, often (as here) involving the
    fundamental proof technique of _logical relations_.

    The calculus we shall consider here is the simply typed
    lambda-calculus over a single base type [bool] and with
    pairs. We'll give most details of the development for the basic
    lambda-calculus terms treating [bool] as an uninterpreted base
    type, and leave the extension to the boolean operators and pairs
    to the reader.  Even for the base calculus, normalization is not
    entirely trivial to prove, since each reduction of a term can
    duplicate redexes in subterms. *)

(* EX2M (norm_fail) *)
(** Where do we fail if we attempt to prove normalization by a
    straightforward induction on the size of a well-typed term? *)

(* SOLUTION *)
(** To complete the application case of the proof we will need to use
    the induction hypothesis on the body of the applied lambda abstraction
    _after_ a value has been substituted in for the bound variable.  But
    this substitution may _increase_ the size of the term, making the
    appeal to induction invalid. *)
(* /SOLUTION *)

(* GRADE_MANUAL 2: norm_fail *)
(** [] *)

(* EX5M! (norm) *)
(** The best ways to understand an intricate proof like this is
    are (1) to help fill it in and (2) to extend it.  We've left out some
    parts of the following development, including some proofs of lemmas
    and the all the cases involving products and conditionals.  Fill them
    in. *)

(* GRADE_MANUAL 10: norm *)
(** [] *)

(* ###################################################################### *)
(** * Language *)

(** We begin by repeating the relevant language definition, which is
    similar to those in the \CHAP{MoreStlc} chapter, plus supporting
    results including type preservation and step determinism.  (We
    won't need progress.)  You may just wish to skip down to the
    Normalization section... *)

(* ###################################################################### *)
(** *** Syntax and Operational Semantics *)

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Prod  : ty -> ty -> ty
.

Inductive tm : Type :=
    (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
    (* booleans *)
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
    (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm.

Declare Custom Entry stlc.

(* INSTRUCTORS: Begin Copy of template stlc_fun *)
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.
(* INSTRUCTORS: End Copy of template stlc_fun *)

(* INSTRUCTORS: Begin Copy of template stlc_constr *)
Notation "{ x }" := x (in custom stlc at level 1, x constr).
(* INSTRUCTORS: End Copy of template stlc_constr *)

(* INSTRUCTORS: Begin Copy of template stlc_bool *)
Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).
(* INSTRUCTORS: End Copy of template stlc_bool *)

(* INSTRUCTORS: Begin Copy of template stlc_prod *)
Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc at level 2, X custom stlc, Y custom stlc at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 1).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 1).
(* INSTRUCTORS: End Copy of template stlc_prod *)

(* ###################################################################### *)
(** *** Substitution *)

(* TERSE: HIDEFROMHTML *)
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
(* TERSE: /HIDEFROMHTML *)

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{ \ y : T, t1 }> =>
      if String.eqb x y then t else <{ \y:T, [x:=s] t1 }>
  | <{t1 t2}> =>
      <{ ([x:=s]t1) ([x:=s]t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{(t1, t2)}> =>
      <{( ([x:=s] t1), ([x:=s] t2) )}>
  | <{t0.fst}> =>
      <{ ([x:=s] t0).fst}>
  | <{t0.snd}> =>
      <{ ([x:=s] t0).snd}>
  end

  where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ###################################################################### *)
(** *** Reduction *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>.

Hint Constructors value : core.

(* TERSE: HIDEFROMHTML *)
Reserved Notation "t '-->' t'" (at level 40).
(* TERSE: /HIDEFROMHTML *)

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
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  | ST_Pair1 : forall t1 t1' t2,
        t1 --> t1' ->
        <{ (t1,t2) }> --> <{ (t1' , t2) }>
  | ST_Pair2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        <{ (v1, t2) }> -->  <{ (v1, t2') }>
  | ST_Fst1 : forall t0 t0',
        t0 --> t0' ->
        <{ t0.fst }> --> <{ t0'.fst }>
  | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ (v1,v2).fst }> --> v1
  | ST_Snd1 : forall t0 t0',
        t0 --> t0' ->
        <{ t0.snd }> --> <{ t0'.snd }>
  | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ (v1,v2).snd }> --> v2

where "t '-->' t'" := (step t t').

(* TERSE: HIDEFROMHTML *)
Hint Constructors step : core.
(* TERSE: /HIDEFROMHTML *)

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Notation step_normal_form := (normal_form step).

Lemma value__normal : forall t, value t -> step_normal_form t.
(* FOLD *)
Proof with eauto.
  intros t H; induction H; intros [t' ST]; inversion ST...
Qed.
(* /FOLD *)

(* ###################################################################### *)
(** *** Typing *)

(* TERSE: HIDEFROMHTML *)
Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).
(* TERSE: /HIDEFROMHTML *)

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Same as before: *)
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
      Gamma |-- t1 \in Bool ->
      Gamma |-- t2 \in T1 ->
      Gamma |-- t3 \in T1 ->
      Gamma |-- if t1 then t2 else t3 \in T1
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t0 T1 T2,
      Gamma |-- t0 \in (T1 * T2) ->
      Gamma |-- t0.fst \in T1
  | T_Snd : forall Gamma t0 T1 T2,
      Gamma |-- t0 \in (T1 * T2) ->
      Gamma |-- t0.snd \in T2

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

(* TERSE: HIDEFROMHTML *)
Hint Constructors has_type : core.
(* TERSE: /HIDEFROMHTML *)

(* NOWISH: Ori: are these needed? *)
Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

(* ###################################################################### *)
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

(* ###################################################################### *)
(** *** Substitution *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |-- t \in T ->
  empty |-- v \in U   ->
  Gamma |-- [x:=v]t \in T.
(* NOTATION: NOWISH: Ori: In this file, for some reason I need to use
 paratheses for (x |-> U ; Gamma) *)
Proof with eauto.
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

(* ###################################################################### *)
(** *** Preservation *)

 Theorem preservation : forall t t' T,
   empty |-- t \in T  ->
   t --> t'  ->
   empty |-- t' \in T.
Proof with eauto.
intros t t' T HT. generalize dependent t'.
remember empty as Gamma.
induction HT;
  intros t' HE; subst; inversion HE; subst...
- (* T_App *)
  inversion HE; subst...
  + (* ST_AppAbs *)
    apply substitution_preserves_typing with T2...
    inversion HT1...
- (* T_Fst *)
  inversion HT...
- (* T_Snd *)
  inversion HT...
Qed.


(* ###################################################################### *)
(** *** Context Invariance *)

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall (x : string),
      appears_free_in x <{ x }>
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x <{ t1 t2 }>
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x <{ t1 t2 }>
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x <{ \y : T11, t12 }>
  (* booleans *)
  | afi_test0 : forall x t0 t1 t2,
      appears_free_in x t0 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_test1 : forall x t0 t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_test2 : forall x t0 t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  (* pairs *)
  | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ (t1, t2) }>
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ (t1 , t2) }>
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x <{ t.fst }>
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x <{ t.snd }>
.

Hint Constructors appears_free_in : core.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |-- t \in S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     Gamma' |-- t \in S.
(* FOLD *)
Proof.
  intros.
  generalize dependent Gamma'.
  induction H; intros; eauto 12.
  - (* T_Var *)
    apply T_Var. rewrite <- H0; auto.
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... *)
    destruct (eqb_spec x x1); subst.
    + rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + rewrite update_neq; [| assumption].
      rewrite update_neq; [| assumption].
      auto.
Qed.
(* /FOLD *)

(* A handy consequence of [eqb_neq]. *)
Theorem false_eqb_string : forall x y : string,
   x <> y -> String.eqb x y = false.
Proof.
  intros x y. rewrite String.eqb_neq.
  intros H. apply H. Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |-- t \in T ->
   exists T', Gamma x = Some T'.
(* FOLD *)
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  - (* T_Abs *)
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
Qed.
(* /FOLD *)

Corollary typable_empty__closed : forall t T,
    empty |-- t \in T  ->
    closed t.
(* FOLD *)
Proof.
  intros. unfold closed. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' C].
  discriminate C.  Qed.
(* /FOLD *)

(* ###################################################################### *)
(** *** Determinism *)

(** To prove determinsm, we introduce a helpful tactic.  It identifies
    cases in which a value takes a step and solves them by using
    value__normal.  *)

Ltac solve_by_value_nf :=
  match goal with | H : value ?v, H' : ?v --> ?v' |- _ =>
  exfalso; apply value__normal in H; eauto
  end.

Lemma step_deterministic :
   deterministic step.
(* FOLD *)
Proof with eauto.
   unfold deterministic.
   intros t t' t'' E1 E2.
   generalize dependent t''.
   induction E1; intros t'' E2; inversion E2; subst; clear E2;
   try solve_by_invert; try f_equal; try solve_by_value_nf; eauto.
   - inversion E1; subst; solve_by_value_nf.
   - inversion H2; subst; solve_by_value_nf.
   - inversion E1; subst; solve_by_value_nf.
   - inversion H2; subst; solve_by_value_nf.
Qed.
(* /FOLD *)

(* ###################################################################### *)
(** * Normalization *)

(** Now for the actual normalization proof.

    Our goal is to prove that every well-typed term reduces to a
    normal form.  In fact, it turns out to be convenient to prove
    something slightly stronger, namely that every well-typed term
    reduces to a _value_.  This follows from the weaker property
    anyway via Progress (why?) but otherwise we don't need Progress,
    and we didn't bother re-proving it above.

    Here's the key definition: *)

Definition halts  (t:tm) : Prop :=  exists t', t -->* t' /\  value t'.

(** A trivial fact: *)

Lemma value_halts : forall v, value v -> halts v.
(* FOLD *)
Proof.
  intros v H. unfold halts.
  exists v. split.
  - apply multi_refl.
  - assumption.
Qed.
(* /FOLD *)

(** The key issue in the normalization proof (as in many proofs by
    induction) is finding a strong enough induction hypothesis.  To
    this end, we begin by defining, for each type [T], a set [R_T] of
    closed terms of type [T].  We will specify these sets using a
    relation [R] and write [R T t] when [t] is in [R_T]. (The sets
    [R_T] are sometimes called _saturated sets_ or _reducibility
    candidates_.)

    Here is the definition of [R] for the base language:

    - [R bool t] iff [t] is a closed term of type [bool] and [t] halts
      in a value

    - [R (T1 -> T2) t] iff [t] is a closed term of type [T1 -> T2] and
      [t] halts in a value _and_ for any term [s] such that [R T1 s],
      we have [R T2 (t s)]. *)

(** This definition gives us the strengthened induction hypothesis that we
    need.  Our primary goal is to show that all _programs_ ---i.e., all
    closed terms of base type---halt.  But closed terms of base type can
    contain subterms of functional type, so we need to know something
    about these as well.  Moreover, it is not enough to know that these
    subterms halt, because the application of a normalized function to a
    normalized argument involves a substitution, which may enable more
    reduction steps.  So we need a stronger condition for terms of
    functional type: not only should they halt themselves, but, when
    applied to halting arguments, they should yield halting results.

    The form of [R] is characteristic of the _logical relations_ proof
    technique.  (Since we are just dealing with unary relations here, we
    could perhaps more properly say _logical properties_.)  If we want to
    prove some property [P] of all closed terms of type [A], we proceed by
    proving, by induction on types, that all terms of type [A] _possess_
    property [P], all terms of type [A->A] _preserve_ property [P], all
    terms of type [(A->A)->(A->A)] _preserve the property of preserving_
    property [P], and so on.  We do this by defining a family of
    properties, indexed by types.  For the base type [A], the property is
    just [P].  For functional types, it says that the function should map
    values satisfying the property at the input type to values satisfying
    the property at the output type.

    When we come to formalize the definition of [R] in Rocq, we hit a
    problem.  The most obvious formulation would be as a parameterized
    Inductive proposition like this:
[[
      Inductive R : ty -> tm -> Prop :=
      | R_bool : forall b t, empty |-- t \in Bool ->
                      halts t ->
                      R Bool t
      | R_arrow : forall T1 T2 t, empty |-- t \in (Arrow T1 T2) ->
                      halts t ->
                      (forall s, R T1 s -> R T2 (app t s)) ->
                      R (Arrow T1 T2) t.
]]
    Unfortunately, Rocq rejects this definition because it violates the
    _strict positivity requirement_ for inductive definitions, which says
    that the type being defined must not occur to the left of an arrow in
    the type of a constructor argument. Here, it is the third argument to
    [R_arrow], namely [(forall s, R T1 s -> R TS (app t s))], and
    specifically the [R T1 s] part, that violates this rule.  (The
    outermost arrows separating the constructor arguments don't count when
    applying this rule; otherwise we could never have genuinely inductive
    properties at all!)  The reason for the rule is that types defined
    with non-positive recursion can be used to build non-terminating
    functions, which as we know would be a disaster for Rocq's logical
    soundness. Even though the relation we want in this case might be
    perfectly innocent, Rocq still rejects it because it fails the
    positivity test.

    Fortunately, it turns out that we _can_ define [R] using a
    [Fixpoint]: *)

Fixpoint R (T:ty) (t:tm) : Prop :=
  empty |-- t \in T /\ halts t /\
  (match T with
   | <{ Bool }>  => True
   | <{ T1 -> T2 }> => (forall s, R T1 s -> R T2 <{t s}> )
(* QUIETSOLUTION *)
   | <{ T1 * T2 }> => (R T1 <{ t.fst }> ) /\ (R T2 <{ t.snd }>)
(* /QUIETSOLUTION *)
(* UNCOMMENT WHEN HIDING SOLUTIONS
   (* ... edit the next line when dealing with products *)
   | <{ T1 * T2 }> => False    (* FILL IN HERE *)
/UNCOMMENT *)
   end).

(** As immediate consequences of this definition, we have that every
    element of every set [R_T] halts in a value and is closed with type
    [T] :*)

Lemma R_halts : forall {T} {t}, R T t -> halts t.
(* FOLD *)
Proof.
  intros.
  destruct T; unfold R in H; destruct H as [_ [H _]]; assumption.
Qed.
(* /FOLD *)


Lemma R_typable_empty : forall {T} {t}, R T t -> empty |-- t \in T.
(* FOLD *)
Proof.
  intros.
  destruct T; unfold R in H; destruct H as [H _]; assumption.
Qed.
(* /FOLD *)

(** Now we proceed to show the main result, which is that every
    well-typed term of type [T] is an element of [R_T].  Together with
    [R_halts], that will show that every well-typed term halts in a
    value.  *)


(* ###################################################################### *)
(** **  Membership in [R_T] Is Invariant Under Reduction *)

(** We start with a preliminary lemma that shows a kind of strong
    preservation property, namely that membership in [R_T] is _invariant_
    under reduction. We will need this property in both directions,
    i.e., both to show that a term in [R_T] stays in [R_T] when it takes a
    forward step, and to show that any term that ends up in [R_T] after a
    step must have been in [R_T] to begin with.

    First of all, an easy preliminary lemma. Note that in the forward
    direction the proof depends on the fact that our language is
    determinstic. This lemma might still be true for nondeterministic
    languages, but the proof would be harder! *)

Lemma step_preserves_halting :
  forall t t', (t --> t') -> (halts t <-> halts t').
(* FOLD *)
Proof.
 intros t t' ST.  unfold halts.
 split.
 - (* -> *)
  intros [t'' [STM V]].
  destruct STM.
   + exfalso; apply value__normal in V; eauto.
   + rewrite (step_deterministic _ _ _ ST H). exists z. split; assumption.
 - (* <- *)
  intros [t'0 [STM V]].
  exists t'0. split; eauto.
Qed.
(* /FOLD *)

(** Now the main lemma, which comes in two parts, one for each
    direction.  Each proceeds by induction on the structure of the type
    [T]. In fact, this is where we make fundamental use of the
    structure of types.

    One requirement for staying in [R_T] is to stay in type [T]. In the
    forward direction, we get this from ordinary type Preservation. *)

Lemma step_preserves_R : forall T t t', (t --> t') -> R T t -> R T t'.
(* FOLD *)
Proof.
 induction T;  intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [typable_empty_t [halts_t RRt]].
  (* Bool *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  auto.
  (* Arrow *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  intros.
  eapply IHT2.
  apply  ST_App1. apply E.
  apply RRt; auto.
  (* ADMITTED *)
  (* Prod *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  destruct RRt. split; eauto.  Qed.
  (* /ADMITTED *)
(* /FOLD *)

(** The generalization to multiple steps is trivial: *)

Lemma multistep_preserves_R : forall T t t',
  (t -->* t') -> R T t -> R T t'.
(* FOLD *)
Proof.
  intros T t t' STM; induction STM; intros.
  assumption.
  apply IHSTM. eapply step_preserves_R. apply H. assumption.
Qed.
(* /FOLD *)

(** In the reverse direction, we must add the fact that [t] has type
   [T] before stepping as an additional hypothesis. *)

Lemma step_preserves_R' : forall T t t',
  empty |-- t \in T -> (t --> t') -> R T t' -> R T t.
(* FOLD *)
Proof.
  (* ADMITTED *)
  induction T; intros t t' typable_empty_t E Rt'; unfold R; fold R;
               unfold R in Rt'; fold R in Rt';
               destruct Rt' as [typable_empty_t' [halts_t' RRt']].
  (* Bool *)
  split. assumption.
  split. apply (step_preserves_halting _ _ E); eauto.
  auto.
  (* Arrow *)
  split. assumption.
  split. apply (step_preserves_halting _ _ E); eauto.
  intros.
  eapply IHT2. eapply T_App.  apply typable_empty_t.
  eapply R_typable_empty. assumption.
  apply  ST_App1. apply E.
  apply RRt'; auto.
  (* Prod *)
  split.  assumption.
  split. apply (step_preserves_halting _ _ E); eauto.
  destruct RRt'. split; eauto. Qed.
  (* /ADMITTED *)
(* /FOLD *)

Lemma multistep_preserves_R' : forall T t t',
  empty |-- t \in T -> (t -->* t') -> R T t' -> R T t.
(* FOLD *)
Proof.
  intros T t t' HT STM.
  induction STM; intros.
    assumption.
    eapply step_preserves_R'.  assumption. apply H. apply IHSTM.
    eapply preservation;  eauto. auto.
Qed.
(* /FOLD *)

(* ###################################################################### *)
(** ** Closed Instances of Terms of Type [t] Belong to [R_T] *)

(** Now we proceed to show that every term of type [T] belongs to
    [R_T].  Here, the induction will be on typing derivations (it would be
    surprising to see a proof about well-typed terms that did not
    somewhere involve induction on typing derivations!).  The only
    technical difficulty here is in dealing with the abstraction case.
    Since we are arguing by induction, the demonstration that a term
    [abs x T1 t2] belongs to [R_(T1->T2)] should involve applying the
    induction hypothesis to show that [t2] belongs to [R_(T2)].  But
    [R_(T2)] is defined to be a set of _closed_ terms, while [t2] may
    contain [x] free, so this does not make sense.

    This problem is resolved by using a standard trick to suitably
    generalize the induction hypothesis: instead of proving a statement
    involving a closed term, we generalize it to cover all closed
    _instances_ of an open term [t].  Informally, the statement of the
    lemma will look like this:

    If [x1:T1,..xn:Tn |-- t : T] and [v1,...,vn] are values such that
    [R T1 v1], [R T2 v2], ..., [R Tn vn], then
    [R T ([x1:=v1][x2:=v2]...[xn:=vn]t)].

    The proof will proceed by induction on the typing derivation
    [x1:T1,..xn:Tn |-- t : T]; the most interesting case will be the one
    for abstraction. *)

(* ###################################################################### *)
(** *** Multisubstitutions, Multi-Extensions, and Instantiations *)

(** However, before we can proceed to formalize the statement and
    proof of the lemma, we'll need to build some (rather tedious)
    machinery to deal with the fact that we are performing _multiple_
    substitutions on term [t] and _multiple_ extensions of the typing
    context.  In particular, we must be precise about the order in which
    the substitutions occur and how they act on each other.  Often these
    details are simply elided in informal paper proofs, but of course Rocq
    won't let us do that. Since here we are substituting closed terms, we
    don't need to worry about how one substitution might affect the term
    put in place by another.  But we still do need to worry about the
    _order_ of substitutions, because it is quite possible for the same
    identifier to appear multiple times among the [x1,...xn] with
    different associated [vi] and [Ti].

    To make everything precise, we will assume that environments are
    extended from left to right, and multiple substitutions are performed
    from right to left.  To see that this is consistent, suppose we have
    an environment written as [...,y:bool,...,y:nat,...]  and a
    corresponding term substitution written as [...[y:=(tbool
    true)]...[y:=(const 3)]...t].  Since environments are extended from
    left to right, the binding [y:nat] hides the binding [y:bool]; since
    substitutions are performed right to left, we do the substitution
    [y:=(const 3)] first, so that the substitution [y:=(tbool true)] has
    no effect. Substitution thus correctly preserves the type of the term.

    With these points in mind, the following definitions should make sense.

    A _multisubstitution_ is the result of applying a list of
    substitutions, which we call an _environment_. *)

Definition env := list (string * tm).

Fixpoint msubst (ss:env) (t:tm) : tm :=
match ss with
| nil => t
| ((x,s)::ss') => msubst ss' <{ [x:=s]t }>
end.

(** We need similar machinery to talk about repeated extension of a
    typing context using a list of (identifier, type) pairs, which we
    call a _type assignment_. *)

Definition tass := list (string * ty).

Fixpoint mupdate (Gamma : context) (xts : tass) :=
  match xts with
  | nil => Gamma
  | ((x,v)::xts') => update (mupdate Gamma xts') x v
  end.

(** We will need some simple operations that work uniformly on
    environments and type assigments *)

Fixpoint lookup {X:Set} (k : string) (l : list (string * X))
              : option X :=
  match l with
    | nil => None
    | (j,x) :: l' =>
      if String.eqb j k then Some x else lookup k l'
  end.

Fixpoint drop {X:Set} (n:string) (nxs:list (string * X))
            : list (string * X) :=
  match nxs with
    | nil => nil
    | ((n',x)::nxs') =>
        if String.eqb n' n then drop n nxs'
        else (n',x)::(drop n nxs')
  end.

(** An _instantiation_ combines a type assignment and a value
    environment with the same domains, where corresponding elements are
    in R. *)

Inductive instantiation :  tass -> env -> Prop :=
| V_nil :
    instantiation nil nil
| V_cons : forall x T v c e,
    value v -> R T v ->
    instantiation c e ->
    instantiation ((x,T)::c) ((x,v)::e).

(** We now proceed to prove various properties of these definitions. *)

(* ###################################################################### *)
(** *** More Substitution Facts *)

(** First we need some additional lemmas on (ordinary) substitution. *)

Lemma vacuous_substitution : forall  t x,
     ~ appears_free_in x t  ->
     forall t', <{ [x:=t']t }> = t.
(* FOLD *)
Proof with eauto.
  (* ADMITTED *)
  induction t; intros; simpl.
  - (* var *)
    destruct (eqb_spec x s)...
    destruct H. subst...
  - (* app *)
    rewrite IHt1... rewrite IHt2...
  - (* abs *)
    destruct (eqb_spec x s)... rewrite IHt...
  - (* tru *) eauto.
  - (* fls *) eauto.
  - (* test *)
    rewrite IHt1... rewrite IHt2... rewrite IHt3...
  - (* pair *)
    rewrite IHt1... rewrite IHt2...
  - (* fst *)
    rewrite IHt...
  - (* snd *)
    rewrite IHt...
Qed.
  (* /ADMITTED *)
(* /FOLD *)

Lemma subst_closed: forall t,
     closed t  ->
     forall x t', <{ [x:=t']t }> = t.
(* FOLD *)
Proof.
  intros. apply vacuous_substitution. apply H.  Qed.
(* /FOLD *)

Lemma subst_not_afi : forall t x v,
    closed v ->  ~ appears_free_in x <{ [x:=v]t }>.
(* FOLD *)
Proof with eauto.  (* rather slow this way *)
  unfold closed, not.
  induction t; intros x v P A; simpl in A.
    - (* var *)
     destruct (eqb_spec x s)...
     inversion A; subst. auto.
    - (* app *)
     inversion A; subst...
    - (* abs *)
     destruct (eqb_spec x s)...
     + inversion A; subst...
     + inversion A; subst...
    - (* tru *)
     inversion A.
    - (* fls *)
     inversion A.
    - (* test *)
     inversion A; subst...
    - (* pair *)
     inversion A; subst...
    - (* fst *)
     inversion A; subst...
    - (* snd *)
     inversion A; subst...
Qed.
(* /FOLD *)

Lemma duplicate_subst : forall t' x t v,
  closed v -> <{ [x:=t]([x:=v]t') }> = <{ [x:=v]t' }>.
(* FOLD *)
Proof.
  intros. eapply vacuous_substitution. apply subst_not_afi. assumption.
Qed.
(* /FOLD *)

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v -> closed v1 ->
    <{ [x1:=v1]([x:=v]t) }> = <{ [x:=v]([x1:=v1]t) }>.
(* FOLD *)
Proof with eauto.
 induction t; intros; simpl.
  - (* var *)
   destruct (eqb_spec x s); destruct (eqb_spec x1 s).
   + subst. exfalso...
   + subst. simpl. rewrite String.eqb_refl. apply subst_closed...
   + subst. simpl. rewrite String.eqb_refl. rewrite subst_closed...
   + simpl. rewrite false_eqb_string... rewrite false_eqb_string...
  (* ADMITTED *)
  - (* app *)
   rewrite IHt1...  rewrite IHt2...
  - (* abs *)
   destruct (eqb_spec x s); destruct (eqb_spec x1 s); subst; simpl.
   + rewrite String.eqb_refl...
   + rewrite String.eqb_refl. rewrite false_eqb_string...
   + rewrite String.eqb_refl. rewrite false_eqb_string...
   + rewrite false_eqb_string... rewrite false_eqb_string...
     rewrite IHt; auto.
   - (* tru *)
     eauto.
   - (* fls *)
     eauto.
   - (* test *)
     f_equal...
   - (* pair *)
   rewrite IHt1... rewrite IHt2...
  - (* fst *)
   rewrite IHt...
  - (* snd *)
   rewrite IHt...
Qed.
  (* /ADMITTED *)
(* /FOLD *)

(* ###################################################################### *)
(** *** Properties of Multi-Substitutions *)

Lemma msubst_closed: forall t, closed t -> forall ss, msubst ss t = t.
(* FOLD *)
Proof.
  induction ss.
    reflexivity.
    destruct a. simpl. rewrite subst_closed; assumption.
Qed.
(* /FOLD *)

(** Closed environments are those that contain only closed terms. *)

Fixpoint closed_env (env:env) :=
  match env with
  | nil => True
  | (x,t)::env' => closed t /\ closed_env env'
  end.

(** Next come a series of lemmas charcterizing how [msubst] of closed terms
    distributes over [subst] and over each term form *)

Lemma subst_msubst: forall env x v t, closed v -> closed_env env ->
    msubst env <{ [x:=v]t }> = <{ [x:=v]  { msubst (drop x env) t }  }> .
(* FOLD *)
Proof.
  induction env0; intros; auto.
  destruct a. simpl.
  inversion H0.
  destruct (eqb_spec s x).
  - subst. rewrite duplicate_subst; auto.
  - simpl. rewrite swap_subst; eauto.
Qed.
(* /FOLD *)

Lemma msubst_var:  forall ss x, closed_env ss ->
   msubst ss (tm_var x) =
   match lookup x ss with
   | Some t => t
   | None => tm_var x
  end.
(* FOLD *)
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
     simpl. destruct (String.eqb s x).
      apply msubst_closed. inversion H; auto.
      apply IHss. inversion H; auto.
Qed.
(* /FOLD *)

Lemma msubst_abs: forall ss x T t,
  msubst ss <{ \ x : T, t }> = <{ \x : T, {msubst (drop x ss) t} }>.
(* FOLD *)
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. destruct (String.eqb s x); simpl; auto.
Qed.
(* /FOLD *)

Lemma msubst_app : forall ss t1 t2,
    msubst ss <{ t1 t2 }> = <{ {msubst ss t1} ({msubst ss t2}) }>.
(* FOLD *)
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite <- IHss. auto.
Qed.
(* /FOLD *)

(** You'll need similar functions for the other term constructors. *)

(* SOLUTION *)
Lemma msubst_pair : forall ss t1 t2,
  msubst ss <{ (t1, t2) }> = <{ ( {msubst ss t1}, {msubst ss t2} ) }>.
Proof.
  induction ss; intros.
     auto.
     destruct a.
      simpl. rewrite <- IHss. auto.
Qed.

Lemma msubst_fst : forall ss t, msubst ss <{ t.fst }> = <{ {msubst ss t}.fst  }>.
Proof.
  induction ss; intros.
    auto.
    destruct a.
      simpl. rewrite <- IHss. auto.
Qed.

Lemma msubst_snd : forall ss t, msubst ss <{ t.snd }> = <{ {msubst ss t}.snd }>.
Proof.
  induction ss; intros.
    auto.
    destruct a.
      simpl. rewrite <- IHss. auto.
Qed.

Lemma msubst_true : forall ss, msubst ss <{ true }> = <{ true }> .
Proof.
  apply msubst_closed.
  intros x H. inversion H.
Qed.

Lemma msubst_false : forall ss, msubst ss <{ false }> = <{ false }>.
Proof.
  apply msubst_closed.
  intros x H. inversion H.
Qed.

Lemma msubst_test : forall ss t0 t1 t2,
  msubst ss <{ if t0 then t1 else t2 }> =
  <{ if {msubst ss t0} then {msubst ss t1} else {msubst ss t2} }>.
Proof.
   induction ss; intros.
     auto.
     destruct a. simpl. auto.
Qed.
(* /SOLUTION *)

(* ###################################################################### *)
(** *** Properties of Multi-Extensions *)

(** We need to connect the behavior of type assignments with that of
    their corresponding contexts. *)

Lemma mupdate_lookup : forall (c : tass) (x:string),
    lookup x c = (mupdate empty c) x.
(* FOLD *)
Proof.
  induction c; intros.
    auto.
    destruct a. unfold lookup, mupdate, update, t_update. destruct (String.eqb s x); auto.
Qed.
(* /FOLD *)

Lemma mupdate_drop : forall (c: tass) Gamma x x',
      mupdate Gamma (drop x c) x'
    = if String.eqb x x' then Gamma x' else mupdate Gamma c x'.
(* FOLD *)
Proof.
  induction c; intros.
  - destruct (eqb_spec x x'); auto.
  - destruct a. simpl.
    destruct (eqb_spec s x).
    + subst. rewrite IHc.
      unfold update, t_update. destruct (eqb_spec x x'); auto.
    + simpl. unfold update, t_update. destruct (eqb_spec s x'); auto.
      subst. rewrite false_eqb_string; congruence.
Qed.
(* /FOLD *)

(* ###################################################################### *)
(** *** Properties of Instantiations *)

(** These are strightforward. *)

Lemma instantiation_domains_match: forall {c} {e},
    instantiation c e ->
    forall {x} {T},
      lookup x c = Some T -> exists t, lookup x e = Some t.
(* FOLD *)
Proof.
  intros c e V. induction V; intros x0 T0 C.
    solve_by_invert.
    simpl in *.
    destruct (String.eqb x x0); eauto.
Qed.
(* /FOLD *)

Lemma instantiation_env_closed : forall c e,
  instantiation c e -> closed_env e.
(* FOLD *)
Proof.
  intros c e V; induction V; intros.
    econstructor.
    unfold closed_env. fold closed_env.
    split; [|assumption].
    eapply typable_empty__closed. eapply R_typable_empty. eauto.
Qed.
(* /FOLD *)

Lemma instantiation_R : forall c e,
    instantiation c e ->
    forall x t T,
      lookup x c = Some T ->
      lookup x e = Some t -> R T t.
(* FOLD *)
Proof.
  intros c e V. induction V; intros x' t' T' G E.
    solve_by_invert.
    unfold lookup in *.  destruct (String.eqb x x').
      inversion G; inversion E; subst.  auto.
      eauto.
Qed.
(* /FOLD *)

Lemma instantiation_drop : forall c env,
    instantiation c env ->
    forall x, instantiation (drop x c) (drop x env).
(* FOLD *)
Proof.
  intros c e V. induction V.
    intros.  simpl.  constructor.
    intros. unfold drop.
    destruct (String.eqb x x0); auto. constructor; eauto.
Qed.
(* /FOLD *)


(* ###################################################################### *)
(** *** Congruence Lemmas on Multistep *)

(** We'll need just a few of these; add them as the demand arises. *)

Lemma multistep_App2 : forall v t t',
  value v -> (t -->* t') -> <{ v t }> -->* <{ v t' }>.
(* FOLD *)
Proof.
  intros v t t' V STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_App2; eauto.  auto.
Qed.
(* /FOLD *)

(* SOLUTION *)
Lemma multistep_Test : forall t1 t1' t2 t3,
  (t1 -->* t1') -> <{ if t1 then t2 else t3 }> -->* <{ if t1' then t2 else t3 }>.
Proof.
  intros t1 t1' t2 t3 STM. induction STM.
  apply multi_refl.
  eapply multi_step.
  apply ST_If; eauto. auto.
Qed.

Lemma multistep_Pair1 : forall t1 t1' t2,
  (t1 -->* t1') -> <{ (t1 , t2) }> -->* <{ (t1', t2) }>.
Proof.
  intros t1 t2' t2 STM. induction STM.
  apply multi_refl.
  eapply multi_step.
  apply ST_Pair1; eauto.
  auto.
Qed.

Lemma multistep_Pair2 : forall v1 t2 t2',
  value v1 -> (t2 -->* t2') -> <{( v1, t2) }> -->* <{ ( v1, t2') }>.
Proof.
  intros v1 t2 t2' V STM. induction STM.
  apply multi_refl.
  eapply multi_step.
  apply ST_Pair2; eauto.
  auto.
Qed.

Lemma multistep_Fst : forall t t',
  (t -->* t') ->  <{ t.fst }> -->* <{ t'.fst }>.
Proof.
  intros t t' STM. induction STM.
  apply multi_refl.
  eapply multi_step.
   apply ST_Fst1; eauto.
   auto.
Qed.

Lemma multistep_Snd : forall t t',
  (t -->* t') -> <{ t.snd }> -->* <{ t'.snd }>.
Proof.
  intros t t' STM. induction STM.
  apply multi_refl.
  eapply multi_step.
   apply ST_Snd1; eauto.
   auto.
Qed.
(* /SOLUTION *)

(* ###################################################################### *)
(** *** The R Lemma *)

(** We can finally put everything together.

    The key lemma about preservation of typing under substitution can
    be lifted to multi-substitutions: *)

Lemma msubst_preserves_typing : forall c e,
     instantiation c e ->
     forall Gamma t S, (mupdate Gamma c) |-- t \in S ->
     Gamma |-- { (msubst e t) } \in S.
(* FOLD *)
Proof.
    intros c e H. induction H; intros.
    simpl in H. simpl. auto.
    simpl in H2.  simpl.
    apply IHinstantiation.
    eapply substitution_preserves_typing; eauto.
    apply (R_typable_empty H0).
Qed.
(* /FOLD *)

(** And at long last, the main lemma. *)

Lemma msubst_R : forall c env t T,
    (mupdate empty c) |-- t \in T ->
    instantiation c env ->
    R T (msubst env t).
(* FOLD *)
Proof.
  intros c env0 t T HT V.
  generalize dependent env0.
  (* We need to generalize the hypothesis a bit before setting up the induction. *)
  remember (mupdate empty c) as Gamma.
  assert (forall x, Gamma x = lookup x c).
    intros. rewrite HeqGamma. rewrite mupdate_lookup. auto.
  clear HeqGamma.
  generalize dependent c.
  induction HT; intros.

  - (* T_Var *)
   rewrite H0 in H. destruct (instantiation_domains_match V H) as [t P].
   eapply instantiation_R; eauto.
   rewrite msubst_var.  rewrite P. auto. eapply instantiation_env_closed; eauto.

  - (* T_Abs *)
    rewrite msubst_abs.
    (* We'll need variants of the following fact several times, so its simplest to
       establish it just once. *)
    assert (WT : empty |-- \x : T2, {msubst (drop x env0) t1 } \in (T2 -> T1) ).
    { eapply T_Abs. eapply msubst_preserves_typing.
      { eapply instantiation_drop; eauto. }
      eapply context_invariance.
      { apply HT. }
      intros.
      unfold update, t_update. rewrite mupdate_drop. destruct (eqb_spec x x0).
      + auto.
      + rewrite H.
        clear - c n. induction c.
        simpl.  rewrite false_eqb_string; auto.
        simpl. destruct a.  unfold update, t_update.
        destruct (String.eqb s x0); auto. }
    unfold R. fold R. split.
       auto.
     split. apply value_halts. apply v_abs.
     intros.
     destruct (R_halts H0) as [v [P Q]].
     pose proof (multistep_preserves_R _ _ _ P H0).
     apply multistep_preserves_R' with (msubst ((x,v)::env0) t1).
       eapply T_App. eauto.
       apply R_typable_empty; auto.
       eapply multi_trans.  eapply multistep_App2; eauto.
       eapply multi_R.
       simpl.  rewrite subst_msubst.
       eapply ST_AppAbs; eauto.
       eapply typable_empty__closed.
       apply (R_typable_empty H1).
       eapply instantiation_env_closed; eauto.
       eapply (IHHT ((x,T2)::c)).
          intros. unfold update, t_update, lookup. destruct (String.eqb x x0); auto.
       constructor; auto.

  - (* T_App *)
    rewrite msubst_app.
    destruct (IHHT1 c H env0 V) as [_ [_ P1]].
    pose proof (IHHT2 c H env0 V) as P2.  fold R in P1.  auto.

  (* ADMITTED *)
  - (* T_True *)
    rewrite msubst_true.
    unfold R. split.
    apply T_True.
    split.  unfold halts.  exists <{ true }>. split. apply multi_refl. apply v_true. auto.

  - (* T_False *)
    rewrite msubst_false.
    unfold R. split.
    apply T_False.
    split.  unfold halts.  exists <{ false }>. split. apply multi_refl.
    apply v_false. auto.

  - (* T_If *)
    rewrite msubst_test.
    assert (WT : empty |-- if {msubst env0 t1} then {msubst env0 t2} else {msubst env0 t3} \in T1 ).
      apply T_If; eapply msubst_preserves_typing; eauto;
        eapply context_invariance; eauto; intros;
        rewrite <- mupdate_lookup;  auto.
    pose proof (IHHT1 c H env0 V) as IH1.
    destruct (R_halts IH1) as [v [P Q]].
    assert (R <{ Bool }> v).
        eapply multistep_preserves_R. apply P. apply IH1.
   (* The following is a somewhat easier approach than that taken
      in Pierce's TAPL sample solutions; in essence we apply canonical
      forms, on the fly. *)
   pose proof (R_typable_empty H0).
   inversion Q; subst.
      (* abs : impossible *)
      inversion H1.

      (* true *)
      eapply multistep_preserves_R' with (msubst env0 t2).
      assumption.
      eapply multi_trans. apply multistep_Test. eapply P.
      eapply multi_R. apply ST_IfTrue.
      apply (IHHT2 c H env0 V).

      (* false *)
      eapply multistep_preserves_R' with (msubst env0 t3).
      assumption.
      eapply multi_trans. apply multistep_Test. eapply P.
      eapply multi_R. apply ST_IfFalse.
      apply (IHHT3 c H env0 V).

      (* pair : impossible *)
      inversion H1.

  - (* T_Pair *)
    rewrite msubst_pair.
    pose proof (IHHT1 c H env0 V) as  IH1.
    pose proof (IHHT2 c H env0 V) as IH2.
    assert (WT : empty |-- ( {msubst env0 t1}, {msubst env0 t2} ) \in (T1 * T2) ).
       apply T_Pair. apply (R_typable_empty IH1). apply (R_typable_empty IH2).
    destruct (R_halts IH1) as [v1 [P1 Q1]].
    destruct (R_halts IH2) as [v2 [P2 Q2]].
    assert (H1: R T1 v1).
       eapply multistep_preserves_R. apply P1. apply IH1.
    assert (H2: R T2 v2).
       eapply multistep_preserves_R. apply P2. apply IH2.
    assert (WE : <{ ( {msubst env0 t1} , {msubst env0 t2} ) }> -->* <{ (v1,v2) }> ).
       apply multi_trans with <{ (v1, {msubst env0 t2} ) }>.
       apply multistep_Pair1. assumption.
       apply multistep_Pair2. assumption. assumption.
    unfold R; fold R.
    split. assumption.
    split. unfold halts. exists <{ (v1,v2) }>.
    split. assumption.
    apply v_pair; auto.
    split.
    eapply multistep_preserves_R'.
    apply T_Fst with T2. assumption.
    apply multi_trans with <{ (v1,v2).fst }>.
      apply multistep_Fst. assumption.
      apply multi_R. apply ST_FstPair; auto.
    assumption.
    eapply multistep_preserves_R'.
    apply T_Snd with T1. assumption.
    apply multi_trans with <{ (v1,v2).snd }>.
      apply  multistep_Snd. assumption.
      apply multi_R.  apply ST_SndPair; auto.
    assumption.

  - (* T_Fst *)
    rewrite msubst_fst.
    pose proof (IHHT c H env0 V) as IH.
    unfold R in IH.  fold R in IH. inversion IH. inversion H1.
    inversion H3. assumption.

  - (* T_Snd *)
    rewrite msubst_snd.
    pose proof (IHHT c H env0 V) as IH.
    unfold R in IH.  fold R in IH. inversion IH. inversion H1.
    inversion H3. assumption.

Qed.
(* /ADMITTED *)
(* /FOLD *)

(* ###################################################################### *)
(** *** Normalization Theorem *)

(** And the final theorem: *)

Theorem normalization : forall t T, empty |-- t \in T -> halts t.
(* FOLD *)
Proof.
  intros.
  replace t with (msubst nil t) by reflexivity.
  apply (@R_halts T).
  apply (msubst_R nil); eauto.
  eapply V_nil.
Qed.
(* /FOLD *)

(* HIDE *)
(* ###################################################################### *)
(* ###################################################################### *)
(* ###################################################################### *)

Module GoingNegative.

(* At OPLSS10, Harper gave a blackboard presentation of this proof,
jokingly calling the system "Goedel's B". He emphasized that an important
choice to be made when defining R for a particular type constructor is
whether to treat it "positively," where the relation explicitly enforces
termination at the type, or "negatively," where the relation describes
the behavior of values of the type indirectly.    For example, the following
definition treats the base type of booleans positively (we really have
no choice here) and functions and pairs negatively:

- [R bool t] iff [t] is a closed term of type [bool] and [t] halts in
  a value ([true] or [false]).

- [R (T1 -> T2) t] iff [t] is a closed term of type [T1 -> t2] _and_
  for any term [s] such that [R T1 s], we have [R T2 (t s)].

- [R (T1 x T2) t] iff [t] is a closed term of type [T1 x T2] _and_
  [R (fst t) T1] and [R (snd t) T2].

Alternatively, here are "positive" characterizations of functions and pairs:

- [R (T1 -> T2) t] iff [t] is a closed term of type [T1 -> T2] and
  [t] halts in a value of the form [\x:T1.t2] and [R T2 t2].

- [R (T1 x T2) t] iff [t] is a closed term of type [T1 x T2] _and_
  [t] halts in a value of the form [(t1,t2)] where [R T1 t1] and
  [R T2 t2].

For these types, the main intution is that the "negative" form
makes the proof easy for the elimination cases, but hard for
the introduction forms, and vice-versa for the "positive" forms.
For other types, it might be that only one characterization makes
the proof work, e.g., sums need to be done positively.

Seen in this light, the proof in the main body above is a bit weird,
because the definition of [R] mixes elements of negative and positive.
In particular, for arrows and pairs, the definition of [R] requires
_both_ the "negative" form _and_ the "positive" form. This actually
seems to work out fairly well in making the proof go through.
But to show that a weaker invariant also suffices, here is a
more "purely negative" version of the proof. The main difference
is that the proof that [R T t] implies [t] halts is no longer trivial.
Following Harper, this property is shown as a simultaneous induction
with the property that  [R T] is inhabited for every [T]. *)


Fixpoint R (T:ty) (t:tm) : Prop :=
  has_type empty t T /\
  (match T with
   | <{ Bool }>  => t -->* <{ true }> \/ t -->* <{ false }>
   | <{ T1 -> T2 }> => (forall s, R T1 s -> R T2 <{ t s }> )
(* SOLUTION *)
   | <{ T1 * T2 }> => (R T1 <{ t.fst }> ) /\ (R T2 <{ t.snd }> )
(* /SOLUTION *)
(* UNCOMMENT WHEN HIDING SOLUTIONS
   | Prod T1 T2 => False (* ... and delete this line *)
/UNCOMMENT *)
   end).


(** As immediate consequnces of this definition, we have that every element of
every set [R_T] is closed with type [t] :*)

Lemma R_typable_empty : forall {T} {t}, R T t -> empty |-- t \in T.
Proof.
  intros. destruct T; unfold R in H; inversion H; assumption.
Qed.


(* ###################################################################### *)
(** **  Membership in [R_T] is Invariant Under Reduction *)

(** We start with a preliminary lemma that shows a kind of strong
    preservation property, namely that membership in [R_T] is
    _invariant_ under reduction. We will need this property in both
    directions, i.e., both to show that a term in [R_T] stays in [R_T]
    when it takes a forward step, and to show that any term that ends
    up in [R_T] after a step must have been in [R_T] to begin with.

    First of all, an easy preliminary lemma. Note that in the forward
    direction the proof depends on the fact that our language is
    determinstic. This lemma might still be true for nondeterministic
    languages, but the proof would be harder! *)

Lemma step_preserves_halting : forall t t', (t --> t') -> (halts t <-> halts t').
Proof.
 intros t t' ST.  unfold halts.
 split.
 - (* -> *)
  intros [t'' [STM V]].
  inversion STM; subst.
   exfalso.  apply value__normal in V. unfold normal_form in V. apply V. exists t'. auto.
   rewrite (step_deterministic _ _ _ ST H). exists t''. split; assumption.
 - (* <- *)
  intros [t'0 [STM V]].
  exists t'0. split; eauto.
Qed.

(** Now the main lemma, which comes in two parts, one for each direction.
   Each proceeds by induction on the structure of the type [T].  In fact,
   this is where we make fundamental use of the finiteness of types.

   One requirement for staying in [R_T] is to stay in type [T]. In the
   forward direction, we get this from ordinary type Preservation. *)

Lemma step_preserves_R : forall T t t', (t --> t') -> R T t -> R T t'.
Proof.
 induction T;  intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [typable_empty_t RRt].
  (* Bool *)
  split. eapply preservation; eauto.
  inversion RRt.
     left.  inversion H; subst.  inversion E.
          rewrite (step_deterministic _ _ _ E H0). auto.
     right. inversion H; subst. inversion E.
         rewrite (step_deterministic _ _ _ E H0). auto.
  (* Arrow *)
  split. eapply preservation; eauto.
  intros.
  eapply IHT2.
  apply  ST_App1. apply E.
  apply RRt; auto.
  (* ADMITTED *)
  (* Prod *)
  split. eapply preservation; eauto.
  inversion RRt. split; eauto.  Qed.
  (* /ADMITTED *)


(** The generalization to multiple steps is trivial: *)

Lemma multistep_preserves_R : forall T t t', (t -->* t') -> R T t -> R T t'.
Proof.
  intros T t t' STM; induction STM; intros.
  assumption.
  apply IHSTM. eapply step_preserves_R. apply H. assumption.
Qed.

(** In the reverse direction, we must add the fact that [t] is has type [T] before stepping
   as a additional hypothesis. *)
Lemma step_preserves_R' : forall T t t', empty |-- t \in T -> (t --> t') -> R T t' -> R T t.
Proof.
  (* ADMITTED *)
  induction T; intros t t' typable_empty_t E Rt'; unfold R; fold R; unfold R in Rt'; fold R in Rt';
               destruct Rt' as [typable_empty_t' RRt'].
  (* Bool *)
  split. assumption.
  inversion RRt'.
     left.  eapply multi_step; eauto.
     right. eapply multi_step; eauto.
  (* Arrow *)
  split. assumption.
  intros.
  eapply IHT2. eapply T_App.  apply typable_empty_t.
  eapply R_typable_empty. assumption.
  apply  ST_App1. apply E.
  apply RRt'; auto.
  (* Prod *)
  split.  assumption.
  inversion RRt'. split; eauto. Qed.
  (* /ADMITTED *)

Lemma multistep_preserves_R' : forall T t t', empty |-- t \in T -> (t -->* t') -> R T t' -> R T t.
Proof.
  intros T t t' HT STM.
  induction STM; intros.
    assumption.
    eapply step_preserves_R'.  assumption. apply H. apply IHSTM.
    eapply preservation;  eauto. auto.
Qed.

Lemma halts_app1 : forall t T1 T2 t1, empty |-- t \in (T1 -> T2) -> halts <{t t1}> ->
          exists x T t0, t -->* <{ \ x : T, t0 }> .
  unfold halts. intros. inversion H0 as [v' [P V]]. clear H0.
  remember <{ t t1 }> as u.  generalize dependent t1. generalize dependent t. induction P; intros.
    rewrite Hequ in V. inversion V.
    rewrite Hequ in H. inversion H; subst.
      exists x0, T0, t0. eauto.
      pose proof (preservation _ _ _ H0 H4).
      destruct (IHP V t1' H1 t1 (refl_equal _)) as [x [T [t0 Q]]].
      exists x, T, t0. eauto.
      inversion H3; try (subst; solve_by_invert).
         exists x, T0, t0.  eauto.
Qed.

Lemma halts_fst : forall t, halts <{ t.fst }>  -> exists v1 v2, value v1 /\ value v2 /\ t -->* <{ (v1,v2) }>.
  unfold halts. intros. inversion H as [v' [P V]]. clear H.
  remember <{ t.fst }> as u.  generalize dependent t. induction P; intros.
    rewrite Hequ in V; inversion V.
    rewrite Hequ in H. inversion H; subst.
       destruct (IHP V t0' (refl_equal _)) as [v1 [v2 [V1 [V2 Q]]]].
          exists v1, v2. split; auto.  split; auto.  eauto.
       exists y, v2. eauto.
Qed.

Lemma R_inhabited_and_halts : forall T,
      (exists t, R T t) /\ (forall t, R T t -> halts t).
Proof.
  induction T.
    (* Bool *)
    split.
     exists <{ true }> . unfold R.  split; auto.
     intros t H; simpl in H; destruct H.  destruct H0. exists <{ true }>; split; auto. exists <{ false }>; split; auto.
    (* Arrow *) inversion IHT1 as [[t1 P1] Q1]. clear IHT1. inversion IHT2 as [[t2 P2] Q2].  clear IHT2.
    split.
     (* inhabited *)
     remember "x"%string as x.
     exists <{ \ x: T1, t2 }>. simpl.
       assert (has_type empty t2 T2).  apply (R_typable_empty P2).
       split.
         constructor. eapply context_invariance; eauto. intros. apply typable_empty__closed in H. contradiction (H x0).
         intros.
         pose proof (Q1 _ H0). inversion H1.
         eapply multistep_preserves_R'. eapply T_App. eapply T_Abs.
            eapply context_invariance; eauto. intros. apply typable_empty__closed in H. contradiction (H x1).
         apply (R_typable_empty H0).
         eapply multi_trans. eapply multistep_App2. auto.  inversion H2. apply H3.
         eapply multi_R. eapply ST_AppAbs. inversion H2; auto. assert (<{ [x:=x0]t2 }> = t2).
         apply vacuous_substitution.  apply (typable_empty__closed _ _ H).  rewrite H3. auto.
     (* halts *)
      intros t H; simpl in H; destruct H.
      pose proof (H0 _ P1).  pose proof (Q2 _ H1).
      destruct (halts_app1 _ _ _ _ H H2) as [x [T [t0 S]]].
      unfold halts; eauto.
    (* Pair *)
    inversion IHT1 as [[t1 P1] Q1]. clear IHT1.  inversion IHT2 as [[t2 P2] Q2]. clear IHT2.
    split.
     (* inhabited *)
      unfold halts in Q1, Q2.  destruct (Q1 _ P1) as [t1' [R1 V1]].  destruct (Q2 _ P2) as [t2' [R2 V2]].
      exists <{ (t1', t2') }>. simpl.
      assert (empty |-- ( t1', t2') \in ( T1 * T2) ).
        apply T_Pair; eapply R_typable_empty; eauto; eapply multistep_preserves_R; eauto.
      split.  auto. split.
          eapply multistep_preserves_R'.
             eapply T_Fst; eauto. eapply multi_R.
             eapply ST_FstPair; eauto. eapply multistep_preserves_R; eauto.
          eapply multistep_preserves_R'.
             eapply T_Snd.  eauto. eapply multi_R.
             eapply ST_SndPair; eauto. eapply multistep_preserves_R; eauto.
     (* halts *)
       unfold R.  fold R.  intros t [HT [Rfst Rsnd]].
       pose proof (Q1 _ Rfst).
       destruct (halts_fst t H) as [v1 [v2 [V1 [V2 Q]]]].
       unfold halts. exists <{ (v1 , v2) }>.  split; eauto.
Qed.

Lemma R_halts : forall {T} t, R T t -> halts t.
Proof.
  intros. destruct (R_inhabited_and_halts T). auto.
Qed.

(** Re-define instantiations, etc. *)

(** An _instantiation_ combines a type assignment and a value environment with the same domains,
   where corresponding elements are in R *)

Inductive instantiation :  tass -> env -> Prop :=
| V_nil : instantiation nil nil
| V_cons : forall x T v c e, value v -> R T v -> instantiation c e -> instantiation ((x,T)::c) ((x,v)::e).


(* ###################################################################### *)
(** *** Properties of Instantiations *)

(** These are strightforward. *)

Lemma instantiation_domains_match: forall {c} {e},
  instantiation c e -> forall {x} {T}, lookup x c = Some T -> exists t, lookup x e = Some t.
Proof.
  intros c e V. induction V; intros x0 T0 C.
    solve_by_invert.
    simpl in *.
    destruct (String.eqb x x0); eauto.
Qed.

Lemma instantiation_env_closed : forall c e,  instantiation c e -> closed_env e.
Proof.
  intros c e V; induction V; intros.
    econstructor.
    unfold closed_env. fold closed_env.
    split.  eapply typable_empty__closed. eapply R_typable_empty. eauto.
        auto.
Qed.

Lemma instantiation_R : forall c e, instantiation c e ->
                        forall x t T, lookup x c = Some T ->
                                      lookup x e = Some t -> R T t.
Proof.
  intros c e V. induction V; intros x' t' T' G E.
    solve_by_invert.
    unfold lookup in *.  destruct (String.eqb x x').
      inversion G; inversion E; subst.  auto.
      eauto.
Qed.

Lemma instantiation_drop : forall c env,
  instantiation c env -> forall x, instantiation (drop x c) (drop x env).
Proof.
  intros c e V. induction V.
    intros.  simpl.  constructor.
    intros. unfold drop. destruct (String.eqb x x0); auto. constructor; eauto.
Qed.


(* ###################################################################### *)
(** *** The R Lemma. *)

(** We finally put everything together.

    The key lemma about preservation of typing under substitution can be
    lifted to multi-substitutions: *)

Lemma msubst_preserves_typing : forall c e,
     instantiation c e ->
     forall Gamma t S, (mupdate Gamma c) |-- t \in S ->
      Gamma |-- { (msubst e t) } \in S.
Proof.
  intros c e H. induction H; intros.
    simpl in H. simpl. auto.
    simpl in H2.  simpl.
    apply IHinstantiation.
    eapply substitution_preserves_typing; eauto.
    apply (R_typable_empty H0).
Qed.

(** And at long last, the main lemma. *)

Lemma msubst_R : forall c env t T, (mupdate empty c) |-- t \in T -> instantiation c env -> R T (msubst env t).
Proof.
  intros c env0 t T HT V.
  generalize dependent env0.
  (* We need to generalize the hypothesis a bit before setting up the induction. *)
  remember (mupdate empty c) as Gamma.
  assert (forall x, Gamma x = lookup x c).
    intros. rewrite HeqGamma. rewrite mupdate_lookup. auto.
  clear HeqGamma.
  generalize dependent c.
  induction HT; intros.

  - (* T_Var *)
   rewrite H0 in H. destruct (instantiation_domains_match V H) as [t P].
   eapply instantiation_R; eauto.
   rewrite msubst_var.  rewrite P. auto. eapply instantiation_env_closed; eauto.

  - (* T_Abs *)
    rewrite msubst_abs.
    (* We'll need variants of the following fact several times, so its simplest to
       establish it just once. *)
    assert (WT: empty |-- (\x :T2, {msubst (drop x env0) t1}) \in (T2 -> T1)).
     eapply T_Abs. eapply msubst_preserves_typing.  eapply instantiation_drop; eauto.
      eapply context_invariance.  apply HT.
      intros.
      unfold update, t_update. rewrite mupdate_drop. destruct (eqb_spec x x0).  auto.
        rewrite H.
          clear - c n. induction c.
              simpl.  rewrite false_eqb_string; auto.
              simpl. destruct a.  unfold update, t_update. destruct (String.eqb s x0); auto.
    unfold R. fold R. split.
       auto.
     intros.
     destruct (R_halts _ H0) as [v [P Q]].
     pose proof (multistep_preserves_R _ _ _ P H0).
     apply multistep_preserves_R' with (msubst ((x,v)::env0) t1).
       eapply T_App. eauto.
       apply R_typable_empty; auto.
       eapply multi_trans.  eapply multistep_App2; eauto.
       eapply multi_R.
       simpl.  rewrite subst_msubst.
       eapply ST_AppAbs; eauto.
       eapply typable_empty__closed.
       apply (R_typable_empty H1).
       eapply instantiation_env_closed; eauto.
       eapply (IHHT ((x,T2)::c)).
          intros. unfold update, t_update, lookup. destruct (String.eqb x x0); auto.
       constructor; auto.

  - (* T_App *)
    rewrite msubst_app.
    destruct (IHHT1 c H env0 V) as [_ P1].
    pose proof (IHHT2 c H env0 V) as P2.  fold R in P1.  auto.

  (* ADMITTED *)

  - (* T_True *)
    rewrite msubst_true.
    unfold R. split.
    apply T_True.
    left. eauto.

  - (* T_False *)
    rewrite msubst_false.
    unfold R. split.
    apply T_False.
    right. eauto.

  - (* T_Test *)
    rewrite msubst_test.
    assert (WT: empty |-- (if {msubst env0 t1} then {msubst env0 t2} else {msubst env0 t3}) \in T1).
      apply T_If; eapply msubst_preserves_typing; eauto;
        eapply context_invariance; eauto; intros; rewrite <- mupdate_lookup;  auto.
    pose proof (IHHT1 c H env0 V) as IH1.
    destruct (R_halts _ IH1) as [v [P Q]].
    assert (R <{ Bool }> v).
        eapply multistep_preserves_R. apply P. apply IH1.
   (* The following is a somewhat easier approach than that taken in Pierce's TAPL sample solutions;
      in essence we apply canonical forms,  on the fly *)
   pose proof (R_typable_empty H0).
   inversion Q; subst.
      (* abs : impossible *)
      inversion H1.

      (* true *)
      eapply multistep_preserves_R' with (msubst env0 t2).
      assumption.
      eapply multi_trans. apply multistep_Test. eapply P.
      eapply multi_R. apply ST_IfTrue.
      apply (IHHT2 c H env0 V).

      (* false *)
      eapply multistep_preserves_R' with (msubst env0 t3).
      assumption.
      eapply multi_trans. apply multistep_Test. eapply P.
      eapply multi_R. apply ST_IfFalse.
      apply (IHHT3 c H env0 V).

      (* pair : impossible *)
      inversion H1.


  - (* T_Pair *)
    rewrite msubst_pair.
    pose proof (IHHT1 c H env0 V) as  IH1.
    pose proof (IHHT2 c H env0 V) as IH2.
    assert (WT: empty |-- ({msubst env0 t1}, {msubst env0 t2}) \in
                         (T1 * T2)).
       apply T_Pair. apply (R_typable_empty IH1). apply (R_typable_empty IH2).
    destruct (R_halts _ IH1) as [v1 [P1 Q1]].
    destruct (R_halts _ IH2) as [v2 [P2 Q2]].
    assert (H1: R T1 v1).
       eapply multistep_preserves_R. apply P1. apply IH1.
    assert (H2: R T2 v2).
       eapply multistep_preserves_R. apply P2. apply IH2.
    assert (WE: <{( {msubst env0 t1}, {msubst env0 t2}) }> -->* <{ (v1, v2) }> ).
       apply multi_trans with <{ (v1, {msubst env0 t2} ) }>.
       apply multistep_Pair1. assumption.
       apply multistep_Pair2. assumption. assumption.
    unfold R; fold R.
    split. assumption.
    split.
    eapply multistep_preserves_R'.
    apply T_Fst with T2. assumption.
    apply multi_trans with (<{ (v1,v2).fst }>).
      apply multistep_Fst. assumption.
      apply multi_R. apply ST_FstPair; auto.
    assumption.
    eapply multistep_preserves_R'.
    apply T_Snd with T1. assumption.
    apply multi_trans with (<{ (v1,v2).snd }>).
      apply  multistep_Snd. assumption.
      apply multi_R.  apply ST_SndPair; auto.
    assumption.

  - (* T_Fst *)
    rewrite msubst_fst.
    pose proof (IHHT c H env0 V) as IH.
    unfold R in IH.  fold R in IH. inversion IH. inversion H1.  assumption.

  - (* T_Snd *)
    rewrite msubst_snd.
    pose proof (IHHT c H env0 V) as IH.
    unfold R in IH.  fold R in IH. inversion IH. inversion H1.  assumption.

Qed.
(* /ADMITTED *)

(* ###################################################################### *)
(** *** Normalization Theorem *)

Theorem normalization : forall t T, empty |-- t \in T -> halts t.
Proof.
  intros.
  replace t with (msubst nil t) by reflexivity.
  apply (@R_halts T).
  apply (msubst_R nil); eauto.
  eapply V_nil.
Qed.

End GoingNegative.

(* /HIDE *)
