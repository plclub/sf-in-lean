(** * Rel: Properties of Relations *)

(** This short (and optional) chapter develops some basic definitions
    and a few theorems about binary relations in Rocq.  The key
    definitions are repeated where they are actually used (in the
    \CHAPV2{Smallstep} chapter of _Programming Language Foundations_),
    so readers who are already comfortable with these ideas can safely
    skim or skip this chapter.  However, relations are also a good
    source of exercises for developing facility with Rocq's basic
    reasoning facilities, so it may be useful to look at this material
    just after the [IndProp] chapter. *)
(* SOONER: The chapter `Rel` is useful for `Imp`,
   but does not otherwise seem consistent with the earlier chapters.
   It is especially unclear what results are allowed to be used
   in the proofs of some of the reoccurring theorems. *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden".
From LF Require Export IndProp.
(* TERSE: /HIDEFROMHTML *)

(** * Relations *)

(** A binary _relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)
(* SOONER: They've already seen lots of non-binary relations,
   e.g., evaluation of Imp programs was also a relation *)

Definition relation (X: Type) := X -> X -> Prop.

(* FULL *)
(** Somewhat confusingly, the Rocq standard library hijacks the generic
    term "relation" for this specific instance of the idea. To
    maintain consistency with the library, we will do the same.  So,
    henceforth, the Rocq identifier [relation] will always refer to a
    binary relation _on_ some set (between the set and itself),
    whereas in ordinary mathematical English the word "relation" can
    refer either to this specific concept or the more general concept
    of a relation between any number of possibly different sets.  The
    context of the discussion should always make clear which is
    meant. *)
(* /FULL *)

(** An example relation on [nat] is [le], the less-than-or-equal-to
    relation, which we usually write [n1 <= n2]. *)

Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.
(** (Why did we write it this way instead of starting with [Inductive
    le : relation nat...]?  Because we wanted to put the first [nat]
    to the left of the [:], which makes Rocq generate a somewhat nicer
    induction principle for reasoning about [<=].) *)

(* ######################################################### *)
(** * Basic Properties *)

(* FULL *)
(** As anyone knows who has taken an undergraduate discrete math
    course, there is a lot to be said about relations in general,
    including ways of classifying relations (as reflexive, transitive,
    etc.), theorems that can be proved generically about certain sorts
    of relations, constructions that build one relation from another,
    etc.  For example... *)
(* /FULL *)

(** *** Partial Functions *)

(** A relation [R] on a set [X] is a _partial function_ if, for every
    [x], there is at most one [y] such that [R x y] -- i.e., [R x y1]
    and [R x y2] together imply [y1 = y2]. *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(** For example, the [next_nat] relation is a partial function. *)
Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Check next_nat : relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
(* FOLD *)
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed.
(* /FOLD *)

(** However, the [<=] relation on numbers is not a partial
    function.  (Assume, for a contradiction, that [<=] is a partial
    function.  But then, since [0 <= 0] and [0 <= 1], it follows that
    [0 = 1].  This is nonsense, so our assumption was
    contradictory.) *)

Theorem le_not_a_partial_function :
  ~ (partial_function le).
(* FOLD *)
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense.   Qed.
(* /FOLD *)

(* FULL *)
(* EX2? (total_relation_not_partial_function) *)
(** Show that the [total_relation] defined in (an exercise in)
    \CHAP{IndProp} is not a partial function. *)

(** Copy the definition of [total_relation] from your \CHAP{IndProp}
    here so that this file can be graded on its own.  *)
Inductive total_relation : nat -> nat -> Prop :=
  (* SOLUTION *)
  | tot n m : total_relation n m
(* /SOLUTION *)
.

Theorem total_relation_not_partial_function :
  ~ (partial_function total_relation).
Proof.
  (* ADMITTED *)
  unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense.
    apply Hc with 0. apply tot. apply tot.
  discriminate Nonsense. Qed.
(* /ADMITTED *)
(** [] *)

(* EX2? (empty_relation_partial_function) *)
(** Show that the [empty_relation] defined in (an exercise in)
    \CHAP{IndProp} is a partial function. *)

(** Copy the definition of [empty_relation] from your \CHAP{IndProp}
    here so that this file can be graded on its own.  *)
Inductive empty_relation : nat -> nat -> Prop :=
  (* SOLUTION *)
(* /SOLUTION *)
.

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  (* ADMITTED *)
  unfold partial_function. intros n y1 y2 H1 H2. inversion H1. Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** *** Reflexive Relations *)

(** A _reflexive_ relation on a set [X] is one for which every element
    of [X] is related to itself. *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
(* FOLD *)
Proof.
  unfold reflexive. intros n. apply le_n.  Qed.
(* HIDE: The lemma [le_refl] in the standard library is exactly like
   this except that 'reflexive' is not a definition. :-( *)
(* /FOLD *)

(** *** Transitive Relations *)

(** A relation [R] is _transitive_ if [R a c] holds whenever [R a b]
    and [R b c] do. *)

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
(* FOLD *)
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo.  Qed.
(* /FOLD *)

(* FULL *)
Theorem lt_trans:
  transitive lt.
(* FOLD *)
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.
(* /FOLD *)

(* EX2? (le_trans_hard_way) *)
(** We can also prove [lt_trans] more laboriously by induction,
    without using [le_trans].  Do this. *)

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that [m] is less than [o]. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    (* ADMITTED *)
    - (* le_m *) apply le_S in Hnm. apply Hnm.
    - (* le_S *) apply le_S in IHHm'o. apply IHHm'o.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX2? (lt_trans'') *)
(** Prove the same thing again by induction on [o]. *)

Theorem lt_trans'' :
  transitive lt.
(* FOLD *)
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  (* ADMITTED *)
    - (* o = 0 *) inversion Hmo.
    - (* o = S o' *) inversion Hmo.
      + (* le_n *) rewrite -> H0 in Hnm. apply le_S in Hnm. apply Hnm.
      + (* le_S *) apply IHo' in H0. apply le_S in H0. apply H0.  Qed.
(* /ADMITTED *)
(* /FOLD *)
(** [] *)

(** The transitivity of [le], in turn, can be used to prove some facts
    that will be useful later (e.g., for the proof of antisymmetry
    below)... *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
(* FOLD *)
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.
(* /FOLD *)

(* SOONER: AC: This statment is exactly the same as [Sn_le_Sm__n_le_m]
   from [IndProp], which is imported here. *)
(* EX1? (le_S_n) *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  (* ADMITTED *)
  intros n m H. inversion H.
  - (* le_n *)
    apply le_n.
  - (* le_S *)
    apply le_Sn_le. apply H1.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX2? (le_Sn_n_inf) *)
(** Provide an informal proof of the following theorem:

    Theorem: For every [n], [~ (S n <= n)]

    A formal proof of this is an optional exercise below, but try
    writing an informal proof without doing the formal proof first.

    Proof: *)
    (* SOLUTION *)
(** By induction on [n].

    - Suppose first that [n = 0].  Then we must show [~ (S 0 <=
      0)].  But this follows immediately from the definition of
      [<=], since neither [le_n] nor [le_S] can be used to prove
      [~ (S 0 <= 0)].

    - Next, suppose [n = S n'] for some [n'] with [~ (S n' <= n')].
      We must show [~ (S n <= n)] -- that is, [~ (S (S n') <= (S
      n'))].  Suppose, for a contradiction, that [S (S n') <= (S
      n')].  Then, by lemma [le_S_n], we have [S n' <= n'], which
      contradicts the induction hypothesis. *)
    (* /SOLUTION *)
(** [] *)

(* EX1? (le_Sn_n) *)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  (* ADMITTED *)
  induction n as [| n'].
    - (* n = 0 *) intros H. inversion H.
    - (* n = S n' *) intros H. unfold not in IHn'. apply IHn'.
      apply le_S_n. apply H.  Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** Reflexivity and transitivity are the main concepts we'll need for
    later chapters, but, for a bit of additional practice working with
    relations in Rocq, let's look at a few other common ones... *)

(** *** Symmetric and Antisymmetric Relations *)

(** A relation [R] is _symmetric_ if [R a b] implies [R b a]. *)

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(* FULL *)
(* EX2? (le_not_symmetric) *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  (* ADMITTED *)
  unfold symmetric. intros H.
  assert (1 <= 0) as Nonsense.
  { (* Proof of assertion. *) apply H. apply le_S. apply le_n. }
  inversion Nonsense.  Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** A relation [R] is _antisymmetric_ if [R a b] and [R b a] together
    imply [a = b] -- that is, if the only "cycles" in [R] are trivial
    ones. *)

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(* FULL *)
(* EX2? (le_antisymmetric) *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  (* ADMITTED *)
  (* Here is a pretty proof due to Jianzhou Zhao: *)
  unfold antisymmetric. induction a as [| a'].
    - (* a = 0 *) intros b H1 H2. inversion H2. reflexivity.
    - (* a = S a' *) intros b H1 H2. destruct b as [| b'].
      + (* b = 0 *) inversion H1.
      + (* b = S b' *)
         apply le_S_n in H1.
         apply le_S_n in H2.
         apply IHa' in H1.
            rewrite H1. reflexivity.
            apply H2.  Qed.

(* Here is another solution, by induction on the evidence for [le]. *)
Theorem le_antisymmetric' :
  antisymmetric le.
Proof.
  unfold antisymmetric. intros a b Hab Hba. induction Hab.
  - (* b = a *)
    reflexivity.
  - (* b = S m, a <= m *)
    apply le_S in Hab.
    assert (m <= a) as Hma. apply le_Sn_le. apply Hba.
    apply IHHab in Hma.
    rewrite -> Hma in Hba.
    apply le_Sn_n in Hba.
    destruct Hba. Qed.

(* An uglier way of getting there: *)
Theorem le_antisymmetric'' :
  antisymmetric le.
Proof.
  unfold antisymmetric. intros a b Hab Hba.
  inversion Hab.
    - (* le_n *) reflexivity.
    - (* le_S *) inversion Hba.
      + (* le_n *) rewrite <- H1. symmetry. apply H0.
      + (* le_S *)
        rewrite <- H2 in H.
        rewrite <- H0 in H1.
        assert (S m0 <= m0) as bad.
        { (* Proof of assertion *)
          apply le_trans with (b:=m).
          - (* S m0 <= m *) apply H.
          - (* m <= m0 *)
            apply le_trans with (b:=S m).
            + (* m <= S m *) apply le_S. apply le_n.
            + (* S m <= m0 *) apply H1. }
        assert (~ (S m0 <= m0)) as L.
        { (* Proof of assertion *) apply le_Sn_n. }
        unfold not in L.
        apply L in bad. destruct bad.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX2? (le_step) *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  (* ADMITTED *)
  intros.
  unfold lt in H.
  assert (S n <= S p).
    apply le_trans with m. apply  H. apply H0.
  apply le_S_n. assumption.  Qed.
  (* LATER: simpler proof:
     unfold lt. intros.
     apply le_S_n. apply le_trans with m.
       assumption. assumption. Qed. *)
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** *** Equivalence Relations *)

(** A relation is an _equivalence_ if it's reflexive, symmetric, and
    transitive.  *)

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).
(* LATER: Note that the standard library does it like this:
    Record equivalence : Prop :=
      { equiv_refl : reflexive;
        equiv_trans : transitive;
        equiv_sym : symmetric}.
   (in the presence of a parameter for the relation).
*)

(** *** Partial Orders and Preorders *)

(** A relation is a _partial order_ when it's reflexive,
    _anti_-symmetric, and transitive.  In the Rocq standard library
    it's called just "order" for short. *)

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(** A preorder is almost like a partial order, but doesn't have to be
    antisymmetric. *)

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

(* FULL *)
Theorem le_order :
  order le.
(* FOLD *)
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans.  Qed.
(* /FOLD *)
(* /FULL *)

(* ########################################################### *)
(** * Reflexive, Transitive Closure *)

(** The _reflexive, transitive closure_ of a relation [R] is the
    smallest relation that contains [R] and that is both reflexive and
    transitive.  Formally, it is defined like this in the Relations
    module of the Rocq standard library: *)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
  | rt_step x y (H : R x y) : clos_refl_trans R x y
  | rt_refl x : clos_refl_trans R x x
  | rt_trans x y z
        (Hxy : clos_refl_trans R x y)
        (Hyz : clos_refl_trans R y z) :
        clos_refl_trans R x z.

(** For example, the reflexive and transitive closure of the
    [next_nat] relation coincides with the [le] relation. *)

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
(* FOLD *)
Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.
(* /FOLD *)

(** The above definition of reflexive, transitive closure is natural:
    it says, explicitly, that the reflexive and transitive closure of
    [R] is the least relation that includes [R] and that is closed
    under rules of reflexivity and transitivity.  But it turns out
    that this definition is not very convenient for doing proofs,
    since the "nondeterminism" of the [rt_trans] rule can sometimes
    lead to tricky inductions.  Here is a more useful definition: *)

Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

(** Our new definition of reflexive, transitive closure "bundles"
    the [rt_step] and [rt_trans] rules into the single rule step.
    The left-hand premise of this step is a single use of [R],
    leading to a much simpler induction principle.

    Before we go on, we should check that the two definitions do
    indeed define the same relation...

    First, we prove two lemmas showing that [clos_refl_trans_1n] mimics
    the behavior of the two "missing" [clos_refl_trans]
    constructors.  *)

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
  R x y -> clos_refl_trans_1n R x y.
(* FOLD *)
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl.   Qed.
(* /FOLD *)

(* EX2? (rsc_trans) *)
Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  (* ADMITTED *)
  intros X R x y z G H.
  induction G.
    - (* rt1n_refl *) assumption.
    - (* rt1n_trans *)
      apply rt1n_trans with y. assumption.
      apply IHG. assumption.  Qed.
(* /ADMITTED *)
(** [] *)

(** Then we use these facts to prove that the two definitions of
    reflexive, transitive closure do indeed define the same
    relation. *)

(* EX3? (rtc_rsc_coincide) *)
Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  (* ADMITTED *)
  intros X R x y.
  unfold iff. split.
    - (* -> *)
      intros H. induction H.
        + (* rt_step *)
          apply rsc_R.  assumption.
        + (* rt_refl *)
          apply rt1n_refl.
        + (* rt_trans *)
          apply rsc_trans with y. assumption. assumption.
    - (* <- *)
      intros H. induction H.
        + (* rt1n_refl *) apply rt_refl.
        + (* rt1n_trans *) apply rt_trans with y. apply rt_step.
          assumption. apply IHclos_refl_trans_1n.  Qed.
(* /ADMITTED *)
(** [] *)

(* LATER *)
(* ########################################################### *)
(* SOME MORE OPTIONAL EXERCISES AND SOLUTIONS, TO BE FLESHED OUT LATER *)

(* EX3? (rt_idempotent) *)
Theorem rt_idempotent : forall (X:Type) (R: relation X) (x y: X),
  clos_refl_trans (clos_refl_trans R) x y <-> clos_refl_trans R x y.
Proof.
  (* ADMITTED *)
  intros X R x y.
  split.
  { intro P. induction P.
    - (* rt_step *)
       apply H.
    - (* rt_refl *)
       apply rt_refl.
    - (* rt_trans *)
       apply rt_trans with y. apply IHP1. apply IHP2. }
  { intro P. induction P.
    - (* rt_step *)
       apply rt_step. apply rt_step. apply H.
    - (* rt_refl *)
       apply rt_refl.
    - (* rt_trans *)
       apply rt_trans with y. apply IHP1. apply IHP2. } Qed.
(* /ADMITTED *)
(** [] *)

(** Define what it means for a relation to preserve a property *)

Definition preserves {X: Type} (R: relation X) (P: X -> Prop) :=
  forall (x y : X), P x -> R x y -> P y.

(* EX3? (rt_preserves) *)
Theorem rt_preserves : forall (X: Type) (R: relation X) (P: X -> Prop),
  preserves R P -> preserves (clos_refl_trans R) P.
Proof.
  (* ADMITTED *)
  intros X R P HR. unfold preserves. intros x y HPx Htc.
  induction Htc.
    - (* rt_step *) unfold preserves in HR. apply HR with (x:=x)(y:=y).
      apply HPx. apply H.
    - (* rt_refl *) apply HPx.
    - (* rt_trans *) apply IHHtc2. apply IHHtc1. apply HPx.  Qed.
(* /ADMITTED *)
(** [] *)

(* LATER: It might be interesting to go on a bit with relational
   algebra, at least in exercises.  E.g., describe composition in
   words, ask them to define it formally, and get them to prove that
   the composition of a transitive relation with itself is itself. *)
Inductive composition (X: Type) (Q R: relation X) : X -> X -> Prop :=
  comp x z
        (H : exists y, Q x y /\ R y z) :
        composition X Q R x z.
(* /LATER *)
