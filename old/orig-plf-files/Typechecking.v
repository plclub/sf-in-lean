(** * Typechecking: A Typechecker for STLC *)

(* NOTATION: SOONER: Make sure that notations are used consistently.  *)

(** The [has_type] relation of the STLC defines what it means for a
    term to belong to a type (in some context).  But it doesn't, by
    itself, give us an algorithm for _checking_ whether or not a term
    is well typed.

    Fortunately, the rules defining [has_type] are _syntax directed_
    -- that is, for every syntactic form of the language, there is
    just one rule that can be used to give a type to terms of that
    form.  This makes it straightforward to translate the typing rules
    into clauses of a typechecking _function_ that takes a term and a
    context and either returns the term's type or else signals that
    the term is not typable.  *)
(* LATER: This is a little unsatisfying -- we're building a function
   for typechecking terms, but not for evaluating them.  Perhaps this
   would be a good place to show them program extraction -- i.e.,
   build an implementation of [step] too, and then extract both and
   combine them with an OCaml parser and execute some examples...  Or
   maybe this could be left as an exercise? :-) *)

(** FULL: This short chapter constructs such a function and proves it
    correct. *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-non-recursive".
From Stdlib Require Import Bool.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From PLF Require MoreStlc.

Module STLCTypes.
Export STLC.
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** * Comparing Types *)

(** First, we need a function to compare two types for equality... *)

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | <{{ Bool }}> , <{{ Bool }}> =>
      true
  | <{{ T11->T12 }}>, <{{ T21->T22 }}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.

(** ... and we need to establish the usual two-way connection between
    the boolean result returned by [eqb_ty] and the logical
    proposition that its inputs are equal. *)

Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
(* FOLD *)
Proof.
  intros T. induction T; simpl.
    reflexivity.
    rewrite IHT1. rewrite IHT2. reflexivity.  Qed.
(* /FOLD *)

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
(* FOLD *)
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  - (* T1=Bool *)
    reflexivity.
  - (* T1 = T1_1->T1_2 *)
    rewrite andb_true_iff in H0. inversion H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst...  Qed.
(* /FOLD *)
(* TERSE: HIDEFROMHTML *)
End STLCTypes.
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** * The Typechecker *)

(** The typechecker works by walking over the structure of the given
    term, returning either [Some T] or [None].  Each time we make a
    recursive call to find out the types of the subterms, we need to
    pattern-match on the results to make sure that they are not
    [None].  Also, in the [app] case, we use pattern matching to
    extract the left- and right-hand sides of the function's arrow
    type (and fail if the type of the function is not [T11->T12]
    for some [T11] and [T12]). *)

(* TERSE: HIDEFROMHTML *)
Module FirstTry.
Import STLCTypes.
(* TERSE: /HIDEFROMHTML *)

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      Gamma x
  | <{\x:T2, t1}> =>
      match type_check (x |-> T2 ; Gamma) t1 with
      | Some T1 => Some <{{ T2->T1 }}>
      | _ => None
      end
  | <{t1 t2}> =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some <{{ T11->T12 }}>, Some T2 =>
          if eqb_ty T11 T2 then Some T12 else None
      | _,_ => None
      end
  | <{true}> =>
      Some <{{ Bool }}>
  | <{false}> =>
      Some <{{ Bool }}>
  | <{if guard then t else f}> =>
      match type_check Gamma guard with
      | Some <{{ Bool }}> =>
          match type_check Gamma t, type_check Gamma f with
          | Some T1, Some T2 =>
              if eqb_ty T1 T2 then Some T1 else None
          | _,_ => None
          end
      | _ => None
      end
  end.

(* TERSE: HIDEFROMHTML *)
End FirstTry.
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** * Digression: Improving the Notation *)

(** Before we consider the properties of this algorithm, let's write
    it out again in a cleaner way, using "monadic" notations in the
    style of Haskell to streamline the plumbing of options.  First, we
    define a notation for composing two potentially failing (i.e.,
    option-returning) computations: *)

Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

(** TERSE: *** *)
(** Second, we define [return] and [fail] as synonyms for [Some] and
    [None]: *)

Notation " 'return' e "
  := (Some e) (at level 60).

Notation " 'fail' "
  := None.

(* TERSE: HIDEFROMHTML *)
Module STLCChecker.
Import STLCTypes.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** Now we can write the same type-checking function in a more
    imperative-looking style using these notations. *)

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{\x:T2, t1}> =>
      T1 <- type_check (x |-> T2 ; Gamma) t1 ;;
      return <{{ T2->T1 }}>
  | <{t1 t2}> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{{ T11->T12 }}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | <{ true }> =>
      return <{{ Bool }}>
  | <{ false }> =>
      return <{{ Bool }}>
  | <{ if guard then t1 else t2 }> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | <{{ Bool }}> =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

(* ###################################################################### *)
(** * Properties *)

(** To verify that the typechecking algorithm is correct, we show that
    it is _sound_ and _complete_ for the original [has_type]
    relation -- that is, [type_check] and [has_type] define the same
    partial function. *)

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
(* FOLD *)
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    remember (type_check Gamma t1) as TO1.
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct T1 as [|T11 T12]; try solve_by_invert;
    remember (type_check Gamma t2) as TO2;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T11 T2) eqn: Heqb.
    apply eqb_ty__eq in Heqb.
    inversion H0; subst...
    inversion H0.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve_by_invert.
    inversion H0; subst...
  - (* tru *) eauto.
  - (* fls *) eauto.
  - (* test *)
    remember (type_check Gamma t1) as TOc.
    remember (type_check Gamma t2) as TO1.
    remember (type_check Gamma t3) as TO2.
    destruct TOc as [Tc|]; try solve_by_invert.
    destruct Tc; try solve_by_invert;
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T1 T2) eqn:Heqb;
    try solve_by_invert.
    apply eqb_ty__eq in Heqb.
    inversion H0. subst. subst...
Qed.
(* /FOLD *)

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
(* FOLD *)
Proof with auto.
  intros Gamma t T Hty.
  induction Hty; simpl.
  - (* T_Var *) destruct (Gamma _) eqn:H0; assumption.
  - (* T_Abs *) rewrite IHHty...
  - (* T_App *)
    rewrite IHHty1. rewrite IHHty2.
    rewrite (eqb_ty_refl T2)...
  - (* T_True *) eauto.
  - (* T_False *) eauto.
  - (* T_If *) rewrite IHHty1. rewrite IHHty2.
    rewrite IHHty3. rewrite (eqb_ty_refl T1)...
Qed.
(* /FOLD *)

(* TERSE: HIDEFROMHTML *)
End STLCChecker.

(* FULL *)
(* ###################################################################### *)
(** * Exercises *)

(** In this exercise we'll extend the typechecker to deal with the
    extended features discussed in chapter \CHAP{MoreStlc}.  Your job
    is to fill in the omitted cases in the following. *)

Module TypecheckerExtensions.
Import MoreStlc.
Import STLCExtended.
(* SOONER: What are all the double brackets about?  Can they be
   deleted?  If not, explain. *)

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | <{{Nat}}>, <{{Nat}}> =>
      true
  | <{{Unit}}>, <{{Unit}}> =>
      true
  | <{{T11 -> T12}}>, <{{T21 -> T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 * T12}}>, <{{T21 * T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 + T12}}>, <{{T21 + T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{List T11}}>, <{{List T21}}> =>
      eqb_ty T11 T21
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
  intros T.
  induction T; simpl; auto;
    rewrite IHT1; rewrite IHT2; reflexivity.  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1.
  induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
    try reflexivity;
    try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
         apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
    try (apply IHT1 in Hbeq; subst; auto).
 Qed.

(* EX4M (type_check_defn) *)
Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{ \ x1 : T1, t2 }> =>
      T2 <- type_check (x1 |-> T1 ; Gamma) t2 ;;
      return <{{T1 -> T2}}>
  | <{ t1 t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{{T11 -> T12}}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tm_const _ =>
      return <{{Nat}}>
  | <{ succ t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ pred t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ t1 * t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | <{{Nat}}>, <{{Nat}}> => return <{{Nat}}>
      | _,_        => fail
      end
  | <{ if0 guard then t else f }> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | <{{Nat}}> => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* Complete the following cases. *)
  (* SOONER: Did we intentionally give them more things to handle than
     in MoreStlc? *)

  (* sums *)
  (* SOLUTION *)
  | <{ inl T2 t1 }> =>
      T1 <- type_check Gamma t1 ;;
      return <{{T1 + T2}}>
  | <{ inr T1 t2 }> =>
      T2 <- type_check Gamma t2 ;;
      return <{{T1 + T2}}>
  | <{ case t0 of | inl x1 => t1 | inr x2 => t2 }> =>
      T0 <- type_check Gamma t0 ;;
      match T0 with
      | <{{T1 + T2}}> =>
          T1' <- type_check (x1 |-> T1 ; Gamma) t1 ;;
          T2' <- type_check (x2 |-> T2 ; Gamma) t2 ;;
          if eqb_ty T1' T2' then return T1' else fail
      | _ => fail
      end
  (* /SOLUTION *)
  (* lists (the [tm_lcase] is given for free) *)
  (* SOLUTION *)
  | <{ nil T1 }> =>
      Some <{{List T1}}>
  | <{ t1 :: t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T2 with
      | <{{List T2'}}> =>
          if eqb_ty T1 T2' then return T2 else fail
      | _ => fail
      end
  (* /SOLUTION *)
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
      T0 <- type_check Gamma t0 ;;
      match T0 with
      | <{{List T}}> =>
          T1 <- type_check Gamma t1 ;;
          T2 <- type_check (x21 |-> T ; x22 |-> <{{List T}}> ; Gamma) t2 ;;
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  (* unit *)
  (* SOLUTION *)
  | <{ unit }> =>
      return <{{Unit}}>
  (* /SOLUTION *)
  (* pairs *)
  (* SOLUTION *)
  | <{ (t1, t2) }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      return <{{T1 * T2}}>
  | <{ t1.fst }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{T11 * T12}}> => return T11
      | _ => fail
      end
  | <{ t1.snd }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{T11 * T12 }}> => return T12
      | _ => fail
      end
  (* /SOLUTION *)
  (* let *)
  (* SOLUTION *)
  | <{ let x = t1 in t2 }> =>
      T1 <- type_check Gamma t1 ;;
      type_check (x |-> T1 ; Gamma) t2
  (* /SOLUTION *)
  (* fix *)
  (* SOLUTION *)
  | <{ fix t1 }> =>
      TT <- type_check Gamma t1 ;;
      match TT with
      | <{{T1 -> T1'}}> =>
          if eqb_ty T1 T1' then return T1' else fail
      | _ => fail
      end
  (* /SOLUTION *)
(* UNCOMMENT WHEN HIDING SOLUTIONS
  | _ => None  (* ... and delete this line when you complete the exercise. *)
/UNCOMMENT *)
  end.
(* GRADE_MANUAL 6: type_check_defn *)
(** [] *)

(** Just for fun, we'll do the soundness proof with just a bit more
    automation than above, using these "mega-tactics": *)
(* SOONER: These all need some much better explanation!! *)

Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

(* NOWISH: explain role of arguments! *)
Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try solve_by_invert.

(* NOWISH: Difference?  and how does it work?  is it the same as
   [analyze; invert_typecheck]?  And: Can we have a better name??? *)
Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

(* NOWISH: Explain *)
Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.
(* NOWISH: Why two substs? *)

(* SOONER: NOWISH: Helping students with this proof is a pretty
   challenging experience... *)
(* EX2 (ext_type_checking_sound) *)
Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T ->
  has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - (* const *) eauto.
  - (* scc *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* prd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* mlt *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  (* Complete the following cases. *)
  (* sums *)
  (* SOLUTION *)
  - (* tinl *)
    rename t into T2, t0 into t1.
    invert_typecheck Gamma t1 T1.
  - (* tinr *)
    rename t into T1, t0 into t2.
    invert_typecheck Gamma t2 T2.
  - (* tcase *)
    rename s into x2, s0 into x3.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    remember (x2 |-> T11 ; Gamma) as Gamma'1.
    invert_typecheck Gamma'1 t2 T2.
    remember (x3 |-> T12 ; Gamma) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  (* /SOLUTION *)
  (* lists (the [tm_lcase] is given for free) *)
  (* SOLUTION *)
  - (* tnil *)
    eauto.
  - (* tcons *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    destruct T2; inversion H0...
    case_equality T1 T2.
  (* /SOLUTION *)
  - (* tlcase *)
    rename s into x31, s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (x31 |-> T11 ; x32 |-> <{{List T11}}> ; Gamma) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  (* unit *)
  (* SOLUTION *)
  - (* unit *) eauto.
  (* /SOLUTION *)
  (* pairs *)
  (* SOLUTION *)
  - (* pair *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
  - (* fst *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* snd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  (* /SOLUTION *)
  (* let *)
  (* SOLUTION *)
  - (* tlet *)
    rename s into x.
    invert_typecheck Gamma t1 T1.
  (* /SOLUTION *)
  (* fix *)
  (* SOLUTION *)
  - (* fix *)
    fully_invert_typecheck Gamma t T T1 T2.
    case_equality T1 T2.
  (* /SOLUTION *)
  (* ADMITTED *)
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: TypecheckerExtensions.type_checking_sound *)
(** [] *)

(* EX2 (ext_type_checking_complete) *)
Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T ->
  type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T0));
    try (rewrite (eqb_ty_refl T1));
    try (rewrite (eqb_ty_refl T2));
    try (rewrite (eqb_ty_refl T3));
    eauto.
    - destruct (Gamma _); [assumption| solve_by_invert].
  (* The above proof script suffices for the reference solution. *)
  (* ADMITTED *)
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: TypecheckerExtensions.type_checking_complete *)
(** [] *)

End TypecheckerExtensions.

(** Above, we showed how to write a typechecking function and prove it
    sound and complete for the typing relation.  Do the same for the
    operational semantics -- i.e., write a _function_ [stepf] of type
    [tm -> option tm] and prove that it is sound and complete with
    respect to [step] from chapter \CHAP{MoreStlc}. *)

Module StepFunction.
Import MoreStlc.
Import STLCExtended.

(* EX2M? (valuef_defn) *)
(* We must first also redefine [value] as a function. *)
Fixpoint valuef (t : tm) : bool :=
  match t with
  | tm_var _ => false
  | <{ \ x : T, _ }> => true
  | <{ _ _ }> => false
  | tm_const _ => true
  | <{ succ _ }> | <{ pred _ }> | <{ _ * _ }> | <{ if0 _ then _ else _ }> => false
  (* Complete the following cases *)
  (* sums *)
  (* SOLUTION *)
  | <{ inl T t1 }> => valuef t1
  | <{ inr T t2 }> => valuef t2
  | <{ case _ of | inl x => _ | inr y => _ }> => false
  (* /SOLUTION*)
  (* lists (the [tm_lcase] is given for free) *)
  (* SOLUTION *)
  | <{ nil T }> => true
  | <{ t1 :: t2 }> => valuef t1 && valuef t2
  (* /SOLUTION*)
  | <{ case _ of | nil => _ | x :: xs => _ }> => false
  (* unit *)
  (* SOLUTION *)
  | <{ unit }> => true
  (* /SOLUTION*)
  (* pairs *)
  (* SOLUTION *)
  | <{ (t1, t2) }> => valuef t1 && valuef t2
  | <{ _.fst }> | <{ _.snd }> => false
  (* /SOLUTION*)
  (* let *)
  (* SOLUTION *)
  | <{ let _ = _ in _ }>
  (* /SOLUTION*)
  (* fix *)
  (* SOLUTION *)
  | <{ fix _ }> => false
  (* /SOLUTION *)
(* UNCOMMENT WHEN HIDING SOLUTIONS
  | _ => false  (* ... and delete this line when you complete the exercise. *)
/UNCOMMENT *)
  end.
(* GRADE_MANUAL 2: valuef_defn *)
(** [] *)

(* A little helper to concisely check some boolean properties
   (in this case, that some term is a value, with [valuef]). *)
Definition assert (b : bool) (a : option tm) : option tm :=
  if b then a else None.

(* EX3M? (stepf_defn) *)
(* Operational semantics as a Rocq function. *)
Fixpoint stepf (t : tm) : option tm :=
  match t with
  (* pure STLC *)
  | tm_var x => None (* We only define step for closed terms *)
  | <{ \x1:T1, t2 }> => None (* Abstraction is a value *)
  | <{ t1 t2 }> =>
    match stepf t1, stepf t2, t1 with
    | Some t1', _, _ => Some <{ t1' t2 }>
    (* otherwise [t1] is a normal form *)
    | None, Some t2', _ => assert (valuef t1) (Some <{ t1 t2' }>)
    (* otherwise [t1], [t2] are normal forms *)
    | None, None, <{ \x:T, t11 }> =>
      assert (valuef t2) (Some <{ [x:=t2]t11 }>)
    | _, _, _ => None
    end
  (* numbers *)
  | tm_const _ => None (* number value *)
  | <{ succ t1 }> =>
    match stepf t1, t1 with
    | Some t1', _ => Some <{ succ t1' }>
    (* otherwise [t1] is a normal form *)
    | None, tm_const n => Some (tm_const (S n))
    | None, _ => None
    end
  | <{ pred t1 }> =>
    match stepf t1, t1 with
    | Some t1', _ => Some <{ pred t1' }>
    (* otherwise [t1] is a normal form *)
    | None, tm_const n => Some (tm_const (n - 1))
    | _, _ => None
    end
  | <{ t1 * t2 }>  =>
    match stepf t1, stepf t2, t1, t2 with
    | Some t1', _, _, _ => Some <{ t1' * t2 }>
    (* otherwise [t1] is a normal form *)
    | None, Some t2', _, _ =>
      assert (valuef t1) (Some <{ t1 * t2' }>)
    | None, None, tm_const n1, tm_const n2 => Some (tm_const (mult n1 n2))
    | _, _, _, _ => None
    end
  | <{ if0 guard then t else f }> =>
    match stepf guard, guard with
    | Some guard', _ => Some <{ if0 guard' then t else f }>
    (* otherwise [guard] is a normal form *)
    | None, tm_const 0 => Some t
    | None, tm_const (S _) => Some f
    | _, _ => None
    end
  (* Complete the following cases. *)
  (* sums *)
  (* SOLUTION *)
  | <{ inl T2 t1 }> =>
    t1' <- stepf t1;;
    Some <{ inl T2 t1' }>
  | <{ inr T1 t2 }> =>
    t2' <- stepf t2;;
    Some <{ inr T1 t2' }>
  | <{ case t0 of | inl x1 => t1 | inr x2 => t2 }> =>
    match stepf t0, t0 with
    | Some t0', _ => Some <{ case t0' of | inl x1 => t1 | inr x2 => t2 }>
    (* otherwise [t0] is a normal form *)
    | None, <{ inl T v1 }> => assert (valuef v1) (Some <{ [x1:=v1] t1 }> )
    | None, <{ inr T v2 }> => assert (valuef v2) (Some <{ [x2:=v2] t2 }> )
    | _, _ => None
    end
  (* /SOLUTION *)
  (* lists (the [tm_lcase] is given for free) *)
  (* SOLUTION *)
  | <{ nil T }> => None (* [tnil] is a value *)
  | <{ t1 :: t2 }> =>
    match stepf t1, stepf t2 with
    | Some t1', _ => Some <{ t1' :: t2 }>
    (* otherwise [t1] is a normal form *)
    | None, Some t2' => assert (valuef t1) (Some <{ t1 :: t2' }>)
    | None, None => None
    end
  (* /SOLUTION *)
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
    match stepf t0, t0 with
    | Some t0', _ => Some <{ case t0' of | nil => t1 | x21 :: x22 => t2 }>
    (* otherwise [t0] is a normal form *)
    | None, <{ nil T }> => Some t1
    | None, <{ vh :: vt }> =>
      assert (valuef vh) (assert (valuef vt)
        (Some <{ [x22:=vt]([x21:=vh]t2) }> ))
    | None, _ => None
    end
  (* unit *)
  (* SOLUTION *)
  | <{ unit }> => None
  (* /SOLUTION *)
  (* pairs *)
  (* SOLUTION *)
  | <{ (t1, t2) }> =>
    match stepf t1, stepf t2 with
    | Some t1', _ => Some <{ (t1', t2) }>
    (* otherwise [t1] is a normal form *)
    | None, Some t2' => assert (valuef t1) (Some <{ (t1, t2') }>)
    | None, None => None
    end
  | <{ t1.fst }> =>
    match stepf t1, t1 with
    | Some t1', _ => Some <{ t1'.fst }>
    (* otherwise [t1] is a normal form *)
    | None, <{ (v11, v12) }> =>
      assert (valuef v11) (assert (valuef v12) (Some v11))
    | None, _ => None
    end
  | <{ t1.snd }> =>
    match stepf t1, t1 with
    | Some t1', _ => Some <{ t1'.snd }>
    (* otherwise [t1] is a normal form *)
    | None, <{ (v11, v12) }> =>
      assert (valuef v11) (assert (valuef v12) (Some v12))
    | None, _ => None
    end
  (* /SOLUTION *)
  (* let *)
  (* SOLUTION *)
  | <{ let x = t1 in t2 }> =>
    match stepf t1 with
    | Some t1' => Some <{ let x = t1' in t2 }>
    (* otherwise [t1] is a normal form *)
    | None => assert (valuef t1) (Some <{ [x:=t1] t2 }> )
    end
  (* /SOLUTION *)
  (* fix *)
  (* SOLUTION *)
  | <{ fix t1 }> =>
    match stepf t1, t1 with
    | Some t1', _ => Some <{ fix t1' }>
    (* otherwise [t1] is a normal form *)
    | None, <{ \x:T1, t2 }> => Some <{ [x:=$(tm_fix t1)] t2 }>
    | None, _ => None
    end
  (* /SOLUTION *)
 (* UNCOMMENT WHEN HIDING SOLUTIONS
  | _ => None  (* ... and delete this line when you complete the exercise. *)
/UNCOMMENT *)
  end.
(* GRADE_MANUAL 3: stepf_defn *)
(** [] *)

(* To prove that [stepf] is equivalent to [step], we start with
   a couple of intermediate lemmas. *)

(* We show that [valuef] is sound and complete with respect to [value]. *)

(* EX2? (sound_valuef) *)
(* [valuef] is sound with respect to [value] *)
Lemma sound_valuef : forall t,
    valuef t = true -> value t.
Proof.
  (* ADMITTED *)
  intros t H.
  induction t;
    (* For some subgoals, the equation [H] reduces to the
       contradictory [true = false]. *)
    try discriminate;
    (* Most other cases are straightforward applications of [simpl],
       [apply] and [constructor] (the constructors of [value] were
       added as hints for [auto] just after we defined it). *)
    auto.
  (* The two remaining cases are those where [t] is a value with two
     subterms [t1] and [t2] ([tcons t1 t2] and [pair t1 t2]):
     [H] simplifies to [true = valuef t1 && valuef t2], from which we
     can deduce [valuef t1 = true /\ valuef t2 = true], and then we
     finish using the induction hypothesis. *)
  - apply andb_true_iff in H;
    (* We destruct the conjunction we just obtained. *)
    destruct H;
    auto.
  - (* Same steps here. *) apply andb_true_iff in H; destruct H; auto.
  (* We could also avoid repeating those three tactics by chaining
     them with the rest just above. We leave it like this to
     make the proof easier to follow. *)
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2? (complete_valuef) *)
(* [valuef] is complete with respect to [value].
   This proof by induction is quite easily done by simplification. *)
Lemma complete_valuef : forall t,
    value t -> valuef t = true.
Proof.
  (* ADMITTED *)
  intros t H.
  induction H; auto; apply andb_true_iff; auto.
Qed.
(* /ADMITTED *)
(** [] *)

(* Soundness of [stepf]:

   Theorem sound_stepf : forall t t',
       stepf t = Some t'  ->  t --> t'.

   By induction on [t]. We automate the handling of each case with
   the following tactic [auto_stepf]. *)

Tactic Notation "auto_stepf" ident(H) :=
  (* Step 1: In every case, the left hand side of the hypothesis
     [H : stepf t = Some t'] simplifies to some combination of
     [match u with ... end], [assert u (...)] (for some [u]).
     The tactic [auto_stepf] then destructs [u] as required.
     We repeat this step as long as it is possible. *)
  repeat
    match type of H with
    | (match ?u with _ => _ end = _) =>
      let e := fresh "e" in
      destruct u eqn:e
    | (assert ?u _ = _) =>
      (* In this case, [u] is always of the form [valuef t0]
         for some term [t0]. If [valuef t0 = true], we immediately
         deduce [value t0] via [sound_valuef]. If [valuef t0 = false],
         then that equation simplifies to [None = Some t'], which is
         contradictory and can be eliminated with [discriminate]. *)
      let e := fresh "e" in
      destruct u eqn:e;
      simpl in H; (* [assert true (...)] must be simplified
                     explicitly. *)
      [apply sound_valuef in e | discriminate]
    end;
  (* Step 2: We are now left with either [H : None = Some t'] or
     [Some (...) = Some t'], and the rest of the proof is a
     straightforward combination of the induction hypotheses. *)
  (discriminate + (inversion H; subst; auto)).

(* EX2? (sound_stepf) *)
(* Soundness of [stepf]. *)
Theorem sound_stepf : forall t t',
    stepf t = Some t'  ->  t --> t'.
Proof.
  intros t.
  induction t; simpl; intros t' H;
    auto_stepf H.
 (* The above proof script suffices for the reference solution. *)
 (* ADMITTED *)
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2? (value_stepf_nf) *)
(* Now for completeness, another lemma will be useful:
   every value is a normal form for [stepf]. *)
Lemma value_stepf_nf : forall t,
    value t -> stepf t = None.
Proof.
  (* ADMITTED *)
  intros t H.
  induction H; simpl; try reflexivity;
    try (rewrite IHvalue; reflexivity);
    try (rewrite IHvalue1, IHvalue2; reflexivity).
 (* ADMITTED *)
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2? (complete_stepf) *)
(* Completeness of [stepf]. *)
Theorem complete_stepf : forall t t',
    t --> t'  ->  stepf t = Some t'.
Proof.
  (* ADMITTED *)
  intros t t' H.
  (* By induction on the derivation of [t --> t'].
     As in the proof of soundness, [stepf t] simplifies to a
     combination of [match] and [assert]; our assumptions actually
     tell us which way [match] and [assert] go. *)
  induction H; simpl;
    try rewrite IHstep;
    try rewrite IHstep1;
    try rewrite IHstep2;
    repeat rewrite value_stepf_nf by assumption;
    repeat rewrite complete_valuef by assumption;
    reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)

End StepFunction.

(* EX5? (stlc_impl) *)
(** Using the Imp parser described in the \CHAPV1{ImpParser} chapter
    of _Logical Foundations_ as a guide, build a parser for extended
    STLC programs.  Combine it with the typechecking and stepping
    functions from the above exercises to yield a complete typechecker
    and interpreter for this language. *)

Module StlcImpl.
Import StepFunction.

(* SOLUTION *)
(** (No solution provided.  If you write one, please let us know!) *)
(* /SOLUTION *)
End StlcImpl.
(** [] *)
(* /FULL *)

(* TERSE: /HIDEFROMHTML *)
