(** * Types: Type Systems *)

(* INSTRUCTORS: This chapter is short, but chewy.  Although all the
   individual pieces are reasonably simple and familiar, but there are
   quite a few of them and the way they fit together is a bit
   intricate, especially coming on top of the Smallstep material,
   which many students also find a bit challenging.

   Spending an entire 80-minute class on this chapter feels about
   right.  Going through the proofs of progress and preservation very
   carefully, at the board, was critical.  Doing the quizzes together
   is good -- a few more quizzes would be better.

   For this lecture, I (BCP) find it useful to make a physical 1-page
   "cheat sheet" for students, containing:
     - syntax of terms
     - definition of values
     - canonical forms lemmas
     - definitions of typing and step relations

   This makes it more fun to put proofs on the board because the class
   can help.

*)
(* SOONER: Beginning at the Types chapter, the text gets a bit
   sparse! *)
(* SOONER: The quizzes we have are pretty good, but the ones at the
   end of the chapter are too hard to jump straight into -- we need
   something in the middle.  (BCP 11/18: Actually, the ones at the end
   of the chapter are OK, but it's disappointing that no property
   breaks!)

*)
(* LATER: For consistency with the STLC definitions in future
   chapters, it would be better and simpler to represent numbers by a
   simple nat, rather than as strings of [succ] applied to [0] (which
   also introduces subtleties that are really not the main point
   here).  But the present formulation is not a big problem either. *)
(* LATER: Harper's lecture from the milner symposium would make a
   good support for this lecture *)
(* LATER: There are a bunch of slides from earlier offerings of
   CIS500 that might be wonderful additions to the TERSE notes.
      https://www.seas.upenn.edu/~cis500/cis500-f06/lectures/1002.pdf
      https://www.seas.upenn.edu/~cis500/cis500-f06/lectures/1004.pdf
*)
(* LATER: There are some notational choices that need to be made
   consistently throughout the rest of the notes: naming of inference
   rules, naming of constructors, naming of syntactic categories,
   ... *)
(* HIDE: Maybe we overdid it with [...] and [eauto]: some of the later
   files are a bit slow to compile!  It should be dialed back a
   little... *)

(** FULL: Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of the simplest
    imaginable language, to introduce the basic ideas of types and
    typing rules and the fundamental theorems about type systems:
    _type preservation_ and _progress_. In chapter \CHAP{Stlc} we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Rocq!). *)
(** TERSE: New topic: _type systems_

      - This chapter: a toy type system for a toy language
           - typing relation
           - _progress_ and _preservation_ theorems

      - Next chapter: _simply typed lambda-calculus_
*)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Arith.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".

(* INSTRUCTORS: APT: best place I could find for these without
   requiring new Auto.  (BCP 11/18: Why can't we put it with the
   definition of multi?) *)
Hint Constructors multi : core.
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** * Typed Arithmetic Expressions *)

(** FULL: To motivate the discussion of type systems, let's begin as
    usual with a tiny toy language.  We want it to have the potential
    for programs to go wrong because of runtime type errors, so we
    need something a tiny bit more complex than the language of
    constants and addition that we used in chapter \CHAP{Smallstep}: a
    single kind of data (e.g., numbers) is too simple, but just two
    kinds (numbers and booleans) gives us enough material to tell an
    interesting story.

    The language definition is completely routine. *)

(** TERSE:
      - A simple toy language where expressions may fail with dynamic
        type errors
           - numbers (and arithmetic)
           - booleans (and conditionals)
      - Unlike Imp, we use a single syntactic category for both
        booleans and numbers
      - This means we can write _stuck_ terms like [5 + true] and [if
        42 then 0 else 1].
*)

(* ###################################################################### *)
(** ** Syntax *)

(** Here is the syntax, informally:
[[
    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
]]
*)
(* TERSE: HIDEFROMHTML *)
(** And here it is formally: *)
Module TM.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'"  := true (at level 1): tm_scope.
Notation "'true'" := (tru) (in custom tm at level 0): tm_scope.
Notation "'false'"  := false (at level 1): tm_scope.
Notation "'false'" := (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := e (e custom tm at level 99): tm_scope.
Notation "( x )" := x (in custom tm, x at level 99): tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := (zro) (in custom tm at level 0): tm_scope.
Notation "'0'"  := 0 (at level 1): tm_scope.
Notation "'succ' x" := (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := (prd x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := (ite c t e)
                 (in custom tm at level 90, c custom tm at level 80,
                  t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** _Values_ are [true], [false], and numeric values... *)
Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.

Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.

Definition value (t : tm) := bvalue t \/ nvalue t.

(* HIDE: CH: This definition of numeric values that insists on well-typing seems
   overly complicated to me. This idea is later dropped in MoreStlc both for
   numbers and also for lists, and some careful students do seem to notice the
   change and wonder about it. *)

(* TERSE: HIDEFROMHTML *)
Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** ** Operational Semantics *)

(** FULL: Here is the single-step relation, first informally... *)
(**
[[[
                   -------------------------------                   (ST_IfTrue)
                   if true then t1 else t2 --> t1

                   -------------------------------                  (ST_IfFalse)
                   if false then t1 else t2 --> t2

                               t1 --> t1'
            ------------------------------------------------             (ST_If)
            if t1 then t2 else t3 --> if t1' then t2 else t3

                             t1 --> t1'
                         --------------------                          (ST_Succ)
                         succ t1 --> succ t1'

                           ------------                               (ST_Pred0)
                           pred 0 --> 0

                         numeric value v
                        -------------------                        (ST_PredSucc)
                        pred (succ v) --> v

                              t1 --> t1'
                         --------------------                          (ST_Pred)
                         pred t1 --> pred t1'

                          -----------------                         (ST_IsZero0)
                          iszero 0 --> true

                         numeric value v
                      -------------------------                  (ST_IsZeroSucc)
                      iszero (succ v) --> false

                            t1 --> t1'
                       ------------------------                      (ST_IsZero)
                       iszero t1 --> iszero t1'
]]]
*)

(* TERSE: HIDEFROMHTML *)
(** ... and then formally: *)

Reserved Notation "t '-->' t'" (at level 40).

(** TERSE: *** *)
Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_IsZero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IsZeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_IsZero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(** FULL: The [nvalue] conditions in [ST_PredSucc] and [ST_IszeroSucc] are
    needed for determinism (will be proved in an optional exercise below). *)

(* TERSE: /HIDEFROMHTML *)
(** FULL: Notice that the [step] relation doesn't care about whether the
    expression being stepped makes global sense -- it just checks that
    the operation in the _next_ reduction step is being applied to the
    right kinds of operands.  For example, the term [succ true] cannot
    take a step, but the almost as obviously nonsensical term
[[
       succ (if true then true else true)
]]
    can take a step (once, before becoming stuck). *)


(* ###################################################################### *)
(** ** Normal Forms and Values *)

(** The first interesting thing to notice about this [step] relation
    is that the strong progress theorem from the \CHAP{Smallstep}
    chapter fails here.  That is, there are terms that are normal
    forms (they can't take a step) but not values (they are not
    included in our definition of possible "results of reduction").

    Such terms are _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.
(* TERSE: HIDEFROMHTML *)

Hint Unfold stuck : core.
(* TERSE: /HIDEFROMHTML *)

(* FULL *)
(* EX2 (some_term_is_stuck) *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  (* ADMITTED *)
  exists <{ succ false }>.
  unfold stuck. split.
    - (* normal form *)
      unfold normal_form. intros [t' Hstp].
      solve_by_inverts 2.
    - (* not a value *)
      intros H. solve_by_inverts 3.  Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)
(** However, although values and normal forms are _not_ the same in this
    language, the set of values is a subset of the set of normal forms.

    This is important because it shows we did not accidentally define
    things so that some value could still take a step. *)

(* FULL *)
(* EX3 (value_is_nf) *)
(* /FULL *)
(* SOONER: Not exactly sure why, but this seems to be very tricky
   for students. *)
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
(* FOLD *)
Proof.
  (* ADMITTED *)
  intros t H.
  (* Here is the easier way: *)
  unfold normal_form.
  destruct H as [H|H].
  - (* boolean value *) destruct H.
    + (* true *) intros [t' P]. inversion P.
    + (* false *) intros [t' P]. inversion P.
  - (* numeric value *)
    Print nvalue.
    induction H.
    + (* nv_0 *) intros [t' P]. inversion P.
    + (* nv_succ *) intros [t' P]. inversion P.
      subst. apply IHnvalue.
      exists t1'. assumption.  Qed.
(* /ADMITTED *)
(* /FOLD *)
(* FULL *)

(** (Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways.) *)
(** [] *)
(* /FULL *)
(* HIDE *)

(* Induction on the term itself. *)
Lemma value_is_nf' : forall t,
  value t -> step_normal_form t.
Proof.
  intros t. unfold normal_form.
  induction t; intros H []; try (solve_by_inverts 2).
  (* The [succ] case is the only one that doesn't immediately
     present a contradiction. Considering how a [succ] term can be
     a value, it is syntactically not a boolean value, but the numeric
     value case requires a bit more work. *)
  inversion H; try solve_by_invert.
  (* By the IH, if [t] is a numeric value, then it can not step. *)
  inversion H0; subst. inversion H1; subst.
  apply IHt.
  - right. assumption.
  - exists t1'. assumption.
Qed.
(* /HIDE *)
(* LATER: MRC:  Here's a third proof that (at least to me)
   is easier than either of the proofs above. It uses induction
   on the term itself, as in the second proof above, but it has
   the simple proof structure of the first proof above.

Ltac inv H := inversion H; subst; clear H.

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros t Hvalt Hstep. inv Hvalt.
  - (* bool value *) solve_by_inverts 3.
  - (* nat value *) induction H.
    + (* 0 *) solve_by_inverts 3.
    + (* succ *) apply IHnvalue. inv Hstep. inv H0. exists t1'. assumption.
Qed.
*)

(* FULL *)
(* EX3? (step_deterministic) *)
(** Use [value_is_nf] to show that the [step] relation is also
    deterministic. *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  (* ADMITTED *)
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1;
   intros y2 Hy2; inversion Hy2; subst; auto;
     try solve_by_invert.
   - (* ST_If *)
    apply IHHy1 in H3. rewrite H3. reflexivity.
   - (* ST_Succ *)
    apply IHHy1 in H0. rewrite H0. reflexivity.
   - (* ST_PredSucc *)
    inversion H1; subst. exfalso.
     apply value_is_nf with v...
   (* ST_Pred *)
   - (* Hy2 by ST_PredSucc *)
    inversion Hy1; subst. exfalso.
      apply value_is_nf with y2...
   - (* Hy2 by ST_Pred *)
      apply IHHy1 in H0. rewrite H0. reflexivity.
   - (* ST_IsZeroSucc *)
    inversion H1; subst. exfalso.
     apply value_is_nf with v...
   (* ST_IsZero *)
   - (* Hy2 by ST_IsZeroSucc *)
     inversion Hy1; subst. exfalso.
     apply value_is_nf with v...
   - (* Hy2y b ST_IsZero *)
     apply IHHy1 in H0. rewrite H0. reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)
(* QUIZ *)
(** Is the following term stuck?
[[
    iszero (if true then (succ 0) else 0)
]]

    (A) Yes

    (B) No

*)
(* /QUIZ *)
(* QUIZ *)
(** What about this one? Is it stuck?
[[
    if (succ 0) then true else false
]]

    (A) Yes

    (B) No

*)
(* /QUIZ *)
(* QUIZ *)
(** What about this one? Is it stuck?
[[
    succ (succ 0)
]]

    (A) Yes

    (B) No
*)
(* /QUIZ *)
(* QUIZ *)
(** What about this one? Is it stuck?
[[
    succ (if true then true else true)
]]

    (A) Yes

    (B) No

    (Hint: Notice that the [step] relation doesn't care about whether the
    expression being stepped makes global sense -- it just checks that
    the operation in the _next_ reduction step is being applied to the
    right kinds of operands.)
*)
(* /QUIZ *)
(* HIDE *)
(* ###################################################################### *)
(* These exercises are good practice with step relations, though they
   aren't all that relevant to the material in this unit.  It would be
   worth uncommenting and fixing them up at some point.  Note that
   eval should be renamed to step. *)
(** *** Exercises *)

(* A SOLUTION TO ADD

     Suppose, now, that we define an alternate version of the
     single-step evaluation relation that drops the premise
     @nvalue n1@ from the rules @E_PredSucc@ and @E_IsZeroSucc@:

     Inductive alteval : tm -> tm -> Prop :=
       | AE_IfTrue : forall t1 t2,
             alteval (if True t1 t2)
                     t1
       | AE_IfFalse : forall t1 t2,
             alteval (if false t1 t2)
                     t2
       | AE_If : forall t1 t1' t2 t3,
             alteval t1 t1' ->
             alteval (if t1 t2 t3)
                     (if t1' t2 t3)
       | AE_Succ : forall t1 t1',
             alteval t1 t1' ->
             alteval (<{succ t1}>)
                     (<{succ t1'}>)
       | AE_Pred0 :
             alteval (<{pred 0}>)
                     <{0}>
       | AE_PredSucc : forall t1,
             (* nvalue t1 -> *)
             alteval <{pred (succ t1)}>
                     t1
       | AE_Pred : forall t1 t1',
             alteval t1 t1' ->
             alteval <{ pred t1 }>
                     <{ pred t1' }>
       | AE_IsZero0 :
             alteval <{ iszero 0}>
                     Truee
       | AE_IsZeroSucc : forall t1,
             (* nvalue t1 -> *)
             alteval <{ iszero (succ t1)}>
                     false
       | AE_IsZero : forall t1 t1',
             alteval t1 t1' ->
             alteval <{ iszero t1 }>
                     <{ t1'}>.

Is the alternate evaluation relation deterministic?  That is, is
the following lemma provable?  (Write ``yes'' or ``no.''  If you
write ``no,'' give a counter-example.)

\begin{verbatim}
    Lemma alteval_deterministic : forall t t' t'',
         alteval t t'  ->
         alteval t t'' ->
         t' = t''.
\end{verbatim}

No.  A counter-example is @t = pred (succ (pred 0)) @

-----------

Is every normal form in the original @eval@ relation also a normal form in
the alternate evaluation relation?  That is, if we define
\begin{verbatim}
    Notation eval_normal_form    := (normal_form _ eval).
    Notation alteval_normal_form := (normal_form _ alteval).
\end{verbatim}
is the following lemma provable?  (Write ``yes'' or ``no.''  If you write ``no,'' give a counter-example.)
%
\begin{verbatim}
    Lemma eval_nf__alteval_nf : forall t,
      eval_normal_form t -> alteval_normal_form t.
\end{verbatim}

\answer[1.2in]{No.  A counter-example is @t = pred (succ true)@.}

------

What about the converse?  Is every normal form in the @alteval@ relation
also a normal form in the original evaluation relation?  That is, is the
following lemma provable?  (Write ``yes'' or ``no.''  If you write ``no,'' give a counter-example.)
%
\begin{verbatim}
    Lemma alteval_nf__eval_nf : forall t,
      alteval_normal_form t -> eval_normal_form t.
\end{verbatim}

\answer{Yes.}

-----------

Can every {\em value} that results from applying @eval@ many times also be
obtained by applying @alteval@ many times?

Formally, if we define
\begin{verbatim}
    Notation evalmany    := (refl_trans_closure _ eval).
    Notation altevalmany := (refl_trans_closure _ alteval).
\end{verbatim}
then is the lemma
\begin{verbatim}
    Lemma eval_result__alteval_result : forall t t',
         evalmany t t' ->
         value t' ->
         altevalmany t t'.
\end{verbatim}
provable?  Write ``yes'' or ``no.''  If you write ``no,'' give a counter-example.

\answer[2in]{Yes.}

-----------

Conversely, can every
value that results from applying @alteval@ many times also be obtained by
applying @eval@ many times?
Write ``yes'' or ``no.''  If you write ``no,'' give a counter-example.
\begin{verbatim}
    Lemma alteval_result__eval_result : forall t t',
         altevalmany t t' ->
         value t' ->
         evalmany t t'.
\end{verbatim}
\answer{No.  A counter-example is @t = iszero (succ true)@.}

*)

(* A SOLUTION TO FILL IN (it may not make sense -- we haven't
   showed them a step *function* -- but this might be a
   nice (optional) opportunity for them to see one...

Complete the following @Fixpoint@ definition so that it defines
a functional version of the @alteval@ relation -- i.e., so that
@alt_simplify_step t = Some _ t'@ whenever @alteval t t'@ holds and
@alt_simplify_step t = None _@ if there is no @t'@ such that
%
@alteval t t'@.
\ifanswers
\begin{alltt}
  Fixpoint alt_simplify_step (t:tm) : option tm :=
    match t with
    | <{ if t1 then t2 else t3 }> =>
        match alt_simplify_step t1 with
        | None => match t1 with
                  | <{ true }> => Some _ t2
                  | <{ false }> => Some _ t3
                  | _ => None _
                  end
        | Some t1' => Some _ (<{ if t1' then t2 else t3 }>)
        end
    | <{ succ t1 }> =>
        match alt_simplify_step t1 with
        | None => None _
        | Some t1' => Some _ (<{ succ t1' }>)
        end
    | <{ pred t1 }> =>
        (* FILL IN HERE: *)
        match alt_simplify_step t1 with
        | None => match t1 with
                  | <{ 0 }> => Some _ <{ 0 }>
                  | <{ succ t2 }> => Some _ t2
                  end
        | Some t1' => Some _ (<{ pred t1' }>)
        end
    | <{ iszero t1 }> =>
        (* FILL IN HERE: *)
        match alt_simplify_step t1 with
        | None => match t1 with
                  | 0 => Some _ <{ true }>
                  | succ t2 => Some _ <{ false }>
                  end
        | Some t1' => Some _ <{ iszero t1' }>
        end
    | _ =>
        (* FILL IN HERE: *)
        None _
    end.
*)
(* /HIDE *)

(* ###################################################################### *)
(** ** Typing *)

(** FULL: The next critical observation is that, although this
    language has stuck terms, they are always nonsensical, mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)
(** TERSE: _Types_ describe the possible shapes of values: *)

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.
(* TERSE *)

(** ** Typing Relations *)
(* /TERSE *)

(* NOTATION: SOONER: BCP 19: Wondering if we should replace "\in" by just
   "in"... The backslash is ugly, and I've never succeeded in getting the
   \in to reliably typeset as a symbol.  I suppose something like :: would
   be another alternative.  Or indeed just :, if we put <{...}> around all
   typing judgements. BCP 23: :: seems not to work (not sure why - maybe
   used in the standard library?), but putting <{...}> around all typing
   judgements seems like a better solution anyway.  Then, I think, we could
   just use :, which would be perfect.  Maybe even |- instead of |-- ??*)
(** TERSE: The _typing relation_ [|-- t \in T] relates terms to the types
    of their results: *)
(** FULL: In informal notation, the typing relation is often written
    [|-- t \in T] and pronounced "[t] has type [T]."  The [|--] symbol
    is called a "turnstile."  Below, we're going to see richer typing
    relations where one or more additional "context" arguments are
    written to the left of the turnstile.  For the moment, the context
    is always empty. *)
(** [[[
                           -----------------                   (T_True)
                           |-- true \in Bool

                          ------------------                   (T_False)
                          |-- false \in Bool

           |-- t1 \in Bool    |-- t2 \in T    |-- t3 \in T
           -----------------------------------------------     (T_If)
                   |-- if t1 then t2 else t3 \in T

                             --------------                    (T_0)
                             |-- 0 \in Nat

                            |-- t1 \in Nat
                          -------------------                  (T_Succ)
                          |-- succ t1 \in Nat

                            |-- t1 \in Nat
                          -------------------                  (T_Pred)
                          |-- pred t1 \in Nat

                            |-- t1 \in Nat
                          ----------------------               (T_IsZero)
                          |-- iszero t1 \in Bool
]]]
*)

(* TERSE: HIDEFROMHTML *)
(* SOONER: Andrew Appel 23: In my opinion, 80 is the wrong level, and
   Iris made the wrong decision. However, last year we modified the
   VST level to 80 because some research projects import both VST and
   Iris. So I still recommend 80 for SF. *)
(* HIDEFROMHTML *)
Declare Custom Entry ty.
Notation "'Nat'" := Nat (in custom ty).
Notation "'Bool'" := Bool (in custom ty).
Notation "x" := x (in custom ty, x global).

Reserved Notation "<{ '|--' t '\in' T }>"
            (at level 0, t custom tm, T custom ty).
(* /HIDEFROMHTML *)

(* SOONER: BCP 21: What about putting the brackets around the very
   outside? I.e., <{ |-- true \in Bool }> instead of |-- <{ true }> \in
   Bool?  After all, the type (and later the context) are also from
   the object language... *)
(* NOTATION: SAZ 2024 - I have implemented this suggestion, which
   I think is a bit nicer.  We can get away with a simpler solution
   in this file because we don't have variables, etc.
 *)

(** TERSE: *** *)
Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       <{ |-- true \in Bool }>
  | T_False :
       <{ |-- false \in Bool }>
  | T_If : forall t1 t2 t3 T,
       <{ |-- t1 \in Bool }> ->
       <{ |-- t2 \in T }> ->
       <{ |-- t3 \in T }> ->
       <{ |-- if t1 then t2 else t3 \in T }>
  | T_0 :
       <{ |-- 0 \in Nat }>
  | T_Succ : forall t1,
       <{ |-- t1 \in Nat }> ->
       <{ |-- succ t1 \in Nat }>
  | T_Pred : forall t1,
       <{ |-- t1 \in Nat }> ->
       <{ |-- pred t1 \in Nat }>
  | T_Iszero : forall t1,
       <{ |-- t1 \in Nat }> ->
       <{ |-- iszero t1 \in Bool }>

where "<{ '|--' t '\in' T }>" := (has_type t T).

Hint Constructors has_type : core.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
Example has_type_1 :
  <{ |-- if false then 0 else (succ 0) \in Nat }>.
Proof.
  apply T_If.
  - apply T_False.
  - apply T_0.
  - apply T_Succ. apply T_0.
Qed.

(** FULL: (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)

(** TERSE: *** *)

(** FULL: It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not consider
    what happens when the term is reduced -- in particular, it does
    not calculate the type of its normal form. *)
(** TERSE: Typing is a _conservative_ (or _static_) approximation to
    behavior.

    In particular, a term can be ill typed even though it steps to
    something well typed. *)

Example not_has_type :
  ~ <{ |-- if false then 0 else true \in Bool }>.
(* FOLD *)
Proof.
  intros Contra. solve_by_inverts 2.  Qed.
(* /FOLD *)

Example not_has_type' :
  ~ <{ |-- if iszero (succ 0) then succ false else true \in Bool }>.
(* FOLD *)
Proof.
  intros Contra. solve_by_inverts 2.  Qed.
(* /FOLD *)

(* FULL *)
(* EX1? (succ_hastype_nat__hastype_nat) *)
Example succ_hastype_nat__hastype_nat : forall t,
  <{ |--  succ t \in Nat }> ->
  <{ |-- t \in Nat }>.
Proof.
  (* ADMITTED *)
  intros t H. inversion H. subst. assumption.  Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* LATER: add some more examples? *)

(* ###################################################################### *)
(** *** Canonical forms *)

(** The following two lemmas capture the fundamental fact that the
    definitions of boolean and numeric values agree with the typing
    relation. *)

Lemma bool_canonical : forall t,
  <{ |-- t \in Bool }> -> value t -> bvalue t.
(* FOLD *)
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - destruct Hn as [ | Hs].
    + inversion HT.
    + inversion HT.
Qed.
(* /FOLD *)

Lemma nat_canonical : forall t,
  <{ |-- t \in Nat }> -> value t -> nvalue t.
(* FOLD *)
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.
(* /FOLD *)

(* ###################################################################### *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.

    The first is that well-typed normal forms are not stuck -- or
    conversely, if a term is well typed, then either it is a value or it
    can take at least one step.  We call this _progress_. *)

(* FULL *)
(* EX3 (finish_progress) *)
(* GRADE_THEOREM 3: progress *)
(* /FULL *)
Theorem progress : forall t T,
  <{ |-- t \in T }> ->
  value t \/ exists t', t --> t'.

(* FULL *)
(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the parts we've given of the informal proof in the
    following exercise before starting -- this will save you a lot of
    time.) *)
(* /FULL *)
(* FOLD *)
Proof.
  intros t T HT.
  induction HT; auto.
  (* The cases that were obviously values, like T_True and
     T_False, are eliminated immediately by auto *)
  - (* T_If *)
    right. destruct IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    destruct H.
      * exists t2. auto.
      * exists t3. auto.
    + (* t1 can take a step *)
      destruct H as [t1' H1].
      exists <{ if t1' then t2 else t3 }>. auto.
  (* ADMITTED *)
  - (* T_Succ *)
    destruct IHHT.
    + (* t1 is a value *)
      apply (nat_canonical t1 HT) in H. auto.
    + (* t1 can take a step *)
      right. destruct H as [t' H1].
      exists <{ succ t' }>. auto.
  - (* T_Pred *)
    destruct IHHT.
    + (* t1 is a value *)
      apply (nat_canonical t1 HT) in H.
      right.
      destruct H.
      * exists <{ 0 }>. auto.
      * exists t. auto.
    + (* t1 steps *)
     right.
     destruct H as [t' H1].
     exists <{ pred t' }>. auto.
  - (* T_Iszero *)
    destruct IHHT.
    + (* t1 is a value *)
      apply (nat_canonical t1 HT) in H.
      right.
      destruct H.
      * exists <{ true }>. auto.
      * exists <{ false }>. auto.
    + (* t1 steps *)
     right.
     destruct H as [t' H1].
     exists <{ iszero t' }>. auto.
Qed.
(* /ADMITTED *)
(* /FOLD *)
(* FULL *)
(** [] *)
(* /FULL *)
(* TERSE *)

(* QUIZ *)
(** What is the relation between the _progress_ property defined here
    and the _strong progress_ from \CHAP{SmallStep}?

    (A) No difference -- they mean the same thing

    (B) Progress implies strong progress

    (C) Strong progress implies progress

    (D) No relationship

    (E) Dunno

*)
(* /QUIZ *)
(* /TERSE *)
(* FULL *)

(* EX3AM? (finish_progress_informal) *)
(** Complete the corresponding informal proof: *)

(** _Theorem_: If [|-- t \in T], then either [t] is a value or else
    [t --> t'] for some [t']. *)

(** _Proof_: By induction on a derivation of [|-- t \in T].

    - If the last rule in the derivation is [T_If], then [t = if t1
      then t2 else t3], with [|-- t1 \in Bool], [|-- t2 \in T] and [|-- t3
      \in T].  By the IH, either [t1] is a value or else [t1] can step
      to some [t1'].

      - If [t1] is a value, then by the canonical forms lemmas
        and the fact that [|-- t1 \in Bool] we have that [t1]
        is a [bvalue] -- i.e., it is either [true] or [false].
        If [t1 = true], then [t] steps to [t2] by [ST_IfTrue],
        while if [t1 = false], then [t] steps to [t3] by
        [ST_IfFalse].  Either way, [t] can step, which is what
        we wanted to show.

      - If [t1] itself can take a step, then, by [ST_If], so can
        [t].

    - (* SOLUTION *)

    - If the last rule in the derivation is [T_True], then [t = true],
      which is a boolean value and hence a value.  The cases for
      [T_False] and [T_0] are similar.

    - If the last rule in the derivation is [T_Succ], then
      [t = succ t1], with [|-- t1 \in Nat].  By the IH, either [t1] is a value
      or else [t1] can step to some [t1'].

      - If [t1] is a value, then by the canonical forms lemma [t1] is
        a [nvalue], and hence [t] is also an [nvalue] (and hence
        a value) by [nv_succ].

      - If [t1] can take a step, then by [ST_Succ], so can [t].

    - If the last rule in the derivation is [T_Pred], then [t = pred t1],
      with [|-- t1 \in Nat].  By the IH, either [t1] is a value or else
      [t1] can step to some [t1'].

      - If [t1] is a value, then (by the same argument as in the
        previous case) it must be an [nvalue].  By case analysis on
        the [nvalue] judgement, there are two cases:

        - If [t1 = 0], then [t] can take a step by
          [ST_Pred0].

        - Otherwise, [t1 = succ t1'], with [t1'] an [nvalue].
          Hence [t] can again take a step, this time by [ST_PredSucc].

        - Finally, if [t1] can take a step, then by [ST_Pred], so
          can [t].

    - If the last rule in the derivation is [T_IsZero], then [t =
      iszero t1], with [|-- t1 \in Nat].  By the IH, either [t1] is a
      value or else [t1] steps to some [t1'].

      - If [t1] is a value, it must be an [nvalue], and there are
        two cases to consider:

        - If [t1 = 0], then [t] can take a step by [ST_IsZero0].

        - Otherwise, [t1 = succ t1'] where [t1'] is an [nvalue].
          Hence [t] can take a step by [ST_IsZeroSucc].

      - If [t1] can take a step, then so can [t], by [ST_IsZero].

    (* /SOLUTION *)
 *)
(* GRADE_MANUAL 3: finish_progress_informal *)
(** [] *)

(** This theorem is more interesting than the strong progress theorem
    that we saw in the \CHAP{Smallstep} chapter, where _all_ normal forms
    were values.  Here a term can be stuck, but only if it is ill
    typed. *)

(* /FULL *)
(* TERSE *)
(* QUIZ *)
(** Quick review:

    In the language defined at the start of this chapter...

      - Every well-typed normal form is a value.

    (A) True

    (B) False
*)
(* /QUIZ *)
(* INSTRUCTORS *)
(* TRUE: This is the content of the progress theorem. *)
(* /INSTRUCTORS *)

(* QUIZ *)
(** In this language...

      - Every value is a normal form.

    (A) True

    (B) False
*)
(* /QUIZ *)
(* INSTRUCTORS *)
(* TRUE: This can proved by induction on values. *)
(* /INSTRUCTORS *)

(* QUIZ *)
(** In this language...

      - The single-step reduction relation is
        a partial function (i.e., it is deterministic).

    (A) True

    (B) False
*)
(* /QUIZ *)
(* INSTRUCTORS *)
(* TRUE: This is the determinism theorem. *)
(* /INSTRUCTORS *)

(* QUIZ *)
(** In this language...

      - The single-step reduction relation is a _total_ function.

    (A) True

    (B) False
*)
(* /QUIZ *)
(* INSTRUCTORS *)
(* FALSE: normal forms do not reduce to anything. *)
(* /INSTRUCTORS *)
(* /TERSE *)

(* ###################################################################### *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is a well-typed term (of the same type). *)

(* TERSE: HIDEFROMHTML *)
(* FULL: EX2 (finish_preservation) *)
(* TERSE: /HIDEFROMHTML *)
(* GRADE_THEOREM 2: preservation *)
Theorem preservation : forall t t' T,
  <{ |-- t \in T }> ->
  t --> t' ->
  <{ |-- t' \in T }>.
(* TERSE: HIDEFROMHTML *)

(** FULL: Complete the formal proof of the [preservation] property.
    (Again, make sure you understand the informal proof fragment in
    the following exercise first.) *)

(* FOLD *)
Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
    (* every case needs to introduce a couple of things... *)
       intros t' HE;
    (* and we can deal with several impossible cases at once... *)
       try solve_by_invert.
    - (* T_If *) inversion HE; subst; clear HE.
      + (* ST_IFTrue *) assumption.
      + (* ST_IfFalse *) assumption.
      + (* ST_If *) apply T_If; try assumption.
        apply IHHT1; assumption.
    (* ADMITTED *)
    - (* T_Succ *) inversion HE; subst. auto.
    - (* T_Pred *) inversion HE; subst; auto.
      + (* ST_PredSucc *) inversion HT; subst. assumption.
    - (* T_IsZero *) inversion HE; subst; auto.  Qed.
(* /ADMITTED *)
(* /FOLD *)
(* FULL *)
(** [] *)
(* /FULL *)
(* TERSE: /HIDEFROMHTML *)

(* FULL *)
(* EX3AM? (finish_preservation_informal) *)
(** Complete the following informal proof: *)

(** _Theorem_: If [|-- t \in T] and [t --> t'], then [|-- t' \in T]. *)

(** _Proof_: By induction on a derivation of [|-- t \in T].

    - If the last rule in the derivation is [T_If], then [t = if t1
      then t2 else t3], with [|-- t1 \in Bool], [|-- t2 \in T] and [|-- t3
      \in T].

      Inspecting the rules for the small-step reduction relation and
      remembering that [t] has the form [if ...], we see that the
      only ones that could have been used to prove [t --> t'] are
      [ST_IfTrue], [ST_IfFalse], or [ST_If].

      - If the last rule was [ST_IfTrue], then [t' = t2].  But we
        know that [|-- t2 \in T], so we are done.

      - If the last rule was [ST_IfFalse], then [t' = t3].  But we
        know that [|-- t3 \in T], so we are done.

      - If the last rule was [ST_If], then [t' = if t1' then t2
        else t3], where [t1 --> t1'].  We know [|-- t1 \in Bool] so,
        by the IH, [|-- t1' \in Bool].  The [T_If] rule then gives us
        [|-- if t1' then t2 else t3 \in T], as required.

    - (* SOLUTION *)

    - If the last rule in the derivation were [T_True], then [t = True].
      However, [True] does not step to anything, so this case is
      vacuously true.

    - Similarly, neither [T_False] nor [T_0] could not be the final
      rule in the derivation.

    - If the last rule in the derivation is [T_Succ], then [t =  succ t1]
      with [|-- t1 \in Nat] and [T = Nat]. The only rule which could
      have been used to show that [t] steps is [ST_Succ], in which
      case [t1] steps to some [t1'].  So, by the IH, [|-- t1' \in Nat],
      and hence [t' = succ t1'] also has type [Nat] by [T_Succ].

    - If the last rule in the derivation is [T_Pred], then [t =  pred t1]
      with [|-- t1 \in Nat].  There are only three rules which could
      have been the last rule in the derivation of [pred t1 --> t'].

      - If the last rule was [ST_PredZro], then [t' = 0] which
        has type [Nat].

      - If the last rule was [ST_PredSucc], then [t1 = succ t'];
        by inversion on the fact that [|-- t1 \in Nat] it follows
        that [|-- t' \in Nat] as well.

      - If the last rule was [ST_Pred], then [t1] steps to some [t1'];
        by the IH [|-- t1' \in Nat], and so [pred t1'] has type [Nat]
        as well by [T_Pred].

    - If the last rule in the derivation is [T_IsZero], then [t =
      iszero t1] with [|-- t1 \in Nat] and [T = Bool].  There are only
      three rules which could have been the last rule in the
      derivation of [< iszero t1 }> --> t'].

      - If the last rule was [ST_IsZeroZro], then [t' = true] which
        has type [Bool].

      - If the last rule was [ST_IsZeroSucc], then [t' = false] which
        has type [Bool].

      - If the last rule was [ST_IsZero], then [t1] steps to some [t1'].
        By the IH, [|-- t1' \in Nat] as well, and hence [t' = iszero t1']
        has type [Bool] by [T_IsZero].

    (* /SOLUTION *)
*)
(* GRADE_MANUAL 3: finish_preservation_informal *)
(** [] *)
(* /FULL *)

(* FULL *)
(* EX3 (preservation_alternate_proof) *)
(* GRADE_THEOREM 3: preservation' *)
(** Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proofs to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)

Theorem preservation' : forall t t' T,
  <{ |-- t \in T }> ->
  t --> t' ->
  <{ |-- t' \in T }>.
Proof with eauto.
  (* ADMITTED *)
  intros t t' T HT HE.
  generalize dependent T.
  induction HE;
         (* in each case, invert the given typing derivation *)
         intros T HT; inversion HT; subst;
         (* deal with several easy or contradictory cases
            all at once *)
         try solve [assumption; solve_by_inverts]...
    - (* ST_PredSucc *)
      inversion HT. subst. inversion H2. subst...  Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** FULL: The preservation theorem is often called _subject reduction_,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)

(* ###################################################################### *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we see that a
    well-typed term can never reach a stuck state.  *)

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  <{ |-- t \in T }> ->
  t -->* t' ->
  ~(stuck t').
(* FOLD *)
Proof.
  intros t t' T HT P. induction P; intros [R S].
  - apply progress in HT. destruct HT; auto.
  - apply IHP.
    + apply preservation with (t := x); auto.
    + unfold stuck. split; auto.
Qed.
(* /FOLD *)

(* QUIZ *)
(** Suppose we add the following two new rules to the reduction
    relation:
[[
      | ST_PredTrue :
           pred true --> pred false
      | ST_PredFalse :
           pred false --> pred true
]]
   Which of the following properties remain true in the presence
   of these rules?  (Choose 1 for yes, 2 for no.)
      - Determinism of [step]

(* HIDE *)
            Remains true
(* /HIDE *)
      - Progress

(* HIDE *)
            Remains true
(* /HIDE *)
      - Preservation

(* HIDE *)
            Remains true
(* /HIDE *)
*)
(* /QUIZ *)
(* QUIZ *)
(** Suppose, instead, that we add this new rule to the typing relation:
[[
      | T_IfFunny : forall t2 t3,
           |-- t2 \in Nat ->
           |--  if true then t2 else t3 }> \in Nat
]]
   Which of the following properties remain true in the presence
   of these rules?
      - Determinism of [step]

(* HIDE *)
            Remains true
(* /HIDE *)
      - Progress

(* HIDE *)
            Remains true
(* /HIDE *)
      - Preservation

(* HIDE *)
            Remains true
(* /HIDE *)
*)

(* /QUIZ *)
(* ###################################################################### *)
(* FULL *)
(** ** Additional Exercises *)

(* EX3! (subject_expansion) *)
(** Having seen the subject reduction property, one might
    wonder whether the opposite property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t --> t']
    and [|-- t' \in T], then [|-- t \in T]?  If so, prove it.  If
    not, give a counter-example.

    (* SOLUTION *)
       Subject expansion does not hold in this language (or most
       interesting languages).  For example, [if false
       then true else 0] is ill typed, but it reduces to the
       well-typed term [0].
    (* /SOLUTION *)
*)

Theorem subject_expansion:
  (forall t t' T, t --> t' /\ <{ |-- t' \in T }> -> <{ |-- t \in T }>)
  \/
  ~ (forall t t' T, t --> t' /\ <{ |-- t' \in T }> -> <{ |-- t \in T }>).
Proof.
  (* ADMITTED *)
  right.
  intro HSE.
  assert (HT: <{ |-- if false then true else 0 \in Nat }> ).
  { apply HSE with (t' := <{ 0 }>).
    split.
    { apply ST_IfFalse. }
    { apply T_0. } }
  inversion HT.
  inversion H4.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)
(* HIDE *)
(* EX2M? (variation1a) *)
(** Suppose we add the following two new rules to the reduction
    relation:
[[
      | ST_PredTrue :
           pred true --> pred false
      | ST_PredFalse :
           pred false --> pred true
]]
   Do the following properties remain true in the presence
   of these rules? For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.

      - Determinism of [step]
(* QUIETSOLUTION *)
            Remains true
(* /QUIETSOLUTION *)
      - Progress
(* QUIETSOLUTION *)
            Remains true
(* /QUIETSOLUTION *)
      - Preservation
(* QUIETSOLUTION *)
            Remains true
(* /QUIETSOLUTION *)
*)
(** [] *)

(* EX2M? (variation1b) *)
(** Suppose, instead, that we add this new rule to the typing relation:
[[
      | T_IfFunny : forall t2 t3,
           <{ |-- t2 \in Nat }> ->
           <{ |--  if true then t2 else t3 }> \in Nat }>
]]
   Which of the following properties remain true in the presence of
   this rule?  (Answer in the same style as above.)
      - Determinism of [step]
            (* SOLUTION *)
            Remains true
(* /SOLUTION *)
      - Progress
(* QUIETSOLUTION *)
            Remains true
(* /QUIETSOLUTION *)
      - Preservation
(* QUIETSOLUTION *)
            Remains true
(* /QUIETSOLUTION *)
*)
(** [] *)
(* /HIDE *)

(* FULL *)
(* EX2M (variation1) *)
(** Suppose that we add this new rule to the typing relation:
[[
      | T_SuccBool : forall t,
           <{ |-- t \in Bool }> ->
           <{ |--  succ t \in Bool }>
]]
   Which of the following properties remain true in the presence of
   this rule?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]
            (* SOLUTION *)
            Remains true
(* /SOLUTION *)
      - Progress
            (* SOLUTION *)
            Becomes false:  [succ true] is well typed, but stuck.
(* /SOLUTION *)
      - Preservation
            (* SOLUTION *)
            Remains true
(* /SOLUTION *)
*)
(* GRADE_MANUAL 2: variation1 *)
(** [] *)

(* EX2M (variation2) *)
(** Suppose, instead, that we add this new rule to the [step] relation:
[[
      | ST_Funny1 : forall t2 t3,
           (<{ if true then t2 else t3 }>) --> t3
]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
            (* SOLUTION *)
       - Determinism becomes false: [if true then 0 else (succ 0)] can now
         reduce in one step to either [0] or [succ 0].
(* /SOLUTION *)
*)
(* GRADE_MANUAL 2: variation2 *)
(** [] *)

(* EX2? (variation3) *)
(** Suppose instead that we add this rule:
[[
      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 --> t2' ->
           (<{ if t1 then t2 else t3 }>) --> (<{ if t1 then t2' else t3 }>)
]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
            (* SOLUTION *)
       - Determinism again becomes false: [if false then (pred 0) else (succ 0)}>]
         can now reduce in one step to either [succ 0 }>] or
         [if false then 0 else (succ 0)}>].  (There are several other correct
         counter-examples.)
(* /SOLUTION *)
*)
(** [] *)

(* EX2? (variation4) *)
(** Suppose instead that we add this rule:
[[
      | ST_Funny3 :
          (<{pred false}>) --> (<{ pred (pred false)}>)
]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
(* SOLUTION *)
   All remain true
(* /SOLUTION *)
*)
(** [] *)

(* EX2? (variation5) *)
(** Suppose instead that we add this rule:
[[
      | T_Funny4 :
            |-- <{ 0 }> \in Bool
]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
(* SOLUTION *)
       - Progress becomes false: [if 0 then true else true }>] has type [Bool],
         is a normal form, and is not a value.
(* /SOLUTION *)
*)
(** [] *)

(* EX2? (variation6) *)
(** Suppose instead that we add this rule:
[[
      | T_Funny5 :
            |--  pred 0 }> \in Bool
]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
(* SOLUTION *)
       - Preservation becomes false: [pred 0 }>] has type
         [Bool] and reduces in one step to [0 }>], which
         does not have type [Bool].
(* /SOLUTION *)
*)
(** [] *)

(* EX3? (more_variations) *)
(** Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
*)
(* SOLUTION *)
(* /SOLUTION *)
(** [] *)

(* LATER: How about turning this into variation9? *)
(* EX1M (remove_pred0) *)
(** The reduction rule [ST_Pred0] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of [0] to
    be undefined, rather than being defined to be [0].  Can we
    achieve this simply by removing the rule from the definition of
    [step]?  Would doing so create any problems elsewhere?

(* SOLUTION *)
    Yes, but doing this would break the progress property.
    A better way would be to raise an exception in this case, but this
    requires that we add exceptions to the language we're formalizing!
(* /SOLUTION *)
*)
(* GRADE_MANUAL 1: remove_pred0  *)
(** [] *)

(* EX4AM (prog_pres_bigstep) *)
(** Suppose our evaluation relation is defined in the big-step style.
    State appropriate analogs of the progress and preservation
    properties. (You do not need to prove them.)

    Can you see any limitations of either of your properties?  Do they
    allow for nonterminating programs?  Why might we prefer the
    small-step semantics for stating preservation and progress?

(* SOLUTION *) The type preservation property for the big-step
    semantics is similar to the one we gave for the small-step
    semantics: if a well-typed term evaluates to some final value,
    then this value has the same type as the original term.  The proof
    is similar to the one we gave.  However, preservation for small-step
    semantics implies that all intermediate states (i.e., all states
    reachable in multi-step) are well-typed, whereas big-step semantics
    only relates a term to its final evaluation result, with no notion
    of "intermediate state" about which preservation can make guarantees.

    The situation with the progress property is more interesting.  A
    direct analog (if a term is well typed then it evaluates to some
    other term) makes a much stronger claim than the progress theorem
    we have given: it says that every well-typed term can be evaluated
    to some final value---that is, that evaluation always terminates
    on well-typed terms.  For arithmetic expressions, this happens to
    be the case, but for more interesting languages (languages
    involving general recursion, for example) it will often not be
    true.  For such languages, we simply have no progress property in
    the big-step style: in effect, there is no way to tell the
    difference between reaching an error state and failing to
    terminate.  This is one reason that language theorists generally
    prefer the small-step style.
(* /SOLUTION *)
*)
(* GRADE_MANUAL 6: prog_pres_bigstep *)
(** [] *)
(* /FULL *)
(* TERSE: HIDEFROMHTML *)
End TM.
(* TERSE: /HIDEFROMHTML *)
(* HIDE *)
(* ###################################################################### *)
(** *** Exercise: Typed Imp *)
From PLF Require Import Imp.
Module TImp.
(* LATER: This section was originally intended as a challenging
   exercise -- we'd give them the basic definitions with maybe some
   holes left for them to fill in bits, and they'd complete both the
   definitions and the relevant proofs.  But we're having trouble
   making a good exercise out of it: the statements of the theorems
   are a bit tricky, and the proofs are quite dense and quite
   automated.  One possibility is to make it into an _informal_ proof
   exercise -- have them fill in the definitions and then write
   informal proofs of a couple of things. *)

(* Crunching the two syntactic categories of expressions into one,
   adding lists, and removing a few operations (Minus, Times,
   equality, ...) for brevity. *)
(* LATER: Rename exp to tm and change metavariable conventions below.
   Also, change all the Axxx and Bxxx to the same thing, whatever it
   is! *)
Inductive exp : Type :=
  | ANum : nat -> exp
  | AId : string -> exp
  | APlus : exp -> exp -> exp
  | AHead : exp -> exp
  | ATail : exp -> exp
  | ACons : exp -> exp -> exp
  | ANil  : exp
  | BTrue : exp
  | BFalse : exp
  | BLe : exp -> exp -> exp
  | BNot : exp -> exp
  | BIsCons : exp -> exp.

Inductive value : exp -> Prop :=
| VNum : forall n, value (ANum n)
| VNil : value ANil
| VCons : forall e l, value e -> value l -> value (ACons e l)
| VTrue : value BTrue
| VFalse : value BFalse.

Hint Constructors value : core.

(* Since we no longer have a separate datatype of values, we can just
   put expressions in the state.  By convention, we'll always reduce
   them to values first. *)
Definition state := partial_map exp.

Definition empty_state : state := empty.

(* HIDEFROMHTML *)
Reserved Notation " t '/' st '-->e' t' " (at level 40, st at level 39).
(* /HIDEFROMHTML *)

(* LATER: Need to change to  (state * exp) -> exp, if we do that in Smallstep.v *)
(* NOTATION: LATER: Convert the concrete syntax, if we ever end up
   un-HIDING this... *)
Inductive estep : state -> exp -> exp -> Prop :=
  | AS_Id : forall st i v,
    st i = Some v ->
    AId i / st -->e v
  | AS_Plus : forall st n1 n2,
    APlus (ANum n1) (ANum n2) / st -->e ANum (plus n1 n2)
  | AS_Plus1 : forall st a1 a1' a2,
    a1 / st -->e a1' ->
    (APlus a1 a2) / st -->e (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
    value v1 ->
    a2 / st -->e a2' ->
    (APlus v1 a2) / st -->e (APlus v1 a2')
  | AS_HeadNil : forall st,
    AHead ANil / st -->e ANum 0  (* arbitrary *)
  | AS_HeadCons : forall st a1 a2,
    value a1 ->
    value a2 ->
    AHead (ACons a1 a2) / st -->e a1
  | AS_Head : forall st a1 a1',
    a1 / st -->e a1' ->
    AHead a1 / st -->e AHead a1'
  | AS_TailNil : forall st,
    ATail ANil / st -->e ANil
  | AS_TailCons : forall st a1 a2,
    value a1 ->
    ATail (ACons a1 a2) / st -->e a2
  | AS_Tail : forall st a1 a1',
    a1 / st -->e a1' ->
    ATail a1 / st -->e ATail a1'
  | AS_Cons1 : forall st a1 a1' a2,
    a1 / st -->e a1' ->
    (ACons a1 a2) / st -->e (ACons a1' a2)
  | AS_Cons2 : forall st v1 a2 a2',
    value v1 ->
    a2 / st -->e a2' ->
    (ACons v1 a2) / st -->e (ACons v1 a2')
  | AS_IsConsNil : forall st,
    BIsCons ANil / st -->e BFalse
  | AS_IsConsCons : forall st a1 a2,
    value a1 ->
    value a2 ->
    BIsCons (ACons a1 a2) / st -->e BTrue
  | AS_IsCons : forall st a1 a1',
    a1 / st -->e a1' ->
    BIsCons a1 / st -->e BIsCons a1'
  | BS_LtEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st -->e
             (if (n1 <=? n2) then BTrue else BFalse)
  | BS_LtEq1 : forall st a1 a1' a2,
    a1 / st -->e a1' ->
    (BLe a1 a2) / st -->e (BLe a1' a2)
  | BS_LtEq2 : forall st v1 a2 a2',
    value v1 ->
    a2 / st -->e a2' ->
    (BLe v1 a2) / st -->e (BLe v1 (a2'))
  | BS_NotTrue : forall st,
    (BNot BTrue) / st -->e BFalse
  | BS_NotFalse : forall st,
    (BNot BFalse) / st -->e BTrue
  | BS_NotStep : forall st b1 b1',
    b1 / st -->e b1' ->
    (BNot b1) / st -->e (BNot b1')

  where " t '/' st '-->e' t' " := (estep st t t').

Hint Constructors estep : core.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> exp -> com
  | CSeq : com -> com -> com
  | CIf : exp -> com -> com -> com
  | CWhile : exp -> com -> com.

(* INSTRUCTORS: A copy of template com *)
Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(* INSTRUCTORS: Template for expr *)
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom com at level 75, right associativity).

Notation "'is_cons' t" := (BIsCons t) (in custom com at level 75, right associativity).
Notation "h :: t" := (ACons h t) (in custom com at level 50, left associativity).
Notation "'nil'" := (ANil) (in custom com at level 0).
Notation "'hd' t" := (AHead t) (in custom com at level 75, right associativity).
Notation "'tl' t" := (ATail t) (in custom com at level 75, right associativity).

Coercion ANum : nat >-> exp.
Coercion AId : string >-> exp.

Check <{ skip; skip }>.

Reserved Notation " t '/' st '-->' t' '/' st' " (at level 40, st at next level, t' at next level, left associativity).
Locate ";".

Check fun st i v => i !-> Some v; st.

Inductive cstep : (state * com) -> (state * com) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
    a1 / st -->e a1' ->
    <{i := a1 }> / st --> <{ i := a1'}> / st
  | CS_Asgn : forall st i v,
    value v ->
    <{ i := v }> / st --> <{ skip }> / (i |-> v ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
    c1 / st --> c1' / st' ->
    <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
    <{ skip ; c2 }> / st --> c2 / st
  | CS_IfTrue : forall st c1 c2,
    <{ if BTrue then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
    <{ if BFalse then c1 else c2 end }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
    b1 / st -->e b1' ->
    <{ if b1 then c1 else c2 end }> / st --> <{ if b1' then c1 else c2 end}> / st
  | CS_While : forall st b1 c1,
        <{ while b1 do c1 end }> / st
    --> <{ if b1 then c1 ; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (st,t) (st',t')).

Hint Constructors cstep : core.

Notation "t1 '-->*' t2" := (multi cstep t1 t2) (at level 40).

Example timp_example1 : exists st', (empty_state, <{ X := 42 }> ) -->* (st', <{skip }>).
  eexists. normalize.
Qed.

Hint Constructors estep : core.
Hint Constructors value : core.

Hint Extern 2 (_ = _) => compute; reflexivity : core.

Example timp_example2 : exists st',
  (empty_state, <{ X := 42 ; Y := X + 2 }> ) -->*
  (st', <{skip }> ) .
Proof.
  eexists. normalize.
Qed.

Definition list_rev :=
<{
  while is_cons X
  do
    Y := (hd X) :: Y  ;
    X := tl X
  end
}>.


Example timp_example3 : exists st',
  ((X |-> <{ 1 :: 2 :: 3 :: nil }> ; Y |-> <{ nil }>),
  list_rev) -->* (st', <{ skip }> ) .
Proof.
  unfold list_rev.
  eexists. normalize.
Qed.

Inductive ty : Type :=
  | Nat : ty
  | Natlist : ty
  | Bool : ty.

(* Typing relation *)

Definition state_typing := partial_map ty.

Definition empty_state_typing : state_typing := empty.

(* HIDEFROMHTML *)
Notation "'Nat'" := Nat (in custom ty).
Notation "'Natlist'" := Natlist (in custom ty).
Notation "'Bool'" := Bool (in custom ty).
Notation "x" := x (in custom ty, x global).

(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin MODIFIED  notation - based on template in Stlc.v        *)
Reserved Notation "<{ ST '|--' t '\in' T }>"
            (at level 0, ST custom com, t custom com, T custom ty).
(* INSTRUCTORS: End STCL has_type notation *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* /HIDEFROMHTML *)

Inductive has_type (ST : state_typing) : exp -> ty -> Prop :=
  | T_Num : forall (n : nat),
       <{ ST |-- n \in Nat }>
  | T_Id : forall i T,
       ST i = Some T ->
       <{ ST |-- i \in T }>
  | T_Plus : forall e1 e2,
       <{ ST |-- e1 \in Nat }> ->
       <{ ST |-- e2 \in Nat }> ->
       <{ ST |-- e1 + e2 \in Nat }>
(* LATER: Make them fill in some of these? *)
  | T_Head : forall e1,
       <{ ST |-- e1 \in Natlist }> ->
       <{ ST |-- hd e1 \in Nat }>
  | T_Tail : forall e1,
       <{ ST |-- e1 \in Natlist }> ->
       <{ ST |-- tl e1 \in Natlist }>
  | T_Cons : forall e1 e2,
       <{ ST |-- e1 \in Nat }> ->
       <{ ST |-- e2 \in Natlist }> ->
       <{ ST |-- e1 :: e2 \in Natlist }>
  | T_Nil :
       <{ ST |-- nil \in Natlist }>
  | T_True :
       <{ ST |-- true \in Bool }>
  | T_False :
       <{ ST |-- false \in Bool }>
  | T_Le : forall e1 e2,
       <{ ST |-- e1 \in Nat }> ->
       <{ ST |-- e2 \in Nat }> ->
       <{ ST |-- e1 <= e2 \in Bool }>
  | T_Not : forall e1,
       <{ ST |-- e1 \in Bool }> ->
       <{ ST |-- ~ e1 \in Bool }>
  | T_IsCons : forall e1,
       <{ ST |-- e1 \in Natlist }> ->
       <{ ST |-- is_cons e1 \in Bool }>

where "<{ ST '|--' t '\in' T }>" := (has_type ST t T).

Hint Constructors has_type : core.
Print Grammar constr.
Inductive well_typed (ST : state_typing) : com -> Prop :=
  | WT_Com :
      well_typed ST <{ skip }>
  | WT_Asgn : forall i e1 T,
      ST i = Some T ->
      has_type ST e1 T ->
      well_typed ST <{ i := e1 }>
(* LATER: Fill in the next two.  Maybe also WT_Seq. *)
  | WT_Seq : forall c1 c2,
      well_typed ST c1 ->
      well_typed ST c2 ->
      well_typed ST <{ c1 ; c2 }>
  | WT_If : forall e1 c1 c2,
      has_type ST e1 Bool ->
      well_typed ST c1 ->
      well_typed ST c2 ->
      well_typed ST <{ if e1 then c1 else c2 end }>
  | WT_While : forall e1 c1,
      has_type ST e1 Bool ->
      well_typed ST c1 ->
      well_typed ST <{ while e1 do c1 end }>.

Hint Constructors well_typed : core.

(* Progress *)

(* Note the form of the progress and preservation theorems for the
   different step relations... *)

Definition has_state_type (st : state) (ST : state_typing) : Prop :=
  forall i T,
    ST i = Some T ->
    exists e, st i = Some e /\ has_type ST e T.

(* LATER: Oof -- do we really expect them to understand this and
   preservation without any explanation in class?? *)
Theorem progress_exp : forall e T st ST,
  has_state_type st ST ->
  has_type ST e T ->
  value e \/ exists e', e / st -->e e'.
Proof with eauto.
  intros e T st ST Hst He.
  unfold has_state_type in Hst.
  induction He...
    - (* T_Id *) right. unfold has_state_type in Hst. apply Hst in H.
      destruct H as [sti Hsti]. destruct Hsti...
    - (* T_Plus *) right. destruct IHHe1.
      + (* e1 is a value *) destruct IHHe2...
        * (* e2 is a value *)
          inversion He1; inversion He2; subst; try solve_by_invert.
          exists (ANum (plus n n0))...
        * (* e2 steps *) destruct H0...
      + (* e1 steps *) destruct H...
    - (* T_Head *) right. destruct IHHe.
      + (* e1 is a value *)
        inversion H; subst; try solve_by_invert.
        * exists (ANum 0)...
        * exists e...
      + (* e1 steps *) destruct H...
    - (* T_Tail *) right. destruct IHHe.
      + (* e1 is a value *)
        inversion H; subst; try solve_by_invert.
        * exists ANil...
        * exists l...
      + (* e1 steps *) destruct H...
    - (* T_Cons *) destruct IHHe1.
      + (* e1 is a value *) destruct IHHe2.
        * (* e2 is a value *) left...
        * (* e2 steps *) destruct H0...
      + (* e1 steps *) destruct H...
    - (* T_Le *) right. destruct IHHe1.
      + (* e1 is a value *) destruct IHHe2.
        * (* e2 is a value *)
          inversion H; inversion H0; subst; try solve_by_invert.
          exists (if (n <=? n0) then BTrue else BFalse)...
        * (* e2 steps *) destruct H0...
      + (* e1 steps *) destruct H...
    - (* T_Not *) right. destruct IHHe.
      + (* e1 is a value *)
        inversion H; subst; try solve_by_invert.
        * exists BFalse...
        * exists BTrue...
      + (* e1 steps *) destruct H...
    - (* T_IsCons *) right. destruct IHHe.
      + (* e1 is a value *)
          inversion H; subst; try solve_by_invert.
          * exists BFalse...
          * exists BTrue...
      + (* e1 steps *) destruct H...
  Qed.

(* LATER: Tell them they'll need to use the progress_exp theorem in
   two of the cases. *)
Theorem progress_com : forall c st ST,
  has_state_type st ST ->
  well_typed ST c ->
  (c = <{ skip }>) \/ exists c' st', c / st --> c' / st'.
Proof with eauto.
  intros c st ST Hst Hc.
  induction Hc...
    - (* WT_Asgn *) right.
      destruct (progress_exp e1 T st ST Hst H0).
        + (* e is a value *) eexists. eexists. auto.
        + (* e can step *) inversion H1. eexists. eexists...
    - (* WT_Seq *) right.
      destruct IHHc1; subst.
        + (* c1 = skip *) eexists. eexists. eauto.
        + (* c1 can step *) inversion H. inversion H0.
          eexists. eexists...
    - (* WT_If *) right.
      destruct (progress_exp e1 Bool st ST Hst H).
      + (* e is a value *)
        inversion H0; clear H0; subst; try solve_by_invert.
        * (* e = BTrue *) eexists. eexists. auto.
        * (* e = BFalse *) eexists. eexists. auto.
      + (* e can step *) inversion H0. eexists. eexists...
  Qed.

(* Preservation *)

Theorem preservation_exp : forall e e' st ST T,
  has_state_type st ST ->
  has_type ST e T ->
  e / st -->e e' ->
  has_type ST e' T.
Proof with eauto.
  intros e e' st ST T Hst He Hstep.
  generalize dependent e'.
  induction He;
        intros e' Hstep; inversion Hstep; subst...
    - (* T_Id *) inversion Hstep; subst...
      unfold has_state_type in Hst. apply Hst in H. inversion H as [e'' He''].
      inversion He''. rewrite H2 in H0. injection H0 as H0. subst...
    - (* T_Head *)
      (* LATER: Isn't He the IH?  Why are we using it again? *)
      inversion He...
    - (* T_Tail *)
      (* LATER: Ditto *)
      inversion He...
    - (* T_Le *)
      destruct (n1 <=? n2)...
  Qed.

Theorem preservation_com : forall c c' st st' ST,
  has_state_type st ST ->
  well_typed ST c ->
  c / st --> c' / st' ->
  has_state_type st' ST /\ well_typed ST c'.
Proof with eauto.
  intros c c' st st' ST Hst Hc Hstep.
  generalize dependent c'. generalize dependent st'.
  induction Hc;
          intros st' c' Hstep; inversion Hstep; subst; clear Hstep...
    - (* WT_Asgn *) split...
      eapply WT_Asgn... eapply preservation_exp...
    - split... unfold has_state_type. intros.
      destruct (String.eqb_spec i i0) as [Hii0 | Hii0]; subst; eauto.
      + rewrite H in H1. clear H.
        injection H1 as H1. subst.
        exists e1.
        split; auto.
      + unfold has_state_type in Hst.
        apply Hst in H1.
        destruct H1 as [e0 [ST0 HT0] ].
        exists e0.
        split; auto.
        rewrite update_neq; auto.
    - (* WT_Seq *)
      (* LATER: Why can't I just do [split...]? *)
      split.
      + eapply IHHc1...
      + apply WT_Seq... eapply IHHc1...
    - (* WT_If *) split... apply WT_If... eapply preservation_exp...
Qed.

End TImp.
(* /HIDE *)
