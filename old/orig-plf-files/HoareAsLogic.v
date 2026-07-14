(** * HoareAsLogic: Hoare Logic as a Logic *)

(** The presentation of Hoare logic in chapter \CHAP{Hoare} could be
    described as "model-theoretic": the proof rules for each of the
    constructors were presented as _theorems_ about the evaluation
    behavior of programs, and proofs of program correctness (validity
    of Hoare triples) were constructed by combining these theorems
    directly in Rocq.

    Another way of presenting Hoare logic is to define a completely
    separate proof system -- a set of axioms and inference rules that
    talk about commands, Hoare triples, etc. -- and then say that a
    proof of a Hoare triple is a valid derivation in _that_ logic.  We
    can do this by giving an inductive definition of _valid
    derivations_ in this new logic.

    This chapter is optional.  Before reading it, you'll want to read
    the \CHAPV1{ProofObjects} chapter in _Logical
    Foundations_ (_Software Foundations_, volume 1). *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-deprecated-hint-without-locality,-deprecated-hint-without-locality,-parsing".
From PLF Require Import Maps.
From PLF Require Import Hoare.

Hint Constructors ceval : core.
(* TERSE: /HIDEFROMHTML *)

(** * Hoare Logic and Model Theory *)

(** FULL: In \CHAP{Hoare} we introduced Hoare triples, which contain a
    precondition, command, and postcondition.  For example (and for
    the moment deliberately avoiding the notation we previously
    introduced),
[[
      Pre:  X = 0
      Com:  X := X + 1
      Post: X = 1
]]
    is a Hoare triple, as is
[[
      Pre:  X = 0
      Com:  skip
      Post: X = 1
]]
    But there's an important difference between those two triples: the
    former expresses a truth about how Imp programs execute, whereas
    the latter does not.

    To capture that difference, we introduced a definition
    [valid_hoare_triple] that described when a triple expresses such a
    truth.  Let's repeat that definition, but this time we'll call it
    [valid]: *)

(** TERSE: A _valid_ Hoare triple expresses a truth about how Imp
    program execute. *)

Definition valid (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.

(** FULL: This notion of _validity_ is based on the underlying model of how
    Imp programs execute.  That model itself is based on states.  So,
[[
      Pre:  X = 0
      Com:  X := X + 1
      Post: X = 1
]]
    is _valid_, because starting from any state in which [X] is [0],
    and executing [X := X + 1], we are guaranteed to reach a state in
    which [X] is [1]. But,
[[
      Pre:  X = 0
      Com:  skip
      Post: X = 1
]]
    is _invalid_, because starting from any state in which [X] is [0],
    we are guaranteed not to change the state, so [X] cannot be [1].
*)

(** So far, we have punned between the syntax of a Hoare triple,
    written [{{P}} c {{Q}}], and its validity, as expressed by
    [valid].  In essence, we have said that the semantic meaning of
    that syntax is the proposition returned by [valid].  This way of
    giving semantic meaning to something syntactic is part of the
    branch of mathematical logic known as _model theory_.  *)

(** FULL: Our approach to Hoare logic through model theory led us to
    state proof rules in terms of that same state-based model, and to
    prove program correctness in it, too.  But there is another
    approach, which is arguably more common in Hoare logic. We turn to
    it, next.  *)

(** * Hoare Logic and Proof Theory *)

(** FULL: Instead of using states and evaluation as the basis for reasoning,
    let's take the proof rules from \CHAP{Hoare} as the basis.  Those
    proof rules give us a set of axioms and inference rules that
    constitute a logic in their own right.  We repeat them here: *)

(** TERSE: Proof rules constitute a logic in their own right: *)

(**
[[
             ----------------  (hoare_skip)
             {{P}} skip {{P}}

             ----------------------------- (hoare_asgn)
             {{Q [X |-> a]}} X := a {{Q}}

               {{P}} c1 {{Q}}
               {{Q}} c2 {{R}}
              ------------------  (hoare_seq)
              {{P}} c1; c2 {{R}}

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}

            {{P /\ b}} c {{P}}
      ----------------------------- (hoare_while)
      {{P} while b do c end {{P /\ ~b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
]]
*)

(** FULL: Read the Hoare triples in those rules as devoid of any
    meaning other than what the rules give them.  Forget about states
    and evaluations.  They are just syntax that the rules tell us how
    to manipulate in legal ways.

    Through this new lens, triple [{{X = 0}} X := X + 1 {{X = 1}}]
    is _derivable_, because we can derive a proof tree using the rules:
*)

(** TERSE: *** *)
(** TERSE: Those rules can be used to show that a triple is _derivable_
    by constructing a proof tree: *)
(* SOONER: MRC'20: how to typeset this so that it shows up right in HTML? *)

(**
[[
                    ---------------------------  (hoare_asgn)
   X=0 ->> X+1=1    {{X+1=1}} X := X+1 {{X=1}}
   -------------------------------------------------------  (hoare_consequence)
                     {{X=0}} X := X+1 {{X=1}}
]]
*)

(** FULL: At each step we have either used one of the rules, or we
    have appealed to reasoning about assertions, which do not involve
    Hoare triples.  (Note that we have left off the trivial part of
    [hoare_consequence] above, namely X=1 ->> X=1, only because of
    horizontal space contraints: it's hard to fit that many characters
    on a line and have the page still be readable.  If you prefer,
    think of it as using [hoare_consequence_pre] instead.)

    On the other hand, [{{X = 0}} skip {{X = 1}}] is _not_ derivable,
    because there is no way to apply the rules to construct a proof
    tree with this triple at its root. *)

(** TERSE: *** *)

(** This approach gives meaning to triples not in terms of a model,
    but in terms of how they can be used to construct proof trees.
    It's a different way of giving semantic meaning to something
    syntactic, and it's part of the branch of mathematical logic known
    as _proof theory_.

    Our goal for the rest of this chapter is to formalize Hoare logic
    using proof theory, and then to prove that the model-theoretic and
    proof-theoretic formalizations are consistent with one another.
*)

(** * Derivability *)

(** To formalize derivability of Hoare triples, we introduce inductive type
    [derivable], which describes legal proof trees using the Hoare rules. *)

Inductive derivable : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      derivable P <{skip}> P
  | H_Asgn : forall Q V a,
      derivable ({{Q [V |-> a]}}) <{V := a}> Q
  | H_Seq : forall P c Q d R,
      derivable Q d R -> derivable P c Q -> derivable P <{c;d}> R
  | H_If : forall P Q b c1 c2,
    derivable (fun st => P st /\ bassertion b st) c1 Q ->
    derivable (fun st => P st /\ ~(bassertion b st)) c2 Q ->
    derivable P <{if b then c1 else c2 end}> Q
  | H_While : forall P b c,
    derivable (fun st => P st /\ bassertion b st) c P ->
    derivable P <{while b do c end}> (fun st => P st /\ ~ (bassertion b st))
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
    derivable P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.
(* FULL *)

(** We don't need to include axioms corresponding to
    [hoare_consequence_pre] or [hoare_consequence_post], because these
    can be proven easily from [H_Consequence]. *)

Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    derivable P' c Q ->
    (forall st, P st -> P' st) ->
    derivable P c Q.
(* FOLD *)
Proof. eauto using H_Consequence. Qed.
(* /FOLD *)

Lemma H_Consequence_post  : forall (P Q Q' : Assertion) c,
    derivable P c Q' ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.
(* FOLD *)
Proof. eauto using H_Consequence. Qed.
(* /FOLD *)
(* /FULL *)

(** TERSE: *** *)

(** As an example, let's construct a proof tree for
[[
        {{(X=3) [X |-> X + 2] [X |-> X + 1]}}
      X := X + 1;
      X := X + 2
        {{X=3}}
]]
*)

Example sample_proof :
  derivable
    ({{ $(fun st:state => st X = 3)  [X |-> X + 2] [X |-> X + 1] }})
    <{ X := X + 1; X := X + 2}>
    (fun st:state => st X = 3).
Proof.
  eapply H_Seq.
  - apply H_Asgn.
  - apply H_Asgn.
Qed.

(** You can see how the structure of the proof script mirrors the structure
    of the proof tree: at the root there is a use of the sequence rule; and
    at the leaves, the assignment rule. *)

(* FULL *)

(* EX3 (provable_true_post) *)

(** Show that any Hoare triple whose postcondition is [True] is derivable. Proceed
    by induction on [c]. *)

Theorem provable_true_post : forall c P,
    derivable P c True.
Proof.
  (* ADMITTED *)
  induction c; intros.
  - eapply H_Consequence_pre.
    + apply H_Skip.
    + auto.
  - eapply H_Consequence_pre.
    + apply H_Asgn.
    + auto.
  - eapply H_Consequence_pre.
    + eapply H_Seq; eauto.
    + eauto.
  - eapply H_Consequence_pre.
    + apply H_If; auto.
    + eauto.
  - eapply H_Consequence.
    + eapply H_While. eauto.
    + auto.
    + auto.
Qed.
(* /ADMITTED *)

(** [] *)

(* EX3 (provable_false_pre) *)

(** Show that any Hoare triple whose precondition is [False] is derivable. Again,
    proceed by induction on [c]. *)

Theorem provable_false_pre : forall c Q,
    derivable False c Q.
Proof.
  (* ADMITTED *)
  induction c; intros.
  - eapply H_Consequence_pre.
    + eapply H_Skip.
    + simpl. intros. contradiction.
  - eapply H_Consequence_pre.
    + apply H_Asgn.
    + simpl. intros. contradiction.
  - eapply H_Consequence_pre.
    + eapply H_Seq; eauto.
    + auto.
  - apply H_If; eapply H_Consequence_pre; eauto.
    + simpl. intros st [contra _]. contradiction.
    + simpl. intros st [contra _]. contradiction.
  - eapply H_Consequence_post.
    + eapply H_While. eapply H_Consequence_pre.
      * eauto.
      * simpl. intros st [contra _]. contradiction.
    + simpl. intros st [contra _]. contradiction.
Qed.
(* /ADMITTED *)

(** [] *)

(* /FULL *)


(** * Soundness and Completeness *)

(** We now have two approaches to formulating Hoare logic:

    - The model-theoretic approach uses [valid] to characterize when a Hoare
      triple holds in a model, which is based on states.

    - The proof-theoretic approach uses [derivable] to characterize when a Hoare
      triple is derivable as the end of a proof tree.

    Do these two approaches agree?  That is, are the valid Hoare triples exactly
    the derivable ones?  This is a standard question investigated in
    mathematical logic.  There are two pieces to answering it:

    - A logic is _sound_ if everything that is derivable is valid.

    - A logic is _complete_ if everything that is valid is derivable.

    We can prove that Hoare logic is sound and complete.

*)

(* FULL *)

(* EX3 (hoare_sound) *)

(** Prove that if a Hoare triple is derivable, then it is valid.
    Nearly all the work for this was already done in \CHAP{Hoare} as
    theorems [hoare_skip], [hoare_asgn], etc.; leverage those
    proofs. Proceed by induction on the derivation of the triple. *)

Theorem hoare_sound : forall P c Q,
  derivable P c Q -> valid P c Q.
Proof.
  (* ADMITTED *)
  intros P c Q HP. induction HP.
  - apply hoare_skip.
  - apply hoare_asgn.
  - eapply hoare_seq; eauto.
  - apply hoare_if; auto.
  - apply hoare_while. auto.
  - eapply hoare_consequence; eauto.
Qed.
(* /ADMITTED *)
(** [] *)

(** The proof of completeness is more challenging.  To carry out the
    proof, we need to invent some intermediate assertions using a
    technical device known as _weakest preconditions_ (which are also
    discussed in \CHAP{Hoare2}).  Given a command [c] and a desired
    postcondition assertion [Q], the weakest precondition [wp c Q] is
    an assertion [P] such that [{{P}} c {{Q}}] holds, and moreover,
    for any other assertion [P'], if [{{P'}} c {{Q}}] holds then [P'
    ->> P].

    Another way of stating that idea is that [wp c Q] is the following
    assertion: *)

Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.

Hint Unfold wp : core.

(** The following two theorems show that the two ways of thinking
    about [wp] are the same. *)

Theorem wp_is_precondition : forall c Q,
  {{$(wp c Q)}} c {{Q}}.
Proof. auto. Qed.

Theorem wp_is_weakest : forall c Q P',
    {{P'}} c {{Q}} ->
    P' ->> (wp c Q).
Proof. eauto. Qed.

(** Weakest preconditions are useful because they enable us to
    identify assertions that otherwise would require clever thinking.
    The next two lemmas show that in action. *)

(* EX1 (wp_seq) *)

(** What if we have a sequence [c1; c2], but not an intermediate assertion for
    what should hold in between [c1] and [c2]?  No problem.  Prove that [wp c2 Q]
    suffices as such an assertion. *)

Lemma wp_seq : forall P Q c1 c2,
    derivable P c1 (wp c2 Q) -> derivable (wp c2 Q) c2 Q -> derivable P <{c1; c2}> Q.
Proof.
  (* ADMITTED *)
  intros. econstructor; eassumption.
Qed.
(* /ADMITTED *)

(** [] *)

(* EX2 (wp_invariant) *)

(** What if we have a while loop, but not an invariant for it?  No
    problem.  Prove that for any [Q], assertion [wp (while b do c end)
    Q] is a loop invariant of [while b do c end]. *)

Lemma wp_invariant : forall b c Q,
    valid ({{$(wp <{while b do c end}> Q) /\ b}}) c (wp <{while b do c end}> Q).
Proof.
  (* ADMITTED *)
  intros b c Q st st' Ec [Hwp Hb]. unfold wp in *.
  intros st'' Eloop. apply Hwp. econstructor; eassumption.
Qed.
(* /ADMITTED *)

(** [] *)

(* EX4 (hoare_complete) *)

(** Now we are ready to prove the completeness of Hoare logic.  Finish
    the proof of the theorem below.

    Hint: for the [while] case, use the invariant suggested by
    [wp_invariant].

    Acknowledgment: Our approach to this proof is inspired by:

      {https://www.ps.uni-saarland.de/courses/sem-ws11/script/Hoare.html}
*)

Theorem hoare_complete: forall P c Q,
  valid P c Q -> derivable P c Q.
Proof.
  unfold valid. intros P c. generalize dependent P.
  induction c; intros P Q HT.
  (* ADMITTED *)
  - eapply H_Consequence_pre.
    + apply H_Skip.
    + intros st. apply HT. constructor.
  - eapply H_Consequence_pre.
    + apply H_Asgn.
    + intro st. apply HT. constructor. reflexivity.
  - apply wp_seq.
    + apply IHc1. unfold wp. intros st st' E1 H st'' E2.
      eapply HT; eauto.
    + apply IHc2. auto.
  - apply H_If.
    + eapply IHc1. intros st st' E [H1 H2]. eapply HT.
      * apply E_IfTrue; eassumption.
      * assumption.
    + eapply IHc2. intros st st' E [H1 H2]. eapply HT.
      * apply E_IfFalse.
        ** unfold bassertion in H2. rewrite Bool.not_true_iff_false in H2.
           rewrite <- H2. reflexivity.
        ** assumption.
      * assumption.
  - (* while:  P' is the invariant. *)
     eapply H_Consequence with (P' := wp <{while b do c end}> Q).
       + eapply H_While. eapply IHc. eapply wp_invariant.
       + unfold wp. intros st HP st' E. eapply HT; eassumption.
       + unfold wp. simpl. intros st [E Hb]. apply E. apply E_WhileFalse.
         rewrite Bool.not_true_iff_false in Hb. assumption.
Qed.
(* /ADMITTED *)

(** [] *)

(* /FULL *)

(* HIDE:
    As a last step, we can show that the set of [hoare_proof] axioms
    is sufficient to prove any true fact about (partial) correctness.
    More precisely, any semantic Hoare triple that we can prove can
    also be proved from these axioms.  Such a set of axioms is said to
    be _relatively complete_.  That is, the axioms are complete _relative
    to_ what we can prove in the underlying assertion language.  If there
    are gaps in what can be proved in that language, then we blame it,
    not the Hoare logic axioms. *)
(* HIDE: MRC'20: The notion of *relative* completeness really doesn't
   rear its ugly head in the above proof, because the assertion language
   is relative to...Rocq!  The paragraph above seems more cryptic than
   illuminating. *)

(** * Postscript: Decidability *)

(** We might hope that Hoare logic would be _decidable_; that is, that
    there would be an (terminating) algorithm (a _decision procedure_)
    that can determine whether or not a given Hoare triple is valid or
    derivable.  Sadly, such a decision procedure cannot exist.

    Consider the triple [{{True}} c {{False}}]. This triple is valid
    if and only if [c] is non-terminating.  So any algorithm that
    could determine validity of arbitrary triples could solve the
    Halting Problem.

    Similarly, the triple [{{True}} skip {{P}}] is valid if and only
    if [forall s, P s] is valid, where [P] is an arbitrary assertion
    of Rocq's logic. But this logic is far too powerful to be
    decidable. *)

(* HIDE: MRC'20: I find this paragraph overly pessimistic:
   -----
    Overall, this axiomatic style of presentation gives a clearer
    picture of what it means to "give a proof in Hoare logic."
    However, it is not entirely satisfactory from the point of view of
    writing down such proofs in practice: it is quite verbose.  The
    section of chapter \CHAP{Hoare2} on formalizing decorated programs
    shows how we can do even better.
   -----
   Formalized decorative programs are not proofs.  They are rather propositions
   that might or might not be provable.  To compare them to derivations is
   to compare apples to oranges. *)

(* LATER: Arguably, the one there is so much better that we should not
   bother with this one!  Delete this file??

   CH: Unless one wants to prove (relative) completeness of the rules,
   which has a very simple and elegant proof:
   https://www.ps.uni-saarland.de/courses/sem-ws11/script/Hoare.html#completeness
   We can't prove completeness with respect to a bunch of theorems.
   We need inductive rules for that.

   BCP: OK, we'll leave the chapter in for now.

   MRC'20: I argue to keep the file.  It gets an important aspect not just of
   Hoare logic but of logic in general. *)
