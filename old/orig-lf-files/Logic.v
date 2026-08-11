(** * Logic: Logic in Rocq *)

(* INSTRUCTORS: Warning: This is a LOT of material to get through in
   two 80-minute lectures, and the last couple of sections are quite
   meaty.  Pacing is key!

*)
(* SOONER: Unlike earlier chapters, there are probably too many
   WORKINCLASSes in this chapter.  BCP 20: But conversely some more
   quizzes would be great! *)
(* HIDEFROMHTML *)
Set Warnings "-notation-overridden".
Require Nat.
From LF Require Export Tactics.
(* /HIDEFROMHTML *)

(** FULL: We have now seen many examples of factual claims (i.e.,
    _propositions_) and ways of presenting evidence of their truth
    (_proofs_).  In particular, we have worked extensively with
    equality propositions ([e1 = e2]), implications ([P -> Q]), and
    quantified propositions ([forall x, P]).  In this chapter, we will
    see how Rocq can be used to carry out other familiar forms of
    logical reasoning.

    Before diving into details, we should talk a bit about the status
    of mathematical statements in Rocq. Rocq is a _typed_ language,
    which means that every sensible expression has an associated type.
    Logical claims are no exception: any statement we might try to
    prove in Rocq has a type, namely [Prop], the type of
    _propositions_.  We can see this with the [Check] command: *)

(* TERSE *)
(** So far, we have seen...

       - _propositions_: mathematical statements, so far only of 3 kinds:
             - equality propositions ([e1 = e2])
             - implications ([P -> Q])
             - quantified propositions ([forall x, P])

       - _proofs_: ways of presenting evidence for the truth of a
          proposition

    In this chapter we will introduce several more flavors of both
    propositions and proofs. *)

(** * The [Prop] Type *)

(** Like everything in Rocq, well-formed propositions have a _type_: *)
(* /TERSE *)

Check (forall n m : nat, n + m = m + n) : Prop.

(** TERSE: *** *)
(** Note that _all_ syntactically well-formed propositions have type
    [Prop] in Rocq, regardless of whether they are true or not.

    Simply _being_ a proposition is one thing; being _provable_ is
    a different thing! *)

Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.

(** FULL: Indeed, propositions don't just have types -- they are
    _first-class_ entities that can be manipulated in all the same ways as
    any of the other things in Rocq's world. *)

(** TERSE: *** *)
(** So far, we've seen one primary place where propositions can appear:
    in [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** FULL: But propositions can be used in other ways.  For example, we
    can give a name to a proposition using a [Definition], just as we
    give names to other kinds of expressions. *)
(** TERSE: *** *)
(** TERSE: Propositions are first-class entities in Rocq, though. For
    example, we can name them: *)

(* HIDE: Right now, this idiom is used in exactly one place in earlier
   chapters: in an exercise in Tactics.v.  I'm going to ignore this
   and pretend we're introducing it here.  BCP 1/16 *)
Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

(** FULL: We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity.  Qed.

(** TERSE: *** *)
(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. *)

(** FULL: For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

(** TERSE: *** *)
(** In Rocq, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an _injective function_. *)

Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros x y H. injection H as H1. apply H1.
Qed.

(** TERSE: *** *)
(** The familiar equality operator [=] is a (binary) function that returns
    a [Prop].

    The expression [n = m] is syntactic sugar for [eq n m] (defined in
    Rocq's standard library using the [Notation] mechanism).

    Because [eq] can be used with elements of any type, it is also
    polymorphic: *)

Check @eq : forall A : Type, A -> A -> Prop.

(** FULL: (Notice that we wrote [@eq] instead of [eq]: The type
    argument [A] to [eq] is declared as implicit, and we need to turn
    off the inference of this implicit argument to see the full type
    of [eq].) *)
(* TERSE *)

(* QUIZ *)
(** What is the type of the following expression?
[[
       pred (S O) = O
]]
   (A) [Prop]

   (B) [nat->Prop]

   (C) [forall n:nat, Prop]

   (D) [nat->nat]

   (E) Not typeable










*)
(* /QUIZ *)
(* FOLD *)
Check (pred (S O) = O) : Prop.
(* /FOLD *)

(* QUIZ *)
(** What is the type of the following expression?
[[
      forall n:nat, pred (S n) = n
]]
   (A) [Prop]

   (B) [nat->Prop]

   (C) [forall n:nat, Prop]

   (D) [nat->nat]

   (E) Not typeable










*)
(* /QUIZ *)
(* FOLD *)
Check (forall n:nat, pred (S n) = n) : Prop.
(* /FOLD *)

(* QUIZ *)
(** What is the type of the following expression?
[[
      forall n:nat, S (pred n) = n
]]
   (A) [Prop]

   (B) [nat->Prop]

   (C) [nat->nat]

   (D) Not typeable










*)
(* /QUIZ *)
(* FOLD *)
Check (forall n:nat, S (pred n) = n) : Prop.
(* /FOLD *)

(* QUIZ *)
(** What is the type of the following expression?
[[
      forall n:nat, S (pred n)
]]
   (A) [Prop]

   (B) [nat->Prop]

   (C) [nat->nat]

   (D) Not typeable










*)
(* FOLD *)
Fail Check (forall n:nat, S (pred n)).
(* The command has indeed failed with message:
   In environment
   n : nat
   The term "(S (pred n))" has type "nat" which should be Set, Prop or Type. *)
(* /FOLD *)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of the following expression?
[[
      fun n:nat => S (pred n)
]]
   (A) [Prop]

   (B) [nat->Prop]

   (C) [nat->nat]

   (D) Not typeable









*)
(* FOLD *)
Check (fun n:nat => pred (S n)) : nat -> nat.
(* /FOLD *)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of the following expression?
[[
      fun n:nat => S (pred n) = n
]]
   (A) [Prop]

   (B) [nat->Prop]

   (C) [nat->nat]

   (D) Not typeable










*)
(* FOLD *)
Check (fun n:nat => pred (S n) = n) : nat -> Prop.
(* /FOLD *)
(* /QUIZ *)

(* QUIZ *)
(** Which of the following is _not_ a proposition?

    (A) [3 + 2 = 4]

    (B) [3 + 2 = 5]

    (C) [3 + 2 =? 5]

    (D) [((3+2) =? 4) = false]

    (E) [forall n, (((3+2) =? n) = true) -> n = 5]

    (F) All of these are propositions









*)
(* /QUIZ *)
(* FOLD *)
Check 3 + 2 =? 5 : bool.
Fail Definition bad : Prop := 3 + 2 =? 5.
(* The command has indeed failed with message: *)
(* The term "3 + 2 =? 5" has type "bool" while it is expected to have
   type "Prop". *)
(* /FOLD *)
(* /TERSE *)

(* #################################################################### *)
(** * Logical Connectives *)

(** ** Conjunction *)

(** The _conjunction_, or _logical and_, of propositions [A] and [B] is
    written [A /\ B]; it represents the claim that both [A] and [B] are
    true. *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, start with the [split] tactic.  This will
    generate two subgoals, one for each part of the statement: *)

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

(** TERSE: *** *)

(** For any propositions [A] and [B], if we assume that [A] and [B]
    are each true individually, we can conclude that [A /\ B] is also
    true.  The Rocq library provides a function [conj] that does this. *)

Check @conj : forall A B : Prop, A -> B -> A /\ B.

(** TERSE: we can [apply conj] to achieve the same effect as [split]. *)

(* FULL *)
(** Since applying a theorem with hypotheses to some goal has the
    effect of generating as many subgoals as there are hypotheses for
    that theorem, we can apply [conj] to achieve the same effect as
    [split]. *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.
(* /FULL *)

(* FULL *)
(* EX2 (plus_is_O) *)
(* /FULL *)

(** TERSE: *** *)

Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  (* FULL: ADMITTED *)
  (* TERSE: WORKINCLASS *)
  intros [|n'] m.
  - (* n = 0 *)
    simpl. intros H. split.
    + reflexivity.
    + apply H.
  - (* n = S n' *)
    simpl. intros H. discriminate H.
Qed.
(* FULL: /ADMITTED *)
(* TERSE: /WORKINCLASS *)
(* FULL *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)
(** So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to help prove
    something else -- we can use our good old [destruct] tactic. *)

(** FULL: When the current proof context contains a hypothesis [H] of the
    form [A /\ B], writing [destruct H as [HA HB]] will remove [H]
    from the context and replace it with two new hypotheses: [HA],
    stating that [A] is true, and [HB], stating that [B] is true.  *)

(* HIDE: MRC'20: Using [destruct H as [Hn Hm] eqn:HE] below has the
   unfortunate effect of adding [H = conj Hn Hm] to the hypotheses, and we
   can't explain what that means at this point.  (See the discussion above
   [and_intro].) One possibility is to give a forward reference to
   ProofObjects.  But I suggest instead simply omitting the [eqn] clause.
   That's what I have now done below in [and_example2] and [and_example3].
   BCP 23: I have replaced [and_intro] by [conj] above, but still probably
   best to leave off the [eqn] clauses here. *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKINCLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
(* /WORKINCLASS *)

(** TERSE: *** *)

(** As usual, we can also destruct [H] right at the point where we
    introduce it, instead of introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(* FULL *)
(** TERSE: *** *)
(** You may wonder why we bothered packing the two hypotheses [n = 0] and
    [m = 0] into a single conjunction, since we could also have stated the
    theorem with two separate premises: *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** TERSE: For the present example, both ways work.  But ... *)
(** TERSE: *** *)
(** TERSE: In other situations we may wind up with a
    conjunctive hypothesis in the middle of a proof... *)
(** FULL: For this specific theorem, both formulations are fine.  But
    it's important to understand how to work with conjunctive
    hypotheses because conjunctions often arise from intermediate
    steps in proofs, especially in larger developments.  Here's a
    simple example: *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKINCLASS *)
  intros n m H.
  apply plus_is_O in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.
(* /WORKINCLASS *)
(* /FULL *)
(* FULL *)

(** Another common situation is that we know [A /\ B] but in some
    context we need just [A] or just [B].  In such cases we can do a
    [destruct] (possibly implicitly, as part of an [intros]) and use
    an underscore pattern [_] to indicate that the unneeded conjunct
    should just be thrown away. *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
(* HIDEFROMADVANCED *)
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP.  Qed.
(* /HIDEFROMADVANCED *)

(* HIDEFROMADVANCED *)
(* EX1? (proj2) *)
(* /HIDEFROMADVANCED *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
(* HIDEFROMADVANCED *)
Proof.
  (* ADMITTED *)
  intros P Q [_ HQ].
  apply HQ.  Qed.
  (* /ADMITTED *)
(** [] *)
(* /HIDEFROMADVANCED *)

(** Finally, we sometimes need to rearrange the order of conjunctions
    and/or the grouping of multi-way conjunctions. We can see this
    at work in the proofs of the following commutativity and
    associativity theorems *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
(* HIDEFROMADVANCED *)
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.

(* EX1 (and_assoc) *)
(** In the following proof of associativity, notice how the _nested_
    [intros] pattern breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP : P], [HQ : Q], and [HR : R].  Finish the proof. *)
(* /HIDEFROMADVANCED *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
(* HIDEFROMADVANCED *)
Proof.
  intros P Q R [HP [HQ HR]].
  (* ADMITTED *)
  split.
  - (* left *) split.
    + (* left *) apply HP.
    + (* right *) apply HQ.
  - (* right *) apply HR.  Qed.
(* /ADMITTED *)
(** [] *)
(* /HIDEFROMADVANCED *)
(* /FULL *)

(** TERSE: *** *)
(** The infix notation [/\] is actually just syntactic sugar for
    [and A B].  That is, [and] is a Rocq operator that takes two
    propositions as arguments and yields a proposition. *)

Check and : Prop -> Prop -> Prop.

(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_,
    of two propositions: [A \/ B] is true when either [A] or [B] is.
    This infix notation stands for [or A B], where
    [or : Prop -> Prop -> Prop]. *)

(** TERSE: *** *)
(** To use a disjunctive hypothesis in a proof, we proceed by case
    analysis -- which, as with other data types like [nat], can be done
    explicitly with [destruct] or implicitly with an [intros]
    pattern: *)

(** HIDE: APT 21: There is nothing exactly like this in the library, so
    no particular name to match. But converse is named [mult_is_O], so
    I've changed this to [factor_is_O] to sort of match. *)
Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This intro pattern implicitly does case analysis on
     [n = 0 \/ m = 0]... *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** FULL: We can see in this example that, when we perform case
    analysis on a disjunction [A \/ B], we must separately discharge
    two proof obligations, each showing that the conclusion holds
    under a different assumption -- [A] in the first subgoal and [B]
    in the second.

    The case analysis pattern [[Hn | Hm]] allows us to name the
    hypotheses that are generated for the subgoals. *)

(** TERSE: *** *)

(** Conversely, to show that a disjunction holds, it suffices to show
    that one of its sides holds. This can be done via the tactics
    [left] and [right].  As their names imply, the first one requires
    proving the left side of the disjunction, while the second
    requires proving the right side.  Here is a trivial use... *)

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** TERSE: *** *)
(** ... and here is a slightly more interesting example requiring both
    [left] and [right]: *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKINCLASS *)
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.
(* /WORKINCLASS *)

(* TERSE: HIDEFROMHTML *)
(* EX2 (mult_is_O) *)
Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  (* ADMITTED *)
  intros [|n'] m H.
  - left. reflexivity.
  - destruct m as [|m'].
    + right. reflexivity.
    + simpl in H. discriminate H.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX1 (or_commut) *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* ADMITTED *)
  intros P Q [HP | HQ].
  - (* left *) right. apply HP.
  - (* right *) left. apply HQ.  Qed.
(* /ADMITTED *)
(** [] *)
(* TERSE: /HIDEFROMHTML *)

(** ** Falsehood and Negation *)

(** Up to this point, we have mostly been concerned with proving
    "positive" statements -- addition is commutative, appending lists
    is associative, etc.  We are sometimes also interested in negative
    results, demonstrating that some proposition is _not_ true. Such
    statements are expressed with the logical negation operator [~]. *)

(** TERSE: *** *)
(** To see how negation works, recall the _principle of explosion_
    from the \CHAP{Tactics} chapter, which asserts that, if we assume a
    contradiction, then any other proposition can be derived.

    Following this intuition, we could define [~ P] ("not [P]") as
    [forall Q, P -> Q]. *)

(** TERSE: *** *)
(** Rocq actually makes an equivalent but slightly different choice,
    defining [~ P] as [P -> False], where [False] is a specific
    un-provable proposition defined in the standard library. *)

(* HIDEFROMHTML *)
Module NotPlayground.
(* /HIDEFROMHTML *)

Definition not (P:Prop) := P -> False.

Check not : Prop -> Prop.

Notation "~ x" := (not x) : type_scope.

(* HIDEFROMHTML *)
End NotPlayground.
(* /HIDEFROMHTML *)

(** TERSE: *** *)
(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we can get [False] into the context,
    we can use [destruct] on it to complete any goal: *)
(* HIDE: (Christine) [inversion] also works. It also seems to work
   for eliminating conjunctions in a hypothesis.  There is no
   constructor for False, so I get it in this case.  Any intuition for
   why inversion destructs conjunctions in a hypothesis? *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.  Qed.

(** FULL: The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(* HIDE: Just before `not_implies_our_not`, it would be nice to have an
   explanation about how `destruct` works in implications (and maybe also
   about unfolding `not`).  BCP 9/18: Some more explanation of how destruct
   works on conjunctions, disjunctions, etc. would certainly be good.  Not
   sure why it would be good right here, though! *)
(* FULL *)
(* EX2? (not_implies_our_not) *)
(** Show that Rocq's definition of negation implies the intuitive one
    mentioned above.

    Hint: While getting accustomed to Rocq's definition of [not], you might
    find it helpful to [unfold not] near the beginning of proofs. *)

Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  (* ADMITTED *)
  intros P H Q HP. unfold not in H.
  apply ex_falso_quodlibet. apply H. apply HP.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)
(** Inequality is a very common form of negated statement, so there is a
    special notation for it: *)

Notation "x <> y" := (~(x = y)) : type_scope.

(** For example: *)

Theorem zero_not_one : 0 <> 1.
Proof.
  (** FULL: The proposition [0 <> 1] is exactly the same as
      [~(0 = 1)] -- that is, [not (0 = 1)] -- which unfolds to
      [(0 = 1) -> False]. (We use [unfold not] explicitly here,
      to illustrate that point, but generally it can be omitted.) *)
  unfold not.
  (** FULL: To prove an inequality, we may assume the opposite
      equality... *)
  intros contra.
  (** FULL: ... and deduce a contradiction from it. Here, the
      equality [O = S O] contradicts the disjointness of
      constructors [O] and [S], so [discriminate] takes care
      of it. *)
  discriminate contra.
Qed.

(* INSTRUCTORS: Since 8.2, there's a tactic "contradict H" that can be used
   to solve any kind of goal as long as the user can provide afterwards a
   proof of the negation of the hypothesis H.  If H is already a negation,
   say ~T, then a proof of T is asked.  If the current goal is a negation,
   say ~U, then U is saved in H.  We don't explain [contradict], though,
   just to save memory overhead on readers. *)
(** TERSE: *** *)
(** It takes a little practice to get used to working with negation in Rocq.
    Even though _you_ may see perfectly well why a claim involving
    negation holds, it can be a little tricky at first to see how to make
    Rocq understand it!

    Here are proofs of a few familiar facts to help get you warmed up. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

(** TERSE: *** *)
Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKINCLASS *)
  intros P Q [HP HNP]. unfold not in HNP.
  apply HNP in HP. destruct HP.  Qed.
(* /WORKINCLASS *)

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKINCLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.
(* /WORKINCLASS *)

(* FULL *)
(* EX2AM? (double_neg_informal) *)
(** Write an _informal_ proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P]. *)

(* SOLUTION *)
(* _Proof_: Suppose some proposition [P] holds.  We must show [~~P] --
   i.e., [~P -> False], so suppose [~P] as well and try to derive
   [False].  Then we have both [P] and [~P] (i.e., [P -> False]) from
   which we can indeed derive [False].  So [~~P] holds. *)
(* /SOLUTION *)

(* GRADE_MANUAL 2: double_neg_informal *)
(** [] *)

(* EX1! (contrapositive) *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* ADMITTED *)
  intros P Q H HNotB HP.
  apply HNotB.  apply H. apply HP.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX1 (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (* ADMITTED *)
  intros P H. destruct H as [HP HNA]. apply HNA. apply HP.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX1AM (not_PNP_informal) *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* SOLUTION *)
(* _Proof_: Suppose, for some [P], that [(P /\ ~P)] holds.  Recall that
   [~P] is defined as [P -> False].  Given [P] and [P -> False], we can
   prove [False], so [(P /\ ~P) -> False], i.e., [~ (P /\ ~P)]. *)
(* /SOLUTION *)

(* GRADE_MANUAL 1: not_PNP_informal *)
(** [] *)

(* EX2 (de_morgan_not_or) *)
(** _De Morgan's Laws_, named for Augustus De Morgan, describe how
    negation interacts with conjunction and disjunction.  The
    following law says that "the negation of a disjunction is the
    conjunction of the negations." There is a dual law
    [de_morgan_not_and_not] to which we will return at the end of this
    chapter. *)
Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  (* ADMITTED *)
  unfold not. intros P Q H. split.
  - intros HP. apply H. left. apply HP.
  - intros HQ. apply H. right. apply HQ.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX1? (not_S_inverse_pred) *)
(** Since we are working with natural numbers, we can disprove that
    [S] and [pred] are inverses of each other: *)
Lemma not_S_pred_n : ~(forall n : nat, S (pred n) = n).
Proof.
  (* ADMITTED *)
  intros H. specialize H with (n:=0). simpl in H. discriminate H.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)

(** TERSE: Since inequality involves a negation, getting comfortable
    with it also often requires a little practice.

    A useful trick: if you are trying to prove a nonsensical goal,
    apply [ex_falso_quodlibet] to change the goal to [False]. This
    makes it easier to use assumptions of the form [~P], and in
    particular of the form [x<>y]. *)

(** FULL: Since inequality involves a negation, it also requires a little
    practice to be able to work with it fluently.  Here is one useful
    trick.

    If you are trying to prove a goal that is nonsensical (e.g., the
    goal state is [false = true]), apply [ex_falso_quodlibet] to
    change the goal to [False].

    This makes it easier to use assumptions of the form [~P] that may
    be available in the context -- in particular, assumptions of the
    form [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
(* FOLD *)
Proof.
  intros b H. destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.
(* /FOLD *)

(* FULL *)
(** Since reasoning with [ex_falso_quodlibet] is quite common, Rocq
    provides a built-in tactic, [exfalso], for applying it. *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.             (* note implicit [destruct b] here! *)
  - (* b = true *)
    unfold not in H.
    exfalso.               (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.
(* /FULL *)

(* HIDE: CH: I don't think this was the original intention, but some
   of these quizzes got unnecessarily tricky and pedantic. For
   instance, the first quiz below makes a big distinction between
   using the destruct tactic and destructing using an intro pattern,
   even if conceptually there is no difference. Could it be that these
   quizzes were devised when intro patterns were not taught in the
   course and an update would be helpful now? Since I don't see the
   gain in tricking a majority of students in giving the "wrong"
   answer, even if it's a perfectly sensible one. *)

(* TERSE *)
(* LATER: There are probably too many of these particular quizzes... *)
(* QUIZ *)
(** To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?
[[
        forall X, forall a b : X, (a=b) /\ (a<>b) -> False.
]]
    (A) [destruct], [unfold], [left] and [right]

    (B) [destruct] and [unfold]

    (C) only [destruct]

    (D) [left] and/or [right]

    (E) only [unfold]

    (F) none of the above

*)
(* /QUIZ *)
(* FOLD *)
Lemma quiz1: forall X, forall a b : X, (a=b) /\ (a<>b) -> False.
Proof.
  intros X a b [Hab Hnab]. apply Hnab. apply Hab.
Qed.
(* /FOLD *)

(* QUIZ *)
(** To prove the following proposition, which tactics will we
    need besides [intros] and [apply]?
[[
        forall P Q : Prop,  P \/ Q -> ~~(P \/ Q).
]]
    (A) [destruct], [unfold], [left] and [right]

    (B) [destruct] and [unfold]

    (C) only [destruct]

    (D) [left] and/or [right]

    (E) only [unfold]

    (F) none of the above

*)
(* /QUIZ *)
(* FOLD *)
Lemma quiz2 : forall P Q : Prop,  P \/ Q -> ~~(P \/ Q).
Proof.
  intros P Q HPQ HnPQ. apply HnPQ in HPQ. apply HPQ.
Qed.
(* /FOLD *)

(* QUIZ *)
(** To prove the following proposition, which tactics will we
    need besides [intros] and [apply]?
[[
         forall P Q: Prop, P -> (P \/ ~~Q).
]]
    (A) [destruct], [unfold], [left] and [right]

    (B) [destruct] and [unfold]

    (C) only [destruct]

    (D) [left] and/or [right]

    (E) only [unfold]

    (F) none of the above

*)
(* /QUIZ *)
(* FOLD *)
Lemma quiz3 : forall P Q: Prop, P -> (P \/ ~~Q).
Proof.
intros P Q HP. left. apply HP.
Qed.
(* /FOLD *)

(* QUIZ *)
(** To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?
[[
         forall P Q: Prop,  P \/ Q -> ~~P \/ ~~Q.
]]
    (A) [destruct], [unfold], [left] and [right]

    (B) [destruct] and [unfold]

    (C) only [destruct]

    (D) [left] and/or [right]

    (E) only [unfold]

    (F) none of the above

*)
(* /QUIZ *)
(* FOLD *)
Lemma quiz4 : forall P Q: Prop,  P \/ Q -> ~~P \/ ~~Q.
Proof.
  intros P Q [HP | HQ].
  - (* left *)
    left. intros HnP. apply HnP in HP. apply HP.
  - (* right *)
    right. intros HnQ. apply HnQ in HQ. apply HQ.
Qed.
(* /FOLD *)

(* QUIZ *)
(** To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?
[[
         forall A : Prop, 1=0 -> (A \/ ~A).
]]
    (A) [discriminate], [unfold], [left] and [right]

    (B) [discriminate] and [unfold]

    (C) only [discriminate]

    (D) [left] and/or [right]

    (E) only [unfold]

    (F) none of the above

*)
(* /QUIZ *)
(* FOLD *)
Lemma quiz5 : forall A : Prop, 1=0 -> (A \/ ~A).
Proof.
  intros P H. discriminate H.
Qed.
(* /FOLD *)
(* /TERSE *)

(** ** Truth *)

(** Besides [False], Rocq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    constant [I : True], which is also defined in the standard
    library: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** Unlike [False], which is used extensively, [True] is used
    relatively rarely: it is trivial (and therefore uninteresting) to
    prove as a goal, and it provides no useful information when it
    appears as a hypothesis. *)

(* FULL *)
(** However, [True] can be quite useful when defining complex [Prop]s using
    conditionals or as a parameter to higher-order [Prop]s. We'll come back
    to this later.

    For now, let's take a look at how we can use [True] and [False] to
    achieve an effect similar to that of the [discriminate] tactic, without
    literally using [discriminate]. *)

(** Pattern-matching lets us do different things for different
    constructors.  If the result of applying two different
    constructors were hypothetically equal, then we could use [match]
    to convert an unprovable statement (like [False]) to one that is
    provable (like [True]). *)
(* SOONER: BCP 25: I find the previous sentence quite puzzling. *)

(* HIDE: BCP: Andrew and I both have concerns about this example being
   confusing. APT 21: I've tentatively added this back to full
   version, using a different inductive to try to minimize confusion
   between true/True, etc. *)

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n contra.
  assert (H : disc_fn O). { simpl. apply I. }
  rewrite contra in H. simpl in H. apply H.
Qed.

(** To generalize this to other constructors, we simply have to provide an
    appropriate variant of [disc_fn]. To generalize it to other
    conclusions, we can use [exfalso] to replace them with [False].

    The built-in [discriminate] tactic takes care of all this for us. *)

(* EX2AM? (nil_is_not_cons) *)

(** Use the same technique as above to show that [nil <> x :: xs].
    Do not use the [discriminate] tactic. *)

(* QUIETSOLUTION *)
Definition is_nil {X : Type} (x : list X) : Prop :=
  match x with
  | nil => True
  | _ => False
  end.
(* /QUIETSOLUTION *)

Theorem nil_is_not_cons : forall X (x : X) (xs : list X), ~ (nil = x :: xs).
Proof.
  (* ADMITTED *)
  intros X x xs Heq.
  assert (@is_nil X []) as H.
  { simpl. apply I. }
  rewrite Heq in H. apply H.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** ** Logical Equivalence *)
Print "<->".
(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is simply the conjunction
    of two implications.
[[
      Print "<->".
]]
*)
(* ===>
     Notation "A <-> B" := (iff A B)

     iff = fun A B : Prop => (A -> B) /\ (B -> A)
         : Prop -> Prop -> Prop

     Argumments iff (A B)%type_scope  *)

(** TERSE: *** *)
Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKINCLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.
(* /WORKINCLASS *)
(* SOONER: The <- and -> notations in comments do not look the same in HTML. *)

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

(** TERSE: *** *)
(** TERSE: The [apply] tactic can also be used with [<->]. *)
(** FULL: We can also use [apply] with an [<->] in either direction,
    without explicitly thinking about the fact that it is really an
    [and] underneath. *)
(* HIDE: MRC, APT, and BCP had a discussion about these examples in
   02/22. They work because of how [apply] tries to match the goal,
   not because of setoids. The conversation can be found at
   https://github.com/DeepSpec/sfdev/pull/459. *)

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H HP. apply H. apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff H HQ. apply H. apply Hiff. apply HQ.
Qed.

(* TERSE: HIDEFROMHTML *)
(* EX1? (iff_properties) *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  (* ADMITTED *)
  intros P. split.
    - (* -> *) intros H. apply H.
    - (* <- *) intros H. apply H.  Qed.
(* /ADMITTED *)

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* ADMITTED *)
  intros P Q R HPQ HQR. split.
  - (* -> *) intro HP. apply HQR. apply HPQ. apply HP.
  - (* <- *) intro HR. apply HPQ. apply HQR. apply HR.
Qed.
(* /ADMITTED *)
(** [] *)
(* TERSE: /HIDEFROMHTML *)

(* FULL *)
(* EX3 (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* ADMITTED *)
  intros P Q R. split.
  - (* -> *)
    intros [HP | [HQ HR]].
    + split.
      * left. apply HP.
      * left. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.
  - (* <- *)
    intros [[HP1 | HQ] [HP2 | HR]].
    + left. apply HP1.
    + left. apply HP1.
    + left. apply HP2.
    + right. split.
      * apply HQ.
      * apply HR.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** ** Setoids and Logical Equivalence *)

(** Some of Rocq's tactics treat [iff] statements specially, avoiding some
    low-level proof-state manipulation.  In particular, [rewrite] and
    [reflexivity] can be used with [iff] statements, not just equalities.
    To enable this behavior, we have to import the Rocq library that
    supports it: *)
From Stdlib Require Import Setoids.Setoid.
(* HIDE: (mrc) It's confusing whether we really need to import the
   Setoid library. Basics.v in full mode already imported String,
   which caused Setoid to be loaded. But the terse version never
   imports String.  So commenting out the import above leaves full
   compiling but terse not compiling. Likewise, it's hard to discern
   the extent to which Setoid is used in future chapters. *)

(** FULL: A "setoid" is a set equipped with an equivalence relation -- that
    is, a relation that is reflexive, symmetric, and transitive.  When two
    elements of a set are equivalent according to the relation, [rewrite]
    can be used to replace one by the other.

    We've seen this already with the equality relation [=] in Rocq: when
    [x = y], we can use [rewrite] to replace [x] with [y] or vice-versa.

    Similarly, the logical equivalence relation [<->] is reflexive,
    symmetric, and transitive, so we can use it to replace one part of a
    proposition with another: if [P <-> Q], then we can use [rewrite] to
    replace [P] with [Q], or vice-versa. *)

(** TERSE: A "setoid" is a set equipped with an equivalence relation,
    such as [=] or [<->]. *)

(** TERSE: *** *)

(** Here is a simple example demonstrating how these tactics work with
    [iff].

    First, let's prove a couple of basic iff equivalences. (For these
    proofs we are not using setoids yet.) *)

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
(* FOLD *)
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.
(* /FOLD *)

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
(* FOLD *)
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.
(* /FOLD *)

(** We can now use these facts with [rewrite] and [reflexivity] to
    prove a ternary version of the [mult_eq_0] fact above _without_
    splitting the top-level iff: *)

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

(* SOONER: CH: An exercise would be nice here. *)

(* ############################################################ *)
(** ** Existential Quantification *)

(** FULL: Another fundamental logical connective is _existential
    quantification_. To say that there is some [x] of type [T] such
    that some property [P] holds of [x], we write [exists x : T, P].
    As with [forall], the type annotation [: T] can be omitted if Rocq
    is able to infer from the context what the type of [x] should be. *)

(** To prove a statement of the form [exists x, P], we must show that [P]
    holds for some specific choice for [x], known as the _witness_ of the
    existential.  This is done in two steps: First, we explicitly tell Rocq
    which witness [t] we have in mind by invoking the tactic [exists t].
    Then we prove that [P] holds after all occurrences of [x] are replaced
    by [t]. *)

(* HIDE: CH: Is there any way to tell coqdoc to not write applications of the
   exists tactic as unicode? Manually inserting HTML looks bad in .v version. *)

(* HIDE: BCP 19: (Out of date now!) It might have been a mistake to
   introduce this definition, since, in chapter IndProp and beyond, the
   word "even" is used for the inductive definition of evenness.  Maybe we
   could call this one "ev"? But then some of the theorem names in IndProp
   will be exactly backwards!  (As it is, they are confusing because, even
   further ago, this one (IIRC) used to be named "even" and the one in
   IndProp used to be named "ev", but "ev" no longer exists!) This is
   really a confusing state of affairs!  APT 20: Slightly rationalized now,
   to match standard library. *)
Definition Even x := exists n : nat, x = double n.
Check Even : nat -> Prop.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

(** TERSE: *** *)
(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKINCLASS *)
  intros n [m Hm]. (* note the implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.
(* /WORKINCLASS *)

(* FULL *)
(* EX1! (dist_not_exists) *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold."  (Hint: [destruct H as [x E]] works on
    existential assumptions!)  *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  (* ADMITTED *)
  intros X P H [x Hx].
  apply Hx. apply H. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: dist_not_exists *)
(** [] *)

(* EX2 (dist_exists_or) *)
(** FULL: Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* ADMITTED *)
  intros X P Q. split.
  - (* -> *) intros [x [HP | HQ]].
    + (* P x *) left. exists x. apply HP.
    + (* Q x *) right. exists x. apply HQ.
  - (* <- *) intros [[x Hx] | [x Hx]].
    + (* exists x, P x *)
      exists x. left. apply Hx.
    + (* exists x, Q x *)
      exists x. right. apply Hx.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: dist_exists_or *)
(** [] *)

(* EX3? (leb_plus_exists) *)
Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof.
(* ADMITTED *)
  induction n as [| n' IHn'].
  - intros m H. exists m. reflexivity.
  - intros m.
    destruct m eqn:HE.
    + intros H. discriminate H.
    + intros H. simpl in H.
      apply IHn' in H.
      destruct H as [x Hx].
      exists x.
      simpl.
      rewrite <- Hx.
      reflexivity.
Qed.
(* /ADMITTED *)

(* QUIETSOLUTION *)
Lemma leb_plus: forall n m, (n <=? n + m) = true.
Proof.
  induction n.
  - intros m.
    reflexivity.
  - intros m.
    simpl. apply IHn.
Qed.
(* /QUIETSOLUTION *)

Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  (* ADMITTED *)
  intros n m H.
  destruct H as [x Hx].
  rewrite Hx.
  apply leb_plus.
Qed.
(* /ADMITTED *)

(* HIDE *)
(* A direct proof without a lemma. *)
Theorem plus_exists_leb' : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  induction n as [ | k].
  - intros m [w Hw]. reflexivity.
  - intros m [w Hw]. destruct m as [ | j].
    -- simpl in Hw. discriminate.
    -- simpl. apply IHk. exists w.
       rewrite plus_Sn_m in Hw. injection Hw as Hj. assumption.
Qed.
(* /HIDE *)
(** [] *)
(* /FULL *)

(* TERSE *)
(* ############################################################ *)
(** ** Recap -- Logical connectives in Rocq *)

(** Basic connectives:
       - [and : Prop -> Prop -> Prop] (conjunction):
         - introduced with the [split] tactic
         - eliminated with [destruct H as [H1 H2]]
       - [or : Prop -> Prop -> Prop] (disjunction):
         - introduced with [left] and [right] tactics
         - eliminated with [destruct H as [H1 | H2]]
       - [False : Prop]
         - eliminated with [destruct H as []]
       - [True : Prop]
         - introduced with [apply I], but not as useful
       - [ex : forall A:Type, (A -> Prop) -> Prop] (existential)
         - introduced with [exists w]
         - eliminated with [destruct H as [x H]]

    Derived connectives:
       - [not : Prop -> Prop] (negation):
         - [not P] defined as [P -> False]
       - [iff : Prop -> Prop -> Prop] (logical equivalence):
         - [iff P Q] defined as [(P -> Q) /\ (Q -> P)]

    Fundamental connectives we've been using since the beginning:
       - equality ([e1 = e2])
       - implication ([P -> Q])
       - universal quantification ([forall x, P]) *)

(* HIDE: CH: Some quizzes would be nice for this recap, and there's
   plenty of material for that in prior exams. *)

(* /TERSE *)

(* #################################################################### *)
(** * Programming with Propositions *)

(** FULL: The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure: *)
(** TERSE: What does it mean to say that "an element [x] occurs in a
    list [l]"? *)
(**    - If [l] is the empty list, then [x] cannot occur in it, so the
         property "[x] appears in [l]" is simply false. *)
(**    - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
         occurs in [l] if it is equal to [x'] or it occurs in [l']. *)

(** We can translate this directly into a straightforward recursive
    function taking an element and a list and returning... a proposition! *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** TERSE: *** *)
(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKINCLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.
(* /WORKINCLASS *)

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKINCLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.
(** (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)
(* /WORKINCLASS *)

(** TERSE: *** *)

(** We can also reason about more generic statements involving [In]. *)

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
(* TERSE: FOLD *)
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.
(* TERSE: /FOLD *)

(** FULL: (Note here how [In] starts out applied to a variable and only
    gets expanded when we do case analysis on this variable.) *)

(* FULL *)
(** This way of defining propositions recursively is very convenient in
    some cases, less so in others.  In particular, it is subject to Rocq's
    usual restrictions regarding definitions of recursive functions,
    e.g., the requirement that they be "obviously terminating."

    In the next chapter, we will see how to define propositions
    _inductively_ -- a different technique with its own strengths and
    limitations. *)

(* EX2 (In_map_iff) *)
Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|x l' IHl'].
    (* ADMITTED *)
    + (* l = nil, contradiction *)
      simpl. intros [].
    + (* l = x :: l' *)
      simpl. intros [H | H].
      * exists x. split.
        { apply H. }
        { left. reflexivity. }
      * apply IHl' in H.
        destruct H as [x' [H1 H2]].
        exists x'. split.
        { apply H1. }
        { right. apply H2. }
  - intros [x [H1 H2]]. rewrite <- H1.
    apply In_map. apply H2.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2 (In_app_iff) *)
(* LATER: The CIS500 exam in Fall 2020 included an informal proof of
   this.  We might want to turn it into a(n optional) exercise. *)
Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  (* ADMITTED *)
  - intros l' a. simpl. split.
    + intros H. right. apply H.
    + intros [[]|H]. apply H.
  - intros l'' a. simpl. rewrite IH. rewrite or_assoc.
    reflexivity. Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* FULL *)
(* EX3! (All) *)
(** We noted above that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] says that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)
(* HIDE: APT: The standard library calls this Forall, but defines it
   as an inductive.  It is used in VFA. *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  (* ADMITDEF *) :=
  match l with
  | [] => True
  | x :: l' => P x /\ All P l'
  end.
(* /ADMITDEF *)

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  (* ADMITTED *)
  intros T P l.
  induction l as [|x l IHl].
  - simpl. split.
    + intros _. apply I.
    + intros _ x [].
  - simpl. rewrite <- IHl. split.
    + intros H. split.
      * apply H. left. reflexivity.
      * intros x' Hx'. apply H. right.
        apply Hx'.
    + intros [Hx H] x' [Hxx'|Hl].
      * rewrite <- Hxx'. apply Hx.
      * apply H. apply Hl.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: All_In *)
(** [] *)

(* EX2? (combine_odd_even) *)
(** Complete the definition of [combine_odd_even] below.  It takes as
    arguments two properties of numbers, [Podd] and [Peven], and it should
    return a property [P] such that [P n] is equivalent to [Podd n] when
    [n] is [odd] and equivalent to [Peven n] otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  (* ADMITDEF *) :=
  fun n => if odd n then Podd n else Peven n.
  (* /ADMITDEF *)

(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* ADMITTED *)
  intros Podd Peven n Hodd Heven.
  unfold combine_odd_even.
  destruct (odd n) eqn:HE.
  - (* oddn n = true *)
    apply Hodd. reflexivity.
  - (* oddn n = false *)
    apply Heven. reflexivity. Qed.
(* /ADMITTED *)

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  (* ADMITTED *)
  unfold combine_odd_even.
  intros Podd Peven n H Hodd.
  destruct (odd n) eqn:HE.
  - (* odd n = true *)
    apply H.
  - (* odd n = false *)
    discriminate Hodd. Qed.
(* /ADMITTED *)

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  (* ADMITTED *)
  unfold combine_odd_even.
  intros Podd Peven n H Heven.
  destruct (odd n) eqn:HE.
  - (* odd n = true *)
    discriminate Heven.
  - (* odd n = false *)
    apply H. Qed.
(* /ADMITTED *)
(** [] *)

(* HIDE *)
(* CH: Here is a definition that makes the proofs above quite trivial.
   I thought that this is what the exercise asked for, and only
   became suspicious when my proofs were all quite trivial. *)
Definition combine_odd_even' (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => (odd n = true -> Podd n) /\ (odd n = false -> Peven n).

Theorem combine_odd_even_intro' :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even' Podd Peven n.
Proof.
  intros Podd Peven n Hodd Heven. split. { apply Hodd. } { apply Heven. }
Qed.

Theorem combine_odd_even_elim_odd' :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even' Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n [Hodd Heven]. apply Hodd.
Qed.

Theorem combine_odd_even_elim_even' :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even' Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros Podd Peven n [Hodd Heven]. apply Heven.
Qed.
(* /HIDE *)
(* /FULL *)

(* #################################################################### *)
(** * Applying Theorems to Arguments *)

(** FULL: One feature that distinguishes Rocq from some other popular proof
    assistants (e.g., ACL2 and Isabelle) is that it treats _proofs_ as
    first-class objects.

    There is a great deal to be said about this, but it is not necessary to
    understand it all in order to use Rocq.  This section gives just a
    taste, leaving a deeper exploration for the optional chapters
    [ProofObjects] and [IndPrinciples]. *)
(** TERSE: Rocq also treats _proofs_ as first-class objects! *)

(** We have seen that we can use [Check] to ask Rocq to check whether
    an expression has a given type: *)

Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.

(** We can also use it to check what theorem a particular identifier
    refers to: *)

Check add_comm        : forall n m : nat, n + m = m + n.
Check plus_id_example : forall n m : nat, n = m -> n + n = m + m.

(** Rocq checks the _statements_ of the [add_comm] and
    [plus_id_example] theorems in the same way that it checks the
    _type_ of any term (e.g., plus). If we leave off the colon and
    type, Rocq will print these types for us.

    Why? *)

(** TERSE: *** *)
(** The reason is that the identifier [add_comm] actually refers to a
    _proof object_ -- a logical derivation establishing the truth of the
    statement [forall n m : nat, n + m = m + n].  The type of this object
    is the proposition that it is a proof of. *)
(** TERSE: *** *)
(** The type of an ordinary function tells us what we can do with it.
       - If we have a term of type [nat -> nat -> nat], we can give it two
         [nat]s as arguments and get a [nat] back.

    Similarly, the statement of a theorem tells us what we can use that
    theorem for.
       - If we have a term of type [forall n m, n = m -> n + n = m + m] and we
         provide it two numbers [n] and [m] and a third "argument" of type
         [n = m], we get back a proof object of type [n + n = m + m]. *)

(** FULL: Operationally, this analogy goes even further: by applying a
    theorem as if it were a function, i.e., applying it to values and
    hypotheses with matching types, we can specialize its result
    without having to resort to intermediate assertions.  For example,
    suppose we wanted to prove the following result: *)
(** TERSE: *** *)
(** TERSE: Rocq actually allows us to _apply_ a theorem as if it were a
    function.

    This is often handy in proof scripts -- e.g., suppose we want too
    prove the following: *)

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.

(** It appears at first sight that we ought to be able to prove this by
    rewriting with [add_comm] twice to make the two sides match.  The
    problem is that the second [rewrite] will undo the effect of the
    first. *)

Proof.
  intros x y z.
  rewrite add_comm.
  rewrite add_comm.
  (* We are back where we started... *)
Abort.

(* FULL *)
(** We encountered similar issues back in \CHAP{Induction}, and we saw
    one way to work around them by using [assert] to derive a specialized
    version of [add_comm] that can be used to rewrite exactly where we
    want. *)

Lemma add_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  assert (H : y + z = z + y).
    { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.
(* /FULL *)

(** FULL: A more elegant alternative is to apply [add_comm] directly
    to the arguments we want to instantiate it with, in much the same
    way as we apply a polymorphic function to a type argument. *)
(** TERSE: *** *)
(** TERSE: We can fix this by applying [add_comm] to the arguments we want
    it be to instantiated with.  Then the [rewrite] is forced to happen
    exactly where we want it. *)

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

(* FULL *)
(** If we really wanted, we could in fact do it for both rewrites. *)

Lemma add_comm3_take4 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite (add_comm x (y + z)).
  rewrite (add_comm y z).
  reflexivity.
Qed.
(* /FULL *)

(** TERSE: *** *)
(** Here's another example of using a theorem about lists like
    a function.  Suppose we have proved the following simple fact
    about lists... *)

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
(* FOLD *)
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.
(* /FOLD *)

(** FULL: (I.e., if a list [l] contains some element [x], then [l]
    must be nonempty.) *)

(** Note that one quantified variable ([x]) does not appear in
    the conclusion ([l <> []]). *)

(** Intuitively, we should be able to use this theorem to prove the special
    case where [x] is [42]. However, simply invoking the tactic [apply
    in_not_nil] will fail because it cannot infer the value of [x]. *)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

(** TERSE: *** *)
(** There are several ways to work around this: *)

(** We can use [apply ... with ...]: *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(** TERSE: *** *)
(** Or we can use [apply ... in ...]: *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(** TERSE: *** *)
(** Or -- this is the new one -- we can explicitly
    apply the lemma to the value [42] for [x]: *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(** TERSE: *** *)
(** We can also explicitly apply the lemma to a hypothesis,
    causing the values of the other parameters to be inferred: *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

(* HIDE *)
    (** TERSE: *** *)
    (* SOONER: BCP: Not sure what this comment means.  Also, I worry that
      this example gets in the way between the previous example and
      the discussion below. *)
    (** apply like induction tactic can benefit from modest introse *)
    Lemma in_not_nil_42_modest :
      forall l : list nat, In 42 l -> l <> [].
    Proof.
      intros l.
      apply in_not_nil.
    Qed.
(* /HIDE *)

(* FULL *)
(** You can "use a theorem as a function" in this way with almost any
    tactic that can take a theorem's name as an argument.

    Note, also, that theorem application uses the same inference
    mechanisms as function application; thus, it is possible, for
    example, to supply wildcards as arguments to be inferred, or to
    declare some hypotheses to a theorem as implicit by default.
    These features are illustrated in the proof below. (The details of
    how this proof works are not critical -- the goal here is just to
    illustrate applying theorems to arguments.) *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** We will see many more examples in later chapters. *)
(* /FULL *)

(* HIDEFROMADVANCED *)
(* TERSE *)

(* HIDE *)
Section FunctionTheoremQuiz.
(* /HIDE *)

(* HIDEFROMHTML *)
Lemma quiz : forall a b : nat,
  a = b -> b = 42 ->
  (forall (X : Type) (n m o : X),
          n = m -> m = o -> n = o) ->
  True.
Proof.
  intros a b H1 H2 trans_eq.

(* /HIDEFROMHTML *)
(* QUIZ *)
(** Suppose we have
[[
      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o
]]
    What is the type of this "proof object"?
[[
      trans_eq nat a b 42 H1 H2
]]

    (A) [a = b]

    (B) [42 = a]

    (C) [a = 42]

    (D) Does not typecheck











 *)
(* FOLD *)
Check trans_eq nat a b 42 H1 H2
  : a = 42.
(* /FOLD *)



(* /QUIZ *)

(* QUIZ *)
(** Suppose, again, that we have
[[
      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o
]]
    What is the type of this proof object?
[[
      trans_eq nat _ _ _ H1 H2
]]

    (A) [a = b]

    (B) [42 = a]

    (C) [a = 42]

    (D) Does not typecheck







 *)
(* FOLD *)
Check trans_eq nat _ _ _ H1 H2
  : a = 42.
(* /FOLD *)



(* /QUIZ *)

(* QUIZ *)
(* SOONER: BCP 25: Not sure whether the rest of these quizzes are useful
   enough to justify explaining them in class. *)
(** Suppose, again, that we have
[[
      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o
]]
    What is the type of this proof object?
[[
      trans_eq nat b 42 a H2
]]

    (A) [b = a]

    (B) [b = a -> 42 = a]

    (C) [42 = a -> b = a]

    (D) Does not typecheck







 *)
(* FOLD *)
Check trans_eq nat b 42 a H2
    : 42 = a -> b = a.
(* /FOLD *)



(* /QUIZ *)

(* QUIZ *)
(** Suppose, again, that we have
[[
      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o
]]
    What is the type of this proof object?
[[
      trans_eq _ 42 a b
]]

    (A) [a = b -> b = 42 -> a = 42]

    (B) [42 = a -> a = b -> 42 = b]

    (C) [a = 42 -> 42 = b -> a = b]

    (D) Does not typecheck







 *)
(* FOLD *)
Check trans_eq _ 42 a b
    : 42 = a -> a = b -> 42 = b.
(* /FOLD *)



(* /QUIZ *)

(* QUIZ *)
(** Suppose, again, that we have
[[
      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o
]]
    What is the type of this proof object?
[[
      trans_eq _ _ _ _ H2 H1
]]

    (A) [b = a]

    (B) [42 = a]

    (C) [a = 42]

    (D) Does not typecheck








 *)
(* FOLD *)
Fail Check trans_eq _ _ _ _ H2 H1.
(* /FOLD *)
(* /QUIZ *)

(* HIDE *)
    (* HIDE: (mrc) per BCP comment above, I'm hiding these quizzes.
       They involve existential variables, which is a concept that has
       not yet been explained. *)
    (* QUIZ *)
    (** What is the type of this proof object?

          [trans_eq _ _ _ _ H1]

        (A) [a = 42]

        (B) [b = 42 -> a = 42]

        (C) [a = 42 -> b = 42]

        (D) Does not typecheck

     *)
    (* FOLD *)
    (* INSTRUCTORS: Existential variables make this a bit awkward,
       but if we ignore them, then that doesn't typecheck. *)
    Check trans_eq _ _ _ _ H1.
    (* /FOLD *)
    (* /QUIZ *)

    (* QUIZ *)
    (** What is the type of this proof object?

          [trans_eq nat 42 a b _ H1]

        (A) [a = 42]

        (B) [42 = b]

        (C) [42 = a -> 42 = b]

        (D) Does not typecheck

     *)
    (* FOLD *)
    Check trans_eq nat 42 a b _ H1.
    Check (fun H => trans_eq nat 42 a b H H1).
    (* /FOLD *)
    (* /QUIZ *)
(* /HIDE *)
(* HIDEFROMHTML *)
Abort.
(* /HIDEFROMHTML *)

(* HIDE *)
End FunctionTheoremQuiz.
(* /HIDE *)
(* /TERSE *)
(* /HIDEFROMADVANCED *)

(* #################################################################### *)
(** * Working with Decidable Properties *)

(** We've seen two different ways of expressing logical claims in Rocq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    Here are the key differences between [bool] and [Prop]:
<<
                                           bool     Prop
                                           ====     ====
           decidable?                      yes       no
           useable with match?             yes       no
           works with rewrite tactic?      no        yes
>>
*)

(** FULL: The crucial difference between the two worlds is _decidability_.
    Every (closed) Rocq expression of type [bool] can be simplified in a
    finite number of steps to either [true] or [false] -- i.e., there is a
    terminating mechanical procedure for deciding whether or not it is
    [true].

    This means that, for example, the type [nat -> bool] is inhabited only
    by functions that, given a [nat], always yield either [true] or [false]
    in finite time; and this, in turn, means (by a standard computability
    argument) that there is _no_ function in [nat -> bool] that checks
    whether a given number is the code of a terminating Turing machine.

    By contrast, the type [Prop] includes both decidable and undecidable
    mathematical propositions; in particular, the type [nat -> Prop] does
    contain functions representing properties like "the nth Turing machine
    halts."

    The second row in the table follows directly from this essential
    difference.  To evaluate a pattern match (or conditional) on a boolean,
    we need to know whether the scrutinee evaluates to [true] or [false];
    this only works for [bool], not [Prop].

    The third row highlights an important practical difference:
    equality functions like [eqb_nat] that return a boolean cannot be
    used directly to justify rewriting with the [rewrite] tactic;
    propositional equality is required for this. *)

(** TERSE: Since every function terminates on all inputs in Rocq, a function
    of type [nat -> bool] is a _decision procedure_ -- i.e., it yields
    [true] or [false] on all inputs.

      - For example, [even : nat -> bool] is a decision procedure for the
        property "is even". *)

(** TERSE: *** *)
(** TERSE: It follows that there are some properties of numbers that we _cannot_
    express as functions of type [nat -> bool].

      - For example, the property "is the code of a halting Turing machine"
        is undecidable, so there is no way to write it as a function of
        type [nat -> bool].

    On the other hand, [nat->Prop] is the type of _all_ properties of
    numbers that can be expressed in Rocq's logic, including both decidable
    and undecidable ones.

      - For example, "is the code of a halting Turing machine" is a
        perfectly legitimate mathematical property, and we can absolutely
        represent it as a Rocq expression of type [nat -> Prop].
*)
(* LATER: Comment from Arthur C: For converting from "eqb_nat x y =
   true" to "x = y", I have been using autorewrite, wrapped in a
   tactic (you could name it "rew_eqb"), that avoids cluttering proof
   scripts with, e.g., [rewrite String.eqb_eq].

   Moreover, as you wish to use this tactic "rew_eqb" pretty much
   everytime after a case analysis, I set up the tactic [case_if] to
   automatically call it as a postprocessing. The overall result is as
   follows: on a goal [if eqb_nat x y then foo else bar], you call
   [case_if], and you get one goal with [x = y |- foo] and the other
   one [x <> y |- bar]. Exactly what you'd expect. In just a single
   tactic, which requires no arguments.

   BCP 19: Wonder if this would be a good candidate for a little
   example in Auto.v... (Putting it in this chapter seems premature.)
   BCP 25: We'd need to explain autorewrite, though. *)

(** TERSE: *** *)

(** Since [Prop] includes _both_ decidable and undecidable properties, we
    have two options when we want to formalize a property that happens to
    be decidable: we can express it either as a boolean computation or as a
    function into [Prop]. *)

(** TERSE: For instance, to claim that a number [n] is even, we can say
    either that [even n] evaluates to [true]... *)
Example even_42_bool : even 42 = true.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** ... or that there exists some [k] such that [n = double k]. *)
Example even_42_prop : Even 42.
(* FOLD *)
Proof. unfold Even. exists 21. reflexivity. Qed.
(* /FOLD *)

(** Of course, it would be deeply strange if these two
    characterizations of evenness did not describe the same set of
    natural numbers!

    Fortunately, they do! *)

(* TERSE: HIDEFROMHTML *)

(** To prove this, we first need two helper lemmas. *)

Lemma even_double : forall k, even (double k) = true.
(* FOLD *)
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.
(* /FOLD *)

(* FULL *)
(* EX3 (even_double_conv) *)
(* /FULL *)
Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
(* FOLD *)
Proof.
  (* Hint: Use the [even_S] lemma from [Induction.v]. *)
  (* ADMITTED *)
  intros n. induction n as [|n' [k Hk]].
  - simpl. exists 0. reflexivity.
  - rewrite even_S. destruct (even n') eqn:HE.
    + simpl. exists k. rewrite Hk. reflexivity.
    + simpl. exists (S k). rewrite Hk. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** Now the main theorem: *)

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
(* FOLD *)
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.
(* /FOLD *)

(** In view of this theorem, we can say that the boolean computation
    [even n] is _reflected_ in the truth of the proposition
    [exists k, n = double k]. *)
(* HIDE: Andrew Appel, Arthur Azevedo, and BCP had a long discussion
   about the terminology here, leading to the present wording. BCP has
   it all saved in an email chain with subject "reflects is not
   symmetric" if anybody wants to see it later... *)

(* HIDE *)
      (* LATER: BCP: An experiment... *)

      (** Similarly, we can can state what it means for a number to be
          positive in two different ways: *)

      Definition Positive (n:nat) := exists m, n = S m.

      Definition positive (n:nat) := negb (eqb n 0).

      Theorem positive_bool_prop : forall n,
        positive n = true <-> Positive n.
      Proof.
        (* WORKINCLASS *)
        intros n.
        unfold Positive. unfold positive.
        split.
        - intros H. destruct n.
          * simpl in H. discriminate H.
          * exists n. reflexivity.
        - Admitted.
      (* /WORKINCLASS *)
(* /HIDE *)

(** TERSE: *** *)
(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either
      - (1) that [n =? m] returns [true], or
      - (2) that [n = m].
    Again, these two notions are equivalent: *)

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
(* FOLD *)
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.
(* /FOLD *)

(* HIDEFROMADVANCED *)
(** TERSE: *** *)

(** So what should we do in situations where some claim could be
    formalized as either a proposition or a boolean computation? Which
    should we choose?

    In general, _both_ can be useful. *)

(* HIDE: BCP 23: The next point might be useful (or maybe it is not,
   really?), but it gets in the way right here.  I'm going to delete it for
   now and see if anybody screams. :-) *)
(* HIDE *)
    (** FULL: In the case of even numbers above, when proving the backwards
        direction of [even_bool_prop] (i.e., [even_double], going from the
        propositional to the boolean claim), we used a simple induction on [k].

        On the other hand, the converse (the [even_double_conv] exercise)
        required a clever generalization, since we can't directly prove
        [(even n = true) -> Even n]. *)
(* /HIDE *)

(** For example, booleans are more useful for defining functions.
    There is no effective way to _test_ whether or not a [Prop] is
    true, so we cannot use [Prop]s in conditional expressions. The
    following definition is rejected: *)

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** FULL: Rocq complains that [n = 2] has type [Prop], while it expects an
    element of [bool] (or some other inductive type with two constructors).
    This has to do with the _computational_ nature of Rocq's core language,
    which is designed so that every function it can express is computable
    and total. (One reason for this is to allow the extraction of
    executable programs from Rocq developments.) As a consequence, [Prop] in
    Rocq does _not_ have a universal case analysis operation telling whether
    any given proposition is true or false, since such an operation would
    allow us to write non-computable functions.  *)

(** Rather, we have to state this definition using a boolean equality
    test. *)

Definition is_even_prime n :=
  if n =? 2 then true
  else false.

(** FULL: Beyond the fact that non-computable properties are impossible in
    general to phrase as boolean computations, even many _computable_
    properties are easier to express using [Prop] than [bool], since
    recursive function definitions in Rocq are subject to significant
    restrictions.  For instance, the next chapter shows how to define the
    property that a regular expression matches a given string using [Prop].
    Doing the same with [bool] would amount to writing a regular expression
    matching algorithm, which would be more complicated, harder to
    understand, and harder to reason about than a simple (non-algorithmic)
    definition of this property.

    Conversely, an important side benefit of stating facts using booleans
    is enabling some proof automation through computation with Rocq terms, a
    technique known as _proof by reflection_.

    Consider the following statement: *)
(* /HIDEFROMADVANCED *)
(** TERSE: *** *)
(** TERSE: More generally, stating facts using booleans can often enable
    effective proof automation through computation with Rocq terms, a
    technique known as _proof by reflection_.

    Consider the following statement: *)

(* HIDE: CH: [In] would be better than [Even] for illustrating reflection? *)

Example even_1000 : Even 1000.

(** The most direct way to prove this is to give the value of [k]
    explicitly. *)

Proof. unfold Even. exists 500. reflexivity. Qed.

(** The proof of the corresponding boolean statement is simpler, because we
    don't have to invent the witness [500]: Rocq's computation mechanism
    does it for us! *)

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

(** TERSE: *** *)
(** Now, the useful observation is that, since the two notions are
    equivalent, we can use the boolean formulation to prove the other one
    without mentioning the value 500 explicitly: *)

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof-script
    line count in this case, larger proofs can often be made considerably
    simpler by the use of reflection.  As an extreme example, a famous
    Rocq proof of the even more famous _4-color theorem_ uses
    reflection to reduce the analysis of hundreds of different cases
    to a boolean computation. *)

(** TERSE: *** *)

(** Another advantage of booleans is that the _negation_ of a claim
    about booleans is straightforward to state and (when true) prove:
    simply flip the expected boolean result. *)

Example not_even_1001 : even 1001 = false.
Proof.
  reflexivity.
Qed.

(** TERSE: *** *)
(** In contrast, propositional negation can be difficult to work with
    directly.

    For example, suppose we state the non-evenness of [1001]
    propositionally: *)

Example not_even_1001' : ~(Even 1001).

(** Proving this directly -- by assuming that there is some [n] such that
    [1001 = double n] and then somehow reasoning to a contradiction --
    would be rather complicated.

    But if we convert it to a claim about the boolean [even] function, we
    can let Rocq do the work for us. *)

Proof.
  (* WORKINCLASS *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.
(* /WORKINCLASS *)

(** TERSE: *** *)

(** Conversely, there are situations where it can be easier to work
    with propositions rather than booleans.

    In particular, knowing that [(n =? m) = true] is generally of
    little direct help in the middle of a proof involving [n] and [m].
    But if we convert the statement to the equivalent form [n = m],
    then we can easily [rewrite] with it. *)

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKINCLASS *)
  intros n m p H.
(* HIDE *)
  Fail rewrite H.
(* /HIDE *)
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.
(* /WORKINCLASS *)

(** FULL: We won't discuss reflection any further for the moment, but
    it serves as a good example showing the different strengths of
    booleans and general propositions. *)

(** Being able to cross back and forth between the boolean and
    propositional worlds will often be convenient in later chapters. *)

(* FULL *)
(* EX2 (logical_connectives) *)
(** The following theorems relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)

Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* ADMITTED *)
  intros [].
  - simpl. intros b2. split.
    + intros H. split.
      * reflexivity.
      * apply H.
    + intros [_ H]. apply H.
  - simpl. intros b2. split.
    + intros H. discriminate H.
    + intros [H _]. discriminate H.  Qed.
(* /ADMITTED *)

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* ADMITTED *)
  intros [].
  - simpl. intros b2. split.
    + intros _. left. reflexivity.
    + intros _. reflexivity.
  - simpl. intros [].
    + split.
      * intros _. right. reflexivity.
      * intros _. reflexivity.
    + split.
      * intros H. discriminate H.
      * intros [H | H].
        { apply H. }
        { apply H. }  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: andb_true_iff *)
(* GRADE_THEOREM 1: orb_true_iff *)
(** [] *)

(* EX1 (eqb_neq) *)
(** The following theorem is an alternate "negative" formulation of
    [eqb_eq] that is more convenient in certain situations.  (We'll see
    examples in later chapters.)  Hint: [not_true_iff_false]. *)

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  (* ADMITTED *)
  intros x y. rewrite <- not_true_iff_false. rewrite eqb_eq.
  reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (eqb_list) *)
(** Given a boolean operator [eqb] for testing equality of elements of
    some type [A], we can define a function [eqb_list] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [eqb_list] function below.  To make sure that your
    definition is correct, prove the lemma [eqb_list_true_iff]. *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool
  (* ADMITDEF *) :=
  match l1, l2 with
  | [], [] => true
  | a1 :: l1, a2 :: l2 => eqb a1 a2 && eqb_list eqb l1 l2
  | _, _ => false
  end.
(* /ADMITDEF *)

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
(* ADMITTED *)
  intros A eqb Heqb l1.
  induction l1 as [|a1 l1 IH].
  - intros [|a2 l2].
    + split.
      * intros H. reflexivity.
      * intros H. reflexivity.
    + simpl. split.
      * intros contra. discriminate contra.
      * intros contra. discriminate contra.
  - intros [|a2 l2].
    + simpl. split.
      * intros contra. discriminate contra.
      * intros contra. discriminate contra.
    + simpl.
      rewrite andb_true_iff, Heqb, IH.
      split.
      * intros [H1 H2].
        rewrite H1, H2.
        reflexivity.
      * intros H. injection H as H1 H2.
        { split.
          - apply H1.
          - apply H2. }
Qed.
(* /ADMITTED *)

(* GRADE_THEOREM 3: eqb_list_true_iff *)
(** [] *)
(* /FULL *)

(* FULL *)
(* EX2! (All_forallb) *)
(** Prove the theorem below, which relates [forallb], from the
    exercise [forall_exists_challenge] in chapter \CHAP{Tactics}, to
    the [All] property defined above. *)

(** Copy the definition of [forallb] from your \CHAP{Tactics} here
    so that this file can be graded on its own. *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
  (* ADMITDEF *) :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.
(* /ADMITDEF *)

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* ADMITTED *)
  intros X test l.
  induction l as [|x l' IHl'].
  - (* l = [] *)
    simpl. split.
    + intros _. split.
    + intros _. reflexivity.
  - (* l = x :: l' *)
    simpl.
    rewrite andb_true_iff. rewrite IHl'.
    reflexivity. Qed.
(* /ADMITTED *)

(** (Ungraded thought question) Are there any important properties of
    the function [forallb] which are not captured by this
    specification? *)

(* SOLUTION *)
(* This theorem exactly captures the input-output behaviour of
   [forallb]. However, it does not say anything about the running
   time. *)
(* /SOLUTION *)
(* GRADE_THEOREM 2: forallb_true_iff *)
(** [] *)
(* /FULL *)

(* #################################################################### *)
(** * The Logic of Rocq *)

(** FULL: Rocq's logical core, the _Calculus of Inductive
    Constructions_, differs in some important ways from other formal
    systems that are used by mathematicians to write down precise and
    rigorous definitions and proofs -- in particular from
    Zermelo-Fraenkel Set Theory (ZFC), the most popular foundation for
    paper-and-pencil mathematics.

    We conclude this chapter with a brief discussion of some of the
    most significant differences between these two worlds. *)
(** TERSE: Rocq's logical core, the _Calculus of Inductive Constructions_,
    is a "metalanguage for mathematics" in the same sense as familiar
    foundations for paper-and-pencil math, like Zermelo-Fraenkel Set
    Theory (ZFC).

    Mostly, the differences are not too important, but a few points are
    useful to understand. *)

(** ** Functional Extensionality *)

(* HIDEFROMADVANCED *)
(** Rocq's logic is quite minimalistic.  This means that one occasionally
    encounters cases where translating standard mathematical reasoning into
    Rocq is cumbersome -- or even impossible -- unless we enrich its core
    logic with additional axioms. *)

(** FULL: For example, the equality assertions that we have seen so far
    mostly have concerned elements of inductive types ([nat], [bool],
    etc.).  But, since Rocq's equality operator is polymorphic, we can use
    it at _any_ type -- in particular, we can write propositions claiming
    that two _functions_ are equal to each other: *)
(** TERSE: A first instance has to do with equality of functions. *)
(** In certain cases Rocq can successfully prove equality propositions stating
    that two _functions_ are equal to each other: **)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** This works when Rocq can simplify the functions to the same expression,
    but this doesn't always happen. **)
(* /HIDEFROMADVANCED *)

(** TERSE: *** *)
(** These two functions are equal just by simplification, but in general
    functions can be equal for more interesting reasons.

    In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same output on every input:
[[
    (forall x, f x = g x) -> f = g
]]
    This is known as the principle of _functional extensionality_. *)

(* FULL *)
(** (Informally, an "extensional" property is one that pertains to an
    object's observable behavior.  Thus, functional extensionality
    simply means that a function's identity is completely determined
    by what we can observe from it -- i.e., the results we obtain
    after applying it.) *)
(* /FULL *)

(** However, functional extensionality is not part of Rocq's built-in logic.
    This means that some intuitively obvious propositions are not
    provable. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  Fail reflexivity. Fail rewrite add_comm.
  (* Stuck *)
Abort.

(** TERSE: *** *)
(** However, if we like, we can add functional extensionality to Rocq
    using the [Axiom] command. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Defining something as an [Axiom] has the same effect as stating a
    theorem and skipping its proof using [Admitted], but it alerts the
    reader that this isn't just something we're going to come back and
    fill in later! *)

(** TERSE: *** *)
(** We can now invoke functional extensionality in proofs: *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

(** TERSE: *** *)
(** Naturally, we need to be quite careful when adding new axioms into
    Rocq's logic, as this can render it _inconsistent_ -- that is, it may
    become possible to prove every proposition, including [False], [2+2=5],
    etc.!

    In general, there is no simple way of telling whether an axiom is safe
    to add: hard work by highly trained mathematicians is often required to
    establish the consistency of any particular combination of axioms.

    Fortunately, it is known that adding functional extensionality, in
    particular, _is_ consistent. *)

(** TERSE: *** *)
(** To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command:
[[
      Print Assumptions function_equality_ex2.
]]
*)
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)
(** FULL: (If you try this yourself, you may also see [add_comm] listed as
    an assumption, depending on whether the copy of [Tactics.v] in the
    local directory has the proof of [add_comm] filled in.) *)

(* HIDE *)
(* QUIZ *)
(** Is the following statement provable by just [reflexivity], without
    [functional_extensionality]?

      [(fun xs => 1 :: xs) = (fun xs => [1] ++ xs)]

    (A) Yes

    (B) No

 *)
(* FOLD *)
Example cons_1_eq_ex : (fun xs => 1 :: xs) = (fun xs => [1] ++ xs).
Proof. reflexivity. Qed.
(* /FOLD *)
(* /QUIZ *)
(* /HIDE *)

(* FULL *)
(* EX4 (tr_rev_correct) *)
(** One problem with the definition of the list-reversing function [rev]
    that we have is that it performs a call to [app] on each step.  Running
    [app] takes time asymptotically linear in the size of the list, which
    means that [rev] is asymptotically quadratic.

    We can improve this with the following two-argument definition: *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** This version of [rev] is said to be _tail recursive_, because the
    recursive call to the function is the last operation that needs to be
    performed (i.e., we don't have to execute [++] after the recursive
    call); a decent compiler will generate very efficient code in this
    case.

    Prove that the two definitions are indeed equivalent. *)
(* QUIETSOLUTION *)

Lemma rev_append_rev : forall X (l1 l2 : list X),
  rev_append l1 l2 = rev l1 ++ l2.
Proof.
  intros T l1. induction l1 as [|x l1' IHl1'].
  - intros acc. reflexivity.
  - intros acc. simpl. rewrite IHl1'. rewrite <- app_assoc.
    simpl. reflexivity.
Qed.

(* /QUIETSOLUTION *)
Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
(* ADMITTED *)
  intros X. apply functional_extensionality.
  intros l. unfold tr_rev.
  rewrite rev_append_rev. rewrite app_nil_r. reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** ** Classical vs. Constructive Logic *)

(** FULL: We have seen that it is not possible to test whether or not a
    proposition [P] holds while defining a Rocq function.  You may be
    surprised to learn that a similar restriction applies in _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Rocq: *)
(** TERSE: The following reasoning principle is _not_ derivable in
    Rocq (though, again, it can consistently be added as an axiom): *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** FULL: To understand operationally why this is the case, recall
    that, to prove a statement of the form [P \/ Q], we use the [left]
    and [right] tactics, which effectively require knowing which side
    of the disjunction holds.  But the universally quantified [P] in
    [excluded_middle] is an _arbitrary_ proposition, which we know
    nothing about.  We don't have enough information to choose which
    of [left] or [right] to apply. *)

(* FULL *)

(** However, in the special case where we happen to know that [P] is
    reflected in some boolean term [b], knowing whether it holds or
    not is trivial: we just have to check the value of [b]. *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

(** In particular, the excluded middle is valid for equations [n = m],
    between natural numbers [n] and [m]. *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(** Sadly, this trick only works for decidable propositions. *)

(* /FULL *)

(** FULL: It may seem strange that the general excluded middle is not
    available by default in Rocq, since it is a standard feature of familiar
    logics like ZFC.  But there is a distinct advantage in _not_ assuming
    the excluded middle: statements in Rocq make stronger claims than the
    analogous statements in standard mathematics.  Notably, a Rocq proof of
    [exists x, P x] always includes a particular value of [x] for which we
    can prove [P x] -- in other words, every proof of existence is
    _constructive_. *)

(** Logics like Rocq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    Logical systems such as ZFC, in which the excluded middle does
    hold for arbitrary propositions, are referred to as _classical_. *)

(* FULL *)
(** The following example illustrates why assuming the excluded middle may
    lead to non-constructive proofs:

    _Claim_: There exist irrational numbers [a] and [b] such that [a ^
    b] ([a] to the power [b]) is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is irrational.  So if
    [sqrt 2 ^ sqrt 2] is rational, it suffices to take [a = b = sqrt 2] and
    we are done.  Otherwise, [sqrt 2 ^ sqrt 2] is irrational.  In this
    case, we can take [a = sqrt 2 ^ sqrt 2] and [b = sqrt 2], since [a ^ b
    = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2].  []

    Do you see what happened here?  We used the excluded middle to
    consider separately the cases where [sqrt 2 ^ sqrt 2] is rational
    and where it is not, without knowing which one actually holds!
    Because of this, we finish the proof knowing that such [a] and [b]
    exist, but not being sure of their actual values.

    As useful as constructive logic is, it does have its limitations:
    There are many statements that can easily be proven in classical
    logic but that have only much more complicated constructive
    proofs, and there are some that are known to have no constructive
    proof at all!  Fortunately, like functional extensionality, the
    excluded middle is known to be compatible with Rocq's logic,
    allowing us to add it safely as an axiom. However, we will not
    need to do so here: the results that we cover in Software
    Foundations can be developed entirely within constructive logic at
    negligible extra cost.

    It takes some practice to understand which proof techniques must
    be avoided in constructive reasoning, but arguments by
    contradiction, in particular, are infamous for leading to
    non-constructive proofs. Here's a typical example: suppose that we
    want to show that there exists [x] with some property [P], i.e.,
    such that [P x].  We start by assuming that our conclusion is
    false; that is, [~ exists x, P x]. From this premise, it is not
    hard to derive [forall x, ~ P x].  If we manage to show that this
    results in a contradiction, we arrive at an existence proof
    without ever exhibiting a value of [x] for which [P x] holds!

    The technical flaw here, from a constructive standpoint, is that we
    claimed to prove [exists x, P x] using a proof of [~ ~ (exists x, P x)].
    Allowing ourselves to remove double negations from arbitrary
    statements is equivalent to assuming the excluded middle law, as shown
    in one of the exercises below.  Thus, this line of reasoning cannot be
    encoded in Rocq without assuming additional axioms. *)

(* EX3 (excluded_middle_irrefutable) *)
(** Proving the consistency of Rocq with the general excluded middle
    axiom requires complicated reasoning that cannot be carried out
    within Rocq itself.  However, the following theorem implies that it
    is always safe to assume a decidability axiom (i.e., an instance
    of excluded middle) for any _particular_ Prop [P].  Why?  Because
    the negation of such an axiom leads to a contradiction.  If [~ (P
    \/ ~P)] were provable, then by [de_morgan_not_or] as proved above,
    [P /\ ~P] would be provable, which would be a contradiction. So, it
    is safe to add [P \/ ~P] as an axiom for any particular [P].

    Succinctly: for any proposition P,
        [Rocq is consistent ==> Rocq + (P \/ ~P) is consistent]. *)

Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* ADMITTED *)
  intros P H.
  apply de_morgan_not_or in H. destruct H as [HNP HNNP].
  unfold not in HNP. unfold not in HNNP.
  apply HNNP. apply HNP.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3A (not_exists_dist) *)
(** It is a theorem of classical logic that the following two
    assertions are equivalent:
[[
    ~ (exists x, ~ P x)
    forall x, P x
]]
    The [dist_not_exists] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle. *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* ADMITTED *)
  intros Hem X P H x.
  destruct (Hem (P x)) as [HPx | HNPx].
  - (* P x *) apply HPx.
  - (* ~P x *)
    exfalso.
    apply H.
    exists x.
    apply HNPx.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX5? (classical_axioms) *)
(** For those who like a challenge, here is an exercise adapted from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following five statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Rocq, but we can consistently add any _one_ of them as an
    axiom if we wish to work in classical logic.

    To see this, prove that all six propositions (these five plus
    [excluded_middle]) are equivalent.

    Hint: Rather than considering all pairs of statements pairwise,
    prove a single circular chain of implications that connects them
    all. *)
(* LATER:
    This might benefit from an additional exercise
    to define `cyclic_implication` such that one could state
    `Theorem classical_axioms :
    cyclic_implication [excluded_middle; peirce;
    double_negation_elimination; de_morgan_not_and_not; implies_to_or]`. *)

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

Definition consequentia_mirabilis := forall P:Prop,
  (~P -> P) -> P.

(* SOLUTION *)
Theorem ito__em :
  implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or, excluded_middle.
  intros Hito P.
  apply or_commut.
  apply Hito.
  intros HP. apply HP.
Qed.

Theorem em__ito :
  excluded_middle -> implies_to_or.
Proof.
  unfold implies_to_or, excluded_middle.
  intros Hem P Q H.
  destruct (Hem P) as [HP | HNP].
  - (* P *) right. apply H. apply HP.
  - (* ~P *) left. apply HNP.
Qed.

Theorem em__demorgan :
  excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle, de_morgan_not_and_not.
  intros Hem P Q H.
  destruct (Hem P) as [HP | HNP].
  - (* P *)
    left. apply HP.
  - (* ~P *)
    destruct (Hem Q) as [HQ | HNQ].
    + (* Q *)
      right. apply HQ.
    + (* ~Q *)
      exfalso. apply H.
      split. apply HNP. apply HNQ.
Qed.

Theorem demorgan__em :
  de_morgan_not_and_not -> excluded_middle.
Proof.
  unfold de_morgan_not_and_not, excluded_middle.
  intros Hdm P.
  apply Hdm.
  unfold not. intros Hcontra.
  destruct Hcontra as [HNP HNNP].
  apply HNNP. apply HNP.
Qed.

Theorem em__dne :
  excluded_middle -> double_negation_elimination.
Proof.
  intros Hem P.
  destruct (Hem P) as [HP | HNP].
  - (* P *) intros H'. apply HP.
  - (* ~P *) intros H'. destruct (H' HNP).
Qed.

Theorem dne__demorgan :
  double_negation_elimination -> de_morgan_not_and_not.
Proof.
  intros Hc P Q H.
  apply Hc.
  intros H2.
  apply H.
  split.
  - (* left conjunct *) intros HP. apply H2. left. apply HP.
  - (* right conjunct *) intros HQ. apply H2. right. apply HQ.
Qed.

(** The above suffices (along with [demorgan__em]), but we can also
    prove it directly this way *)

Theorem dne__em :
  double_negation_elimination -> excluded_middle.
Proof.
  intros Hc P.
  apply Hc.
  apply excluded_middle_irrefutable.
Qed.

Theorem em__peirce :
  excluded_middle -> peirce.
Proof.
  intros Hem P Q H.
  destruct (Hem P) as [HP | HNP].
  - (* P *) apply HP.
  - (* ~P *)
    destruct (Hem (P -> Q)) as [HPQ | HNPQ].
    + (* P->Q *) apply H. apply HPQ.
    + (* ~(P->Q) *) assert (P -> Q) as HPQ.
      intros HP.
      exfalso.
      apply HNP. apply HP.
      apply H. apply HPQ.
Qed.

Theorem peirce__em :
  peirce -> excluded_middle.
Proof.
  intros Hp P.
  apply (Hp _ False).
  right.
  intros HP. apply H.
  left. apply HP.
Qed.

Theorem consequentia_mirabilis__dne :
  consequentia_mirabilis -> double_negation_elimination.
Proof.
  intros Hcm P HnnP.
  apply Hcm.
  intros HnP.
  destruct (HnnP HnP).
Qed.

Theorem dne__consequentia_mirabilis :
  double_negation_elimination -> consequentia_mirabilis.
Proof.
  intros Hdne P H.
  apply Hdne.
  intros HnP.
  destruct (HnP (H HnP)).
Qed.
(* /SOLUTION *)
(** [] *)
(* /FULL *)
