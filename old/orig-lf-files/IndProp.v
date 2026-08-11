(** * IndProp: Inductively Defined Propositions *)

(* INSTRUCTORS: In one 80-minute lecture, I (BCP) was able to get
   _to_, but not _through_, the proof of [in_re_match] in the regexp
   case study.  I covered the rest in an hour, going pretty slowly and
   working lots of examples in real time.  That left 20 minutes to
   show them just the first half of the ProofObjects chapter.

   Making time for at least a bit of discussion of ProofObjects is
   pretty important, even if you don't go into it in detail.  Entirely
   skipping this material leads to needless confusion and beating
   around the bush in later discussions.

*)
(* HIDE: BCP 25: After teaching the chapter this semester, I feel
   that (a) the ev example, while arguably suboptimal, actually works
   acceptably well. (I just wish that the n in [ev_SS n H] was not
   two smaller than the n that is being shown to be even -- that's
   always awkward.  Wonder if there is some clever way around that...)

   However, (b) the chapter is very long, and quite a
   few of the exercises are hard, especially if you do as I did this
   year and require the advanced exercises for everybody (on the
   assumption that they could get plenty of help from LLMs, etc.).  I
   think it really needs to be at least significantly trimmed, if not
   split up.
*)
(* HIDE: MRC 3/22: I offer a few remarks. I'm putting them here, above
   the BCP'21 comment, not to say that they are in any way more
   important; rather, just to preserve some chronological legibility.

   - This chapter is an outlier in length. It now has the maximum line
     length (in the FULL version) of any chapter in LF, at about 2300
     LoC. That's a z-score of about 1.75 for the "blue arrow" chapters
     in the dependency diagram.

   - This chapter has 39 exercises, of which 25 (!) are optional.

   - The running example of evenness is known to be uncompelling
     because it is representable without inductively-defined
     propositions. There do exist compelling examples:

     + Functions like [factorial] whose "natural" definitions are not
       structurally recursive. [Coq'Art 8.4]  [BCP 25: FWIW, I don't find
       the "natural" definition of factorial suitable for present purposes:
       the reasons it is better and more natural than a simple fixpoint
       seem rather subtle.]

     + Partial functions.

     + Relations (that are not strictly functions).

   I have a couple of personal opinions based on those observations:

   - I favor BCP'21's "path 1" of de-emphasizing (to the extent
     perhaps of eliminating) evenness.

   - I favor re-factoring this chapter into two files, with a main
     (blue) path that covers the essentials without cluttering
     optional exercises throughout the file.
 *)

(* HIDE: BCP '21: This chapter has been the subject of a lot of
   discussion over the past couple of years, with lots of people
   expressing dissatisfaction with the use of evenness as a main
   example.  In this revision, I have attempted a compromise: keeping
   evenness as the running example (because, aside from the
   artificiality of the example, it is pretty well polished) but
   preceding it with short discussions of several better-motivated
   examples.

   I'm not yet convinced that this goes far enough, though (I was not
   satisfied with my lecture on this part of the chapter, even after
   adding these examples, though I did do some further streamlining
   afterward and there are some further opportunities for
   streamlining -- perhaps enough to make the present treatment
   palatible).  I see three possible paths forward:
     - 1) Choose a better example and simply replace all the even
       stuff.  (But which one is better?  I don't think we've found it
       yet.)
     - 2) Mix and match -- use different examples from the top of the
       chapter to make different points.
     - 3) Leave the examples as-is but streamline as much as possible
       so we don't get stuck in them.

   Here, for reference, is the whole discussion from before:

       -----------------

       CH: In my Lyon course it became obvious to pretty much everyone
       that the inductive definition of evenness that this chapter uses
       intensiviely is so silly and artificial that it makes understanding
       very hard for most students. There's zero need to define evenness
       inductively, when [exists k. n = 2*k] does the job fine, so
       inductive propositions seem to students not something useful, but
       just self-inflicted pain. All the inductive propositions, up to
       subsequences and the matching on Regular Expressions at the end,
       have this useless self-inflicted pain flavour. So I returned to
       this the following morning and showed to the students how to define
       reflexive-transitive closure as an inductive relation, and
       afterwards the were able to follow much better. The code I quickly
       hacked up for this is at:
       https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/Multi.v

       BCP: Yes, this chapter needs a revamp!  For the moment I am going
       to just add a couple of sentences to the opening sequence below, to
       warn students about this potential confusion.  Moving forward, I
       wonder whether something like ordered binary trees would be a
       simple enough running example.

       BCP 20: I remain puzzled by what is the really right example for
       this chapter.  Ordered trees (and sorted lists) don't feel quite
       right because students might think we should define them with
       Fixpoint, not Inductive.  APT 21: Ordered trees are also
       surprisingly complex to describe (see VFA/SearchTree.v). Maybe
       Permutations would be be a good choice?  The only problem is
       convincing students that the standard Rocq inductive definition is
       actually correct (see VFA/Perm.v)!

       We should also think about how to make the material flow better
       between this chapter and ProofObjects.  When lecturing about this
       one I ended up introducing a lot of the concepts from that one.

       --------

       LATER: BCP 19: After lecturing on the first part of this chapter,
       I'm afraid I have to agree that the ev / even / evenb stuff is a
       total mess.  Besides the "why are there so many definitions of
       evenness?" problem, evenness is just not a very natural inductively
       defined proposition as a first example, because we already have so
       many intuitions about what evenness is, and they clash with the new
       definition.

       So what to do?

       An early version of this chapter, years ago, used a completely
       artificial inductively defined property of numbers (0 is beautiful,
       twice a beautiful number is beautiful, etc.).  We could consider
       going back to that.  Or perhaps there is a more natural example,
       either involving numbers or perhaps using some other inductive
       structure like lists or binary trees.  Not sure what's best.

       A related issue is that later chapters (ProofObjects,
       IndPrinciples) also rely heavily on this example.  Sigh.

       BCP 20: Tried to sort this out a bit better by renaming the
       propositional definition from [ev] to [eveni], for symmetry with
       [evenb], and renaming the definition that says "a number is even if
       it is twice something" to [evend].  What do people think of this?

       BCP 20 update: In parallel, APT tried to sort it out a different
       way; his is more consistent with the standard library, so let's try
       to go with that one consistently...
*)
(* SOONER: This chapter needs more (and better!) quizzes

*)
(* LATER: BCP 19: The following suggestion seems interesting.

  Robert Rand:

  I had an interesting experience in my most recent class which
  covered the IndProp (skipping over Regular Expressions and stuff we
  already know.)

  When we were walking through the attempted first proof of evSS_ev (I
  use WORKINCLASS quite a bit more than the book does), I had to
  explain how [destruct] is dumb in that it does case analysis while
  ignoring details of the hypothesis. To be precise, in the first case
  it doesn't notice that [ev_0] is not a constructor for any [ev (S (S
  n))], and in the second, it throws away [S (S n)].

  Immediately a student asked: Can we use [eqn] to tell it not to
  throw away that information?

  So we tried [eqn:E] and saw that it didn't save the information we
  cared about.

  The student followed up with: Can we use eqn on (S (S n)) itself?

  At that point I caved and introduced [remember] (actually,
  [destruct (S (S n)) eqn:E'] would have worked, but it's
  unnecessarily messy) and the class produced the following proof:

  Theorem evSS_ev : forall n,
    ev (S (S n)) -> ev n.
  Proof.
    intros n E.
    remember (S (S n)) as m.
    destruct E.
    - discriminate Heqm.
    - injection Heqm as E'.
      rewrite <- E'.
      apply E.
  Qed.

  I thought this was really nice as it helps spell out what
  [inversion] is doing behind the scenes, and I've always found
  inversion itself kind of hard to understand. It's also convenient in
  that [remember] is introduced in the same chapter in (from my
  perspective) a somewhat more awkward position.

  Thoughts on moving [remember] up and using it to introduce
  inversion?

  __________________

  from wldhx:

  Agree. My class has generally been keen on small essentials of tactics
  (revert, assert) and finding them on their own, especially after they
  found eqn sometimes breaks / is unwieldy; they also much like having
  clear and composable mental models of tactics.

  Most of them were already familiar with set by the time of IndProp, so
  we talked through inversion in terms of it, and remember was like a nice
  bonus. Moving it up does sound like a more consistent narrative though.
*)
(* TERSE: HIDEFROMHTML *)

Set Warnings "-notation-overridden".
From LF Require Export Logic.

(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** * Inductively Defined Propositions *)

(** In the \CHAP{Logic} chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.

    In this chapter, we bring yet another new tool into the mix:
    _inductively defined propositions_.

    To begin, some examples... *)

(* ############################################## *)
(** ** Example: The Collatz Conjecture *)

(** The _Collatz Conjecture_ is a famous open problem in number
    theory.

    Its statement is quite simple.  First, we define a function [csf]
    on numbers, as follows (where [csf] stands for "Collatz step function"): *)

Fixpoint div2 (n : nat) : nat :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

(* HIDE: CH: This is now called [csf] and not just [f] for a good
   reason. If one adds single letter global identifiers that badly
   interferes with inadvertently reusing the same names in pattern
   matching patterns, leading to confusing error messages from Rocq. *)

(** TERSE: *** *)

(** Next, we look at what happens when we repeatedly apply [csf] to
    some given starting number.  For example, [csf 12] is [6], and
    [csf 6] is [3], so by repeatedly applying [csf] we get the
    sequence [12, 6, 3, 10, 5, 16, 8, 4, 2, 1].

    Similarly, if we start with [19], we get the longer sequence [19,
    58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8,
    4, 2, 1].

    Both of these sequences eventually reach [1].  The question posed
    by Collatz was: Is the sequence starting from _any_ positive
    natural number guaranteed to reach [1] eventually? *)

(** TERSE: *** *)

(** To formalize this question in Rocq, we might try to define a
    recursive _function_ that calculates the total number of steps
    that it takes for such a sequence to reach [1]. *)

Fail Fixpoint reaches1_in (n : nat) : nat :=
  if n =? 1 then 0
  else 1 + reaches1_in (csf n).

(** You can write this definition in a standard programming language.
    This definition is, however, rejected by Rocq's termination
    checker, since the argument to the recursive call, [csf n], is not
    "obviously smaller" than [n].

    Indeed, this isn't just a pointless limitation: functions in Rocq
    are required to be total, to ensure logical consistency.

    Moreover, we can't fix it by devising a more clever termination
    checker: deciding whether this particular function is total
    would be equivalent to settling the Collatz conjecture! *)

(** TERSE: *** *)

(** Another idea could be to express the concept of "eventually
    reaches [1] in the Collatz sequence" as an _recursively defined
    property_ of numbers [Collatz_holds_for : nat -> Prop]. *)

Fail Fixpoint Collatz_holds_for (n : nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if even n then Collatz_holds_for (div2 n)
                   else Collatz_holds_for ((3 * n) + 1)
  end.

(** This recursive function is also rejected by the termination
    checker, since, while we could in principle convince Rocq that
    [div2 n] is smaller than [n], we certainly can't convince it that
    [(3 * n) + 1] is smaller than [n]! *)

(** TERSE: *** *)

(** Fortunately, there is another way to do it: We can express the
    concept "reaches [1] eventually in the Collatz sequence" as an
    _inductively defined property_ of numbers. Intuitively, this
    property is defined by a set of rules:

[[[
                  ------------------- (Chf_one)
                  Collatz_holds_for 1

     even n = true      Collatz_holds_for (div2 n)
     --------------------------------------------- (Chf_even)
                     Collatz_holds_for n

     even n = false    Collatz_holds_for ((3 * n) + 1)
     ------------------------------------------------- (Chf_odd)
                    Collatz_holds_for n
]]]

    So there are three ways to prove that a number [n] eventually
    reaches 1 in the Collatz sequence:
        - [n] is 1;
        - [n] is even and [div2 n] eventually reaches 1;
        - [n] is odd and [(3 * n) + 1] eventually reaches 1.
*)
(** TERSE: *** *)
(** We can prove that a number reaches 1 by constructing a (finite)
    derivation using these rules. For instance, here is the derivation
    proving that 12 reaches 1 (where we left out the evenness/oddness
    premises):
[[

                    ———————————————————— (Chf_one)
                    Collatz_holds_for 1
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 2
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 4
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 8
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 16
                    ———————————————————— (Chf_odd)
                    Collatz_holds_for 5
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 10
                    ———————————————————— (Chf_odd)
                    Collatz_holds_for 3
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 6
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 12
]]
*)
(** TERSE: *** *)

(** Formally in Rocq, the [Collatz_holds_for] property is
    _inductively defined_: *)

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : nat) : even n = true ->
                         Collatz_holds_for (div2 n) ->
                         Collatz_holds_for n
  | Chf_odd (n : nat) :  even n = false ->
                         Collatz_holds_for ((3 * n) + 1) ->
                         Collatz_holds_for n.

(** FULL: What we've done here is to use Rocq's [Inductive] definition
    mechanism to characterize the property "Collatz holds for..." by
    stating three different ways in which it can hold: (1) Collatz
    holds for [1], (2) if Collatz holds for [div2 n] and [n] is even
    then Collatz holds for [n], and (3) if Collatz holds for [(3 * n)
    + 1] and [n] is odd then Collatz holds for [n]. This Rocq definition
    directly corresponds to the three rules we wrote informally above. *)

(** TERSE: *** *)

(** LATER: BCP 23: Maybe better to postpone / suppress these examples? Dunno. *)
(** For particular numbers, we can now prove that the Collatz sequence
    reaches [1] (we'll look more closely at how it works a bit later
    in the chapter): *)

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_one.
Qed.

(* HIDE *)
    (** Here is a more compact definition that seems better for proofs,
        but requires more mental unfolding for getting intuition,
        illustrates less about inductive definitions, and also
        informal derivations look less informative.

        The way to read this one is: "The number [1] reaches [1], and
        any number [n] reaches [1] if [csf n] does." *)

    Inductive reaches_1 : nat -> Prop :=
      | reach_done : reaches_1 1
      | reach_more (n : nat) : reaches_1 (csf n) -> reaches_1 n.

    (** Alternatively, we can define the partial function
        [Collatz_holds_for_in] as a two-argument inductive relation... *)

    Inductive Chf_in : nat -> nat -> Prop :=
    | tst_done :
        Chf_in 1 0
    | tst_more (n k : nat) :
        Chf_in (csf n) k ->
        Chf_in n (k+1).

    (** ... and then say that [n] reaches [1] if there is some [k] such
        that the sequence beginning at [n] reaches [1] in [k] total
        steps. *)

    Definition Collatz_holds_for' (n : nat) := exists k, Chf_in n k.
(* /HIDE *)

(** TERSE: *** *)

(** The Collatz conjecture then states that the sequence beginning
    from _any_ positive number reaches [1]: *)

Conjecture collatz : forall n, n <> 0 -> Collatz_holds_for n.

(** If you succeed in proving this conjecture, you've got a bright
    future as a number theorist!  But don't spend too long on it --
    it's been open since 1937. *)

(* HIDE: CH: We may want to add an exercise later proving false if one
   assumes Collatz' conjecture without the [n <> 0] assumption. We had
   that mistake in the script for years and no one noticed, wow! *)

(* ############################################## *)
(** ** Example: Binary relation for comparing numbers *)

(** A binary _relation_ on a set [X] has Rocq type [X -> X -> Prop].
    This is a family of propositions parameterized by two elements of
    [X] -- i.e., a proposition about pairs of elements of [X]. *)

(** For example, one familiar binary relation on [nat] is [le : nat ->
    nat -> Prop], the less-than-or-equal-to relation, which can be
    inductively defined by the following two rules: *)

(**
[[[
                           ------ (le_n)
                           le n n

                           le n m
                         ---------- (le_S)
                         le n (S m)
]]]
*)
(** FULL: These rules say that there are two ways to show that a
    number is less than or equal to another: either observe that they
    are the same number, or, if the second has the form [S m], give
    evidence that the first is less than or equal to [m]. *)

(** This corresponds to the following inductive definition in Rocq: *)

(* HIDEFROMHTML *)
Module LePlayground.
(* /HIDEFROMHTML *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)   : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

(* FULL *)
(** This definition is a bit simpler and more elegant than the Boolean function
    [leb] we defined in \CHAP{Basics}. As usual, [le] and [leb] are
    equivalent, and there is an exercise about that later. *)

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. Qed.
(* /FULL *)

(* HIDEFROMHTML *)
End LePlayground.
(* /HIDEFROMHTML *)

(* ############################################## *)
(** ** Example: Transitive Closure *)

(** Another example: The _transitive closure_ of a
    relation [R] is the smallest relation that contains [R] and that
    is transitive. This can be defined by the following
    two rules:
[[[
                     R x y
                ---------------- (t_step)
                clos_trans R x y

       clos_trans R x y    clos_trans R y z
       ------------------------------------ (t_trans)
                clos_trans R x z
]]]

    In Rocq this looks as follows:
*)

Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

(** TERSE: *** *)

(** For example, suppose we define a "parent of" relation on a group
    of people... *)

Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
  po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_CM : parent_of Cleo Moss.

(** FULL: In this example, [Sage] is a parent of both [Cleo] and
    [Ridley]; and [Cleo] is a parent of [Moss]. *)

(** The [parent_of] relation is not transitive, but we can define
   an "ancestor of" relation as its transitive closure: *)

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

(** Here is a derivation showing that Sage is an ancestor of Moss:
[[

 ———————————————————(po_SC)     ———————————————————(po_CM)
 parent_of Sage Cleo            parent_of Cleo Moss
—————————————————————(t_step)  —————————————————————(t_step)
ancestor_of Sage Cleo          ancestor_of Cleo Moss
————————————————————————————————————————————————————(t_trans)
                ancestor_of Sage Moss
]]
*)

(* TERSE: HIDEFROMHTML *)
Example ancestor_of_ex : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of. apply t_trans with Cleo.
  - apply t_step. apply po_SC.
  - apply t_step. apply po_CM. Qed.
(* TERSE: /HIDEFROMHTML *)

(* HIDE: CH: A simple exercise could be nice here? *)

(** FULL: Computing the transitive closure can be undecidable even for
    a relation R that is decidable (e.g., the [cms] relation below), so in
    general we can't expect to define transitive closure as a boolean
    function. Fortunately, Rocq allows us to define transitive closure
    as an inductive relation.

    The transitive closure of a binary relation cannot, in general, be
    expressed in first-order logic. The logic of Rocq is, however, much
    more powerful, and can easily define such inductive relations. *)

(* ############################################## *)
(** ** Example: Reflexive and Transitive Closure *)

(** As another example, the _reflexive and transitive closure_
    of a relation [R] is the
    smallest relation that contains [R] and that is reflexive and
    transitive. This can be defined by the following three rules
    (where we added a reflexivity rule to [clos_trans]):
[[[
                        R x y
                --------------------- (rt_step)
                clos_refl_trans R x y

                --------------------- (rt_refl)
                clos_refl_trans R x x

     clos_refl_trans R x y    clos_refl_trans R y z
     ---------------------------------------------- (rt_trans)
                clos_refl_trans R x z
]]]
*)

(* TERSE: HIDEFROMHTML *)
Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_step (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)

(** For instance, this enables an equivalent definition of the Collatz
    conjecture.  First we define a binary relation corresponding to
    the "Collatz step function" [csf]: *)

Definition cs (n m : nat) : Prop := csf n = m.

(** This Collatz step relation can be used in conjunction with the
    reflexive and transitive closure operation to define a _Collatz
    multi-step_ ([cms]) relation, expressing that a number [n]
    reaches another number [m] in zero or more Collatz steps: *)

Definition cms n m := clos_refl_trans cs n m.
Conjecture collatz' : forall n, n <> 0 -> cms n 1.

(** FULL: This [cms] relation defined in terms of
    [clos_refl_trans] allows for more interesting derivations than the
    linear ones of the directly-defined [Collatz_holds_for] relation:
[[

csf 16 = 8         csf 8 = 4         csf 4 = 2         csf 2 = 1
————————(rt_step)  ———————(rt_step)  ———————(rt_step)  ———————(rt_step)
cms 16 8           cms 8 4           cms 4 2           cms 2 1
—————————————————————————(rt_trans)  ————————————————————————(rt_trans)
        cms 16 4                              cms 4 1
        —————————————————————————————————————————————(rt_trans)
                           cms 16 1
]]
*)

(* HIDE: CH: Would it be helpful to add an exercise later proving cms
   equivalent to Collatz_holds_for? *)

(* FULL *)
(* EX1M? (clos_refl_trans_sym) *)
(** How would you modify the [clos_refl_trans] definition above so as
    to define the reflexive, symmetric, and transitive closure? *)

(* SOLUTION *)
Inductive clos_refl_trans_sym {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | srt_refl (x : X) :
      clos_refl_trans_sym R x x
  | srt_step (x y : X) :
      R x y ->
      clos_refl_trans_sym R x y
  | srt_sym (x y : X) :
      clos_refl_trans_sym R y x ->
      clos_refl_trans_sym R x y
  | srt_trans (x y z : X) :
      clos_refl_trans_sym R x y ->
      clos_refl_trans_sym R y z ->
      clos_refl_trans_sym R x z.
(* /SOLUTION *)
(** [] *)
(* /FULL *)

(* ############################################## *)
(** ** Example: Permutations *)

(** The familiar mathematical concept of _permutation_ also has an
    elegant formulation as an inductive relation.  For simplicity,
    let's focus on permutations of lists with exactly three
    elements.

    We can define such permulations by the following rules:
[[[
               --------------------- (perm3_swap12)
               Perm3 [a;b;c] [b;a;c]

               --------------------- (perm3_swap23)
               Perm3 [a;b;c] [a;c;b]

            Perm3 l1 l2       Perm3 l2 l3
            ----------------------------- (perm3_trans)
                     Perm3 l1 l3
]]]
    For instance we can derive [Perm3 [1;2;3] [3;2;1]] as follows:
[[
    ————————(perm_swap12)  —————————————————————(perm_swap23)
    Perm3 [1;2;3] [2;1;3]  Perm3 [2;1;3] [2;3;1]
    ——————————————————————————————(perm_trans)  ————————————(perm_swap12)
        Perm3 [1;2;3] [2;3;1]                   Perm [2;3;1] [3;2;1]
        —————————————————————————————————————————————————————(perm_trans)
                          Perm3 [1;2;3] [3;2;1]
]]
*)

(** FULL: This definition says:
      - If [l2] can be obtained from [l1] by swapping the first and
        second elements, then [l2] is a permutation of [l1].
      - If [l2] can be obtained from [l1] by swapping the second and
        third elements, then [l2] is a permutation of [l1].
      - If [l2] is a permutation of [l1] and [l3] is a permutation of
        [l2], then [l3] is a permutation of [l1]. *)

(** TERSE: *** *)

(** In Rocq [Perm3] is given the following inductive definition: *)

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(* FULL *)
(* EX1M? (perm) *)
(** According to this definition, is [[1;2;3]] a permutation of
    itself? *)

(* SOLUTION *)
(** Yes! Just apply [perm3_swap12] twice (or [perm3_swap23] twice). *)
(* /SOLUTION *)
(** [] *)
(* /FULL *)

(* ############################################## *)
(** ** Example: Evenness (yet again) *)

(** We've already seen two ways of stating a proposition that a number
    [n] is even: We can say

      (1) [even n = true] (using the recursive boolean function [even]), or

      (2) [exists k, n = double k] (using an existential quantifier). *)

(** TERSE: *** *)

(** A third possibility, which we'll use as a simple running example
    in this chapter, is to say that a number is even if we can
    _establish_ its evenness from the following two rules:
[[[
                          ---- (ev_0)
                          ev 0

                          ev n
                      ------------ (ev_SS)
                      ev (S (S n))
]]]
*)

(** FULL: Intuitively these rules say that:
       - The number [0] is even.
       - If [n] is even, then [S (S n)] is even. *)

(** FULL: (Defining evenness in this way may seem a bit confusing,
    since we have already seen two perfectly good ways of doing
    it. It makes a convenient running example because it is
    simple and compact, but we will soon return to the more compelling
    examples above.) *)

(** To illustrate how this new definition of evenness works, let's
    imagine using it to show that [4] is even:
[[
                           ———— (ev_0)
                           ev 0
                       ———————————— (ev_SS)
                       ev (S (S 0))
                   ———————————————————— (ev_SS)
                   ev (S (S (S (S 0))))
]]
*)

(** FULL: In words, to show that [4] is even, by rule [ev_SS], it
   suffices to show that [2] is even. This, in turn, is again
   guaranteed by rule [ev_SS], as long as we can show that [0] is
   even. But this last fact follows directly from the [ev_0] rule. *)

(** TERSE: *** *)

(** We can translate the informal definition of evenness from above
    into a formal [Inductive] declaration, where each "way that a
    number can be even" corresponds to a separate constructor: *)

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** TERSE: There are both similarities and a few differences between
    inductive _properties_ like [ev] and the inductive _types_ like
    [nat] or [list] that we have been using throughout the course:
[[
    Inductive list (X:Type) : Type :=
      | nil                       : list X
      | cons (x : X) (l : list X) : list X.
]]]
    The most important difference is that the constructors of [ev],
    [ev_0] and [ev_SS], yield different types ([ev 0] and [ev (S (S n))]),
    whereas the [list] constructors both build [list X] values. *)

(* FULL *)
(** Such definitions are interestingly different from previous uses of
    [Inductive] for defining inductive datatypes like [nat] or [list].
    For one thing, we are defining not a [Type] (like [nat]) or a
    function yielding a [Type] (like [list]), but rather a function
    from [nat] to [Prop] -- that is, a property of numbers. But what
    is really new is that, because the [nat] argument of [ev] appears
    to the _right_ of the colon on the first line, it is allowed to
    take _different_ values in the types of different constructors:
    [0] in the type of [ev_0] and [S (S n)] in the type of [ev_SS].
    Accordingly, the type of each constructor must be specified
    explicitly (after a colon), and each constructor's type must have
    the form [ev n] for some natural number [n].

    In contrast, recall the definition of [list]:
[[
    Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).
]]
    or (equivalently but more explicitly):
[[
    Inductive list (X:Type) : Type :=
      | nil                       : list X
      | cons (x : X) (l : list X) : list X.
]]
   This definition introduces the [X] parameter _globally_, to the
   _left_ of the colon, forcing the result of [nil] and [cons] to be
   the same type (i.e., [list X]).  But if we had tried to bring [nat]
   to the left of the colon in defining [ev], we would have seen an
   error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]" as 1st
        argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type constructor
    on the left of the colon is called a "parameter", whereas an
    argument on the right is called an "index" or "annotation."

    For example, in [Inductive list (X : Type) := ...], the [X] is a
    parameter, while in [Inductive ev : nat -> Prop := ...], the
    unnamed [nat] argument is an index. *)
(* /FULL *)

(** TERSE: *** *)

(** We can think of the inductive definition of [ev] as defining a
    Rocq property [ev : nat -> Prop], together with two "evidence
    constructors": *)

Check ev_0 : ev 0.
Check ev_SS : forall (n : nat), ev n -> ev (S (S n)).

(* FULL *)
(** Indeed, Rocq also accepts the following equivalent definition of [ev]: *)

Module EvPlayground.

Inductive ev : nat -> Prop :=
  | ev_0  : ev 0
  | ev_SS : forall (n : nat), ev n -> ev (S (S n)).

End EvPlayground.
(* /FULL *)

(** TERSE: *** *)
(** These evidence constructors can be thought of as "primitive
    evidence of evenness", and they can be used later on just like proven
    theorems.  In particular, we can use Rocq's [apply] tactic with the
    constructor names to obtain evidence for [ev] of particular
    numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax to combine several
    constructors: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** In this way, we can also prove theorems that have hypotheses
    involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(* FULL *)
(* EX1 (ev_double) *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  (* ADMITTED *)
  intros n. induction n as [| n'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'. Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** ** Constructing Evidence for Permutations *)

(** Similarly we can apply the evidence constructors to obtain
    evidence of [Perm3 [1;2;3] [3;2;1]]: *)

Lemma Perm3_rev : Perm3 [1;2;3] [3;2;1].
Proof.
  apply perm3_trans with (l2:=[2;3;1]).
  - apply perm3_trans with (l2:=[2;1;3]).
    + apply perm3_swap12.
    + apply perm3_swap23.
  - apply perm3_swap12.
Qed.

(** TERSE: *** *)
(** And again we can equivalently use function application syntax to
    combine several constructors. (Note that the Rocq type checker can
    infer not only types, but also nats and lists, when they are clear
    from the context.) *)

Lemma Perm3_rev' : Perm3 [1;2;3] [3;2;1].
Proof.
  apply (perm3_trans _ [2;3;1] _
          (perm3_trans _ [2;1;3] _
            (perm3_swap12 _ _ _)
            (perm3_swap23 _ _ _))
          (perm3_swap12 _ _ _)).
Qed.

(** So the informal derivation trees we drew above are not too far
    from what's happening formally.  Formally we're using the evidence
    constructors to build _evidence trees_, similar to the finite trees we
    built using the constructors of data types such as nat, list,
    binary trees, etc. *)

(* FULL *)
(* EX1 (Perm3) *)
Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  (* ADMITTED *)
  apply perm3_trans with (l2:=[2;1;3]).
  - apply perm3_swap12.
  - apply perm3_swap23.
Qed.
(* /ADMITTED *)

Lemma Perm3_refl : forall (X : Type) (a b c : X),
  Perm3 [a;b;c] [a;b;c].
Proof.
  (* ADMITTED *)
  intros X a b c.
  apply perm3_trans with (l2:=[b;a;c]).
  - apply perm3_swap12.
  - apply perm3_swap12.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: Perm3_ex1 *)
(* GRADE_THEOREM 0.5: Perm3_refl *)
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _destruct_ such evidence, reasoning about how it could have been
    built.

    Defining [ev] with an [Inductive] declaration tells Rocq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is [ev], but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are [ev]. *)

(** TERSE: *** *)
(** In other words, if someone gives us evidence [E] for the proposition
    [ev n], then we know that [E] must be one of two things:

      - [E = ev_0] and [n = O], or
      - [E = ev_SS n' E'] and [n = S (S n')], where [E'] is
        evidence for [ev n']. *)

(** FULL: This suggests that it should be possible to analyze a
    hypothesis of the form [ev n] much as we do inductively defined
    data structures; in particular, it should be possible to argue either by
    _case analysis_ or by _induction_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)
(** TERSE: This suggests that it should be possible to do _case
    analysis_ and even _induction_ on evidence of evenness... *)

(** ** Destructing and Inverting Evidence *)

(** FULL: Suppose we are proving some fact involving a number [n], and
    we are given [ev n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence for [ev n] _directly_.

    As a tool for such proofs, we can formalize the intuitive
    characterization that we gave above for evidence of [ev n], using
    [destruct]. *)

(** TERSE: We can prove our characterization of evidence for [ev n],
    using [destruct]. *)

Lemma ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** Facts like this are often called "inversion lemmas" because they
    allow us to "invert" some given information to reason about all
    the different ways it could have been derived. *)
(** FULL: Here there are two ways to prove [ev n], and the inversion
    lemma makes this explicit. *)

(* FULL *)
(* EX1 (le_inversion) *)
(** Let's prove a similar inversion lemma for [le]. *)
Lemma le_inversion : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  (* ADMITTED *)
  intros n m E. destruct E as [ | m' E'] eqn:EE.
  - (* E = le_n n : le n n *)
    left. reflexivity.
  - (* E = le_S n m' E' : le n (S (S m')) *)
    right. exists m'. split. reflexivity. apply E'.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* HIDE *)
    (* QUIZ *)
    (** Which tactics are needed to prove this goal?
    [[
      n : nat
      E : ev n
      F : n = 1
      ======================
      true = false
    ]]

       (A) [destruct]

       (B) [discriminate]

       (C) both [destruct] and [discriminate]

       (D) These tactics are not sufficient to solve the goal. *)
    (* FOLD *)
    Lemma quiz_1_not_ev : forall n, ev n -> n = 1 -> true = false.
    Proof.
      intros n E F.  destruct E as [| n' E'] eqn:EE.
      - discriminate F.
      - discriminate F.
    Qed.
    (* /FOLD *)
    (* /QUIZ *)
(* /HIDE *)

(** TERSE: *** *)

(* HIDE *)
    (* LATER: BCP 21: This part of the chapter has gotten way too dense.
       To streamline it, I am experimentally deleting the whole discussion
       from here... *)
    (** Similarly, the following theorem can easily be proved using
        [destruct] on evidence. *)

    Theorem ev_minus2 : forall n,
      ev n -> ev (pred (pred n)).
    Proof.
      intros n E.  destruct E as [| n' E'] eqn:EE.
      - (* E = ev_0 *)
        simpl. apply ev_0.
      - (* E = ev_SS n' E' *)
        simpl. apply E'.
    Qed.

    (** TERSE: *** *)
    (** However, the following simple variation shows that [destruct] can
        sometimes throw away critical information: *)

    Theorem evSS_ev : forall n,
      ev (S (S n)) -> ev n.
    (** FULL: Intuitively, we know that evidence for the hypothesis cannot
        consist just of the [ev_0] constructor, since [O] and [S] are
        different constructors of the type [nat]; hence, [ev_SS] is the
        only case that applies.  Unfortunately, [destruct] is not smart
        enough to realize this, and it still generates two subgoals.  Even
        worse, in doing so, it keeps the final goal unchanged, failing to
        provide any useful information for completing the proof.  *)
    Proof.
      intros n E.  destruct E as [| n' E'] eqn:EE.
      - (* E = ev_0. *)
        (* Looks like we must prove that [n] is even... but there are no
           useful assumptions! *)
    Abort.

    (** TERSE: Tactic [destruct] replaced [S (S n)] with [0] in [E],
        because that's what [ev_0] proves. *)

    (** FULL: What happened here, exactly?  Calling [destruct] has the effect
        of replacing all occurrences of the property argument by the
        values that correspond to each constructor.  This is enough in the
        case of [ev_minus2] because that argument [n] is mentioned
        directly in the final goal. However, it doesn't help in the case
        of [evSS_ev] since the term that gets replaced -- [S (S n)] -- is
        not mentioned anywhere! *)

    (* LATER: BCP 21: That whole explanation is pretty thick... Could we
       streamline it?  E.g., do students really need to know all these
       details about how destruct works -- and are they likely to retain
       them anyway, from this discussion?  Maybe we could just get to
       inversion more directly.  I'm going to leave it alone for now, but
       I think it is a candidate for radical simplification. *)
    (* HIDE: MRC: I found it helpful (2/19/19) in class to introduce
       [remember] just a little early here. *)

    (** TERSE: *** *)
    (** FULL: We can fix this by [remember]ing that term [S (S n)], the
        proof goes through.  (We'll discuss [remember] in more detail
        below.) *)

    (** TERSE: So let's [remember] that term [S (S n)]. *)

    Theorem evSS_ev_remember : forall n,
      ev (S (S n)) -> ev n.
    Proof.
      intros n E. remember (S (S n)) as k eqn:Hk.
      destruct E as [|n' E'] eqn:EE.
      - (* E = ev_0 *)
        (* Now we do have an assumption, in which [k = S (S n)] has been
           rewritten as [0 = S (S n)] by [destruct]. That assumption
           gives us a contradiction. *)
        discriminate Hk.
      - (* E = ev_S n' E' *)
        (* This time [k = S (S n)] has been rewritten as [S (S n') = S (S n)]. *)
        injection Hk as Heq. rewrite <- Heq. apply E'.
    Qed.

    (** TERSE: *** *)
    (** Alternatively, the proof is straightforward using the inversion
        lemma that we proved above. *)
(* LATER: BCP 21: ... to here -- i.e., now we go straight to inversion
   without all this noodling around about destruct. *)
(* HIDE: MRC 3/22: Yes, I favor going straight to inversion. *)
(* /HIDE *)
(** We can use the inversion lemma that we proved above to help
    structure proofs: *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. apply ev_inversion in E. destruct E as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnn' E']]. injection Hnn' as Hnn'.
    rewrite Hnn'. apply E'.
Qed.

(* HIDE *)
(* HIDE: CH: Tried, but there is no similarly simple lemma for le? *)
Theorem leS_le : forall n m, le n (S m) -> le n m.
Proof.
  intros n m H. apply le_inversion in H. destruct H as [H0|H1].
  - rewrite H0. Abort. (* This one is false! *)

Theorem leS_le : forall n m, le (S n) (S m) -> le n m.
Proof.
  intros n m H. apply le_inversion in H. destruct H as [Hn|HS].
  - injection Hn as Hnm. rewrite Hnm. apply le_n.
  - destruct HS as [m' [Hmm' Hle]]. injection Hmm' as Hmm'.
    rewrite Hmm' in *. (* This one seems true, but needs more work *)
Abort.
(* /HIDE *)

(** FULL: Note how the inversion lemma produces two subgoals, which
    correspond to the two ways of proving [ev].  The first subgoal is
    a contradiction that is discharged with [discriminate].  The
    second subgoal makes use of [injection] and [rewrite].

    Rocq provides a handy tactic called [inversion] that factors out
    this common pattern, saving us the trouble of explicitly stating
    and proving an inversion lemma for every [Inductive] definition we
    make.

    Here, the [inversion] tactic can detect (1) that the first case,
    where [n = 0], does not apply and (2) that the [n'] that appears
    in the [ev_SS] case must be the same as [n].  It includes an
    "[as]" annotation similar to [destruct], allowing us to assign
    names rather than have Rocq choose them. *)
(** TERSE: *** *)
(** TERSE: Rocq provides a handy tactic called [inversion] that does
    the work of our inversion lemma and more besides. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.  inversion E as [| n' E' Hnn'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(* HIDE *)
    (** PR: The following dialogue used to be between two versions of
        Theorem ev_minus2' (using [inversion] and [destruct]). The
        concerns are affected by but not made obsolete by the new
        treatment of [inversion] here. I think more work is needed. *)
    (** AAA: I'm finding it a bit awkward to discuss [inversion] here
       instead of [destruct], especially given that we are using
       [destruct] to talk about [reflect] below... Would it be too crazy
       to use [inversion] only where it is actually needed? *)
    (** BCP: I have never been satisfied with our discussion of destruct
        vs. inversion.  What's here now is much better than we've ever had
        before.  But if you have a clear idea for how to clean it up
        further, I'm all ears.  One possibility -- perhaps easy enough to
        do now -- would be to replace inversion by destruct in this
        discussion and move the inversion vs. destruct discussion into the
        following subsection.  (In fact, I favor trying this.  The next
        section also needs some help, and consolidating the discussion
        would be a good beginning.) *)
    (** AAA: I'm in favor of trying this too, but I'm afraid that it might
        have significant impact on other sections. Let's leave it like
        this for now -- at least it's better than what we had before. *)
(* /HIDE *)

(* FULL *)
(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. Compare: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.  destruct H as [ | [m [Hm _]]].
(* HIDE: OL20: Someone asked here before "Why doesn't eqn:EE work
         here??".  It has to do with the use of _ in the pattern.
         Anyway when destructing \/,/\, or exists, what we get from
         eqn:EE is only confusing for students. I think that we should
         remove all "eqn"s in these cases. I did it in this file. *)
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof. intros H. inversion H. Qed.
(* /FULL *)

(* FULL *)
(* EX1 (inversion_practice) *)
(** Prove the following result using [inversion].  (For extra
    practice, you can also prove it using the inversion lemma.) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* ADMITTED *)
  intros n E.  inversion E as [| n' E' EQ'].
  inversion E' as [| n'' E'' EQ''].  apply E''.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: SSSSev__even *)
(** [] *)

(* EX1 (ev5_nonsense) *)
(** Prove the following result using [inversion]. *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  (* ADMITTED *)
  intros E. inversion E as [| n' E' EQ'].
  inversion E' as [| n'' E'' EQ''].
  inversion E''.
   (* Contradiction, as neither constructor can possibly apply... *) Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** FULL: The [inversion] tactic does quite a bit of work. For
    example, when applied to an equality assumption, it does the work
    of both [discriminate] and [injection]. In addition, it carries
    out the [intros] and [rewrite]s that are typically necessary in
    the case of [injection]. It can also be applied to analyze
    evidence for arbitrary inductively defined propositions, not just
    equality.  As examples, we'll use it to re-prove some theorems
    from chapter \CHAP{Tactics}.  (Here we are being a bit lazy by
    omitting the [as] clause from [inversion], thereby asking Rocq to
    choose names for the variables and hypotheses that it introduces.) *)
(** TERSE: *** *)
(** TERSE: We can use [inversion] to re-prove some theorems from
    [Tactics.v].

    Note that [inversion] also works on equality propositions. *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** TERSE: *** *)
(** TERSE: The [inversion] tactic works on any [H : P] where
    [P] is defined [Inductive]ly:

      - For each constructor of [P], make a subgoal where [H] is
        constrained by the form of this constructor.

      - Discard contradictory subgoals (such as [ev_0] above).

      - Generate auxiliary equalities (as with [ev_SS] above). *)
(* SOONER: The wording there is totally awkward! *)
(* LATER: Is this too dense??  Since equality is defined in the next
   lecture [BCP: for some paths through the material -- they might
   also not see it at all!], it might actually be better to postpone
   the conversation here and do it all at once there. [PR: It is
   dense, but I don't think seeing the definition of equality helps,
   so I'm not sure postponing it would make a difference.] *)
(** FULL: Here's how [inversion] works in general.
      - Suppose the name [H] refers to an assumption [P] in the
        current context, where [P] has been defined by an [Inductive]
        declaration.
      - Then, for each of the constructors of [P], [inversion H]
        generates a subgoal in which [H] has been replaced by the
        specific conditions under which this constructor could have
        been used to prove [P].
      - Some of these subgoals will be self-contradictory; [inversion]
        throws these away.
      - The ones that are left represent the cases that must be proved
        to establish the original goal.  For those, [inversion] adds
        to the proof context all equations that must hold of the
        arguments given to [P] -- e.g., [n' = n] in the proof of
        [evSS_ev]). *)

(* HIDE *)
    (* QUIZ *)
    (* HIDE: LY: not quite a fair question because this is the first
       time they are facing a situation where the index does not start
       with a constructor. *)
    (** Which tactics are needed to prove this goal, in addition to
        [simpl] and [apply]?
    [[
      n : nat
      E : ev (n + 2)
      =====================
      ev n
    ]]

       (A) [inversion]

       (B) [inversion], [discriminate]

       (C) [inversion], [rewrite add_comm]

       (D) [inversion], [rewrite add_comm], [discriminate]

       (E) These tactics are not sufficient to prove the goal.

     *)
    (* FOLD *)
    Lemma quiz_ev_plus_2 : forall n, ev (n + 2) -> ev n.
    Proof.
      intros n E.  rewrite add_comm in E.
      inversion E as [| n' E' Eq]. apply E'.
    Qed.
    (* /FOLD *)
    (* /QUIZ *)
(* /HIDE *)
(** TERSE: *** *)

(* HIDEFROMADVANCED *)
(** FULL: The [ev_double] exercise above allows us to easily show that
    our new notion of evenness is implied by the two earlier ones
    (since, by [even_bool_prop] in chapter \CHAP{Logic}, we already
    know that those are equivalent to each other). To show that all
    three coincide, we just need the following lemma. *)
(** TERSE: Let's try to show that our new notion of evenness implies
    our earlier notion (the one based on [double]). *)
(** SOONER: This whole part of the section is a mess!! *)
(* /HIDEFROMADVANCED *)

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  (* WORKINCLASS *) unfold Even.

(** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy seems
    unpromising, because (as we've noted before) the induction
    hypothesis will talk about [n-1] (which is _not_ even!).  Thus, it
    seems better to first try [inversion] on the evidence for [ev].
    Indeed, the first case can be solved trivially. *)

  intros n E. inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *) exists 0. reflexivity.
  - (* E = ev_SS n' E' *)
(** Unfortunately, the second case is harder.  We need to show [exists
    n0, S (S n') = double n0], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't directly
    useful, it seems that we are stuck and that performing case
    analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to a similar
    one that involves a _different_ piece of evidence for [ev]: namely
    [E'].  More formally, we could finish our proof if we could show
    that
[[
        exists k', n' = double k',
]]
    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Rocq that this
    intermediate result would suffice. *)
    assert (H: (exists k', n' = double k')
               -> (exists n0, S (S n') = double n0)).
        { intros [k' EQ'']. exists (S k'). simpl.
          rewrite <- EQ''. reflexivity. }
    apply H.

    (** Unfortunately, now we are stuck. To see this clearly, let's
        move [E'] back into the goal from the hypotheses. *)

    generalize dependent E'.

    (** Now it is obvious that we are trying to prove another instance
        of the same theorem we set out to prove -- only here we are
        talking about [n'] instead of [n]. *)
Abort.
(* LATER: APT: Added the explicit assert to "convince Rocq" but the
   flow of the preceding discussion seems confusing to me. *)
(* SOONER: BCP 21: I agree that it's all pretty chewy. Wonder if we
   really need any of it or if the point could be made just as well
   with less detail...  When I explained it in class this time, I just
   observed that the destruct was giving us a hypothesis about 2 being
   even, which just can't be what we want, and skipped all the rest...
   After thinking about it for a bit, though, I do think the full
   story here is useful (at least for the FULL version -- the TERSE
   could still be streamlined). So I'm going to leave it for now. *)
(* SOONER: BCP 25: I think best just to shorten it! And maybe make it
   not a WORKINCLASS. *)
(* /WORKINCLASS *)

(* ####################################################### *)
(** ** Induction on Evidence *)

(** If this story feels familiar, it is no coincidence: We
    encountered similar problems in the \CHAP{Induction} chapter, when
    trying to use case analysis to prove results that required
    induction.  And once again the solution is... induction! *)

(** FULL: The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Rocq to generate one subgoal for each
    constructor that could have been used to build that evidence, while
    providing an induction hypothesis for each recursive occurrence of
    the property in question.

    To prove that a property of [n] holds for all even numbers (i.e.,
    those for which [ev n] holds), we can use induction on [ev
    n]. This requires us to prove two things, corresponding to the two
    ways in which [ev n] could have been constructed. If it was
    constructed by [ev_0], then [n=0] and the property must hold of
    [0]. If it was constructed by [ev_SS], then the evidence of [ev n]
    is of the form [ev_SS n' E'], where [n = S (S n')] and [E'] is
    evidence for [ev n']. In this case, the inductive hypothesis says
    that the property we are trying to prove holds for [n']. *)

(** Let's try proving that lemma again: *)

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  unfold Even. intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E',  with IH : Even n' *)
    destruct IH as [k Hk]. rewrite Hk.
    exists (S k). simpl. reflexivity.
Qed.

(** FULL: Here, we can see that Rocq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(* FULL *)
(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas -- in particular for
    formalizing the semantics of programming languages. *)

(** The following exercises provide simpler examples of this
    technique, to help you familiarize yourself with it. *)

(* EX2 (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  (* ADMITTED *)
  intros n m Hn Hm. induction Hn as [|n' Hn IH].
  - (* ev_0 *) simpl. apply Hm.
  - (* ev_SS *) simpl. apply ev_SS. apply IH.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3A! (ev_ev__ev) *)
Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  (* ADMITTED *)
  intros n m Enm En.
  induction En as [| n' En'].
  - (* En = ev_0 *) simpl in Enm. apply Enm.
  - (* En = ev_SS *) simpl in Enm. inversion Enm. apply IHEn'. apply H0.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX3? (ev_plus_plus) *)
(** This exercise can be completed without induction or case analysis.
    But, you will need a clever assertion and some tedious rewriting.
    Hint: Is [(n+m) + (n+p)] even? *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* ADMITTED *)
  intros n m p Enm Enp.
  apply (ev_ev__ev (n+n)).
  assert (n + n + (m + p) = n + m + (n + p)) as H.
  { (* Proof of assertion *)
    rewrite <- add_assoc. rewrite <- add_assoc. f_equal.
    rewrite add_assoc. rewrite add_assoc.
    assert (n + m = m + n) as H1.
    { (* Proof of subassertion *)
      apply add_comm. }
    rewrite  H1.
    reflexivity. }
  rewrite H.
  apply ev_sum.
  apply Enm.
  apply Enp.
  rewrite <- double_plus. apply ev_double.
Qed.
(* /ADMITTED *)
(** [] *)

(* ####################################################### *)
(** ** Multiple Induction Hypotheses *)

(** Recall the definition of the reflexive, transitive, closure of a
    relation: *)

(* HIDEFROMHTML *)
Module clos_refl_trans_remainder.
(* /HIDEFROMHTML *)
Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_step (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.
(* HIDEFROMHTML *)
End clos_refl_trans_remainder.
(* /HIDEFROMHTML *)

(** Let's say that a relation on a type [X] is _diagonal_ if it
    refines the identity relation -- i.e., if [R x y] implies [x = y]. *)

(* HIDE: NDS 25: I originally wanted to do this with the empty
    relation, defined inductively, but this requires introducing the
    surprising behavior of unhabitated types, which I don't think have
    been covered (yet?). Maybe they should be?  BCP 25: This one seems good. *)

Definition isDiagonal {X : Type} (R: X -> X -> Prop) :=
  forall x y, R x y -> x = y.

(** Now consider the following lemma about diagonal relations: *)

Lemma closure_of_diagonal_is_diagonal: forall X (R: X -> X -> Prop),
  isDiagonal R ->
  isDiagonal (clos_refl_trans R).
Proof.
  intros X R IsDiag x y H.
  induction H as [ x y H | x | x y z H IH H' IH' ].
  (* The two first cases go as you'd expect... *)
  - specialize (IsDiag x y H). rewrite -> IsDiag. reflexivity.
  - reflexivity.
  - (* ...  but something interesting happens here: there are two
       induction hypotheses, [IH] and [IH']! If you think about it, it
       is not that weird: we are in the case [srt_trans], which has
       two recursive components, [H], relating [x] to [y] and [H'],
       relating [y] to [z]. Hence we may want (and will actually need)
       an induction hypothesis for [H] and one for [H'] -- they are
       called [IH] and [IH'] here. In general, Rocq will always
       generate one induction hypothesis per recursive constructor of
       the type being inducted over. *)
   rewrite -> IH, <- IH'. reflexivity.
Qed.

(* HIDE: NDS comparing the previous proof to the pen-and-paper version
   could be an idea to consider, as the way people tend to write it
   on paper differs a bit from the mechanized proof.  BCP 25: Yes. *)

(* HIDE *)
    (* LATER: BCP 25: This bit feels potentially confusing and also not
      needed -- people that are paying attention enough to wonder about
      this will notice it when it happens later... *)
    (** Note that having multiple induction hypotheses is not
        specific to evidence: any constructor of any inductive type with
        more than one recursive component will yield as many induction
        hypotheses as it has recursive components. *)
    (* HIDE: NDS we may want to either 1) link to IndPrinciples for such
      examples or 2) add such an example here, even though it is kind of
      out of the topic. *)
(* /HIDE *)

(* EX4A? (ev'_ev) *)
(* INSTRUCTORS: This is pretty hard, unless you know the trick that
   the sample proof uses!!  But at least it's marked as
   advanced and optional. :-) *)
(** In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from the \CHAP{Logic}
    chapter) of applying theorems to arguments, and note that the same
    technique works with constructors of inductively defined
    propositions. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
 (* ADMITTED *)
  intros n. split.
  - (* -> *)
    intros E. induction E as [| |n m En IHn Em IHm].
    + (* ev'_0 *) apply ev_0.
    + (* ev'_2 *) apply ev_SS. apply ev_0.
    + (* ev'_sum *) apply (ev_sum _ _ IHn IHm).
  - (* <- *)
    intros E. induction E as [|n E IH].
    + apply ev'_0.
    + apply (ev'_sum 2 n).
      * apply ev'_2.
      * apply IH.
Qed.
(* /ADMITTED *)
(** [] *)

(** We can do similar inductive proofs on the [Perm3] relation,
    which we defined earlier as follows: *)

Module Perm3Reminder.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

End Perm3Reminder.

Lemma Perm3_symm : forall (X : Type) (l1 l2 : list X),
  Perm3 l1 l2 -> Perm3 l2 l1.
Proof.
  intros X l1 l2 E.
  induction E as [a b c | a b c | l1 l2 l3 E12 IH12 E23 IH23].
  - apply perm3_swap12.
  - apply perm3_swap23.
  - apply (perm3_trans _ l2 _).
    * apply IH23.
    * apply IH12.
Qed.

(* EX2 (Perm3_In) *)
Lemma Perm3_In : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> In x l1 -> In x l2.
Proof.
  (* ADMITTED *)
  intros X x l1 l2 E H.
  induction E as [a b c | a b c | l1 l2 l3 E12 IH12 E23 IH23].
  - simpl in *. destruct H as [H | [H | [H | H]]].
    + right. left. apply H.
    + left. apply H.
    + right. right. left. apply H.
    + destruct H as [].
  - simpl in *. destruct H as [H | [H | [H | H]]].
    + left. apply H.
    + right. right. left. apply H.
    + right. left. apply H.
    + destruct H as [].
  - apply IH23. apply IH12. apply H.
Qed.
(* HIDE: CH: The base cases are a bit stupid without [tauto] *)
(* /ADMITTED *)
(** [] *)

(* EX1? (Perm3_NotIn) *)
Lemma Perm3_NotIn : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> ~In x l1 -> ~In x l2.
Proof.
  (* ADMITTED *)
  intros X x l1 l2 E H1 H2. apply H1. generalize dependent H2.
  apply Perm3_In. apply Perm3_symm. apply E.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2? (NotPerm3) *)
(** Proving that something is NOT a permutation is quite tricky. Some
    of the lemmas above, like [Perm3_In] can be useful for this. *)
Example Perm3_example2 : ~ Perm3 [1;2;3] [1;2;4].
Proof.
  (* ADMITTED *)
  intros C. apply (Perm3_In nat 3) in C.
  - simpl in C. destruct C as [C | [C | [C | C]]].
    + discriminate.
    + discriminate.
    + discriminate.
    + destruct C as [].
  - simpl. right. right. left. reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)
(* LATER: Optional / advanced exercise (or exam question???): Extend
   this definition to permutations on arbitrary-length lists.  Make
   sure that you can prove the following...
     - length-invariant
     - if we filter a nat list and its permutation by equality to some
       number, we get the same length (indeed, this could be an
       alternate characterization, I guess)
*)
(* /FULL *)

(* FULL *)
(* ####################################################### *)
(** * Exercising with Inductive Relations *)

(* SOONER: CH: Bad flow + duplication needs fixing.
   Could move some of this to the top.
   In the terse version this whole section is useless,
   it only has a (mostly) duplicated definition.
   For now FULLED the whole thing, but better fix seems needed. *)

(** TERSE: Just as a single-argument proposition defines a _property_,
    a two-argument proposition defines a _relation_. *)
(** FULL: A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

(* TERSE: HIDEFROMHTML *)
Module Playground.
(* TERSE: /HIDEFROMHTML *)

(** Just like properties, relations can be defined inductively.  One
    useful example is the "less than or equal to" relation on numbers
    that we briefly saw above. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

(** FULL: (We've written the definition a bit differently this time,
    giving explicit names to the arguments to the constructors and
    moving them to the left of the colons.) *)

(** FULL: Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** TERSE: *** *)
(** FULL: Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)
(** TERSE: Some sanity checks... *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKINCLASS *)
  apply le_n.  Qed.
(* /WORKINCLASS *)

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKINCLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.
(* /WORKINCLASS *)

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKINCLASS *)
  intros H. inversion H. inversion H2.  Qed.
(* /WORKINCLASS *)

(** TERSE: *** *)
(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m : nat) := le (S n) m.

Notation "n < m" := (lt n m).


(** TERSE: *** *)
(** The [>=] operation is defined in terms of [<=]. *)

Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).

(* TERSE: HIDEFROMHTML *)
End Playground.

(* TERSE: /HIDEFROMHTML *)

(* HIDE: PR: Added the following paragraph to try to help reduce
   random walks over the following exercises. *)
(** FULL: From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n'].
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

(* EX3! (le_facts) *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* ADMITTED *)
  intros m n o H1 H2. induction H2.
  - (* le_n *)
    apply H1.
  - (* le_S *)
    apply le_S. apply IHle. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: le_trans *)

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* ADMITTED *)
  induction n as [| n'].
  - (* n = 0 *)
    apply le_n.
  - (* n = S n' *)
    apply le_S. apply IHn'. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: O_le_n *)

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  (* ADMITTED *)
  intros n m H. induction H.
  - (* le_n *)
    apply le_n.
  - (* le_S *)
    apply le_S. apply IHle.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: n_le_m__Sn_le_Sm *)

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  (* ADMITTED *)
  intros n m H.
  inversion H.
  - (* le_n *)
    apply le_n.
  - (* le_S *)
    apply (le_trans _ (S n) _).
    + apply le_S. apply le_n.
    + apply H1. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: Sn_le_Sm__n_le_m *)

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  (* ADMITTED *)
  intros a b. induction a as [| a'].
  - (* a = 0 *)
    apply O_le_n.
  - (* a = S a' *)
    apply n_le_m__Sn_le_Sm in IHa'. apply IHa'. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: le_plus_l *)
(** [] *)

(* EX2! (plus_le_facts1) *)

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
 (* ADMITTED *)
  intros n1 n2 m H. destruct H as [ | m' Hm'].
  - split.
    + apply le_plus_l.
    + rewrite add_comm. apply le_plus_l.
  - split.
    + apply le_trans with (n := n1 + n2).
      * apply le_plus_l.
      * apply le_S. apply Hm'.
    + apply le_trans with (n := n1 + n2).
      * rewrite add_comm. apply le_plus_l.
      * apply le_S. apply Hm'.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: plus_le *)

Theorem plus_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
  (** Hint: May be easiest to prove by induction on [n]. *)
Proof.
(* ADMITTED *)
  intros n. induction n.
  - intros m p q H.
    left.
    apply O_le_n.
  - intros m p q H.
    destruct p.
    + right.
      apply plus_le in H. destruct H as [_ H]. apply H.
    + simpl in H.
      apply Sn_le_Sm__n_le_m in H.
      apply IHn in H.
      destruct H as [ H1 | H2].
      * left. apply n_le_m__Sn_le_Sm. apply H1.
      * right. apply H2. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: plus_le_cases *)
(** [] *)

(* EX2! (plus_le_facts2) *)

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  (* ADMITTED *)
  intros n m p H.
  induction p.
  - simpl. apply H.
  - simpl. apply n_le_m__Sn_le_Sm. apply IHp.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: plus_le_compat_l *)

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  (* ADMITTED *)
  intros n m p H.
  rewrite add_comm.
  rewrite (add_comm m).
  apply plus_le_compat_l.
  apply H.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: plus_le_compat_r *)

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  (* ADMITTED *)
  intros n m p H.
  induction p.
  - simpl. rewrite (add_comm m). apply H.
  - rewrite (add_comm m). simpl. apply le_S. rewrite add_comm. apply IHp.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: le_plus_trans *)
(** [] *)


(* EX3? (lt_facts) *)
Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  (* ADMITTED *)
  intros n. unfold lt, ge.
  induction n.
  - intros m. destruct m.
    + right.
      apply le_n.
    + left.
      apply le_n_S.
      apply le_0_n.
  - intros m. destruct m.
    + right.
      apply le_0_n.
    + destruct (IHn m) as [IH | IH].
      * left.
        apply le_n_S, IH.
      * right.
        apply le_n_S, IH.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1.5: lt_ge_cases *)


Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  (* ADMITTED *)
  unfold lt. intros. apply Sn_le_Sm__n_le_m. apply le_S. apply H. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: n_lt_m__n_le_m *)

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
(* ADMITTED *)
  unfold lt. intros n1 n2 m H. split.
  - apply le_trans with (n := S (n1 + n2)).
    + simpl. rewrite <- plus_Sn_m. apply le_plus_l.
    + apply H.
  - apply le_trans with (n := S (n1 + n2)).
    + rewrite add_comm. rewrite <- plus_Sn_m. apply le_plus_l.
    + apply H.
Qed.
(* /ADMITTED *)
(* HIDE *)
(* old version of previous proof.
 (* ADMITTED *)
  intros n1 n2 m H. induction H.
  - (* le_n *)
    split.
    + apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + rewrite add_comm. apply n_le_m__Sn_le_Sm. apply le_plus_l.
  - (* le_S *)
    inversion IHle as [Hn1m Hn2m].
    apply le_S in Hn1m. apply le_S in Hn2m.
    split.
    + apply Hn1m.
    + apply Hn2m.  Qed.
(* /ADMITTED *)
*)
(* /HIDE *)
(* GRADE_THEOREM 1: plus_lt *)
(** [] *)

(* EX4? (leb_le) *)
Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  (* ADMITTED *)
  intros n.
  induction n as [| n'].
  - (* n = 0 *) intros m H.
    apply O_le_n.
  - (* n = S n' *) intros m H.
    simpl in H. destruct m as [| m'].
    + (* m = 0 *)
      discriminate.
    + (* m = S m' *)
      apply IHn' in H.
      apply n_le_m__Sn_le_Sm.
      apply H. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: leb_complete *)

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  (* ADMITTED *)
  intros n. induction n as [|n' IHn'].
  - (* n = 0 *)
    intros m H.
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. intros [|m'].
    + inversion 1.
    + intros H.
      apply IHn'.
      apply le_S_n.
      apply H. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: leb_correct *)

(** Hint: The next two can easily be proved without using [induction]. *)

(* LATER: AC'21: To me what would be interesting for this last lemma [leb_iff]
   would be to show that the proofs of completeness and correctness can
   be carried out in a single induction. *)

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  (* ADMITTED *)
  intros n m. split.
  - apply leb_complete.
  - apply leb_correct.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: leb_iff *)

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  (* ADMITTED *)
  intros n m o. rewrite leb_iff. rewrite leb_iff. rewrite leb_iff.
  apply le_trans.
Qed.
(* /ADMITTED *)
(* HIDE *)
(* old version of previous proof.
 (* ADMITTED *)
  intros n m o P Q.
  apply leb_complete in P. apply leb_complete in Q.
  apply leb_correct.
  apply le_trans with m.  apply P. apply Q. Qed.
(* /ADMITTED *)
*)
(* /HIDE *)
(* GRADE_THEOREM 1: leb_true_trans *)
(** [] *)

(* LATER: Another potential exercise:  m <= n --> n = m+(n-m).
   See p. 188 in CoqArt. *)

Module R.

(* EX3M! (R_provability) *)
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
  | c1                                     : R 0     0     0
  | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
  | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
  | c5 m n o (H : R m     n     o        ) : R n     m     o.

(* HIDE: APT 21: Reformatted the above after a student with dyslexia
   complained. But the effect is still lost in the HTML.  He also
   noted that the kind of question that follows doesn't really require
   a high-arity relation.

   MRC 3/22: I believe that violates the OCaml Community Guidelines on
   indentation.

   https://ocaml.org/learn/tutorials/guidelines.html#Bad-indentation-of-pattern-matching-constructs

   Whether those are applicable here is a matter of debate. But
   torquing the entire textbook into this mode of alignment does not
   seem any more desirable to me than torquing an OCaml codebase.

   BCP 25: No, but for this specific problem it seems OK. Let's leave
   it like this. *)

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer. *)

(* SOLUTION *)
(**
   - The first proposition is provable and the second is not.
     The proof term for the first is:
[[
       (c3 _ _ _ (c2 _ _ _ c1)).
]]
   - Dropping [c5] would not change the set of provable
     propositions.  [c4] and [c1] don't interact with [c5], since
     they're already symmetric in [m] and [n]; [c2] followed by
     [c5] is equivalent to [c3], and vice versa.

   - Dropping [c4] would not change the set of provable
     propositions. This constructor just "undoes" one application
     of [c2] and one application of [c3]. More precisely, the
     only way we can construct evidence for [R (S m) (S n) (S (S o))]
     is by applying [c2] and [c3] (in either order) to evidence for
     [R m n o], so the latter must already hold. (This can be proved
     by induction, although the proof is surprisingly tedious.) *)
(* /SOLUTION *)

(* HIDE *)
    (* Here is such a proof for posterity. *)

    Inductive R' : nat -> nat -> nat -> Prop :=
      | c1' : R' 0 0 0
      | c2' m n o (H : R' m n o) : R' (S m) n (S o)
      | c3' m n o (H : R' m n o) : R' m (S n) (S o).

    Ltac inv H := inversion H; subst; clear H.

    Lemma c5_redundant: forall m n o, R' m n o -> R' n m o.
    Proof.
      intros m n o H.
      induction H.
      - apply c1'.
      - apply c3'; auto.
      - apply c2'; auto.
    Qed.

    Lemma c4_redundant: forall m n o, R' (S m) (S n) (S(S o)) -> R' m n o.
    Proof.
      (* This one is nastier than one might expect. *)
      assert (Q1: forall m n o, R' (S m) n (S o) -> R' m n o).
      { induction n; intros.
        - inv H.  apply H3.
        - inv H.
          + apply H3.
          + destruct o.
            * inv H3.
            * apply c3'. apply IHn. apply H3.
      }
      assert (Q2: forall m n o, R' m (S n) (S o) -> R' m n o).
      { induction m; intros.
        - inv H. apply H3.
        - inv H.
          + destruct o.
            * inv H3.
            * apply c2'.  apply IHm. apply H3.
          + apply H3.
      }
      intros.
      inv H.
      - apply Q2; apply H3.
      - apply Q1; apply H3.
    Qed.

    Lemma R_R': forall m n o, R m n o <-> R' m n o.
    Proof.
      split; intros.
      -  induction H.
        + apply c1'.
        + apply c2'; auto.
        + apply c3'; auto.
        + apply c4_redundant; auto.
        + apply c5_redundant; auto.
      - induction H.
        + apply c1.
        + apply c2; auto.
        + apply c3; auto.
    Qed.
(* /HIDE *)

(* GRADE_MANUAL 3: R_provability *)
(** [] *)

(* EX3? (R_fact) *)
(** The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Rocq. *)

Definition fR : nat -> nat -> nat
  (* ADMITDEF *) :=
  plus.
(* /ADMITDEF *)

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
(* ADMITTED *)
  intros m n o.
  split.
  - intros H. induction H.
    + (* c1 *) reflexivity.
    + (* c2 *) simpl. rewrite IHR. reflexivity.
    + (* c3 *) rewrite <- plus_n_Sm. unfold fR in IHR. rewrite IHR. reflexivity.
    + (* c4 *) simpl in IHR. rewrite <- plus_n_Sm in IHR.
      injection IHR as Hmno. rewrite <- Hmno. reflexivity.
    + (* c5 *) rewrite add_comm. apply IHR.
  - generalize dependent n. generalize dependent m.
    induction o as [|o'].
    + (* o = 0 *)
      intros m n H.
      destruct m as [|m'].
      * (* m = 0 *)
        simpl in H. rewrite -> H. apply c1.
      * (* m = S m' *)
        inversion H.
    + (* o = S o' *)
      intros m n H. destruct m as [|m'].
      * (* m = 0 *)
        simpl in H. rewrite -> H. apply c3. apply IHo'.
        reflexivity.
      * (* m = S m' *)
        apply c2. apply IHo'. inversion H. reflexivity.
Qed.

(* HIDE: And here's a somewhat nicer version using some automation,
   but we haven't covered that yet...

From Stdlib Require Import Lia.

Theorem R_plus: forall m n o, R m n o <-> m + n = o.
Proof.
  intros m n o; split; intros.
  - induction H; try reflexivity; try lia.
  - generalize dependent n. generalize dependent m.
    induction o as [|o']; intros m n H.
    + destruct m; try inversion H.
      destruct n; try inversion H0.
      apply c1.
    + destruct m as [|m'].
      * destruct n; try inversion H. apply c3.
        apply IHo'. reflexivity.
      * apply c2. apply IHo'. lia.
Qed.
*)
(* /ADMITTED *)
(** [] *)

End R.

(* EX4A (subsequence) *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
[[
      [1;2;3]
]]
    is a subsequence of each of the lists
[[
      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]
]]
    but it is _not_ a subsequence of any of the lists
[[
      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].
]]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence.  There are a number
      of correct ways to do this. You should make sure that your
      definition behaves correctly on all the positive and negative
      examples above, but you do not need to prove this formally.

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Harder) Prove [subseq_trans] that subsequence is transitive --
      that is, if [l1] is a subsequence of [l2] and [l2] is a
      subsequence of [l3], then [l1] is a subsequence of [l3]. *)
(* HIDE *)
(* SOONER: (BCP'20) One of my students this semester pointed out
   that there is another definition that is intuitively perhaps just
   as reasonable and that makes these properties either easy or
   trivial: *)
Inductive subseq' : list nat -> list nat -> Prop :=
  | subseq'_0 (l: list nat):
      subseq' l l
  | subseq'_inductive1 l (l1 l2 lx ly lz: list nat)
      (H: subseq' l (l1 ++ l2)):
      subseq' l (lx ++ l1 ++ ly ++ l2 ++ lz)
  | subseq'_inductive2 (l1 l2 l3: list nat)
      (H1: subseq' l1 l2)
      (H2: subseq' l2 l3):
    subseq' l1 l3.
(* SOONER: MRC 3/22: It's MUCH worse than that! a total relation
   suffices! (BCP 25: Really? It gets all the positive examples above,
   obviously, but not the negative ones... right?) Also this is
   another case where a [Fixpoint] would suffice instead of an
   inductively-defined proposition: [subseq] is definable as a
   structurally recursive function. *)
(* SOONER: FSR'25 - This definition of subseq also works, though it requires a
   lemma mirroring subseq_app that allows prepending an excess list.
   Notably, this only has two cases, in spite of the hint above.
   (BCP 25: Removed the hint.) *)
Inductive subseq'' : list nat -> list nat -> Prop :=
  | sub_nil'' (l: list nat):
      subseq'' [] l
  | sub_cons'' (l l' l0: list nat) (x : nat)
      (H: subseq'' l l'):
      subseq'' (x :: l) (l0 ++ (x :: l')).
(* /HIDE *)
(* SOONER: AC'21: I think that it is more atomic to consider
   [sub_nil : subseq [] []]. The benefits is that it makes calls to
   [inversion] produce fewer goals. The downside is that one has to
   state as a lemma [sub_nil_l : forall l, subseq [] l], however it
   would be nice to have this as an exercise anyway, because otherwise
   students who go for the definition of [sub_seq [] []] are required
   to guess the need for [sub_nil_l].
   BCP: I agree this version could be nicer to suggest, and I agree that
   adding this lemma as a warm-up exercise is nice. *)
(* SOONER: Sainati 25: I am generally not against proofs that can be
   made much easier with smart inductive definitions (this is sort of the
   whole ball game in a way, isn't it?) but one way to make sure students
   can't trivialize the exercise is to just give them the definition we
   want them to use? We could also add a (maybe optional) question
   afterwards to provide a different definition that makes the proofs
   easier (and maybe prove them equivalent). *)

Inductive subseq : list nat -> list nat -> Prop :=
(* SOLUTION *)
  | sub_nil  l : subseq [] l
  | sub_take x l1 l2 (H : subseq l1 l2) : subseq (x :: l1) (x :: l2)
  | sub_skip x l1 l2 (H : subseq l1 l2) : subseq l1 (x :: l2)
(* /SOLUTION *)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  (* ADMITTED *)
  induction l as [|x l'].
  - (* l = [] *) apply sub_nil.
  - (* l = x :: l' *) apply sub_take. apply IHl'.
Qed.
(* /ADMITTED *)

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  (* ADMITTED *)
  intros l1 l2 l3 H.
  induction H.
    - (* sub_nil *) apply sub_nil.
    - (* sub_take *) simpl. apply sub_take. apply IHsubseq.
    - (* sub_skip *) simpl. apply sub_skip. apply IHsubseq.
Qed.
(* /ADMITTED *)

(* HIDE: AC'21: this exercise should probably be marked as more
   challenging.  In particular, it's not necessarily obvious at first
   sight that the induction should go on the second hypothesis, and
   with [l1] generalized.  BCP 21: Made it 3 points instead of 2, and
   included a hint. CH'23: Made it 4 points, since there are 5 different
   choices here and the hint doesn't help with that. *)
Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  (* Hint: be careful about what you are doing induction on and which
     other things need to be generalized... *)
  (* ADMITTED *)
  intros l1 l2 l3 S12 S23. generalize dependent l1.
  induction S23 as [|x l2 l3 |x l2 l3].
   - (* sub_nil *)
    intros l1 S12. inversion S12. apply sub_nil.
   - (* sub_take *)
    intros l1 S12.  inversion S12.
        apply sub_nil.
        apply sub_take. apply IHS23. apply H1.
        apply sub_skip. apply IHS23. apply H1.
   - (* sub_skip *)
    intros l1 S12. apply sub_skip. apply IHS23. apply S12.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: subseq_refl *)
(* GRADE_THEOREM 2: subseq_app *)
(* GRADE_THEOREM 3: subseq_trans *)
(** [] *)

(* EX2M? (R_provability2) *)
(** Suppose we give Rocq the following definition:
[[
    Inductive R : nat -> list nat -> Prop :=
      | c1                    : R 0     []
      | c2 n l (H: R n     l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n     l.
]]
    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(* LATER: APT: As in R_provability, above, would be good
   to get this formatting into the HTML version. *)

(* SOLUTION *)
(** The first two are provable; the third is not.

    In case this question puzzled you, one good way to understand
    definitions like this is to explore their implications with
    concrete examples, e.g.
[[
      R 0 []        by c1
      R 1 [0]       by c2 using R 0 []
      R 2 [1;0]     by c2 using R 1 [0]
      R 3 [2;1;0]   by c2 using R 2 [1;0]
      R 2 [2;1;0]   by c3 using R 3 [2;1;0]
      R 1 [2;1;0]   by c3 using R 2 [2;1;0]
      R 2 [1;2;1;0] by c2 using R 1 [2;1;0]
      R 1 [1;2;1;0] by c3 using R 2 [1;2;1;0]
      etc.
]]
    If you do a few more of these yourself, you should see the pattern
    emerging. *)
(* /SOLUTION *)
(** [] *)

(* HIDE *)
    (* Under construction... *)
    Definition partition {X : Type} (test : X -> bool) (l : list X) :=
      (filter test l, filter (fun x => negb (test x)) l) .

    (* LATER: Adjust inductive syntax *)
    Inductive shuffle (X:Type) : list X -> list X -> list X -> Prop :=
      | shuffle_nil_l : forall (l2:list X), shuffle _ [] l2 l2
      | shuffle_nil_r : forall (l1:list X), shuffle _ l1 [] l1
      | shuffle_cons_l : forall (x:X) (l1 l2 l12 : list X),
                          shuffle _ l1 l2 l12 ->
                          shuffle _ (x::l1) l2 (x::l12)
      | shuffle_cons_r : forall (x:X) (l1 l2 l12: list X),
                          shuffle _ l1 l2 l12 ->
                          shuffle _ l1 (x::l2) (x::l12).

    Arguments shuffle [X] _ _ _.

    (* HIDE: If they do this proof, they'll see some uses of [fix]... *)
    (* HIDE: M: I don't understand the above remark. This proof, though
      somewhat messy, can be done with everything they've seen so far.
      In any case, I attempt a proof, which is arguably the same as the
      old one. *)

    Theorem partition_correct_1 : forall (X:Type) (l l1 l2: list X) (test:X -> bool),
      partition test l = (l1,l2) ->
      shuffle l1 l2 l.
    Proof.
      intros X l l1 l2 test H. generalize dependent l2. generalize dependent l1.
      induction l as [| x l' ].
      - (* l = [] *)
        intros. inversion H. apply shuffle_nil_l.
      - (* l = x :: l' *)
        intros. destruct (test x) eqn:Heqb.
          + (* true = test x *)
            inversion H.
            rewrite Heqb in H1. rewrite Heqb in H2. rewrite  Heqb.
            simpl in H2. simpl.
            apply shuffle_cons_l. apply IHl'. reflexivity.
          + (* false = test x *)
            inversion H.
            rewrite Heqb in H1. rewrite Heqb in H2. rewrite Heqb.
            simpl in H2. simpl.
            apply shuffle_cons_r. apply IHl'. reflexivity.
    Qed.

    (* The old proof is longer (in number of lines), but I cheat.
      And the old proof uses more [destruct]s.
      Thus, the new proof above is better in at least two quantifiable
      ways, but I'm afraid its not entirely clean yet. *)

    (*  intros X l l1 l2 test H. generalize dependent l2.
      generalize dependent l1.
      induction l as [|x l'].
      - (* l = [] *)
        intros.
        unfold partition in H.
        unfold filter in H.
        inversion H.
        apply shuffle_nil_l.
      - (* l = x::l' *)
        intros.
        unfold partition in H. unfold filter in H.
        remember (test x) as H1.
        destruct H1.
          + (* true *)
            simpl in H.
            destruct l1.
            * (* nil *)
              inversion H.
            * (* cons *)
              inversion H. subst.
              apply shuffle_cons_l.
              apply IHl'.
              unfold partition.
              unfold filter.
              reflexivity.
          + (* false *)
            simpl in H.
            destruct l2.
            * (* nil *)
              inversion H.
            * (* cons *)
              inversion H. subst.
              apply shuffle_cons_r.
              apply IHl'.
              unfold partition.
              unfold filter.
              reflexivity.
    Qed. *)

    (* LATER: The proof needs to be polished. *)
    (* LATER: Also needs to talk about the two lists respecting the
      partitioning condition.  We'd really like to say all three
      parts of the spec together, but we don't have /\ yet! *)
(* /HIDE *)

(* EX2? (total_relation) *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
  (* SOLUTION *)
  | tot n m : total_relation n m
(* /SOLUTION *)
.

Theorem total_relation_is_total : forall n m, total_relation n m.
  Proof.
  (* ADMITTED *)
  intros n m. apply tot. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: total_relation_is_total *)
(** [] *)

(* EX2? (empty_relation) *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

(* LATER: MRC'20: this exercise feels unsolvable given what students
   already know.  I don't believe we've ever shown them that an
   inductive type can have zero constructors, or what the syntax for
   that would be.  (That will come when we show them how to define
   False in ProofObjects.) Should a hint be added?

   BCP 20: Maybe not needed since it's optional anyway? But also,
   can't it be done with a inductive definition with nonzero cases but
   no base case?

   APT 21: Yes, although arguably that is even less obvious.
   MRC 3/22: And also something I can't recall we've shown them.

   MRC 3/22: [unsolvable /\ optional -> unsolvable]

   MTF 6/22: A solution that more than one of my students have submitted
   is using a "base" case with a built-in contradiction:
   [emp n m : 0 = 1 -> empty_relation n m] or
   [emp n m : False -> empty_relation n m].
   So, I do think that it is solvable given what students know.
 *)

Inductive empty_relation : nat -> nat -> Prop :=
  (* SOLUTION *)
(* /SOLUTION *)
.

Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
  Proof.
  (* ADMITTED *)
  intros n m H. destruct H. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: empty_relation_is_empty *)
(** [] *)

(* LATER:
     A nice exercise...
       - give them a datatype of binary trees
       - ask them to write a "size" function
       - make them write an inductively defined "balanced" property
       - maybe prove something about this property (this might be hard)?

    At some point, perhaps we can show them how propositions and data
    can get mixed together.  E.g., we can define a type of lists of
    numbers less than 10 (where each element carries a proof that it
    is less than 10).  Then we can go a step further and parameterize
    this definition over 10.  Similarly, we can define balanced binary
    trees of height exactly n. (See CoqArt p. 181.)  Show and discuss
    the induction principles for all of these.
*)
(* /FULL *)

(* ############################################################ *)
(** * Case Study: Regular Expressions *)

(** FULL: Many of the examples above were simple and -- in the case of
    the [ev] property -- even a bit artificial. To give a better sense
    of the power of inductively defined propositions, we now show how
    to use them to model a classic concept in computer science:
    _regular expressions_. *)

(** ** Definitions *)

(** Regular expressions are a natural language for describing sets of
    strings.  Their syntax is defined as follows: *)

(* HIDE: N.b. First argument is left explicit in the type (so we
   always have to say what the regular expression takes as elements)
   but not in the constructors. *)
Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

(* TERSE: HIDEFROMHTML *)
Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.
(* TERSE: /HIDEFROMHTML *)

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- which in this exercise we represent as _lists_ with
    elements from [T]. *)

(** FULL: (Technical aside: We depart slightly from standard practice in
    that we do not require the type [T] to be finite.  This results in
    a somewhat different theory of regular expressions, but the
    difference is not significant for present purposes.) *)

(** TERSE: *** *)
(** We connect regular expressions and strings by defining when a
    regular expression _matches_ some string.

    Informally this looks as follows:

      - The regular expression [EmptySet] does not match any string.

      - [EmptyStr] matches the empty string [[]].

      - [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2],
        then [App re1 re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s],
        then [Union re1 re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation
        of a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i],
        then [Star re] matches [s].

        In particular, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** TERSE: *** *)
(** We can easily translate this intuition into a set of rules,
    where we write [s =~ re] to say that [re] matches [s]:
[[[
                        -------------- (MEmpty)
                        [] =~ EmptyStr

                        --------------- (MChar)
                        [x] =~ (Char x)

                    s1 =~ re1     s2 =~ re2
                  --------------------------- (MApp)
                  (s1 ++ s2) =~ (App re1 re2)

                           s1 =~ re1
                     --------------------- (MUnionL)
                     s1 =~ (Union re1 re2)

                           s2 =~ re2
                     --------------------- (MUnionR)
                     s2 =~ (Union re1 re2)

                        --------------- (MStar0)
                        [] =~ (Star re)

                           s1 =~ re
                        s2 =~ (Star re)
                    ----------------------- (MStarApp)
                    (s1 ++ s2) =~ (Star re)
]]]
*)

(** TERSE: *** *)
(** This directly corresponds to the following [Inductive] definition.
    We use the notation [s =~ re] in  place of [exp_match s re].
    (By "reserving" the notation before defining the [Inductive],
    we can use it in the definition.) *)
(* SOONER: We should explain the Reserved thing earlier, so it isn't
   piled on them here. *)
(* HIDE: Module Hide. *)

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR s2 re1 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

(* QUIZ *)
(** Notice that this clause in our informal definition...

      - "The expression [EmptySet] does not match any string."

    ... is not explicitly reflected in the above definition.  Do we
    need to add something?

   (A) Yes, we should add a rule for this.

   (B) No, one of the other rules already covers this case.

   (C) No, the _lack_ of a rule actually gives us the behavior we
       want.
*)
(* /QUIZ *)
(* HIDE *)
Lemma quiz : forall T (s:list T), ~(s =~ EmptySet).
Proof. intros T s Hc. inversion Hc. Qed.
(* /HIDE *)

(** FULL: Notice that these rules are not _quite_ the same as the
    intuition that we gave at the beginning of the section. First, we
    don't need to include a rule explicitly stating that no string is
    matched by [EmptySet]; indeed, the syntax of inductive definitions
    doesn't even _allow_ us to give such a "negative rule." We just
    don't happen to include any rule that would have the effect of
    [EmptySet] matching some string.

    Second, the intuition we gave for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    intuition but more convenient to use in Rocq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the intuition is indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

(** ** Examples *)

(** TERSE: *** *)
Example reg_exp_ex1 : [1] =~ Char 1.
(* FOLD *)
Proof.
  apply MChar.
Qed.
(* /FOLD *)

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
(* FOLD *)
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.
(* /FOLD *)

(** FULL: (Notice how the last example applies [MApp] to the string
    [[1]] directly.  Since the goal mentions [[1; 2]] instead of
    [[1] ++ [2]], Rocq wouldn't be able to figure out how to split
    the string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
(* FOLD *)
Proof.
  intros H. inversion H.
Qed.
(* /FOLD *)

(* FULL *)
(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the string that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
(* FOLD *)
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.
(* /FOLD *)
(* /FULL *)

(** FULL: We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] matched by [re]
    is also matched by [Star re]. *)
(** TERSE: *** *)
(** TERSE: Something more interesting: *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
(* FULL: FOLD *)
(* TERSE: WORKINCLASS *)
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.
(* FULL: /FOLD *)
(* TERSE: /WORKINCLASS *)

(** FULL: (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the shape expected by [MStarApp].) *)

(* FULL *)
(* EX3 (exp_match_ex1) *)
(* GRADE_THEOREM 0.5: EmptySet_is_empty *)
(* GRADE_THEOREM 0.5: MUnion' *)
(* GRADE_THEOREM 2: MStar' *)
(** The following lemmas show that the intuition about matching given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma EmptySet_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  (* ADMITTED *)
  intros T s H. inversion H. Qed.
(* /ADMITTED *)

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  (* ADMITTED *)
  intros T s re1 re2 [H | H].
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.
(* /ADMITTED *)

(** The next lemma is stated in terms of the [fold] function from the
    \CHAP{Poly} chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  (* ADMITTED *)
  intros T ss re H.
  induction ss as [|s ss' IH].
  - (* ss = [] *)
    simpl. apply MStar0.
  - (* ss = s :: ss' *)
    simpl. apply MStarApp.
    + apply H. left. reflexivity.
    + apply IH.
      intros s' H'. apply H. right. apply H'.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2? (EmptyStr_not_needed) *)
(** It turns out that the [EmptyStr] constructor is actually not
   needed, since the regular expression matching the empty string can
   also be defined from [Star] and [EmptySet]: *)
Definition EmptyStr' {T:Type} := @Star T (EmptySet).

(** State and prove that this [EmptyStr'] definition matches exactly
   the same strings as the [EmptyStr] constructor. *)

(* SOLUTION *)
Lemma empty_equiv : forall {T:Type} (s:list T),
  s =~ EmptyStr <-> s =~ EmptyStr'.
Proof.
  intros T s. split.
  - intro H. inversion H as [H0| | | | | |]. apply MStar0.
  - intro H. inversion H as [ | | | | | re Heqs Heqre|
                            s1 s2 re H1 H2 Heqs Heqre].
    + apply MEmpty.
    + inversion H1.
Qed.
(* /SOLUTION *)
(** [] *)
(* /FULL *)

(** FULL: Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)
(** TERSE: *** *)
(** TERSE: Naturally, proofs about [exp_match] often require
    induction (on evidence!). *)

(** For example, suppose we want to prove the following intuitive
    fact: If a string [s] is matched by a regular expression [re],
    then all elements of [s] must occur as character literals
    somewhere in [re].

    To state this as a theorem, we first define a function [re_chars]
    that lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(* TERSE *)
(* HIDEFROMHTML *)
(** This lemma from chapter \CHAP{Logic} will be useful in the proof. *)

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
(* FOLD *)
Proof.
  intros A l. induction l as [|a' l' IH].
  - intros l' a. simpl. split.
    + intros H. right. apply H.
    + intros [[]|H]. apply H.
  - intros l'' a. simpl. rewrite IH. rewrite or_assoc.
    reflexivity. Qed.
(* /FOLD *)
(* /HIDEFROMHTML *)
(* /TERSE *)

(** TERSE: *** *)

(** Now, the main theorem: *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKINCLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.

(** Something interesting happens in the [MApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which is matched by [re1]), and a second one that applies when [x]
    occurs in [s2] (matched by [re2]). *)

    rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.

(** Here again we get two induction hypotheses, and they illustrate
    why we need induction on evidence for [exp_match], rather than
    induction on the regular expression [re]: The latter would only
    provide an induction hypothesis for strings that match [re], which
    would not allow us to reason about the case [In x s2]. *)

    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.
(* /WORKINCLASS *)

(* FULL *)
(* EX4 (re_not_empty) *)
(* GRADE_THEOREM 3: re_not_empty *)
(* GRADE_THEOREM 3: re_not_empty_correct *)
(** Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool
  (* ADMITDEF *) :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App re1 re2 => (re_not_empty re1) && (re_not_empty re2)
  | Union re1 re2 => (re_not_empty re1) || (re_not_empty re2)
  | Star re => true
  end.
(* /ADMITDEF *)

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  (* ADMITTED *)
  intros T re.
  induction re as [| |x|re1 IH1 re2 IH2
                   |re1 IH1 re2 IH2|re IH].
  - (* EmptySet *)
    simpl. split.
    + intros [s contra]. inversion contra.
    + intros H. discriminate.
  - (* EmptyStr *)
    simpl. split.
    + intros _. reflexivity.
    + exists []. apply MEmpty.
  - (* Char *)
    simpl. split.
    + intros _. reflexivity.
    + exists [x].
      apply MChar.
  - (* App *)
    simpl.
    rewrite andb_true_iff.
    split.
    + intros [s H].
      inversion H. split.
      * apply IH1. exists s1. apply H3.
      * apply IH2. exists s2. apply H4.
    + intros [H1 H2].
      apply IH1 in H1. destruct H1 as [s1 Hs1].
      apply IH2 in H2. destruct H2 as [s2 Hs2].
      exists (s1 ++ s2). apply (MApp _ _ _ _ Hs1 Hs2).
  - (* Union *)
    simpl.
    rewrite orb_true_iff.
    split.
    + intros [s H]. inversion H.
      * left. apply IH1. exists s. apply H2.
      * right. apply IH2. exists s. apply H1.
    + intros [H | H].
      * apply IH1 in H. destruct H as [s H].
        exists s. apply (MUnionL _ _ _ H).
      * apply IH2 in H. destruct H as [s H].
        exists s. apply (MUnionR _ _ _ H).
  - (* Star *)
    simpl. split.
    + intros _. reflexivity.
    + exists []. apply MStar0.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** ** The [remember] Tactic *)

(* HIDE: CH: Restoring flow in the slides given current FULL-ing *)
(** TERSE: Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)

(** HIDE: AAA: There is a [dependent induction] tactic that obviates
    the need for the [remember] + [induction] idiom. It's already
    discussed in some of the later chapters; perhaps we could just
    mention that instead of introducing [remember]?  BCP: Sounds like
    a fine idea.  Does [dependent induction] basically subsume
    [remember], or are there other applications of [remember]?  AAA:
    It could pretty much replace [remember], as we use it here.  The
    problem is that it doesn't seem to allow us to name the arguments
    as we want... BCP: Sigh.  OK, let's use [remember] for now. *)

(** One potentially confusing feature of the [induction] tactic is
    that it will let you try to perform an induction over a term that
    isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] without an [eqn:] clause can do),
    and leave you unable to complete the proof.  Here's an example: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** FULL: Now, just doing an [inversion] on [H1] won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence). Here is a naive first attempt. *)
(** TERSE: Here is a naive first attempt at setting up the
    induction. *)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** FULL: But now, although we get seven cases (as we would expect
    from the definition of [exp_match]), we have lost a very important
    bit of information from [H1]: the fact that [s1] matched something
    of the form [Star re].  This means that we have to give proofs for
    _all_ seven constructors of this definition, even though all but
    two of them ([MStar0] and [MStarApp]) are contradictory.  We can
    still get the proof to go through for a few constructors, such as
    [MEmpty]... *)

(** TERSE: *** *)
(** TERSE: We can get through the first case... *)

  - (* MEmpty *)
    simpl. intros H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show
[[
      s2     =~ Char x' ->
      x'::s2 =~ Char x'
]]
    which is clearly impossible. *)

  - (* MChar. *) intros H. simpl. (* Stuck... *)
Abort.

(** TERSE: *** *)
(** The problem here is that [induction] over a Prop hypothesis only
    works properly with hypotheses that are "fully general," i.e.,
    ones in which all the arguments are just variables, as opposed to more
    specific expressions like [Star re].

(* FULL *)
    (In this respect, [induction] on evidence behaves more like
    [destruct]-without-[eqn:] than like [inversion].)

(* /FULL *)
    A possible, but awkward, way to solve this problem is "manually
    generalizing" over the problematic expressions by adding
    explicit equality hypotheses to the lemma: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** FULL: We can now proceed by performing induction over evidence
    directly, because the argument to the first hypothesis is
    sufficiently general, which means that we can discharge most cases
    by inverting the [re' = Star re] equality in the context. *)
(** This works, but it makes the statement of the lemma a bit ugly.
    Fortunately, there is a better way... *)
Abort.

(** TERSE: *** *)
(** The tactic [remember e as x eqn:Eq] causes Rocq to (1) replace all
    occurrences of the expression [e] by the variable [x], and (2) add
    an equation [Eq : x = e] to the context.  Here's how we can use it
    to show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re' eqn:Eq.

(** We now have [Eq : re' = Star re]. *)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** TERSE: *** *)
(** The [Eq] is contradictory in most cases, allowing us to
    conclude immediately. *)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** The interesting cases are those that correspond to [Star]. *)

  - (* MStar0 *)
    intros H. apply H.

  - (* MStarApp *)
    intros H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * apply Eq.
      * apply H1.

(** Note that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re], which
    results from the equality generated by [remember]. *)
Qed.

(** TERSE: *** *)
(** TERSE: The remainder of this section in the full version of the chapter
    develops an extended exercise on regular expressions, leading up
    to a proof of the well-known "pumping lemma."

    Informally, this lemma states that any sufficiently long string
    [s] matching a regular expression [re] can be "pumped" by
    repeating some middle section of [s] an arbitrary number of times
    to produce a new string also matching [re]. *)

(* FULL *)
(* EX4? (exp_match_ex2) *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  (* ADMITTED *)
  intros T s re H. remember (Star re) as re' eqn:Eq.
  induction H
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)  discriminate Eq.
  - (* MChar *)   discriminate Eq.
  - (* MApp *)    discriminate Eq.
  - (* MUnionL *) discriminate Eq.
  - (* MUnionR *) discriminate Eq.
  - (* MStar0 *)
    exists []. simpl. split.
    + reflexivity.
    + intros s [].
  - (* MStarApp *)
    inversion Eq as [Eq']. clear IH1.
    apply IH2 in Eq. destruct Eq as [ss [IH2fold IH2In]].
    exists (s1::ss). simpl. split.
    + f_equal. apply IH2fold.
    + intro s. intros [H | H].
      * subst. apply Hmatch1.
      * apply IH2In. apply H.
Qed.
(* /ADMITTED *)
(** [] *)

(** ** The "Weak" Pumping Lemma *)

(** One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].  For the sake of simplicity, this
    exercise considers a slightly weaker theorem than is usually
    stated in courses on automata theory -- hence the name
    [weak_pumping].  The stronger one can be found below.

    To get started, we need to define "sufficiently long."  Since we
    are working in a constructive logic, we actually need to be able
    to _calculate_, for each regular expression [re], a minimum length
    for strings [s] to guarantee "pumpability." *)

(* HIDE *)
(* Needed for hidden stuff below *)
From Stdlib Require Import Lia.
(* /HIDE *)
Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

(** You may find these lemmas about the pumping constant useful when
    proving the pumping lemma below. *)

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
(* FOLD *)
Proof.
  intros T re. induction re.
  - (* EmptySet *)
    apply le_n.
  - (* EmptyStr *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* App *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Union *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Star *)
    simpl. apply IHre.
Qed.
(* /FOLD *)

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
(* FOLD *)
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  rewrite H in Hp1. inversion Hp1.
Qed.
(* /FOLD *)

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

(** This auxiliary lemma might also be useful in your proof of the
    pumping lemma. *)

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
(* FOLD *)
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.
(* /FOLD *)

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
(* FOLD *)
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.
(* /FOLD *)

(** The (weak) pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3], will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

(** This proof is quite long, so to make it more tractable we've
    broken it up into a number of sub-proofs, which we then assemble
    to prove the main lemma.

    Your job is to complete the proofs of the helper lemmas; the main
    lemma relies on these. Several of the lemmas about [le] that were
    in an optional exercise earlier in this chapter may be useful here
    -- in particular, [lt_ge_cases] and [plus_le]. *)

(* EX2 (weak_pumping_char) *)
Lemma weak_pumping_char : forall (T : Type) (x : T),
  pumping_constant (Char x) <= length [x] ->
  exists s1 s2 s3 : list T,
    [x] = s1 ++ s2 ++ s3 /\
    s2 <> [ ] /\
    (forall m : nat, s1 ++ napp m s2 ++ s3 =~ Char x).
Proof.
  (* ADMITTED *)
  simpl. intros T x contra. inversion contra. inversion H0.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (weak_pumping_app) *)
Lemma weak_pumping_app : forall (T : Type)
                         (s1 s2 : list T) (re1 re2 : reg_exp T),
  s1 =~ re1 ->
  s2 =~ re2 ->
  (pumping_constant re1 <= length s1 ->
  exists s2 s3 s4 : list T,
    s1 = s2 ++ s3 ++ s4 /\
    s3 <> [ ] /\
    (forall m : nat, s2 ++ napp m s3 ++ s4 =~ re1)) ->
  (pumping_constant re2 <= length s2 ->
    exists s1 s3 s4 : list T,
      s2 = s1 ++ s3 ++ s4 /\
      s3 <> [ ] /\
      (forall m : nat, s1 ++ napp m s3 ++ s4 =~ re2)) ->
  pumping_constant (App re1 re2) <= length (s1 ++ s2) ->
  exists s0 s3 s4 : list T,
    s1 ++ s2 = s0 ++ s3 ++ s4 /\
    s3 <> [ ] /\
    (forall m : nat, s0 ++ napp m s3 ++ s4 =~ App re1 re2).
Proof.
  simpl. intros T s1 s2 re1 re2 Hmatch1 Hmatch2 IH1 IH2 Hlen.
  assert (H : pumping_constant re1 <= length s1 \/
              pumping_constant re2 <= length s2).
  {
    (* ADMIT *)
    rewrite app_length in Hlen.
    apply plus_le_cases. apply Hlen.
    (* /ADMIT *)
  }
  (* ADMITTED *)
  destruct H as [H | H].
  + destruct (IH1 H) as [s11 [s12 [s13 [H1 [H2 H3]]]]].
    rewrite H1.
    exists s11. exists s12. exists (s13 ++ s2).
    rewrite <- app_assoc, <- app_assoc.
    split. { reflexivity. }
    split. { apply H2. }
    intros m.
    rewrite app_assoc, app_assoc. apply MApp.
    * rewrite <- app_assoc. apply H3.
    * apply Hmatch2.
  + destruct (IH2 H) as [s21 [s22 [s23 [H1 [H2 Hnapp]]]]].
    rewrite H1.
    exists (s1 ++ s21). exists s22. exists s23.
      rewrite <- app_assoc.
      split. { reflexivity. }
      split. { apply H2. }
      intros m.
      rewrite <- app_assoc. apply MApp.
      * apply Hmatch1.
      * apply Hnapp.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (weak_pumping_union_l) *)
Lemma weak_pumping_union_l : forall T (s1 : list T) (re1 re2 : reg_exp T),
  s1 =~ re1 ->
  (pumping_constant re1 <= length s1 ->
    exists s2 s3 s4 : list T,
      s1 = s2 ++ s3 ++ s4 /\
      s3 <> [ ] /\
      (forall m : nat, s2 ++ napp m s3 ++ s4 =~ re1)) ->
  pumping_constant (Union re1 re2) <= length s1 ->
  exists s0 s2 s3 : list T,
    s1 = s0 ++ s2 ++ s3 /\
    s2 <> [ ] /\
    (forall m : nat, s0 ++ napp m s2 ++ s3 =~ Union re1 re2).
Proof.
  simpl. intros T s1 re1 re2 Hmatch IH Hlen.
  assert (H : pumping_constant re1 <= length s1).
  {
    (* ADMIT *)
    apply (plus_le _ _ _ Hlen).
    (* /ADMIT *)
  }
  (* ADMITTED *)
  destruct (IH H) as [s11 [s12 [s13 [H1 [H2 Hnapp]]]]].
  exists s11. exists s12. exists s13. split. { apply H1. }
  split. { apply H2. }
  intros m. apply MUnionL. apply Hnapp.
Qed.
(* /ADMITTED *)
(** [] *)

Lemma weak_pumping_union_r : forall T (s2 : list T) (re1 re2 : reg_exp T),
  s2 =~ re2 ->
  (pumping_constant re2 <= length s2 ->
    exists s1 s3 s4 : list T,
      s2 = s1 ++ s3 ++ s4 /\
      s3 <> [ ] /\
      (forall m : nat, s1 ++ napp m s3 ++ s4 =~ re2)) ->
  pumping_constant (Union re1 re2) <= length s2 ->
  exists s1 s0 s3 : list T,
    s2 = s1 ++ s0 ++ s3 /\
    s0 <> [ ] /\
    (forall m : nat, s1 ++ napp m s0 ++ s3 =~ Union re1 re2).
Proof.
  (* Symmetric to the previous... *)
  (* ADMITTED *)
  simpl. intros T s2 re1 re2 Hmatch IH Hlen.
  assert (H : pumping_constant re2 <= length s2).
  {
    rewrite add_comm in Hlen.
    apply (plus_le _ _ _ Hlen).
  }
  destruct (IH H) as [s21 [s22 [s23 [H1 [H2 Hnapp]]]]].
  exists s21. exists s22. exists s23. split. { apply H1. }
  split. { apply H2. }
  intros m. apply MUnionR. apply Hnapp.
Qed.
(* /ADMITTED *)

(* EX2? (weak_pumping_star_zero) *)
Lemma weak_pumping_star_zero : forall T (re : reg_exp T),
  pumping_constant (Star re) <= @length T [] ->
  exists s1 s2 s3 : list T,
    [ ] = s1 ++ s2 ++ s3 /\
    s2 <> [ ] /\
    (forall m : nat, s1 ++ napp m s2 ++ s3 =~ Star re).
Proof.
  (* ADMITTED *)
  simpl. intros T re Hp. inversion Hp as [|Hp0].
  apply pumping_constant_0_false in H. inversion H.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX4? (weak_pumping_star_app) *)
(** (You may also want the [plus_le_cases] lemma here.) *)

Lemma weak_pumping_star_app : forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ re ->
  s2 =~ Star re ->
  (pumping_constant re <= length s1 ->
    exists s2 s3 s4 : list T,
      s1 = s2 ++ s3 ++ s4
      /\ s3 <> [ ] /\
      (forall m : nat, s2 ++ napp m s3 ++ s4 =~ re)) ->
  (pumping_constant (Star re) <= length s2 ->
    exists s1 s3 s4 : list T,
      s2 = s1 ++ s3 ++ s4 /\
      s3 <> [ ] /\
      (forall m : nat, s1 ++ napp m s3 ++ s4 =~ Star re)) ->
  pumping_constant (Star re) <= length (s1 ++ s2) ->
  exists s0 s3 s4 : list T,
    s1 ++ s2 = s0 ++ s3 ++ s4 /\
    s3 <> [ ] /\
    (forall m : nat, s0 ++ napp m s3 ++ s4 =~ Star re).
Proof.
  simpl. intros T s1 s2 re Hmatch1 Hmatch2 IH1 IH2 Hlen.
  rewrite app_length in *.
  assert (Hs1re1 : length s1 = 0
                \/ (length s1 <> 0 /\ length s1 < pumping_constant re)
                \/ pumping_constant re <= length s1).
  {
    destruct s1 as [| h s1'].
    - (* ADMIT *)
    left. reflexivity.
    (* /ADMIT *)
    - (* ADMIT *) right.
      assert (Hcases : length (h :: s1') < pumping_constant re
                    \/ pumping_constant re <= length (h :: s1')).
      { apply lt_ge_cases. }
      destruct Hcases as [Hlenlt | Hlengt].
      + left.
        split.
        * unfold not. intros contra. inversion contra.
        * apply Hlenlt.
      + right. apply Hlengt.
      (* /ADMIT *)
  }
  (* ADMITTED *)
  destruct Hs1re1 as [Hs1len0 | [[Hs1len Hs1re1] | Hs1re1]].
  + assert (Hs1nil : s1 = []).
    { destruct s1. reflexivity. inversion Hs1len0. }
    subst. simpl in *. apply IH2. apply Hlen.
  + exists [], s1, s2. simpl in *.
    split. reflexivity.
    split.
    { unfold not. intros Hs1nil. subst.
      unfold not in Hs1len. apply Hs1len.
      reflexivity.
    }

    intros m. apply napp_star.
    * apply Hmatch1.
    * apply Hmatch2.
  + destruct (IH1 Hs1re1) as [s11 [s12 [s13 [H1 [H2 Hnapp]]]]].
    exists s11, s12, (s13 ++ s2).
    split.
    { subst. rewrite <- app_assoc. rewrite <- app_assoc.
      reflexivity. }
    split.
    { apply H2. }

    intros m.
    rewrite -> app_assoc.
    rewrite -> app_assoc.
    apply MStarApp.
    * rewrite <- app_assoc. apply Hnapp.
    * apply Hmatch2.
Qed.
(* /ADMITTED *)
(** [] *)

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - apply weak_pumping_char.
  - apply weak_pumping_app; assumption.
  - apply weak_pumping_union_l; assumption.
  - apply weak_pumping_union_r; assumption.
  - apply weak_pumping_star_zero.
  - apply weak_pumping_star_app; assumption.
Qed.

(** ** The (Strong) Pumping Lemma *)

(* EX5A? (pumping) *)
(* GRADE_THEOREM 10: Pumping.pumping *)
(** Now here is the usual version of the pumping lemma. In addition to
    requiring that [s2 <> []], it also strengthens the result to
    include the claim that [length s1 + length s2 <= pumping_constant
    re]. *)

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You may want to copy your proof of weak_pumping below. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  (* ADMITTED *)
  - (* MChar *)
    simpl. intros contra. inversion contra. inversion H0.
  - (* MApp *)
    simpl. intros Hlen.
    assert (H : pumping_constant re1 <= length s1 \/
                pumping_constant re2 <= length s2).
    { rewrite app_length in Hlen.
      apply plus_le_cases. apply Hlen. }
    destruct H as [H | H].
    + destruct (IH1 H) as [s11 [s12 [s13 [H1 [H2 H3]]]]].
      rewrite H1.
      exists s11. exists s12. exists (s13 ++ s2).
      rewrite <- app_assoc, <- app_assoc.
      split. { reflexivity. }
      split. { apply H2. }
      split. { destruct H3 as [Hlenp Hnapp]. apply le_plus_trans.
               apply Hlenp. }
      intros m.
      rewrite app_assoc, app_assoc. apply MApp.
      * rewrite <- app_assoc. apply H3.
      * apply Hmatch2.
    + (* now, either... length s1 < pumping_constant re,
         or pumping_constant <= length s1 *)
      assert (Hs1re1 : length s1 < pumping_constant re1
                       \/ pumping_constant re1 <= length s1).
      { apply lt_ge_cases. }

      destruct Hs1re1 as [Hs1re1 | Hs1re1].
      * destruct (IH2 H) as [s21 [s22 [s23 [H1 [H2 [Hlenp Hnapp]]]]]].
        rewrite H1.
        exists (s1 ++ s21). exists s22. exists s23.
        rewrite <- app_assoc.
        split. { reflexivity. }
        split. { apply H2. }
        split.
        { rewrite app_length in *.
          rewrite <- add_assoc.
          apply le_trans with (n:=length s1 + pumping_constant re2).
          + apply plus_le_compat_l. apply Hlenp.
          + apply plus_le_compat_r. apply n_lt_m__n_le_m. apply Hs1re1.
        }

        intros m.
        rewrite <- app_assoc. apply MApp.
        -- apply Hmatch1.
        -- apply Hnapp.

      * destruct (IH1 Hs1re1) as [s11 [s12 [s13 [H1 [H2 H3]]]]].
        rewrite H1.
        exists s11. exists s12. exists (s13 ++ s2).
        rewrite <- app_assoc, <- app_assoc.
        split. { reflexivity. }
        split. { apply H2. }
        split. { destruct H3 as [Hlenp Hnapp].
                 apply le_plus_trans. apply Hlenp. }
        intros m.
        rewrite app_assoc, app_assoc. apply MApp.
        -- rewrite <- app_assoc. apply H3.
        -- apply Hmatch2.
  - (* MUnionL *)
    simpl. intros Hlen.
    assert (H : pumping_constant re1 <= length s1).
    { apply (plus_le _ _ _ Hlen). }
    destruct (IH H) as [s11 [s12 [s13 [H1 [H2 [Hlenp Hnapp]]]]]].
    exists s11. exists s12. exists s13. split. { apply H1. }
    split. { apply H2. }
    split. { apply le_plus_trans. apply Hlenp. }
    intros m. apply MUnionL. apply Hnapp.
  - (* MUnionR *)
    simpl. intros Hlen.
    assert (H : pumping_constant re2 <= length s2).
    { rewrite add_comm in Hlen. apply (plus_le _ _ _ Hlen). }
    destruct (IH H) as [s21 [s22 [s23 [H1 [H2 [Hlenp Hnapp]]]]]].
    exists s21. exists s22. exists s23. split. { apply H1. }
    split. { apply H2. }
    split. { rewrite (add_comm (pumping_constant re1)).
             apply le_plus_trans. apply Hlenp. }
    intros m. apply MUnionR. apply Hnapp.
  - (* MStar0 *)
    simpl. intro Hp. inversion Hp as [|Hp0].
    apply pumping_constant_0_false in H. inversion H.
  - (* MStarApp *)
    simpl. intros Hlen.
    rewrite app_length in *.
    assert (Hs1re1 : length s1 = 0
                     \/ (length s1 <> 0 /\ length s1 < pumping_constant re)
                     \/ pumping_constant re <= length s1).
    { induction s1 as [| h s1' IHs1].
      - left. reflexivity.
      - right.
        assert (Hcases : length (h :: s1') < pumping_constant re
                         \/ pumping_constant re <= length (h :: s1')).
        { apply lt_ge_cases. }
        destruct Hcases as [Hlenlt | Hlengt].
        + left.
          split.
          * unfold not. intros contra. inversion contra.
          * apply Hlenlt.
        + right. apply Hlengt.
    }
    destruct Hs1re1 as [Hs1len0 | [[Hs1len Hs1re1] | Hs1re1]].
    + assert (Hs1nil : s1 = []).
      { destruct s1. reflexivity. inversion Hs1len0. }
      subst. simpl in *. apply IH2. apply Hlen.
    + exists [], s1, s2. simpl in *.
      split. reflexivity.
      split.
      { unfold not. intros Hs1nil. subst.
        unfold not in Hs1len. apply Hs1len.
        reflexivity.
      }
      split.
      { apply n_lt_m__n_le_m. apply Hs1re1. }
      intros m. apply napp_star.
      * apply Hmatch1.
      * apply Hmatch2.
    + destruct (IH1 Hs1re1) as [s11 [s12 [s13 [H1 [H2 [Hlenp Hnapp]]]]]].
      exists s11, s12, (s13 ++ s2).
      split.
      { subst. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
      split.
      { apply H2. }
      split.
      { apply Hlenp. }

      intros m.
      rewrite -> app_assoc.
      rewrite -> app_assoc.
      apply MStarApp.
      * rewrite <- app_assoc. apply Hnapp.
      * apply Hmatch2.
Qed.
(* /ADMITTED *)

(* HIDE *)
(* LATER: BCP 25: A fancier version...*)

(** To streamline the proof (which you are to fill in), the [lia]
    tactic, which is enabled by an [Import] line at the beginning of
    this chapter, is helpful in several places for automatically
    completing tedious low-level arguments involving equalities or
    inequalities over natural numbers.  We'll return to [lia] in a
    later chapter, but feel free to experiment with it now if you
    like.  The first case of the induction gives an example of how it
    is used. *)

Lemma pumping' : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. lia.
  (* ADMITTED *)
  - (* MChar *)
    simpl. lia.
  - (* MApp *)
    simpl. intros Hlen.
    assert (H : pumping_constant re1 <= length s1 \/
                pumping_constant re2 <= length s2).
    { rewrite app_length in Hlen. lia. }
    destruct H as [H | H].
    + destruct (IH1 H) as [s11 [s12 [s13 [H1 [H2 H3]]]]].
      rewrite H1.
      exists s11. exists s12. exists (s13 ++ s2).
      rewrite <- app_assoc, <- app_assoc.
      split. { reflexivity. }
      split. { apply H2. }
      split. { destruct H3 as [Hlenp Hnapp]. apply le_plus_trans. apply Hlenp. }
      intros m.
      rewrite app_assoc, app_assoc. apply MApp.
      * rewrite <- app_assoc. apply H3.
      * apply Hmatch2.
    + (* now, either...  length s1 < pumping_constant re, or pumping_constant <= length s1 *)
      assert (Hs1re1 : length s1 < pumping_constant re1 \/ pumping_constant re1 <= length s1).
      { apply lt_ge_cases. }

      destruct Hs1re1 as [Hs1re1 | Hs1re1].
      * destruct (IH2 H) as [s21 [s22 [s23 [H1 [H2 [Hlenp Hnapp]]]]]].
        rewrite H1.
        exists (s1 ++ s21). exists s22. exists s23.
        rewrite <- app_assoc.
        split. { reflexivity. }
        split. { apply H2. }
        split.
        { rewrite app_length in *.
          rewrite <- add_assoc.
          apply le_trans with (n:=length s1 + pumping_constant re2).
          + lia.
          + apply plus_le_compat_r. apply n_lt_m__n_le_m. apply Hs1re1.
        }

        intros m.
        rewrite <- app_assoc. apply MApp.
        -- apply Hmatch1.
        -- apply Hnapp.

      * destruct (IH1 Hs1re1) as [s11 [s12 [s13 [H1 [H2 H3]]]]].
        rewrite H1.
        exists s11. exists s12. exists (s13 ++ s2).
        rewrite <- app_assoc, <- app_assoc.
        split. { reflexivity. }
        split. { apply H2. }
        split. { destruct H3 as [Hlenp Hnapp]. apply le_plus_trans. apply Hlenp. }

        intros m.
        rewrite app_assoc, app_assoc. apply MApp.
        -- rewrite <- app_assoc. apply H3.
        -- apply Hmatch2.
  - (* MUnionL *)
    simpl. intros Hlen.
    assert (H : pumping_constant re1 <= length s1) by lia.
    destruct (IH H) as [s11 [s12 [s13 [H1 [H2 [Hlenp Hnapp]]]]]].
    exists s11. exists s12. exists s13. split. { apply H1. }
    split. { apply H2. }
    split. { lia. }
    intros m. apply MUnionL. apply Hnapp.
  - (* MUnionR *)
    simpl. intros Hlen.
    assert (H : pumping_constant re2 <= length s2) by lia.
    destruct (IH H) as [s21 [s22 [s23 [H1 [H2 [Hlenp Hnapp]]]]]].
    exists s21. exists s22. exists s23. split. { apply H1. }
    split. { apply H2. }
    split. { lia. }
    intros m. apply MUnionR. apply Hnapp.
  - (* MStar0 *)
    simpl. intro Hp. inversion Hp as [|Hp0].
    apply pumping_constant_0_false in H. inversion H.
  - (* MStarApp *)
    simpl. intros Hlen.
    rewrite app_length in *.
    assert (Hs1re1 : length s1 = 0 \/ (length s1 <> 0 /\ length s1 < pumping_constant re) \/ pumping_constant re <= length s1).
    { induction s1 as [| h s1' IHs1].
      - left. reflexivity.
      - right.
        assert (Hcases : length (h :: s1') < pumping_constant re \/ pumping_constant re <= length (h :: s1')).
        { apply lt_ge_cases. }
        destruct Hcases as [Hlenlt | Hlengt].
        + left.
          split.
          * unfold not. intros contra. inversion contra.
          * apply Hlenlt.
        + right. apply Hlengt.
    }
    destruct Hs1re1 as [Hs1len0 | [[Hs1len Hs1re1] | Hs1re1]].
    + assert (Hs1nil : s1 = []).
      { destruct s1. reflexivity. inversion Hs1len0. }
      subst. simpl in *. apply IH2. apply Hlen.
    + exists [], s1, s2. simpl in *.
      split. reflexivity.
      split.
      { unfold not. intros Hs1nil. subst.
        unfold not in Hs1len. apply Hs1len.
        reflexivity.
      }
      split.
      { apply n_lt_m__n_le_m. apply Hs1re1. }
      intros m. apply napp_star.
      * apply Hmatch1.
      * apply Hmatch2.
    + destruct (IH1 Hs1re1) as [s11 [s12 [s13 [H1 [H2 [Hlenp Hnapp]]]]]].
      exists s11, s12, (s13 ++ s2).
      split.
      { subst. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
      split.
      { apply H2. }
      split.
      { apply Hlenp. }

      intros m.
      rewrite -> app_assoc.
      rewrite -> app_assoc.
      apply MStarApp.
      * rewrite <- app_assoc. apply Hnapp.
      * apply Hmatch2.
Qed.
(* /ADMITTED *)
(* /HIDE *)

End Pumping.
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** * Case Study: Improving Reflection *)

(** FULL: We've seen in the \CHAP{Logic} chapter that we sometimes
    need to relate boolean computations to statements in [Prop].  But
    performing this conversion as we did there can result in tedious
    proof scripts.  Consider the proof of the following theorem: *)
(* TERSE *)
(** We've seen that we often need to relate boolean
    computations to statements in [Prop]: *)

Check eqb_eq : forall n1 n2, (n1 =? n2) = true <-> n1 = n2.

(** However, this can result in some tedium in proof scripts. Consider: *)
(* /TERSE *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] -> In n l.
(* FOLD *)
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = nil *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.
(* /FOLD *)

(** TERSE: The first subcase (where [n =? m = true]) is awkward
    because we have to explicitly "switch worlds."

    It would be annoying to have to do this kind of thing all the
    time. *)

(** FULL: In the first branch after [destruct], we explicitly apply the [eqb_eq]
    lemma to the equation generated by destructing [n =? m], to convert the
    assumption [n =? m
    = true] into the assumption [n = m]; then we had to
    [rewrite] using this assumption to complete the case. *)

(** TERSE: *** *)
(** We can streamline this sort of reasoning by defining an inductive
    proposition that yields a better case-analysis principle for [n =?
    m].  Instead of generating the assumption [(n =? m) = true], which
    usually requires some massaging before we can use it, this
    principle gives us right away the assumption we really need: [n =
    m].

    Following the terminology introduced in \CHAP{Logic}, we call this
    the "reflection principle for equality on numbers," and we say
    that the boolean [n =? m] is _reflected in_ the proposition
    [n = m]. *)

(* HIDE *)
    (* BCP 9/17: Don't find it helpful to show them this first. *)
    Module FirstTry.
    Inductive reflect : Prop -> bool -> Prop :=
      | ReflectT : forall (P:Prop), P -> reflect P true
      | ReflectF : forall (P:Prop), ~P -> reflect P false.
    End FirstTry.
    (** TERSE: *** *)
    (** Before explaining this, let's rearrange it a little: Since the
        types of both [ReflectT] and [ReflectF] begin with
        [forall (P:Prop)], we can make the definition a bit more readable
        and easier to work with by making [P] a parameter of the whole
        Inductive declaration. *)
(* /HIDE *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

(** FULL: The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  It states that the property [P]
    _reflects_ (intuitively, is equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].

    To see this, notice that, by definition, the only way we can
    produce evidence for [reflect P true] is by showing [P] and then
    using the [ReflectT] constructor.  If we invert this statement,
    this means that we can extract evidence for [P] from a proof of
    [reflect P true].

    Similarly, the only way to show [reflect P false] is by tagging
    evidence for [~ P] with the [ReflectF] constructor. *)
(** TERSE: Notice that the only way to produce evidence for [reflect P
    true] is by showing [P] and then using the [ReflectT] constructor.

    If we play this reasoning backwards, it says we can extract
    _evidence_ for [P] from evidence for [reflect P true]. *)

(** To put this observation to work, we first prove that the
    statements [P <-> b = true] and [reflect P b] are indeed
    equivalent.  First, the left-to-right implication: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKINCLASS *)
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.
(* /WORKINCLASS *)

(** TERSE: (The right-to-left implication is left as an exercise.) *)
(** FULL: Now you prove the right-to-left implication: *)

(* FULL *)
(* HIDEFROMADVANCED *)
(* EX2! (reflect_iff) *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  (* ADMITTED *)
  intros P b H.
  destruct H as [H | H].
  - split.
    + intros _. reflexivity.
    + intros _. apply H.
  - split.
    + intros contra. exfalso. apply H. apply contra.
    + intros contra. discriminate. Qed.
(* /ADMITTED *)
(** [] *)
(* /HIDEFROMADVANCED *)
(* /FULL *)

(** TERSE: *** *)
(** We can think of [reflect] as a variant of the usual "if and only
    if" connective; the advantage of [reflect] is that, by destructing
    a hypothesis or lemma of the form [reflect P b], we can perform
    case analysis on [b] while _at the same time_ generating
    appropriate hypothesis in the two branches ([P] in the first
    subgoal and [~ P] in the second). *)

(** TERSE: *** *)
(** Let's use [reflect] to produce a smoother proof of
    [filter_not_empty_In].

    We begin by recasting the [eqb_eq] lemma in terms of [reflect]: *)

(* LATER: The standard library seems to call this eqb_spec now!
   BCP 25: Here's chatgpt's summary of the situation:
        In the Coq ecosystem, the convention is fairly clear:
        eqbP is the MathComp-style name:
        In Mathematical Components, for every boolean test foo you get a reflection lemma fooP.
        So if you have eqb : A → A → bool, the canonical reflection lemma is called eqbP.
        It states reflect (x = y) (eqb x y).
        eqb_spec is the Coq standard library style:
        In Coq’s standard library, decidability and boolean lemmas are usually named with _spec.
        So for Nat.eqb, you’ll find Nat.eqb_spec : ∀ x y, BoolSpec (x = y) (x ≠ y) (Nat.eqb x y).
        So the "proper" name depends on the style of the library you’re in:
        If you’re writing in the MathComp / ssreflect world, use eqbP.
        If you’re working in the Coq standard library style (no MathComp), use eqb_spec.
        Both are expressing the same idea, but in different idioms:
        eqbP is a reflect lemma, which is very convenient for ssreflect tactics.
        eqb_spec is a BoolSpec, which fits the standard Coq pattern.
    Indeed, it's even called eqb_spec in Maps.v!

    I.e., we should indeed be using eqb_spec here.  But then we should
    perhaps *also* rename some other things, in many files. That's a
    bigger change than I'm up for making right now, but if anyone else
    feels like pushing it through...

*)
Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** TERSE: *** *)
(** The proof of [filter_not_empty_In] now goes as follows.  Notice
    how the calls to [destruct] and [rewrite] in the earlier proof of
    this theorem are combined here into a single call to
    [destruct]. *)

(** FULL: (To see this clearly, execute the two proofs of
    [filter_not_empty_In] with Rocq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [EQnm | NEQnm].
    + (* n = m *)
      intros _. rewrite EQnm. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(* FULL *)
(* HIDEFROMADVANCED *)
(* EX3! (eqbP_practice) *)
(** Use [eqbP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl'].
  (* ADMITTED *)
  - intros contra. inversion contra.
  - simpl in Hcount. destruct (eqbP n m) as [H | H].
    + discriminate Hcount.
    + apply IHl' in Hcount. intros contra. inversion contra.
      * symmetry in H0. apply H in H0. apply H0.
      * apply Hcount in H0. apply H0.
Qed.
(* /ADMITTED *)
(** [] *)
(* /HIDEFROMADVANCED *)
(* /FULL *)

(** TERSE: *** *)
(** This small example shows reflection giving us a small gain in
    convenience; in larger developments, using [reflect] consistently
    can often lead to noticeably shorter and clearer proof scripts.
    We'll see many more examples in later chapters and in _Programming
    Language Foundations_.

    This way of using [reflect] was popularized by _SSReflect_, a Rocq
    library that has been used to formalize important results in
    mathematics, including the 4-color theorem and the Feit-Thompson
    theorem.  The name SSReflect stands for _small-scale reflection_,
    i.e., the pervasive use of reflection to streamline small proof
    steps by turning them into boolean computations. *)

(* FULL *)
(* ####################################################### *)
(** * Additional Exercises *)

(* EX3! (nostutter_defn) *)
(** Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence [[1;4;1]] has two occurrences of the element [1] but
    does not stutter.)  The property "[nostutter mylist]" means that
    [mylist] does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
 (* SOLUTION *)
  | nostutter0: nostutter nil
  | nostutter1 n : nostutter (n::nil)
  | nostutter2 a b r (Hneq : a<>b) (H : nostutter(b::r)) : nostutter (a::b::r)
 (* /SOLUTION *)
.
(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
(* ADMITTED *)
(* /ADMITTED *)
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)

Example test_nostutter_2:  nostutter (@nil nat).
(* ADMITTED *)
(* /ADMITTED *)
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)

Example test_nostutter_3:  nostutter [5].
(* ADMITTED *)
(* /ADMITTED *)
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  Proof. repeat constructor; auto. Qed.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)

(* LATER: AAA: The script below seems too fragile, we should probably
   change it to make it more robust. *)
Example test_nostutter_4:      not (nostutter [3;1;1;4]).
(* ADMITTED *)
(* /ADMITTED *)
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)

(* GRADE_MANUAL 3: nostutter *)
(** [] *)

(* EX4A (filter_challenge) *)
(** Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,
[[
    [1;4;6;2;3]
]]
    is an in-order merge of
[[
    [1;6;2]
]]
    and
[[
    [4;3].
]]
    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    First define what it means for one list to be a merge of two
    others.  Do this with an inductive relation, not a [Fixpoint].  *)

Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
(* SOLUTION *)
  | merge_empty :
      merge [] [] []
  | merge_left : forall l1 l2 l3 x,
      merge l1 l2 l3 ->
      merge (x::l1) l2 (x::l3)
  | merge_right : forall l1 l2 l3 x,
      merge l1 l2 l3 ->
      merge l1 (x::l2) (x::l3)
(* /SOLUTION *)
.

Theorem merge_filter : forall (X : Set) (test: X->bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  (* ADMITTED *)
  intros X test l l1 l2 HM. induction HM as [|l1'|l2']; intros Hl1 Hl2.
  - (* merge_empty *) reflexivity.
  - (* merge_left *) simpl. destruct Hl1 as [HX Hl1']. rewrite -> HX.
    rewrite -> (IHHM Hl1' Hl2). reflexivity.
  - (* merge right *) simpl. destruct Hl2 as [HX Hl2']. rewrite -> HX.
    apply (IHHM Hl1 Hl2').
Qed.
(* /ADMITTED *)

(* SOLUTION *)
(* An alternative solution: *)

Theorem filter_good : forall (X : Type),
                      forall (test : X -> bool),
                      forall (l1 l2 l3 : list X),
  forallb test l1 = true ->
  forallb (fun x => negb (test x)) l2 = true ->
  merge l1 l2 l3 ->
  filter test l3 = l1.
Proof.
  intros X test l1 l2 l3 HT HF HM.
  induction HM.
  - (* merge_empty *) reflexivity.
  - (* merge_left *) unfold filter.
    destruct (test x) eqn:Heqtestx.
    + (* test x = true *) unfold filter in IHHM. rewrite -> IHHM. reflexivity.
      unfold forallb in HT. rewrite -> Heqtestx in HT. apply HT. apply HF.
    + (* test x = false *) unfold forallb in HT. rewrite -> Heqtestx in HT.
      discriminate HT.
  - (* merge_right *) unfold filter.
    destruct (test x) eqn:Heqtestx.
    + (* test x = true *) unfold forallb in HF. rewrite -> Heqtestx in HF.
      discriminate HF.
    + (* test x = false *)
      unfold filter in IHHM. rewrite -> IHHM. reflexivity.
      apply HT. unfold forallb in HF. rewrite -> Heqtestx in HF. apply HF.
Qed.

(* Another alternative solution: *)

Lemma negb_true : forall b, negb b = true -> b = false.
Proof.
  intros b eq. destruct b.
  - (* b = true *)
    discriminate eq.
  - (* b = false *)
    reflexivity. Qed.

Theorem filter_spec : forall (X:Type) (test:X -> bool) (l l1 l2:list X),
  merge l1 l2 l ->
  forallb test l1 = true ->
  forallb (fun x => negb (test x)) l2 = true ->
  l1 = filter test l.
Proof.
  intros X test l1 l2 l3 HM. induction HM.
  - (* merge_empty *) intros HT HF. simpl. reflexivity.
  - (* merge_left *) intros HT HF. simpl. simpl in HT.
    apply andb_true_iff in HT.  destruct HT as [HX HL1].
    rewrite -> HX. f_equal.  apply IHHM. apply HL1. apply HF.
  - (* merge_right *) intros HT HF. simpl. simpl in HF.
    apply andb_true_iff in HF. destruct HF as [HX HL2].
    apply negb_true in HX. rewrite -> HX. apply IHHM. apply HT. apply HL2.
Qed.

(* /SOLUTION *)
(* HIDE *)
(* Another possible problem (perhaps for Basics.v): Write a Rocq function
   that generates the list of all in-order merges of two lists... However, the
   following isn't structurally recursive :-(
       Fixpoint all_merges {X : Type} (l1 l2 : list X) :=
         match (l1,l2) with
         | (l1,[]) => [l1]
         | ([],l2) => [l2]
         | (x1::rest1,x2::rest2) =>
              (map (fun l => cons x1 l) (all_merges rest1 l2))
           ++ (map (fun l => cons x2 l) (all_merges l1 rest2))
         end. *)
(* /HIDE *)

(* GRADE_THEOREM 6: merge_filter *)
(** [] *)

(* EX5A? (filter_challenge_2) *)
(** A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

(* SOLUTION *)
Module Sol.
(** We reproduce the definition of subseq here, in a module
    so it doesn't conflict. *)

Inductive subseq {X:Type} : list X -> list X -> Prop :=
  | sub_nil  : forall l, subseq [] l
  | sub_take : forall x l1 l2, subseq l1 l2 -> subseq (x :: l1) (x :: l2)
  | sub_skip : forall x l1 l2, subseq l1 l2 -> subseq l1 (x :: l2)
.

(** A few lemmas about subseq. *)
Lemma subseq_drop_l : forall (X:Type) (x:X) (l1 l2 : list X),
  subseq (x :: l1) l2 -> subseq l1 l2.
Proof.
  intros X x l1 l2 Hsub.
  induction l2 as [|x' l2'].
  - (* l2 = [] *) inversion Hsub.
  - (* l2 = x' :: l2' *)
    inversion Hsub.
    + (* sub_take *) apply sub_skip. apply H0.
    + (* sub_skip *) apply sub_skip. apply IHl2'. apply H1.
Qed.

Lemma subseq_drop : forall (X:Type) (x:X) (l1 l2 : list X),
  subseq (x :: l1) (x :: l2) -> subseq l1 l2.
Proof.
  intros X x l1 l2 Hsub.
  inversion Hsub.
    apply H0.
    apply (subseq_drop_l _ x). apply H1.
Qed.

(** Now for some silly lemmas about [<=], which we need since we
    redefined [<=] ourselves. Of course, these are all in the Rocq
    standard library. *)

Lemma le_0_n : forall n, 0 <= n.
Proof.
  induction n as [|n'].
    apply le_n.
    apply le_S. apply IHn'.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. induction H2.
    apply H1.
    apply le_S. apply IHle.
Qed.

Lemma le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply (le_trans _ (S n)).
    apply le_S. apply le_n.
    apply H.
Qed.

Lemma le_S_n : forall n m, S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - (* m = n *) apply le_n.
  - (* S n <= m *) apply le_Sn_le. apply H1.
Qed.

Lemma le_n_S : forall n m, n <= m -> S n <= S m.
Proof.
  intros n m H. induction H.
    apply le_n.
    apply le_S. apply IHle.
Qed.

Lemma Sn_le_n : forall n, ~ (S n <= n).
Proof.
  unfold not. induction n as [|n'].
  - (* n = 0 *) intros contra. inversion contra.
  - (* n = S n' *) intros H. apply IHn'.
  apply le_S_n. apply H.
Qed.

(** A list is _maximal_ with property [P] if it has the property, and
    every other list with the property is at most as long as it is. *)

Definition maximal {X:Type} (lmax : list X) (P : list X -> Prop) :=
  P lmax /\ forall l', P l' -> length l' <= length lmax.

(** A "good subsequence" for a given list [l] and a [test] is a
    subsequence of [l] all of whose members evaluate to [true] under
    the [test]. *)

Definition good_subseq {X:Type} (test : X -> bool) (l lsub : list X) :=
  subseq lsub l /\ forallb test lsub = true.

(** Good subsequences can be extended with good elements. *)

Lemma good_subseq_extend : forall (X:Type) (test : X -> bool)
                                  (l lsub : list X) (x : X),
  good_subseq test l lsub ->
  test x = true ->
  good_subseq test (x::l) (x::lsub).
Proof.
  intros X test l lsub x [Hsub Hall] Hx. split.
  - (* subseq *) apply sub_take. apply Hsub.
  - (* all *) simpl. rewrite Hx. apply Hall.
Qed.

(** If [lmax] is a maximal good subsequence of [x :: l] and [x] is not good,
    then [lmax] is also a maximal good subsequence of [l]. *)
Lemma maximal_strengthening : forall (X:Type) (x:X)
                                     (lmax l : list X)
                                     (test : X -> bool),
  maximal lmax (good_subseq test (x::l)) ->
  test x = false ->
  maximal lmax (good_subseq test l).
Proof.
  intros X x lmax l test [[Hsub Hall] Hlen] Hx.
  split. split.
  - (* subseq *)
    inversion Hsub.
    + (* sub_nil *) apply sub_nil.
    + (* sub_take *) rewrite H in H0.
      rewrite <- H0 in Hall. simpl in Hall. rewrite Hx in Hall. discriminate Hall.
    + (* sub_skip *) apply H1.
  - (* all *) apply Hall.
  - (* len *) intros l' [Hsub' Hall']. apply Hlen. split.
    + (* subseq *) apply sub_skip. apply Hsub'.
    + (* all *) apply Hall'.
Qed.

(** Some easy lemmas about filter: its result is a good subsequence of
    the original list. *)

Lemma filter_subseq : forall (X:Type) (l : list X) (test : X -> bool),
  subseq (filter test l) l.
Proof.
  intros X l test. induction l as [|x l'].
  - (* l = [] *) apply sub_nil.
  - (* l = x :: l' *) simpl. destruct (test x) eqn:E.
    + (* test x = true *) apply sub_take. apply IHl'.
    + (* test x = false *) apply sub_skip. apply IHl'.
Qed.

Lemma filter_all : forall (X:Type) (l : list X) (test : X -> bool),
  forallb test (filter test l) = true.
Proof.
  intros X l test. induction l as [|x l'].
  - (* l = [] *) reflexivity.
  - (* l = x :: l' *) simpl.
    destruct (test x) eqn: Heqtx.
    + (* test x = true *) simpl. rewrite -> Heqtx. apply IHl'.
    + (* test x = false *) apply IHl'.
Qed.

(** And now for the main theorem: [lsub] is a maximal good subsequence
    of [l] if and only if [filter test l = lsub]. *)
(* LATER: This could use a lot of cleanup... *)

Theorem filter_spec2 : forall (X:Type) (l lsub:list X) (test : X -> bool),
  maximal lsub (good_subseq test l) <-> filter test l = lsub.
Proof.
  split.
  - (* -> *)
    generalize dependent lsub.
    induction l as [|x l'].
    + (* l = [] *)
      (* lsub = [] since lsub is a subseq of l. *)
      intros lsub [[Hsub _] _].
      inversion Hsub. reflexivity.
    + (* l = x :: l' *)
      intros lsub H. simpl.
      destruct (test x) eqn: Heqtx.
      * (* test x = true *)
        destruct H as [[Hsub Hall] Hlen].
        (* in this case, lsub must begin with x, since otherwise it
           wouldn't be maximal. *)
        destruct lsub as [|x' lsub'].
        { (* lsub = [] (impossible: contradicts maximality of lsub) *)
          assert (length [x] <= length ([] : list X)) as contra.
          { apply Hlen. split.
            - apply sub_take. apply sub_nil.
            - simpl. rewrite -> Heqtx. reflexivity. }
          inversion contra. }
        { (* lsub = x' :: lsub' *)
          assert (x = x'). (* because of maximality again *)
          { (* proof of assertion *)
            inversion Hsub.
            - (* sub_take *) reflexivity.
            - (* sub_skip *) (* contradiction, since x :: x' :: lsub'
                                would be longer *)
              assert (length (x :: x' :: lsub') <= length (x' :: lsub')).
              { (* proof of assertion *)
                apply Hlen. split.
                - apply sub_take. apply H1.
                - simpl. rewrite -> Heqtx. simpl. simpl in Hall.
                  apply Hall. }
              simpl in H3. apply Sn_le_n in H3. destruct H3. }
          rewrite H.
          rewrite -> (IHl' lsub'). reflexivity.
          split. split. rewrite H in Hsub. apply subseq_drop with x'. apply Hsub.
            simpl in Hall. apply andb_true_elim2 in Hall. apply Hall.
            intros l0 Hgood0. rewrite <- H in Hlen. simpl in Hlen.
            apply le_S_n.
            apply (Hlen (x :: l0)). apply good_subseq_extend. apply Hgood0.
            symmetry. rewrite  Heqtx. reflexivity. }
      * (* test x = false *)
        apply IHl'.
        apply (maximal_strengthening _ x). apply H.
        symmetry. rewrite Heqtx. reflexivity.
  - (* <- *) intros Hfilter.
    split. split.
    + (* subseq *) rewrite <- Hfilter. apply filter_subseq.
    + (* all *) rewrite <- Hfilter. apply filter_all.
    + (* len *) generalize dependent lsub. induction l as [|x l2].
      * (* l = [] *) intros lsub _ l' [Hsub _]. inversion Hsub. apply le_0_n.
      * (* l = x :: l2 *) intros lsub Hfilter l' [Hsub Hall].
        simpl in Hfilter.
        destruct (test x) eqn: Heqtx.
        { (* test x = true *)
          rewrite <- Hfilter. inversion Hsub.
          - (* sub_nil *) apply le_0_n.
          - (* sub_take *) simpl. apply le_n_S.
            apply IHl2. reflexivity. split. apply H1. rewrite <- H0 in Hall.
            simpl in Hall. apply andb_true_elim2 in Hall. apply Hall.
          - (* sub_skip *) simpl. apply le_S.
            apply IHl2. reflexivity. split. apply H1. apply Hall. }
        { (* test x = false *)
          apply IHl2. apply Hfilter. split.
          inversion Hsub. apply sub_nil. rewrite <- H0 in Hall. rewrite H in Hall.
            simpl in Hall. rewrite -> Heqtx in Hall. discriminate Hall.
            apply H1. apply Hall. }
Qed.
End Sol.
(* /SOLUTION *)
(** [] *)

(* EX4? (palindromes) *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.

    - Prove ([pal_app_rev]) that
[[
       forall l, pal (l ++ rev l).
]]
    - Prove ([pal_rev] that)
[[
       forall l, pal l -> l = rev l.
]]

    For extra credit, try proving the same theorems with an alternate
    definition with a _single_ constructor of this type:
[[
        forall l, l = rev l -> pal l
]]
*)

(* HIDE: MTF 6/22: It isn't exactly clear why the single constructor approach
   "will not work very well".  It seems to work extremely well:

    Inductive pal {X:Type} : list X -> Prop :=
      | palc : forall l, l = rev l -> pal l.

    Theorem pal_app_rev : forall (X:Type) (l : list X),
      pal (l ++ (rev l)).
    Proof.
      intros X l.
      apply palc.
      rewrite rev_app_distr.
      rewrite rev_involutive.
      reflexivity.
    Qed.

    Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
    Proof.
      intros X l H. destruct H. assumption.
    Qed.

    Theorem palindrome_converse: forall {X: Type} (l: list X), l = rev l -> pal l.
    Proof.
      intros X l H. apply palc. assumption.
    Qed.

      This seems to be yet another example of a property that can be expressed as a
      non-inductive proposition being artificially formulated as an inductive
      proposition.  Are there any other properties of the [palindrome] proposition
      that would be difficult to prove from its specification?

   BCP 25: Took away the "will not work very well" wording. *)

Inductive pal {X:Type} : list X -> Prop :=
(* SOLUTION *)
  | pal_nil : pal []
  | pal_one : forall x, pal [x]
  | pal_consnoc : forall x l, pal l -> pal (x::(l++[x]))
(* /SOLUTION *)
.

(* LATER: APT21: a student noted that the pal_one case is easy to
   miss, since the theorems don't require it! BCP 25: We could fix
   that by adding some examples, e.g. [], [1], and [1,1]. *)

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  (* ADMITTED *)
  induction l as [| n' l'].
  - (* l = nil *)
    simpl. apply pal_nil.
  - (* l = n' :: l' *)
    simpl. rewrite app_assoc. apply pal_consnoc. apply IHl'.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: pal_app_rev *)

(* LATER: Note that we're using some standard library stuff here...
   We should at least explicitly qualify them... *)
Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  (* ADMITTED *)
  intros X l P. induction P.
  - (* P = pal_nil *) reflexivity.
  - (* P = pal_one *) reflexivity.
  - (* P = pal_consnoc *)
    simpl. rewrite rev_app_distr. rewrite <- IHP.
    simpl. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: pal_rev *)
(** [] *)

(* EX5? (palindrome_converse) *)
(** Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that
[[
     forall l, l = rev l -> pal l.
]]
*)

(* QUIETSOLUTION *)
(** Proving the converse theorem is much harder, because a standard
    induction over the list [l] doesn't work.  The trick to the
    following proof, due to Nathan Collins, is to induct over _half
    the length_ of [l].  We make heavy use of destruct and inversion
    to clear away the impossible cases. *)

Lemma rev_pal': forall {X: Type} (n:nat) (l:list X ),
  div2 (length l) = n -> l = rev l -> pal l.
Proof.
  intros X n.
  induction n as [| n'].
    - (* n = O *)
     (* (length l) div 2 = 0 || l has length 0 or 1 *)
    intros l Hlen Hrev.
      destruct l as [| x l'].
        (* l = [] *)
        apply pal_nil.
        destruct l' as [| x' l''].
          (* l = [x] *)
          apply pal_one.
          (* impossible : l has length > 1 *)
          discriminate Hlen.
    - (* n = S n' *)
    (* (length l) div 2 >= 1  || l has length at least 2 *)
    intros l Hlen Hrev.
      destruct l as [| x l'].
        + (* l = [] *)
        (* impossible : l has length 0 *)
        discriminate Hlen.
        + (* l = x :: l' *)
          simpl in Hrev.
          destruct (rev l') as [| x' l''] eqn: Heqrevl'.
            * (* rev l' = [] *)
            (* impossible : l has length 1 *)
             inversion Hrev. rewrite H0 in Hlen. discriminate Hlen.
            * (* rev l' = x'::l'' *)
              inversion Hrev.
              (* l = x' :: l'' ++ [x'] *)
              apply pal_consnoc.
              apply IHn'.
              rewrite H1 in Hlen. simpl in Hlen.
              replace (length (l'' ++ [x'])) with (S (length l'')) in Hlen.
              { injection Hlen as H2. apply H2. }
              symmetry. rewrite app_length. rewrite add_comm. reflexivity.
              rewrite H1 in Heqrevl'. rewrite rev_app_distr in Heqrevl'.
              injection Heqrevl' as H2. rewrite H2. reflexivity.
Qed.

(* And here's another solution due (modulo some fixes by BCP/AAA to
   replace snoc with app) to Michael Schulman. It uses a few tactics
   that we haven't seen yet. *)

Theorem eqrev_pal_gen (X : Type) : forall (l:list X) (p t:list X),
  l = p ++ t -> p = rev p -> pal p.
Proof.
 induction l as [| x l'].
 - (* l = nil *)
   destruct p.
   + (* p = nil *)
     destruct t as [| x t'].
        * (* t = nil *)
          intros; constructor.
        * (* t = cons *)
          intros H; inversion H.
   + (* p = cons *)
     intros t H.
     inversion H.
 - (* l = cons *)
   destruct p as [| y p'].
   + (* p = nil *)
     intros. constructor.
   + (* p = cons *)
     intros t H K.
     inversion H.
     simpl in K.
     destruct (rev p') as [| z p''] eqn:Heqrevp'.
     * (* rev p' = nil *)
       destruct p' as [| w q].
       { (* p' = nil *) constructor. }
       { (* p' = cons *)
         assert (L : [] = w :: q).
         { rewrite <- rev_involutive. rewrite  Heqrevp'. reflexivity. }
         inversion L. }
     * (* rev p' = cons *)
       assert (M : rev (rev p') = (rev p'') ++ [z]).
       { rewrite Heqrevp'. reflexivity. }
       rewrite rev_involutive in M.
       rewrite M.
       inversion K.
       (* Now we finally get to do *)
       constructor.
       apply (IHl' _ (z :: t)).
       { (* l' = rev p'' ++ z :: t *)
         rewrite H2. rewrite M. rewrite <- app_assoc. reflexivity. }
       { (* rev p'' = rev (rev p'') *)
         rewrite H4 in Heqrevp'. rewrite rev_app_distr in Heqrevp'.
         inversion Heqrevp'.
         rewrite rev_involutive.
         symmetry. apply H5. } Qed.

Theorem eqrev_pal (X : Type) (l:list X) : (l = rev l) -> pal l.
Proof.
  intros H.
  apply (eqrev_pal_gen _ l l []).
  rewrite app_nil_r. reflexivity.
  apply H.
Qed.

(* A final possibility is adding a natural number n and a hypothesis
   "length l <= n" and inducting on n.  The following solution by
   Mihir Mehta follows this strategy... *)

Lemma palindrome_converse_lemma_1:
  forall {X: Type} (l: list X), length (rev l) = length l.
Proof. {
  intros X. induction l.
  { reflexivity. }
  { simpl. rewrite -> app_length. rewrite -> IHl. simpl.
    rewrite -> add_comm. reflexivity. }
} Qed.

Lemma palindrome_converse_lemma_2:
  forall {X: Type} (n: nat) (l: list X), (length l <= n) -> l = rev l -> pal l.
Proof. {
  intros X. induction n as [| n'].
  { (* n = 0 *)
    intros [| x l'] H1 H2.
    { (* l = [] *) apply pal_nil. }
    { (* l = x :: l' *) inversion H1. }
  }
  { (* n = S n'*)
    intros [| x l'] H3 H4.
    { (* l = [] *) apply pal_nil. }
    { (* l = x :: l' *)
      simpl in H4.
      destruct (rev l') as [| x' l''] eqn:H5.
      { (* rev l = [] *)
        rewrite <- (rev_involutive X l'). rewrite -> H5. simpl.
        apply pal_one. }
      { (* rev l = x' :: l'' *)
        inversion H4 as [[H6 H7]]. apply pal_consnoc. apply (IHn' l'').
        { (* proving: length l'' <= n' *)
          rewrite -> H7 in H3. simpl in H3.
          rewrite -> app_length in H3. simpl in H3.
          rewrite -> add_comm in H3. simpl in H3.
          apply Sn_le_Sm__n_le_m, Sn_le_Sm__n_le_m.
          apply le_S. apply H3.
        }
        { (* proving l'' = rev l'' *)
          rewrite -> H7 in H5. rewrite -> rev_app_distr in H5. simpl in H5.
          inversion H5 as [H8]. rewrite -> H8, -> H8. reflexivity.
        }
      }
    }
  }
} Qed.
(* /QUIETSOLUTION *)

Theorem palindrome_converse: forall {X: Type} (l: list X),
    l = rev l -> pal l.
Proof.
  (* ADMITTED *)
  intros X l. apply (palindrome_converse_lemma_2 (length l)), le_n.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX4A? (NoDup) *)
(** Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* HIDEFROMHTML *)
Module RecallIn.
(* /HIDEFROMHTML *)
   Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
     match l with
     | [] => False
     | x' :: l' => x' = x \/ In A x l'
     end.
(* HIDEFROMHTML *)
End RecallIn.
(* /HIDEFROMHTML *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

(* SOLUTION *)
Definition disjoint {X:Type} (l1 l2: list X) :=
  forall (x:X), In x l1 -> ~ In x l2.
(* /SOLUTION *)

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

(* SOLUTION *)
Inductive NoDup {X:Type} : list X -> Prop :=
  | NoDup_nil : NoDup nil
  | NoDup_cons : forall a l,
              ~ In a l ->
              NoDup l ->
              NoDup (a::l).
(* /SOLUTION *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

(* SOLUTION *)
(* Here are some possible answers: *)

Lemma NoDup_append : forall (X:Type) (l1 l2: list X),
  NoDup l1 -> NoDup l2 -> disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof.
  intros X l1. induction l1 as [| x l1'].
  - (* l1 = nil *)
    intros l2 NR1 NR2 D. simpl. apply NR2.
  - (* l1 = x:l1' *)
    intros l2 NR1 NR2 D. simpl.
    apply NoDup_cons.
    + intros contra. apply In_app_iff in contra. destruct contra.
      * inversion NR1 as [| ? ? NA NRl1']. apply NA. apply H.
      * unfold disjoint in D.  apply (D x).
        { left. reflexivity. }
        apply H.
    + apply IHl1'.
      * inversion NR1 as [| ? ? NA NRl1']. apply NRl1'.
      * apply NR2.
      * unfold disjoint. intros x0 AI. apply D. right. apply AI.
Qed.

Lemma NoDup_disjoint : forall (X:Type) (l1 l2: list X),
  NoDup (l1++l2) -> disjoint l1 l2.
Proof.
  unfold disjoint.
  induction l1 as [|x l1'].
  - intros l2 NR x AI. inversion AI.
  - intros l2 NR x0 AI. simpl in NR. inversion NR. inversion AI.
    + intros contra. apply H1.
      apply In_app_iff. right. rewrite H3. apply contra.
    + apply IHl1'.
      * apply H2.
      * apply H3.
Qed.

(* We can also show the following results about [NoDup] and [++]
   by themselves *)
Lemma NoDup_left : forall (X:Type) (l1 l2: list X),
  NoDup (l1++l2) -> NoDup l1.
Proof.
  induction l1 as [|x l1'].
  - intros l2 NR. apply NoDup_nil.
  - intros l2 NR. inversion NR. apply NoDup_cons.
    + intro contra. apply H1. apply In_app_iff. left. apply contra.
    + apply (IHl1' l2). apply H2.
Qed.

Lemma NoDup_right: forall (X:Type) (l1 l2: list X),
  NoDup (l1++l2) -> NoDup l2.
Proof.
  induction l1 as [|x l1'].
  - intros l2 NR. simpl in NR. apply NR.
  - intros l2 NR. inversion NR. apply IHl1'. apply H2.
Qed.

(* This theorem combines the various lemmas to give a complete
   characterization *)
Theorem NoDup_disjoint_app : forall {X:Type} (l1 l2: list X),
  NoDup (l1++l2) <->
  (NoDup l1 /\ NoDup l2 /\ disjoint l1 l2).
Proof.
  intros X l1 l2.
  split.
  - (* -> *)
    intro NR. split.
    + apply (NoDup_left _ _ l2). apply NR.
    + split.
      * apply (NoDup_right _ l1). apply NR.
      * apply NoDup_disjoint. apply NR.
  - (* <- *)
    intros [NR1 [NR2 DISJ]].
    apply NoDup_append.
    + apply NR1.
    + apply NR2.
    + apply DISJ.
Qed.
(* /SOLUTION *)

(* GRADE_MANUAL 6: NoDup_disjoint_etc *)
(** [] *)

(* EX5A? (pigeonhole_principle) *)
(* GRADE_THEOREM 2: in_split *)
(* GRADE_THEOREM 6: pigeonhole_principle *)
(** The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy and useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  (* ADMITTED *)
  induction l as [|x' l' IHl'].
  - (* l = nil *)
    intros [].
  - (* l = x' :: l' *)
    simpl. intros [AI | AI].
    + (* x' = x *)
      exists []. exists l'. rewrite AI. reflexivity.
    + (* In x l' *)
      destruct (IHl' AI) as [l1' [l2' EQ]].
      exists (x'::l1'). exists l2'. rewrite -> EQ. reflexivity.
Qed.
(* /ADMITTED *)

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* SOLUTION *)
  | rep_here : forall a l, In a l -> repeats (a::l)
  | rep_later : forall a l, repeats l -> repeats (a::l)
(* /SOLUTION *)
.

(* GRADE_MANUAL 2: check_repeats *)

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)
(* HIDE: APT21: Apparently, this is really quite hard; even the strongest
   students couldn't do it this year. *)
Theorem pigeonhole_principle: excluded_middle ->
  forall (X:Type) (l1  l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1. induction l1 as [|x l1' IHl1'].
  (* ADMITTED *)
    - intros l2 INC NR.  simpl in NR. inversion NR.
    - intros l2 INC NR.
      destruct (EM (In x l1')) as [H | H].
      + (* In x l1' *)
        apply rep_here. apply H.
      + (* ~ In x l1' *)
        apply rep_later.
        assert (INX: In x l2).
        {  apply INC. left. reflexivity. }
        destruct (in_split _ _ _ INX) as [l2a [l2b EQ]].
        remember (l2a ++ l2b) as l2' eqn:Heql2'.
        assert (IN2: forall x0 : X, In x0 l1' -> In x0 l2').
        { intros x0 AI.
          assert (H0: x <> x0).
          { intros Heq. apply H. rewrite  Heq. apply AI. }
          assert (H1: In x0 l2).
          { apply INC. simpl. right. apply AI. }
          rewrite EQ in H1. apply In_app_iff in H1.
          rewrite Heql2'. apply In_app_iff.
          simpl in H1. destruct H1 as [H1 | [H1 | H1]].
          - left. apply H1.
          - exfalso. apply H0. apply H1.
          - right. apply H1.  }
        assert (LEN2: length l2' < length l1').
        { assert (LS: length l2 = S(length (l2a ++ l2b))).
          { rewrite EQ.
            rewrite app_length. rewrite app_length. rewrite add_comm.
            simpl. rewrite add_comm. reflexivity. }
          rewrite LS in NR. rewrite <- Heql2' in NR. simpl in NR.
          apply Sn_le_Sm__n_le_m.  apply NR.
        }
        apply (IHl1' l2' IN2 LEN2).
Qed.
(* /ADMITTED *)
(* LATER: A student came up with

Definition repeats {X} (xs: list X) : Prop :=
  exists x ps qs rs,  xs = ps ++ [x] ++ qs ++ [x] ++ rs.
Should check to see how much harder this makes things.
*)
(** [] *)

(* QUIETSOLUTION *)
    (** Here's a clever alternative proof, based heavily on one by Daniel
        Schepler (<dschepler@gmail.com> Coq club mailing list on Wed, 02 Oct
        2013 02:02:12 -0700), that doesn't use decidability of [In], and hence
        doesn't need [excluded_middle]. *)

    (** First, some more auxiliary lemmas, some of which are a bit ad hoc. *)

    Lemma in_repeats: forall {X:Type} (l1 l2:list X) (x:X),
      In x (l1++l2) ->
      repeats (l1++x::l2).
    Proof.
      intros X l1. induction l1 as [|y l1' IHl1'].
      - (* l1 = [] *)
        intros l2 x AI. simpl in AI. simpl. apply rep_here. apply AI.
      - (* l1 = y::l1' *)
        intros l2 x AI. simpl in AI. simpl. destruct AI as [AI | AI].
        + apply rep_here. apply In_app_iff. right. left.
          rewrite AI. reflexivity.
        + apply rep_later. apply IHl1'. apply AI.
    Qed.

    Lemma rep_insert: forall {X:Type} (l1 l2:list X) (x: X),
      repeats (l1 ++ l2) -> repeats (l1 ++ x::l2).
    Proof.
      intros X l1. induction l1 as [| y l1' IHl1'].
      - (* l1 = [] *)
        intros l2 x H. simpl. simpl in H. apply rep_later.  apply H.
      - (* l1 = y::l1' *)
        intros l2 x H. simpl. simpl in H. inversion H.
        + (* rep_here *)
          apply rep_here. apply In_app_iff. apply In_app_iff in H1.
          destruct H1 as [H1 | H1].
          * left. apply H1.
          * right. right. apply H1.
        + (* rep_later *)
          apply rep_later. apply IHl1'. apply H1.
    Qed.

    Lemma repeats_app_comm : forall {X:Type} (l1 l2:list X),
      repeats (l1++l2) -> repeats(l2++l1).
    Proof.
      intros X l1. induction l1 as [|x l1'].
      - (* l1 = [] *)
        intros l2 H.  rewrite app_nil_r. simpl in H. apply H.
      - (* l1 = x::l1' *)
        intros l2 H. simpl in H. inversion H.
        + (* rep_here *)
          apply in_repeats. apply In_app_iff.
          apply In_app_iff in H1.
          destruct H1 as [H1 | H1].
          * right. apply H1.
          * left. apply H1.
        + (* rep_later *)
          apply IHl1' in H1. apply rep_insert. apply H1.
    Qed.

    (** Now the main lemma: *)

    Lemma pigeonhole_principle_aux: forall {X:Type} (l1 l2 ls: list X),
      (forall x:X, In x l1 -> In x (ls++l2)) ->
      length l2 < length l1 -> repeats (ls++l1).
    Proof.
      intros X l1. induction l1 as [|x l1' IHl1'].
      - (* l1 = [] *)
        intros l2 ls AI LT. inversion LT.
      - (* l1 = x::l1' *)
        intros l2 ls AI LT.
        assert (In x (ls++l2)).
        { (* Proof of assertion *)
          apply AI. left. reflexivity. }
        assert (In x ls \/ In x l2).
        { (* Proof of assertion *)
          apply In_app_iff. apply H. }
        destruct H0.
        + (* In x ls *)
          apply repeats_app_comm. simpl. apply rep_here.
          apply In_app_iff. right. apply H0.
        + (* In x l2 *)
          apply in_split in H0.
          destruct H0 as [l2a [l2b P]]. rewrite P in *.
          assert (repeats ((x::ls) ++ l1')).
          * (* Proof of assertion *)
            apply (IHl1' (l2a++l2b) (x::ls)).
            { (* re-establish inclusion relation *)
              intros x0 AI'.
              assert (In x0 (ls ++ l2a ++ x::l2b)).
              { (* Proof of assertion *)
                apply AI. right. apply AI'. }
              apply In_app_iff in H0. inversion H0.
                apply In_app_iff.  left. right. apply H1.
                apply In_app_iff in H1. inversion H1.
                  apply In_app_iff. right.
                    apply In_app_iff. left. apply H2.
                  inversion H2.
                    simpl. left. apply H3.
                    apply In_app_iff. right.
                      apply In_app_iff. right. apply H3. }
            rewrite app_length in LT.  rewrite app_length.
            simpl in LT. rewrite <- plus_n_Sm in LT.
            unfold lt. unfold lt in LT. apply le_S_n. apply LT.
          * simpl in H0. apply repeats_app_comm. simpl. inversion H0.
            { apply rep_here. apply In_app_iff.
              apply In_app_iff in H2. inversion H2.
              - right. apply H4.
              - left. apply H4. }
            apply rep_later. apply repeats_app_comm. apply H2.
    Qed.

    Theorem stronger_pigeonhole_principle: forall {X:Type} (l1 l2 : list X),
      (forall x : X, In x l1 -> In x l2) ->
      length l2 < length l1 ->
      repeats l1.
    Proof.
      intros X l1 l2 AI LT.
      assert (H: l1 = nil ++ l1). { reflexivity. }
      rewrite H. apply (pigeonhole_principle_aux l1 l2 nil).
      simpl. apply AI. apply LT.
    Qed.

    (** One key to how this proof works is that at the inductive step,
        when we re-establish the inclusion relation, the contents on the
        list on the right-hand side of the inclusion have not changed at
        all---they are merely re-arranged, so validity of the inclusion is
        trivial (modulo some messy book-keeping). Compare this to the
        equivalent step in the original proof, where we remove [x] from the
        list on the right-hand side of the inclusion; this is only valid when
        we know that [x] is not in the left-hand list [l1'] either---exactly
        the knowledge that we get from decidability of [In], and cannot get
        any other way. *)

    (* ------------------------ *)

    (** Finally, here is a much more elegant proof due to N. Raghavendra
        <raghu@hri.res.in>, based on Daniel's.  It uses the following
        sequence of observations:

          Lemma app_ass :
          forall (X : Type) (l1 l2 l3 : list X),
            (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.

          Lemma app_length :
          forall (X : Type) (l1 l2 : list X),
            length (l1 ++ l2) = length l1 + length l2.

          Lemma In_app_iff_split :
          forall (X : Type) (x : X) (l : list X),
            In x l ->
            exists (l1 l2 : list X), l = l1 ++ x :: l2.

          Lemma In_both_impl_repeats_app :
          forall (X : Type) (x : X) (l1 l2 : list X),
            In x l1 -> In x l2 -> repeats (l1 ++ l2).

          Lemma In_app_iff_midswap :
          forall (X : Type) (x : X) (l1 l2 l3 l4 : list X),
            In x (l1 ++ l2 ++ l3 ++ l4) ->
            In x (l1 ++ l3 ++ l2 ++ l4).

          Lemma pigeonhole_principle_aux :
          forall (X : Type) (l1 l2 u : list X),
            (forall x : X, In x l1 -> In x (u ++ l2)) ->
            length l2 < length l1 -> repeats (u ++ l1).

          Theorem pigeonhole_principle :
          forall (X : Type) (l1 l2 : list X),
            (forall x : X, In x l1 -> In x l2) ->
            length l2 < length l1 -> repeats l1.
    *)

    (* HIDE: Some of these are already proved elsewhere. Also, this
      vertical style is hard to read. *)

    Module Pigeon.

    Inductive repeats {X : Type} : list X -> Prop :=
      | repeats_1 (x : X) (l : list X)
                  (H : In x l) : repeats (x :: l)
      | repeats_2 (x : X) (l : list X)
                  (H : repeats l) : repeats (x :: l).

    Definition pigeonhole_principle_prop (X : Type) : Prop :=
      forall l1 l2 : list X,
        (forall x : X, In x l1 -> In x l2) ->
        length l2 < length l1 -> repeats l1.

    Lemma app_ass :
      forall (X : Type) (l1 l2 l3 : list X),
        (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.

    Proof.
      intros X l1 l2 l3.
      induction l1 as [ | h t IH].
      {
        - (* l1 = nil *)
        reflexivity.
      }
      {
        - (* l1 = h :: t *)
        simpl.
        rewrite -> IH.
        reflexivity.
      }
    Qed.

    Lemma app_length :
      forall (X : Type) (l1 l2 : list X),
        length (l1 ++ l2) = length l1 + length l2.

    Proof.
      intros X l1 l2.
      induction l1 as [ | h t IH].
      {
        - (* l1 = nil *)
        reflexivity.
      }
      {
        - (* l1 = h :: t *)
        simpl.
        rewrite -> IH.
        reflexivity.
      }
    Qed.

    Lemma In_both_impl_repeats_app :
      forall (X : Type) (x : X) (l1 l2 : list X),
        In x l1 -> In x l2 -> repeats (l1 ++ l2).

    Proof.
      intros X x l1.
      induction l1 as [ | h1 t1 IH].
      {
        - (* l1 = nil *)
        intros l2 H1 H2.
        inversion H1.
      }
      {
        - (* l1 = h1 :: t1 *)
        intros l2 H1 H2. simpl in H1.
        destruct H1 as [H3 | H3].
        {
          +
          simpl.
          apply repeats_1.
          apply In_app_iff.
          right.
          rewrite H3.
          apply H2.
        }
        {
          + (* H1 = ai_later z u H3 *)
          simpl.
          apply repeats_2.
          apply IH.
          {
            apply H3.
          }
          {
            apply H2.
          }
        }
      }
    Qed.

    Lemma In_app_iff_midswap :
      forall (X : Type) (x : X) (l1 l2 l3 l4 : list X),
        In x (l1 ++ l2 ++ l3 ++ l4) -> In x (l1 ++ l3 ++ l2 ++ l4).

    Proof.
      intros X x l1 l2 l3 l4 H.
      apply In_app_iff in H.
      destruct H as [H1 | H1r].
      {
        - (* In x l1 *)
        apply In_app_iff.
        left.
        apply H1.
      }
      {
        - (* In x (l2 ++ l3 ++ l4) *)
        apply In_app_iff in H1r.
        destruct H1r as [H2 | H2r].
        {
          + (* In x l1 *)
          apply In_app_iff.
          right.
          apply In_app_iff.
          right.
          apply In_app_iff.
          left.
          apply H2.
        }
        {
          + (* In x (l3 ++ l4) *)
          apply In_app_iff in H2r.
          destruct H2r as [H3 | H3r].
          {
            * (* In x l3 *)
            apply In_app_iff.
            right.
            apply In_app_iff.
            left.
            apply H3.
          }
          {
            * (* In x l4 *)
            apply In_app_iff.
            right.
            apply In_app_iff.
            right.
            apply In_app_iff.
            right.
            apply H3r.
          }
        }
      }
    Qed.

    Lemma pigeonhole_principle_aux :
      forall (X : Type) (l1 l2 u : list X),
        (forall x : X, In x l1 -> In x (u ++ l2)) ->
        length l2 < length l1 -> repeats (u ++ l1).

    Proof.
      intros X l1.
      induction l1 as [ | h1 t1 IH].
      {
        - (* l1 = nil *)
        intros l2 u H1 H2.
        inversion H2.
      }
      {
        - (* l1 = h1 :: t1 *)
        intros l2 u H1 H2.
        assert (H3 : In h1 (u ++ l2)).
        {
          + (* Proof of H3 *)
          apply H1.
          left. reflexivity.
        }
        apply In_app_iff in H3.
        destruct H3 as [H3l | H3r].
        {
          + (* In h1 u *)
          apply (In_both_impl_repeats_app _ h1).
          {
            apply H3l.
          }
          {
            left. reflexivity.
          }
        }
        {
          + (* In h1 l2 *)
          apply in_split in H3r.
          destruct H3r as [v2 H4].
          destruct H4 as [w2 H5].
          assert (H6 : u ++ h1 :: t1 = (u ++ [h1]) ++ t1).
          {
            * (* Proof of H6 *)
            rewrite -> app_ass.
            reflexivity.
          }
          rewrite -> H6.
          apply (IH (v2 ++ w2)).
          {
            * (* Proof of first condition of IH *)
            intros x H7.
            rewrite -> app_ass.
            apply In_app_iff_midswap.
            simpl.
            rewrite <- H5.
            apply H1.
            right.
            apply H7.
          }
          {
            * (* Proof of second condition of IH *)
            unfold lt.
            assert (H8 : length l2 = S (length (v2 ++ w2))).
            {
              rewrite -> H5.
              rewrite -> app_length.
              rewrite -> app_length.
              simpl.
              rewrite <- plus_n_Sm.
              reflexivity.
            }
            rewrite <- H8.
            apply Sn_le_Sm__n_le_m.
            unfold lt in H2.
            simpl in H2.
            apply H2.
          }
        }
      }
    Qed.

    Theorem pigeonhole_principle :
      forall X : Type,
        pigeonhole_principle_prop X.

    Proof.
      intros X.
      unfold pigeonhole_principle_prop.
      intros l1 l2 H1 H2.
      assert (H: l1 = nil ++ l1). { reflexivity. }
      rewrite H.
      apply (pigeonhole_principle_aux _ _ l2).
      {
        intros x H3.
        simpl.
        apply H1.
        apply H3.
      }
      {
        apply H2.
      }
    Qed.

    End Pigeon.

(* /QUIETSOLUTION *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)
(* INSTRUCTORS: Thanks to Bill Harris for contributing this! *)
(* LATER: We should probably introduce the `;`, `try` and `auto`
   tactics, or encourage readers to look ahead and find out about
   them, before getting to the extended exercise? *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match automatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function that reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Rocq. As a result, Rocq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)
From Stdlib Require Import Strings.Ascii.

Definition string := list ascii.

(** The Rocq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(* ####################################################### *)
(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(* EX3? (app_ne) *)
(** [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([ ] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  (* ADMITTED *)
  intros.
  rewrite app_exists.
  split.
  - (* matches App implies prop *)
    intros [ [ | b s0 ] [ s1 [ Happ [ Hre0 Hre1 ] ] ] ].
    + left. split.
      * apply Hre0.
      * rewrite Happ. apply Hre1.
    + right. exists s0, s1. injection Happ as H H1. split.
      * apply H1.
      * split. rewrite H. apply Hre0. apply Hre1.
  - intros [ [ Heps0 Hne1 ] | [ s0 [ s1 [ Happ [ Hre0 Hre1 ] ] ] ] ].
    + exists [ ], (a :: s). split.
      * reflexivity.
      * split.
        ** apply Heps0.
        ** apply Hne1.
    + exists (a :: s0), s1. split.
      * rewrite Happ. reflexivity.
      * split.
        ** apply Hre0.
        ** apply Hre1.
Qed.
(* /ADMITTED *)
(** [] *)

(** [s] is matched by [Union re0 re1] iff [s] matched by
    [re0] or [s] matched by [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
  s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(* EX3? (star_ne) *)
(** [a::s] is matched by [Star re] iff [s = s0 ++ s1], where [a::s0] is matched by
    [re] and [s1] is matched by [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  (* ADMITTED *)
  split.
  - intros.
    remember (a :: s) as s' eqn:Heqs'.
    remember (Star re) as re' eqn:Eq.
    induction H.
   + discriminate Eq.
   + discriminate Eq.
   + discriminate Eq.
   + discriminate Eq.
   + discriminate Eq.
   + discriminate Heqs'.
   + destruct s1.
     * apply (IHexp_match2 Heqs' Eq).
     * exists s1, s2. injection Heqs' as H2 H3.
       injection Eq as H4. split. (* inversion Heqs'. inversion Eq. split. *)
       ** rewrite H3. reflexivity.
       ** split.
          *** rewrite <- H2, <- H4. apply H.
          *** apply H0.
  - intros [ s0 [ s1 [ H0 [ H1 H2 ] ] ] ].
    rewrite H0.
    apply (MStarApp (a :: s0) s1). apply H1. apply H2.
Qed.
(* /ADMITTED *)
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

(* EX2? (match_eps) *)
(** Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: reg_exp ascii) : bool
  (* ADMITDEF *) :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => false
  | App re0 re1 => (match_eps re0) && (match_eps re1)
  | Union re0 re1 => (match_eps re0) || (match_eps re1)
  | Star re => true
  end.
(* /ADMITDEF *)
(** [] *)

(* EX3? (match_eps_refl) *)
(** Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  (* ADMITTED *)
  unfold refl_matches_eps.
  induction re.
  -(* empty set *)
    apply ReflectF. unfold not. intros. inversion H.
  -(* empty string *)
    apply ReflectT. apply MEmpty.
  -(* char *)
    apply ReflectF. unfold not. intros. inversion H.
  -(* app *)
    simpl. destruct IHre1.
    + destruct IHre2.
      * apply ReflectT. apply (MApp [ ] _ [ ]). apply H. apply H0.
      * apply ReflectF. unfold not. intros. apply H0. inversion H1; subst.
        destruct s1.
        ** apply H6.
        ** discriminate H2.
    + apply ReflectF. unfold not. intros. inversion H0. apply H. destruct s1.
      * apply H4.
      * discriminate H1.
  -(* union *)
    simpl. destruct IHre1.
    + apply ReflectT. apply MUnionL. apply H.
    + destruct IHre2.
      * apply ReflectT. apply MUnionR. apply H0.
      * apply ReflectF. unfold not. intros. inversion H1.
        ** apply H. apply H4.
        ** apply H0. apply H4.
  - apply ReflectT. apply MStar0.
Qed.
(* /ADMITTED *)
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(* ####################################################### *)
(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(* EX3? (derive) *)
(** Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii
  (* ADMITDEF *) :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char x => if ascii_dec a x then EmptyStr else EmptySet
  | App re0 re1 =>
    Union (App (derive a re0) re1)
          (if match_eps re0 then derive a re1 else EmptySet)
  | Union re0 re1 => Union (derive a re0) (derive a re1)
  | Star re => App (derive a re) (Star re)
  end.
(* /ADMITDEF *)
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  (* ADMITTED *)
  reflexivity. Qed.
(* /ADMITTED *)

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  (* ADMITTED *)
  reflexivity. Qed.
(* /ADMITTED *)

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  (* ADMITTED *)
  reflexivity. Qed.
(* /ADMITTED *)

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  (* ADMITTED *)
  reflexivity. Qed.
(* /ADMITTED *)

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  (* ADMITTED *)
  reflexivity. Qed.
(* /ADMITTED *)

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  (* ADMITTED *)
  reflexivity. Qed.
(* /ADMITTED *)

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  (* ADMITTED *)
  reflexivity. Qed.
(* /ADMITTED *)

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  (* ADMITTED *)
  reflexivity. Qed.
(* /ADMITTED *)

(* EX4? (derive_corr) *)
(** Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
  (* ADMITTED *)
  unfold derives, is_der.
  induction re.
  - (* EmptySet *)
    simpl. intros. rewrite null_matches_none, null_matches_none.
    reflexivity.
  - (* EmptyStr *)
    simpl. intros. rewrite empty_nomatch_ne, null_matches_none.
    reflexivity.
  - (* Char *)
    simpl. intros. destruct (ascii_dec a t).
    + (* a is character in regex *)
      rewrite e, char_eps_suffix, empty_matches_eps. reflexivity.
    + (* a is not character in regex. *)
      rewrite null_matches_none.
      apply char_nomatch_char. apply n.
  - (* App *)
    intros. simpl. rewrite app_ne, union_disj, app_exists. split.
    + (* full match implies suffix matches derivation *)
      intros [ [ Hepsmat Hrem ] | [ s0 [ s1 [ H1 [ H2 H3 ] ] ] ] ].
      * right. destruct (match_eps_refl re1).
        ** apply IHre2. apply Hrem.
        ** exfalso. apply H. apply Hepsmat.
      * left. exists s0, s1. split.
        ** apply H1.
        ** split.
           *** apply IHre1. apply H2.
           *** apply H3.
    + (* suffix matches derivation implies full match. *)
      intros [ [ s0 [ s1 [ Happ [ Hre1 Hre2 ] ] ] ] | Hre2 ].
      * right. exists s0, s1. split.
        ** apply Happ.
        ** split.
           *** apply IHre1. apply Hre1.
           *** apply Hre2.
      * destruct (match_eps_refl re1).
        ** left. split.
           *** apply H.
           *** apply IHre2. apply Hre2.
        ** inversion Hre2.
  - (* Union *)
    simpl. intros. rewrite union_disj, union_disj. split.
    + intros [ H0 | H1 ].
      * left. apply IHre1. apply H0.
      * right. apply IHre2. apply H1.
    + intros [ H0 | H1 ].
      * (* matches left union term *)
        left. apply IHre1. apply H0.
      * right. apply IHre2. apply H1.
  - (* Star *)
    simpl. intros. rewrite star_ne, app_exists. split.
    + intros [ s0 [ s1 [ Heq [ Hmat Hmatstar] ] ] ].
      exists s0, s1. split.
      * apply Heq.
      * split.
        ** apply IHre. apply Hmat.
        ** apply Hmatstar.
    + intros [ s0 [ s1 [ Happ [ Hre Hstar ] ] ] ].
      exists s0, s1. split.
      * apply Happ.
      * split.
        ** apply IHre. apply Hre.
        ** apply Hstar.
Qed.
(* /ADMITTED *)
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(* ####################################################### *)
(** A function [m] _matches regexes_ if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [re] matches
    [s]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(* EX2? (regex_match) *)
(** Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool
  (* ADMITDEF *) :=
  match s with
  | [ ] => match_eps re
  | a :: s' => regex_match s' (derive a re)
  end.
(* /ADMITDEF *)
(** [] *)

(* EX3? (regex_match_correct) *)
(** Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_match_correct : matches_regex regex_match.
Proof.
  (* ADMITTED *)
  unfold matches_regex.
  induction s.
  - apply match_eps_refl.
  - simpl. intros. destruct (IHs (derive x re)).
    + apply ReflectT.
      apply (derive_corr x re).
      apply H.
    + apply ReflectF. unfold not. intros.
      apply H.
      apply (derive_corr x re).
      apply H0.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

