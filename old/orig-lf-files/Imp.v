(** * Imp: Simple Imperative Programs *)

(* INSTRUCTORS: This chapter plus Maps.v takes a little more than one
   80-minute lecture.  It could be streamlined a bit further without
   losing much, by removing (for example) the inference rules and BNF
   notations from the terse version.

   (BCP 21: ... Actually, I tried removing inference rules from the
   TERSE version; eventually decided that it makes some of the
   definitions harder to talk about.)

*)
(* SOONER: Needs some WORKINCLASSes and some quizzes  *)
(* SOONER: We still need to adjust the explanations of notations in Imp,
   Hoare, and Stlc from some earlier changes... *)
(* LATER: Another nice challenge exercise at some point would be to add
   C-style arrays (i.e., indirect read/write).  This sets up some
   really nice challenge problems in Hoare.v (reasoning about arrays /
   aliasing / etc.).
*)
(* SOONER: BCP 25: Maybe we should write /\ instead of && in assertions,
   to save a mismatch in the dec_minimum exercise in Hoare2? *)
(* HIDE: At some point we could consider moving material from the old
   HoareLists.v to this chapter (and into later files, as
   appropriate).  We haven't done it yet because it's a shame to
   complicate the nice simple presentation here when it's used as the
   basis for applications like Xavier's static analysis lectures.
   Also, we now have a whole volume on real separation logic... *)
(* HIDE: Check out 8.14 / 8/15 Notation changes -- in particular, note that
  identifiers can now elaborate to strings in a custom grammar -- this may
  help a lot in PLF!
  The release notes now include a section on Notation changes. See
  https://coq.github.io/doc/v8.15/refman/changes.html#id15 for 8.15 and
  https://coq.github.io/doc/v8.14/refman/changes.html#id19 for 8.14
  NDS'25: That does not seem right. I could not find anything to that effect
  in the changelogs, and this hack (from 2022!) also seems to contradict this statement:
  https://github.com/rocq-prover/rocq/issues/15643
*)

(** In this chapter, we take a more serious look at how to use Rocq as
    a tool to study other things.  Our case study is a _simple
    imperative programming language_ called Imp, embodying a tiny core
    fragment of conventional mainstream languages such as C and Java.

    Here is a familiar mathematical function written in Imp.
[[
       Z := X;
       Y := 1;
       while Z <> 0 do
         Y := Y * Z;
         Z := Z - 1
       end
]]
*)
(* HIDEFROMADVANCED *)

(** We concentrate here on defining the _syntax_ and _semantics_ of
    Imp; later, in _Programming Language Foundations_ (_Software
    Foundations_, volume 2), we develop a theory of _program
    equivalence_ and introduce _Hoare Logic_, a popular logic for
    reasoning about imperative programs. *)
(* /HIDEFROMADVANCED *)
(* TERSE: HIDEFROMHTML *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From LF Require Import Maps.
(* TERSE: /HIDEFROMHTML *)

(* ####################################################### *)
(** * Arithmetic and Boolean Expressions *)

(* SOONER: At this point, I usually take some of the lecture time to
   give a high-level picture of the structure of an interpreter, the
   processes of lexing and parsing, the notion of ASTs, etc.  Might be
   nice to work some of those ideas into the notes. - BCP *)
(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    with _variables_, and finally a language of _commands_ including
    assignment, conditionals, sequencing, and loops. *)

(* ####################################################### *)
(** ** Syntax *)

(* TERSE: HIDEFROMHTML *)
Module AExp.

(* TERSE: /HIDEFROMHTML *)
(** FULL: These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)
(** TERSE: _Abstract syntax trees_ for arithmetic and boolean expressions: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(** FULL: In this chapter, we'll mostly elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees -- the process that, for example, would
    translate the string ["1 + 2 * 3"] to the AST
[[
      APlus (ANum 1) (AMult (ANum 2) (ANum 3)).
]]
    The optional chapter \CHAP{ImpParser} develops a simple lexical
    analyzer and parser that can perform this translation.  You do not
    need to understand that chapter to understand this one, but if you
    haven't already taken a course where these techniques are
    covered (e.g., a course on compilers) you may want to skim it. *)

(* FULL *)
(** For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax:
[[
    a := nat
        | a + a
        | a - a
        | a * a

    b := true
        | false
        | a = a
        | a <> a
        | a <= a
        | a > a
        | ~ b
        | b && b
]]
*)
(* /FULL *)

(** FULL: Compared to the Rocq version above...

       - The BNF is more informal -- for example, it gives some
         suggestions about the surface syntax of expressions (like the
         fact that the addition operation is written with an infix
         [+]) while leaving other aspects of lexical analysis and
         parsing (like the relative precedence of [+], [-], and [*],
         the use of parens to group subexpressions, etc.)
         unspecified.  Some additional information -- and human
         intelligence -- would be required to turn this description
         into a formal definition, e.g., for implementing a compiler.

         The Rocq version consistently omits all this information and
         concentrates on the abstract syntax only.

       - Conversely, the BNF version is lighter and easier to read.
         Its informality makes it flexible, a big advantage in
         situations like discussions at the blackboard, where
         conveying general ideas is more important than nailing down
         every detail precisely.

         Indeed, there are dozens of BNF-like notations and people
         switch freely among them -- usually without bothering to say
         which kind of BNF they're using, because there is no need to:
         a rough-and-ready informal understanding is all that's
         important.

    It's good to be comfortable with both sorts of notations: informal
    ones for communicating between humans and formal ones for carrying
    out implementations and proofs. *)

(* ####################################################### *)
(** ** Evaluation *)

(** _Evaluating_ an arithmetic expression produces a number. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** TERSE: *** *)
(** Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BNeq a1 a2  => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BGt a1 a2   => negb ((aeval a1) <=? (aeval a2))
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* HIDEFROMADVANCED *)
(* QUIZ *)
(** What does the following expression evaluate to?
[[
  aeval (APlus (ANum 3) (AMinus (ANum 4) (ANum 1)))
]]

  (A) true

  (B) false

  (C) 0

  (D) 3

  (E) 6

*)
(* /QUIZ *)
(* /HIDEFROMADVANCED *)

(* ####################################################### *)
(** ** Optimization *)

(** FULL: We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0 + e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.

(** FULL: To gain confidence that our optimization is doing the right
    thing we can test it on some examples and see if the output looks
    OK. *)
(* HIDEFROMADVANCED *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* /HIDEFROMADVANCED *)

(** FULL: But if we want to be certain the optimization is correct --
    that evaluating an optimized expression _always_ gives the same
    result as the original -- we should prove it! *)
(** TERSE: *** *)

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
(* FOLD *)
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.
(* /FOLD *)

(* ####################################################### *)
(** * Rocq Automation *)

(** FULL: The amount of repetition in this last proof is a little
    annoying.  And if either the language of arithmetic expressions or
    the optimization being proved sound were significantly more
    complex, it would start to be a real problem.

    So far, we've been doing all our proofs using just a small handful
    of Rocq's tactics and completely ignoring its powerful facilities
    for constructing parts of proofs automatically.  This section
    introduces some of these facilities, and we will see more over the
    next several chapters.  Getting used to them will take some
    energy -- Rocq's automation is a power tool -- but it will allow us
    to scale up our efforts to more complex definitions and more
    interesting properties without becoming overwhelmed by boring,
    repetitive, low-level details. *)
(** TERSE: That last proof was getting a little repetitive.  Time to
    learn a few more Rocq tricks... *)

(* ####################################################### *)
(** ** Tacticals *)

(** _Tacticals_ is Rocq's term for tactics that take other tactics as
    arguments -- "higher-order tactics," if you will.  *)

(* ####################################################### *)
(** *** The [try] Tactical *)

(* LATER: put [;] before [try]? *)
(** If [T] is a tactic, then [try T] is a tactic that is just like [T]
    except that, if [T] fails, [try T] _successfully_ does nothing at
    all (rather than failing). *)
(* LATER: Maybe we want to move the discussion of "try solve" from
   later to here?  It might be helpful for students, but it will make
   this already-longish chapter a bit longer... *)
Theorem silly1 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* Plain [reflexivity] would have failed. *)
  apply HP. (* We can still finish the proof in some other way. *)
Qed.

(* HIDEFROMADVANCED *)

Theorem silly2 : forall ae, aeval ae = aeval ae.
Proof.
    try reflexivity. (* This just does [reflexivity]. *)
Qed.
(* /HIDEFROMADVANCED *)

(** FULL: There is not much reason to use [try] in completely manual
    proofs like these, but it is very useful for doing automated
    proofs in conjunction with the [;] tactical, which we show
    next. *)

(* ####################################################### *)
(** *** The [;] Tactical (Simple Form) *)

(** In its most common form, the [;] tactical takes two tactics as
    arguments.  The compound tactic [T;T'] first performs [T] and then
    performs [T'] on _each subgoal_ generated by [T]. *)

(** FULL: For example, consider the following trivial lemma: *)
(** TERSE: For example: *)

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(** TERSE: *** *)
(** We can simplify this proof using the [;] tactical: *)

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* [destruct] the current goal *)
  destruct n;
  (* then [simpl] each resulting subgoal *)
  simpl;
  (* and do [reflexivity] on each resulting subgoal *)
  reflexivity.
Qed.

(** TERSE: *** *)
(** Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... but the remaining cases -- ANum and APlus --
       are different: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the [try...]
       does nothing, is when [e1 = ANum n]. In this
       case, we have to destruct [n] (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.   Qed.

(* HIDEFROMADVANCED *)
(* FULL *)
(** Rocq experts often use this "[...; try... ]" idiom after a tactic
    like [induction] to take care of many similar cases all at once.
    Indeed, this practice has an analog in informal proofs.  For
    example, here is an informal proof of the optimization theorem
    that matches the structure of the formal one:

    _Theorem_: For all arithmetic expressions [a],
[[
       aeval (optimize_0plus a) = aeval a.
]]
    _Proof_: By induction on [a].  Most cases follow directly from the
    IH.  The remaining cases are as follows:

      - Suppose [a = ANum n] for some [n].  We must show
[[
          aeval (optimize_0plus (ANum n)) = aeval (ANum n).
]]
        This is immediate from the definition of [optimize_0plus].

      - Suppose [a = APlus a1 a2] for some [a1] and [a2].  We must
        show
[[
          aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus a1 a2).
]]
        Consider the possible forms of [a1].  For most of them,
        [optimize_0plus] simply calls itself recursively for the
        subexpressions and rebuilds a new expression of the same form
        as [a1]; in these cases, the result follows directly from the
        IH.

        The interesting case is when [a1 = ANum n] for some [n].  If
        [n = 0], then
[[
          optimize_0plus (APlus a1 a2) = optimize_0plus a2
]]
        and the IH for [a2] is exactly what we need.  On the other
        hand, if [n = S n'] for some [n'], then again [optimize_0plus]
        simply calls itself recursively, and the result follows from
        the IH.  [] *)

(* /FULL *)
(* /HIDEFROMADVANCED *)
(* FULL *)
(** However, this proof can still be improved: the first case (for
    [a = ANum n]) is very trivial -- even more trivial than the cases
    that we said simply followed from the IH -- yet we have chosen to
    write it out in full.  It would be better and clearer to drop it
    and just say, at the top, "Most cases are either immediate or
    direct from the IH.  The only interesting case is the one for
    [APlus]..."  We can make the same improvement in our formal proof
    too.  Here's how it looks: *)

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(* ####################################################### *)
(** *** The [;] Tactical (General Form) *)

(** The [;] tactical also has a more general form than the simple
    [T;T'] we've seen above.  If [T], [T1], ..., [Tn] are tactics,
    then
[[
      T; [T1 | T2 | ... | Tn]
]]
    is a tactic that first performs [T] and then performs [T1] on the
    first subgoal generated by [T], performs [T2] on the second
    subgoal, etc.

    So [T;T'] is just special notation for the case when all of the
    [Ti]'s are the same tactic; i.e., [T;T'] is shorthand for:
[[
      T; [T' | T' | ... | T']
]]
*)
(* /FULL *)

(* ####################################################### *)
(** *** The [repeat] Tactical *)
(* LATER: The `do` tactic could also be introduced before the
   `repeat` tactic. *)

(** The [repeat] tactical takes another tactic and keeps applying this
    tactic until it fails or until it succeeds but doesn't make any
    progress.

    Here is an example proving that [10] is in a long list using
    [repeat]. *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(* FULL *)
(** The tactic [repeat T] never fails: if the tactic [T] doesn't apply
    to the original goal, then repeat _succeeds_ without changing the
    goal at all (i.e., it repeats zero times). *)

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat simpl.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.
(* /FULL *)

(** FULL: The tactic [repeat T] does not have any upper bound on the
    number of times it applies [T].  If [T] is a tactic that _always_
    succeeds (and makes progress), then repeat [T] will loop
    forever. *)

(** TERSE: [repeat] can loop forever. *)

Theorem repeat_loop : forall (m n : nat),
  m + n = n + m.
Proof.
  intros m n.
  (* Uncomment the next line to see the infinite loop occur.  You will
     then need to interrupt Rocq to make it listen to you again.  (In
     Proof General, [C-c C-c] does this.) *)
(* SOONER: BCP 23: What about in VSCoq? *)
  (* repeat rewrite Nat.add_comm. *)
Admitted.

(* FULL *)
(** Wait -- did we just write an infinite loop in Rocq?!?!

    Sort of.

    While evaluation in Rocq's term language, Gallina, is guaranteed to
    terminate, _tactic_ evaluation is not.  This does not affect Rocq's
    logical consistency, however, since the job of [repeat] and other
    tactics is to guide Rocq in constructing proofs; if the
    construction process diverges (i.e., it does not terminate), this
    simply means that we have failed to construct a proof at all, not
    that we have constructed a bad proof. *)

(* EX3 (optimize_0plus_b_sound) *)
(** Since the [optimize_0plus] transformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function that performs this transformation on [bexp]s and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as short and elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp
  (* ADMITDEF *) :=
  match b with
  | BTrue       => BTrue
  | BFalse      => BFalse
  | BEq a1 a2   => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BNeq a1 a2  => BNeq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2   => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BGt a1 a2   => BGt (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1     => BNot (optimize_0plus_b b1)
  | BAnd b1 b2  => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.
(* /ADMITDEF *)

Example optimize_0plus_b_test1:
  optimize_0plus_b (BNot (BGt (APlus (ANum 0) (ANum 4)) (ANum 8))) =
                   (BNot (BGt (ANum 4) (ANum 8))).
Proof. (* ADMITTED *) reflexivity.  Qed. (* /ADMITTED *)

Example optimize_0plus_b_test2:
  optimize_0plus_b (BAnd (BLe (APlus (ANum 0) (ANum 4)) (ANum 5)) BTrue) =
                   (BAnd (BLe (ANum 4) (ANum 5)) BTrue).
Proof. (* ADMITTED *) reflexivity.  Qed. (* /ADMITTED *)

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  (* ADMITTED *)
  induction b;
     simpl;
     try (repeat rewrite optimize_0plus_sound);
     try reflexivity.
  - (* BNot *)
    rewrite IHb.  reflexivity.
  - (* BAnd *)
    rewrite IHb1. rewrite IHb2. reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: optimize_0plus_b_test1 *)
(* GRADE_THEOREM 0.5: optimize_0plus_b_test2 *)
(* GRADE_THEOREM 2: optimize_0plus_b_sound *)
(** [] *)

(* EX4? (optimize) *)
(** _Design exercise_: The optimization implemented by our
    [optimize_0plus] function is only one of many possible
    optimizations on arithmetic and boolean expressions.  Write a more
    sophisticated optimizer and prove it correct.  (You will probably
    find it easiest to start small -- add just a single, simple
    optimization and its correctness proof -- and build up
    incrementally to something more interesting.)  *)

(* SOLUTION *) (* LATER: add a possible solution here? *)
(* /SOLUTION *)
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** ** Defining New Tactics *)

(** FULL: Rocq also provides facilities for "programming" in tactic
    scripts.

    The [Ltac] idiom illustrated below gives a handy way to define
    "shorthand tactics" that bundle several tactics into a single
    command.

    Ltac also includes syntactic pattern-matching on the goal and
    context, as well as general programming facilities.

    It is useful for proof automation and there are several idioms for
    programming with Ltac. Because it is a language style you might
    not have seen before, a good reference is the textbook "Certified
    Programming with dependent types" [CPDT], which is more advanced
    that what we will need in this course, but is considered by many
    the best reference for Ltac programming.

    Just for future reference: Rocq provides two other ways of defining
    new tactics.  There is a [Tactic Notation] command that allows
    defining new tactics with custom control over their concrete
    syntax. And there is also a low-level API that can be used to
    build tactics that directly manipulate Rocq's internal structures.
    We will not need either of these for present purposes.

    Here's an example [Ltac] script called [invert]. *)
(** TERSE: Rocq also provides ways of "programming" tactic scripts:
     - [Ltac]: scripting language for tactics (good for more
       sophisticated proof engineering)
     - [Tactic Notation] for defining tactics with custom concrete
       syntax
     - OCaml tactic scripting API (for wizards)

    [Ltac] is all we need for present purposes.

    For example: *)

Ltac invert H :=
  inversion H; subst; clear H.

(* FULL *)
(** This defines a new tactic called [invert] that takes a hypothesis
    [H] as an argument and performs the sequence of commands
    [inversion H; subst; clear H]. This gives us quick way to do
    inversion on evidence and constructors, rewrite with the generated
    equations, and remove the redundant hypothesis at the end. *)

Lemma invert_example1: forall {a b c: nat}, [a ;b] = [a;c] -> b = c.
  intros.
  invert H.
  reflexivity.
Qed.
(* /FULL *)

(* ####################################################### *)
(** ** The [lia] Tactic *)

(** The [lia] tactic implements a decision procedure for integer linear
    arithmetic, a subset of propositional logic and arithmetic.

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

      - equality ([=] and [<>]) and ordering ([<=] and [>]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [lia] will either solve the goal or fail, meaning
    that the goal is actually false.  (If the goal is _not_ of this
    form, [lia] will fail.) *)

(** TERSE: *** *)
Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. lia.
Qed.


Example add_comm__lia : forall m n,
    m + n = n + m.
Proof.
  intros. lia.
Qed.

Example add_assoc__lia : forall m n p,
    m + (n + p) = m + n + p.
Proof.
  intros. lia.
Qed.

(** FULL: (Note the [From Stdlib Require Import Lia.] at the top of
    this file, which makes [lia] available.) *)

(* ####################################################### *)
(** ** A Few More Handy Tactics *)

(* SOONER: Have we really not introduced any of these? (e.g. subst?) *)
(** Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Delete hypothesis [H] from the context.

     - [subst x]: Given a variable [x], find an assumption [x = e] or
       [e = x] in the context, replace [x] with [e] throughout the
       context and current goal, and clear the assumption.

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x] (where [x] is a variable).

     - [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     - [assumption]: Try to find a hypothesis [H] in the context that
       exactly matches the goal; if one is found, solve the goal.

     - [contradiction]: Try to find a hypothesis [H] in the context
       that is logically equivalent to [False].  If one is found,
       solve the goal.

     - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal.  If one is found, behave
       like [apply c].

    We'll see examples of all of these as we go along. *)

(* ####################################################### *)
(** * Evaluation as a Relation *)

(** We have presented [aeval] and [beval] as functions defined by
    [Fixpoint]s.  Another way to think about evaluation -- one that is
    often more flexible -- is as a _relation_ between expressions and
    their values.  This perspective leads to [Inductive] definitions
    like the following... *)

(* TERSE: HIDEFROMHTML *)
Module aevalR_first_try.

(* TERSE: /HIDEFROMHTML *)
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(* FULL *)
Module HypothesisNames.

(** A small notational aside. We could also write the definition of
    [aevalR] as follow, with explicit names for the hypotheses in each
    case: *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

(** This style gives us more control over the names that Rocq chooses
    during proofs involving [aevalR], at the cost of making the
    definition a little more verbose. *)

End HypothesisNames.
(* /FULL *)

(** FULL: It will be convenient to have an infix notation for
    [aevalR].  We'll write [e ==> n] to mean that arithmetic expression
    [e] evaluates to value [n]. *)
(* HIDE: OLD: (This notation is one place where the
    limitation to ASCII symbols becomes a little bothersome.  The
    standard notation for the evaluation relation is a double
    down-arrow.  We'll typeset it like this in the HTML version of the
    notes and use a double slash as the closest approximation in [.v]
    files.) *)
(** TERSE: *** *)
(** TERSE: A standard notation for "evaluates to": *)

Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.
(* TERSE: HIDEFROMHTML *)

End aevalR_first_try.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** FULL: As we saw in our case study of regular expressions in
    chapter \CHAP{IndProp}, Rocq provides a way to use this notation in
    the definition of [aevalR] itself. *)
(** TERSE: With infix notation: *)

(* HIDEFROMHTML *)
Reserved Notation "e '==>' n" (at level 90, left associativity).
(* /HIDEFROMHTML *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2)  ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2)  ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.
(* LATER: Comment from reader: How do I keep the ==> notation for
   aevalR from conflicting with the ==> notation for bevalR ?

   BCP/AAA 1/16: We should explain about notation scopes somewhere.

   NDS: notation scopes were already briefly touched upon in previous
   chapters.
   *)

(* ####################################################### *)
(** ** Inference Rule Notation *)

(** In informal discussions, it is convenient to write the rules
    for [aevalR] and similar relations in the more readable graphical
    form of _inference rules_, where the premises above the line
    justify the conclusion below the line.

    For example, the constructor [E_APlus]...
[[
      | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)
]]
    ...can be written like this as an inference rule:
[[[
                               e1 ==> n1
                               e2 ==> n2
                         --------------------                (E_APlus)
                         APlus e1 e2 ==> n1+n2
]]]
*)

(** FULL: Formally, there is nothing deep about inference rules: they
    are just implications.

    You can read the rule name on the right as the name of the
    constructor and read each of the linebreaks between the premises
    above the line (as well as the line itself) as [->].

    All the variables mentioned in the rule ([e1], [n1], etc.) are
    implicitly bound by universal quantifiers at the beginning. (Such
    variables are often called _metavariables_ to distinguish them
    from the variables of the language we are defining.  At the
    moment, our arithmetic expressions don't include variables, but
    we'll soon be adding them.)

    The whole collection of rules is understood as being wrapped in an
    [Inductive] declaration.  In informal prose, this is sometimes
    indicated by saying something like "Let [aevalR] be the smallest
    relation closed under the following rules...". *)
(** TERSE: *** *)
(** TERSE: There is nothing very deep going on here:
      - a group of inference rules corresponds to a single [Inductive]
        definition
      - each rule's name corresponds to a constructor name
      - above the line are premises
      - below the line is conclusion
      - _metavariables_ like [e1] and [n1] are implicitly universally
        quantified
*)

(** For example, we could define [==>] as the smallest relation
    closed under these rules:
[[[
                             -----------                               (E_ANum)
                             ANum n ==> n

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 ==> n1+n2

                               e1 ==> n1
                               e2 ==> n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 ==> n1-n2

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 ==> n1*n2
]]]
*)

(* HIDE *)
    (* INSTRUCTORS: It might be useful to write the inference rules on the
       chalkboard, walking through the translation from the inductive
       definition, and then use these quizzes to check comprehension.
       BCP 21: Too heavy. *)
    (*-------*)
    (* LATER: The first two quizzes here seem kind of boring. *)
    (* QUIZ *)
    (** Which rules are needed to prove the following?
    [[
       (AMult (APlus (ANum 3) (ANum 1)) (ANum 0)) ==> 0
    ]]

      (A) [E_ANum] and [E_APlus]

      (B) [E_ANum] only

      (C) [E_ANum] and [E_AMult]

      (D) [E_AMult] and [E_APlus]

      (E) [E_ANum], [E_AMult], and [E_APlus]

    *)
    (* /QUIZ *)
    (* QUIZ *)
    (** Which rules are needed to prove the following?
    [[
       (AMinus (ANum 3) (AMinus (ANum 2) (ANum 1))) ==> 2
    ]]

      (A) [E_ANum] and [E_APlus]

      (B) [E_ANum] only

      (C) [E_ANum] and [E_AMinus]

      (D) [E_AMinus] and [E_APlus]

      (E) [E_ANum], [E_AMinus], and [E_APlus]

    *)
    (* /QUIZ *)
    (*-------*)
(* /HIDE *)

(* FULL *)
(* EX1? (beval_rules) *)
(** Here, again, is the Rocq definition of the [beval] function:
[[
  Fixpoint beval (e : bexp) : bool :=
    match e with
    | BTrue       => true
    | BFalse      => false
    | BEq a1 a2   => (aeval a1) =? (aeval a2)
    | BNeq a1 a2  => negb ((aeval a1) =? (aeval a2))
    | BLe a1 a2   => (aeval a1) <=? (aeval a2)
    | BGt a1 a2   => ~((aeval a1) <=? (aeval a2))
    | BNot b      => negb (beval b)
    | BAnd b1 b2  => andb (beval b1) (beval b2)
    end.
]]
    Write out a corresponding definition of boolean evaluation as a
    relation (in inference rule notation). *)
(* SOLUTION *)
(* Answer ('==>b' is defined below):
[[[
                            ---------------                           (E_BTrue)
                            BTrue ==>b true

                           -----------------                         (E_BFalse)
                           BFalse ==>b false

                              e1 ==> n1
                              e2 ==> n2
                       -------------------------                        (E_BEq)
                       BEq e1 e2 ==>b (n1 =? n2)

                              e1 ==> n1
                              e2 ==> n2
                     -------------------------------                    (E_BNeq)
                     BNeq e1 e2 ==>b negb (n1 =? n2)

                              e1 ==> n1
                              e2 ==> n2
                       --------------------------                       (E_BLe)
                       BLe e1 e2 ==>b (n1 <=? n2)

                              e1 ==> n1
                              e2 ==> n2
                    -------------------------------                     (E_BGt)
                    BGt e1 e2 ==>b negb (n1 <=? n2)

                               e ==>b b
                          ------------------                           (E_BNot)
                          BNot e ==>b negb b

                              e1 ==>b b1
                              e2 ==>b b2
                      --------------------------                       (E_BAnd)
                      BAnd e1 e2 ==>b andb b1 b2
]]]
*)
(* /SOLUTION *)

(* GRADE_MANUAL 1: beval_rules *)
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** ** Equivalence of the Definitions *)

(* HIDEFROMADVANCED *)
(** It is straightforward to prove that the relational and functional
    definitions of evaluation agree: *)

(* /HIDEFROMADVANCED *)
Theorem aevalR_iff_aeval : forall a n,
  (a ==> n) <-> aeval a = n.
(* FOLD *)
(* SOONER: BCP 23: WHy can't we do induction on H in the <-
   direction?? *)
Proof.
  split.
  - (* -> *)
    intros H.
    induction H; simpl.
    + (* E_ANum *)
      reflexivity.
    + (* E_APlus *)
      rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
    + (* E_AMinus *)
      rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
    + (* E_AMult *)
      rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a;
       simpl; intros; subst.
    + (* ANum *)
      apply E_ANum.
    + (* APlus *)
      apply E_APlus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + (* AMinus *)
      apply E_AMinus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + (* AMult *)
      apply E_AMult.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
Qed.
(* /FOLD *)
(* HIDEFROMADVANCED *)

(** Again, we can make the proof quite a bit shorter using some
    tacticals. *)

Theorem aevalR_iff_aeval' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  (* WORKINCLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.
(* /WORKINCLASS *)

(* /HIDEFROMADVANCED *)
(* FULL *)
(* EX3 (bevalR) *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval]. *)

(* HIDEFROMHTML *)
Reserved Notation "e '==>b' b" (at level 90, left associativity).
(* /HIDEFROMHTML *)
Inductive bevalR: bexp -> bool -> Prop :=
(* SOLUTION *)
  | BETrue : bevalR BTrue true
  | BEFalse : bevalR BFalse false
  | BEEq : forall  a1 a2 n1 n2,
    aevalR  a1 n1 ->
    aevalR  a2 n2 ->
    bevalR  (BEq a1 a2) (n1 =? n2)
  | BENeq : forall  a1 a2 n1 n2,
    aevalR  a1 n1 ->
    aevalR  a2 n2 ->
    bevalR  (BNeq a1 a2) (negb (n1 =? n2))
  | BELe : forall  a1 a2 n1 n2,
    aevalR  a1 n1 ->
    aevalR  a2 n2 ->
    bevalR  (BLe a1 a2) (n1 <=? n2)
  | BEGt : forall  a1 a2 n1 n2,
    aevalR  a1 n1 ->
    aevalR  a2 n2 ->
    bevalR  (BGt a1 a2) (negb (n1 <=? n2))
  | BENot : forall  b tv,
    bevalR  b tv ->
    bevalR  (BNot b) (negb tv)
  | BEAnd : forall  b1 b2 tv1 tv2,
    bevalR  b1 tv1 ->
    bevalR  b2 tv2 ->
    bevalR  (BAnd b1 b2) (andb tv1 tv2)
(* /SOLUTION *)
where "e '==>b' b" := (bevalR e b) : type_scope
.

Lemma bevalR_iff_beval : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
  (* ADMITTED *)
  split.
  - (* -> *)
    intros H.
    induction H; simpl; intros; subst;
       try (rewrite aevalR_iff_aeval in H, H0; rewrite H; rewrite H0); reflexivity.
  - (* <- *)
    generalize dependent bv.
    induction b; simpl; intros; subst; constructor;
      try rewrite aevalR_iff_aeval;
      try apply IHb; try apply IHb1; try apply IHb2; try reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: bevalR_iff_beval *)
(** [] *)
(* /FULL *)
(* LATER: Comment from reader: I am mainly following my nose and
   doing trial & error when I write these long [;]-chains. Are there
   some general patterns to follow? For example, what kinds of
   situations call for [try (a_1; a_2; ...; a_k)] and what kinds call
   for [try a_1; try a_2; ...; try a_l]? I know the difference between
   their effects but it is not immediately clear to me what this means
   for the practical uses. Also, are there recommended orders in which
   to chain [intro]s, [rewrite]s, [apply]s, [reflexivity]s and
   [simpl]s? Should [simpl]s be avoided for their slowness? When
   exactly is [simpl] necessary? Most importantly, why was my proof
   for [bevalR_iff_beval'] so much longer than yours for
   [aevalR_iff_aeval'] ? *)

(* TERSE: HIDEFROMHTML *)
End AExp.
(* TERSE: /HIDEFROMHTML *)

(* ####################################################### *)
(** ** Computational vs. Relational Definitions *)

(** FULL: For the definitions of evaluation for arithmetic and boolean
    expressions, the choice of whether to use functional or relational
    definitions is mainly a matter of taste: either way works fine.

    However, there are many situations where relational definitions of
    evaluation work much better than functional ones.  *)

(** TERSE: Sometimes relational definitions are the only reasonable
    option... *)

(* TERSE: HIDEFROMHTML *)
Module aevalR_division.

(* TERSE: /HIDEFROMHTML *)
(* TERSE *)
(** *** Adding division *)
(* /TERSE *)

(** FULL: For example, suppose that we wanted to extend the arithmetic
    operations with division: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).         (* <--- NEW *)

(** FULL: Extending the definition of [aeval] to handle this new
    operation would not be straightforward (what should we return as
    the result of [ADiv (ANum 5) (ANum 0)]?).  But extending [aevalR]
    is very easy. *)
(** TERSE: What should [aeval] return for
       [ADiv (ANum 1) (ANum 0)]?? *)

(* TERSE *)
(** *** Adding division, relationally *)
(* /TERSE *)

(* HIDEFROMHTML *)
Reserved Notation "e '==>' n"
                  (at level 90, left associativity).
(* /HIDEFROMHTML *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :          (* <----- NEW *)
      (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) ==> n3

where "a '==>' n" := (aevalR a n) : type_scope.

(** Notice that this evaluation relation corresponds to a _partial_
    function: There are some inputs for which it does not specify an
    output. *)

(* TERSE: HIDEFROMHTML *)
End aevalR_division.

Module aevalR_extended.

(* TERSE: /HIDEFROMHTML *)
(* TERSE *)
(** *** Adding Nondeterminism *)
(* /TERSE *)

(** FULL: Or suppose that we want to extend the arithmetic operations
    by a nondeterministic number generator [any] that, when evaluated,
    may yield any number.

    (Note that this is not the same as making a _probabilistic_ choice
    among all possible numbers -- we're not specifying any particular
    probability distribution for the results, just saying what results
    are _possible_.) *)

(** TERSE: Another example: A _nondeterministic_ number generator: *)

(* HIDEFROMHTML *)
Reserved Notation "e '==>' n" (at level 90, left associativity).
(* /HIDEFROMHTML *)

Inductive aexp : Type :=
  | AAny                           (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** FULL: Again, extending [aeval] would be tricky, since now
    evaluation is _not_ a deterministic function from expressions to
    numbers; but extending [aevalR] is no problem... *)
(** TERSE: What should [aeval] do with nondeterminism?? *)

(* TERSE *)
(** *** Adding nondeterminism, relationally *)
(* /TERSE *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny ==> n                        (* <--- NEW *)
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)

where "a '==>' n" := (aevalR a n) : type_scope.

(* TERSE: HIDEFROMHTML *)
End aevalR_extended.

(* TERSE: /HIDEFROMHTML *)

(* TERSE *)
(** *** Tradeoffs *)
(* /TERSE *)

(** FULL: At this point you maybe wondering: Which of these styles
    should I use by default?

    In the examples we've just seen, relational definitions turned out
    to be more useful than functional ones.  For situations like
    these, where the thing being defined is not easy to express as a
    function, or indeed where it is _not_ a function, there is no real
    choice.  But what about when both styles are workable?

    One point in favor of relational definitions is that they can be
    more elegant and easier to understand.

    Another is that Rocq automatically generates nice inversion and
    induction principles from [Inductive] definitions.

    On the other hand, functional definitions can often be more
    convenient:
     - Functions are automatically deterministic and total; for a
       relational definition, we have to _prove_ these properties
       explicitly if we need them.
     - With functions we can also take advantage of Rocq's computation
       mechanism to simplify expressions during proofs.

    Furthermore, functions can be directly "extracted" from Gallina to
    executable code in OCaml or Haskell.

    Ultimately, the choice often comes down to either the specifics of
    a particular situation or simply a question of taste.  Indeed, in
    large Rocq developments it is common to see a definition given in
    _both_ functional and relational styles, plus a lemma stating that
    the two coincide, allowing further proofs to switch from one point
    of view to the other at will. *)

(** TERSE: Which is better, functional or relational definitions?

    - Functional: take advantage of computation.
    - Relational: more (easily) expressive.
    - Best of both worlds: define both and prove them equivalent.
*)

(* ####################################################### *)
(** * Expressions With Variables *)

(** Let's return to defining Imp, where the next thing we need to do
    is to enrich our arithmetic and boolean expressions with
    variables.

    To keep things simple, we'll assume that all variables are global
    and that they only hold numbers. *)

(* ####################################################### *)
(** ** States *)

(* LATER: Maybe this section needs a little preface talking about "what is
   the meaning of an expression with variables?"... *)
(** LATER: (Note copied from Equiv.v right before the assign_aequiv
   exercise): Some or all of this discussion should really happen when
   states are introduced in Imp.v, and the whole idea of treating
   states as an ADT should be raised there. *)

(** Since we'll want to look variables up to find out their current
    values, we'll use total maps from the \CHAP{Maps} chapter.

    A _machine state_ (or just _state_) represents the current values
    of all variables at some point in the execution of a program. *)

(** FULL: For simplicity, we assume that the state is defined for
    _all_ variables, even though any given program is only able to
    mention a finite number of them.  Because each variable stores a
    natural number, we can represent the state as a total map from
    strings (variable names) to [nat], and will use [0] as default
    value in the store. *)

Definition state := total_map nat.

(* INSTRUCTORS: BAY, 23 Feb 2011: We tried making state more general,

      state X := id -> option X

   so it could be reused generically later.  However, this ends up
   complicating some of the proofs quite a bit, and not in an
   interesting way.  For example, the factorial invariant would need
   to be something like exists m n, st X = m /\ st Y = n /\ ... which
   is a pain to deal with. The present chapter jumps up the complexity
   coefficient quite a bit already, so we decided it's better to leave
   the simple version here, and go for more generality later on in the
   course.  BCP/AAA 12/2015: This comment led us to implement both
   total and partial maps in earlier chapters, so that we could re-use
   the total ones here. *)

(* ################################################### *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before
    simply by including one more constructor: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)
(* INSTRUCTORS: We usually don't use x as a "bare identifier" in
   examples -- it is normally wrapped in an AId constructor.  If this
   were _always_ the case, then it would make more sense to define the
   notation [x] to mean [AId (Id 0)].  But there quite a few
   counterexamples.  Maybe we could define [xx] to mean [AId (Id 0)],
   or some such?  But it's still awkward.

   BCP/AAA 2/16: Should we use a Coq coercion for this?  It means
   introducing a new concept -- a somewhat magical one -- but it will
   make examples look quite a bit nicer...

   BCP 11/16: It will also solve some problems later on with
   confusions about bound identifiers in Stlc vs. "global" ones in
   Imp. I think it's a good idea to try it for the next big revision.

   ET 10/17: coercions and notations are done, see below.  (still
   keeping the global variables W, X, Y, Z for readability)

   BCP 7/20: This still needs another look to see if there's a way to
   make it globally better.
*)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(** FULL: (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in the chapters
    developed to Imp, this overloading should not cause confusion.) *)

(* TERSE: HIDEFROMHTML *)

(** The definition of [bexp]s is unchanged (except that it now refers
    to the new [aexp]s): *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
(* TERSE: /HIDEFROMHTML *)

(** ** Notations *)
(** LATER: Maybe these notations and coercions should be introduced
    earlier in the chapter? *)

(** To make Imp programs easier to read and write, we introduce some
    notations and implicit coercions.  *)

(** TERSE: (The details are a bit hideous, but also not important to
    understand.) *)
(* TERSE: HIDEFROMHTML *)
(** FULL: You do not need to understand exactly what these declarations do.

    Briefly, though:
       - The [Coercion] declaration stipulates that a function (or
         constructor) can be implicitly used by the type system to
         coerce a value of the input type to a value of the output
         type.  For instance, the coercion declaration for [AId]
         allows us to use plain strings when an [aexp] is expected;
         the string will implicitly be wrapped with [AId].
       - [Declare Custom Entry com] tells Rocq to create a new "custom
         grammar" for parsing Imp expressions and programs. The first
         notation declaration after this tells Rocq that anything
         between [<{] and [}>] should be parsed using the Imp
         grammar. Again, it is not necessary to understand the
         details, but it is important to recognize that we are
         defining _new_ interpretations for some familiar operators
         like [+], [-], [*], [=], [<=], etc., when they occur between
         [<{] and [}>]. *)

(** TERSE: *** *)
(* NOTATION: LATER: We could perhaps avoid this (somewhat confusing)
   coercion by just defining all the single uppercase letters to be
   identifiers, rather than using strings. But we can't make a similar
   change in the lambda-expression syntax, where many more variable
   names are needed, so not clear it's a good idea here.

   Coq's new numeral syntax mechanism.

   NDS'25 that is not clear cut, as the string/int literal mechanisms
   is not really meant for custom scopes:
   https://github.com/rocq-prover/rocq/issues/9516
   https://github.com/rocq-prover/rocq/issues/9518
   We attempted to hack around this by entering a scope in the atom
   case of the grammar, but you'd end up with things being displayed as
   [<{ 5%com + "X"%com }>], which is not a clear win.

   We also briefly attempted to use this hack:
   https://github.com/rocq-prover/rocq/issues/15643
   this worked nicely for the syntax, but caused issues with pattern-matching.
   There should be a way to get it to work (this hack was used in Koika), but
   we did not figure it out.
   *)
Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

(* INSTRUCTORS: Some notations in this file are declared under a scope
   despite being also in a custom entry to allow us to change some of them
   later, e.g., in Hoare2.v.

   NDS'25
   Maybe we should migrate to a model without scopes (other than for entrypoints)
   but with multiple custom entries? *)

(* INSTRUCTORS: If anything changes here, make sure to do the same
   adjustment in all the other grammars for Imp-like languages...

   There are notes at the bottom of the file about some of the
   technical choices we've made in setting up the notations.  Search
   for REASONS. *)
Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e
  (e custom com, format "'[hv' <{ '/  ' '[v' e ']' '/' }> ']'") : com_scope.

Notation "( x )" := x (in custom com, x at level 99).
Notation "x" := x (in custom com at level 0, x constr at level 0).
(* NOTATION: SAZ 2024  I don't understand the rationale for why the arguments
   to embedded functions are put at level 9 of the constr grammar.

   SAZ 2024: Answering my own question.  In the general [term] grammar,
   function applications are parsed at precedence level 10 as:
     [SELF ; list1 arg] where [arg] is given by a grammar that invokes
     [term] at level 9.  So, in general, function arguments should be
   at level 9.  *HOWEVER* we want to give special precedence to some
   arguments in [Hoare.v].  I don't think we lose much if we ask these
   function arguments to parse at level 1 of the [constr] grammer. This
   will enable us to put the assertions in [Hoare.v] at a looser
   precedence.
 *)

Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 1,
                      y constr at level 1).
(* INSTRUCTORS: Template for expr *)
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

(* NOTATION: NDS'25 I'd recommend making this [Local] and opening the scope
   in every file which wants to use this notation, as that seems to be a better
   practice. *)
Open Scope com_scope.

(* HIDE *)
Locate "=".
Check <{ X + Y }>.
Check <{ X + Y = 0 }>.
Check <{ ~ (Y = X) }>.
Check <{ X + Y }>.
Check <{ ~ (X + Y = Y) && Z = W }>.
(* /HIDE *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)

(** We can now write [3 + (X * 2)] instead  of [APlus 3 (AMult X 2)],
    and [true && ~(X <= 4)] instead of [BAnd true (BNot (BLe X 4))]. *)

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

(* ################################################### *)
(** ** Evaluation *)

(** FULL: The arith and boolean evaluators must now be extended to
    handle variables in the obvious way, taking a state [st] as an
    extra argument: *)
(** TERSE: Now we need to add an [st] parameter to both evaluation
    functions: *)

Fixpoint aeval (st : state) (* <--- NEW *)
               (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (* <--- NEW *)
               (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

(** TERSE: *** *)
(** We can use our notation for total maps in the specific case of
    states -- i.e., we write the empty state as [(__ !-> 0)]. *)

Definition empty_st := (__ !-> 0).

(** Also, we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100, right associativity).


(* FULL *)
Example aexp1 :
    aeval (X !-> 5) <{ 3 + (X * 2) }>
  = 13.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
Example aexp2 :
    aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }>
  = 20.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4) }>
  = true.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* /FULL *)

(* ####################################################### *)
(** * Commands *)

(** Now we are ready to define the syntax and behavior of Imp
    _commands_ (or _statements_). *)

(* ################################################### *)
(** ** Syntax *)

(* HIDEFROMADVANCED *)
(** Informally, commands [c] are described by the following BNF
    grammar.
[[
     c := skip
        | x := a
        | c ; c
        | if b then c else c end
        | while b do c end
]]
 *)

(** FULL: Here is the formal definition of the abstract syntax of
    commands: *)
(** TERSE: Formally: *)

(* /HIDEFROMADVANCED *)
Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(** TERSE: *** *)
(** As we did for expressions, we can use a few [Notation]
    declarations to make reading and writing Imp programs more
    convenient. *)

(* TERSE: HIDEFROMHTML *)
(* NOTATION: NDS'25 changed the syntax to include new lines.
   Whether the boxes ('[..') should be regular, vertical (v)
   or horizontal-or-else-vertical (hv) is up to debate.
   I went with "force newlines" (using vertical boxes) because
   this should lead to fewer (bad) surprises.

   The crux of my pain is that Rocq does seem to have a very
   local definition of "fits on one line", i.e., if a subox
   spans multiple lines, but the current notation does not
   require line breaks other than the ones in the sub-notation, then
   it "fits on one line".*)
(* SOONER: (NOTATION NDS'25)
   I considered changing maps to also span multiple lines, but I
   have not attempted this yet, as this would have required changes
   in earlier chapters. *)
(* NOTATION: NDS'25
   We may want to experiment with forcing a newline after <{ ... }>. We
   currently get a "snake-like" display in some cases (see Smallstep:mult_while_h):
   c0 = <{ while true do
             skip
           end }> \/ c0 = <{ if true then
                               skip;
                               while true do
                                 skip
                               end
                             else
                                 skip
                             end }> \/ c0 = <{ skip;
                                               while true do
                                                skip
                                               end }> -> ...
    As much as I think this is an improvement over no line-breaks,
    this is far from optimal...
  *)
(* INSTRUCTORS: Template for com *)
Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99,
    format "'[v' 'while'  x  'do' '/  ' y '/' 'end' ']'") : com_scope.
(* TERSE: /HIDEFROMHTML *)

(* HIDE *)
Check <{ skip }>.
Check <{ skip; skip; skip; skip; skip; skip; skip }>.
Check <{ (skip ; skip) ; skip }>.
Check <{ 1 + 2 }>.
Check <{ 2 = 1 }>.
Check <{ Z := X }>.
Check <{ Z := X + 3 }>.
Definition func (c : com) : com := <{ c ; skip }>.
Check <{ skip; func <{ skip }> }>.
Definition func2 (c1 c2 : com) : com := <{ c1 ; c2 }>.
Check <{ skip ; func2 <{skip}> <{skip}> }>.
Check <{ true && ~(false && true) }>.
Check <{ if true then skip else skip end }>.
Check <{ if true && true then skip; skip else skip; X:=X+1 end }>.
Check <{ while Z <> 0 do Y := Y * Z; Z := Z - 1 end }>.
(* /HIDE *)

(* TERSE *)
(** *** *)
(* /TERSE *)
(** For example, here is the factorial function again, written as a
    formal Rocq definition.  When this command terminates, the variable
    [Y] will contain the factorial of the initial value of [X]. *)

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while Z <> 0 do
       Y := Y * Z;
       Z := Z - 1
     end }>.

(* HIDEFROMHTML *)
Print fact_in_coq.
(* /HIDEFROMHTML *)

(* FULL *)
(* LATER: MRC'20: this section is somewhat redundant w.r.t. the
   discussion of [Set Printing Coercions] that has already occurred
   above.  Would be nice to unify them. *)
(** ** Desugaring Notations *)

(** Rocq offers a rich set of features to manage the increasing
    complexity of the objects we work with, such as coercions and
    notations. However, their heavy usage can make it hard to
    understand what the expressions we enter actually mean. In such
    situations it is often instructive to "turn off" those features to
    get a more elementary picture of things, using the following
    commands:

    - [Unset Printing Notations] (undo with [Set Printing Notations])
    - [Set Printing Coercions] (undo with [Unset Printing Coercions])
    - [Set Printing All] (undo with [Unset Printing All])

    These commands can also be used in the middle of a proof, to
    elaborate the current goal and context. *)

Unset Printing Notations.
Print fact_in_coq.
(* ===>
   fact_in_coq =
   CSeq (CAsgn Z X)
        (CSeq (CAsgn Y (S O))
              (CWhile (BNot (BEq Z O))
                      (CSeq (CAsgn Y (AMult Y Z))
                            (CAsgn Z (AMinus Z (S O))))))
        : com *)
Set Printing Notations.

Print example_bexp.
(* ===> example_bexp = <{(true && ~ (X <= 4))}> *)

Set Printing Coercions.
(* LATER: Ori: CoqIde error msg:
   "Set this option from the IDE menu instead".
   I guess this is a recent change? *)
Print example_bexp.
(* ===> example_bexp = <{(true && ~ (AId X <= ANum 4))}> *)

Print fact_in_coq.
(* ===>
  fact_in_coq =
  <{ Z := (AId X);
     Y := (ANum 1);
     while ~ (AId Z) = (ANum 0) do
       Y := (AId Y) * (AId Z);
       Z := (AId Z) - (ANum 1)
     end }>
       : com *)
Unset Printing Coercions.

(** ** [Locate] Again *)
(* HIDE: MRC'20: this section is somewhat redundant w.r.t. a similar
   discussion in Maps. Would be nice to unify them.  BCP 21: I decided
   to leave them both, but added pointers in both places so it doesn't
   look like a mistake. *)

(** *** Finding identifiers *)

(** When used with an identifier, the [Locate] prints the full path to
    every value in scope with the same name.  This is useful to
    troubleshoot problems due to variable shadowing. *)
Locate aexp.
(* ===>
     Inductive LF.Imp.aexp
     Inductive LF.Imp.AExp.aexp
       (shorter name to refer to it in current context is AExp.aexp)
     Inductive LF.Imp.aevalR_division.aexp
       (shorter name to refer to it in current context is aevalR_division.aexp)
     Inductive LF.Imp.aevalR_extended.aexp
       (shorter name to refer to it in current context is aevalR_extended.aexp)
*)
(** *** Finding notations *)

(** When faced with an unknown notation, you can use [Locate] with a
    string containing one of its symbols to see its possible
    interpretations. *)
Locate "&&".
(* ===>
    Notation
      "x && y" := BAnd x y (default interpretation)
      "x && y" := andb x y : bool_scope (default interpretation)
*)
Locate ";".
(* ===>
    Notation
      "x '|->' v ';' m" := (update m x v) (default interpretation)
      "x ; y" := (CSeq x y) (default interpretation)
      "x '!->' v ';' m" := (t_update m x v) (default interpretation)
      "[ x ; y ; .. ; z ]" := cons x (cons y .. (cons z nil) ..) : list_scope
      (default interpretation) *)

Locate "while".
(* ===>
    Notation
      "'while' x 'do' y 'end'" :=
          (CWhile x y) (default interpretation)
*)
(* /FULL *)

(* HIDEFROMADVANCED *)
(* ####################################################### *)
(** ** More Examples *)

(** *** Assignment: *)

Definition plus2 : com :=
  <{ X := X + 2 }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

(** *** Loops *)

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.

Definition subtract_slowly : com :=
  <{ while X <> 0 do
       subtract_slowly_body
     end }>.

Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ;
     Z := 5 ;
     subtract_slowly }>.

(** *** An infinite loop: *)

Definition loop : com :=
  <{ while true do
       skip
     end }>.

(* HIDE *)
(** Exponentiation: *)
Definition exp_body : com :=
  <{ Z := Z * X ;
     Y := Y - 1 }>.
Definition pexp : com :=
  <{ while Y <> 0 do
       exp_body
     end }>.
(** (Note that [pexp] should be run in a state where [Z] is [1].) *)
(* /HIDE *)

(* /HIDEFROMADVANCED *)
(* ################################################################ *)
(** * Evaluating Commands *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [while] loops don't necessarily terminate makes
    defining an evaluation function tricky... *)

(* #################################### *)
(** ** Evaluation as a Function (Failed Attempt) *)

(** Here's an attempt at defining an evaluation function for commands
    (with a bogus [while] case). *)

(* LATER: In SmallStep we need to package the state and command into
   a pair, so that we can talk about normal forms and such.  Probably
   we should do it here too, for consistency.  (Won't change much
   except the type declarations, but we'll need to add a comment why
   we wrote them this way.) *)
Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ x := a }> =>
        (x !-> aeval st a ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | <{ while b do c end }> =>
        st  (* bogus *)
  end.
(* FULL *)

(** In a more conventional functional programming language like OCaml or
    Haskell we could add the [while] case as follows:
<<
        Fixpoint ceval_fun (st : state) (c : com) : state :=
          match c with
            ...
            | <{ while b do c end}> =>
                if (beval st b)
                  then ceval_fun st <{c ; while b do c end}>
                  else st
          end.
>>
    Rocq doesn't accept such a definition ("Error: Cannot guess
    decreasing argument of fix") because the function we want to
    define is not guaranteed to terminate. Indeed, it _doesn't_ always
    terminate: for example, the full version of the [ceval_fun]
    function applied to the [loop] program above would never
    terminate. Since Rocq aims to be not just a functional programming
    language but also a consistent logic, any potentially
    non-terminating function needs to be rejected.

    Here is an example showing what would go wrong if Rocq allowed
    non-terminating recursive functions:
<<
         Fixpoint loop_false (n : nat) : False := loop_false n.
>>
    That is, propositions like [False] would become provable
    ([loop_false 0] would be a proof of [False]), which would be
    a disaster for Rocq's logical consistency.

    Thus, because it doesn't terminate on all inputs, [ceval_fun]
    cannot be written in Rocq -- at least not without additional tricks
    and workarounds (see chapter \CHAP{ImpCEvalFun} if you're curious
    about those). *)
(* HIDE: Perhaps that discussion should be moved to -- or previewed
   in -- Logic.v?  MRC'20: It's already in ProofObjects (which not
   everyone sees). *)
(* /FULL *)

(* TERSE *)
(** *** Nontermination leads to Inconsistency *)
(** Consider the following "proof object":

<<
        Fixpoint loop_false (n : nat) : False := loop_false n.
>>

     Accepting such a definition would be catastrophic, so Rocq
     conservatively rejects _all_ nonterminating (or potentially
     non-terminating, or not-obviously-terminating) programs.
*)
(* /TERSE *)

(* #################################### *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., make its result a [Prop] rather than a
    [state], similar to what we did for [aevalR] above. *)


(* FULL *)
(* HIDEFROMADVANCED *)
(** This is an important change.  Besides freeing us from awkward
    workarounds, it gives us a ton more flexibility in the definition.
    For example, if we add nondeterministic features like [any] to the
    language, we want the definition of evaluation to be
    nondeterministic -- i.e., not only will it not be total, it will
    not even be a function! *)

(* /HIDEFROMADVANCED *)
(* /FULL *)
(** We'll use the notation [st =[ c ]=> st'] for the [ceval] relation:
    [st =[ c ]=> st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(** *** Operational Semantics *)

(* SOONER: BCP 21: I wonder if E_Seq would be easier to work with if
   st' and st'' were swapped...*)
(** Here is an informal definition of evaluation, presented as inference
    rules for readability:
[[[
                           -----------------                            (E_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                      (E_Asgn)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                           (E_Seq)
                         st =[ c1;c2 ]=> st''

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------                 (E_WhileTrue)
                  st  =[ while b do c end ]=> st''
]]]
*)

(* HIDE: APT: Investigate rewriting these to use equality hypotheses
   rather than repeated variables in the conclusion.  For example:

      E_Skip : forall st st', st = st' -> st =[ skip ]=> st'.

   This makes the constructors easier to apply, and allows us to "swap
   in" an equivalence in place of equality.

  BAY: It sounds nice, but I tried this (23 Feb 2011) and didn't
    really find any benefit. The only difference seemed to be that it
    made quite a few proofs a tiny bit more annoying, due to the need
    for an extra 'reflexivity' or 'subst' or what have you. *)

(** FULL: Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)
(** TERSE: *** *)

(* NOTATION: LATER: Consider
                "st '={' c '}=>' st'"
             or
                "st '=<{' c '}>=>' st'"
*)
(* INSTRUCTORS: Template for eval *)
(* HIDEFROMHTML *)
(* NOTATION: NDS'25 should we change the level to force parentheses
   around when on the left-hand side of an arrow? *)
Reserved Notation
         "st0 '=[' c ']=>' st1"
         (at level 40, c custom com at level 99,
          st0 constr, st1 constr at next level,
          format "'[hv' st0  =[ '/  ' '[' c ']' '/' ]=>  st1 ']'").
(* /HIDEFROMHTML *)

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st0 =[ c ]=> st1" := (ceval c st0 st1).
(** TERSE: *** *)

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct a _proof_ that some
    program evaluates to some result state, rather than just letting
    Rocq's computation mechanism do it for us. *)

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Asgn. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

(* FULL *)
(* EX2 (ceval_example2) *)
Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  (* ADMITTED *)
  apply E_Seq with (X !-> 0).
  - (* first assignment command *)
    apply E_Asgn. reflexivity.
  - (* second ; *)
    apply E_Seq with (Y !-> 1 ; X !-> 0).
    + (* second assignment command *)
      apply E_Asgn. reflexivity.
    + (* third assignment *)
      apply E_Asgn. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

Set Printing Implicit.
Check @ceval_example2.

(* EX3? (pup_to_n) *)
(** Write an Imp program that sums the numbers from [1] to [X]
    (inclusive: [1 + 2 + ... + X]) in the variable [Y].  Your program
    should update the state as shown in theorem [pup_to_2_ceval],
    which you can reverse-engineer to discover the program you should
    write.  The proof of that theorem will be somewhat lengthy. *)
(* HIDE: CH: This is hard to solve without eapply.
   Decreased number of iterations to 2. Made the whole thing optional. *)

Definition pup_to_n : com
  (* ADMITDEF *) :=
  <{ Y := 0;
     while (1 <= X) do
       Y := Y + X;
       X := X - 1
     end }>.
(* /ADMITDEF *)

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
(* HIDE: Result is the same as (X !-> 0 ; Y !-> 3)
   if one admits functional extensionality *)
Proof.
  (* ADMITTED *)
  unfold pup_to_n.
  apply E_Seq with (Y !-> 0; X !-> 2).
  - (* assignment command *)
    apply E_Asgn. reflexivity.
  - (* while command *)
    apply E_WhileTrue with (X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
    + reflexivity.
    + (* first round *)
      apply E_Seq with (Y !-> 2; Y !-> 0; X !-> 2); apply E_Asgn; reflexivity.
    + (* the other rounds *)
      apply E_WhileTrue with (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
      * reflexivity.
      * (* second round *)
        apply E_Seq with (Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2); apply E_Asgn; reflexivity.
      * (* no more rounds *)
        apply E_WhileFalse. reflexivity. Qed.
(* /ADMITTED *)
(** [] *)
(* LATER: Comment from reader: Another good place to mention lack of
   functional extensionality. The 6 [t_update]s in the above theorem are
   not redundant, nor would [pup_to_2_ceval] be provable if the
   algorithm would be defined differently (e.g., if it would use [Z]
   as a "buffer" variable instead of decrementing [X]). *)
(* /FULL *)

(** TERSE: What sorts of things might we want to prove using these
    definitions?

    Here are some simple examples...
*)
(* HIDE: PR: I phrased these quizzes with the following alternatives:

   (A) Not true

   (B) True and easily provable in Rocq

   (C) True and takes more work to prove in Rocq

   (D) True and cannot be proved in Rocq without additional axioms
*)
(* QUIZ *)
(** Is the following proposition provable?
[[
      forall (c : com) (st st' : state),
        st =[ skip ; c ]=> st' ->
        st =[ c ]=> st'
]]
    (A) Yes

    (B) No

    (C) Not sure

*)
(* HIDE *)
Lemma quiz1_answer :  forall c st st',
  st =[ skip ; c ]=> st' ->
  st =[ c ]=> st'.
Proof.
  intros c st st' E.
  inversion E.
  inversion H1.
  subst.
  assumption.
Qed.

(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** Is the following proposition provable?
[[
      forall (c1 c2 : com) (st st' : state),
          st =[ c1 ; c2 ]=> st' ->
          st =[ c1 ]=> st ->
          st =[ c2 ]=> st'
]]
    (A) Yes

    (B) No

    (C) Not sure

*)
(* INSTRUCTORS: Answer is given later as it depends on
   ceval_deterministic *)
(* /QUIZ *)
(* QUIZ *)
(** Is the following proposition provable?
[[
      forall (b : bexp) (c : com) (st st' : state),
          st =[ if b then c else c end ]=> st' ->
          st =[ c ]=> st'
]]
    (A) Yes

    (B) No

    (C) Not sure

*)
(* INSTRUCTORS *)
Lemma quiz3_answer: forall (b : bexp) (c : com) (st st' : state),
  st =[ if b then c else c end]=> st' ->
  st =[ c ]=> st'.
Proof.
  intros b c st st' H. inversion H.
  - subst. assumption.
  - subst. assumption.
Qed.
(* /INSTRUCTORS *)
(* /QUIZ *)
(* QUIZ *)
(** Is the following proposition provable?
[[
      forall b : bexp,
         (forall st, beval st b = true) ->
         forall (c : com) (st : state),
           ~(exists st', st =[ while b do c end ]=> st')
]]
    (A) Yes

    (B) No

    (C) Not sure

*)
(* HIDE *)
(* This one is tricky! *)
Lemma quiz4_answer: forall b : bexp,
  (forall st, beval st b = true) ->
  forall (c : com) (st : state),
    ~(exists st', st =[ while b do c end ]=> st').
Proof.
  intros b H c st.
  unfold not.
  intros W.
  destruct W as [st' WW].
  remember <{ while b do c end }> as cc.
  induction WW; try discriminate Heqcc; inversion Heqcc; subst.
  (* NOTATION NDS'25 another weird layout after the next bullet ...*)
  - rewrite H in H0. discriminate H0.
  - apply IHWW2. reflexivity.
Qed.
(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** Is the following proposition provable?
[[
      forall (b : bexp) (c : com) (st : state),
         ~(exists st', st =[ while b do c end ]=> st') ->
         forall st'', beval st'' b = true
]]
    (A) Yes

    (B) No

    (C) Not sure

*)
(* HIDE *)
Lemma quiz5_answer: forall (b : bexp) (c : com) (st : state),
  ~(exists st', st =[ while b do c end ]=> st') ->
  forall st'', beval st'' b = true.
Proof.
  intros b c st H st''.
Abort. (* Can't make any progress - claim is false! *)
(* /HIDE *)
(* /QUIZ *)

(* ####################################################### *)
(** ** Determinism of Evaluation *)

(* LATER: Maybe this should go at the end of the file in a section
   marked optional?  Not everybody will want to spend time on it. *)
(** TERSE: Finally, we should pause to check that our evaluation
    relation really is a (partial) function... *)
(* FULL *)
(** Changing from a computational to a relational definition of
    evaluation is a good move because it frees us from the artificial
    requirement that evaluation should be a total function.  But it
    also raises a question: Is the second definition of evaluation
    really a partial _function_?  Or is it possible that, beginning from
    the same state [st], we could evaluate some command [c] in
    different ways to reach two different output states [st'] and
    [st'']?

    In fact, this cannot happen: [ceval] _is_ a partial function: *)
(* /FULL *)
(* LATER: Informal proof needed!  (And one can surely be found in
   some past CIS500 exam solutions!) *)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
(* FOLD *)
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.
(* /FOLD *)

(* HIDE *)
(* Answer to previous quiz. *)
Lemma quiz2_answer : forall c1 c2 st st',
  st =[ c1;c2 ]=> st' ->
  st =[ c1 ]=> st ->
  st =[ c2 ]=> st'.
Proof.
  intros c1 c2 st st' H1 H2.
  inversion H1. subst.
  rewrite ceval_deterministic with (c := c1) (st := st)
                                   (st1 := st) (st2 := st'0);
     assumption.
Qed.
(* /HIDE *)

(* FULL *)
(* ####################################################### *)
(** * Reasoning About Imp Programs *)

(* LATER: This section doesn't seem very useful -- to anybody!  It
   takes too much time to go through it in class, and even for
   advanced students it's too low-level and grubby to be a very
   convincing motivation for what follows -- i.e., to feel motivated
   by its grubbiness, you have to understand it, but this takes more
   time than it's worth.  Better to cut the whole rest of the
   file (except the further exercises at the very end), or at least
   make it optional.

   (BCP 10/18: However, this removes quite a few exercises. Is the
   homework assignment still meaty enough?  I'm going to leave it
   as-is for now, but we should reconsider this later.) *)

(** We'll get into more systematic and powerful techniques for
    reasoning about Imp programs in _Programming Language
    Foundations_, but we can already do a few things (albeit in a
    somewhat low-level way) just by working with the bare definitions.
    This section explores some examples. *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.

  (** Inverting [Heval] essentially forces Rocq to expand one step of
      the [ceval] computation -- in this case revealing that [st']
      must be [st] extended with the new value of [X], since [plus2]
      is an assignment. *)

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

(* LATER: This used to be recommended.  Should it be reinstated? *)
(* EX3? (XtimesYinZ_spec) *)
(** State and prove a specification of [XtimesYinZ]. *)

(* SOLUTION *)
(* Here is a specification in the style of plus2_spec *)
Theorem XtimesYinZ_spec1 : forall st nx ny st',
  st X = nx ->
  st Y = ny ->
  st =[ XtimesYinZ ]=> st' ->
  st' Z = nx * ny.
Proof.
  intros st nx ny st' HX HY Heval.
  (* Start by inverting the assignment *)
  inversion Heval. subst.
  apply t_update_eq.  Qed.

(* Though perhaps a cleaner specification would be: *)
Theorem XtimesYinZ_spec : forall st,
  st =[ XtimesYinZ ]=> (Z !-> st X * st Y ; st ).
Proof. intros. apply E_Asgn. reflexivity. Qed.

(* A less informative specification would be ... *)
Theorem XtimesYinZ_spec2 : forall st, exists st',
  st =[ XtimesYinZ ]=> st'.
Proof.
  intros. exists (Z !-> st X * st Y ; st).
  apply E_Asgn. reflexivity.
Qed.
(* /SOLUTION *)

(* GRADE_MANUAL 3: XtimesYinZ_spec *)
(** [] *)

(* EX3! (loop_never_stops) *)
Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn:Heqloopdef.

  (** Proceed by induction on the assumed derivation showing that
      [loopdef] terminates.  Most of the cases are immediately
      contradictory and so can be solved in one step with
      [discriminate]. *)

  (* ADMITTED *)
  induction contra; try (discriminate Heqloopdef).
  - (* E_WhileFalse *)
      injection Heqloopdef as H0 H1. rewrite -> H0 in H. discriminate H.
    - (* E_WhileTrue *) apply IHcontra2. apply Heqloopdef. Qed.

(* /ADMITTED *)
(** [] *)
(* LATER: Marc Bezem 2022:

    4. There are trade-offs between using tactics and additional lemmas.
    Here are some cases where I think a lemma would make things clearer.

    Imp.v, l. 1612: Theorem loop_never_stops :
                       forall st st', ~(st =[ loop ]=> st').

    The surprise here is that this is proved by induction, and the
    tactic "remember" is hard to understand.
    The following formulation explains the induction better:

    Theorem loop_never_stops' : forall st st' c,
      st =[ c ]=> st' -> c = loop -> False.
    Proof. intros st st' c Hopsem.
      induction Hopsem; try discriminate; intro Loopbc; injection Loopbc;
      intros Ecskip Ebtrue; subst.
      - discriminate.
      - apply IHHopsem2. assumption.
    Qed.

    The equivalence of the two formulations is an easy lemma.

    BCP 23: Not sure I see a big difference between the two presentations:
    both statements are negations, and the [remember] in the proof is avoided in the
    new one by introducing an equality in the theorem statement that IMO
    is not very pretty...
*)

(* EX3 (no_whiles_eqv) *)
(** Consider the following function: *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> =>
      true
  | <{ _ := _ }> =>
      true
  | <{ c1 ; c2 }> =>
      andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }>  =>
      false
  end.

(** This predicate yields [true] just on programs that have no while
    loops.  Using [Inductive], write a property [no_whilesR] such that
    [no_whilesR c] is provable exactly when [c] is a program with no
    while loops.  Then prove its equivalence with [no_whiles]. *)

Inductive no_whilesR: com -> Prop :=
 (* SOLUTION *)
 | nw_Skip: no_whilesR <{ skip }>
 | nw_Asgn: forall x ae, no_whilesR <{ x := ae }>
 | nw_Seq: forall c1 c2,
     no_whilesR c1 ->
     no_whilesR c2 ->
     no_whilesR <{ c1 ; c2 }>
 | nw_If: forall be c1 c2,
     no_whilesR c1 ->
     no_whilesR c2 ->
     no_whilesR <{ if be then c1 else c2 end }>
(* /SOLUTION *)
.

Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  (* ADMITTED *)
  intros; split.
  - (* -> *)
    induction c; intro Hc;
      try (simpl in Hc; rewrite andb_true_iff in Hc;
        destruct Hc as [Hc1 Hc2]);
      try constructor;
      try (apply IHc1; assumption); try (apply IHc2; assumption).
    + (* while *) discriminate Hc.
  - (* <- *)
    intro H. induction H; simpl;
      try reflexivity;
      try (rewrite IHno_whilesR1; rewrite IHno_whilesR2; reflexivity).
  Qed.
  (* /ADMITTED *)
(** [] *)

(* EX4 (no_whiles_terminating) *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)
(** FULL: Use either [no_whiles] or [no_whilesR], as you prefer. *)

(* SOLUTION *)
(* Here is a solution by induction on no_whilesR: *)
Theorem no_whiles_terminating : forall c st,
  no_whilesR c ->
  exists st',
  st =[ c ]=> st'.
Proof.
  intros c st H. generalize dependent st.
  induction H; intros; simpl.
  - (* nw_Skip *) exists st. constructor.
  - (* nw_Asgn *) exists (x !-> (aeval st ae) ; st).
    constructor. reflexivity.
  - (* nw_Seq *)
    destruct (IHno_whilesR1 st) as [st' IH'].
    destruct (IHno_whilesR2 st') as [st'' IH''].
    exists st''. apply E_Seq with st'; assumption.
  - (* nw_If *)
    destruct (beval st be) eqn:Heqbv.
    + (* bv = true *)
      destruct (IHno_whilesR1 st) as [st' IH'].
      exists st'. apply E_IfTrue.
      * rewrite Heqbv. reflexivity.
      * assumption.
    + (* bv = false *)
      destruct (IHno_whilesR2 st) as [st' IH'].
      exists st'. apply E_IfFalse.
      * rewrite Heqbv. reflexivity.
      * assumption.
Qed.

(* And here is an alternative solution by induction on c: *)
Theorem no_whiles_terminating' : forall c st1,
  no_whiles c = true ->
  exists st2, st1 =[ c ]=> st2.
Proof.
  induction c; intros st1 Hb.

  - (* skip *)
    exists st1. apply E_Skip.

  - (* := *)
    exists (x !-> aeval st1 a ; st1). apply E_Asgn. reflexivity.

  - (* ; *)
    simpl in Hb.
    rewrite andb_true_iff in Hb.
    destruct Hb as [Hb1 Hb2].
    apply (IHc1 st1) in Hb1. destruct Hb1 as [st1' ceH1].
    apply (IHc2 st1') in Hb2. destruct Hb2 as [st1'' ceH2].
    exists st1''.
    apply E_Seq with (st' := st1'); assumption.

  - (* if *)
    simpl in Hb. rewrite andb_true_iff in Hb.
    destruct Hb as [Hb1 Hb2].
    destruct (beval st1 b) eqn:Heqbv.
    + (* E_IfTrue *)
      apply (IHc1 st1) in Hb1.
      destruct Hb1 as [st2 Hce1]. exists st2.
      apply E_IfTrue.
      * (* b is true *)
        rewrite <- Heqbv. reflexivity.
      * (* true branch eval *)
        assumption.
    + (* E_IfFalse *)
      apply (IHc2 st1) in Hb2.
      destruct Hb2 as [st2 Hce2]. exists st2.
      apply E_IfFalse.
      * (* b is false *)
        rewrite <- Heqbv. reflexivity.
      * (* false branch eval *)
        assumption.

  - (* while *)
    discriminate Hb.  Qed.
(* /SOLUTION *)

(* GRADE_MANUAL 6: no_whiles_terminating *)
(** [] *)
(* /FULL *)

(* LATER: The following section always gets skipped over when I (BCP)
   teach the course, because there isn't time to go through all the
   details and we're going to see the right way to do the same thing
   in a later chapter, so I am hiding it for now.  I wouldn't mind
   reinstating it for the use of advanced / self-study readers if
   somebody wants to write some text to really explain it, but what's
   there is a bit too telegraphic, so I'm removing it for now. *)
(* HIDE *)
(* ####################################################### *)
(** * Case Study (Optional) *)

(** Recall the factorial program (broken up into smaller pieces this
    time, for convenience of proving things about it).  *)

Definition fact_body : com :=
  <{ Y := Y * Z ;
     Z := Z - 1 }>.

Definition fact_loop : com :=
  <{ while Z <> 0 do
       fact_body
     end }>.

Definition fact_com : com :=
  <{ Z := X ;
     Y := 1 ;
     fact_loop }>.

(** Here is an alternative "mathematical" definition of the factorial
    function: *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** We would like to show that they agree -- if we start [fact_com] in
    a state where variable [X] contains some number [n], then it will
    terminate in a state where variable [Y] contains the factorial of
    [n].

    To show this, we rely on the critical idea of a _loop
    invariant_. *)

Definition fact_invariant (n:nat) (st:state) : Prop :=
  (st Y) * (real_fact (st Z)) = real_fact n.

(** We show that the body of the factorial loop preserves the invariant: *)

(* LATER: Needs an informal proof! *)
Theorem fact_body_preserves_invariant: forall st st' n,
     fact_invariant n st ->
     st Z <> 0 ->
     st =[ fact_body ]=> st' ->
     fact_invariant n st'.
(* FOLD *)
Proof.
  unfold fact_invariant, fact_body.
  intros st st' n Hm HZnz He.
  inversion He; subst; clear He.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  unfold t_update. simpl.
  (* Show that st Z = S z' for some z' *)
  destruct (st Z) as [| z'].
  - exfalso. apply HZnz. reflexivity.
  - rewrite <- Hm. rewrite <- mul_assoc.
    replace (S z' - 1) with z' by lia.
    reflexivity.  Qed.
(* /FOLD *)

(** From this, we can show that the whole loop also preserves the
    invariant: *)

Theorem fact_loop_preserves_invariant : forall st st' n,
     fact_invariant n st ->
     st =[ fact_loop ]=> st' ->
     fact_invariant n st'.
(* FOLD *)
Proof.
  intros st st' n H Hce.
  remember fact_loop as c.
  induction Hce; inversion Heqc; subst; clear Heqc.
  - (* E_WhileFalse *)
    (* trivial when the loop doesn't run... *)
    assumption.
  - (* E_WhileTrue *)
    (* if the loop does run, we know that fact_body preserves
       fact_invariant -- we just need to assemble the pieces *)
    apply IHHce2.
    + apply fact_body_preserves_invariant with st;
            try assumption.
      intros Contra. simpl in H0; subst.
      rewrite Contra in H0. inversion H0.
    + reflexivity.  Qed.
(* /FOLD *)

(** Next, we show that, for any loop, if the loop terminates, then the
    condition guarding the loop must be false at the end: *)

Theorem guard_false_after_loop: forall b c st st',
     st =[ while b do c end ]=> st' ->
     beval st' b = false.
(* FOLD *)
Proof.
  intros b c st st' Hce.
  remember <{ while b do c end }> as cloop.
  induction Hce; inversion Heqcloop; subst; clear Heqcloop.
  - (* E_WhileFalse *)
    assumption.
  - (* E_WhileTrue *)
    apply IHHce2. reflexivity.  Qed.
(* /FOLD *)

(** Finally, we can patching it all together... *)

Theorem fact_com_correct : forall st st' n,
     st X = n ->
     st =[ fact_com ]=> st' ->
     st' Y = real_fact n.
(* FOLD *)
Proof.
  intros st st' n HX Hce.
  inversion Hce; subst; clear Hce.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  inversion H1; subst; clear H1.
  rename st' into st''. simpl in H5.
  (* The invariant is true before the loop runs... *)
  remember (Y !-> 1 ; Z !-> st X ; st) as st' eqn:Heqst'.
  assert (fact_invariant (st X) st').
  + subst. unfold fact_invariant, t_update. simpl. lia.
  (* ...so when the loop is done running, the invariant
     is maintained *)
  + assert (fact_invariant (st X) st'').
    * apply fact_loop_preserves_invariant with st'; assumption.
    * unfold fact_invariant in H0.
    (* Finally, if the loop terminated, then Z is 0; so Y must be
       factorial of X *)
      apply guard_false_after_loop in H5. simpl in H5.
      destruct (st'' Z) eqn:E.
      { (* st'' Z = 0 *) simpl in H0. lia. }
      {(* st'' Z > 0 (impossible) *) inversion H5. }
Qed.
(* /FOLD *)

(** One might wonder whether all this work with poking at states and
    unfolding definitions could be ameliorated with some more powerful
    lemmas and/or more uniform reasoning principles... Indeed, this is
    exactly the point of the \CHAP{Hoare} chapters in _Programming
    Language Foundations_! *)

(* FULL *)
(* EX4? (subtract_slowly_spec) *)
(** Prove a specification for [subtract_slowly], using the above
    specification of [fact_com] and the invariant below as
    guides. *)

Definition ss_invariant (n:nat) (z:nat) (st:state) : Prop :=
  ((st Z) - st X) = (z - n).

(* SOLUTION *)
Theorem ss_body_preserves_invariant : forall st n z st',
     ss_invariant n z st ->
     st X <> 0 ->
     st =[ subtract_slowly_body ]=> st' ->
     ss_invariant n z st'.
Proof.
  unfold ss_invariant.
  intros st n z st' H Hnz He.
  inversion He; subst; clear He.
  inversion H2; subst; clear H2.
  inversion H5; subst; clear H5.
  unfold t_update. simpl.
  lia. (* Interestingly, this is all we need here -- although we see this
          only after a perceptible delay! *)
Qed.

Theorem ss_preserves_invariant : forall st n z st',
     ss_invariant n z st ->
     st =[ subtract_slowly ]=> st'  ->
     ss_invariant n z st'.
Proof.
  intros st n z st' H He.
  remember subtract_slowly as c.
  induction He; inversion Heqc; subst; clear Heqc.
  - (* E_WhileFalse *)
    assumption.
  - (* E_WhileTrue *)
    apply IHHe2; try reflexivity.
    apply ss_body_preserves_invariant with st; try assumption.
    intros Contra. simpl in H0. rewrite Contra in H0. inversion H0.  Qed.

Theorem ss_correct : forall st n z st',
     st X = n ->
     st Z = z ->
     st =[ subtract_slowly ]=> st' ->
     st' Z = (z - n).
Proof.
  intros st n z st' HX HZ He.
  assert (ss_invariant n z st).
  - unfold ss_invariant.
    subst.
    reflexivity.
  - assert (ss_invariant n z st').
    + apply ss_preserves_invariant with st; assumption.
    + unfold ss_invariant in H0.
    apply guard_false_after_loop in He. simpl in He.
    destruct (st' X) eqn:E.
    * (* st' X = 0 *) lia.
    * (* st' X > 0 (impossible) *) inversion He.
Qed.
(* /SOLUTION *)
(** [] *)
(* /HIDE *)

(* TERSE: HIDEFROMHTML *)
(* HIDE: N.b.: No "FULL" here because this exercise is needed for the
   TERSE version of the Smallstep chapter. *)
(* ####################################################### *)
(** * Additional Exercises *)

(* EX3 (stack_compiler) *)
(** Old HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a _stack_. For instance, the expression
<<
      (2*3)+(3*(4-2))
>>
   would be written as
<<
      2 3 * 3 4 2 - * +
>>
   and evaluated like this (where we show the program being evaluated
   on the right and the contents of the stack on the left):
<<
      [ ]           |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |
>>
  The goal of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract the first number from the second.
     - [SMult]:   Similar, but multiply. *)

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

(** Write a function to evaluate programs in the stack language. It
    should take as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and it should return the
    stack after executing the program.  Test your function on the
    examples below.

    Note that it is unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    fewer than two elements.  In a sense, it is immaterial what we do,
    since a correct compiler will never emit such a malformed program.
    But for sake of later exercises, it would be best to skip the
    offending instruction and continue with the next one.  *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat
  (* ADMITDEF *) :=
  match (prog, stack) with
  | (nil,             _           ) => stack
  | (SPush n::prog',  _           ) => s_execute st (n::stack) prog'
  | (SLoad x::prog',  _           ) => s_execute st (st x::stack) prog'
  | (SPlus::prog',    n::m::stack') => s_execute st ((m+n)::stack') prog'
  | (SMinus::prog',   n::m::stack') => s_execute st ((m-n)::stack') prog'
  | (SMult::prog',    n::m::stack') => s_execute st ((m*n)::stack') prog'
  | (_::prog',        _           ) => s_execute st stack prog'
                                       (* Bad state: skip *)
  end.
(* /ADMITDEF *)

Check s_execute.

Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
(* ADMITTED *)
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* /ADMITTED *)
(* GRADE_THEOREM 1: s_execute1 *)

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
(* ADMITTED *)
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: s_execute2 *)

(** Next, write a function that compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr
  (* ADMITDEF *) :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | <{ a1 + a2 }> => s_compile a1 ++ s_compile a2 ++ [SPlus]
  | <{ a1 - a2 }>  => s_compile a1 ++ s_compile a2 ++ [SMinus]
  | <{ a1 * a2 }> => s_compile a1 ++ s_compile a2 ++ [SMult]
  end.
(* /ADMITDEF *)

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
  s_compile <{ X - (2 * Y) }>
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
(* ADMITTED *)
Proof. reflexivity. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1.5: s_compile1 *)
(** [] *)

(* EX3 (execute_app) *)

(** Execution can be decomposed in the following sense: executing
    stack program [p1 ++ p2] is the same as executing [p1], taking
    the resulting stack, and executing [p2] from that stack. Prove
    that fact. *)

Theorem execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  (* ADMITTED *)
  intros st. induction p1.
  - reflexivity.
  - intros p2 stack. destruct a; simpl; try apply IHp1;
    destruct stack as [ | x [ | y t ] ]; simpl; try apply IHp1.
Qed.
(* /ADMITTED *)

(** [] *)

(* EX3 (stack_compiler_correct) *)

(* HIDE: MRC'20: this had been a 4-star advanced exercise.  I think
   it's a shame to relegate this to the advanced track, because it's
   really the payoff of this entire chapter.  Everyone deserves to
   prove the correctness of this little compiler!  It's such a
   rewarding, compelling result to prove.  In Spring 2019 I used the
   decomposition here, including the previous exercise, and students
   generally were successful. I'd like to propose making it the
   standard version. *)

(* HIDE: Adam Chlipala's book has a slicker solution which does it all
   in a single induction... APT: Slicker, but arguably harder to
   understand. *)

(** Now we'll prove the correctness of the compiler implemented in the
    previous exercise.  Begin by proving the following lemma. If it
    becomes difficult, consider whether your implementation of
    [s_execute] or [s_compile] could be simplified. *)

Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  (* ADMITTED *)
  induction e;
    try reflexivity ; (* Push, Load *)
    intros; simpl;   (* Plus, Minus, Mult *)
      repeat rewrite execute_app;
      rewrite IHe1; rewrite IHe2; simpl; reflexivity.
Qed.
(* /ADMITTED *)

(** The main theorem should be a very easy corollary of that lemma. *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* ADMITTED *)
  intros. apply s_compile_correct_aux.
Qed.
(* /ADMITTED *)

(* GRADE_THEOREM 2.5: s_compile_correct_aux *)
(* GRADE_THEOREM 0.5: s_compile_correct *)

(** [] *)

(* TERSE: /HIDEFROMHTML *)

(* FULL *)
(* EX3? (short_circuit) *)
(** Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval].  (N.b. This is only true because expression
    evaluation in Imp is rather simple.  In a bigger language where
    evaluating an expression might diverge, the short-circuiting [BAnd]
    would _not_ be equivalent to the original, since it would make more
    programs terminate.) *)

(* SOLUTION *)
Fixpoint beval_sc (st : state) (e : bexp) : bool :=
  match e with
  | <{ true }>       => true
  | <{ false }>      => false
  | <{ a1 = a2 }>    => (aeval st a1) =? (aeval st a2)
  | <{ a1 <> a2 }>   => negb ((aeval st a1) =? (aeval st a2))
  | <{ a1 <= a2 }>   => (aeval st a1) <=? (aeval st a2)
  | <{ a1 > a2 }>    => negb ((aeval st a1) <=? (aeval st a2))
  | <{ ~ b1 }>       => negb (beval_sc st b1)
  | <{ b1 && b2 }>   =>  match (beval_sc st b1) with
                         | false => false
                         | true  => (beval_sc st b2)
                         end
  end.

(* This exercise turned out to be easier than we intended! *)
Theorem beval__beval_sc : forall st e,
  beval st e = beval_sc st e.
Proof.
  intros st e.
  destruct e; reflexivity.
Qed.
(* /SOLUTION *)
(** [] *)

Module BreakImp.
(* EX4? (break_imp) *)
(** Imperative languages like C and Java often include a [break] or
    similar statement for interrupting the execution of loops. In this
    exercise we consider how to add [break] to Imp.  First, we need to
    enrich the language of commands with an additional case. *)

Inductive com : Type :=
  | CSkip
  | CBreak                        (* <--- NEW *)
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'break'" := CBreak (in custom com at level 0) : com_scope.
(* INSTRUCTORS: Copy of template com *)
Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99,
    format "'[v' 'while'  x  'do' '/  ' y '/' 'end' ']'") : com_scope.

(** Next, we need to define the behavior of [break].  Informally,
    whenever [break] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the [break]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [break]. In those cases, [break] should only
    terminate the _innermost_ loop. Thus, after executing the
    following...
[[
       X := 0;
       Y := 1;
       while 0 <> Y do
         while true do
           break
         end;
         X := 1;
         Y := Y - 1
       end
]]
    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [break] statement: *)

Inductive result : Type :=
  | SContinue
  | SBreak.

(* INSTRUCTORS: Copy of template eval *)
(* HIDEFROMHTML *)
Reserved Notation
         "st0 '=[' c ']=>' st1 '/' s"
         (at level 40, c custom com at level 99,
          st0 constr, st1 constr at next level,
          format "'[hv' st0  =[ '/  ' '[' c ']' '/' ]=>  st1 / s ']'").
(* /HIDEFROMHTML *)

(** Intuitively, [st =[ c ]=> st' / s] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[st =[ c ]=> st' / s]" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([st =[ c ]=> st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [skip], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [break], the state stays unchanged but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [if b then c1 else c2 end], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ; c2], we first execute
      [c1].  If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal
      generated there.

    - Finally, for a loop of the form [while b do c end], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises.  If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration.  In either case, since [break] only terminates the
      innermost loop, [while] signals [SContinue]. *)

(** Based on the above description, complete the definition of the
    [ceval] relation. *)

(* QUIETSOLUTION *)

(** Because we include if syntax for the if syntax in com,
    we cannot use typical coq if syntax. We avoid this issues
    by making a function that encodes the behavior of if *)
Definition if_then_else {A : Type} (b : bool) (l r : A) :=
  if b then l else r.

(* /QUIETSOLUTION *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  (* SOLUTION *)
  | E_Break : forall st,
      st =[ CBreak ]=> st / SBreak
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st) / SContinue
  | E_SeqContinue : forall c1 c2 st st' st'' s,
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / s ->
      st =[ c1 ; c2 ]=> st'' / s
  | E_SeqBreak : forall c1 c2 st st',
      st =[ c1 ]=> st' / SBreak ->
      st =[ c1 ; c2 ]=> st' / SBreak
  | E_If : forall c1 c2 b st st' s,
      st =[ if_then_else (beval st b) c1 c2 ]=> st' / s ->
      st =[ if b then c1 else c2 end ]=> st' / s
  | E_WhileFalse : forall c b st,
      beval st b = false ->
      st =[ while b do c end ]=> st / SContinue
  | E_WhileContinue : forall c b st st' st'',
      beval st b = true ->
      st  =[ c ]=> st' / SContinue ->
      st' =[ while b do c end ]=> st'' / SContinue ->
      st  =[ while b do c end ]=> st'' / SContinue
  | E_WhileBreak : forall c b st st',
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
      st =[ while b do c end ]=> st' / SContinue
  (* /SOLUTION *)

  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

(** Now prove the following properties of your definition of [ceval]: *)

Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.
Proof.
  (* ADMITTED *)
  intros c st st' s H.
  inversion H; clear H; subst.
  - inversion H2.
  - inversion H5. subst. reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1.5: break_ignore *)

Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof.
  (* ADMITTED *)
  intros b c st st' s H. inversion H; reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1.5: while_continue *)

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
  (* ADMITTED *)
  intros b c st st' H1 H2.
  apply E_WhileBreak; assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: while_stops_on_break *)

Theorem seq_continue : forall c1 c2 st st' st'',
  st =[ c1 ]=> st' / SContinue ->
  st' =[ c2 ]=> st'' / SContinue ->
  st =[ c1 ; c2 ]=> st'' / SContinue.
Proof.
  (* ADMITTED *)
  intros c1 c2 st st' st'' H1 H2.
  apply E_SeqContinue with st'; assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: seq_continue *)

Theorem seq_stops_on_break : forall c1 c2 st st',
  st =[ c1 ]=> st' / SBreak ->
  st =[ c1 ; c2 ]=> st' / SBreak.
Proof.
  (* ADMITTED *)
  intros c1 c2 st st' H.
  apply E_SeqBreak; assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: seq_stops_on_break *)
(** [] *)

(* EX3A? (while_break_true) *)
Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
(* ADMITTED *)
  intros b c st st' H Hb.
  remember <{ while b do c end }> as c'.
  induction H; inversion Heqc'; clear Heqc'; subst.
  - (* E_WhileFalse *)
    rewrite Hb in H. discriminate H.
  - (* E_WhileContinue *)
    clear IHceval1.
    apply IHceval2.
    + reflexivity.
    + assumption.
  - (* E_WhileBreak *)
    exists st. assumption.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX4A? (ceval_deterministic) *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* ADMITTED *)
  intros c st st1 st2 s1 s2 E1 E2.
  generalize dependent s2.
  generalize dependent st2.
  induction E1;
    intros st2 s2 E2;
    inversion E2; clear E2; subst;
(* HIDE:
   BCP: This proof could be better automated in general.
   AAA: The problem with this proof is that it is somewhat hard to automate
        without using [match], which we haven't told them about yet. Each
        branch needs hypotheses with different names. Furthermore, [apply]
        by itself doesn't quite work as well, because we need to substitute
        some values in order for the unification to work. This is what I was
        able to do.
 *)
    try (rewrite H in H2; inversion H2);
    try (rewrite H in H5; inversion H5);
    try (apply IHE1_1 in H1; destruct H1 as [H11 H12]; try subst);
    try (apply IHE1_2 in H5; destruct H5 as [H51 H52]; try subst);
    try (apply IHE1_1 in H4; destruct H4 as [H41 H42]; inversion H42);
    try (apply IHE1 in H1; destruct H1 as [H11 H12]; try subst; inversion H12);
    try (apply IHE1 in H4; destruct H4 as [H41 H42]; try subst; inversion H42);
    try (apply IHE1_1 in H3; destruct H3 as [H31 H32]; try subst; inversion H32);
    try (apply IHE1_1 in H6; destruct H6 as [H61 H62]; try subst; inversion H62);
    try (apply IHE1_2 in H7; destruct H7 as [H71 H72]; try subst; inversion H72);
    try (apply IHE1 in H3; destruct H3 as [H31 H32]; try subst; inversion H32);
    try (apply IHE1 in H6; destruct H6 as [H61 H62]; try subst; inversion H62);
    try (split; reflexivity).
  - (* E_If *)
    apply IHE1. assumption.
Qed.
(* /ADMITTED *)

(** [] *)
End BreakImp.

(* HIDE *)
(* LATER: Should this exercise be un-hidden?  It needs a tiny bit
   more material to be really interesting, though it also leads to a
   very interesting exercise in Hoare2... *)
(* EX4A? (exn_imp) *)
Module ThrowImp.

(** Many programming languages include mechanisms for raising and
    handling exceptions.  In this problem (a variant of the above
    exercises on [break]), we'll experiment with a very simple
    version, with just a single exception called [THROW].  First, we
    need to enrich the language of commands with an additional case
    for raising the [THROW] exception and a case for catching it. *)

Inductive com : Type :=
  | CSkip
  | CThrow                       (* <--- NEW *)
  | CTry (c1 c2 : com)           (* <--- NEW *)
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 x2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'throw'" := CThrow (in custom com at level 0).
Notation "'try' c1 'catch' c2 'end'" := (CTry c1 c2)
  (in custom com at level 0, c1 custom com at level 99, c2 custom com at level 99,
    format "'[v' 'try' '/  ' c1 '/' 'catch' '/  ' c2 '/' 'end' ']'").
(* INSTRUCTORS: Copy of template com *)
Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99,
    format "'[v' 'while'  x  'do' '/  ' y '/' 'end' ']'") : com_scope.

(** Next, we need to define the behavior of [THROW].  Informally,
    whenever [THROW] is executed, we immediately stop executing this
    command and start executing the [else] clause of the closest
    enclosing [try].

    A simple way of achieving this effect is to add another parameter
    to the evaluation relation that specifies whether evaluation of a
    command executes a [THROW] statement: *)

Inductive status : Type :=
  | SNormal
  | SThrow.

(** Intuitively, [st =[ c ]=> st' / s] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that an exception has been raised ([s = SThrow]) or that execution
    can continue normally ([s = SNormal]).

    - If the command is [skip], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [THROW], the state stays unchanged but we
      signal a [SThrow].

    - If the command is [try], we begin by executing the first
      subcommand; if it terminates normally, then the whole [try]
      terminates in the same state; if it terminates with an
      exception, we execute the second subcommand instead.

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [if b then c1 else c2 end], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ; c2], we first execute [c1].
      If this yields a [SThrow], we skip the execution of [c2] and
      propagate the [SThrow] signal to the surrounding context; the
      resulting state is the same as the one obtained by executing
      [c1] alone. Otherwise, we execute [c2] on the state obtained
      after executing [c1], and propagate the signal generated there.

    - Finally, for a loop of the form [while b do c end], when [b]
      evaluates to true, we execute [c] and check the signal that it
      raises.  If that signal is [SNormal], the execution proceeds
      as in the original semantics. Otherwise, we stop the execution
      of the loop and signal [SThrow]. *)


(* SOLUTION *)

(** Because we include if syntax for the if syntax in com,
    we cannot use typical coq if syntax. We avoid this issues
    by making a function that encodes the behavior of if *)
Definition if_then_else {A : Type} (b : bool) (l r : A) :=
  if b then l else r.

(* /SOLUTION *)

(** Based on the above description, complete the definition of the
    [ceval] relation. *)

(* INSTRUCTORS: Copy of template eval *)
(* HIDEFROMHTML *)
Reserved Notation "st '=[' c ']=>' st' '/' s"
         (at level 40, c custom com at level 99, st' constr at next level).
(* /HIDEFROMHTML *)

(* SOONER: The E_WhileContinue case in this solution should have [s],
   not [SNormal], in the last two lines -- see fixed version in
   comment.  This will require a bit of fixing proofs. *)
Inductive ceval : com -> state -> status -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SNormal
  (* SOLUTION *)
  | E_Throw : forall st,
      st =[ CThrow ]=> st / SThrow
  | E_TryContinue : forall c1 c2 st st',
      st =[ c1 ]=> st' / SNormal ->
      st =[ try c1 catch c2 end ]=> st' / SNormal
  | E_TryThrow : forall c1 c2 st st' st'' s,
      st  =[ c1 ]=> st'  / SThrow ->
      st' =[ c2 ]=> st'' / s ->
      st  =[ try c1 catch c2 end ]=> st'' / s
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st) / SNormal
  | E_SeqContinue : forall c1 c2 st st' st'' s,
      st  =[ c1 ]=> st'  / SNormal ->
      st' =[ c2 ]=> st'' / s ->
      st  =[ c1 ; c2 ]=> st'' / s
  | E_SeqThrow : forall c1 c2 st st',
      st =[ c1 ]=> st' / SThrow ->
      st =[ c1 ; c2 ]=> st' / SThrow
  | E_If : forall c1 c2 b st st' s,
      st =[ if_then_else (beval st b) c1 c2 ]=> st' / s ->
      st =[ if b then c1 else c2 end ]=> st' / s
  | E_WhileFalse : forall c b st,
      beval st b = false ->
      st =[ while b do c end ]=> st / SNormal
  | E_WhileContinue : forall c b st st' st'',
      beval st b = true ->
      st  =[ c ]=> st' / SNormal ->
      st' =[ while b do c end ]=> st'' / SNormal ->
      st  =[ while b do c end ]=> st'' / SNormal
(* HIDE: BETTER version!
  | E_WhileContinue : forall c b st st' st'' s,
      beval st b = true ->
      c / st ==> SNormal / st' ->
      (while b do c end) / st' ==> s / st'' ->
      (while b do cend) / st ==> s / st''
*)
  | E_WhileThrow : forall c b st st',
      beval st b = true ->
      st =[ c ]=> st' / SThrow ->
      st =[ while b do c end ]=> st' / SThrow
  (* /SOLUTION *)

  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

(** Now prove the following properties of your definition of [ceval]: *)

(* LATER: It would be good to have some examples that verify
   that their implementation does the right thing on a few unit
   tests! *)

Theorem ceval_deterministic_throw: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* ADMITTED *)
  intros c st st1 st2 s1 s2 E1 E2.
  generalize dependent s2.
  generalize dependent st2.
  induction E1;
    intros st2 s2 E2;
    inversion E2; clear E2; subst;
(* LATER: see comments in the break exercise *)
    try (rewrite H in H2; inversion H2);
    try (rewrite H in H5; inversion H5);
    try (apply IHE1_1 in H1; destruct H1 as [H11 H12]; try subst);
    try (apply IHE1_2 in H5; destruct H5 as [H51 H52]; try subst);
    try (apply IHE1_1 in H4; destruct H4 as [H41 H42]; inversion H42);
    try (apply IHE1 in H1; destruct H1 as [H11 H12]; try subst; inversion H12);
    try (apply IHE1 in H4; destruct H4 as [H41 H42]; try subst; inversion H42);
    try (apply IHE1_1 in H3; destruct H3 as [H31 H32]; try subst; inversion H32);
    try (apply IHE1_1 in H6; destruct H6 as [H61 H62]; try subst; inversion H62);
    try (apply IHE1_2 in H7; destruct H7 as [H71 H72]; try subst; inversion H72);
    try (apply IHE1 in H3; destruct H3 as [H31 H32]; try subst; inversion H32);
    try (apply IHE1 in H6; destruct H6 as [H61 H62]; try subst; inversion H62);
    try (split; reflexivity).
  - (* E_If *)
    apply IHE1. assumption.
Qed.
(* /ADMITTED *)

End ThrowImp.
(** [] *)
(* /HIDE *)

(* EX4? (add_for_loop) *)
(** Add C-style [for] loops to the language of commands, update the
    [ceval] definition to define the semantics of [for] loops, and add
    cases for [for] loops as needed so that all the proofs in this
    file are accepted by Rocq.

    A [for] loop should be parameterized by (a) a statement executed
    initially, (b) a test that is run on each iteration of the loop to
    determine whether the loop should continue, (c) a statement
    executed at the end of each loop iteration, and (d) a statement
    that makes up the body of the loop.  (You don't need to worry
    about making up a concrete Notation for [for] loops, but feel free
    to play with this too if you like.) *)

(* SOLUTION *)
(* (Providing a solution for this exercise would involve changes
   in many places, so we'll leave this one to you!) *)
(* /SOLUTION *)
(** [] *)
(* /FULL *)

(* INSTRUCTORS *)
(* -------------------------------------------------------------------------

For future reference, here are some REASONS why the Imp notation is the way it is...

Discussion of variable representation, 1/2021

A (wrong) proposal from BCP:

  For a couple of months, I've been wanting to eliminate the
  string-to-id coercions that we've used for a long time (and that
  I've always kind of disliked because they introduce magic into the
  parsing process that sometimes doesn't work very smoothly) and
  instead just treat individual identifiers as keywords within custom
  grammars. I think this will make the grammars simpler without
  changing what people see most of the time.

Arthur Chargueraud pointed out that this would cause lots of problems
because these identifiers would then be parsed as keywords
*everywhere*!

Robert Rand proposed:

  I'm guessing we'll have a bunch of variables U, V, X, Y, Z set to
  AId 1 ... AId n? We could even use Definition rather than Notation
  if we wanted. (I'm assuming here that these are meant to be distinct
  – otherwise, why not use Variables?)

Arthur Chargueraud responded:

  I think it is useful to refer to a variable "X", and not just to
  "AId X". Otherwise, you can't reason about about binders and
  substitutions, e.g., write "fun X => t" or "subst X v t", you need X
  to be a variable and not an occurence of a variable. I understand
  that the IMP language may not require these features, yet I'd prefer
  to encourage a solution that extends to STLC and to the SLF
  volume. For this reason, I would discourage a shorthand of the form:

  Definition X : aexp := AId 1.

  One thing I do in the SLF volume is the following:

  Type var := string.  (* could do with an nat as well *)

  Definition X : var := "X".
  Definition Y : var := "Y".

  Coercion Aid : var >-> aexp.

  Notation "x" := x
    (in custom aexp at level 0, x constr at level 0) : aexp_scope.
    (* could also restrict x to be an ident *)
  Now, if you want to go without the coercions, there might be other possible routes.
  If you are ready to introduce a backquote to mean [Aid], then the solution is easy.

  Type var := string.  (* could do with an nat as well *)

  Definition X : var := "X".
  Definition Y : var := "Y".

  Notation "` x" := (Aid x, format "` x", x ident) : aexp_scope.

  If you are not ready to introduce a coercion nor a backquote, and
  want to nevertheless be able to refer to the variable X both to
  means just the variable name X and the occurence of the variable X,
  then I guess the only way to go for two distinct pieces of notation,
  and play with the scopes.

  Type var := string.  (* could do with an nat as well *)

  Notation "'X'" := ("X") (at level 0) : var_scope.
  Notation "'X'" := (AId "X") (in custom aexp at level 0) : aexp_scope.
  You then need to play with arguments scope to get the desired parsing,
  something alongs the lines of:

  Notation "'fun' x => t" := (aexp_fun x t)
     (in custom aexp at level 65, x constr at level 0, t custom aexp) : aexp_scope.
  Definition subst (x:var) (v:val) (t:aexp) : ...
  Arguments subst x%var_scope v%aexp_scope t%aexp_scope.
  (* This should allow [subst X v X] to parse property, the first X as a var,
     and the second X as an expression. *)
  My take is that this approach would add up to too much confusion, because
  although writing "X" would usually work out the way you expect, when it does
  not parse to the right type (var vs aexp), it's going to be very confusing.

  Disclaimer: I haven't tried to typecheck any of this stuff, so it might
  not work out of the box.

  I summary, I think that coercions are really the appropriate mechanism here,
  it is more robust and modular than the notation system imo for resolving the
  ambiguities between X as a variable name and X as an occurence in a term.
  If you don't want to teach coercion, use a backquote to make the coercion explicit.
  It's not pretty, but it's got a trivial interpretation.

  Of course, maybe there are other approaches that I haven't thought of...

Final decision:

  Leave things as they are, using coercions.
*)
(* /INSTRUCTORS *)

(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(\\*\\* \\*+" *)
(* End: *)
(* mode: outline-minor *)
(* /HIDE *)
