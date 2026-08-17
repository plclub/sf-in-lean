(** * Induction: Proof by Induction *)

(* SOONER: Readers might expect us to add eqn:H annotations to uses of
   induction, but this changes the shape of the IH in a nasty way! :-(
   We should at least comment. *)
(* SOONER: We should also consider adding more examples to clarify
   the concepts introduced in this chapter. This could help in
   reinforcing the understanding of induction principles.
*)
(* LATER: In 3/22, MRC and BCP discussed "inlining" IndPrinciples
   into earlier chapters, thus eliminating it as a chapter. This
   chapter, Induction, is the first place a change would occur.  We
   would present [nat_ind] here. Then in Lists/Poly we'd present
   [list_ind], and the rest would go in IndProp and ProofObjects. The
   main wrinkle is that we'd need to introduce [apply] here instead of
   in Tactics if we want to preserve the presentation. The discussion
   is preserved here: https://github.com/DeepSpec/sfdev/pull/471.
*)
(* LATER: Now that we've added Steve's nice late-policy exercise in
   Basics.v, the assignment for that chapter is probably hard enough.  Now
   what about this chapter?  Can/should we make it a notch or two
   harder? *)

(* ################################################################# *)
(** * Separate Compilation *)

(** TERSE: Rocq will first need to compile [Basics.v] into [Basics.vo]
    so it can be imported here -- detailed instructions are in the
    full version of this chapter... *)
(** FULL: Before getting started on this chapter, we need to import
    all of our definitions from the previous chapter: *)

From LF Require Export Basics.

(** FULL: For this [Require] command to work, Rocq needs to be able to
    find a compiled version of the previous chapter ([Basics.v]).
    This compiled version, called [Basics.vo], is analogous to the
    [.class] files compiled from [.java] source files and the [.o]
    files compiled from [.c] files.

    To compile [Basics.v] and obtain [Basics.vo], first make sure that
    the files [Basics.v], [Induction.v], and [_CoqProject] are in
    the current directory.

    The [_CoqProject] file should contain just the following line:
[[
      -Q . LF
]]
    This maps the current directory ("[.]", which contains [Basics.v],
    [Induction.v], etc.) to the prefix (or "logical directory")
    "[LF]". Proof General, CoqIDE, and VSCoq read [_CoqProject]
    automatically, to find out to where to look for the file
    [Basics.vo] corresponding to the library [LF.Basics].

    Once the files are in place, there are various ways to build
    [Basics.vo] from an IDE, or you can build it from the command
    line.  From an IDE...

     - In Proof General: The compilation can be made to happen
       automatically when you submit the [Require] line above to PG, by
       setting the emacs variable [coq-compile-before-require] to [t].
       This can also be found in the menu: "Coq" > "Auto Compilation" >
       "Compile Before Require".

     - In CoqIDE: One thing you can do on all platforms is open
       [Basics.v]; then, in the "Compile" menu, click on "Compile Buffer".

     - For VSCode users, open the terminal pane at the bottom and then
       follow the command line instructions below.  (If you downloaded
       the project setup .tgz file, just doing `make` should build all
       the code.)

    To compile [Basics.v] from the command line...

     - First, generate a [Makefile] using the [rocq makefile] utility,
       which comes installed with Rocq. (If you obtained the whole volume as
       a single archive, a [Makefile] should already exist and you can
       skip this step.)
[[
         rocq makefile -f _CoqProject *.v -o Makefile
]]
       You should rerun that command whenever you add or remove
       Rocq files in this directory.

     - Now you can compile [Basics.v] by running [make] with the
       corresponding [.vo] file as a target:
[[
         make Basics.vo
]]
       All files in the directory can be compiled by giving no
       arguments:
[[
         make
]]
     - Under the hood, [make] uses the Rocq compiler, [rocq compile].  You can
       also run [rocq compile] directly:
[[
         rocq compile -Q . LF Basics.v
]]

     - Since [make] also calculates dependencies between source files
       to compile them in the right order, [make] should generally be
       preferred over running [rocq compile] explicitly.  But as a last (but
       not terrible) resort, you can simply compile each file manually
       as you go.  For example, before starting work on the present
       chapter, you would need to run the following command:
[[
        rocq compile -Q . LF Basics.v
]]
       Then, once you've finished this chapter, you'd do
[[
        rocq compile -Q . LF Induction.v
]]
       to get ready to work on the next one.  If you ever remove the
       .vo files, you'd need to give both commands again (in that
       order).

    Troubleshooting:

     - For many of the alternatives above you need to make sure that
       the [rocq] executable is in your [PATH].

     - If you get complaints about missing identifiers, it may be
       because the "load path" for Rocq is not set up correctly.  The
       [Print LoadPath.] command may be helpful in sorting out such
       issues.

     - When trying to compile a later chapter, if you see a message like
[[
        Compiled library Induction makes inconsistent assumptions over
        library Basics
]]
       a common reason is that the library [Basics] was modified and
       recompiled without also recompiling [Induction] which depends
       on it.  Recompile [Induction], or everything if too many files
       are affected (for instance by running [make] and if even this
       doesn't work then [make clean; make]).

     - If you get complaints about missing identifiers later in this
       file it may be because the "load path" for Rocq is not set up
       correctly.  The [Print LoadPath.] command may be helpful in
       sorting out such issues.

       In particular, if you see a message like
[[
           Compiled library Foo makes inconsistent assumptions over
           library Bar
]]
       check whether you have multiple installations of Rocq on your
       machine.  It may be that commands (like [rocq compile]) that you execute
       in a terminal window are getting a different version of Rocq than
       commands executed by Proof General or CoqIDE.

     - One more tip for CoqIDE users: If you see messages like [Error:
       Unable to locate library Basics], a likely reason is
       inconsistencies between compiling things _within CoqIDE_ vs _using
       [rocq] from the command line_.  This typically happens when there
       are two incompatible versions of Rocq installed on your
       system (one associated with CoqIDE, and one associated with [rocq]
       from the terminal).  The workaround for this situation is
       compiling using CoqIDE only (i.e. choosing "make" from the menu),
       and avoiding using [rocq] directly at all. *)

(* TERSE *)
(* ###################################################################### *)
(** * Review *)
(* /TERSE *)
(* QUIZ *)
(** To prove the following theorem, which tactics will we need besides
    [intros] and [reflexivity]?  (A) none, (B) [rewrite], (C)
    [destruct], (D) both [rewrite] and [destruct], or (E) can't be
    done with the tactics we've seen.
[[
    Theorem review1: (orb true false) = true.
]]
*)
(* HIDE *)
Theorem review1:  (orb true false) = true.
Proof. reflexivity.  Qed.
(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** What about the next one?
[[
    Theorem review2: forall b, (orb true b) = true.
]]
    Which tactics do we need besides [intros] and [reflexivity]?  (A)
    none (B) [rewrite], (C) [destruct], (D) both [rewrite] and
    [destruct], or (E) can't be done with the tactics we've seen.
*)
(* HIDE *)
Theorem review2: forall b, (orb true b) = true.
Proof. intros b. reflexivity. Qed.
(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** What if we change the order of the arguments of [orb]?
[[
    Theorem review3: forall b, (orb b true) = true.
]]
    Which tactics do we need besides [intros] and [reflexivity]?  (A)
    none (B) [rewrite], (C) [destruct], (D) both [rewrite] and
    [destruct], or (E) can't be done with the tactics we've seen.
*)
(* HIDE *)
Theorem review3: forall b, (orb b true) = true.
Proof. intros b. destruct b. reflexivity. reflexivity. Qed.
(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** What about this one?
[[
    Theorem review4 : forall n : nat, n = 0 + n.
]]
    (A) none, (B) [rewrite], (C) [destruct], (D) both [rewrite] and
    [destruct], or (E) can't be done with the tactics we've seen.
*)
(* HIDE *)
Theorem review4 : forall n : nat, n = 0 + n.
Proof. reflexivity.  Qed.
(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** What about this?
[[
    Theorem review5 : forall n : nat, n = n + 0.
]]
    (A) none, (B) [rewrite], (C) [destruct], (D) both [rewrite] and
    [destruct], or (E) can't be done with the tactics we've seen.
*)
(* HIDE *)
Theorem review5 : forall n : nat, n = n + 0.
Abort.
(* /HIDE *)
(* /QUIZ *)

(* ###################################################################### *)
(** * Proof by Induction *)

(** We can prove that [0] is a neutral element for [+] on the _left_
    using just [reflexivity].  But the proof that it is also a neutral
    element on the _right_ ... *)

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.
(** TERSE: ... gets stuck. *)
(* FULL *)

(** ... can't be done in the same simple way.  Just applying
  [reflexivity] doesn't work, since the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)

(* /FULL *)
Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(** TERSE: *** *)

(** And reasoning by cases using [destruct n] doesn't get us much
    further: the branch of the case analysis where we assume [n = 0]
    goes through just fine, but in the branch where [n = S n'] for
    some [n'] we get stuck in exactly the same way. *)

Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* ...but here we are stuck again *)
Abort.

(** FULL: We could use [destruct n'] to get a bit further, but,
    since [n] can be arbitrarily large, we'll never get all the way
    there if we just go on like this. *)

(** TERSE: *** *)

(** FULL: To prove interesting facts about numbers, lists, and other
    inductively defined sets, we often need a more powerful reasoning
    principle: _induction_.

    Recall (from a discrete math course, probably) the _principle of
    induction over natural numbers_: If [P(n)] is some proposition
    involving a natural number [n] and we want to show that [P] holds for
    all numbers [n], we can reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Rocq, the steps are the same, except we typically encounter them
    in reverse order: we begin with the goal of proving [P(n)] for all
    [n] and apply the [induction] tactic to break it down into two
    separate subgoals: one where we must show [P(O)] and another where
    we must show [P(n') -> P(S n')].  Here's how this works for the
    theorem at hand... *)

(** TERSE: We need a bigger hammer: the _principle of induction_ over
    natural numbers...

      - If [P(n)] is some proposition involving a natural number [n],
        and we want to show that [P] holds for _all_ numbers, we can
        reason like this:

         - show that [P(O)] holds
         - show that, if [P(n')] holds, then so does [P(S n')]
         - conclude that [P(n)] holds for all [n].

    For example... *)

(** TERSE: *** *)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.  Qed.

(** FULL: Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  Since there are two subgoals, the [as...] clause
    has two parts, separated by a vertical bar, [|].  (Strictly
    speaking, we can omit the [as...] clause and Rocq will choose names
    for us.  In practice, this is a bad practice, as Rocq's automatic
    choices tend to be confusing.)

    In the first subgoal, [n] is replaced by [0].  No new variables
    are introduced (so the first part of the [as...] is empty), and
    the goal becomes [0 = 0 + 0], which follows easily by simplification.

    In the second subgoal, [n] is replaced by [S n'], and the
    assumption [n' + 0 = n'] is added to the context with the name
    [IHn'] (i.e., the Induction Hypothesis for [n']).  These two names
    are specified in the second part of the [as...] clause.  The goal
    in this case becomes [S n' = (S n') + 0], which simplifies to
    [S n' = S (n' + 0)], which in turn follows from [IHn']. *)

(** TERSE: *** *)
(** TERSE: Let's try this one together: *)

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  (* WORKINCLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.
(* /WORKINCLASS *)

(** FULL: (The use of the [intros] tactic in these proofs is actually
    redundant.  When applied to a goal that contains quantified
    variables, the [induction] tactic will automatically move them
    into the context as needed.) *)

(* FULL *)
(* EX2! (basic_induction) *)
(** Prove the following using induction. You might need previously
    proven results. *)

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* ADMITTED *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: mul_0_r *)

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* ADMITTED *)
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: plus_n_Sm *)
(* /FULL *)
(** TERSE: *** *)
(** TERSE: Here's another related fact about addition, which we'll
    need later.  (The proof is left as an exercise.) *)

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* ADMITTED *)
  intros n m. induction m as [| m' IHm'].
  - (* m = 0 *)
    simpl. rewrite -> add_0_r. reflexivity.
  - (* m = S m' *)
    simpl. rewrite <- IHm'. rewrite <- plus_n_Sm.
    reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: add_comm *)
(* FULL *)

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* ADMITTED *)
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.   Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: add_assoc *)
(** [] *)

(* EX2 (double_plus) *)
(** Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  (* ADMITTED *)
  intros n.  induction n as [|n' IHn'].
  - (* n = 0 *)
   reflexivity.
  - (* n = S n' *)
   simpl. rewrite add_comm. simpl. rewrite IHn'. reflexivity. Qed.
  (* /ADMITTED *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)
(* EX2 (eqb_refl) *)
(** The following theorem relates the computational equality [=?] on
    [nat] with the definitional equality [=] on [bool]. *)

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  (* ADMITTED *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)
(* HIDE:
   Note: we might expect a similar property to hold on
   UNequal [nat]'s:
      Theorem eqb_n_n' : forall n n' : nat,
           n <> n' ->
           n =? n' = false.
   But it will be a while before we get to terms with what
   [n <> n'] really means... *)

(* FULL *)
(* EX2? (even_S) *)
(** TERSE: Here's a useful theorem that proves [n-1] is not even if
    [n] is even.  This will facilitate proofs by induction on [n]: *)
(** FULL: One inconvenient aspect of our definition of [even n] is the
    recursive call on [n - 2]. This makes proofs about [even n]
    harder when done by induction on [n], since we may need an
    induction hypothesis about [n - 2]. The following lemma gives an
    alternative characterization of [even (S n)] that works better
    with induction: *)

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  (* ADMITTED *)
  intros n.
  induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *)
    rewrite IHn'. rewrite negb_involutive. simpl. reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: even_S *)
(** [] *)
(* /FULL *)

(* HIDE *)
(* QUIZ *)
(** We've seen that there are goals that [destruct] can't solve but
    [induction] can. What about the other way around? Are there steps
    in a proof that can be solved by pure case analysis ([destruct])
    but not using [induction]?

    (A) No

    (B) Yes
*)
(* /QUIZ *)
(* /HIDE *)

(* ###################################################################### *)
(** * Proofs Within Proofs *)

(** FULL: In Rocq, as in informal mathematics, large proofs are often
    broken into a sequence of theorems, with later proofs referring to
    earlier theorems.  But sometimes a proof will involve some
    miscellaneous fact that is too trivial and of too little general
    interest to bother giving it its own top-level name.  In such
    cases, it is convenient to be able to simply use the required fact
    "in place" and then prove it as a separate step.  The [replace]
    tactic allows us to do this. *)
(** TERSE: New tactic: [replace]. *)

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  replace (n + 0 + 0) with n.
  - reflexivity.
  - rewrite add_comm. simpl. rewrite add_comm. reflexivity.
Qed.
(* LATER: BCP 21: Changed 0+n to n+0+0 for a more interesting
   proof (with 0+n was provable just by reflexivity!).  The new one is
   still straightforward without the replace, but maybe not quite so
   obviously so! *)

(** FULL: The tactic [replace e1 with e2] tactic introduces two subgoals.

    The first subgoal is the same as the one at the point where we
    invoke [replace], except that [e1] is replaced by [e2].  The
    second subgoal is the equality [e1 = e2] itself.  *)

(** TERSE: *** *)

(** FULL: As another example, suppose we want to prove that [(n + m)
    + (p + q) = (m + n) + (p + q)]. The only difference between the
    two sides of the [=] is that the arguments [m] and [n] to the
    first inner [+] are swapped, so it seems we should be able to use
    the commutativity of addition ([add_comm]) to rewrite one into the
    other.  However, the [rewrite] tactic is not very smart about
    _where_ it applies the rewrite.  There are three uses of [+] here,
    and it turns out that doing [rewrite -> add_comm] will affect only
    the _outer_ one... *)
(* HIDE: APT: It is really sad not to be able to specify rewrite
  positions.  Students get annoyed: "why is the behavior of this
  tactic so unpredictable?"  Maybe we should [Import Setoid] to
  enable the [rewrite ... at] notation.  BCP '20: Agreed -- let's do
  it! (APT '21: In fact, the [Import Setoid] is already happening
  silently via the [Require Export String] in Basics.v But sadly, we
  would need to use [setoid_rewrite...at] instead of plain
  [rewrite...at], since they have different semantics (despite what
  the reference manual seems to imply).) (And even if we choose not
  to do it, this example is very underwhelming... The fact that it
  involves explaining the difference between a universally quantified
  variable and a fixed but arbitrary value is... problematic... at
  this point in the course! APT: Agreed!)  BCP 21: How bad would it
  be simply to drop this example??  BCP 25: I think switching from
  assert to replace makes this much much better. *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
    like add_comm should do the trick! *)
  rewrite add_comm.
  (* Doesn't work... Rocq rewrites the wrong plus! :-( *)
Abort.

(** TERSE: *** *)
(** To use [add_comm] at the point where we need it, we can rewrite
    [n + m] to [m + n] using [replace] and then prove [n + m = m + n]
    using [add_comm]. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite add_comm. reflexivity.
Qed.

(* FULL *)
(* ###################################################################### *)
(** * Formal vs. Informal Proof *)

(** #<div class="quote">#"Informal proofs are algorithms; formal proofs are code."#</div># *)

(** What constitutes a successful proof of a mathematical claim?

    The question has challenged philosophers for millennia, but a
    rough and ready answer could be this: A proof of a mathematical
    proposition [P] is a written (or spoken) text that instills in the
    reader or hearer the certainty that [P] is true -- an unassailable
    argument for the truth of [P].  That is, a proof is an act of
    communication.

    Acts of communication may involve different sorts of readers.  On
    one hand, the "reader" can be a program like Rocq, in which case
    the "belief" that is instilled is that [P] can be mechanically
    derived from a certain set of formal logical rules, and the proof
    is a recipe that guides the program in checking this fact.  Such
    recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will probably be written in English or some other natural
    language and will thus necessarily be _informal_.  Here, the
    criteria for success are less clearly specified.  A "valid" proof
    is one that makes the reader believe [P].  But the same proof may
    be read by many different readers, some of whom may be convinced
    by a particular way of phrasing the argument, while others may not
    be. Some readers may be particularly pedantic, inexperienced, or
    just plain thick-headed; the only way to convince them will be to
    make the argument in painstaking detail.  Other readers, more
    familiar in the area, may find all this detail so overwhelming
    that they lose the overall thread; all they want is to be told the
    main ideas, since it is easier for them to fill in the details for
    themselves than to wade through a written presentation of them.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that will convince every
    conceivable reader.

    In practice, however, mathematicians have developed a rich set of
    conventions and idioms for writing about complex mathematical
    objects that -- at least within a certain community -- make
    communication fairly reliable.  The conventions of this stylized
    form of communication give a reasonably clear standard for judging
    proofs good or bad.

    Because we are using Rocq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can
    completely forget about informal ones!  Formal proofs are useful
    in many ways, but they are _not_ very efficient ways of
    communicating ideas between human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity.  Qed.

(** Rocq is perfectly happy with this.  For a human, however, it
    is difficult to make much sense of it.  We can use comments and
    bullets to show the structure a little more clearly... *)

Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity.   Qed.

(** ... and if you're used to Rocq you might be able to step
    through the tactics one after the other in your mind and imagine
    the state of the context and goal stack at each point, but if the
    proof were even a little bit more complicated this would be next
    to impossible.

    A (pedantic) mathematician might write the proof something like
    this: *)

(** - _Theorem_: For any [n], [m] and [p],
[[
      n + (m + p) = (n + m) + p.
]]
    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show that
[[
        0 + (m + p) = (0 + m) + p.
]]
      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where
[[
        n' + (m + p) = (n' + m) + p.
]]
      We must now show that
[[
        (S n') + (m + p) = ((S n') + m) + p.
]]
      By the definition of [+], this follows from
[[
        S (n' + (m + p)) = S ((n' + m) + p),
]]
      which is immediate from the induction hypothesis.  _Qed_. *)

(* HIDE *)
(* MMG: the proof above makes no use of lemmas, so it's hard for
   students to know what to do.  It might be good to also give them a
   sample proof of mult_1_l so they know how to "invoke" things
   they've already proved. *)
(* /HIDE *)

(** The overall form of the proof is basically similar, and of
    course this is no accident: Rocq has been designed so that its
    [induction] tactic generates the same sub-goals, in the same
    order, as the bullet points that a mathematician would usually
    write.  But there are significant differences of detail: the
    formal proof is much more explicit in some ways (e.g., the use of
    [reflexivity]) but much less explicit in others (in particular,
    the "proof state" at any given point in the Rocq proof is
    completely implicit, whereas the informal proof reminds the reader
    several times where things stand). *)

(* EX2AM? (add_comm_informal) *)
(** Translate your solution for [add_comm] into an informal proof:

    Theorem: Addition is commutative.

    Proof: (* SOLUTION *)
       Let natural numbers [n] and [m] be given.  We show [n + m = m +
       n] by induction on [m].

       - First, suppose [m = 0].  We must show [n + 0 = 0 + n].  By
         the definition of [+], we know [0 + n = n], and we have
         already shown (lemma [add_0_r]) that [n + 0 = n].  Thus,
         showing [n + 0 = 0 + n] is equivalent to showing [n = n],
         which is true by reflexivity.

       - Next, suppose [m = S m'] for some [m'], where [n + m'] = [m'
         + n].  We must show that [n + (S m') = (S m') + n].  By the
         definition of [+] and the induction hypothesis, [(S m') + n =
         S (m' + n) = S (n + m')].  It remains to show [n + (S m') = S
         (n + m')], which is precisely lemma [plus_n_Sm].
(* /SOLUTION *)
*)

(* GRADE_MANUAL 2: add_comm_informal *)
(** [] *)

(* EX2M? (eqb_refl_informal) *)
(** Write an informal proof of the following theorem, using the
    informal proof of [add_assoc] as a model.  Don't just
    paraphrase the Rocq tactics into English!

    Theorem: [(n =? n) = true] for any [n].

    Proof: (* SOLUTION *)
       By induction on [n].

       - First, suppose [n = 0].  We must show [(0 =? 0) = true].  This
         follows directly from the definition of [eqb].

       - Next, suppose [n = S n'], where [(n' =? n') = true].  We
         must show [(S n' =? S n') = true]. This
         follows directly from the induction hypothesis and the
         definition of [eqb].
(* /SOLUTION *)
*)

(* GRADE_MANUAL 2: eqb_refl_informal *)
(** [] *)

(* /FULL *)
(* TERSE: HIDEFROMHTML *)
(* HIDEFROMADVANCED *)
(* ###################################################################### *)
(** * More Exercises *)

(* TERSE: These additional exercises state facts that will be used in
   later chapters.  We don't need to work them in class. *)

(* LATER: Is this one too many recommended exercises? *)
(* EX3! (mul_comm) *)
(** Use [replace] to help prove [add_shuffle3].  You don't need to
    use induction yet. *)

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* ADMITTED *)
  intros n m p.
  rewrite add_assoc.
  replace (n + m) with (m + n).
  - rewrite -> add_assoc. reflexivity.
  - rewrite <- add_comm. reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: add_shuffle3 *)
(* QUIETSOLUTION *)
Theorem mult_m_Sn : forall m n : nat,
  m * (S n) = m + (m * n).
Proof.
  induction m as [| m' IHm'].
  - (* m = 0 *)
    intros n. simpl. reflexivity.
  - (* m = S m' *)
    intros n.
    simpl.
    rewrite -> IHm'.
    rewrite -> add_shuffle3.
    reflexivity.  Qed.

(* /QUIETSOLUTION *)
(** Now prove commutativity of multiplication.  You will probably want
    to look for (or define and prove) a "helper" theorem to be used in
    the proof of this one. Hint: what is [n * (1 + k)]? *)

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* ADMITTED *)
  intros m n.
  induction m as [| m' IHm'].
  - (* m = 0 *)
    simpl. rewrite mul_0_r. reflexivity.
  - (* m = S m' *)
    simpl.
    rewrite -> IHm'.
    rewrite -> mult_m_Sn.
    reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: mul_comm *)
(** [] *)

(* EX3? (more_exercises) *)
(** Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before you hack!) *)

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  (* ADMITTED *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.
(* /ADMITTED *)

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  (* ADMITTED *)
  reflexivity.  Qed.
(* /ADMITTED *)

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* ADMITTED *)
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.  Qed.
(* /ADMITTED *)

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  (* ADMITTED *)
  reflexivity.  Qed.
(* /ADMITTED *)

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* ADMITTED *)
  intros n. simpl. rewrite -> add_0_r.
  reflexivity.  Qed.
(* /ADMITTED *)

(* HIDE *)
Theorem mult_2_l : forall n:nat, 2 * n = n + n.
Proof.
  (* ADMITTED *)
  intros n. simpl. rewrite -> add_0_r.
  reflexivity.  Qed.
(* /ADMITTED *)
(* /HIDE *)

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  (* ADMITTED *)
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.  Qed.
(* /ADMITTED *)

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* ADMITTED *)
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'.
    rewrite -> add_assoc.
    reflexivity.  Qed.
(* /ADMITTED *)

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* ADMITTED *)
  intros n m p.  induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> mult_plus_distr_r.  rewrite IHn'.  reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* FULL *)
(** * Nat to Bin and Back to Nat *)

(** Recall the [bin] type we defined in \CHAP{Basics}: *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin)
.
(** Before you start working on the next exercise, replace the stub
    definitions of [incr] and [bin_to_nat], below, with your solution
    from \CHAP{Basics}.  That will make it possible for this file to
    be graded on its own. *)

Fixpoint incr (m:bin) : bin
  (* ADMITDEF *) :=
  match m with
  | Z     => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.
(* /ADMITDEF *)

Fixpoint bin_to_nat (m:bin) : nat
  (* ADMITDEF *) :=
  match m with
  | Z     => O
  | B0 m' => double (bin_to_nat m')
  | B1 m' => 1 + (double (bin_to_nat m'))
  end.
(* /ADMITDEF *)

(** In \CHAP{Basics}, we did some unit testing of [bin_to_nat], but we
    didn't prove its correctness. Now we'll do so. *)

(* EX3! (binary_commute) *)
(** Prove that the following diagram commutes:

<<
                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S
>>
    That is, incrementing a binary number and then converting it to
    a (unary) natural number yields the same result as first converting
    it to a natural number and then incrementing.

    If you want to change your previous definitions of [incr] or [bin_to_nat]
    to make the property easier to prove, feel free to do so! *)

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  (* ADMITTED *)
  intros b.
  induction b as [| b' IHb' | b' IHb'].
  - (* b = 0 *)
    reflexivity.
  - (* b = 2*b' *)
    reflexivity.
  - (* b = 1 + 2*b' *)
    simpl. rewrite -> IHb'.
    reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: bin_to_nat_pres_incr *)

(** [] *)

(* EX3 (nat_bin_nat) *)

(** Write a function to convert natural numbers to binary numbers. *)

Fixpoint nat_to_bin (n:nat) : bin
  (* ADMITDEF *) :=
  match n with
  | O    => Z
  | S n' => incr (nat_to_bin n')
  end.
(* /ADMITDEF *)

(** Prove that, if we start with any [nat], convert it to [bin], and
    convert it back, we get the same [nat] which we started with.

    Hint: This proof should go through smoothly using the previous
    exercise about [incr] as a lemma. If not, revisit your definitions
    of the functions involved and consider whether they are more
    complicated than necessary: the shape of a proof by induction will
    match the recursive structure of the program being verified, so
    make the recursions as simple as possible. *)

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  (* ADMITTED *)
  induction n as [|n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl.
    rewrite bin_to_nat_pres_incr.
    rewrite IHn'.
    reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: nat_bin_nat *)

(** [] *)

(** * Bin to Nat and Back to Bin (Advanced) *)

(** The opposite direction -- starting with a [bin], converting to [nat],
    then converting back to [bin] -- turns out to be problematic. That
    is, the following theorem does not hold. *)

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

(** Let's explore why that theorem fails, and how to prove a modified
    version of it. We'll start with some lemmas that might seem
    unrelated, but will turn out to be relevant. *)

(* EX2A (double_bin) *)

(** Prove this lemma about [double], which we defined earlier in the
    chapter. *)

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
  (* ADMITTED *)
  destruct n eqn:E.
  - reflexivity.
  - reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: double_incr *)

(** Now define a similar doubling function for [bin]. *)

Definition double_bin (b:bin) : bin
  (* ADMITDEF *) :=
  match b with
  | Z => Z
  | _ => B0 b
  end.
(* /ADMITDEF *)

(** Check that your function correctly doubles zero. *)

Example double_bin_zero : double_bin Z = Z.
(* ADMITTED *) Proof. simpl. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: double_bin_zero *)

(** Prove this lemma, which corresponds to [double_incr]. *)

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  (* ADMITTED *)
  destruct b eqn:E.
  - (* Z *) reflexivity.
  - (* B0 *) reflexivity.
  - (* B1 *) reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: double_incr_bin *)

(** [] *)

(** Let's return to our desired theorem: *)

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

(** The theorem fails because there are some [bin] such that we won't
    necessarily get back to the _original_ [bin], but instead to an
    "equivalent" [bin].  (We deliberately leave that notion undefined
    here for you to think about.)

    Explain in a comment, below, why this failure occurs. Your
    explanation will not be graded, but it's important that you get it
    clear in your mind before going on to the next part. If you're
    stuck on this, think about alternative implementations of
    [double_bin] that might have failed to satisfy [double_bin_zero]
    yet otherwise seem correct. *)

(* SOLUTION *)
(** The problem is that [0] has many representations: it can be written
    [Z], [B0 Z], [B0 (B0 Z)], and so on.  For these alternate
    representations, if you do [bin_to_nat] then [nat_to_bin], you
    don't get back what you started with.

    Any other number also has many representations, after applying
    constructors to the multiple representations of zero. *)
(* /SOLUTION *)

(** To solve that problem, we can introduce a _normalization_ function
    that selects the simplest [bin] out of all the equivalent
    [bin]. Then we can prove that the conversion from [bin] to [nat] and
    back again produces that normalized, simplest [bin]. *)

(* EX4A (bin_nat_bin) *)

(** Define [normalize]. You will need to keep its definition as simple
    as possible for later proofs to go smoothly. Do not use
    [bin_to_nat] or [nat_to_bin], but do use [double_bin].

    Hint: Structure the recursion such that it _always_ reaches the
    end of the [bin] and _only_ processes each bit only once. Do not
    try to "look ahead" at future bits. *)

Fixpoint normalize (b:bin) : bin
  (* ADMITDEF *) :=
  match b with
  | Z    => Z
  | B0 b' => double_bin (normalize b')
  | B1 b' => incr (double_bin (normalize b'))
  end.
(* /ADMITDEF *)

(** It would be wise to do some [Example] proofs to check that your definition of
    [normalize] works the way you intend before you proceed. They won't be graded,
    but fill them in below. *)

(* SOLUTION *)
Example normalize_test_0 : normalize Z = Z. Proof. reflexivity. Qed.
Example normalize_test_1 : normalize (B1 Z) = B1 Z. Proof. reflexivity. Qed.
Example normalize_test_2 : normalize (B0 Z) = Z. Proof. reflexivity. Qed.
Example normalize_test_3 : normalize (B0 (B0 Z)) = Z. Proof. reflexivity. Qed.
Example normalize_test_4 : normalize (B1 (B0 Z)) = B1 Z. Proof. reflexivity. Qed.
(* /SOLUTION *)

(** Finally, prove the main theorem. The inductive cases could be a
    bit tricky.

    Hint: Start by trying to prove the main statement, see where you
    get stuck, and see if you can find a lemma -- perhaps requiring
    its own inductive proof -- that will allow the main proof to make
    progress. We have one lemma for the [B0] case (which also makes
    use of [double_incr_bin]) and another for the [B1] case. *)

(* QUIETSOLUTION *)
Lemma incr_double_bin : forall b, incr (double_bin b) = B1 b.
Proof.
  destruct b eqn:E.
  - (* Z *) reflexivity.
  - (* B0 *) reflexivity.
  - (* B1 *) reflexivity.
Qed.

Lemma nat_to_bin_double : forall n, nat_to_bin (double n) = double_bin (nat_to_bin n).
Proof.
  induction n as [|n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite IHn'. rewrite <- double_incr_bin. reflexivity.
Qed.
(* /QUIETSOLUTION *)

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  (* ADMITTED *)
  induction b as [|b' IHb'|b' IHb'].
  - (* Z *) reflexivity.
  - (* B0 *) simpl.
    rewrite <- IHb'.
    rewrite nat_to_bin_double.
    reflexivity.
  - (* B1 *) simpl.
    rewrite <- IHb'.
    rewrite nat_to_bin_double.
    reflexivity.
Qed.
(* /ADMITTED *)

(* GRADE_THEOREM 6: bin_nat_bin *)
(* HIDE *)

Module AltSolution.

(* Another perfectly natural idea is as follows... *)

Fixpoint bin_to_nat (m:bin) : nat
  (* ADMITDEF *) :=
  match m with
  | Z     => O
  | B0 m' => 2 * (bin_to_nat m')
  | B1 m' => 1 + 2 * (bin_to_nat m')
  end.
(* /ADMITDEF *)

Fixpoint all_zeros (b:bin) : bool :=
  match b with
  | Z => true
  | B0 b' => all_zeros b'
  | B1 _ => false
  end.

Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z    => Z
  | B0 b' => if all_zeros b' then Z else B0 (normalize b')
  | B1 b' => B1 (normalize b')
  end.

(* ...but this solution uses various techniques we haven't seen yet.
   In particular, I don't see a way to avoid reasoning about falsehood
   using discriminate (or inversion). *)

Lemma all_zeros_O: forall b, all_zeros b = true -> bin_to_nat b = 0.
Proof.
  induction b.
   + simpl. intro. reflexivity.
   + simpl. intro. rewrite IHb. (* a new idea *)
     * simpl. reflexivity.
     * rewrite H. reflexivity.
   + simpl. intro. discriminate H. (* a new tactic *)
Qed.

Lemma O_all_zeros : forall b, bin_to_nat b = 0 -> all_zeros b = true.
Proof.
  induction b.
   + simpl. intro. reflexivity.
   + simpl. intro. destruct (bin_to_nat b). (* a new idea *)
     rewrite IHb. reflexivity. reflexivity. discriminate H.
   + simpl. intro. discriminate H.
Qed.


Lemma nat_to_bin_even: forall n,
  nat_to_bin (n + n) = if n =? 0 then Z else B0 (nat_to_bin n).
Proof.
  induction n.
  + simpl. reflexivity.
  + simpl. rewrite <- plus_n_Sm. simpl. rewrite  IHn.
    destruct n.
    * reflexivity.
    * reflexivity.
Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  induction b.
  + auto.
  + simpl.
    rewrite -> add_0_r.
    rewrite nat_to_bin_even.
    destruct (all_zeros b) eqn:E .
    * (* SOONER: BCP 25: use replace instead! *)
      assert (H: bin_to_nat b =? 0 = true). (* a tedious workaround instead of [apply in] *)
       { rewrite all_zeros_O. reflexivity. rewrite E. reflexivity. }
       rewrite H. reflexivity.
    * (* SOONER: BCP 25: use replace instead! *)
       assert (H: bin_to_nat b =? 0 = false).
       { destruct (bin_to_nat b) eqn:F.
         - simpl. rewrite <- E. rewrite O_all_zeros.
           * reflexivity.
           * rewrite F. reflexivity.
         - simpl. reflexivity. }
       rewrite H. rewrite <- IHb.  reflexivity.
 + simpl.
   rewrite -> add_0_r.
   rewrite nat_to_bin_even.
   destruct (bin_to_nat b).
   * rewrite <- IHb. simpl. reflexivity.
   * rewrite <- IHb. simpl. reflexivity.
Qed.

End AltSolution.

(* /HIDE *)
(** [] *)
(* /FULL *)

(* /HIDEFROMADVANCED *)
(* TERSE: /HIDEFROMHTML *)

(* HIDE: There is MUCH more that we could say about this topic.  We
   could do a similar example (and pair of exercises) involving
   [destruct].  We could talk about references to external theorems.
   Basically, for each tactic, we could give people some guidance
   about how to lay out corresponding informal proofs...  But the
   current direction is to minimize the role of informal proofs (at
   least, the degree to which we try to get people to write them) in
   SF. *)
