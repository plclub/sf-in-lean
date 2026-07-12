(** * ProofObjects: The Curry-Howard Correspondence *)

(* SOONER: Some of this discussion is awkward: we've probably already
   been using the terminology of "proof of [ev 4]" above, so it
   doesn't make sense to introduce it here as a novel idea...

   A bigger problem is that the ideas are not really explained all
   that well.  I (BCP 9/17) found this lecture pretty hard to give.
*)
(* SOONER: More quizzes would be nice. *)
(* SOONER: PR: I'd like to see if the example of demystifying [discriminate]
   via a [match] producing contradictory predicates for different constructors
   can work and would be valuable here.  (BCP 19: Sounds great!) *)
(* LATER: I wonder whether it might be better to split this chapter
   into the material on proof objects per se and the part on defining
   the logical connectives.  The former seems like a core idea.  The
   latter is less essential. *)

(* TERSE: HIDEFROMHTML *)
(* HIDE: the "incompatible-prefix" here comes from the [exists] notation,
   which is incompatible with the one from core Rocq, which uses an
   elipsis. *)
Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From LF Require Export IndProp.
(* TERSE: /HIDEFROMHTML *)

(** #<div class="quote">#"Algorithms are the computational content of proofs."
    (Robert Harper)#</div># *)

(* HIDEFROMADVANCED *)
(** TERSE: Programming and proving in Rocq are two sides of the same coin.
    Proofs manipulate evidence much as programs manipulate data. *)
(** FULL: We have seen that Rocq has mechanisms both for _programming_,
    using inductive data types like [nat] or [list] and functions over
    these types, and for _proving_ properties of these programs, using
    inductive propositions (like [ev]), implication, universal
    quantification, and the like.  So far, we have mostly treated
    these mechanisms as if they were quite separate, and for many
    purposes this is a good way to think.  But we have also seen hints
    that Rocq's programming and proving facilities are closely related.
    For example, the keyword [Inductive] is used to declare both data
    types and propositions, and [->] is used both to describe the type
    of functions on data and logical implication.  This is not just a
    syntactic accident!  In fact, programs and proofs in Rocq are
    almost the same thing.  In this chapter we will study this connection
    in more detail.

    We have already seen the fundamental idea: provability in Rocq is
    always witnessed by _evidence_.  When we construct the proof of a
    basic proposition, we are actually building a tree of evidence,
    which can be thought of as a concrete data structure.

    If the proposition is an implication like [A -> B], then its proof
    is an evidence _transformer_: a recipe for converting evidence for
    A into evidence for B.  So at a fundamental level, proofs are
    simply programs that manipulate evidence. *)

(** Question: If evidence is data, what are propositions themselves?

    Answer: They are types! *)

(** TERSE: *** *)
(** Look again at the formal definition of the [ev] property.  *)

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** We can pronounce the ":" here as either "has type" or "is a proof
    of."  For example, the second line in the definition of [ev]
    declares that [ev_0 : ev 0].  Instead of "[ev_0] has type [ev 0],"
    we can say that "[ev_0] is a proof of [ev 0]." *)

(** TERSE: *** *)

(** This pun between types and propositions -- between [:] as "has type"
    and [:] as "is a proof of" or "is evidence for" -- is called the
    _Curry-Howard correspondence_.  It proposes a deep connection
    between the world of logic and the world of computation:
<<
                 propositions  ~  types
                 proofs        ~  programs
>>
    See \CITE{Wadler 2015} for a brief history and modern exposition. *)

(** TERSE: *** *)
(** Many useful insights follow from this connection.  To begin with,
    it gives us a natural interpretation of the type of the [ev_SS]
    constructor: *)
(* /HIDEFROMADVANCED *)
(** ADVANCED: The type of [ev_SS] says that it is a _function_
    (better: a data _constructor_) taking two arguments (one number
    [n] plus evidence for [ev n]) and returning evidence that [S (S
    n)] is even. *)

Check ev_SS
  : forall n,
      ev n ->
      ev (S (S n)).

(* HIDEFROMADVANCED *)

(** This can be read "[ev_SS] is a constructor that takes two
    arguments -- a number [n] and evidence for the proposition [ev
    n] -- and yields evidence for the proposition [ev (S (S n))]." *)
(* /HIDEFROMADVANCED *)

(** TERSE: *** *)
(** Now let's look again at an earlier proof involving [ev]. *)

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** Just as with ordinary data values and functions, we can use the
    [Print] command to see the _proof object_ that results from this
    proof script. *)

Print ev_4.
(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0)
      : ev 4  *)

(** TERSE: *** *)
(** Indeed, we can also write down this proof object directly,
    with no need for a proof script at all: *)

Check (ev_SS 2 (ev_SS 0 ev_0))
  : ev 4.

(** FULL: The expression [ev_SS 2 (ev_SS 0 ev_0)] instantiates the
    parameterized constructor [ev_SS] with the specific arguments [2]
    and [0] plus the corresponding proof objects for its premises [ev
    2] and [ev 0].  Alternatively, we can think of [ev_SS] as a
    primitive "evidence constructor" that, when applied to a
    particular number, wants to be further applied to evidence that
    this number is even; its type,
[[
      forall n, ev n -> ev (S (S n)),
]]
    expresses this functionality, in the same way that the polymorphic
    type [forall X, list X] expresses the fact that the constructor
    [nil] can be thought of as a function from types to empty lists
    with elements of that type. *)

(* HIDEFROMADVANCED *)
(** FULL: We saw in the \CHAP{Logic} chapter that we can use function
    application syntax to instantiate universally quantified variables
    in lemmas, as well as to supply evidence for assumptions that
    these lemmas impose.  For instance: *)
(** TERSE: Similarly, as we've seen, we can directly apply theorems to
    arguments in proof scripts: *)

Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.
(* /HIDEFROMADVANCED *)

(* ##################################################### *)
(** * Proof Scripts *)

(* FULL *)
(** The _proof objects_ we've been discussing lie at the core of how
    Rocq operates.  When Rocq is following a proof script, what is
    happening internally is that it is gradually constructing a proof
    object -- a term whose type is the proposition being proved.  The
    tactics between [Proof] and [Qed] tell it how to build up a term
    of the required type.  To see this process in action, let's use
    the [Show Proof] command to display the current state of the proof
    tree at various points in the following tactic proof. *)
(* /FULL *)
(* TERSE *)
(** When we write a proof using tactics, what we are doing is
    instructing Rocq to build a proof object under the hood.  We can
    see this using [Show Proof]: *)
(* /TERSE *)

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

(* HIDEFROMADVANCED *)
(** FULL: At any given moment, Rocq has constructed a term with a
    "hole" (indicated by [?Goal] here, and so on), and it knows what
    type of evidence is needed to fill this hole.

    Each hole corresponds to a subgoal, and the proof is
    finished when there are no more subgoals.  At this point, the
    evidence we've built is stored in the global context under the name
    given in the [Theorem] command. *)

(* /HIDEFROMADVANCED *)
(** TERSE: *** *)
(** Tactic proofs are convenient, but they are not essential in Rocq:
    in principle, we can always just construct the required evidence
    by hand. Then we can use [Definition] (rather than [Theorem]) to
    introduce a global name for this evidence. *)

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

(* FULL *)
(** All these different ways of building the proof lead to exactly the
    same evidence being saved in the global environment. *)

Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)

(* FULL *)
(* EX2 (eight_is_even) *)
(** Give a tactic proof and a proof object showing that [ev 8]. *)

Theorem ev_8 : ev 8.
Proof.
  (* ADMITTED *)
  apply ev_SS. apply ev_SS. apply ev_4. Qed.
(* /ADMITTED *)

Definition ev_8' : ev 8
  (* ADMITDEF *) :=
  ev_SS 6 (ev_SS 4 ev_4).
(* /ADMITDEF *)
(* GRADE_THEOREM 1: ev_8 *)
(* GRADE_THEOREM 1: ev_8' *)
(** [] *)
(* /FULL *)

(* ##################################################### *)
(** * Quantifiers, Implications, Functions *)

(** In Rocq's computational universe (where data structures and
    programs live), there are two sorts of values that have arrows in
    their types: _constructors_ introduced by [Inductive]ly defined
    data types, and _functions_.

    Similarly, in Rocq's logical universe (where we carry out proofs),
    there are two ways of giving evidence for an implication:
    constructors introduced by [Inductive]ly defined propositions,
    and... functions! *)

(** TERSE: *** *)
(** For example, consider this statement: *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

(** What is the proof object corresponding to [ev_plus4]? *)

(** TERSE: *** *)

(** We're looking for an expression whose _type_ is [forall n, ev n ->
    ev (4 + n)] -- that is, a _function_ that takes two arguments (one
    number and a piece of evidence) and returns a piece of evidence!

    Here it is: *)

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

(** FULL: Recall that [fun n => blah] means "the function that, given [n],
    yields [blah]," and that Rocq treats [4 + n] and [S (S (S (S n)))]
    as synonyms. Another equivalent way to write this definition is: *)
(** TERSE: Or equivalently: *)

Definition ev_plus4'' (n : nat) (H : ev n)
                    : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4'' : forall n : nat, ev n -> ev (4 + n).

(** TERSE: *** *)
(** When we view the proposition being proved by [ev_plus4] as a
    function type, one interesting point becomes apparent: The second
    argument's type, [ev n], mentions the _value_ of the first
    argument, [n].

    While such _dependent types_ are not found in most mainstream
    programming languages, they can be quite useful in programming
    too, as the flurry of activity in the functional programming
    community over the past couple of decades demonstrates. *)

(** TERSE: *** *)
(** Notice that both implication ([->]) and quantification ([forall])
    correspond to functions on evidence.  In fact, they are really the
    same thing: [->] is just a shorthand for a degenerate use of
    [forall] where there is no dependency, i.e., no need to give a
    name to the type on the left-hand side of the arrow:
[[
           forall (x:nat), nat
        =  forall (_:nat), nat
        =  nat          -> nat
]]
*)

(* FULL *)
(* SOONER: The following examples do not work great in the explanation.
   We need better examples.

   MG: How about just start from the third and go back to the first?
   It seems easier to understand the addition of  information instead
   of the removing.

   BCP: We need to do even better than this -- find a much better way
   of motivating the whole explanation. *)

(** FULL: For example, consider this proposition: *)

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

(** FULL: A proof term inhabiting this proposition would be a function
    with two arguments: a number [n] and some evidence [E] that [n] is
    even.  But the name [E] for this evidence is not used in the rest
    of the statement of [ev_plus2], so it's a bit silly to bother
    making up a name for it.  We could write it like this instead,
    using the dummy identifier [_] in place of a real name: *)

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

(** FULL: Or, equivalently, we can write it in a more familiar way: *)

Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

(* HIDEFROMADVANCED *)
(** In general, "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)

(* /HIDEFROMADVANCED *)
(* /FULL *)

(* QUIZ *)
(** Recall the definition of [ev]:
[[
       Inductive ev : nat -> Prop :=
         | ev_0 : ev 0
         | ev_SS : forall n, ev n -> ev (S (S n)).
]]
    What is the type of this expression?
[[
       fun (n : nat) =>
         fun (H : ev n) =>
            ev_SS (2 + n) (ev_SS n H)
]]

  (A) [forall n, ev n]

  (B) [forall n, ev (2 + n)]

  (C) [forall n, ev n -> ev n]

  (D) [forall n, ev n -> ev (2 + n)]

  (E) [forall n, ev n -> ev (4 + n)]

  (F) Not typeable
*)










(* FOLD *)
Check (fun (n : nat) =>
         fun (H : ev n) =>
            ev_SS (2 + n) (ev_SS n H))
       : forall n : nat, ev n -> ev (4 + n).
(* /FOLD *)
(* /QUIZ *)


(* ##################################################### *)
(** * Programming with Tactics *)

(** If we can build proofs by giving explicit terms rather than
    executing tactic scripts, you may wonder whether we can build
    _programs_ using tactics rather than by writing down explicit
    terms.

    Naturally, the answer is yes! *)

Definition add2 : nat -> nat.
intros n.
Show Proof.
apply S.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add2.
(* ==>
    add2 = fun n : nat => S (S n)
          : nat -> nat
*)

Compute add2 2.
(* ==> 4 : nat *)

(** FULL: Notice that we terminated the [Definition] with a [.] rather than
    with [:=] followed by a term.  This tells Rocq to enter _proof
    scripting mode_ to build an object of type [nat -> nat].  Also, we
    terminate the proof with [Defined] rather than [Qed]; this makes
    the definition _transparent_ so that it can be used in computation
    like a normally-defined function.  ([Qed]-defined objects are
    opaque during computation.)

    This feature is mainly useful for writing functions with dependent
    types, which we won't explore much further in this book.  But it
    does illustrate the uniformity and orthogonality of the basic
    ideas in Rocq. *)

(* HIDE *)
(* ####################################################### *)
(** * Building Proof Objects Incrementally (Optional) *)

(* LATER: Is the following helpful / necessary? I (Mukund) find myself
   doing exactly this when constructing proof objects... *)
(** As you probably noticed while solving the exercises earlier in the
    chapter, constructing proof objects is more involved than
    constructing the corresponding tactic proofs. Fortunately, there's
    a simple trick to help in the construction: we can start with a
    little bit of magic defining a term [admit] that can be used as a
    placeholder of any type we like. *)

Definition admit {T: Type} : T.  Admitted.

(** As an example, let's walk through the process of constructing a
    proof object demonstrating the beauty of [16]. *)

Definition ev_8_atmpt_1 : ev 8 := admit.

(** Maybe we can use [ev_SS] to construct a term of type [ev 8]?
    Recall that [ev_SS] is of type

[[
    forall n : nat, ev n -> ev (S (S n))
]]

    If we can demonstrate that [6] is even, we should be done. *)

Definition ev_8_atmpt_2 : ev 8 := ev_SS 6 admit.

(** In the attempt above, we've omitted the proofs that [6] is even,
    but it can easily be constructed following the same procedure: *)

Definition ev_8_atmpt_3 : ev 8 :=
  ev_SS 6 (ev_SS 4 admit).

Definition ev_8_atmpt_4 : ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_SS 2 admit)).

Definition ev_8_atmpt_5 : ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

(** To recap, we've been guided by an informal proof that we have in
    our minds, and we check the high level details before completing
    the intricacies of the proof. The [admit] term allows us to do
    this. *)

(* /HIDE *)


(* ###################################################################### *)
(** * Logical Connectives as Inductive Types *)

(** Inductive definitions are powerful enough to express most of the
    logical connectives we have seen so far.  Indeed, only universal
    quantification (with implication as a special case) is built into
    Rocq; all the others are defined inductively.

    Let's see how. *)

(* TERSE: HIDEFROMHTML *)
Module Props.
(* TERSE: /HIDEFROMHTML *)

(** ** Conjunction *)

(** To prove that [P /\ Q] holds, we must present evidence for both
    [P] and [Q].  Thus, it makes sense to define a proof object for
    [P /\ Q] to consist of a pair of two proofs: one for [P] and
    another one for [Q]. This leads to the following definition. *)
(* TERSE: HIDEFROMHTML *)

Module And.
(* TERSE: /HIDEFROMHTML *)

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

(** Notice the similarity with the definition of the [prod] type,
    given in chapter \CHAP{Poly}; the only difference is that [prod] takes
    [Type] arguments, whereas [and] takes [Prop] arguments. *)

Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)

(** TERSE: *** *)
(** This similarity should clarify why [destruct] and [intros]
    patterns can be used on a conjunctive hypothesis.  Case analysis
    allows us to consider all possible ways in which [P /\ Q] was
    proved -- here just one (the [conj] constructor). *)

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

(* HIDE: CH: Proof term in Show Proof above is not the simplest one,
   so I would only return to it after showing proj1'' below *)

(** Similarly, the [split] tactic actually works for any inductively
    defined proposition with exactly one constructor.  In particular,
    it works for [and]: *)

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

(* TERSE: HIDEFROMHTML *)

End And.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** This shows why the inductive definition of [and] can be
    manipulated by tactics as we've been doing.  We can also use it to
    build proofs directly, using pattern-matching.  For instance: *)

Definition proj1'' P Q (HPQ : P /\ Q) : P :=
  match HPQ with
  | conj HP HQ => HP
  end.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(* FULL *)
(* EX2 (conj_fact) *)
(** Construct a proof object for the following proposition. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R
  (* ADMITDEF *) :=
  fun P Q R HPQ HQR =>
    match HPQ, HQR with
    | conj HP _, conj _ HR => conj HP HR
    end.
(* /ADMITDEF *)
(** [] *)
(* /FULL *)

(* QUIZ *)
(** What is the type of this expression?
[[
        fun P Q R (H1: and P Q) (H2: and Q R) =>
          match (H1,H2) with
          | (conj HP _, conj  _ HR) => conj HP HR
          end.
]]

  (A) [forall P Q R, P /\ Q -> Q /\ R -> P /\ R]

  (B) [forall P Q R, Q /\ P -> R /\ Q -> P /\ R]

  (C) [forall P Q R, P /\ R]

  (D) [forall P Q R, P \/ Q -> Q \/ R -> P \/ R]

  (E) Not typeable

*)
(* FOLD *)
Check
  (fun P Q R (H1: and P Q) (H2: and Q R) =>
    match (H1,H2) with
    | (conj HP _, conj _ HR) => conj HP HR
    end) : forall P Q R, P /\ Q -> Q /\ R -> P /\ R.
(* /FOLD *)
(* /QUIZ *)

(** ** Disjunction *)

(** The inductive definition of disjunction uses two constructors, one
    for each side of the disjunction: *)
(* TERSE: HIDEFROMHTML *)

Module Or.
(* TERSE: /HIDEFROMHTML *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.

(** This declaration explains the behavior of the [destruct] tactic on
    a disjunctive hypothesis, since the generated subgoals match the
    shape of the [or_introl] and [or_intror] constructors. *)

(** TERSE: *** *)
(** Once again, we can also directly write proof objects for theorems
    involving [or], without resorting to tactics. *)

Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.

Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
  Show Proof.
Qed.

(** TERSE: *** *)
Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.

(* TERSE: HIDEFROMHTML *)

End Or.
(* TERSE: /HIDEFROMHTML *)

(* FULL *)
(* EX2 (or_commut') *)
(** Construct a proof object for the following proposition. *)

Definition or_commut' : forall P Q, P \/ Q -> Q \/ P
  (* ADMITDEF *) :=
    fun (P Q : Prop) (H : P \/ Q) =>
      match H with
      | or_introl HP => or_intror HP
      | or_intror HQ => or_introl HQ
      end.
(* /ADMITDEF *)
(** [] *)
(* /FULL *)

(* QUIZ *)
(** What is the type of this expression?
[[
       fun P Q H =>
         match H with
         | or_introl HP => @or_intror Q P HP
         | or_intror HQ => @or_introl Q P HQ
         end.
]]

  (A) [forall P Q H, Q \/ P \/ H]

  (B) [forall P Q, P \/ Q -> P \/ Q]

  (C) [forall P Q H, P \/ Q -> Q \/ P -> H]

  (D) [forall P Q, P \/ Q -> Q \/ P]

  (E) Not typeable

*)
(* FOLD *)
Check (fun P Q H =>
      match H with
      | or_introl HP => @or_intror Q P HP
      | or_intror HQ => @or_introl Q P HQ
      end) : forall P Q, P \/ Q -> Q \/ P.
(* /FOLD *)
(* /QUIZ *)

(** ** Existential Quantification *)

(** To give evidence for an existential quantifier, we package a
    witness [x] together with a proof that [x] satisfies the property
    [P]: *)

(* TERSE: HIDEFROMHTML *)

Module Ex.
(* TERSE: /HIDEFROMHTML *)

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.
(* TERSE: HIDEFROMHTML *)

End Ex.
(* TERSE: /HIDEFROMHTML *)

(** FULL: This probably needs a little unpacking.  The core definition is
    for a type former [ex] that can be used to build propositions of
    the form [ex P], where [P] itself is a _function_ from witness
    values in the type [A] to propositions.  The [ex_intro]
    constructor then offers a way of constructing evidence for [ex P],
    given a witness [x] and a proof of [P x].

    The notation in the standard library is a slight extension of
    the above, enabling syntactic forms such as [exists x y, P x y]. *)

(** TERSE: *** *)
(** The more familiar form [exists x, ev x] desugars to an expression
    involving [ex]: *)

Check ex (fun n => ev n) : Prop.

(** Here's how to define an explicit proof object involving [ex]: *)

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(* HIDE *)
(* APT: Move to IndPrinciples ? *)
    (** FULL: Here's the induction principle that Rocq generates: *)

    Check ex_ind
      : forall (X: Type) (P: X->Prop) (Q: Prop),
        (forall witness:X, P witness -> Q) ->
        (exists y, P y) ->
        Q.

    (* FULL: This induction principle can be understood as follows: If we have
        a function [f] that can construct evidence for [Q] given _any_
        witness of type [X] together with evidence that this witness has
        property [P], then from a proof of [ex X P] we can extract the
        witness and evidence that must have been supplied to the
        constructor, give these to [f], and thus obtain a proof of [Q]. *)
(* /HIDE *)

(* HIDEFROMADVANCED *)
(* HIDE: APT21: Moved this here because it seemed misplaced further below. *)
(* QUIZ *)
(** Which of the following propositions is proved by
    providing an explicit witness [w] using [exist w]?

    (A) [forall x: nat, (exists n, x = S n) -> (x<>0)]

    (B) [forall x: nat, (x<>0) -> (exists n, x = S n)]

    (C) [forall x: nat, (x=0) ->  ~(exists n, x = S n)]

    (D) [forall x: nat, x = 4 -> (x<>0)]

    (E) none of the above

*)





(* FOLD *)
Goal forall x: nat, (x<>0) -> (exists n, x = S n).
Proof.
intros. destruct x as [| x'].
- exfalso. apply H. reflexivity.
- exists x'. reflexivity.
Qed.
(* /FOLD *)
(* /QUIZ *)

(* /HIDEFROMADVANCED *)

(* FULL *)
(* EX2 (ex_ev_Sn) *)
(** Construct a proof object for the following proposition. *)

Definition ex_ev_Sn : ex (fun n => ev (S n))
  (* ADMITDEF *) :=
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).
(* /ADMITDEF *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)
(** To destruct existentials in a proof term we simply use match: *)
Definition dist_exists_or_term (X:Type) (P Q : X -> Prop) :
  (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x) :=
  fun H => match H with
           | ex_intro _ x Hx =>
               match Hx with
               | or_introl HPx => or_introl (ex_intro _ x HPx)
               | or_intror HQx => or_intror (ex_intro _ x HQx)
               end
           end.

(* FULL *)
(* EX2 (ex_match) *)
(** Construct a proof object for the following proposition: *)
Definition ex_match : forall (A : Type) (P Q : A -> Prop),
  (forall x, P x -> Q x) ->
  (exists x, P x) -> (exists x, Q x)
  (* ADMITDEF *) :=
  fun A P Q HPQ HP =>
    match HP with
    | ex_intro _ x HPx => ex_intro _ x (HPQ x HPx)
    end.
(* /ADMITDEF *)
(** [] *)
(* /FULL *)

(** ** [True] and [False] *)

(** The inductive definition of the [True] proposition is simple: *)

Inductive True : Prop :=
  | I : True.

(** It has one constructor (so every proof of [True] is the same, so
    being given a proof of [True] is not informative.) *)

(* FULL *)
(* EX1 (p_implies_true) *)
(** Construct a proof object for the following proposition. *)

Definition p_implies_true : forall P, P -> True
  (* ADMITDEF *) :=
  fun P _ => I.
(* /ADMITDEF *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)

(** [False] is equally simple -- indeed, so simple it may look
    syntactically wrong at first glance! *)

Inductive False : Prop := .

(** That is, [False] is an inductive type with _no_ constructors --
    i.e., no way to build evidence for it. For example, there is
    no way to complete the following definition such that it
    succeeds. *)

Fail
  Definition contra : False :=
  42.

(** TERSE: *** *)
(** But it is possible to destruct [False] by pattern matching. There can
    be no patterns that match it, since it has no constructors.  So
    the pattern match also is so simple it may look syntactically
    wrong at first glance. *)

Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.

(** Since there are no branches to evaluate, the [match] expression
    can be considered to have any type we want, including [0 = 1].
    Fortunately, it's impossible to ever cause the [match] to be
    evaluated, because we can never construct a value of type [False]
    to pass to the function. *)

(* FULL *)
(* EX1 (ex_falso_quodlibet') *)
(** Construct a proof object for the following proposition. *)

Definition ex_falso_quodlibet' : forall P, False -> P
  (* ADMITDEF *) :=
  fun P contra => match contra with end.
(* /ADMITDEF *)
(** [] *)
(* /FULL *)


(* TERSE: HIDEFROMHTML *)
End Props.
(* TERSE: /HIDEFROMHTML *)

(* ###################################################### *)
(** * Equality *)

(** Even Rocq's equality relation is not built in.  We can define
    it ourselves: *)
(* TERSE: HIDEFROMHTML *)

Module EqualityPlayground.
(* TERSE: /HIDEFROMHTML *)

(* HIDE: APT: (This) isn't exactly the library definition, which treats the
   first argument as a fixed parameter, in order to give a better
   induction principle. [CH: This difference is mentioned below. Is
   this difference the reason we use "==" notation instead of that
   from the standard library (=)? Reading on this may also have
   to do with setoids?] *)
Inductive eq {X:Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                       (at level 70, no associativity)
                     : type_scope.

(** FULL: The way to think about this definition (which is just a slight
    variant of the standard library's) is that, given a set [X], it
    defines a _family_ of propositions "[x] is equal to [y]," indexed
    by pairs of values ([x] and [y]) from [X].  There is just one way
    of constructing evidence for members of this family: applying the
    constructor [eq_refl] to a type [X] and a single value [x : X],
    which yields evidence that [x] is equal to [x].

    Other types of the form [eq x y] where [x] and [y] are not the
    same are thus uninhabited. *)

(** TERSE: *** *)
(** FULL: We can use [eq_refl] to construct evidence that, for example, [2 =
    2].  Can we also use it to construct evidence that [1 + 1 = 2]?
    Yes, we can.  Indeed, it is the very same piece of evidence!

    The reason is that Rocq treats as "the same" any two terms that are
    _convertible_ according to a simple set of computation rules.

    These rules, which are similar to those used by [Compute], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.  *)

(** TERSE: Rocq terms are "the same" if they are _convertible_
    according to a simple set of computation rules: evaluation of
    function applications, inlining of definitions, and simplification
    of [match]es. *)

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

(** TERSE: *** *)

(** TERSE: [reflexivity] is essentially just [apply eq_refl]. *)

(** FULL: The [reflexivity] tactic that we have used to prove
    equalities up to now is essentially just shorthand for [apply
    eq_refl].

    In tactic-based proofs of equality, the conversion rules are
    normally hidden in uses of [simpl] (either explicit or implicit in
    other tactics such as [reflexivity]).

    But you can see them directly at work in the following explicit
    proof objects: *)

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[]  :=
  fun (X:Type) (x:X) => eq_refl [x].

(** TERSE: *** *)
(** We can also pattern-match on an equality proof: *)
Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
  fun n1 n2 Heq =>
    match Heq with
    | eq_refl n => eq_refl (S n)
    end.

(** FULL: By pattern-matching against [n1 == n2], we obtain a term [n]
    that replaces [n1] and [n2] in the type we have to produce, so
    instead of [(S n1) == (S n2)], we now have to produce something
    of type [(S n) == (S n)], which we establish by [eq_refl (S n)]. *)

(** HIDE: CH: Old text for reference:
    "By pattern-matching against [n1 == n2], we obtain a term [n]
    that is known to be convertible to both [n1] and [n2]. The term
    [eq_refl (S n)] establishes [(S n) == (S n)]. The first [n] can be
    converted to [n1], and the second to [n2], which yields [(S n1) ==
    (S n2)]. Rocq handles all that conversion for us."

    CH: This explanation seems to imply that conversion in Rocq
    is symmetric. Then [eq_refl (S n1)] should work above too, but it
    doesn't. I may be wrong, but to me the replacement of [n1] and
    [n2] by [n] done by the destruct below seems like better intuition
    for what's going on, and why one can't [eq_refl (S n1)] to prove a
    goal where [n1] was already substituted away. *)

(** TERSE: *** *)

(** A tactic-based proof runs into some difficulties if we try to use
    our usual repertoire of tactics, such as [rewrite] and
    [reflexivity]. Those work with *setoid* relations that Rocq knows
    about, such as [=], but not our [==]. We could prove to Rocq that
    [==] is a setoid, but a simpler way is to use [destruct] and
    [apply] instead. *)

Theorem eq_add' : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2).
Proof.
  intros n1 n2 Heq.
  Fail rewrite Heq. (* doesn't work for _our_ == relation *)
  destruct Heq as [n]. (* n1 and n2 replaced by n in the goal! *)
  Fail reflexivity. (* doesn't work for _our_ == relation *)
  apply eq_refl.
Qed.

(* FULL *)
(* EX2 (eq_cons) *)
(** Construct the proof object for the following theorem. Use pattern
    matching on the equality hypotheses. *)

Definition eq_cons : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
    h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2
  (* ADMITDEF *) :=
  fun X h1 h2 t1 t2 Heq Teq =>
    match Heq, Teq with
    | eq_refl h, eq_refl t => eq_refl (h :: t)
    end.
(* /ADMITDEF *)
(** [] *)

(* LATER: (PR) The leibniz_equality exercise may confuse students
   because of the reuse of = for local equality. In the solution, the
   inversion cannot be replaced with a rewrite, as it can outside this
   module, because rewrite does not understand local equality. A quick
   fix is to use notation such as "x == y" locally.  Then it is clear
   that the inversion replaces local equality with library
   equality. But to really clarify, perhaps the exercise should be
   moved to IndPrinciples.v, where the text can show the actual
   definition of library equality (after the discussion of the simpler
   principle for le to motivate the use of a parameter) and the
   resulting eq_ind, and the exercise can ask for an explicit proof
   term instead of a tactics-based proof.

   (BCP) At least one reader did get confused by the rewrite failure.
   And the harder exercise is also confusing for the same reason (have
   to use apply instead of reflexivity).  Would be good to do
   something about this.  I agree with moving it elsewhere, I think.

   (PR) I have put the == quick fix in.

   MRC 3/22: I have added [eq_add'] above to explain why [rewrite] and
   [reflexivity] fail, and to show that [destruct] and [apply] will
   work.  I've also added a second exercise to give the proof object,
   which does not actually require [eq_ind]. I think the exercise
   stands on its own here, now. *)

(* EX2 (equality__leibniz_equality) *)
(** The inductive definition of equality implies _Leibniz equality_:
    what we mean when we say "[x] and [y] are equal" is that every
    property on [P] that is true of [x] is also true of [y]. Prove
    that. *)

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall (P : X -> Prop), P x -> P y.
Proof.
  (* ADMITTED *)
intros X x y Heq P HPx. destruct Heq eqn:E. apply HPx.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2 (equality__leibniz_equality_term) *)
(** Construct the proof object for the previous exercise.  All it
    requires is anonymous functions and pattern-matching; the large
    proof term constructed by tactics in the previous exercise is
    needessly complicated. Hint: pattern-match as soon as possible. *)
Definition equality__leibniz_equality_term : forall (X : Type) (x y: X),
    x == y -> forall P : (X -> Prop), P x -> P y
  (* ADMITDEF *) :=
  fun X x y Heq =>
     match Heq with
     | eq_refl z => fun P HP => HP
     end.
(* /ADMITDEF *)
(** [] *)

(* EX3? (leibniz_equality__equality) *)
(** Show that, in fact, the inductive definition of equality is
    _equivalent_ to Leibniz equality.  Hint: the proof is quite short;
    about all you need to do is to invent a clever property [P] to
    instantiate the antecedent.*)

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
(* ADMITTED *)
intros X x y H.
apply (H (fun z => x == z)).
apply eq_refl.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* HIDE: CH: The hint here is not necessarily helpful. No "clever"
   instantiation of H is needed, since Rocq can just figure it out with
   a backwards proof: *)
(* HIDE *)
Lemma leibniz_equality__equality_simpler : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
  intros X x y H. apply H. apply eq_refl.
Qed.
(* /HIDE *)


(* HIDEFROMADVANCED *)
(* QUIZ *)
(** Which of the following is a correct proof object for the proposition
[[
    exists x, x + 3 == 4
]]
?

    (A) [eq_refl 4]

    (B) [ex_intro (z + 3 == 4) 1 (eq_refl 4)]

    (C) [ex_intro (fun z => (z + 3 == 4)) 1 (eq_refl 4)]

    (D) [ex_intro (fun z => (z + 3 == 4)) 1 (eq_refl 1)]

    (E) none of the above
*)






(* FOLD *)
Fail Definition quiz1 : exists x, x + 3 == 4
  := eq_refl 4.
Fail Definition quiz2 : exists x, x + 3 == 4
  := ex_intro (z + 3 == 4) 1 (eq_refl 4).
Definition quiz3 : exists x, x + 3 == 4
  := ex_intro (fun z => (z + 3 == 4)) 1 (eq_refl 4).
Fail Definition quiz4 : exists x, x + 3 == 4
  := ex_intro (fun z => (z + 3 == 4)) 1 (eq_refl 1).
(* /FOLD *)
(* /QUIZ *)
(* /HIDEFROMADVANCED *)

(* TERSE: HIDEFROMHTML *)
End EqualityPlayground.
(* TERSE: /HIDEFROMHTML *)

(* FULL *)
(* ####################################################### *)
(** ** Inversion, Again *)

(** HIDE: PR: This section may be repetitive given the increased
    attention paid to [inversion], and it may be ineffective since
    this chapter is no longer on the recommended path. We need to
    think about whether this kind of reinforcement of the tactic is
    needed, and if so, where to place it for best impact.

    BCP 11/18: I agree -- this material is a bit redundant.  On the
    other hand, the examples at the end may be helpful, so maybe it's
    fine to leave it. *)

(** We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves.

    In general, the [inversion] tactic...

    - takes a hypothesis [H] whose type [P] is inductively defined,
      and

    - for each constructor [C] in [P]'s definition,

      - generates a new subgoal in which we assume [H] was
        built with [C],

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses,

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable,

      - adds these equalities to the context (and, for convenience,
        rewrites them in the goal), and

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O]), immediately solves the subgoal. *)

(** TERSE: *** *)
(** _Example_: If we invert a hypothesis built with [or], there are
    two constructors, so two subgoals get generated.  The
    conclusion (result type) of the constructor ([P \/ Q]) doesn't
    place any restrictions on the form of [P] or [Q], so we don't get
    any extra equalities in the context of the subgoal. *)

(** TERSE: *** *)
(** _Example_: If we invert a hypothesis built with [and], there is
    only one constructor, so only one subgoal gets generated.  Again,
    the conclusion (result type) of the constructor ([P /\ Q]) doesn't
    place any restrictions on the form of [P] or [Q], so we don't get
    any extra equalities in the context of the subgoal.  The
    constructor does have two arguments, though, and these can be seen
    in the context in the subgoal. *)

(** TERSE: *** *)
(** _Example_: If we invert a hypothesis built with [eq], there is
    again only one constructor, so only one subgoal gets generated.
    Now, though, the form of the [eq_refl] constructor does give us
    some extra information: it tells us that the two arguments to [eq]
    must be the same!  The [inversion] tactic adds this fact to the
    context. *)
(* /FULL *)

(* ####################################################### *)
(** * Rocq's Trusted Computing Base *)

(** FULL: One question that arises with any automated proof assistant
    is "why should we trust it?" -- i.e., what if there is a bug in
    the implementation that renders all its reasoning suspect?

    While it is impossible to allay such concerns completely, the fact
    that Rocq is based on the Curry-Howard correspondence gives it a
    strong foundation. Because propositions are just types and proofs
    are just terms, checking that an alleged proof of a proposition is
    valid just amounts to _type-checking_ the term.  Type checkers are
    relatively small and straightforward programs, so the "trusted
    computing base" for Rocq -- the part of the code that we have to
    believe is operating correctly -- is small too.

    What must a typechecker do?  Its primary job is to make sure that
    in each function application the expected and actual argument
    types match, that the arms of a [match] expression are constructor
    patterns belonging to the inductive type being matched over and
    all arms of the [match] return the same type, and so on. *)

(** TERSE: The Coq typechecker is what actually checks our proofs.  We
    have to trust it, but it's relatively small and
    straightforward. *)

(** FULL: There are a few additional wrinkles:

    First, since Rocq types can themselves be expressions, the checker
    must normalize these (by using the computation rules) before
    comparing them.

    Second, the checker must make sure that [match] expressions are
    _exhaustive_.  That is, there must be an arm for every possible
    constructor.  To see why, consider the following alleged proof
    object: *)

(** TERSE: For example, it rejects this broken proof: *)

Fail Definition or_bogus : forall P Q, P \/ Q -> P :=
  fun (P Q : Prop) (A : P \/ Q) =>
    match A with
    | or_introl H => H
    end.

(** FULL: All the types here match correctly, but the [match] only
    considers one of the possible constructors for [or].  Rocq's
    exhaustiveness check will reject this definition.

    Third, the checker must make sure that each recursive function
    terminates.  It does this using a syntactic check to make sure
    that each recursive call is on a subexpression of the original
    argument.  To see why this is essential, consider this alleged
    proof: *)

(** TERSE: And these: *)

Fail Fixpoint infinite_loop {X : Type} (n : nat) {struct n} : X :=
  infinite_loop n.

Fail Definition falso : False := infinite_loop 0.

(** FULL: Recursive function [infinite_loop] purports to return a
    value of any type [X] that you would like.  (The [struct]
    annotation on the function tells Rocq that it recurses on argument
    [n], not [X].)  Were Rocq to allow [infinite_loop], then [falso]
    would be definable, thus giving evidence for [False].  So Rocq rejects
    [infinite_loop]. *)

(** FULL: Note that the soundness of Rocq depends only on the
    correctness of this typechecking engine, not on the tactic
    machinery.  If there is a bug in a tactic implementation (which
    does happen occasionally), that tactic might construct an invalid
    proof term.  But when you type [Qed], Rocq checks the term for
    validity from scratch.  Only theorems whose proofs pass the
    type-checker can be used in further proof developments.  *)

(** TERSE: The tactic language and its implementation are _not_ part
    of Rocq's TCB.  This is fortunate, because complex tactics can (and
    occasionally do) produce invalid proof objects.  The [Qed] command
    runs the type checker to make sure that the proof object
    constructed by the tactic script is valid. *)

(* FULL *)
(* ####################################################### *)
(** * More Exercises *)

(** Most of the following theorems were already proved with tactics in
    \CHAP{Logic}.  Now construct the proof objects for them
    directly. *)

(* EX2 (and_assoc) *)
Definition and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R
  (* ADMITDEF *) :=
  fun P Q R H =>
    match H with
    | conj HP (conj HQ HR) => conj (conj HP HQ) HR
    end.
(* /ADMITDEF *)
(** [] *)

(* EX3 (or_distributes_over_and) *)
Definition or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R)
  (* ADMITDEF *) :=
  fun p q r =>
  conj
    (fun H =>
       match H with
       | or_introl P => conj (or_introl P) (or_introl P)
       | or_intror (conj Q R) => conj (or_intror Q) (or_intror R)
       end)
    (fun H =>
       match H with
       | conj PQ PR =>
           match PQ, PR with
           | or_introl P, _ | _, or_introl P => or_introl P
           | or_intror Q, or_intror R  => or_intror (conj Q R)
           end
       end).
(* /ADMITDEF *)
(** [] *)

(* EX3 (negations) *)
Definition double_neg : forall P : Prop,
    P -> ~~P
  (* ADMITDEF *) :=
  fun p P notP => notP P.
(* /ADMITDEF *)
(* GRADE_THEOREM 1: double_neg *)

Definition contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q
  (* ADMITDEF *) :=
  fun p q H =>
    match H with
    | conj P notP => match notP P with end
    end.
(* /ADMITDEF *)
(* GRADE_THEOREM 1: contradiction_implies_anything *)

Definition de_morgan_not_or : forall P Q : Prop,
    ~ (P \/ Q) -> ~P /\ ~Q
  (* ADMITDEF *) :=
  fun p q H =>
    conj (fun P => H (or_introl P)) (fun Q => H (or_intror Q)).
(* /ADMITDEF *)
(* GRADE_THEOREM 1: de_morgan_not_or *)
(** [] *)

(* EX2 (currying) *)
Definition curry : forall P Q R : Prop,
    ((P /\ Q) -> R) -> (P -> (Q -> R))
  (* ADMITDEF *) :=
  fun p q r H P Q =>
    H (conj P Q).
(* /ADMITDEF *)
(* GRADE_THEOREM 1: curry *)

Definition uncurry : forall P Q R : Prop,
    (P -> (Q -> R)) -> ((P /\ Q) -> R)
  (* ADMITDEF *) :=
  fun p q r H PQ =>
    match PQ with
    | conj P Q => H P Q
    end.
(* /ADMITDEF *)
(* GRADE_THEOREM 1: uncurry *)
(** [] *)

(* ####################################################### *)
(** * Proof Irrelevance (Advanced) *)

(** In \CHAP{Logic} we saw that functional extensionality could be
    added to Rocq. A similar notion about propositions can also
    be defined (and added as an axiom, if desired): *)

Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

(** Propositional extensionality asserts that if two propositions are
    equivalent -- i.e., each implies the other -- then they are in
    fact equal. The _proof objects_ for the propositions might be
    syntactically different terms. But propositional extensionality
    overlooks that, just as functional extensionality overlooks the
    syntactic differences between functions. *)

(* EX1A (pe_implies_or_eq) *)
(** Prove the following consequence of propositional extensionality. *)

Theorem pe_implies_or_eq :
  propositional_extensionality ->
  forall (P Q : Prop), (P \/ Q) = (Q \/ P).
Proof.
  (* ADMITTED *)
  unfold propositional_extensionality. intros PE P Q.
  apply PE with (P := P \/ Q) (Q := Q \/ P).
  apply or_comm.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX1A (pe_implies_true_eq) *)
(** Prove that if a proposition [P] is provable, then it is equal to
    [True] -- as a consequence of propositional extensionality. *)

Lemma pe_implies_true_eq :
  propositional_extensionality ->
  forall (P : Prop), P -> True = P.
Proof. (* ADMITTED *)
  unfold propositional_extensionality.
  intros PE P p. apply PE. split.
  - intros _. apply p.
  - intros _. apply I.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3A (pe_implies_pi) *)
(** (Acknowledgment: this theorem and its proof technique are inspired
    by Gert Smolka's manuscript Modeling and Proving in Computational
    Type Theory Using the Coq Proof Assistant, 2021. *)

(** Another, perhaps surprising, consequence of propositional
    extensionality is that it implies _proof irrelevance_, which
    asserts that all proof objects for a proposition are equal.*)

Definition proof_irrelevance : Prop :=
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

(** Prove that fact. Use [pe_implies_true_eq] to establish that the
    proposition [P] in [proof_irrelevance] is equal to [True]. Leverage
    that equality to establish that both proof objects [pf1] and
    [pf2] must be just [I]. *)

Theorem pe_implies_pi :
  propositional_extensionality -> proof_irrelevance.
Proof. (* ADMITTED *)
  unfold proof_irrelevance.
  intros PE P pf1 pf2.
  assert (H : True = P). { apply pe_implies_true_eq. apply PE. apply pf1. }
  destruct H. destruct pf1. destruct pf2. reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* HIDE *)
(*
Local Variables:
fill-column: 70
End:
*)
(* /HIDE *)
