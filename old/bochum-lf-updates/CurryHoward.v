(** * CurryHoward: A Formal Development of the Curry-Howard Correspondence *)

(** FULL: In \CHAP{ProofObjects} we learned that Rocq tactics construct _proof
    objects_: programs that manipulate evidence in Rocq's programming language,
    Gallina. Each tactic step corresponds to building a piece of a program, and
    the completed proof is a fully constructed term whose type expresses the
    statement being proved. In this sense, proving a theorem is not just a
    matter of logical reasoning -- it is also the act of writing a program.

    This perspective suggests a deeper connection. A proof of a proposition can
    be understood as a program that transforms evidence for its assumptions
    into evidence for its conclusion. Likewise, a function transforms inputs
    into outputs. From this point of view, programs can be seen as proofs, and
    the types of programs as propositions. This relationship between programs
    and proofs, and between types and propositions, is the essence of the
    Curry–Howard correspondence.

    In this chapter we make that correspondence precise. Rather than relying on
    Rocq's built-in logic and type system, we define our own _proof system_ for
    logic and our own _type system_ for programs inside Rocq. We then prove
    that whenever a program is well-typed, its type can be translated into a
    proposition that is provable in the corresponding proof system. In other
    words, typing derivations can be systematically transformed into logical
    proofs. Conversely, we will also show that whenever a proposition is
    provable, there exists a well-typed program whose type corresponds to that
    proposition. Thus, programs and proofs correspond in both directions. The
    program itself serves as a proof object, just as in Rocq, but now the
    connection is made explicit and formal.

    Why is this correspondence so exciting? It shows that logic and programming
    are not merely analogous; rather, they are fundamentally the same kind of
    structure viewed from two different perspectives. Logical connectives
    correspond to programming constructs, and proofs correspond to executable
    programs. As a result, writing a correct program becomes a form of proving
    a theorem, and proving a theorem becomes a way of constructing a program.
    This unification helps explain why systems like Rocq work the way they do,
    and it forms the foundation for modern ideas in programming languages and
    formal verification.

    Historical note: Haskell B. Curry discovered this correspondence in the
    1930s in his work on combinatory logic. William A. Howard later adapted it
    to another logical system, the sequent calculus, in 1969, and extended the
    analogy to show that computation corresponds to proof simplification.
    Building on this connection, Per Martin-Löf developed constructive type
    theory (on which Rocq itself is based) in the 1970s. The presentation in
    this chapter follows \CITE{Sørensen and Urzyczyn 2006}. *)

(** TERSE: In \CHAP{ProofObjects} we saw that Rocq tactics construct _proof
    objects_: programs in Gallina whose types are the statements being proved.
    Thus, proving a theorem is also writing a program.

    This suggests a deeper connection: proofs transform evidence for
    assumptions into evidence for conclusions, just as functions transform
    inputs into outputs. Hence programs correspond to proofs, and types to
    propositions—this is the Curry–Howard correspondence.

    In this chapter we formalize that correspondence. We define a proof system
    for logic and a type system for programs, both inside Rocq. We show:
    - If a program is well-typed, its type corresponds to a provable proposition.
    - If a proposition is provable, there exists a well-typed program of that type.

    Thus, programs and proofs correspond in both directions.

    Why is this exciting? It reveals that logic and programming share the same
    underlying structure: logical connectives correspond to programming
    constructs, and proofs correspond to executable programs. *)

From Stdlib Require Import List String.
Import ListNotations.

(** We will first develop the correspondence in a setting that focuses
    on implication. Later we will add conjunction and disjunction. *)

Module Implicational.

(* ###################################################################### *)
(** * Logic *)

(** FULL: So far we have been doing logic _with_ Rocq -- that is, with its
    definitions of logical connectives like conjunction and disjunction, and
    with its rules about how proofs can be formed. But to make the
    correspondence precise, we need to do logic _embedded in_ Rocq -- that is,
    to define the syntax of logical propositions with an inductive type,
    and to define the proof rules with an inductively-defined proposition.

    The logic formalized here is known as _propositional constructive logic_.
    It is propositional because it does not contain quantifiers. It is
    constructive for the same reasons we studied in \CHAP{Logic}: it does not
    include excluded middle (or an equivalent axiom). *)

(** TERSE: So far we have been doing logic _with_ Rocq. To make the
    correspondence precise, we instead need to do logic _embedded in_ Rocq: we
    define propositions as an inductive type and provability as an inductive
    relation. The logic formalized here is known as _propositional constructive
    logic_.*)

(* ###################################################################### *)
(** ** Propositions *)

(** We start by modeling propositions.

    - An _atom_ is an atomic proposition, much like [P] in [P : Prop], as we
      are accustomed to in Rocq. Atomic propositions are given names using
      Rocq [string]s.

    - An implication is the usual [P -> Q].

    - The contradictory proposition is named [false]. *)

Inductive proposition :=
  | atom (id : string)
  | implies (p q : proposition)
  | false.

(** From that starting point, we can define negation and truth in terms
    of other propositions. *)

Definition not (p : proposition) : proposition :=
  implies p false.

Definition true : proposition :=
  implies false false.

(** Here are some examples of propositions. *)

Definition ex_P :=
  (* P -> P *)
  implies (atom "P") (atom "P").

Definition ex_PQ :=
  (* P -> Q -> P *)
  implies (atom "P") (implies (atom "Q") (atom "P")).

Definition ex_PQR :=
  (* (P -> Q -> R) -> (P -> Q) -> P -> R *)
  implies
    (implies (atom "P") (implies (atom "Q") (atom "R")))
    (implies (implies (atom "P") (atom "Q")) (implies (atom "P") (atom "R"))).

(* ###################################################################### *)
(** ** Proofs *)

(** FULL: What is a proof? What makes a proof correct or incorrect? In the
    study of formal logic, a _proof system_ is a collection of axioms and
    inference rules that describe how to form correct proofs. Here we present a
    proof system known as _natural deduction_. It is based on a _provability_
    relation, which characterizes when a proposition is provable from a set of
    assumptions.

    The provability relation is written [A |- p], where [p] is a proposition,
    [A] is a set of propositions (the assumptions), and the _turnstile_ symbol
    [|-] is pronounced "proves". It is defined with these inference rules, in
    which we write [A, p] to mean the union of [A] and [{p}]: *)

(** TERSE: A _proof system_ specifies how to construct correct proofs via
    axioms and inference rules. We use _natural deduction_, defined by a
    _provability_ relation.

    The relation [A |- p] means that proposition [p] is provable from
    assumptions [A]. We write [A, p] for [A] extended with [p]. *)

(**
[[[
        -------------------- (axiom)
              A, p |- p

              A, p |- q
        -------------------- (implies intro)
             A |- p -> q

        A |- p -> q   A |- p
        -------------------- (implies elim)
              A |- q

             A |- false
        -------------------- (false elim)
               A |- p
]]]

*)

(** FULL: The rules can be interpreted as follows:

    - Axiom: from a set of assumptions that includes [p], it follows that
      [p] is provable -- that is, [p] holds "by assumption."

    - Implies introduction: if it is possible to prove [q] from the assumption
      of [A, p], then it follows that [p -> q] is provable from the assumption
      of [A]. That is, a proof of [p -> q] is a way of transforming the
      assumption of [p] into a proof of [q]. The name of the rule indicates
      that the implication connective [->] is _introduced_ in the conclusion;
      it was not present in the premise.

    - Implies elimination: if it is possible to prove [p -> q] as well as [p]
      from [A], then it follows that [q] is provable from [A]. That is, since
      there is a way of transforming an assumption of [p] into a proof of [q],
      and since there is a proof of [p], it is possible to use those together
      to construct a proof of [q]. The name of the rule indicates that [->]
      is _eliminated_ in the conclusion; it was present in the premises.
      This rule is commonly known as "modus ponens".

    - False elimination: if it is possible to prove [false] from [A], then
      the set of assumptions is inconsistent, so it follows that it is
      possible to prove anything from [A] -- including an arbitrary
      proposition [p]. This is the "ex falso quodlibet" principle.
      Note that there is no inference rule for false introduction, since we
      should never be able to prove [false] from a consistent set of
      assumptions. *)

(** TERSE: The rules:

    - Axiom: proof "by assumption".
    - Implies intro: to prove an implication, assume its premise and
      prove its conclusion.
    - Implies elim (modus ponens): given an implication and a proof of
      its premise, you obtain a proof of its conclusion.
    - False elim: from a contradiction, anything follows.

    Introduction rules put a connective in the conclusion; elimination rules
    remove a connective from the premise(s). Implication represents a
    transformation from proofs of [p] to proofs of [q]. There is no rule for
    introducing [false]. *)

(** The natural deduction inference rules are straightforward to formalize
    in Rocq. It is convenient to represent the set of assumptions as a list,
    since we already have lots of experience with that type. *)

Inductive provable : list proposition -> proposition -> Prop :=
  | axiom : forall A p,
      In p A ->
      provable A p
  | implies_intro : forall A p q,
      provable (p :: A) q ->
      provable A (implies p q)
  | implies_elim : forall A p q,
      provable A (implies p q) ->
      provable A p ->
      provable A q
  | false_elim : forall A p,
      provable A false ->
      provable A p.

(** Here are some examples of using the proof system. *)

Example ex_P_provable : provable [] ex_P.
(*
         -------------------- (axiom)
                p |- p
         -------------------- (implies intro)
              |- p -> p
*)
Proof.
  unfold ex_P. apply implies_intro.
  apply axiom. simpl. left. reflexivity.
Qed.

Example ex_PQ_provable : provable [] ex_PQ.
(*
      ------------------- (axiom)
           P, Q |- P
      ------------------- (implies intro)
          P |- Q -> P
      ------------------- (implies intro)
        |- P -> Q -> P
*)
Proof.
  (* WORKINCLASS *)
  unfold ex_PQ. apply implies_intro. apply implies_intro.
  apply axiom. simpl. right. left. reflexivity.
Qed.
(* /WORKINCLASS *)

Example ex_mp : forall (P Q : string),
  provable [implies (atom P) (atom Q); (atom P)] (atom Q).
(*
    ------------------- (axiom)     -------------- (axiom)
    P -> Q, P |- P -> Q             P -> Q, P |- P
    ---------------------------------------------- (implies elim)
                   P -> Q, P |- Q
*)
Proof.
  (* WORKINCLASS *)
  intros P Q. apply implies_elim with (atom P).
  - apply axiom. simpl. left. reflexivity.
  - apply axiom. simpl. right. left. reflexivity.
Qed.
(* /WORKINCLASS *)

(* TERSE *)
(* QUIZ *)
(**
    To prove [~P] from assumptions [P -> Q] and [~Q],
    we need to show [P -> false].

    What is the key intermediate proposition to derive?

    (A) [P]

    (B) [Q]

    (C) [false]

    (D) [P -> Q]







*)
(* HIDE *)
(** We need [Q].
  - Start with [P].
  - Use [P->Q] to get [Q]. <-- That is the intermediate proposition.
  - Use [Q->false] to get [false].
 *)
(* /HIDE *)
(* /QUIZ *)

(* QUIZ *)
(**
    In a proof of [P -> Q, ~Q |- ~P], which rules are required?

    (A) [axiom] and [implies_intro]

    (B) [axiom] and [false_elim]

    (C) [axiom], [implies_elim], and [implies_intro]

    (D) [axiom], [implies_intro], and [false_elim]







*)
(* HIDE *)
Example modus_tollens : forall (p q : proposition),
  provable [implies p q; not q] (not p).
Proof.
  intros p q. unfold not.
  apply implies_intro.
  apply implies_elim with q.
    - apply axiom. simpl. right. right. left. reflexivity.
    - apply implies_elim with p.
      + apply axiom. simpl. right. left. reflexivity.
      + apply axiom. simpl. left. reflexivity.
Qed.
(* /HIDE *)
(* /QUIZ *)
(* /TERSE *)

(** The use of the [axiom] rule followed by reasoning about [In] gets tedious.
    We can automate it with the following little custom tactic. The techniques
    used in the tactic will be explained in \CHAP{Auto} (or alternatively
    \CHAP{AltAuto}). *)

Ltac by_assumption :=
  constructor;
  repeat match goal with
  | |- In ?p (?h :: ?t) => simpl
  | |- (?x = ?y) \/ ?p => first [left; reflexivity | right]
  | |- False => idtac "by_assumption failed: not in assumptions"; fail
  end.

Example in_assumptions : provable [atom "P"] (atom "P").
Proof.
  by_assumption.
Qed.

Example not_in_assumptions : provable [atom "Q"] (atom "P").
Proof.
  by_assumption.
Abort.

Example ex_P_provable' : provable [] ex_P.
Proof.
  unfold ex_P. apply implies_intro.
  by_assumption.
Qed.

(* FULL *)
(* EX2 (ex_PQR_provable) *)

(** Show that the third example proposition we originally gave is provable.
    First, as a warmup, prove an equivalent of it in Rocq. *)

Theorem ex_PQR_provable_rocq : forall (P Q R : Prop),
  (P -> Q -> R) -> (P -> Q) -> P -> R.
Proof.
  (* ADMITTED *)
  intros P Q R HPQR HPQ HP. apply HPQR.
  - apply HP.
  - apply HPQ. apply HP.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: ex_PQR_provable_rocq *)

(** Second, prove it using natural deduction.

    Tip: try sketching out the derivation with the inference rules on paper
    first. The tricky part is finding the correct propositions to instantiate
    [implies_elim] with each time. *)

Theorem ex_PQR_provable_nd : provable [] ex_PQR.
Proof.
  (* ADMITTED *)
  unfold ex_PQR. apply implies_intro. apply implies_intro.
  apply implies_intro. apply implies_elim with (implies (atom "Q") (atom "R")).
  - apply implies_intro. apply implies_elim with (atom "Q").
    + by_assumption.
    + apply implies_elim with (atom "P").
      * by_assumption.
      * by_assumption.
  - apply implies_elim with (atom "P").
    + by_assumption.
    + by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1.5: ex_PQR_provable_nd *)

(** [] *)

(* EX3 (more_provable_propositions) *)

(** Prove each of the following propositions. *)

Theorem implies_trans : forall (P Q R : string),
  provable []
  (implies (implies (atom P) (atom Q))
           (implies (implies (atom Q) (atom R))
                    (implies (atom P) (atom R)))).
Proof.
  (* ADMITTED *)
  intros P Q R. apply implies_intro. apply implies_intro. apply implies_intro.
  apply implies_elim with (atom Q).
  - by_assumption.
  - apply implies_elim with (atom P).
    + by_assumption.
    + by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: implies_trans *)

Theorem exfalso_quodlibet : forall (P : string),
  provable [] (implies false (atom P)).
Proof.
  (* ADMITTED *)
  intros P. apply implies_intro. apply false_elim. by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: exfalso_quodlibet *)

Theorem contrapositive : forall (P Q : string),
  provable []
  (implies (implies (atom P) (atom Q))
           (implies (not (atom Q)) (not (atom P)))).
Proof.
  (* ADMITTED *)
  intros P Q. unfold not.
  apply implies_intro. apply implies_intro. apply implies_intro.
  apply implies_elim with (atom Q).
  - by_assumption.
  - apply implies_elim with (atom P).
    + by_assumption.
    + by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: contrapositive *)

(** [] *)
(* /FULL *)

(* HIDE *)
Theorem weakening_provable :
  forall (A : list proposition) (p q : proposition),
    provable A p -> provable (q :: A) p.
Proof.
  intros A p q H. induction H.
  - apply axiom. simpl. right. apply H.
  - apply implies_intro.
Abort.

Theorem consistency : ~ provable [] false.
Proof.
  intros H. remember false as p. induction H.
Abort.
(* /HIDE *)

(* ###################################################################### *)
(** * Programs *)

(** FULL: Much like we just embedded logic in Rocq, we now need to embed a
    programming language in Rocq. That is, we model the syntax of programs
    with inductive types, and we model type checking with an
    inductively-defined proposition.

    The language we formalize is the _simply-typed pure lambda calculus_.
    It is a small but expressive core of functional programming: programs
    consist of variables, functions, and function application. At this level
    of detail, the correspondence between programs and proofs can be
    stated cleanly and proved precisely. Moreover, this calculus already
    captures the essential structure underlying typed functional languages,
    so the results we obtain here generalize well beyond this minimal setting. *)

(** TERSE: Much like we just embedded logic in Rocq, we now need to embed a
    programming language in Rocq. The language we formalize here is known as
    the _simply-typed pure lambda calculus_. It is the core of any functional
    programming language.  *)

(* ###################################################################### *)
(** ** Syntax *)

(** We start by modeling the types of programs.

    - A _type variable_ stands for an unknown type, much like the [X]
      in [X : Type] that we have used when defining polymorphic lists
      in Rocq. We again use Rocq [string]s as identifiers.

    - An _arrow_ represents a function type, like [t1 -> t2] in Rocq. *)

Inductive type :=
  | tvar (id : string)
  | arrow (t1 t2 : type).

(** Next, we model program _expressions_ (aka _terms_).

    - As usual we have _variables_.

    - A function aka _abstraction_ is like [fun (x : t) => e] in Rocq.
      It binds a variable, explicitly states the type of that variable,
      and has an expression as its body.

    - An _application_ applies a function to an argument, like [e1 e2] in
      Rocq.*)

Inductive expr :=
  | var (id : string)
  | abs (id : string) (t : type) (e : expr)
  | app (e1 e2 : expr).

(** Here are some examples of programs. *)

Definition e_I : expr :=
  (* fun (x:T) => x *)
  abs "x" (tvar "T") (var "x").

Definition e_K : expr :=
  (* fun (x:T) (y:U) => x *)
  abs "x" (tvar "T") (abs "y" (tvar "U") (var "x")).

Definition e_S : expr :=
  (* fun (x:T->U->V) (y:T->U) (z:T) => x z (y z) *)
  abs "x" (arrow (tvar "T") (arrow (tvar "U") (tvar "V")))
    (abs "y" (arrow (tvar "T") (tvar "U"))
      (abs "z" (tvar "T")
        (app (app (var "x") (var "z"))
             (app (var "y") (var "z"))))).

(* ###################################################################### *)
(** ** Type Checking *)

(** FULL: A _type system_ is a collection of axioms and inference rules for
    determining whether a program is well-typed. Because our little programming
    language explicitly states the type of each variable as part of the [abs]
    syntax, it is quite easy to build a type system for the language. In
    particular, we do not need to infer any types.

    The basis for our type system is a _typing_ relation written [E |- e : t],
    where [e] is an expression, [t] is a type, [E] is a _typing environment_
    that records the types of variables, and as usual the colon is pronounced
    "has type".

    The typing environment can be thought of as a _partial map_ that binds
    identifiers to types. We write [E, x:t] to denote the map that contains
    all the bindings of [E] as well as a binding from [x] to [t]. We assume
    (without loss of generality -- variables can be renamed as needed) in
    that notation that [x] was not already bound in [E]. *)

(** TERSE: A _type system_ specifies when programs are well-typed.
    The typing relation [E |- e : t] means expression [e] has type [t]
    under environment [E], which maps variables to types. We write
    [E, x:t] to extend [E] with a binding for identifier [x] at type [t]. *)

(** The typing relation is defined with the following inference rules:

[[[
        ---------------------------------- (t-var)
                E, x : t |- x : t

              E, x : t1 |- e : t2
        ---------------------------------- (t-abs)
        E |- fun (x : t1) => e : t1 -> t2

        E |- e1 : t1 -> t2    E |- e2 : t1
        ---------------------------------- (t-app)
                 E |- e1 e2 : t2
]]]

*)

(** FULL: The rules can be interpreted as follows:

    - T-Var: if the typing environment binds [x] to [t], then [x] has type [t]
      in that environment.

    - T-Abs: if [e] has type [t2] in a typing environment that binds [x] to
      [t1], then the function [fun (x : t1) => e], created by abstracting [x],
      has type [t1 -> t2].

    - T-App: if [e1] is a function with type [t1 -> t2] and [e2] has type [t1],
      then applying [e1] to input [e2] yields an output of type [t2]. *)

(** TERSE: The rules:

    - T-Var: a variable has the type assigned to it in the environment.

    - T-Abs: to type a function, assume its parameter has a given type
      and type-check the body.

    - T-App: to type a function application, type-check the function
      and its argument, then use the function's output type. *)

(** As a simple representation of partial maps, we use an _association list_,
    that is, a list of pairs, where the first component of the pair is a _key_
    and the second component is the value to which that key is bound. For
    simplicity, we omit any checking to prohibit duplicate keys. *)

Definition tenv := list (string * type).

(** The type system inference rules are straightforward to formalize in Rocq. *)

Inductive hastype : tenv -> expr -> type -> Prop :=
  | t_var : forall E x t,
      In (x, t) E ->
      hastype E (var x) t
  | t_abs : forall E x t1 e t2,
      hastype ((x, t1) :: E) e t2 ->
      hastype E (abs x t1 e) (arrow t1 t2)
  | t_app : forall E e1 t1 t2 e2,
      hastype E e1 (arrow t1 t2) ->
      hastype E e2 t1 ->
      hastype E (app e1 e2) t2.

(** The example programs given above are all well-typed. Our [by_assumption]
    tactic continues to work equally well for association lists. *)

Example e_I_typable :
  hastype [] e_I (arrow (tvar "T") (tvar "T")).
(*
        ---------------------------- (t-var)
               x : T |- x : T
        ---------------------------- (t-abs)
        |- fun (x : T) => x : T -> T
*)
Proof.
  unfold e_I. apply t_abs. by_assumption.
Qed.

Example e_K_typable :
  hastype [] e_K (arrow (tvar "T") (arrow (tvar "U") (tvar "T"))).
(*
      ------------------------------------------------ (t-var)
                   x : T, y : U |- x : T
      ------------------------------------------------ (t-abs)
            x : T |- fun (y : U) => x : U -> T
      ------------------------------------------------ (t-abs)
      |- fun (x : T) => fun (y : U) => x : T -> U -> T
*)
Proof.
  (* WORKINCLASS *)
  unfold e_K. apply t_abs. apply t_abs. by_assumption.
Qed.
(* /WORKINCLASS *)

(* FULL *)
(* EX2 (e_S_typable) *)

(** Show that the third example program from above is typable.
    Tip: try drawing out the proof on paper first. *)

Theorem e_S_typable :
  hastype [] e_S
    (arrow (arrow (tvar "T") (arrow (tvar "U") (tvar "V")))
           (arrow (arrow (tvar "T") (tvar "U"))
                  (arrow (tvar "T") (tvar "V")))).
Proof.
  (* ADMITTED *)
  unfold e_S. apply t_abs. apply t_abs. apply t_abs.
  apply t_app with (tvar "U").
  - apply t_app with (tvar "T").
    + by_assumption.
    + by_assumption.
  - apply t_app with (tvar "T").
    + by_assumption.
    + by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: e_S_typable *)

(** [] *)

(* EX3 (more_typable_programs) *)

Definition prog_B :=
  (abs "g" (arrow (tvar "Y") (tvar "Z"))
    (abs "f" (arrow (tvar "X") (tvar "Y"))
      (abs "x" (tvar "X")
        (app (var "g") (app (var "f") (var "x")))))).

Theorem prog_B_typable : exists (T : type),
  hastype [] prog_B T.
Proof.
  (* ADMITTED *)
  unfold prog_B.
  exists (arrow (arrow (tvar "Y") (tvar "Z"))
                (arrow (arrow (tvar "X") (tvar "Y"))
                       (arrow (tvar "X") (tvar "Z")))).
   apply t_abs. apply t_abs. apply t_abs.
   apply t_app with (tvar "Y").
   - by_assumption.
   - apply t_app with (tvar "X").
     + by_assumption.
     + by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: prog_B_typable *)

Definition prog_C :=
  (abs "f" (arrow (tvar "X") (arrow (tvar "Y") (tvar "Z" )))
    (abs "y" (tvar "Y")
      (abs "x" (tvar "X")
        (app (app (var "f") (var "x")) (var "y"))))).

Theorem prog_C_typable : exists (T : type),
  hastype [] prog_C T.
Proof.
  (* ADMITTED *)
  unfold prog_C.
  exists (arrow (arrow (tvar "X") (arrow (tvar "Y") (tvar "Z") ))
                (arrow (tvar "Y") (arrow (tvar "X") (tvar "Z")))).
  apply t_abs. apply t_abs. apply t_abs.
  apply t_app with (tvar "Y").
  - apply t_app with (tvar "X").
    + by_assumption.
    + by_assumption.
  - by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: prog_C_typable *)

Definition prog_W_type :=
  arrow (arrow (tvar "X") (arrow (tvar "X") (tvar "Y")))
        (arrow (tvar "X") (tvar "Y")).

Theorem prog_W_typable : exists (e : expr),
  hastype [] e prog_W_type.
Proof.
  (* ADMITTED *)
  unfold prog_W_type.
  exists (abs "f" (arrow (tvar "X") (arrow (tvar "X") (tvar "Y")))
                  (abs "x" (tvar "X")
                  (app (app (var "f") (var "x"))
                       (var "x")))).
  apply t_abs. apply t_abs.
  apply t_app with (tvar "X").
  - apply t_app with (tvar "X").
    + by_assumption.
    + by_assumption.
  - by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: prog_W_typable *)

(** [] *)
(* /FULL *)

(* HIDE *)

Theorem selfapp_untypable :
  ~ exists (E : tenv) (t : type),
      hastype E (app (var "x") (var "x")) t.
Proof.
  intros [E [t H]]. inversion H. inversion H3. inversion H5.
  subst. assert (contra: arrow t1 t = t1). {
    (* Need uniqueness of keys in tenv. *)
    admit. }
  clear E H H3 H5 H8 H12.
  induction t1.
  - discriminate.
  - inversion contra. subst. apply IHt1_1. apply H0.
Admitted.

Definition vars_of_tenv (E : tenv) : list string :=
  map fst E.

Theorem weakening_hastype :
  forall (E : tenv) (x : string) (t u : type) (e : expr),
    hastype E e t ->
    ~ In x (vars_of_tenv E) ->
    hastype ((x, u) :: E) e t.
Proof.
  intros E x t u e H Hnotin. induction H.
  - apply t_var. simpl. right. apply H.
  - apply t_abs.
Abort.

(* /HIDE *)

(* ###################################################################### *)
(** * The Correspondence *)

(** FULL: Using the formalizations of provability and typability, we can now
    make the Curry-Howard correspondence precise. Rather than treating it
    as an informal analogy, we will compare the inference rules of the
    proof system with those of the type system.

    The key idea is that each logical rule has a corresponding typing rule,
    and that typing derivations can be viewed as proof derivations with
    additional computational content. To see this, we examine the rules
    side by side and observe how they express the same underlying structure. *)

(** TERSE: Using the formalizations of provability and typability, we can now
    make the Curry-Howard correspondence precise. *)

(* ###################################################################### *)
(** ** Arrow Elimination *)

(** First, consider the rules that involve eliminating an arrow, whether it's a
    function type arrow or an implication arrow: *)

(**
[[[
        E |- e1 : t1 -> t2    E |- e2 : t1
        ---------------------------------- (t-app)
                E |- e1 e2 : t2

            A |- p -> q         A |- p
        ---------------------------------- (implies elim)
                     A |- q
]]]

*)

(** Observe what happens if we erase from [t-app] everything between
    each turnstile [|-] (exclusive) and colon (inclusive): *)

(**
[[[
            E |- t1 -> t2       E |- t1
        ---------------------------------- (t-app-erased)
                     E |- t2

            A |- p -> q         A |- p
        ---------------------------------- (implies elim)
                     A |- q
]]]

*)

(** FULL: The resulting rule (even if it is no longer a well-formed typing rule)
    looks _exactly_ like [implies elim]. This is no accident!

    Recall that we can think of implication as a transformation: it takes a
    proof of [p] and transforms it into a proof of [q]. Likewise, an arrow type
    is a transformation: it takes an input of type [t1] and transforms it into
    an output of type [t2].

    The typing rule [t-app] thus is expressing the same idea as the provability
    rule [implies elimination], but augments it with the code [e1] that
    accomplishes the transformation. *)

(** TERSE: Erasing programs from [t-app] yields [implies elim]!

    Both rules express _transformation_:

    - Implication maps proofs of [p] to proofs of [q]
    - Functions map inputs of type [t1] to outputs of type [t2].

    The typing rule just adds the code that performs the transformation. *)

(* ###################################################################### *)
(** ** Arrow Introduction *)

(** Second, consider the rules that involve introducing an arrow: *)

(**
[[[
              E, x : t1 |- e : t2
        --------------------------------- (t-abs)
        E |- fun (x : t1) => e : t1 -> t2

                    A, p |- q
        --------------------------------- (implies intro)
                   A |- p -> q
]]]

*)

(** As before, if we erase the programs from [t-abs], we obtain a rule
    that looks exactly like [implies introduction]: *)

(**
[[[
                   E, t1 |- t2
        --------------------------------- (t-abs-erased)
                  E |- t1 -> t2

                    A, p |- q
        --------------------------------- (implies intro)
                   A |- p -> q
]]]
*)

(** FULL: Again, this is no accident. Both express the idea of how to create a
    transformer, whether that is an implication or a function. The typing rule
    [t-abs] is just more explicit by providing the code [fun (x : t1) => e]
    that implements the transformation. *)

(** TERSE: Both rules create a transformer: implication on proofs, functions on values.
    The typing rule includes the code that implements the transformation. *)

(* ###################################################################### *)
(** ** Assumptions *)

(** Third and finally, consider the rules that involve assumptions, and the
    erasure of the typing rule: *)

(**
[[[
        ----------------- (t-var)
        E, x : t |- x : t

        ----------------- (t-var-erased)
            E, t |- t

        ----------------- (axiom)
            A, p |- p
]]]

*)

(** Again, [t-var-erased] looks exactly like its logical companion [axiom].
    The rules are expressing the same basic principle of reasoning "by
    assumption." *)

(* TERSE *)
(* QUIZ *)
(**
    What proposition does the following program prove?
    (Assume that T and U are types in scope.)

        fun (f : T -> U) => f

    (A) T -> U

    (B) (T -> U) -> (T -> U)

    (C) (T -> U) -> T

    (D) T -> (T -> U)






*)
(* HIDE *)
Definition itproves1 := fun (T U : Type) =>
  fun (f : T -> U) => f.
Check itproves1 : forall T U : Type,
  (T -> U) -> T -> U.
(* /HIDE *)
(* /QUIZ *)

(* QUIZ *)
(**
    What proposition does the following program prove?

        fun (f : T -> U) =>
        fun (x : T) =>
          f x

    A. T -> U
    B. (T -> U) -> T -> U
    C. (T -> U) -> U
    D. T -> (T -> U)







*)
(* HIDE *)
Definition itproves2 := fun (T U : Type) =>
  fun (f : T -> U) => fun (x : T) => f x.
Check itproves2 : forall T U : Type,
  (T -> U) -> T -> U.
(* /HIDE *)
(* /QUIZ *)
(* /TERSE *)

(* ###################################################################### *)
(** ** Proving the Correspondence *)

(** We saw above that by erasing programs from typability rules, we are
    left essentially with provability rules. Thus, any derivation of
    the type of a program also establishes a derivation of the provability
    of a corresponding proposition. *)

(** For example, here is a derivation of the type [X -> (Y -> X)] of a program:

<<
        ------------------------------------------------- (t-var)
                         x:X, y:Y |- x : X
        ------------------------------------------------- (t-abs)
                  x:X |- fun (y:Y) => x : Y -> X
        ------------------------------------------------- (t-abs)
        |- fun (x:X) => (fun (y:Y) => x)) : X -> (Y -> X)
>>

And by erasing the code from that derivation we are left with a derivation
of the provability of [X -> (Y -> X)]:

<<
        ---------------- (axiom)
            X, Y |- X
        ---------------- (implies introduction)
          X |- Y -> X
        ---------------- (implies introduction)
        |- X -> (Y -> X)
>>

*)

(** Therefore, our logical proof system rules are in a correspondence with our
    type system rules:

    - [axiom] corresponds to [t_var].

    - [implies_intro] corresponds to [t_abs].

    - [implies_elim] corresponds to [t_app].

    And therefore there is a correspondence between logical connectives and
    programming language features:

    - _Propositional variables_ correspond to _program variables_.

    - _Implication_ corresponds to _functions and application_.

    *)

(** There is a small mismatch, however, between our data structures for
    types and propositions. We can use the following function to
    convert a type to a proposition: *)

Fixpoint proposition_of_type (t : type) : proposition :=
  match t with
  | tvar x => atom x
  | arrow t1 t2 =>
    implies (proposition_of_type t1) (proposition_of_type t2)
  end.

Example pot_XY :
  proposition_of_type
    (arrow (tvar "X") (arrow (tvar "Y") (tvar "X")))
  =
    (implies (atom "X") (implies (atom "Y") (atom "X"))).
Proof. reflexivity. Qed.

(** With the help of that function, we can convert a type environment into a
    list of assumptions: *)

Definition assumptions_of_tenv (E : tenv) : list proposition :=
  map proposition_of_type (map snd E).

Example aot_XY :
  assumptions_of_tenv
    [("x"%string, tvar "X"); ("y"%string, tvar "Y")]
  =
    [atom "X"; atom "Y"].
Proof. reflexivity. Qed.

(* FULL *)
(* EX2 (in_snd) *)

(** The following lemma should be useful in the main theorem below. Hint: proceed by
    induction on [l]. *)

Lemma in_snd : forall (X Y Z : Type) (x : X) (y : Y) (f : Y -> Z) (l : list (X*Y)),
  In (x, y) l -> In (f y) (map f (map snd l)).
Proof. (* ADMITTED *)
  intros X Y Z x y f l Hin. induction l as [ | (a, b) t].
  - simpl in Hin. destruct Hin.
  - simpl. simpl in Hin. destruct Hin as [Hhere | Hlater].
    + inversion Hhere. left. reflexivity.
    + right. apply IHt. apply Hlater.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: in_snd *)

(** [] *)
(* /FULL *)

(* EX3 (curry_howard) *)

(** FULL: At last we can state the first of two main theorems of the Curry-Howard
    correspondence: if [E |- e : t] then [E |- t] after applying appropriate
    conversion functions to [E] and [t]. That is, a derivation of typability for a
    program also yields a derivation of provability for a proposition.
    (We return to the second of the two main theorems at the end of the chapter.)

    Hint: proceed by induction on the evidence for [hastype]. *)

(** TERSE: Derivation of typability for a program also yields a derivation of
    provability for a proposition.*)

Theorem curry_howard : forall E e t,
  hastype E e t ->
  provable (assumptions_of_tenv E) (proposition_of_type t).
Proof. (* ADMITTED *)
  intros E e t HT. induction HT.
  - apply axiom. unfold assumptions_of_tenv. apply in_snd with x. apply H.
  - unfold assumptions_of_tenv in IHHT. simpl in IHHT.
    unfold assumptions_of_tenv. simpl.
    apply implies_intro. apply IHHT.
  - apply implies_elim with (proposition_of_type t1).
    + simpl in IHHT1. apply IHHT1.
    + apply IHHT2.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: curry_howard *)

(** [] *)

End Implicational.

(* ###################################################################### *)
(** * Extending the Correspondence to Larger Systems *)

Module Propositional.

(* ###################################################################### *)
(** ** Logic: Adding Conjunction and Disjunction *)

(** Now we extend the development to a full propositional logic with conjunction
    and disjunction. *)

Inductive proposition :=
  | atom (id : string)
  | implies (p q : proposition)
  | and (p q : proposition)
  | or (p q : proposition)
  | false.

Definition not (f : proposition) : proposition :=
  implies f false.

Definition true : proposition :=
  implies false false.

Definition iff (p q : proposition) :=
  and (implies p q) (implies q p).

(** The new proof system rules are as follows: *)

(**
[[[
        A |- p   A |- q
        --------------- (and intro)
          A |- p /\ q

        A |- p /\ q
        ----------- (and elim L)
          A |- p

        A |- p /\ q
        ----------- (and elim R)
          A |- q

          A |- p
        ----------- (or intro L)
        A |- p \/ q

          A |- q
        ----------- (or intro R)
        A |- p \/ q

        A, p |- r    A, q |- r    A |- p \/ q
        ------------------------------------- (or elim)
                      A |- r
]]]

*)

(** FULL: The new rules can be interpreted as follows:

    - And introduction: if it is possible to prove both [p] and [q] from
      [A], then it follows that [p /\ q] is provable from [A]. That is,
      a proof of a conjunction consists of a proof of each component.

    - And elimination (left): if it is possible to prove [p /\ q] from [A],
      then it follows that [p] is provable from [A]. That is, from a proof
      of a conjunction, we can extract its first component.

    - And elimination (right): if it is possible to prove [p /\ q] from [A],
      then it follows that [q] is provable from [A].

    - Or introduction (left): if it is possible to prove [p] from [A], then
      it follows that [p \/ q] is provable from [A]. That is, to prove a
      disjunction, it suffices to prove one of its components and identify
      which component we proved (by choosing the left vs. right rule).

    - Or introduction (right): if it is possible to prove [q] from [A], then
      it follows that [p \/ q] is provable from [A].

    - Or elimination: if from [A, p] we can prove [r], and from [A, q] we can
      prove [r], and we also have a proof of [p \/ q] from [A], then it follows
      that [r] is provable from [A]. That is, to use a proof of a disjunction,
      we must consider both cases -- assuming [p] and assuming [q] -- and show
      that the same conclusion [r] follows in each case. *)

(** TERSE: The rules:

    - And intro: to prove a conjunction, prove both parts.
    - And elim L: from a conjunction, obtain its first component.
    - And elim R: from a conjunction, obtain its second component.
    - Or intro L: to prove a disjunction, prove the left part.
    - Or intro R: to prove a disjunction, prove the right part.
    - Or elim: to use a disjunction, consider both cases and show a
      common conclusion follows. *)

(** We formalize those as follows. *)

Inductive provable : list proposition -> proposition -> Prop :=
  (* The first four rules were part of our previous development. *)
  | axiom : forall A p,
      In p A ->
      provable A p
  | implies_intro : forall A p q,
      provable (p :: A) q ->
      provable A (implies p q)
  | implies_elim : forall A p q,
      provable A (implies p q) ->
      provable A p ->
      provable A q
  | false_elim : forall A p,
      provable A false ->
      provable A p
  (* The next six rules are new. *)
  | and_intro : forall A p q,
      provable A p ->
      provable A q ->
      provable A (and p q)
  | and_elim_L : forall A p q,
      provable A (and p q) ->
      provable A p
  | and_elim_R : forall A p q,
      provable A (and p q) ->
      provable A q
  | or_intro_L : forall A p q,
      provable A p ->
      provable A (or p q)
  | or_intro_R : forall A p q,
      provable A q ->
      provable A (or p q)
  | or_elim : forall A p q r,
      provable (p :: A) r ->
      provable (q :: A) r ->
      provable A (or p q) ->
      provable A r.

(* FULL *)

Ltac by_assumption :=
  constructor;
  repeat match goal with
  | |- In ?p (?h :: ?t) => simpl
  | |- (?x = ?y) \/ ?p => first [left; reflexivity | right]
  | |- False => idtac "by_assumption failed: not in assumptions"; fail
  end.

(* EX2 (false_iff_inconsistency) *)

(** Prove that [false] is equivalent to an inconsistency. *)

Theorem false_iff_inconsistency : forall (p : proposition),
  provable [] (iff false (and p (not p))).
Proof.
  (* ADMITTED *)
  intros p. apply and_intro.
  - apply implies_intro. apply false_elim. by_assumption.
  - apply implies_intro. unfold not. apply implies_elim with p.
    + apply and_elim_R with p. by_assumption.
    + apply and_elim_L with (implies p false). by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: false_iff_inconsistency *)

(** [] *)

(* EX2 (and_comm) *)

(** Prove that [and] is commutative. *)

Theorem and_comm : forall (p q : proposition),
  provable [] (iff (and p q) (and q p)).
Proof.
  (* ADMITTED *)
  intros p q. unfold iff. apply and_intro.
  - apply implies_intro. apply and_intro.
    + apply and_elim_R with p. by_assumption.
    + apply and_elim_L with q. by_assumption.
  - apply implies_intro. apply and_intro.
    + apply and_elim_R with q. by_assumption.
    + apply and_elim_L with p. by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: and_comm *)

(** [] *)

(* EX2 (or_comm) *)

(** Prove that [or] is commutative. *)

Theorem or_comm : forall (p q : proposition),
  provable [] (iff (or p q) (or q p)).
Proof.
  (* ADMITTED *)
  intros p q. unfold iff. apply and_intro.
  - apply implies_intro. apply (or_elim _ p q (or q p)).
    + apply or_intro_R. by_assumption.
    + apply or_intro_L. by_assumption.
    + by_assumption.
  - apply implies_intro. apply (or_elim _ q p (or p q)).
    + apply or_intro_R. by_assumption.
    + apply or_intro_L. by_assumption.
    + by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: or_comm *)

(** [] *)

(* EX3 (and_distr_or) *)

(** Prove that [and] distributes over [or]. *)

Theorem and_distr_or : forall (p q r : proposition),
  provable [] (iff (and p (or q r)) (or (and p q) (and p r))).
Proof.
  (* ADMITTED *)
  intros p q r. unfold iff. apply and_intro.
  - apply implies_intro. apply (or_elim _ q r (or (and p q) (and p r))).
    + apply or_intro_L. apply and_intro.
      * apply and_elim_L with (or q r). by_assumption.
      * by_assumption.
    + apply or_intro_R. apply and_intro.
      * apply and_elim_L with (or q r). by_assumption.
      * by_assumption.
    + apply and_elim_R with p. by_assumption.
  - apply implies_intro. apply and_intro.
    + apply (or_elim _ (and p q) (and p r) p).
      * apply and_elim_L with q. by_assumption.
      * apply and_elim_L with r. by_assumption.
      * by_assumption.
    + apply (or_elim _ (and p q) (and p r) (or q r)).
      * apply or_intro_L. apply and_elim_R with p. by_assumption.
      * apply or_intro_R. apply and_elim_R with p. by_assumption.
      * by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: and_distr_or *)

(** [] *)

(* EX3? (or_distr_and) *)

(** Prove that [or] distributes over [and]. *)

Theorem or_distr_and : forall (p q r : proposition),
  provable [] (iff (or p (and q r)) (and (or p q) (or p r))).
Proof.
  (* ADMITTED *)
  intros p q r. unfold iff. apply and_intro.
  - apply implies_intro. apply and_intro.
    + apply (or_elim _ p (and q r) (or p q)).
      * apply or_intro_L. by_assumption.
      * apply or_intro_R. apply and_elim_L with r. by_assumption.
      * by_assumption.
    + apply (or_elim _ p (and q r) (or p r)).
      * apply or_intro_L. by_assumption.
      * apply or_intro_R. apply and_elim_R with q. by_assumption.
      * by_assumption.
  - apply implies_intro. apply (or_elim _ p q _).
    + apply or_intro_L. by_assumption.
    + apply (or_elim _ p r _).
      * apply or_intro_L. by_assumption.
      * apply or_intro_R. apply and_intro.
        ** by_assumption.
        ** by_assumption.
      * apply and_elim_R with (or p q). by_assumption.
    + apply and_elim_L with (or p r). by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: or_distr_and *)

(** [] *)

(* /FULL *)

(* ###################################################################### *)
(** ** Programs: Adding Products, Sums, and the Empty Type *)

(** FULL: Next we extend our programming language to have pairs and variants.

    A _pair_ is just like the two-element pairs we've previously used in Rocq,
    e.g., [(1, true)]. Each component of the pair has a potentially different
    type. The type of a pair is a [product]. Informally, we write a product
    type as [t1 * t2]. We introduce _projection_ functions [fst] and [snd] to
    return the first and second components of pairs.

    A _variant_ is like the following Rocq type:

[[
        Inductive sum (T1 T2 : Type) :=
        | inl : T1 -> sum T1 T2
        | inr : T2 -> sum T1 T2.
]]

    That is, it has two constructors named [inl] and [inr]. These are so-called
    _injection_ functions that take a single value and inject it into the [sum]
    type. The [l] and [r] stand for "left" and "right", i.e., whether the type
    is [T1] on the left of the sum, or [T2] on the right. A value of a sum type
    is thus a value of either type [T1] or [T2], along with a tag (the
    constructor) to say which type it came from. Informally we write a sum type
    as [T1 + T2].

    To make use of a [sum], we add a [case] expression, which says how to
    compute a result based on whether the value being examined is tagged with
    [inl] or [inr]. Informally, we notate it as

<<
        case e of (x1 : t1) => e1 | (x2 : t2) => e2 end
>>

    That is much like the following Rocq expression:

[[
        match e with (x1 : t1) => e1 | (x2 : t2) => e2 end
]]

    In fact we would happily use "match" as the name for it, but that word is
    reserved by Rocq. The type annotations are required for our [case]
    expression so that we can avoid any worries about type inference or
    reconstruction.

    We also take this opportunity to introduce a new type and expression that
    we will need much later on to complete the second of the main Curry-Howard
    theorems. We introduce the _empty_ type, which has no values. It
    corresponds to the [false] proposition.

    And, we introduce the [magic] program, where [magic t e] is "magically" an
    expression of type [t] as long as [e : empty] -- which of course is
    impossible, since there are no values of the [empty] type. The [magic]
    program somewhat resembles a type cast, except that type casts in some
    languages allow arbitrary casting without justification, whereas [magic] is
    justified by an impossible premise (a value of the empty type). *)

(* HIDE: We could have introduced [magic] earlier in the Implicational module,
   but it isn't needed to prove the forward direction (typability -> provability)
   of Curry-Howard. We will need it later in this module to prove the backward
   direction (provability -> typability). *)

(** TERSE: We extend the language with pairs, variants, and the empty type.

    - _Pairs_ combine two values; their type is a product [t1 * t2]. Projections
      [fst] and [snd] extract components.

    - _Variants_ represent a value of one of two types, written [t1 + t2],
      like this Rocq type:

<<
        Inductive sum (T1 T2 : Type) :=
        | inl : T1 -> sum T1 T2
        | inr : T2 -> sum T1 T2.
>>

      A [case] expression (like Rocq's [match]) analyzes them:

<<
        case e of (x1 : t1) => e1 | (x2 : t2) => e2 end
>>

    - The _empty type_ has no values and corresponds to [false]. The expression
      [magic t e] "magically" produces a value of type [t] from [e : empty].
      It is like an empty [match] expression in Rocq. *)

Inductive type :=
  | tvar (id : string)
  | arrow (t1 t2 : type)
  | product (t1 t2 : type)
  | sum (t1 t2 : type)
  | empty.

Inductive expr :=
  | var (id : string)
  | abs (id : string) (t : type) (e : expr)
  | app (e1 e2 : expr)
  | magic (t : type) (e : expr)
  | pair (e1 e2 : expr)
  | fst (e : expr)
  | snd (e : expr)
  | inl (e1 : expr)
  | inr (e2 : expr)
  | case (e : expr) (id1 : string) (t1 : type) (e1 : expr)
                    (id2 : string) (t2 : type) (e2 : expr).

(** The new type system rules are as follows: *)

(**
[[[
          E |- e : empty
        ------------------ (t-magic)
        E |- magic t e : t

        E |- e1 : t1    E |- e2 : t2
        ---------------------------- (t-pair)
        E |- pair e1 e2 : t1 * t2

        E |- e : t1 * t2
        ---------------- (t-fst)
        E |- fst e : t1

        E |- e : t1 * t2
        ---------------- (t-snd)
        E |- snd e : t2

              E |- e : t1
        -------------------- (t-inl)
        E |- inl e : t1 + t2

              E |- e : t2
        -------------------- (t-inr)
        E |- inr e : t1 + t2

        E |- e : t1 + t2   E, x1:t1 |- e1 : t   E, x2:t2 |- e2 : t
        ---------------------------------------------------------- (t-case)
        E |- case e of (x1 : t1) => e1 | (x2 : t2) => e2 end : t
]]]

*)

(** FULL: The new rules can be interpreted as follows:

    - T-Magic: if [e] has type [empty], then [magic t e] has type [t] for
      any [t]. That is, from an impossible value (one of type [empty]),
      we can produce a value of any type.

    - T-Pair: if [e1] has type [t1] and [e2] has type [t2], then the pair
      [pair e1 e2] has type [t1 * t2]. That is, a pair packages together
      two values, one of each type.

    - T-Fst: if [e] has type [t1 * t2], then [fst e] has type [t1].
      That is, from a pair, we can extract its first component.

    - T-Snd: if [e] has type [t1 * t2], then [snd e] has type [t2].
      That is, from a pair, we can extract its second component.

    - T-Inl: if [e] has type [t1], then [inl e] has type [t1 + t2] for
      any type [t2]. That is, we can inject a value into the left side
      of a sum type.

    - T-Inr: if [e] has type [t2], then [inr e] has type [t1 + t2] for
      any type [t1]. That is, we can inject a value into the right side
      of a sum type.

    - T-Case: if [e] has type [t1 + t2], and if assuming [x1 : t1] we can
      show that [e1] has type [t], and assuming [x2 : t2] we can show that
      [e2] has type [t], then the case expression has type [t]. That is,
      to use a value of sum type, we must consider both possibilities, one
      for each injection, and ensure that both branches produce the same
      type of result. *)

(** TERSE: The rules:

    - T-Magic: from an impossible value, produce a value of any type.
    - T-Pair: combine two values into a pair.
    - T-Fst: from a pair, obtain its first component.
    - T-Snd: from a pair, obtain its second component.
    - T-Inl: inject a value into the left side of a sum.
    - T-Inr: inject a value into the right side of a sum.
    - T-Case: to use a sum, consider both cases and produce the same type. *)

(** We formalize those as follows. *)

Definition tenv := list (string * type).

Inductive hastype : tenv -> expr -> type -> Prop :=
  (* The first three rules were part of our previous development. *)
  | t_var : forall E x t,
      In (x, t) E ->
      hastype E (var x) t
  | t_abs : forall E x t1 e t2,
      hastype ((x, t1) :: E) e t2 ->
      hastype E (abs x t1 e) (arrow t1 t2)
  | t_app : forall E e1 t1 t2 e2,
      hastype E e1 (arrow t1 t2) ->
      hastype E e2 t1 ->
      hastype E (app e1 e2) t2
  (* The next seven rules are new. *)
  | t_magic : forall E e t,
      hastype E e empty ->
      hastype E (magic t e) t
  | t_pair : forall E e1 e2 t1 t2,
      hastype E e1 t1 ->
      hastype E e2 t2 ->
      hastype E (pair e1 e2) (product t1 t2)
  | t_fst : forall E e t1 t2,
      hastype E e (product t1 t2) ->
      hastype E (fst e) t1
  | t_snd : forall E e t1 t2,
      hastype E e (product t1 t2) ->
      hastype E (snd e) t2
  | t_inl : forall E e t1 t2,
      hastype E e t1 ->
      hastype E (inl e) (sum t1 t2)
  | t_inr : forall E e t1 t2,
      hastype E e t2 ->
      hastype E (inr e) (sum t1 t2)
  | t_case : forall E e x1 t1 e1 x2 t2 e2 t,
      hastype E e (sum t1 t2) ->
      hastype ((x1, t1) :: E) e1 t ->
      hastype ((x2, t2) :: E) e2 t ->
      hastype E (case e x1 t1 e1 x2 t2 e2) t.

(* FULL *)
(* EX2 (swap_product) *)

(** Show that there exists a program that can swap products. *)

Theorem swap_product :
  forall (t1 t2 : type), exists (e : expr),
    hastype [] e (arrow (product t1 t2) (product t2 t1)).
Proof.
  (* ADMITTED *)
  intros t1 t2.
  exists (abs "p" (product t1 t2) (pair (snd (var "p")) (fst (var "p")))).
  apply t_abs. apply t_pair.
  - apply t_snd with t1. by_assumption.
  - apply t_fst with t2. by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: swap_product *)

(** [] *)

(* EX2 (swap_sum) *)

(** Show that there exists a program that can swap sums. *)

Theorem swap_sum :
  forall (t1 t2 : type), exists (e : expr),
    hastype [] e (arrow (sum t1 t2) (sum t2 t1)).
Proof.
  (* ADMITTED *)
  intros t1 t2.
  exists (abs "p" (sum t1 t2)
            (case (var "p") "x1" t1 (inr (var "x1"))
                            "x2" t2 (inl (var "x2")))).
  apply t_abs. apply t_case.
  - by_assumption.
  - apply t_inr. by_assumption.
  - apply t_inl. by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: swap_sum *)

(** [] *)

(* EX3 (product_of_sum__sum_of_product) *)

(** Show that there exists a program that can distribute a product over
    a sum. *)

Theorem product_of_sum__sum_of_product :
  forall (t1 t2 t3 : type), exists (e : expr),
    hastype [] e (arrow (product t1 (sum t2 t3))
                        (sum (product t1 t2) (product t1 t3))).
Proof. (* ADMITTED *)
  intros t1 t2 t3.
  exists
    (abs "p" (product t1 (sum t2 t3))
      (case (snd (var "p")) "x2" t2 (inl (pair (fst (var "p")) (var "x2")))
                            "x3" t3 (inr (pair (fst (var "p")) (var "x3"))))).
  apply t_abs. apply t_case.
  - apply t_snd with t1. by_assumption.
  - apply t_inl. apply t_pair.
    + apply t_fst with (sum t2 t3). by_assumption.
    + by_assumption.
  - apply t_inr. apply t_pair.
    + apply t_fst with (sum t2 t3). by_assumption.
    + by_assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: product_of_sum__sum_of_product *)

(** [] *)

(** *)

(* /FULL *)

(* ###################################################################### *)
(** ** Proving the Extended Correspondence *)

(** The new rules we've added are also in a correspondence:

    - [false_elim] corresponds to [t_magic].
    - [and_intro] corresponds to [t_pair].
    - [and_elim_L] corresponds to [t_fst].
    - [and_elim_R] corresponds to [t_snd].
    - [or_intro_L] corresponds to [t_inl].
    - [or_intro_R] corresponds to [t_inr].
    - [or_elim] corresponds to [t_case].

    And therefore there is an extended correspondence between logical connectives
    and programming language features:

    - (_Propositional variables_ correspond to _program variables_.)
    - (_Implication_ corresponds to _functions and application_.)
    - _False_ corresponds to the _empty type_.
    - _Conjunction_ corresponds to _pairs_.
    - _Disjunction_ corresponds to _variants_.

    *)

(** Now we can re-prove the first of the two main Curry-Howard theorems for our
    extended logic and programming language. First, we extend our conversion
    function to change products to conjunctions, and sums to disjunctions. *)

Fixpoint proposition_of_type (t : type) : proposition :=
  match t with
  | tvar x => atom x
  | arrow t1 t2 =>
    implies (proposition_of_type t1) (proposition_of_type t2)
  | product t1 t2 =>
    and (proposition_of_type t1) (proposition_of_type t2)
  | sum t1 t2 =>
    or (proposition_of_type t1) (proposition_of_type t2)
  | empty => false
  end.

Definition assumptions_of_tenv (E : tenv) : list proposition :=
  map proposition_of_type (map Datatypes.snd E).

(* EX3 (curry_howard_extended) *)

(** Derivation of typability for a program still yields a derivation of
    provability for a proposition. *)

(** FULL: Hint: the first three cases of the proof should go through with minimal
    changes from your previous version. The new cases should be similar in
    difficulty to the previous cases. *)

Theorem curry_howard_extended : forall E e t,
  hastype E e t ->
  provable (assumptions_of_tenv E) (proposition_of_type t).
Proof. (* ADMITTED *)
  intros E e t HT. induction HT.
  - apply axiom. unfold assumptions_of_tenv. apply Implicational.in_snd with x. apply H.
  - unfold assumptions_of_tenv in IHHT. simpl in IHHT.
    unfold assumptions_of_tenv. simpl.
    apply implies_intro. apply IHHT.
  - apply implies_elim with (proposition_of_type t1).
    + simpl in IHHT1. apply IHHT1.
    + apply IHHT2.
  - apply false_elim. simpl in IHHT. apply IHHT.
  - simpl. apply and_intro.
    + apply IHHT1.
    + apply IHHT2.
  - simpl in IHHT. apply and_elim_L with (proposition_of_type t2). apply IHHT.
  - simpl in IHHT. apply and_elim_R with (proposition_of_type t1). apply IHHT.
  - simpl. apply or_intro_L. apply IHHT.
  - simpl. apply or_intro_R. apply IHHT.
  - unfold assumptions_of_tenv in IHHT2, IHHT3. simpl in IHHT1, IHHT2, IHHT3.
    apply (or_elim _ (proposition_of_type t1) (proposition_of_type t2) (proposition_of_type t)).
    + apply IHHT2.
    + apply IHHT3.
    + apply IHHT1.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: curry_howard_extended *)

(** [] *)

(* ###################################################################### *)
(** * The Second Main Theorem of the Correspondence (Advanced) *)

(** FULL: So far, we have shown that if [E |- e : t] then [E |- t] after applying
    appropriate conversion functions to [E] and [t]. That is, a derivation of
    typability for a program also yields a derivation of provability for a
    proposition.

    What about the converse direction? Could we get a derivation of
    typability from a derivation of provability? The answer is yes -- but it
    takes more work. The reason for that is that in the original direction we
    could erase information (the programs) from the derivations to do the
    conversion. In this new direction, we have to _synthesize_ the missing
    programs. *)

(** TERSE: So far: if a program is well-typed, its type-as-a-proposition is
    provable.

    Conversely: if a proposition is provable, there exists a well-typed
    program of that proposition-as-a-type.

    The forward direction erases programs; the converse must synthesize them. *)

(** First, we define a function that converts a proposition to a string
    representation. *)

Fixpoint string_of_proposition (p : proposition) : string :=
  match p with
  | atom id => "(" ++ id ++ ")"
  | implies p q =>
    "(implies " ++ (string_of_proposition p) ++ " "
                ++ (string_of_proposition q) ++ ")"
  | and p q =>
    "(and " ++ (string_of_proposition p) ++ " "
            ++ (string_of_proposition q) ++ ")"
  | or p q =>
    "(or " ++ (string_of_proposition p) ++ " "
           ++ (string_of_proposition q) ++ ")"
  | false => "(false)"
  end.

(** Second, we define a function that converts a proposition to
    its equivalent type. *)

Fixpoint type_of_proposition (p : proposition) : type :=
  match p with
  | atom id => tvar id
  | implies p q => arrow (type_of_proposition p) (type_of_proposition q)
  | and p q => product (type_of_proposition p) (type_of_proposition q)
  | or p q => sum (type_of_proposition p) (type_of_proposition q)
  | false => empty
  end.

(** Third, we define a function to convert assumptions to a type
    environment. Each assumption gets a name, which is its conversion
    to a string. *)

Definition tenv_of_assumptions (A : list proposition) : tenv :=
  map (fun p => (string_of_proposition p, type_of_proposition p)) A.

(** Now we're ready for the second of the main Curry-Howard theorems. *)

(* EX4A (curry_howard_converse) *)

(** Prove that if a proposition is provable, then there is a well-typed
    program whose type corresponds to that proposition. *)

(** FULL: Hint: proceed by induction on the evidence that [p] is provable.
    In the (many) inductive cases, use the inductive hypotheses to
    derive the existence of some subexpressions, then assemble those
    into an expression with the required type. *)

Theorem curry_howard_converse : forall A p,
  provable A p ->
  exists e, hastype (tenv_of_assumptions A) e (type_of_proposition p).
Proof. (* ADMITTED *)
  intros A p H. induction H.
  - exists (var (string_of_proposition p)). apply t_var.
    induction A.
    + inversion H.
    + inversion H.
      * simpl. left. rewrite H0. reflexivity.
      * simpl. right. apply IHA. apply H0.
  - simpl. destruct IHprovable as [e He].
    exists (abs (string_of_proposition p) (type_of_proposition p) e).
    apply t_abs. simpl in He. apply He.
  - simpl in IHprovable1. destruct IHprovable1 as [f Hf].
    destruct IHprovable2 as [x Hx].
    exists (app f x). apply t_app with (type_of_proposition p).
    + apply Hf.
    + apply Hx.
  - simpl in IHprovable. destruct IHprovable as [e He].
    exists (magic (type_of_proposition p) e).
    apply t_magic. apply He.
  - simpl. destruct IHprovable1 as [e1 He1]. destruct IHprovable2 as [e2 He2].
    exists (pair e1 e2). apply t_pair.
    + apply He1.
    + apply He2.
  - simpl in IHprovable. destruct IHprovable as [e He].
    exists (fst e). apply t_fst with (type_of_proposition q). apply He.
  - simpl in IHprovable. destruct IHprovable as [e He].
    exists (snd e). apply t_snd with (type_of_proposition p). apply He.
  - simpl. destruct IHprovable as [e He]. exists (inl e).
    apply t_inl. apply He.
  - simpl. destruct IHprovable as [e He]. exists (inr e).
    apply t_inr. apply He.
  - simpl. destruct IHprovable1 as [e1 He1]. destruct IHprovable2 as [e2 He2].
    destruct IHprovable3 as [e He].
    exists (case e (string_of_proposition p) (type_of_proposition p) e1
                   (string_of_proposition q) (type_of_proposition q) e2).
    apply t_case.
    + apply He.
    + simpl in He1. apply He1.
    + simpl in He2. apply He2.
Qed.
(* /ADMITTED *)

(** [] *)

End Propositional.

(* ###################################################################### *)
(** * Further Extensions *)

(** FULL: The Curry–Howard correspondence extends far beyond the systems we have
    studied in this chapter. What we have seen here is just the beginning of a
    much richer connection between logic and programming.

    Many other logical constructs correspond to programming language features,
    including:

    - _Classical axioms_, which correspond to _control flow operators_
      (e.g., mechanisms related to exceptions and non-local jumps).

    - _First-order universal quantification_, which corresponds to
      _dependent types_, where types may depend on values.

    - _First-order existential quantification_, which corresponds to
      _abstract types_, which hide implementation details.

    - _Second-order propositional quantification_, which corresponds to
      _polymorphism_, where programs can be written generically over types.

    These correspondences are not just curiosities: they form the foundation
    of modern type systems, proof assistants, and techniques for building
    reliable software. The same ideas you have seen here reappear in the
    design of programming languages, in the verification of critical systems,
    and in ongoing research at the boundary of logic and computation.

    See \CITE{Sørensen and Urzyczyn 2006} for a deeper exploration. *)

(** TERSE: The Curry–Howard correspondence extends far beyond this chapter.

    - Classical axioms ↔ control flow (e.g., exceptions)
    - Universal quantification ↔ dependent types
    - Existential quantification ↔ abstract types
    - Second-order quantification ↔ polymorphism

    These ideas underlie modern type systems, proof assistants, and
    program verification. *)
