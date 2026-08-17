(** * Review1: Review Session for First Midterm *)

(* HIDE: This file is not included in the SF book as it appears on the
   web -- it is only for the "terse" version.  It is mainly intended
   for the CIS5000 course at Penn, but others are welcome to use it
   too. *)
(* HIDEFROMHTML *)
Require Export IndPrinciples.
(* /HIDEFROMHTML *)

(* ###################################################################### *)
(** * General Notes *)

(** *** Standard vs. Advanced Exams *)

(** - Unlike the homework assignments, we will make up two 
      separate versions of the exam -- a "standard exam" and an
      "advanced exam."  They will share some problems, but there will
      be problems on each that are not on the other.

      You can choose to take whichever one you want at the beginning
      of the exam period.
*)

(** *** Grading *)

(** - Meaning of grades:
        - A = mastery of all or almost all of the material
        - B = good understanding of most of the material, perhaps with
          a few gaps
        - C = some understanding of most of the material, with
          substantial gaps
        - D = major gaps
        - F = didn't show up / try

    - There is no predetermined curve.  We'd be perfectly delighted
      to give everyone an A (for the exam, and later for the course).
        - Exception: A+ grades will be given only for completing the
          advanced track.

    - Standard and advanced exams will be graded relative to different
      expectations (i.e., "the material" is different)
*)

(** *** Hints *)

(**
    - On each version of the exam, will be at least one problem taken
      more or less verbatim from a homework assignment.

    - On the advanced version, there will be an informal proof.
*)


(* ###################################################################### *)
(** * Expressions and Their Types *)
(* SOONER: Not certain that it's helpful to divide the problems into
   sections like this... *)

(** Thinking about well-typed expressions and their types is a great
    way of reviewing many aspects of how Coq works...

*)

(* QUIZ *)
(** What is the type of the following expression?
[[
      fun x:nat => x :: []
]]

    (A) [nat]

    (B) [list nat]

    (C) [nat -> list X]

    (D) [nat -> list nat]

    (E) [nat -> nat]

    (6) Not typeable

    (N.b.: On an actual exam, this might not be multiple choice!)

*)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of the following expression?
[[
      ((2 :: 3 :: []) :: []) :: []
]]

    (A) [nat]

    (B) [list list]

    (C) [list nat]

    (D) [list (list nat)]

    (E) [list (list (list nat))]

    (6) Not typeable

*)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of the following expression?
[[
      fun (X Y Z : Type)
          (f : X -> Y)
          (g : Y -> Z)
          (a : X) =>
         g (f a)
]]

    (A) [Z]

    (B) [forall Z : Type, Z]

    (C) [forall X Y Z : Type, (X -> Y) -> (Y -> Z) -> X -> Z]

    (D) [forall X Y Z : Type, (X -> Y) -> (Y -> Z) -> X -> Y]

    (E) [forall X Y Z : Type, X -> Y -> Z]

    (6) [forall X Y Z : Type, X -> Z]

    (7) Not typeable

*)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of the following expression?
[[
      forall x:nat, x + 3 = 1 + x + 2
]]

    (A) [nat]

    (B) [nat -> nat]

    (C) [nat -> Prop]

    (D) [Prop]

    (E) [Type]

    (6) [True]

    (7) Not typeable

*)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of the following expression?
[[
      fun x:nat => x + 3 = 1 + x + 2
]]

    (A) [nat]

    (B) [nat -> nat]

    (C) [nat -> Prop]

    (D) [forall x:nat, x + 3 = 1 + x + 2]

    (E) [Type]

    (6) Not typeable

*)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of the following expression?
[[
      exists x:nat, x + x = 5
]]

    (A) [False]

    (B) [Prop]

    (C) [nat -> Prop]

    (D) [forall x:nat, x + x = 5]

    (E) [Type]

    (6) Not typeable

*)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of the following expression?
[[
      nat -> list nat
]]

    (A) [Type]

    (B) [nat -> list nat]

    (C) [list nat]

    (D) [forall x:nat, list nat]

    (E) [nat]

    (6) Not typeable

*)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of the following expression?
[[
      forall x:nat, eqb_nat x x
]]

    (A) [Type]

    (B) [nat -> list nat]

    (C) [list nat]

    (D) [forall x:nat, list nat]

    (E) [forall x:nat, Prop]

    (6) [Prop]

    (7) Not typeable

*)
(* /QUIZ *)

(* QUIZ *)
(** Recall the inductively defined proposition
[[
    Inductive le : nat -> nat -> Prop :=
      | le_n : forall n, le n n
      | le_S : forall n m, (le n m) -> (le n (S m)).
]]
    What is the type of the following expression?
[[
      forall x:nat, le x x
]]

    (A) [Prop]

    (B) [nat -> Prop]

    (C) [fun x:nat => le x x]

    (D) [forall x:nat, le x x]

    (E) [True]

    (6) Not typeable

*)
(* /QUIZ *)

(* QUIZ *)
(** Recall the inductively defined proposition
[[
    Inductive le : nat -> nat -> Prop :=
      | le_n : forall n, le n n
      | le_S : forall n m, (le n m) -> (le n (S m)).
]]
    What is the type of the following expression?
[[
      le 5
]]

    (A) [Prop]

    (B) [nat -> Prop]

    (C) [nat -> nat -> Prop]

    (D) [forall x:nat, le 5 x]

    (E) [True]

    (6) [False]

    (7) Not typeable

*)
(* /QUIZ *)

(* QUIZ *)
(** Recall the inductively defined proposition
[[
    Inductive le : nat -> nat -> Prop :=
      | le_n : forall n, le n n
      | le_S : forall n m, (le n m) -> (le n (S m)).
]]
    What is the type of the following expression?
[[
      le_S 5
]]

    (A) [Prop]

    (B) [nat -> Prop]

    (C) [forall m:nat, le 5 m]

    (D) [le 5 -> le (S 5)]

    (E) [forall m:nat, (le 5 m) -> le 5 (S m)]

    (6) Not typeable

*)
(* /QUIZ *)

(* QUIZ *)
(** Recall the inductively defined proposition
[[
    Inductive le : nat -> nat -> Prop :=
      | le_n : forall n, le n n
      | le_S : forall n m, (le n m) -> (le n (S m)).
]]
    What is the type of the following expression?
[[
      le_n 5 5
]]

    (A) [Prop]

    (B) [nat -> Prop]

    (C) [forall m:nat, le 5 m]

    (D) [le 5 -> le (S 5)]

    (E) [forall m:nat, (le 5 m) -> le 5 (S m)]

    (6) [le 5 5]

    (7) Not typeable

*)
(* /QUIZ *)

(** (Discussion of Coq's view of the universe...) #<br><br><br><br><br><br><br># *)

(* QUIZ *)
(** Recall the inductively defined proposition
[[
    Inductive or (P Q : Prop) : Prop :=
        | or_introl : P -> or P Q
        | or_intror : Q -> or P Q.
]]
    What is the type of the following expression?
[[
      or_introl True
]]

    (A) [Prop]

    (B) [bool -> Prop]

    (C) [forall Q: Prop, or True Q]

    (D) [forall Q: Prop, Q]

    (E) [forall Q: Prop, True -> or True Q]

    (6) [forall Q: Prop, Q -> True]

    (7) Not typeable

*)
(* /QUIZ *)

(* QUIZ *)
(** Recall the inductively defined proposition
[[
    Inductive or (P Q : Prop) : Prop :=
        | or_introl : P -> or P Q
        | or_intror : Q -> or P Q.
]]
    What is the type of the following expression?
[[
      or_intror False True
]]

    (A) [Prop]

    (B) [bool -> bool -> Prop]

    (C) [True -> or False True]

    (D) [Prop, or False True]

    (E) [forall Q: Prop, or True False]

    (6) [forall Q: Prop, False -> or True False]

    (7) Not typeable

*)
(* /QUIZ *)

(* HIDE *)
(* QUIZ *)
(** Recall the inductively defined proposition
[[
    Inductive or (P Q : Prop) : Prop :=
        | or_introl : P -> or P Q
        | or_intror : Q -> or P Q.
]]
    What is the type of the following expression?
[[
      or_intror True Q
]]

    (A) [Prop]

    (B) [bool -> Prop]

    (C) [forall Q: Prop, or True Q]

    (D) [forall Q: Prop, Q]

    (E) [forall Q: Prop, True -> or True Q]

    (6) [forall Q: Prop, Q -> True]

    (7) Not typeable

*)
(* /QUIZ *)
(* /HIDE *)

(* QUIZ *)
(** Recall the inductively defined proposition
[[
    Inductive and (P Q : Prop) : Prop :=
       conj : P -> Q -> (and P Q).
]]
    What is the type of the following expression?
[[
      conj
]]

    (A) [Prop]

    (B) [bool -> bool]

    (C) [forall P Q : Prop, P -> Q -> and P Q]

    (D) [P -> Q -> and P Q]

    (E) [Prop -> Prop -> Prop]

    (6) Not typeable

*)
(* /QUIZ *)

(* HIDE *)
(* QUIZ *)
(** Recall the inductively defined propositions
[[
    Inductive and (P Q : Prop) : Prop :=
       conj : P -> Q -> (and P Q).
]]
and
[[
    Inductive eq (X:Type) : X -> X -> Prop :=
       refl_equal : forall x, eq X x x.
]]
    What is the type of the following expression?
[[
      conj (eq _ 2 (0+2)) (eq nat 1 2) (refl_equal _ 2)
]]

    (A) [Prop]

    (B) [eq nat 1 2]

    (C) [forall X : Type, eq X 1 2 -> and (eq X 2 (0 + 2))  (eq X 1 2)]

    (D) [eq nat 1 2 -> and (eq nat 2 (0 + 2)) (eq nat 1 2]

    (E) [eq _ 1 2 -> and (eq _ 2 (0 + 2)) (eq _ 1 2)]

    (6) [forall P : Prop, P -> and (eq X 2 (0 + 2)) P ]

    (7) Not typeable

*)
(* /QUIZ *)
(* /HIDE *)

(* QUIZ *)
(** The [appears_in] relation expresses that an element [a]
    appears in a list [l].
[[
  Inductive appears_in (X:Type) (a:X)
                     : list X -> Prop :=
  | ai_here : forall l,
       appears_in X a (a::l)
  | ai_later : forall b l,
       appears_in X a l ->
       appears_in X a (b::l).
]]
Complete the definition of the following proof object:
[[
  Definition appears_example :
     forall x y : nat, appears_in nat 4 [x;4;y] :=
]]

*)
(* /QUIZ *)
(* HIDE *)
(**  fun (x y : nat) => ai_later nat 4 x [4;y] (ai_here nat 4 [y]). *)
(* /HIDE *)

(* QUIZ *)
(** Write an expression of the following type:
[[
(nat -> False) -> False
]]
*)
(* /QUIZ *)


(* QUIZ *)
(** Write an expression of the following type:
[[
 forall (A:Prop) , (A -> False) -> A -> False
]]
*)
(* /QUIZ *)


(* QUIZ *)
(* SOONER: Need to remind them of the definition of True for this, right? *)
(** Write an expression of the following type:
[[
forall (A:Prop),
  (A -> False) ->
  (A -> True) ->
  A ->
  False /\ True
]]
*)
(* /QUIZ *)


(* QUIZ *)
(** Write an expression of the following type:
[[
forall A:Prop, A -> A -> A
]]
*)
(* /QUIZ *)

(* HIDE *)
(** # <center><img src="../images/TypingOverview.svg"></center> # *)
(* /HIDE *)

(* ###################################################################### *)
(** * Inductive Definitions *)

(* QUIZ *)
(** Recall that a list [l3] is an ``in-order merge'' of lists [l1] and
[l2] if it contains all the elements of [l1], in the same order as
[l1], and all the elements of [l2], in the same order as
[l2], with elements from [l1] and [l2] interleaved in any
order.  For example, the following lists (among others) are in-order
merges of [[1;2;3]] and [[4;5]]:
[[
    [1;2;3;4;5]
    [4;5;1;2;3]
    [1;4;2;5;3]
]]
Complete the following inductively defined relation in such a way that
[merge l1 l2 l3] is provable exactly when [l3] is an in-order
merge of [l1] and [l2].

[[
Inductive merge {X:Type}
    : list X -> list X -> list X -> Prop :=
]]
*)

(* /QUIZ *)

(* ###################################################################### *)
(** * Tactics *)

(* QUIZ *)
(** When is the [generalize dependent] tactic useful?

(Briefly explain.) *)

(* /QUIZ *)

(* QUIZ *)
(** What is the difference between [apply] and [apply ... in]?

(Briefly explain.) *)

(* /QUIZ *)

(* QUIZ *)
(** To prove the following proposition, which tactics will we need
    besides [intros] and [reflexivity]?
[[
    forall n:nat, 2 * n = n + n
]]

    (A) [simpl], and [rewrite -> plus_0_r]

    (B) [induction], [simpl] and [rewrite -> plus_0_r]

    (C) [destruct], and [rewrite -> plus_0_r]

    (D) only [rewrite -> plus_0_r]

    (E) only [induction]

    (6) none of the above

*)
(* /QUIZ *)
(* HIDE *)
Theorem mult_2_l_rev : forall n:nat, 2 * n = n + n.
Proof.
  (* ADMITTED *)
  intros n. simpl. rewrite -> plus_0_r.
  reflexivity.  Qed.
(* /ADMITTED *)
(* /HIDE *)

(* HIDE *)
(** HIDE: This seems too involved. *)
(* QUIZ *)
(** What about this one?
[[
  forall n m p : nat,
    n + (m + p) = m + (n + p)
]]

    (A) [simpl], [rewrite -> plus_assoc], and
        [rewrite -> plus_comm]

    (B) [induction], [simpl], [rewrite -> plus_assoc], and

    [rewrite -> plus_comm]

    (C) [destruct], [rewrite -> plus_assoc], and
        [rewrite -> plus_comm]

    (D) only [rewrite -> plus_assoc], and
        [rewrite -> plus_comm]

    (E) only [induction]

    (6) none of the above

*)
(* /QUIZ *)
Theorem plus_swap_rev : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* ADMITTED *)
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n).
  { rewrite <- plus_comm. reflexivity. }
  rewrite -> H. rewrite -> plus_assoc. reflexivity.  Qed.
(* /ADMITTED *)
(* /HIDE *)

(* QUIZ *)
(** To prove the following proposition, which tactics will we need
    besides [intros], [rewrite], and [reflexivity]?
[[
   forall n m p : nat,
     leb n m = true ->
     leb (p + n) (p + m) = true.
]]

    (A) only [simpl]

    (B) [simpl], [destruct p] and [induction n]

    (C) [simpl], and [destruct n]

    (D) [simpl], and [induction p]

    (E) [simpl], and [induction n]

    (6) none of the above

*)
(* /QUIZ *)
(* HIDE *)
Theorem plus_leb_compat_l_rev : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  (* ADMITTED *)
  intros n m p. induction p as [| p'].
  - (* p = 0 *)
    intros H.
    simpl. rewrite -> H. reflexivity.
  - (* p = S p' *)
    intros H.
    simpl. rewrite -> IHp'. reflexivity.
    rewrite -> H. reflexivity.  Qed.
(* /ADMITTED *)
(* /HIDE *)

(* QUIZ *)
(** To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?
[[
forall P Q R: Prop, P -> (P \/ Q) /\ (R \/ P).
]]

    (A) [split], [inversion], [left], and [right]

    (B) [inversion], [left], and [right]

    (C) [inversion] and one of [left] and [right]

    (D) [split], [left], and [right]

    (E) only [right]

    (6) none of the above

*)
(* /QUIZ *)
(* HIDE *)
Theorem foo : forall P Q R: Prop, P -> (P \/ Q) /\ (R \/ P).
Proof.
  (* ADMITTED *)
  intros P Q R H.
  split. left. apply H.
  right. apply H. Qed.
(* /ADMITTED *)
(* /HIDE *)


(* ###################################################################### *)
(** * Functional Programming *)

(* QUIZ *)
(** Recall the definition of [override]:
[[
  Definition override {X} (f : nat -> X) (k1 : nat) (v : X) (k2 : nat) :=
    if eqb_nat k1 k2 then v else f k2.
]]

   Consider the definition of the following function:

[[
  Fixpoint foo {X} (l : list (nat * X)) (x : X) :=
    match l with
    | [] => fun m : nat => x
    | (n, v) :: l' => override (foo l' x) n v
    end.
]]

   What does [foo [(1,3), (3,4)] 20 43] evaluate to?

   (A) 1

   (B) 3

   (C) 4

   (D) 20

   (E) 43

*)
(* /QUIZ *)

(* QUIZ *)
(** Recall the definition of [override]:
[[
  Definition override {X} (f : nat -> X) (k1 : nat) (v : X) (k2 : nat) :=
    if eqb_nat k1 k2 then v else f k2.
]]

   Consider the definition of the following function:

[[
  Fixpoint foo {X} (l : list (nat * X)) (x : X) :=
    match l with
    | [] => fun m : nat => x
    | (n, v) :: l' => override (foo l' x) n v
    end.
]]

   What does [foo [(1,3), (1,4)] 20 1] evaluate to?

   (A) 1

   (B) 3

   (C) 4

   (D) 20

   (E) 43

*)
(* /QUIZ *)

(* HIDE *)
(* QUIZ *)
(** Consider the following datatype:
[[
  Inductive unit :=
  | tt : unit.
]]

    How many elements of type [nat -> unit] are there?

    (A) 0

    (B) 1

    (C) 2

    (D) 3

    (E) Infinitely many
*)
(* /QUIZ *)
(* /HIDE *)

(* HIDE *)
(* QUIZ *)
(** Consider the following datatype:
[[
  Inductive unit :=
  | tt : unit.
]]

    How many elements of type [unit -> nat] are there?

    (A) 0

    (B) 1

    (C) 2

    (D) 3

    (E) Infinitely many
*)
(* /QUIZ *)
(* /HIDE *)

(* QUIZ *)
(** Recall the definition of [fold]:
[[
  Fixpoint fold {X Y}
                (f : X -> Y -> Y)
                (y : Y)
                (l : list X) :=
    match l with
    | [] => y
    | x :: xs => f x (fold f y xs)
    end
]]

    Consider now the following function:

[[
    fun X (l : list X) (x : X) => fold cons [x] l
]]

    Which of these functions does the same thing as the previous one?

    (A) [rev]

    (B) [cons]

    (C) [snoc]

    (D) [map]

    (E) [app]

*)

(* /QUIZ *)


(* ###################################################################### *)
(** * Judging Propositions *)

(* QUIZ *)
(** Recall the definition of [map]:
[[
  Fixpoint map {X Y} (f : X -> Y) (l : list X) :=
    match l with
    | [] => []
    | x :: xs => f x :: map f xs
    end.
]]
    Is the following proposition provable?
[[
  Theorem map_comp : forall X Y Z (f : X -> Y) (g : Y -> Z) l,
    map (fun x => g (f x)) l = map g (map f l)
]]

    (A) Yes

    (B) No
*)
(* /QUIZ *)

(* QUIZ *)
(** Recall the definition of [rev]:
[[
  Fixpoint rev {X} (l : list X) :=
    match l with
    | [] => []
    | x :: xs => snoc (rev xs) x
    end.
]]
    Is the following proposition provable?
[[
  Theorem t1 : forall X (l1 l2 : list X),
    rev (l1 ++ l2) = rev l1 ++ rev l2.
]]

    (A) Yes

    (B) No
*)
(* /QUIZ *)

(* QUIZ *)
(** Is the following proposition provable?
[[
  True = False
]]

  (A) Yes

  (B) No
*)
(* /QUIZ *)

(* QUIZ *)
(** Recall the definition of [fold]:
[[
  Fixpoint fold {X Y : Type}
                (f : X -> Y -> Y)
                (y : Y)
                (l : list X) :=
    match l with
    | [] => y
    | x :: xs => f x (fold f y xs)
    end
]]

    Is the following proposition provable?

[[
  Theorem foo : forall X (l : list (list X)),
    fold (fun a b => b ++ rev a) [] l =
    rev (fold (fun a b => a ++ b) [] l).
]]

    (A) Yes

    (B) No
*)
(* /QUIZ *)

(* ###################################################################### *)
(** * More Type Checking*)

(* QUIZ *)
(** Consider the following inductive definition:
[[
  Inductive R : nat -> list nat -> Prop :=
  | c1 : R 0 []
  | c2 : forall n h l, R n l -> R (S n) (h :: l).
]]
    Which of the following propositions is not provable?

    (A) [R 2 [1,0]]

    (B) [R 0 []]

    (C) [R 10 [1,2,1,0]]

    (D) [R 4 [3,2,1,0]]
*)
(* /QUIZ *)
(* HIDE *)
(** Solution: (C) [R 10 [1,2,1,0]] *)
(* /HIDE *)

(* QUIZ *)
(** Consider the following inductive definition:
[[
  Inductive R : nat -> list nat -> Prop :=
  | c1 : R 0 []
  | c2 : forall n l h, R n l -> R (S n) (h :: l)
  | c3 : forall n l, R n l -> R (S n) l.
]]
    Which of the following propositions is not provable?

    (A) [R 2 [1,0]]

    (B) [R 0 []]

    (C) [R 10 [1,2,1,0]]

    (D) [R 3 [3,2,1,0]]
*)
(* /QUIZ *)
(* HIDE *)
(** Solution: (D) [R 3 [3,2,1,0]] *)
(* /HIDE *)



(* QUIZ *)
(** Consider the following inductive definition:
[[
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l h, R n l -> R (S n) (h :: l)
      | c3 : forall n l, R (S n) l -> R n l.
]]
   Which of the following propositions is not provable?

    (A) [R 2 [1,0]]

    (B) [R 0 []]

    (C) [R 10 [1,2,1,0]]

    (D) [R 3 [3,2,1,0]]
*)
(* /QUIZ *)
(* HIDE *)
(** Solution: (C) [R 10 [1,2,1,0]] *)
(* /HIDE *)


(* QUIZ *)
(** Consider the following inductive definition:
[[
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
]]
    Which of the following propositions is not provable?

    (A) [R 2 [1,0]]

    (B) [R 1 [1,2,1,0]]

    (C) [R 3 [3,0,1,0]]

    (D) [R 1 [3,2,1,0]]

*)
(* /QUIZ *)
(* HIDE *)
(** Solution: (C) [R 3 [3,0,1,0]] *)
(* /HIDE *)

(** Good luck on the exam! *)

(* HIDEFROMHTML *)
(* $Date$ *)
(* /HIDEFROMHTML *)
