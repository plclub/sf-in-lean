Require Import String.
Require Import Bool.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Inductive aexp : Type :=
  | ANum (n : nat)        (* Constant *)
  | AId (x : string)      (* Variable *)
  | APlus (a1 a2 : aexp)  (* + *)
  | AMinus (a1 a2 : aexp) (* - *)
  | AMult (a1 a2 : aexp). (* * *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Notation "[[ e ]]" := e (e custom com at level 10).
Notation "( x )" := x (in custom com, x at level 10).
(* BCP: After the next two declarations, doing "check true" at the top
   level fails.  I think this is because true has become a keyword for
   the parser, not an identifier; maybe it would help to add explicit
   notations for true and false to the global grammar as well as
   com... *)
Notation "'true'"  := (BTrue) (in custom com at level 0).
Notation "'false'"  := (BFalse) (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 5, no associativity).
Notation "x = y"  := (BEq x y) (in custom com at level 5, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 4, left associativity).
Notation "'~' b"  := (BNot b) (in custom com at level 3, right associativity).
Notation "x + y" := (APlus x y) (in custom com at level 2, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 2, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 1, left associativity).
Notation "x" := x (in custom com at level 0, x constr at level 0).

Definition X : string := "X".

Check [[ 1 + 2 ]].
Check [[ 2 = 1 ]].
Check [[ X = 1 ]].
Check ([[ X ]] : aexp).

Definition five := 5.
Check [[ 5 + five ]].

(* BCP: This allows us to embed arbitrary Rocq terms in com, but I'm
   not actually sure it's needed, given that we can embed
   applications... *)
Notation "[[ e ]]" := e (in custom com, e constr).
Definition plus2 n := S (S n).
Check [[ [[plus2 2]] = 1 ]].

(* By the way, I expected this to work, by analogy with the above, but
   it didn't: "Syntax error: 'Fields' or 'Rings' or 'Firstorder'
   'Solver' expected after 'Print' (in [vernac:command])." *)
(* Print [[ [[plus2 2]] = 1 ]]. *)

(* ----------------------------------------------------------------- *)

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'"  :=
  (CSkip)
    (in custom com at level 0).
Notation "x :=  y" :=
  (CAss x y)
    (in custom com at level 0, x custom string at level 0,
     y custom com at level 2, no associativity).
Notation "x ; y" :=
  (CSeq x y) (in custom com at level 10, right associativity).
Notation "'if' x 'then' y 'else' z 'endif'" :=
  (CIf x y z)
    (in custom com at level 10, right associativity, x custom com at level 0).
Notation "'while' x 'do' y 'end'" :=
  (CWhile x y)
    (in custom com at level 10, right associativity, x custom com at level 0).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Check [[ skip ]].
Check [[ (skip ; skip) ; skip ]].
Check [[ Z := X ]].

(* Is this a good way to get multiple function arguments??  Surely
   there is something more elegant / general... *)
Notation "x y" := (x y) (in custom com at level 0, x constr at level 0).
Notation "x y z" := (x y z) (in custom com at level 1, x constr at level 1).
Notation "x y z w" := (x y z w) (in custom com at level 2, x constr at level 2).

Definition func (c : com) : com :=
  [[ c ; skip ]].
Definition func2 (c1 c2 : com) : com :=
  [[ c1 ; c2 ]].

Check [[ skip ; func skip ]].
Check [[ skip ; func2 skip skip ]].

Definition fact_in_coq : com :=
  [[ Z := X;
     Y := 1;
     while ~(Z = 0) do
       Y := Y * Z;
       Z := Z - 1
     end ]].

(* BCP: I think we have to use ANum and AId explicitly here... *)
Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | [[ a1 + a2 ]] =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => [[ a1' + a2' ]]
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => [[ a1' - a2' ]]
    end
  | AMult a1 a2  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => [[ a1' * a2' ]]
    end
  end.

(* BCP: Stopped here... *)
Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then BTrue else BFalse
      | (a1', a2') =>
          BEq a1' a2'
      end
  | BLe a1 a2  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then BTrue else BFalse
      | (a1', a2') =>
          BLe a1' a2'
      end
  | BNot b1  =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2  =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | [[ skip ]] =>
      [[ skip ]]
  | [[ x := a ]] =>
      [[ x := fold_constants_aexp a ]]
  | [[ c1 ; c2 ]]  =>
      [[ [[fold_constants_com c1]] ;; [[fold_constants_com c2]] ]]
  | if b then c1 else c2 endif =>
      match fold_constants_bexp b with
      | BTrue  => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => TEST b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | while b do c END =>
      match fold_constants_bexp b with
      | BTrue => while BTrue do skip END
      | BFalse => skip
      | b' => while b' do (fold_constants_com c) END
      end
  end.

