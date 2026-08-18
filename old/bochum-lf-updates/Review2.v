WHI(** * Review2: Review Session for Second Midterm *)

(* HIDE: This file is not included in the SF book as it appears on the
   web -- it is only for the "terse" version.  It is mainly intended
   for the CIS5000 course at Penn, but others are welcome to use it
   too. *)
(* HIDEFROMHTML *)
Require Export Hoare2.
(* /HIDEFROMHTML *)

(* ###################################################################### *)
(** * General Notes *)

(** *** Hints *)

(**
    - On each version of the exam, there will be at least one problem
      taken more or less verbatim from a homework assignment.

    - Both versions will include one or more decorated programs.

    - On the advanced version, there will be an informal proof.

    - This set of review questions is biased toward ones that can be
      discussed in class / using clickers, so it doesn't fully
      represent the range of questions that might show up on the exam.

      Make sure to have a look at some prior exams to get a sense of
      some other sorts of questions you might see.
*)


(* ###################################################################### *)
(** * Definitions *)

(* QUIZ *)
(** On a piece of paper, write down the precise definition of what it
    means to say that two Imp programs are _equivalent_. *)
(* /QUIZ *)

(* QUIZ *)
(** On a piece of paper, write down precisely what it means to say
    that a Hoare triple is _valid_. *)
(* /QUIZ *)

(* QUIZ *)
(** In the [Hoare] chapter, we used the notation [bassn b] to "lift a
    boolean expression into an assertion."  Briefly explain what this
    means and why it's needed.  *)
(* /QUIZ *)

(* ###################################################################### *)
(** * IMP Program Equivalence  *)

(* QUIZ *)
(** Are the two following programs equivalent?
[[
X::= Y+1
Y::= X-1
]]

[[
X::= Y+1
]]

    (A) yes

    (B) no (and give a counterexample)

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   yes
*)
(* /QUIETSOLUTION *)

(* QUIZ *)
(** Are the two following programs equivalent?
[[
X::= Y-1
Y::= X+1
]]

[[
X::= Y-1
]]

    (A) yes

    (B) no (and give a counterexample)

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   no, they are not equivalent. E.g.:
   Y=0
*)
(* /QUIETSOLUTION *)


(* QUIZ *)
(** Are the two following programs equivalent?
[[
TEST X <> 1 THEN Y ::=0 ELSE Y ::= 1 FI
]]

[[
TEST X > 0 THEN Y ::=0 ELSE Y ::= 1 FI
]]

    (A) yes

    (B) no (and give a counterexample)

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   no, they are not equivalent. E.g.:
   X=1
*)
(* /QUIETSOLUTION *)


(* QUIZ *)
(** Are the two following programs equivalent?
[[
TEST X <> 1 THEN Y ::= 1 ELSE Y ::= 1 FI
]]

[[
TEST X >= 0 THEN Y ::= 1 ELSE Y ::= 0 FI
]]

    (A) yes

    (B) no (and give a counterexample)

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   yes
*)
(* /QUIETSOLUTION *)


(* QUIZ *)
(** Are the two following programs equivalent?
[[
TEST X <> 0 THEN SKIP ELSE Y ::= 1 FI
]]

[[
TEST X < 0 THEN Y ::= 0 ELSE Y ::= 1 FI
]]

    (A) yes

    (B) no (and give a counterexample)

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   no, they are not equivalent. E.g.:
   X=1
*)
(* /QUIETSOLUTION *)


(* QUIZ *)
(** Are the two following programs equivalent?
[[
  Y := 0;
  while X > 0 do
    Y := Y+X
    X := X-1
 end
 Z ::= Y
]]

[[
  Y ::= 0;
  while X > 0 do
    Y := Y+X
    Z := Y
    X := X-1
  end
]]

    (A) yes

    (B) no (and give a counterexample)

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   no. If X = 0 then the first program is equivalent to
      Y := 0; Z := 0  but the second is equivalent to
      Y := 0
*)
(* /QUIETSOLUTION *)


(* QUIZ *)
(** Are the two following programs equivalent?
[[
  while X > 0 DO
    Y := Y+1
    X := X-1
  end
]]

[[
    Y := X + Y
]]

    (A) yes

    (B) no (and give a counterexample)

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   no, they are not equivalent. E.g.:
   X=1 Y=0
*)
(* /QUIETSOLUTION *)

(* QUIZ *)
(** Are the two following programs equivalent?
[[
  while X > 0 do
    Y := 0
    X := X+1
  end
]]

[[
  if X > 0 then
    while true do
      Y := X + Y
    end
  else
    skip
  end
]]

    (A) yes

    (B) no (and give a counterexample)

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   yes
*)
(* /QUIETSOLUTION *)


(* HIDE *)
(* HIDE: BCP -- don't get the point of this one *)
(* QUIZ *)
(** Are the two following programs equivalent?
[[
  X := X+1;
  Z := 0;
  while X <> 0 do
      if Z = 0 then
         X := X - 1;
         Z := 1
      else
         X := X + 1;
         Z := Z - 1
      end
  end
]]

[[
  X := X+1;
  Z := 1;
  while X <> 0 do
      if Z = 0 then
         X := X - 1;
         Z := 1
      else
         X := X + 1;
         Z := Z - 1
      end
  end
]]

    (A) yes

    (B) no (and give a counterexample)

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   no, they are different. E.g.:
   X = 0
*)
(* /QUIETSOLUTION *)
(* /HIDE *)

(* SOONER: Add some more abstract ones (forall c, ...) *)

(** * Hoare triples *)

(* QUIZ *)
(** Is the following Hoare triple valid ?
[[
      {{ X = 5 /\  Y= 6 }}
      X := Y
      {{ X = 6 /\ Y = 6 }}
]]

    (A) yes

    (B) no

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   yes
*)
(* /QUIETSOLUTION *)

(* QUIZ *)
(** Is the following Hoare triple valid ?
[[
      {{ X = 5 /\  Y= 6 }}
      Y := X
      {{ X = 6 /\ Y = 6 }}
]]

    (A) yes

    (B) no

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   no, the state after the assignment is X = 5 /\ Y = 5
*)
(* /QUIETSOLUTION *)

(* QUIZ *)
(** Is the following Hoare triple valid ?
[[
       {{ True }}
       if Y <= X then
          X := Y
       else
          Y := X
       end
       {{ X > Y }}
]]

    (A) yes

    (B) no

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   no, if X = Y then they will still have the same
   value after the command executes.
*)
(* /QUIETSOLUTION *)

(* QUIZ *)
(** Is the following Hoare triple valid ?
[[
       {{ X = m /\ Y = n }}
       if Y <= X then
          X := Y
       else
          Y := X
       end
       {{ X = Y /\  X = min(m,n) }}
]]

    (A) yes

    (B) no

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   yes
*)
(* /QUIETSOLUTION *)

(* QUIZ *)
(** Is the following Hoare triple valid ?
[[
       {{ X = m + 1 }}
       while X > 0 do
         X := X+1
       end
       {{ False }}
]]

    (A) yes

    (B) no

*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
   yes
*)
(* /QUIETSOLUTION *)

(** * Decorated programs *)

(* QUIZ *)
(** Fill in valid decorations for the following program:
[[
  {{ X = m /\ Y = n }}
  if Y <= X then
     {{                          }} ->>
     {{                          }}
    X := Y
     {{                          }}
  else
     {{                          }} ->>
     {{                          }}
     Y := X
     {{                          }}
  end
  {{ X = Y /\  Y = min m n }}
]]
*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
[[
  {{ X = m /\ Y = n }}
  if Y <= X then
     {{ X = m /\ Y = n /\ Y <= X }} ->>
     {{ Y = Y /\ Y = min(m,n) }}
    X := Y
     {{ X = Y /\ Y = min(m,n) }}
  else
     {{ X = m /\ Y = n /\ Y > X }} ->>
     {{ X = X /\ X = min(m,n) }}
     Y := X
     {{ X = Y /\ Y = min(m,n) }}
  end
  {{ X = Y /\  Y = min(m,n) }}
]]
*)
(* /QUIETSOLUTION *)


(* QUIZ *)
(** Fill in valid decorations for the following program:
[[
  {{ TRUE }} ->>
  {{                  }}
  X := 0
  {{                  }}
  Z := 0
  {{                  }}
  while X <> n do
    {{                }} ->>
    {{                }}
    Y := 0
    {{                }}
    while Y <> m do
      {{                     }} ->>
      {{                     }}
      Z := Z + 1
      {{                     }}
      Y := Y + 1
      {{                     }}
    end
    {{                }} ->>
    {{                }}
    X := X + 1
    {{                }}
  end
  {{                  }} ->>
  {{ Z = n * m }}
]]
*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
[[
  {{ TRUE }} ->>
  {{ 0 = 0*m }}
  X := 0
  {{ 0 = X*m }}
  Z := 0
  {{ Z = X*m }}
  while X <> n do
    {{ X = X*m /\ X <> n }} ->>
    {{ Z = X*m + 0 }}
    Y := 0
    {{ Z = X*m + Y }}
    while Y <> m do
      {{ Z = X*m + Y /\ Y <> m }} ->>
      {{ Z + 1 = X*m + (Y+1) }}
      Z := Z + 1
      {{ Z = X*m + (Y+1) }}
      Y := Y + 1
      {{ Z = X*m + Y }}
    end
    {{ Z = X*m + Y /\ Y = m }} ->>
    {{ Z = (X+1)*m }}
    X := X + 1
    {{ Z = X*m }}
  end
  {{ Z = X*m /\ X = n }} ->>
  {{ Z = n * m }}
]]
*)
(* /QUIETSOLUTION *)

(* HIDE *)
(* QUIZ *)
(** Fill in valid decorations for the following program:
[[
  {{ X = m /\ Y = 0 }}
  while X <> 0 do
    {{                                                }}  ->>
    {{                                                }}
   Y := Y + X
    {{                                                }}
   X := X - 1
    {{                                                }}
  end
  {{                                                }} ->>
  {{ Y = (m*(m+1))/2 }}
]]
*)
(* /QUIZ *)
(* QUIETSOLUTION *)
(*
[[
  {{ X = m /\ Y = 0 }}
  while X <> 0 do
    {{ Y = (m-X)*((m-X)+1)/2 /\ X <= m /\ X <> 0}}  ->>
    {{ Y + X = (m-(X-1))*((m-(X-1))+1)/2 /\ X-1 < = m }}
   Y := Y + X
    {{ Y = (m-(X-1))*((m-(X-1))+1)/2 /\ X-1 < = m }}
   X := X - 1
    {{ Y = (m-X)*((m-X)+1)/2 /\ X < = m }}
  end
  {{ Y = (m-X)*((m-X)+1)/2 /\ X < = m /\ X = 0}} ->>
  {{ Y = (m*(m+1))/2 }}
]]
*)
(* /QUIETSOLUTION *)
(* /HIDE *)

