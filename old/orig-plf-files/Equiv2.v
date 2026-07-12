(** * Equiv2: Program Equivalence, Part II *)
(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import PeanoNat. Import Nat.
From Stdlib Require Import EqNat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import FunctionalExtensionality.
(* HIDE: This says "Require Export" instead of "Require Import"
   because we need the notation in _build/EquivTemp.v.  I (BCP) don't
   think it's a big deal -- readers will probably not even notice --
   but is there a better way to achieve this effect? *)
From PLF Require Export Imp.
From PLF Require Export Equiv.
(* TERSE: /HIDEFROMHTML *)


(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(==>*==>* ==>*+==>|(==>* EX[1-5]..." *)
(* mode: outline-minor *)
(* outline-heading-end-regexp: "\n" *)
(* End: *)
(* /HIDE *)
