(** * Extraction: Extracting OCaml from Rocq *)
(* SOONER: Marc Bezem 2022:

  6. Extraction.v, impdriver.ml: we managed to inject

  test "x:=true";;

  and everything worked fine, that is, no syntax error and x is still
  0 afterwards! Somehow the lexer and parser manage to miss the fact
  that the language has only integer variables to which aexp's can be
  assigned, but not a bexp.  Could be a student project to find out
  why and correct.
*)

(* HIDE:

   Xavier Leroy writes:

     On 07/25/2012 04:22 PM, Benjamin C. Pierce wrote:
     > Does someone have an example of an OCaml program extracted from
     > Rocq that illustrates the "correct" way to extract the Rocq
     > string type?  I've been able to use the code below
     > (cribbed From Stdlib.extraction.ExtrOcamlString).

     As far as I know, this is the best you can do.  Instead of cribbing,
     I'd just do

     Require Import ExtrOcamlString.

     (While you're at it, "Require Import ExtrOcamlBasic." is pretty nice too.)

     With ExtrOcamlString, you get Caml's "char list" type for Rocq's
     "string" type.  You can then convert to/from real Caml strings using
     "explode" and "implode" from Batteries, or just write your own.  For
     CompCert, I use

     let camlstring_of_coqstring (s: char list) : string =
      let r = String.create (List.length s) in
      let rec fill pos = function
      | [] -> r
      | c :: s -> r.[pos] <- c; fill (pos + 1) s
      in fill 0 s

     and have no use for the reverse conversion...

     to get something minimally working, but the embedded comments
     suggest that there ought to be a better way.

     The comments just tell you that once Rocq's "ascii" type is mapped to
     Caml's "char", your code is going to be pretty inefficient (but still
     correct, I think) if, on the Rocq side, you take advantage of the
     definition of "ascii" as a 8-tuple of bools.

     Idea for a collaborative project: a *Caml* library of useful functions
     to interface with Rocq-extracted code.  Besides the string <-> char list
     conversions above, it could provide conversions between Rocq's various
     integer types (nat, Z, N, positive) and Caml's (big_int, int, int32, int64)
     [with overflow checking, mind you].  Direct, exact conversions between
     strings and Rocq's integer types would also be nice.  Floats would be
     next, using Flocq on Rocq's side.  And in CompCert, I found it invaluable
     to have a Lisp-like notion of "atoms": hash-consed Caml strings
     represented as positive integers on Rocq's side.

   Alan Schmitt adds:

    > Floats would be next, using Flocq on Rocq's side.

    The following is a quick and dirty way to extract floats from Flocq. I'm
    sure there are much nicer and safer ways to do it.

    ( * number * )
    Require Import ExtrOcamlZInt.
    Extract Inductive Fappli_IEEE.binary_float => float [
     "(fun s -> if s then (0.) else (-0.))"
     "(fun s -> if s then infinity else neg_infinity)"
     "nan"
     "(fun (s, m, e) -> let f = ldexp (float_of_int m) e in if s then f else -.f)"
    ].
    Extract Constant number_comparable => "(=)".
    Extract Constant number_add => "(+.)".
    Extract Constant number_mult => "( *. )".
    Extract Constant number_div => "(/.)".
    Extract Constant number_of_int => float_of_int.
    ( * The following functions make pattern matches with floats and will thus be removed. * )
    Extraction Inline Fappli_IEEE.Bplus Fappli_IEEE.binary_normalize Fappli_IEEE_bits.b64_plus.
    Extraction Inline Fappli_IEEE.Bmult Fappli_IEEE.Bmult_FF Fappli_IEEE_bits.b64_mult.
    Extraction Inline Fappli_IEEE.Bdiv Fappli_IEEE_bits.b64_div.

*)

(** * Basic Extraction *)

(** In its simplest form, extracting an efficient program from one
    written in Rocq is completely straightforward.

    First we say what language we want to extract into.  Options are
    OCaml (the most mature), Haskell (mostly works), and Scheme (a bit
    out of date). *)

From Stdlib Require Extraction.
Set Extraction Output Directory ".".
Extraction Language OCaml.

(** Now we load up the Rocq environment with some definitions, either
    directly or by importing them from other modules. *)

Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Arith.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import EqNat.
From LF Require Import ImpCEvalFun.

(** Finally, we tell Rocq the name of a definition to extract and the
    name of a file to put the extracted code into. *)

Extraction "imp1.ml" ceval_step.

(** When Rocq processes this command, it generates a file [imp1.ml]
    containing an extracted version of [ceval_step], together with
    everything that it recursively depends on.  Compile the present
    [.v] file and have a look at [imp1.ml] now. *)

(* ############################################################## *)
(** * Controlling Extraction of Specific Types *)

(** We can tell Rocq to extract certain [Inductive] definitions to
    specific OCaml types.  For each one, we must say
      - how the Rocq type itself should be represented in OCaml, and
      - how each constructor should be translated. *)

Extract Inductive bool => "bool" [ "true" "false" ].

(** Also, for non-enumeration types (where the constructors take
    arguments), we give an OCaml expression that can be used as a
    "recursor" over elements of the type.  (Think Church numerals.) *)

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

(** We can also extract defined constants to specific OCaml terms or
    operators. *)

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".

(** Important: It is entirely _your responsibility_ to make sure that
    the translations you're proving make sense.  For example, it might
    be tempting to include this one
[[
      Extract Constant minus => "( - )".
]]
    but doing so could lead to serious confusion!  (Why?)
*)

Extraction "imp2.ml" ceval_step.

(** Have a look at the file [imp2.ml].  Notice how the fundamental
    definitions have changed from [imp1.ml]. *)

(* ############################################################## *)
(** * A Complete Example *)

(** To use our extracted evaluator to run Imp programs, all we need to
    add is a tiny driver program that calls the evaluator and prints
    out the result.

    For simplicity, we'll print results by dumping out the first four
    memory locations in the final state.

    Also, to make it easier to type in examples, let's extract a
    parser from the [ImpParser] Rocq module.  To do this, we first need
    to set up the right correspondence between Rocq strings and lists
    of OCaml characters. *)

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.

(** We also need one more variant of booleans. *)

Extract Inductive sumbool => "bool" ["true" "false"].

(** The extraction is the same as always. *)

From LF Require Import Imp.
From LF Require Import ImpParser.

From LF Require Import Maps.
Extraction "imp.ml" empty_st ceval_step parse.

(** Now let's run our generated Imp evaluator.  First, have a look at
    [impdriver.ml].  (This was written by hand, not extracted.)

    Next, compile the driver together with the extracted code and
    execute it, as follows.
<<
        ocamlc -w -20 -w -26 -o impdriver imp.mli imp.ml impdriver.ml
        ./impdriver
>>
    (The [-w] flags to [ocamlc] are just there to suppress a few
    spurious warnings.) *)

(* ############################################################## *)
(** * Discussion *)

(** Since we've proved that the [ceval_step] function behaves the same
    as the [ceval] relation in an appropriate sense, the extracted
    program can be viewed as a _certified_ Imp interpreter.  Of
    course, the parser we're using is not certified, since we didn't
    prove anything about it! *)

(* ############################################################## *)
(** * Going Further *)

(** Further details about extraction can be found in the Extract
    chapter in _Verified Functional Algorithms_ (_Software
    Foundations_ volume 3). *)
