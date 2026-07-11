(** * Hoare: Hoare Logic, Part I *)

(* INSTRUCTORS: In one 80-minute lecture, going at a moderate pace,
   I (BCP) can easily cover up through the sequencing rule.  The
   second lecture then covers the rest of this file and a bit of
   Hoare2, with plenty of time for real-time clicker quizzes and
   WORKINCLASS Rocq experiments (the students seemed to like these) and
   one more lecture for Hoare2.

   Covering both Hoare and Hoare2 in one week (two 80-minute lectures)
   is possible but challenging.  Don't get bogged down in digressions!

*)
(* SOONER: BCP 25: There is an excellent and fairly polished problem
   on a Hoare Logic for a little assembly language in the materials
   for the 2025 CIS 5000 final exam at Penn. We should turn it into an
   exercise in this chapter! *)
(* LATER: BCP 25: The concrete syntax in this chapter has been a long
   and evolving project! The latest development in this saga is a big
   round of improvements by Steve Zdancewic in 2024, with further
   polishing in 2025 by Noé de Santo and others. I've tried to prune
   back most of the notes-to-selves in this file, just leaving a few
   for further exploration at some point...

    - BCP 23: I *think* Assertions should either just be boolean
      expressions or else they should be their own things with
      math-looking syntax.  But in any case it would be good to get
      rid of all the coercion stuff.

    - BCP 21: An interesting concrete syntax idea: maybe we could
       write triples as ```<{ {P} c {Q} }>``` instead of ```{{P}} c
       {{Q}}```.  Maybe this would be better, both in terms of keeping
       the standard notation, and in terms of keeping the "<{...}>
       around object-language syntax" convention. And it's the same
       number of characters. :-) (Fewer, in many circumstances,
       because when writing in comments or on the board we can leave
       off the outer brackets.)  We should try it.  BCP 23: Tried it.
       Was not able to push it all the way through, but this part
       seems promising.

    - BCP 21: We should try either dropping the rule of consequence
     completely or at least using it very seldom; instead, we should
     just include uses of implication in each rule.  This would (a) make
     the assignment rule, especially, MUCH easier to explain, and (b)
     better align with the next chapter.  (One reason this chapter is
     hard to explain is that the assignment rule is so rigid -- this
     forces us to state the first several of examples in a silly, rigid,
     confusing way.) BCP 23: I think this change is quite important.
     Should be given high priority.
     BCP 25: The SparseAnnotations material from Hoare2 is relevant!
*)
(* SOONER: BCP 21: Any chance we could move the (awkwardly placed)
   weakest precondition discussion to this chapter instead? *)
(* SOONER: BCP 21: The terse version of the chapter needs serious
   work -- it has gotten quite ragged after a bunch of reorganization
   of the chapter over the past couple years.  BCP 23: Did some work
   on it.  Bit better now.  But the notation issues make everything a
   bit heavy.

*)
(* LATER: BCP 19: For the second midterm in the the 19fa instance of
   CIS500, we did a little experiment with setting up a
   total-correctness Hoare logic for Imp.  Would be fun to turn that
   into either an extended exercise or perhaps a little chapter on its
   own. I can give the .v file to anyone that wants. (It is
   technically pretty complete but needs words and a couple more
   examples.) *)
(* LATER: BCP 20: I really dislike beginning with assignment.  I know
   we can't do any examples without it, but IMO the examples *with* it
   are incomprehensible anyway! How about: skip, sequencing,
   conditionals, assignment, consequence, and finally while?  BCP 21:
   Partially implemented.  I didn't go as far as the rearrangement I
   proposed last year, because it would have involved some substantial
   rewriting, but I did at least move skip and ; to before assignment.*)
(* HIDE: What about typesetting multi-line triples as
      {{ P }}
         c
      {{ Q }}
   instead of
        {{ P }}
      c
        {{ Q }}
   when we print them? *)
(* HIDE: At some point we should try one more time to see if it's
   possible to use single curly braces for Hoare triples.  The Rocq
   manual says "For the sake of factorization with Rocq predefined
   rules, simple rules have to be observed for notations starting with
   a symbol: e.g., rules starting with { or ( should be put at level
   0."  Maybe this suggests a way forward...?
   BCP 10/18: Nope.  Writing
      Notation "'{' P '}' c '{' Q '}'" :=
        (valid_hoare_triple P c Q) (at level 0, c at next level)
        : hoare_spec_scope.
   yields
       Error: A notation must include at least one symbol.
*)
(* HIDE: This file and all later ones should make a habit of always
   presenting both syntax and semantics of new language constructs in
   informal style as well as formal.  See MoreStlc.v for a
   template. *)
(* LATER: in the HTML, consider changing the sizes of some symbols,
   e.g. make forall bigger and make <<->> and ->> and |-> smaller.
   Check that both full and terse look good.
*)
(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden".
From PLF Require Import Maps.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From PLF Require Export Imp.

(* TERSE: /HIDEFROMHTML *)

(** FULL: In the final chaper of _Logical Foundations_ (_Software
    Foundations_, volume 1), we began applying the mathematical tools
    developed in the first part of the course to studying the theory
    of a small programming language, Imp.

    - We defined a type of _abstract syntax trees_ for Imp, together
      with an _evaluation relation_ (a partial function on states)
      that specifies the _operational semantics_ of programs.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    - We proved a number of _metatheoretic properties_ -- "meta" in
      the sense that they are properties of the language as a whole,
      rather than of particular programs in the language.  These
      included:

        - determinism of evaluation

        - equivalence of some different ways of writing down the
          definitions (e.g., functional and relational definitions of
          arithmetic expression evaluation)

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving meaning) of a number
          of useful program transformations

        - behavioral equivalence of programs (in the \CHAP{Equiv}
          chapter). *)

(** FULL: If we stopped here, we would already have something useful: a set
    of tools for defining and discussing programming languages and
    language features that are mathematically precise, flexible, and
    easy to work with, applied to a set of key properties.  All of
    these properties are things that language designers, compiler
    writers, and users might care about knowing.  Indeed, many of them
    are so fundamental to our understanding of the programming
    languages we deal with that we might not consciously recognize
    them as "theorems."  But properties that seem intuitively obvious
    can sometimes be quite subtle (sometimes also subtly wrong!).

    We'll return to the theme of metatheoretic properties of whole
    languages later in this volume when we discuss _types_ and _type
    soundness_.  In this chapter, though, we turn to a different set
    of issues.
*)
(** Our goal in this chapter is to develop the tools to work through
    some simple examples of _program verification_ -- i.e., to use the
    precise definition of Imp to prove formally that particular
    programs satisfy particular specifications of their behavior.

    We'll develop a reasoning system called _Floyd-Hoare Logic_ --
    often shortened to just _Hoare Logic_ -- in which each of the
    syntactic constructs of Imp is equipped with a generic "proof
    rule" that can be used to reason compositionally about the
    correctness of programs involving this construct. *)

(** FULL: Hoare Logic originated in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a multitude of tools that are being used in
    academia and industry to specify and verify real software systems. *)

(** TERSE: *** *)

(** Hoare Logic combines two beautiful ideas: a natural way of writing
    down _specifications_ of programs, and a _structured proof
    technique_ for proving that programs are correct with respect to
    such specifications -- where by "structured" we mean that the
    structure of proofs directly mirrors the structure of the programs
    that they are about. *)

(* LATER: Add some material talking about particular impressive
   examples of program verification using successors of Hoare logic.
   It would also be good to talk a little more about the history of
   Hoare logic and give some pointers to good books (Esp. JCR's). *)
(* HIDE: MRC'20: The terse version used to start with just an outline of
   what we've done and of this chapter, but it never mentioned Hoare logic!
   The text above seems like a better intro.

   MRC'20: this is the former terse intro.

    What we've done so far:

    - Formalized Imp
         - identifiers and states
         - abstract syntax trees
         - evaluation functions (for [aexp]s and [bexp]s)
         - evaluation relation (for commands)

    - Proved some _metatheoretic_ properties
        - determinism of evaluation
        - equivalence of some different ways of writing down the
          definitions (e.g., functional and relational definitions of
          arithmetic expression evaluation)
        - guaranteed termination of certain classes of programs
        - meaning-preservation of some program transformations
        - behavioral equivalence of programs ([Equiv])

    We've dealt with a few sorts of properties of Imp programs:
      - Termination
      - Nontermination
      - Equivalence

    Topic:
      - A systematic method for reasoning about the _functional
        correctness_ of programs in Imp

    Goals:
      - a natural notation for _program specifications_ and
      - a _compositional_ proof technique for program correctness

    Plan:
      - specifications (assertions / Hoare triples)
      - proof rules
      - loop invariants
      - decorated programs
      - examples *)

(* ####################################################### *)
(** * Assertions *)

(** An _assertion_ is a logical claim about the state of a program's
    memory -- formally, a property of [state]s. *)

Definition Assertion := state -> Prop.

(* HIDE: MRC'20: pulled up these examples from the quiz/optional
   exercise so that there would be some modeling of the kinds of
   answers we expect. *)

(** For example,

    - [fun st => st X = 3] holds for states [st] in which value of [X]
      is [3],

    - [fun st => True] hold for all states, and

    - [fun st => False] holds for no states. *)

(* QUIZ *)
(** Paraphrase the following assertions in English (i.e., say
    which states satisfy them)

    (A) [fun st => st X <= st Y]

    (B) [fun st => st X = 3 \/ st X <= st Y]

    (C) [fun st => st Z * st Z <= st X /\
                   ~ (((S (st Z)) * (S (st Z))) <= st X)]

*)
(* /QUIZ *)
(* FULL *)
(* EX1? (assertions) *)
(** Paraphrase the following assertions in English (or your favorite
    natural language). *)

Module ExAssertions.
Definition assertion1 : Assertion := fun st => st X <= st Y.
Definition assertion2 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition assertion3 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition assertion4 : Assertion :=
  fun st => st Z = max (st X) (st Y).
(* SOLUTION *)
(*
   1) The value of X is less or equal than the value of Y.
   2) The value of X is 3 or is less or equal than the value of Y.
   3) The value of Z is the integer square root of X.
   4) The value of Z is the greater of the values of X and Y
*)
(* /SOLUTION *)
End ExAssertions.
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** ** Notations for Assertions *)

(** FULL: This way of writing assertions can be a little bit heavy,
    for two reasons: (1) every single assertion that we ever write is
    going to begin with [fun st => ]; and (2) this state [st] is the
    only one that we ever use to look up variables in assertions (we
    will almost never need to talk about two different memory states at the
    same time).  For discussing examples informally, we'll adopt some
    simplifying conventions: we'll drop the initial [fun st =>], and
    we'll write just [X] to mean [st X].  Thus, instead of writing
[[
      fun st => st X = m
]]
    we'll write just
[[
      {{ X = m }}.
]]
*)


(** FULL: Here the "doubly curly" braces [{{] and [}}] delimit
    the scope of an assertion.  We'll see more examples below. *)

(** TERSE: We'll use Rocq's notation features to make assertions
    look as much like informal math as possible.

    For example, instead of writing
[[
      fun st => st X = m
]]
    we'll usually write just
[[
     {{ X = m }}
]]
*)

(** FULL: This example also illustrates a convention that we'll use
    throughout the Hoare Logic chapters: in informal assertions,
    capital letters like [X], [Y], and [Z] are Imp variables, while
    lowercase letters like [x], [y], [m], and [n] are ordinary Rocq
    variables (of type [nat]).  This is why, when translating from
    informal to formal, we replace [X] with [st X] but leave [m]
    alone. *)
(* LATER: Say more about that?? *)
(* LATER: BCP 10/18: The following is a really good attempt (by
   Li-Yao) to lighten the notation for assertions.  It hasn't quite
   converged (e.g., we're not happy about [ap]), and there is an
   uncomfortable amount of magic to it, but we should think about it
   some more...

   One thing to consider adding is turning bassertion into a coercion.
   APT: I've tried that and it helps.

   APT: Overall, I really like this new notation a LOT and I would
   favor switching to it. Remainder of this chapter and Hoare2 are
   converted to use it.

   MRC'20: The notation is great in the Rocq source code!  Thanks for
   all the hard work.  It makes almost everything much more pleasant
   to read.  There are a couple further improvements that I wonder
   about.  (I'm not qualified to do them!)

     1. It would help to have a bit of explanation of what's going on,
        even if it were just hidden for instructors.  I do confess I
        don't understand some of this implicit coercion magic, nor
        does the Rocq manual chapter on it read very easily for me.

     2. It's mysterious to me why sometimes I need to write
        [%assertion] or [: Assertion] to get parsing to work right.
        Some more explanation of that, with some examples to play
        with, would be nice.

     3. Though the notations look great in the Rocq source code, they
        work somewhat less well in the middle of a proof.  Rocq almost
        immediately starts expanding them in the proof state, and that
        gets confusing (to me and my students) rather quickly.  I
        wonder whether there's a way to make Rocq less aggressive about
        this?

   APT'21: I fully agree that the expanded notations are not easy to
   read. I think the coercions are the biggest reason for that, and
   things would be a bit better if the coercions are used only for
   input, i.e. we should add

     Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

   [BCP 21: Added!]

   This would be even better if we chose shorter names for the
   coercions, e.g.  'lift_Prop', etc.

   [BCP 21: Didn't do this yet -- had trouble deciding on nice short
   names.  (E.g., 'lift_nat' is not so clear.)] *)
(* SOONER: RRand 2022: The coercion printing in recent updates is
   making the Hoare logic statements we're aiming to prove essentially
   unreadable. If the implicit coercions are too hard to deal with (I
   don't see why they would be, given the number of coercion happening
   here and in Imp) I would roll back to a previous version.  I cannot
   read what's happening in my Rocq buffer.  *)
(* HIDE: SAZ  2024: I'm confused by the above discussion.  Doesn't
   [Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop]
   request Rocq to _show_ those coercions?  I've removed it. *)
(* HIDE: SAZ 2024:
   From what I can tell, the reason the notations expand during
   the proofs is that they're writen in such a way that they
   inlude type annotations [(a : Aexp)] and explicit lambdas
   [(fun st => a st + b st)], neither of which is stable under
   simplification.  For example:

    [(fun st =>
       (fun st => (X:Aexp) st + (Y:Aexp) st) st +
       (fun st => (Z:Aexp) st) st)]

   Will print as [X + Y + Z] until simplification, at which point
   we have [(fun st => st X + st Y + st Z)] but there is no notation
   that covers this case.
*)
(** FULL: The convention described above can be implemented in Rocq with a
    little syntax magic, using coercions and annotation scopes, much
    as we did with the [<{ com }>] notation in \CHAP{Imp}. This new
    notation automatically lifts [aexp]s, numbers, and [Prop]s into
    [Assertion]s when they appear in the [{{ _ }}] scope, or when Rocq
    knows that the type of an expression is [Assertion].

    There is no need to understand the details of how these notation
    hacks work, so we hide them in the HTML version of the notes.  (We
    barely understand some of it ourselves!)  For the gory details,
    see the Rocq development.  *)

(** TERSE: Here, the [{{ A }}] brackets delimit the scope of the
    assertion notation. *)

(* HIDEFROMHTML *)
(* HIDE: Assertion-level arith expressions.  (BCP: Not sure this is
   an optimally clear name.) *)
Definition Aexp : Type := state -> nat.

(* HIDE: Some coercions *)
Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

(* HIDE: maybe this one should be explicit. *)
Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

(* INSTRUCTORS: The following command *turns on* printing of coercions, which
   we don't want.
   [ Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.]  *)
(* HIDE *)
Check (True : Assertion).
Check (3 : Aexp).
Check (X).
Check (X : Aexp).
(* /HIDE *)

(* HIDE: Make things easily unfoldable. *)
(* HIDE: MRC'20: Recording this here because it took a merry chase through
   the Rocq manual to find it:  this version of the [Arguments] command is
   documented under [simpl]. *)
(* INSTRUCTORS: These [Arguments] commands tell Rocq that these
    functions should always be unfolded during simplification (by
    [simpl]). *)
(* INSTRUCTORS: SAZ 2024 - Why do we want these functions to simplify?
   Ans: If [a : aexp] then in the assertion_scope [(X !-> a st; st)] and
   [(X !-> aeval st a; st)] look different but are actually identical
   thanks to the coercion [Aexp_of_aexp].
 *)

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

(* INSTRUCTORS: (APT) For some reason, True%assertion does not produce
   an assertion, whereas (True:Assertion) does. (Lyxia) This is
   because coercions ignore scope. *)

(* NOTATION: BCP 20: It probably makes sense now to put all these in a
   custom grammar, so that we can really control how it looks and get
   rid of things like ap. *)

(* NOTATION: SAZ 2024: I have tried to implement the suggestion above.

   There is now a custom entry [assn] for defining the syntax of
   assertions.  Like the delimiters <{ }> used for Imp programs,
   we now also have {{ }} delimiters for use with Assertions.

   Inside that scope, the meaning of variables, nat literals,
   propositions, etc. is "lifted" to take a state parameter.

   The notation {{ #f x1 .. xn }} now "lifts" a normal function
   that should be of type [nat -> .. -> nat -> T] so that each of
   the inputs is treated as an [Aexp] and the state is threaded through.
   (This replaces the need for [ap], [ap2], etc. throughout.)

   The notation {{ $rocq_term }} now "quotes" a rocq term literally
   without lifting.  Parentheses can be used as in {{ $(foo bar) }}.
 *)

Declare Custom Entry assn. (* The grammar for Hoare logic Assertions *)
Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

(* /HIDEFROMHTML *)

(** TERSE: We will sometimes need to lift functions to operate on assertion expressions:

    [{{ #f e1 .. en }}] stands for [(fun st => f (e1 st) .. (en st))]
 *)

(** FULL: One small limitation of this approach is that we don't have
    an automatic way to coerce a function application that appears
    within an assertion to make appropriate use of the state when its
    arguments should be interpets as Imp arithmetic expressions.
    Instead, we introduce a notation [#f e1 .. en] that stands for [(fun
    st => f (e1 st) .. (en st)], letting us manually mark such function
    calls when they're needed as part of an assertion.  *)

(* HIDEFROMHTML *)

(* NOTATION: This notation should come early so that later
   notations for arithmetic expressions take precedence for printing.
   Otherwise [{{ X + X }}] would print as [{{ #add X Y }}].
 *)
Notation "# f x .. y" := (fun st => (.. (f ((x:Aexp) st)) .. ((y:Aexp) st)))
                  (in custom assn at level 2,
                  f constr at level 0, x custom assn at level 1,
                  y custom assn at level 1) : assertion_scope.


Notation "P -> Q" := (fun st => (P:Assertion) st -> (Q:Assertion) st) (in custom assn at level 99, right associativity) : assertion_scope.
Notation "P <-> Q" := (fun st => (P:Assertion) st <-> (Q:Assertion) st) (in custom assn at level 95) : assertion_scope.

Notation "P \/ Q" := (fun st => (P:Assertion) st \/ (Q:Assertion) st) (in custom assn at level 85, right associativity) : assertion_scope.
Notation "P /\ Q" := (fun st => (P:Assertion) st /\ (Q:Assertion) st) (in custom assn at level 80, right associativity) : assertion_scope.
Notation "~ P" := (fun st => ~ ((P:Assertion) st)) (in custom assn at level 75, right associativity) : assertion_scope.
Notation "a = b" := (fun st => (a:Aexp) st = (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a <> b" := (fun st => (a:Aexp) st <> (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a <= b" := (fun st => (a:Aexp) st <= (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a < b" := (fun st => (a:Aexp) st < (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a >= b" := (fun st => (a:Aexp) st >= (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a > b" := (fun st => (a:Aexp) st > (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "'True'" := True.
Notation "'True'" := (fun st => True) (in custom assn at level 0) : assertion_scope.
Notation "'False'" := False.
Notation "'False'" := (fun st => False) (in custom assn at level 0) : assertion_scope.

Notation "a + b" := (fun st => (a:Aexp) st + (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a - b" := (fun st => (a:Aexp) st - (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a * b" := (fun st => (a:Aexp) st * (b:Aexp) st) (in custom assn at level 40, left associativity) : assertion_scope.

Notation "( x )" := x (in custom assn at level 0, x at level 99) : assertion_scope.

(* /HIDEFROMHTML *)

(** FULL: Occasionally we need to "escape" a raw "Rocq-defined" function to express
    a particularly complicated assertion.  We can do that using a [$] prefix,
    as in [{{ $(raw_rocq) }}].

    For example, [{{ $(fun st => forall X, st X = 0) }}] indicates an assertion that
    every variable of [X] maps to [0] in the given state.
 *)

(** TERSE: We can "escape" a raw "Rocq-defined" function using a [$] prefix:

    For example: [{{ $(fun st => forall X, st X = 0) }}]
 *)

(* HIDEFROMHTML *)
Notation "$ f" := f (in custom assn at level 0, f constr at level 0) : assertion_scope.
Notation "x" := (x%assertion) (in custom assn at level 0, x constr at level 0) : assertion_scope.

Declare Scope hoare_spec_scope.
Open Scope hoare_spec_scope.
(* /HIDEFROMHTML *)

(* NOTATION: SAZ 2024: It is important that this custom notation be
   at a level higher than 1 when added to the [constr] grammar because
   it interacts with the "application" case of [com] and the notation
   for Hoare triples.  That grammar parses embedded function arguments
   at level 1. We never want [f {{P}}] to parse [{{P}}] as an
   assertion when used in a command.  Instead we want [{{ P }}] to
   "close" the Hoare triple.
 *)
(* NOTATION: Note for Rocq custom grammar hackers.  From what I can tell, the
   Rocq LL(1) parser does left-factorize the grammar, *however* it uses a very
   strict notion of what counts as "equal" for the purposes of the factorization.
   In particular, a grammar entry might have a level,
   as in [e custom assn at level 99] in the notation below.  Leaving out the
   "at level 99" is *semantically equivalent*, because the [assn] grammar starts
   at that level, but omitting it will not work because the grammar for
   Hoare triples below includes "at level 99" -- the [LEVEL "99"] part of the
   grammar counts for factorization.

   The upshot is that means that this notation and the Hoare triple notation
   (which overlaps with [{{ _ }}]) must be changed in tandem and use identical
   level specifications. *)

(* HIDEFROMHTML *)
Notation "{{ e }}" := e (at level 2, e custom assn at level 99) : assertion_scope.
Open Scope assertion_scope.
(* /HIDEFROMHTML *)

(* HIDE *)
(* NOTATION: SAZ 2024 : useful for debugging notations -- use [Set Printing All] *)
Check X.  (* X : string *)
Check (X : aexp). (* AId X *)
Check (X : Aexp). (* Aexp_of_aexp (AId X) : Aexp *)
Check (<{ X }> : Aexp). (* Aexp_of_aexp (AId X) : Aexp *)
Check (X%assertion). (* X : string *)
Check (3 : aexp). (* Anum (S (S (S O))) : aexp *)
Check (3 : Aexp). (* Aexp_of_nat (S (S (S O))) : Aexp *)
Check {{ X = 3 }}.
Check {{ X > 3 /\ Y = (4 * X - (Y + Z)) }}.
Check {{ X <> 3 \/ (Y = 4 /\ Z = 5) }}.
Check {{ Z = (#max X Y) }}.
Check {{ Z * Z <= X
         /\  ~ (((#S Z) * (#S Z)) <= X) }}.
Check {{ #add X Y > (#max Y X) }}.
Check (fun st => forall P m a, {{ $(fun st => (P (X !-> m ; st)
                                    /\ st X = aeval (X !-> m ; st) a))  }} st).
Check {{ $S }}.
Check {{ $(fun st => st) }}.
(* /HIDE *)

(** ** Example Assertions *)

(** FULL: Here are some example assertions that take advantage of this
    new notation. *)

Module  ExamplePrettyAssertions.
Definition assertion1 : Assertion := {{ X = 3 }}.
Definition assertion2 : Assertion := {{ True }}.
Definition assertion3 : Assertion := {{ False }}.
Definition assertion4 : Assertion := {{ True \/ False }}.
Definition assertion5 : Assertion := {{ X <= Y }}.
Definition assertion6 : Assertion := {{ X = 3 \/ X <= Y }}.
Definition assertion7 : Assertion := {{ Z = (#max X Y) }}.
Definition assertion8 : Assertion := {{ Z * Z <= X
                                        /\  ~ (((#S Z) * (#S Z)) <= X) }}.
Definition assertion9 : Assertion := {{ #add X Y > #max Y X }}.
End ExamplePrettyAssertions.

(** ** Assertion Implication *)

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q], if, whenever [P] holds in some state [st], [Q]
    also holds. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

(** Note that the notation for _assertion implication_ is analogous
    to the "usual" Rocq implication [->]. *)

Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80) : hoare_spec_scope.

(** We'll also want the "iff" variant of implication between
    assertions: *)

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : hoare_spec_scope.

(** FULL: (The [hoare_spec_scope] annotation here tells Rocq that this
    notation is not global but is intended to be used in particular
    contexts.) *)

(* ####################################################### *)
(** * Hoare Triples, Informally *)

(** FULL: A _Hoare triple_ is a claim about the state before and
    after executing a command.  The standard notation is
[[
      {P} c {Q}
]]
    meaning:

      - If command [c] begins execution in a state satisfying assertion [P],
      - and if [c] eventually terminates in some final state,
      - then that final state will satisfy the assertion [Q].

    Assertion [P] is called the _precondition_ of the triple, and [Q] is
    the _postcondition_.

    Because single braces are already used for other things in Rocq, we'll write
    Hoare triples with double braces:
[[
       {{P}} c {{Q}}
]]
 *)
(** TERSE: A _Hoare triple_ is a claim about the state before and
    after executing a command:
[[
      {{P}} c {{Q}}
]]
    This means:

      - If command [c] begins execution in a state satisfying
        assertion [P],
      - and if [c] eventually terminates in some final state,
      - then that final state will satisfy the assertion [Q].

    Assertion [P] is called the _precondition_ of the triple, and [Q]
    is the _postcondition_. *)
(** TERSE: *** *)
(** For example,

    - The Hoare triple
[[
          {{X = 0}} X := X + 1 {{X = 1}}
]]
      states that command [X := X + 1] will transform a state in
      which [X = 0] to a state in which [X = 1].

    - On the other hand,
[[
          forall m, {{X = m}} X := X + 1 {{X = m + 1}}
]]
      is a _proposition_ stating that the Hoare triple [{{X = m}} X :=
      X + 1 {{X = m + 1}}] is valid for any choice of [m].  Note that
      [m] in the two assertions is a reference to the _Rocq_ variable
      [m], which is bound outside the Hoare triple. *)

(* FULL *)
(* EX1? (triples) *)
(* /FULL *)
(* TERSE *)
(* QUIZ *)
(* /TERSE *)
(** Paraphrase the following in English.
[[
     1) {{True}} c {{X = 5}}

     2) forall m, {{X = m}} c {{X = m + 5)}}

     3) {{X <= Y}} c {{Y <= X}}

     4) {{True}} c {{False}}

     5) forall m,
          {{X = m}}
          c
          {{Y = real_fact m}}

     6) forall m,
          {{X = m}}
          c
          {{(Z * Z) <= m /\ ~ (((S Z) * (S Z)) <= m)}}
]]
*)
(* TERSE *)
(* /QUIZ *)
(* /TERSE *)
(* TERSE: QUIETSOLUTION *)
(* FULL: SOLUTION *)
(*
    1) If command c terminates starting in an arbitrary state it produces a
       state where the value of X is equal to 5.
    2) Starting in a state where the value of X is m, if c terminates the
       value of X is equal to m+5.
    3) Starting in a state where the value of X less or equal than the
       value of Y, if c terminates then the value of Y is less or equal
       than the value of X.
    4) c doesn't terminate on any starting state
    5) If c terminates then Y contains as a value the factorial of the
       initial value of X.
    6) Starting in a state in which the value of X is equal to m, if c
       terminates starting in an arbitrary state then Z contains the
       integer square root of the initial value of X. *)
(* FULL: /SOLUTION *)
(* TERSE: /QUIETSOLUTION *)
(* FULL *)
(** [] *)

(* /FULL *)
(* QUIZ *)
(** Is the following Hoare triple _valid_ -- i.e., is the
    claimed relation between [P], [c], and [Q] true?
[[
    {{True}} X := 5 {{X = 5}}
]]

    (A) Yes

    (B) No
*)
(* /QUIZ *)
(* QUIZ *)
(** What about this one?
[[
   {{X = 2}} X := X + 1 {{X = 3}}
]]

   (A) Yes

   (B) No
*)
(* /QUIZ *)
(* QUIZ *)
(** What about this one?
[[
   {{True}} X := 5; Y := 0 {{X = 5}}
]]

   (A) Yes

   (B) No
*)
(* /QUIZ *)
(* QUIZ *)
(** What about this one?
[[
   {{X = 2 /\ X = 3}} X := 5 {{X = 0}}
]]

   (A) Yes

   (B) No
*)
(* /QUIZ *)
(* QUIZ *)
(** What about this one?
[[
   {{True}} skip {{False}}
]]

   (A) Yes

   (B) No
*)
(* /QUIZ *)
(* QUIZ *)
(** What about this one?
[[
   {{False}} skip {{True}}
]]

   (A) Yes

   (B) No
*)
(* /QUIZ *)
(* QUIZ *)
(** What about this one?
[[
   {{True}} while true do skip end {{False}}
]]

   (A) Yes

   (B) No
*)
(* /QUIZ *)
(* QUIZ *)
(** This one?
[[
    {{X = 0}}
      while X = 0 do X := X + 1 end
    {{X = 1}}
]]

   (A) Yes

   (B) No
*)
(* /QUIZ *)
(* QUIZ *)
(** This one?
[[
    {{X = 1}}
      while X <> 0 do X := X + 1 end
    {{X = 100}}
]]

   (A) Yes

   (B) No
*)
(* /QUIZ *)
(* INSTRUCTORS: SOLUTION: All are valid except the 5th. *)
(* FULL *)
(* EX1? (valid_triples) *)
(** Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?
[[
   1) {{True}} X := 5 {{X = 5}}

   2) {{X = 2}} X := X + 1 {{X = 3}}

   3) {{True}} X := 5; Y := 0 {{X = 5}}

   4) {{X = 2 /\ X = 3}} X := 5 {{X = 0}}

   5) {{True}} skip {{False}}

   6) {{False}} skip {{True}}

   7) {{True}} while true do skip end {{False}}

   8) {{X = 0}}
        while X = 0 do X := X + 1 end
      {{X = 1}}

   9) {{X = 1}}
        while X <> 0 do X := X + 1 end
      {{X = 100}}
]]
*)
(* FULL: SOLUTION *)
(* All are valid except the 5th. *)
(* FULL: /SOLUTION *)
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** * Hoare Triples, Formally *)

(** We formalize valid Hoare triples in Rocq as follows: *)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st  ->
     Q st'.

(* NOTATION: SAZ 2024 One trickiness of these notations is that we
   want the [com] and [assn] grammars to be "open", so that they can
   include expressions parsed by the full [constr] grammar of Rocq.
   However, then there is a conflict of precedence of the
   "application" cases:

   The example " {{ True }} X := 0 {{ False }} " does not parse as
   intended because the [com] grammar includes the capability of
   parsing the (ill-typed) term "0 {{ False }}".

   This means that the "application" for [com] should disallow
   arguments at the level at which the [assn] grammar is included
   in constr.  The upshot is that this notation should be included
   in the grammar at the *same* level as the assertion notation
   [{{ P }}], which is 2.  *)

(** Notation for Hoare triples *)

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99,
     Q custom assn at level 99)
    : hoare_spec_scope.

(* HIDE *)
Check {{ True }} skip {{ False }}.
Check {{ True }} X := 0 {{ False }}.
(* /HIDE *)

(* HIDE: AAA: If I try to set the notation as {P} c {Q}, I get the
   following error:

     Error: A notation must include at least one symbol.

   Maybe we could use other braces? For instance, I tried it with [P]
   c [Q] and it seems to work (although I don't know how that would
   affect the rest of the book).

   BCP: Let's try with the "squashed" double braces for a while and
   see if we like it.

   P.S.
   This works:
      Notation "{ x }" := (x) (at level 0, x at level 99).
   But this doesn't:
      Notation "{ P }  c  { Q }" :=
        (valid_hoare_triple P c Q)
        (at level 0, P at level 99, c at level 99, Q at level 99)
      : hoare_spec_scope.
   Why?? *)

(* TERSE: HIDEFROMHTML *)
(* EX1 (hoare_post_true) *)

(** Prove that if [Q] holds in every state, then any triple with [Q]
    as its postcondition is valid. *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  (* ADMITTED *)
  intros P Q c H. unfold valid_hoare_triple.
  intros st st' Heval HP.
  apply H.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX1? (hoare_pre_false) *)

(** Prove that if [P] holds in no state, then any triple with [P] as
    its precondition is valid. *)

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  (* ADMITTED *)
  intros P Q c H. unfold valid_hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  contradiction.
Qed.
(* /ADMITTED *)
(** [] *)
(* TERSE: /HIDEFROMHTML *)

(* ####################################################### *)
(** * Proof Rules *)

(** FULL: The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of specific Hoare triples.  That
    is, we want the structure of a program's correctness proof to
    mirror the structure of the program itself.  To this end, in the
    sections below, we'll introduce a rule for reasoning about each of
    the different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules for gluing things together.  We
    will then be able to prove programs correct using these proof
    rules, without ever unfolding the definition of [valid_hoare_triple]. *)
(** TERSE: We want to be able to _prove_ Hoare triples formally.

    Here's our plan:
      - introduce one "proof rule" for each Imp syntactic form
      - plus a couple of "structural rules" that help glue proofs
        together
      - prove these rules correct in terms of the definition of
        [valid_hoare_triple]
      - prove programs correct using these proof rules, without ever
        unfolding the definition of [valid_hoare_triple] *)

(* ####################################################### *)
(** ** Skip *)

(** Since [skip] doesn't change the state, it preserves any
    assertion [P]:
[[[
      --------------------  (hoare_skip)
      {{ P }} skip {{ P }}
]]]
*)

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
(* FOLD *)
Proof.
  intros P st st' H HP. inversion H; subst. assumption.
Qed.
(* /FOLD *)

(* ####################################################### *)
(** ** Sequencing *)

(** If command [c1] takes any state where [P] holds to a state where
    [Q] holds, and if [c2] takes any state where [Q] holds to one
    where [R] holds, then doing [c1] followed by [c2] will take any
    state where [P] holds to one where [R] holds:
[[[
        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ----------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
]]]
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
(* FOLD *)
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  eauto.
Qed.
(* /FOLD *)

(** FULL: Note that, in the formal rule [hoare_seq], the premises are
    given in backwards order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule, since the natural way to construct a Hoare-logic
    proof is to begin at the end of the program (with the final
    postcondition) and push postconditions backwards through commands
    until we reach the beginning. *)

(* ####################################################### *)
(** ** Assignment *)

(** FULL: The rule for assignment is the most fundamental of the Hoare
    logic proof rules.  Here's how it works.

    Consider this incomplete Hoare triple:
[[
       {{ ??? }}  X := Y  {{ X = 1 }}
]]

    We want to assign [Y] to [X] and finish in a state where [X] is [1].
    What could the precondition be?

    One possibility is [Y = 1], because if [Y] is already [1] then
    assigning it to [X] causes [X] to be [1].  That leads to a valid
    Hoare triple:
[[
       {{ Y = 1 }}  X := Y  {{ X = 1 }}
]]
    It may seem as though coming up with that precondition must have
    taken some clever thought.  But there is a mechanical way we could
    have done it: if we take the postcondition [X = 1] and in it
    replace [X] with [Y]---that is, replace the left-hand side of the
    assignment statement with the right-hand side---we get the
    precondition, [Y = 1]. *)

(** TERSE: How can we complete this triple?
[[
       {{ ??? }}  X := Y  {{ X = 1 }}
]]
    One natural possibility is:
[[
       {{ Y = 1 }}  X := Y  {{ X = 1 }}
]]

    The precondition is just the postcondition, but with [X] replaced
    by [Y]. *)

(** FULL: That same idea works in more complicated cases.  For
    example:
[[
       {{ ??? }}  X := X + Y  {{ X = 1 }}
]]
    If we replace the [X] in [X = 1] with [X + Y], we get [X + Y = 1].
    That again leads to a valid Hoare triple:
[[
       {{ X + Y = 1 }}  X := X + Y  {{ X = 1 }}
]]
    Why does this technique work?  The postcondition identifies some
    property [P] that we want to hold of the variable [X] being
    assigned.  In this case, [P] is "equals [1]".  To complete the
    triple and make it valid, we need to identify a precondition that
    guarantees that property will hold of [X].  Such a precondition
    must ensure that the same property holds of _whatever is being
    assigned to_ [X].  So, in the example, we need "equals [1]" to
    hold of [X + Y].  That's exactly what the technique guarantees. *)

(** TERSE: *** *)
(** TERSE: How about this one?
[[
       {{ ??? }}  X := X + Y  {{ X = 1 }}
]]
    Replace [X] with [X + Y]:
[[
       {{ X + Y = 1 }}  X := X + Y  {{ X = 1 }}
]]
    This works because "equals 1" holding of [X] is guaranteed
    by the property "equals 1" holding of whatever is being
    assigned to [X]. *)

(** TERSE: *** *)

(** In general, the postcondition could be some arbitrary assertion
    [Q], and the right-hand side of the assignment could be some
    arbitrary arithmetic expression [a]:
[[
       {{ ??? }}  X := a  {{ Q }}
]]
    The precondition would then be [Q], but with any occurrences of
    [X] in it replaced by [a]. *)
(** TERSE: *** *)
(** Let's introduce a notation for this idea of replacing occurrences:
    Define [Q [X |-> a]] to mean "[Q] where [a] is substituted in
    place of [X]".

    This yields the Hoare logic rule for assignment:
[[
      {{ Q [X |-> a] }}  X := a  {{ Q }}
]]
    One way of reading this rule is: If you want statement [X := a]
    to terminate in a state that satisfies assertion [Q], then it
    suffices to start in a state that also satisfies [Q], except
    where [a] is substituted for every occurrence of [X]. *)

(** FULL: To many people, this rule seems "backwards" at first, because
    it proceeds from the postcondition to the precondition.  Actually
    it makes good sense to go in this direction: the postcondition is
    often what is more important, because it characterizes what will be
    true after running the code.

    Nonetheless, it's also possible to formulate a "forward" assignment
    rule.  We'll do that later in some exercises. *)

(** TERSE: *** *)

(** Here are some valid instances of the assignment rule:
[[
      {{ (X <= 5) [X |-> X + 1] }}         (that is, X + 1 <= 5)
        X := X + 1
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3] }}              (that is, 3 = 3)
        X := 3
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3] }}.  (that is, 0 <= 3 /\ 3 <= 5)
        X := 3
      {{ 0 <= X /\ X <= 5 }}
]]
*)

(** TERSE: *** *)

(** To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion",
    which we refer to as assertion substitution, or [assertion_sub].

    Intuitively, given a proposition [P], a variable [X], and an
    arithmetic expression [a], we want to derive another proposition
    [P'] that is just the same as [P] except that [P'] should mention
    [a] wherever [P] mentions [X]. *)

(** TERSE: *** *)

(** This operation is related to the idea of substituting Imp
    expressions for Imp variables that we saw in \CHAP{Equiv}
    ([subst_aexp] and friends). The difference is that, here,
    [P] is an arbitrary Rocq assertion, so we can't directly
    "edit" its text. *)

(** TERSE: *** *)

(** However, we can achieve the same effect by evaluating [P] in an
    updated state, defined as follows: *)

Definition assertion_sub X (a:aexp) (P:Assertion) : Assertion :=
  fun (st : state) => P (X !-> (aeval st a); st).

(* SOONER: This concrete syntax is hard to read in comments because of
   all the square brackets. Something like [P with X |-> a] would be
   much better. I guess the same will apply to the lambda-calculus
   chapters...  BCP 25: I still think this is a good idea, and I had
   a quick go at implementing it, but did not succeed yet. *)
Notation "P [ X |-> a ]" := (assertion_sub X a P)
                              (in custom assn at level 10, left associativity,
                               P custom assn, X global, a custom com)
                          : assertion_scope.

(**  This notation allows us to write this operation as:
[[
        P[ X |-> a ]
]]
*)

(* HIDE *)
Check (fun st => assertion_sub X <{ 2 * X }>  ({{ X <= 10 }}) st)%assertion.
Check {{ (X <= 10) [X |-> 2 * X] }}.
Check (forall st, ({{ (X <= 10) [X |-> 2 * X] }}) st).
(* /HIDE *)

(** That is, [P [X |-> a]] stands for an assertion -- let's call it
    [P'] -- that behaves just like [P] except that, wherever [P] looks up
    the variable [X] in the current state, [P'] instead uses the value
    of the expression [a]. *)

(* FULL *)
(** To see how this works in more detail, let's calculate what happens with
    a couple of examples.  First, suppose [P'] is [(X <= 5) [X |-> 3]] --
    that is, more formally, [P'] is the Rocq expression
[[
    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st 3 ; st),
]]
    which simplifies to
[[
    fun st =>
      (fun st' => st' X <= 5)
      (X !-> 3 ; st)
]]
    and further simplifies to
[[
    fun st =>
      ((X !-> 3 ; st) X) <= 5
]]
    and finally to
[[
    fun st =>
      3 <= 5.
]]
    That is, [P'] is the assertion that [3] is less than or equal to
    [5] (as expected). *)

(** For a more interesting example, suppose [P'] is [(X <= 5) [X |->
    X + 1]].  Formally, [P'] is the Rocq expression
[[
    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st (X + 1); st),
]]
    which simplifies to
[[
    fun st =>
      (X !-> aeval st (X + 1) ; st) X <= 5
]]
    and further simplifies to
[[
    fun st =>
      (aeval st (X + 1)) <= 5.
]]
    That is, [P'] is the assertion that [X + 1] is at most [5].
*)
(* /FULL *)

(** TERSE: *** *)
(** We can demonstrate formally that we have captured intuitive meaning of
    "assertion subsitution" by proving some example logical equivalences: *)

(* HIDEFROMHTML *)
Module ExampleAssertionSub.
(* /HIDEFROMHTML *)
Example equivalent_assertion1 :
  {{ (X <= 5) [X |-> 3] }} <<->> {{ 3 <= 5 }}.
(* FOLD *)
Proof.
  split; unfold assert_implies, assertion_sub; intros st H;
  simpl in *; apply H.
Qed.
(* /FOLD *)

Example equivalent_assertion2 :
  {{ (X <= 5) [X |-> X + 1] }} <<->> {{ (X + 1) <= 5 }}.
(* FOLD *)
Proof.
  split; unfold assert_implies, assertion_sub; intros st H;
  simpl in *; apply H.
Qed.
(* /FOLD *)
(* HIDEFROMHTML *)
End ExampleAssertionSub.
(* /HIDEFROMHTML *)

(** TERSE: *** *)

(** Now, using the substitution operation we've just defined, we can
    give the precise proof rule for assignment:
[[[
      ---------------------------- (hoare_asgn)
      {{Q [X |-> a]}} X := a {{Q}}
]]]
*)

(** We can prove formally that this rule is indeed valid. *)

Theorem hoare_asgn : forall Q X (a:aexp),
  {{Q [X |-> a]}} X := a {{Q}}.
(* FOLD *)
Proof.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assertion_sub in HQ. simpl in HQ. assumption.  Qed.
(* /FOLD *)

(** TERSE: *** *)

(** Here's a first formal proof of a Hoare triple using this rule. *)

Example assertion_sub_example :
  {{(X < 5) [X |-> X + 1]}}
    X := X + 1
  {{X < 5}}.
Proof.
  apply hoare_asgn.  Qed.

(** TERSE: *** *)
(** Of course, we'd probably prefer to work with this simpler triple:
[[
      {{X < 4}} X := X + 1 {{X < 5}}
]]
   We will see how to do so in the next section. *)

(* FULL *)

(** Complete these Hoare triples by providing an appropriate
    precondition using [exists], then prove then with [apply
    hoare_asgn]. If you find that tactic doesn't suffice, double check
    that you have completed the triple properly. *)

(* EX2? (hoare_asgn_examples1) *)
Example hoare_asgn_examples1 :
  exists P,
    {{ P }}
      X := 2 * X
    {{ X <= 10 }}.
Proof.
  (* ADMITTED *)
  exists {{ (X <= 10) [X |-> 2 * X] }}. simpl.
  apply hoare_asgn.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2? (hoare_asgn_examples2) *)
Example hoare_asgn_examples2 :
  exists P,
    {{ P }}
      X := 3
    {{ 0 <=  X /\ X <= 5 }}.
Proof. (* ADMITTED *)
  exists  {{ (0 <= X /\ X <= 5) [X |-> 3] }}.
  apply hoare_asgn.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2! (hoare_asgn_wrong) *)

(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems puzzling to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
[[[
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X := a {{ X = a }}
]]]
    Give a counterexample showing that this rule is incorrect and use
    it to complete the proof below, showing that it is really a
    counterexample.  (Hint: The rule universally quantifies over the
    arithmetic expression [a], so your counterexample needs to
    exhibit an [a] for which the rule doesn't work.) *)

Theorem hoare_asgn_wrong : exists a:aexp,
  ~ {{ True }} X := a {{ X = a }}.
Proof.
  (* ADMITTED *)
  exists <{ X + 1 }>. intros Hc.
  unfold valid_hoare_triple in Hc.
  remember (X !-> 1) as st1 eqn:Heqst1.
  assert (st1 X = aeval st1 <{ X + 1 }>) as H2.
  { apply Hc with (st := empty_st).
    - (* assignment *) rewrite -> Heqst1. apply E_Asgn. reflexivity.
    - (* True *)  constructor. }
  rewrite -> Heqst1 in H2.  unfold t_update in H2.
  simpl in H2. discriminate.
Qed.
(* /ADMITTED *)
(* SOLUTION *)

(* If [a] itself mentions [X], then the value of [a] may be different
   in the final state because of this update. For example, if [a] is
   [X + 1], then setting [X] to [a] certainly does not achieve the
   postcondition [X = X + 1]!  The underlying problem is that the
   state in which the postcondition will be checked is different than
   the state in which [a] was evaluated when it was assigned to [X]. *)
(* /SOLUTION *)
(** [] *)

(* LATER: MRC'20: It sure would be great for the next two exercises
   to use the updated notation.  However, I can't figure out how to
   get the postcondition to work with it.  The problem is that the
   substitution operator is defined on assertions, but I need a
   version of it defined on expressions.
   Lef 21: Gave it another unsuccessful go, seems like the same
   issue as MRC'20.

     Theorem hoare_asgn_fwd :
            forall P m a,
              {{ P /\ X = m }}
              X := a
              {{ P [X |-> m] /\ X = a }}.
*)

(* EX3A? (hoare_asgn_fwd) *)
(** By using a _parameter_ [m] (a Rocq number) to remember the
    original value of [X] we can define a Hoare rule for assignment
    that does, intuitively, "work forwards" rather than backwards.
[[[
       ------------------------------------------ (hoare_asgn_fwd)
       {{fun st => P st /\ st X = m}}
         X := a
       {{fun st => P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}
]]]
    Note that we need to write out the postcondition in "desugared"
    form, because it needs to talk about two different states: we use
    the original value of [X] to reconstruct the state [st'] before the
    assignment took place.  (Also note that this rule is more complicated
    than [hoare_asgn]!)

    Prove that this rule is correct. *)

(* HIDE: BCP 21: Could we make the precondition use compact
   notation, at least? *)
(* HIDE: SAZ 2024 - this version of the syntax does let
   us use the compact notation for the precondition, but it
   comes at the cost of having to "escape" the function in
   the postcondition. *)

Theorem hoare_asgn_fwd :
  forall (m:nat) (a:aexp) (P : Assertion),
  {{P /\ X = m}}
    X := a
  {{ $(fun st => (P (X !-> m ; st)
             /\ st X = aeval (X !-> m ; st) a)) }}.
Proof.
  (* ADMITTED *)
  intros m a P.
  unfold valid_hoare_triple. intros st st' Heval Hpre. simpl in Hpre.
  inversion Heval; subst. destruct Hpre; subst.
  rewrite t_update_eq.
  rewrite t_update_shadow.
  rewrite t_update_same.
  auto.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2A? (hoare_asgn_fwd_exists) *)
(** Another way to define a forward rule for assignment is to
    existentially quantify over the previous value of the assigned
    variable.  Prove that it is correct.
[[[
      ------------------------------------ (hoare_asgn_fwd_exists)
      {{fun st => P st}}
        X := a
      {{fun st => exists m, P (X !-> m ; st) /\
                     st X = aeval (X !-> m ; st) a }}
]]]
*)
(* INSTRUCTORS: This rule was proposed to BCP by Nick Giannarakis and
   Zoe Paraskevopoulou.
   APT: This is actually Floyd's original rule.  See Mike Gordon,
   "Background reading on Hoare Logic," p.21
   https://www.cl.cam.ac.uk/archive/mjcg/HL/Notes/Notes.pdf *)

Theorem hoare_asgn_fwd_exists :
  forall a (P : Assertion),
  {{ P }}
    X := a
  {{ $(fun st => exists m, P (X !-> m ; st) /\
                st X = aeval (X !-> m ; st) a) }}.
Proof.
  (* ADMITTED *)
  intros a P.
  unfold valid_hoare_triple.
  intros st st' Heval Hpre.
  exists (st X). inversion Heval; subst.
  rewrite t_update_eq.
  rewrite t_update_shadow.
  rewrite t_update_same.
  auto.
Qed. (* /ADMITTED *)
(** [] *)
(* /FULL *)

(* HIDE *)
    (* HIDE: BCP 19: This sequence of quizzes seems confusing /
      confused. The "trivial" ones, as Robert points out, are NOT
      trivial...  BCP 21: I'm going to hide all these quizzes for the
      moment -- they seem worse than nothing in present form. *)
    (* QUIZ *)
    (** Here is the assignment rule again:
    [[
          {{ Q [X |-> a] }} X := a {{ Q }}
    ]]
        Is the following triple a valid instance of this rule?
    [[
          {{ X = 5 }} X := X + 1 {{ X = 6 }}
    ]]

        (A) Yes

        (B) No
    *)
    (* INSTRUCTORS: a trivial one, to warm up *)
    (* HIDE: Robert Rand: Why is this a trivial one? In the precondition
      we want [X + 1 = 6], instead we have the equivalent [X = 5]. This
      seems like a good example of the problem we want to illustrate in
      the last quiz. *)
    (* /QUIZ *)

    (* QUIZ *)
    (** Here is the assignment rule again:
    [[
          {{ Q [X |-> a] }} X := a {{ Q }}
    ]]
        Is the following triple a valid instance of this rule?
    [[
          {{ Y < Z }} X := Y {{ X < Z }}
    ]]

        (A) Yes

        (B) No
    *)
    (* INSTRUCTORS: a slightly less trivial one, to get the juices flowing *)
    (* /QUIZ *)

    (* QUIZ *)
    (** The assignment rule again:
    [[
          {{ Q [X |-> a] }} X := a {{ Q }}
    ]]
        Is the following triple a valid instance of this rule?
    [[
          {{ X+1 < Y }} X := X + 1 {{ X < Y }}
    ]]

        (A) Yes

        (B) No
    *)
    (* INSTRUCTORS: a less trivial one, to start thinking *)
    (* /QUIZ *)

    (* QUIZ *)
    (** The assignment rule again:
    [[
          {{ Q [X |-> a] }} X := a {{ Q }}
    ]]
        Is the following triple a valid instance of this rule?
    [[
          {{ X < Y }} X := X + 1 {{ X+1 < Y }}
    ]]

        (A) Yes

        (B) No
    *)
    (* INSTRUCTORS: a wrong one (actually an invalid triple), to see if
      they are paying attention *)
    (* /QUIZ *)

    (* QUIZ *)
    (** The assignment rule again:
    [[
          {{ Q [X |-> a] }} X := a {{ Q }}
    ]]
        Is the following triple a valid instance of this rule?
    [[
          {{ X < Y }} X := X + 1 {{ X < Y+1 }}
    ]]

        (A) Yes

        (B) No
    *)
    (* INSTRUCTORS: another wrong one -- valid, but not an instance of the rule! *)
    (* /QUIZ *)

    (* QUIZ *)
    (** The assignment rule again:
    [[
          {{ Q [X |-> a] }} X := a {{ Q }}
    ]]
        Is the following triple a valid instance of this rule?
    [[
          {{ True }} X := 3 {{ X = 3 }}
    ]]

        (A) Yes

        (B) No
    *)
    (* /QUIZ *)
    (* INSTRUCTORS: Again, valid but not an instance of the rule.  This
      leads into the discussion of the rule of consequence. *)
(* /HIDE *)

(* ####################################################### *)
(** ** Consequence *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need. *)

(** TERSE: *** *)
(** For instance,
[[
      {{(X = 3) [X |-> 3]}} X := 3 {{X = 3}},
]]
    follows directly from the assignment rule, but
[[
      {{True}} X := 3 {{X = 3}}
]]
    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.

    However, they are logically _equivalent_, so if one triple is
    valid, then the other must certainly be as well.  We can capture
    this observation with the following rule:
[[[
                {{P'}} c {{Q}}
                  P <<->> P'
             ---------------------
                {{P}} c {{Q}}
]]]
*)

(** TERSE: *** *)

(** Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.
[[[
                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
]]]
*)

(** TERSE: *** *)

(** Here are the formal versions: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
(* FOLD *)
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.
(* /FOLD *)

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
(* FOLD *)
Proof.
  unfold valid_hoare_triple, "->>".
  intros P Q Q' c Hhoare Himp st st' Heval Hpre.
  apply Himp.
  apply Hhoare with (st := st).
  - assumption.
  - assumption.
Qed.
(* /FOLD *)

(** TERSE: *** *)

(** For example, we can use the first consequence rule like this:
[[
    {{ True }} ->>
    {{ (X = 1) [X |-> 1] }}
      X := 1
    {{ X = 1 }}
]]
    Or, formally... *)
(* INSTRUCTORS: BCP 20: Careful: this proof got messed up when I
   tried it in class. *)

Example hoare_asgn_example1 :
  {{True}} X := 1 {{X = 1}}.
Proof.
  (* WORKINCLASS *)
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update; simpl.
    intros st _. reflexivity.
Qed.
(* /WORKINCLASS *)

(** TERSE: *** *)
(** We can also use it to prove the example mentioned earlier.
[[
    {{ X < 4 }} ->>
    {{ (X < 5)[X |-> X + 1] }}
      X := X + 1
    {{ X < 5 }}
]]
   Or, formally ... *)

Example assertion_sub_example2 :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  (* WORKINCLASS *)
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update.
    intros st H. simpl in *. lia.
Qed.
(* /WORKINCLASS *)

(** TERSE: *** *)
(** Finally, here is a combined rule of consequence that allows us to
    vary both the precondition and the postcondition.
[[[
                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
]]]
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
(* FOLD *)
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - apply hoare_consequence_post with (Q' := Q'); assumption.
  - assumption.
Qed.
(* /FOLD *)

(* ####################################################### *)
(** ** Automation *)

(** Many of the proofs we have done so far with Hoare triples can be
    streamlined using the automation techniques that we introduced in
    the \CHAPV1{Auto} chapter of _Logical Foundations_.

    Recall that the [auto] tactic can be told to [unfold] definitions
    as part of its proof search.  Let's give it that hint for the
    definitions and coercions we're using: *)

Hint Unfold assert_implies assertion_sub t_update : core.
Hint Unfold valid_hoare_triple : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

(** Also recall that [auto] will search for a proof involving [intros]
    and [apply].  By default, the theorems that it will apply include
    any of the local hypotheses, as well as theorems in the "core" hint
    database. *)

(** FULL: The proof of [hoare_consequence_pre], repeated below, looks
    like an opportune place for such automation, because all it does
    is [unfold], [intros], and [apply].  (It uses [assumption], too,
    but that's just application of a hypothesis.) *)

(** TERSE: *** *)
(** TERSE: Here's a good candidate for automation: *)

Theorem hoare_consequence_pre' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

(* FULL *)
(** Merely using [auto], though, doesn't complete the proof. *)

Theorem hoare_consequence_pre'' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  auto. (* no progress *)
Abort.

(** The problem is the [apply Hhoare with...] part of the proof.  Rocq
    isn't able to figure out how to instantiate [st] without some help
    from us.  Recall, though, that there are versions of many tactics
    that will use _existential variables_ to make progress even when
    the regular versions of those tactics would get stuck.

    Here, the [eapply] tactic will introduce an existential variable
    [?st] as a placeholder for [st], and [eassumption] will
    instantiate [?st] with [st] when it discovers [st] in assumption
    [Heval].  By using [eapply] we are essentially telling Rocq, "Be
    patient: The missing part is going to be filled in later in the
    proof." *)
(* /FULL *)

(** TERSE: *** *)
(** TERSE: Tactic [eapply] will find [st] for us. *)

Theorem hoare_consequence_pre''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  eapply Hhoare.
  - eassumption.
  - apply Himp. assumption.
Qed.

(** TERSE: *** *)
(** The [eauto] tactic will use [eapply] as part of its proof search.
    So, the entire proof can actually be done in just one line. *)

Theorem hoare_consequence_pre'''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

(** FULL: Of course, it's hard to predict that [eauto] suffices here
    without having gone through the original proof of
    [hoare_consequence_pre] to see the tactics it used. But now that
    we know [eauto] worked there, it's a good bet that it will also
    work for [hoare_consequence_post]. *)

(** TERSE: *** *)
(** TERSE: ...as can the proof for the postcondition consequence
    rule. *)

Theorem hoare_consequence_post' : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

(** TERSE: *** *)
(** We can also use [eapply] to streamline a proof
    ([hoare_asgn_example1]), that we did earlier as an example of
    using the consequence rule: *)

Example hoare_asgn_example1' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre. (* no need to state an assertion *)
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update.
    intros st _. simpl. reflexivity.
Qed.

(** TERSE: *** *)
(** The final bullet of that proof also looks like a candidate for
    automation. *)

Example hoare_asgn_example1'' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto.
Qed.

(** Now we have quite a nice proof script: it simply identifies the
    Hoare rules that need to be used and leaves the remaining
    low-level details up to Rocq to figure out. *)

(** FULL: By now it might be apparent that the _entire_ proof could be
    automated if we added [hoare_consequence_pre] and [hoare_asgn] to
    the hint database.  We won't do that in this chapter, so that we
    can get a better understanding of when and how the Hoare rules are
    used.  In the next chapter, \CHAP{Hoare2}, we'll dive deeper into
    automating entire proofs of Hoare triples. *)

(** TERSE: *** *)
(** The other example of using consequence that we did earlier,
    [hoare_asgn_example2], requires a little more work to automate.
    We can streamline the first line with [eapply], but we can't just use
    [auto] for the final bullet, since it needs [lia]. *)

Example assertion_sub_example2' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto. (* no progress *)
    unfold "->>", assertion_sub, t_update.
    intros st H. simpl in *. lia.
Qed.

(** TERSE: *** *)

(** Let's introduce our own tactic to handle both that bullet and the
    bullet from example 1: *)

Ltac assertion_auto :=
  try auto;  (* as in example 1, above *)
  try (unfold "->>", assertion_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)

(** TERSE: *** *)
Example assertion_sub_example2'' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

(** TERSE: *** *)

Example hoare_asgn_example1''':
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

(** TERSE: *** *)
(** Again, we have quite a nice proof script.  All the low-level
    details of proofs about assertions have been taken care of
    automatically. Of course, [assertion_auto] isn't able to prove
    everything we could possibly want to know about assertions --
    there's no magic here! But it's pretty good. *)

(* FULL *)
(* EX2 (hoare_asgn_examples_2) *)
(** Prove these triples.  Try to make your proof scripts nicely
    automated by following the examples above. *)

Example assertion_sub_ex1' :
  {{ X <= 5 }}
    X := 2 * X
  {{ X <= 10 }}.
Proof.
  (* ADMITTED *)
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.
(* /ADMITTED *)

Example assertion_sub_ex2' :
  {{ 0 <= 3 /\ 3 <= 5 }}
    X := 3
  {{ 0 <= X /\ X <= 5 }}.
Proof.
  (* ADMITTED *)
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.
(* /ADMITTED *)

(* GRADE_THEOREM 1: assertion_sub_ex1' *)
(* GRADE_THEOREM 1: assertion_sub_ex2' *)
(** [] *)

(* LATER: Note here about equivalent preconditions
[[
      {{ X + 1 <= 5 }}  X := X + 1  {{ X <= 5 }}

      {{ 3 = 3 }}  X := 3  {{ X = 3 }}

      {{ 0 <= 3 /\ 3 <= 5 }}  X := 3  {{ 0 <= X /\ X <= 5 }}
]]
*)
(* /FULL *)

(* ####################################################### *)
(** ** Sequencing + Assignment *)

(** Here's an example of a program involving both sequencing and
    assignment.  Note the use of [hoare_seq] in conjunction with
    [hoare_consequence_pre] and the [eapply] tactic. *)

Example hoare_asgn_example3 : forall (a:aexp) (n:nat),
  {{a = n}}
    X := a;
    skip
  {{X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.

(** TERSE: *** *)

(** Informally, a nice way of displaying a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:
[[
              {{ a = n }}
     X := a
              {{ X = n }};    <--- decoration for Q
     skip
              {{ X = n }}
]]
*)
(** We'll come back to the idea of decorated programs in much more
    detail in the next chapter. *)

(* FULL *)
(* EX2! (hoare_asgn_example4) *)
(** Translate this "decorated program" into a formal proof:
[[
                   {{ True }} ->>
                   {{ 1 = 1 }}
    X := 1
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }};
    Y := 2
                   {{ X = 1 /\ Y = 2 }}
]]
   Note the use of "[->>]" decorations, each marking a use of
   [hoare_consequence_pre].

   We've started you off by providing a use of [hoare_seq] that
   explicitly identifies [X = 1] as the intermediate assertion. *)

Example hoare_asgn_example4 :
  {{ True }}
    X := 1;
    Y := 2
  {{ X = 1 /\ Y = 2 }}.
Proof.
  eapply hoare_seq with (Q := {{ X = 1 }}).
  (* ADMITTED *)
  - (* right part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
  - (* left part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (swap_exercise) *)
(** Write an Imp program [c] that swaps the values of [X] and [Y] and
    show that it satisfies the following specification:
[[
      {{X <= Y}} c {{Y <= X}}
]]
    Your proof should not need to use [unfold valid_hoare_triple].

    Hints:
       - Remember that Imp commands need to be enclosed in <{...}>
         brackets.
       - Remember that the assignment rule works best when it's
         applied "back to front," from the postcondition to the
         precondition.  So your proof will want to start at the end
         and work back to the beginning of your program.
       - Remember that [eapply] is your friend.)  *)
(* LATER: One of the OPLSS students noticed that it is quite
   confusing to try to write out the decorated program version of this
   proof. *)
(* HIDE: CH: Here goes:
[[
  {{ X <= Y }}
    Z := X
            {{ Z <= Y }};
    X := Y
            {{ Z <= X }};
    Y := Z
  {{ Y <= X }}
]]
   The _only_ catch is that one needs to do it backwards, since that's
   how the hoare_asgn rule is defined.
   Maybe move this decorated program to the decorated programs
   section, since it's a good warm-up exercise.
*)

Definition swap_program : com
  (* ADMITDEF *) :=
  <{ Z := X; X := Y; Y := Z }>.
  (* /ADMITDEF *)

Theorem swap_exercise :
  {{X <= Y}}
    swap_program
  {{Y <= X}}.
Proof.
  (* ADMITTED *)
  eapply hoare_seq.
  - eapply hoare_seq.
    + apply hoare_asgn.
    + apply hoare_asgn.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX4A (invalid_triple) *)
(* LATER: MRC'20: should this be 3 or 4 stars? *)
(* LATER: BCP 20: We got a LOT of questions about this problem this
   year -- many students clearly find it puzzling.  I added the
   extended hint below to try to help.
*)
(** Show that
[[
    {{ a = n }} X := 3; Y := a {{ Y = n }}
]]
    is not a valid Hoare triple for some choices of [a] and [n].

    Conceptual hint: Invent a particular [a] and [n] for which the
    triple in invalid, then use those to complete the proof.

    Technical hint: Hypothesis [H] below begins [forall a n, ...].
    You'll want to instantiate that with the particular [a] and [n]
    you've invented.  You can do that with [assert] and [apply], but
    you may remember (from \CHAPV1{Tactics.v} in Logical Foundations)
    that Rocq offers an even easier tactic: [specialize].  If you write
[[
       specialize H with (a := your_a) (n := your_n)
]]
    the hypothesis will be instantiated on [your_a] and [your_n].

    Having chosen your [a] and [n], proceed as follows:
     - Use the (assumed) validity of the given hoare triple to derive
       a state [st'] in which [Y] has some value [y1]
     - Use the evaluation rules ([E_Seq] and [E_Asgn]) to show that
       [Y] has a _different_ value [y2] in the same final state [st']
     - Since [y1] and [y2] are both equal to [st' Y], they are equal
       to each other. But we chose them to be different, so this is a
       contradiction, which finishes the proof.
 *)

Theorem invalid_triple : ~ forall (a : aexp) (n : nat),
    {{ a = n }}
      X := 3; Y := a
    {{ Y = n }}.
Proof.
  unfold valid_hoare_triple.
  intros H.
  (* ADMITTED *)
  specialize H with
      (a := AId X) (n := 2)
      (st := (X !-> 2)) (st' := (Y !-> 3; X !-> 3; X !-> 2)).
  simpl in H.
  assert (Heval:
            (X !-> 2) =[ X := 3; Y := X ]=> (Y !-> 3; X !-> 3; X !-> 2)).
  { econstructor; constructor; reflexivity. }
  apply H in Heval.
  - discriminate.
  - reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** ** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?

    Certainly, if the same assertion [Q] holds after executing
    either of the branches, then it holds after the whole conditional.
    So we might be tempted to write:
[[[
              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      ---------------------------------
      {{P}} if b then c1 else c2 {{Q}}
]]]
*)

(** TERSE: *** *)

(** However, this is rather weak. For example, using this rule,
   we cannot show
[[
     {{ True }}
       if X = 0
         then Y := 2
         else Y := X + 1
       end
     {{ X <= Y }}
]]
   since the rule doesn't tell us enough about the state in which the
   assignments take place in the "then" and "else" branches. *)

(** FULL: Fortunately, we can say something more precise.  In the
    "then" branch, we know that the boolean expression [b] evaluates to
    [true], and in the "else" branch, we know it evaluates to [false].
    Making this information available in the premises of the rule gives
    us more information to work with when reasoning about the behavior
    of [c1] and [c2] (i.e., the reasons why they establish the
    postcondition [Q]). *)
(** TERSE: *** *)
(** TERSE: Better: *)
(**
[[[
              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}
]]]
*)

(** TERSE: *** *)

(** FULL: To interpret this rule formally, we need to do a little work.
    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression -- i.e., it
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassertion b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)
(** TERSE: To make this formal, we need a way of formally "lifting"
    any bexp [b] to an assertion.

    We'll write [bassertion b] for the assertion "the boolean expression
    [b] evaluates to [true]." *)

Definition bassertion b : Assertion :=
  fun st => (beval st b = true).

(* TERSE: HIDEFROMHTML *)
Coercion bassertion : bexp >-> Assertion.

(* HIDE: This allows [simpl] to unfold definitions. *)
Arguments bassertion /.

(** A useful fact about [bassertion]: *)

(* SOONER: Robert Rand: This isn't an identity but that's because
   we're using [~(bassertion b st)] in our triples, instead of a more
   direct/intuitive predicate.

   Some alternatives: 1) P_True b and P_False b (defined directly as
   desired) 1) bassertion b false (adds relevant argument to bassertion)
   2) ((bassertion (!b)) st) (clearer, but less direct). *)
Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassertion b) st).
(* FOLD *)
Proof. congruence. Qed.
(* /FOLD *)

Hint Resolve bexp_eval_false : core.

(** FULL: We mentioned the [congruence] tactic in passing in
    \CHAPV1{Auto} when building the [find_rwd] tactic.  Like
    [find_rwd], [congruence] is able to automatically find that both
    [beval st b = false] and [beval st b = true] are being assumed,
    notice the contradiction, and [discriminate] to complete the
    proof. *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
(** That is (unwrapping the notations):
[[
      Theorem hoare_if : forall P Q b c1 c2,
        {{fun st => P st /\ bassertion b st}} c1 {{Q}} ->
        {{fun st => P st /\ ~ (bassertion b st)}} c2 {{Q}} ->
        {{P}} if b then c1 else c2 end {{Q}}.
]]
*)
(* FOLD *)
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.
(* /FOLD *)

(** *** Example *)

(** FULL: Here is a formal proof that the program we used to motivate
    the rule satisfies the specification we wanted. *)

Example if_example :
  {{True}}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto. (* no progress *)
      unfold "->>", assertion_sub, t_update, bassertion.
      simpl. intros st [_ H]. apply eqb_eq in H.
      rewrite H. lia.
  - (* Else *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.

(** TERSE: *** *)

(** As we did earlier, it would be nice to eliminate all the low-level
    proof script that isn't about the Hoare rules.  Unfortunately, the
    [assertion_auto] tactic we wrote wasn't quite up to the job.  Looking
    at the proof of [if_example], we can see why.  We had to unfold a
    definition ([bassertion]) and use a theorem ([eqb_eq]) that we didn't
    need in earlier proofs.  So, let's add those into our tactic, and
    clean it up a little in the process. *)

(* HIDE: MRC'20: There's probably a better way to engineer this.
   I don't know Ltac very well though. *)
Ltac assertion_auto' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.

(** TERSE: *** *)

(** Now the proof is quite streamlined. *)

Example if_example'' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
Qed.

(** TERSE: *** *)
(** We can even shorten it a little bit more. *)

Example if_example''' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if; eapply hoare_consequence_pre;
    try apply hoare_asgn; try assertion_auto'.
Qed.

(** TERSE: *** *)
(** For later proofs, it will help to extend [assertion_auto'] to handle
    inequalities, too. *)

Ltac assertion_auto'' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;  (* for inequalities *)
  auto; try lia.

(* FULL *)
(* EX2 (if_minus_plus) *)
(** Prove the theorem below using [hoare_if].  Do not use [unfold
    valid_hoare_triple].  The [assertion_auto''] tactic we just
    defined may be useful. *)

Theorem if_minus_plus :
  {{True}}
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  {{Y = X + Z}}.
Proof.
  (* ADMITTED *)
  apply hoare_if; eapply hoare_consequence_pre;
    try apply hoare_asgn; try assertion_auto''.
Qed.
(* /ADMITTED *)
(* /FULL *)
(** [] *)

(* FULL *)
(* ####################################################### *)
(** *** Exercise: One-sided conditionals *)

(* HIDE: Question from 2012, Midterm 2. One-sided conditionals. *)
(** In this exercise we consider extending Imp with "one-sided
    conditionals" of the form [if1 b then c end]. Here [b] is a boolean
    expression, and [c] is a command. If [b] evaluates to [true], then
    command [c] is evaluated. If [b] evaluates to [false], then [if1 b
    then c end] does nothing.

    We recommend that you complete this exercise before attempting the
    ones that follow, as it should help solidify your understanding of
    the material. *)

(** The first step is to extend the syntax of commands and introduce
    the usual notations.  (We've done this for you, in a separate
    module to prevent polluting the global name space.) *)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'if1' x 'then' y 'end'" :=
         (CIf1 x y)
             (in custom com at level 0, x custom com at level 99).
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

(* EX2! (if1_ceval) *)

(** Add two new evaluation rules to relation [ceval], below, for
    [if1]. Let the rules for [if] guide you. *)

(* INSTRUCTORS: Copy of template eval *)
(* HIDEFROMHTML *)
Reserved Notation
         "st0 '=[' c ']=>' st1 '/' s"
         (at level 40, c custom com at level 99,
          st0 constr, st1 constr at next level,
          format "'[hv' st0  =[ '/  ' '[' c ']' '/' ]=>  st1 / s ']'").

(* /HIDEFROMHTML *)

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
(* SOLUTION *)
  | E_If1True : forall (st st' : state) (b : bexp) (c : com),
                beval st b = true ->
                st =[ c ]=> st' ->
                st =[ if1 b then c end ]=> st'
  | E_If1False : forall (st : state) (b : bexp) (c : com),
                 beval st b = false ->
                 st =[ if1 b then c end ]=> st
(* /SOLUTION *)

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

(** The following unit tests should be provable simply by [eauto] if
    you have defined the rules for [if1] correctly. *)

Example if1true_test :
  empty_st =[ if1 X = 0 then X := 1 end ]=> (X !-> 1).
Proof. (* ADMITTED *) eauto. Qed. (* /ADMITTED *)

Example if1false_test :
  (X !-> 2) =[ if1 X = 0 then X := 1 end ]=> (X !-> 2).
Proof. (* ADMITTED *) eauto. Qed. (* /ADMITTED *)

(* GRADE_THEOREM 1: if1true_test *)
(* GRADE_THEOREM 1: if1false_test *)

(** [] *)

(** Now we have to repeat the definition and notation of Hoare triples,
    so that they will use the updated [com] type. *)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
       st =[ c ]=> st' ->
       P st  ->
       Q st'.

Hint Unfold valid_hoare_triple : core.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

(* EX2M (hoare_if1) *)

(** Invent a Hoare logic proof rule for [if1].  State and prove a
    theorem named [hoare_if1] that shows the validity of your rule.
    Use [hoare_if] as a guide. Try to invent a rule that is
    _complete_, meaning it can be used to prove the correctness of as
    many one-sided conditionals as possible.  Also try to keep your
    rule _compositional_, meaning that any Imp command that appears
    in a premise should syntactically be a part of the command
    in the conclusion.

    Hint: if you encounter difficulty getting Rocq to parse part of
    your rule as an assertion, try manually indicating that it should
    be in the assertion scope.  For example, if you want [e] to be
    parsed as an assertion, write it as [(e)%assertion]. *)

(* SOLUTION *)
Theorem hoare_if1 : forall (b : bexp) (c : com) (P Q : Assertion),
  {{ P /\ b }} c {{ Q }} ->
  {{ P /\  ~b }} ->> Q ->
  {{ P }} (if1 b then c end) {{ Q }}.
Proof.
  intros b c P Q Htrue Hfalse st st' Heval Hpre.
  inversion Heval; subst; eauto.
Qed.
(* /SOLUTION *)

(** For example ([hoare_if1_good]) your rule should be strong
    enough to show the following Hoare triple is valid:
[[
  {{ X + Y = Z }}
    if1 Y <> 0 then
      X := X + Y
    end
  {{ X = Z }}
]]
*)
(* GRADE_MANUAL 2: hoare_if1 *)
(** [] *)

(** Before the next exercise, we need to restate the Hoare rules of
    consequence (for preconditions) and assignment for the new [com]
    type. *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X := a) {{Q}}.
Proof.
  intros Q X a st st' Heval HQ.
  inversion Heval; subst.
  auto.
Qed.

(* EX2 (hoare_if1_good) *)

(** Use your [if1] rule to prove the following (valid) Hoare triple.

    Hint: [assertion_auto''] will once again get you most but not all
    the way to a completely automated proof.  You can finish manually,
    or tweak the tactic further.

    Hint: If you see a message like [Unable to unify "Imp.ceval
    Imp.CSkip st st'" with...], it probably means you are using a
    definition or theorem [e.g., hoare_skip] from above this exercise
    without re-proving it for the new version of Imp with if1. *)

(* QUIETSOLUTION *)
Ltac assertion_auto''' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> negb_true_iff in *;  (* new *)
  try rewrite -> not_false_iff_true in *;  (* new *)
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;
  auto; try lia.
(* /QUIETSOLUTION *)

(* SOONER: BCP 21: Not quite fair to give them a 2-point exercise
   where our solution uses a custom Ltac... *)
Lemma hoare_if1_good :
  {{ X + Y = Z }}
    if1 Y <> 0 then
      X := X + Y
    end
  {{ X = Z }}.
Proof. (* ADMITTED *)
  apply hoare_if1.
  - eapply hoare_consequence_pre; try apply hoare_asgn; try assertion_auto'''.
  - assertion_auto'''.
Qed.
(* /ADMITTED *)
(** [] *)

End If1.
(* /FULL *)

(* ####################################################### *)
(** ** While Loops *)

(** The Hoare rule for [while] loops is based on the idea of a
    _command invariant_ (or just _invariant_): an assertion whose
    truth is guaranteed after executing a command, assuming it is true
    before.

    That is, an assertion [P] is a command invariant of [c] if
[[
      {{P}} c {{P}}
]]
    holds.  Note that the command invariant might temporarily become
    false in the middle of executing [c], but by the end of [c] it
    must be restored. *)

(** FULL:  As a first attempt at a [while] rule, we could try:

[[
             {{P}} c {{P}}
      ---------------------------
      {{P} while b do c end {{P}}
]]

    This rule is valid: if [P] is a command invariant of [c], as the
    premise requires, then, no matter how many times the loop body
    executes, [P] is going to be true when the loop finally finishes.

    But the rule also omits two crucial pieces of information.  First,
    the loop terminates when [b] becomes false.  So we can strengthen
    the postcondition in the conclusion:

[[
              {{P}} c {{P}}
      ---------------------------------
      {{P} while b do c end {{P /\ ~b}}
]]

    Second, the loop body will be executed only if [b] is true.  So we
    can also strengthen the precondition in the premise:

[[
            {{P /\ b}} c {{P}}
      --------------------------------- (hoare_while)
      {{P} while b do c end {{P /\ ~b}}
]]
*)

(** TERSE: *** *)
(** TERSE: The Hoare while rule combines the idea of a command invariant with
     information about when guard [b] does or does not hold.
[[[
            {{P /\ b}} c {{P}}
      --------------------------------- (hoare_while)
      {{P} while b do c end {{P /\ ~b}}
]]]
*)

(** FULL: That is the Hoare [while] rule.  Note how it combines
    aspects of [skip] and conditionals:

    - If the loop body executes zero times, the rule is like [skip] in
      that the precondition survives to become (part of) the
      postcondition.

    - Like a conditional, we can assume guard [b] holds on entry to
      the subcommand. *)

(* HIDE: The big comment will not display nicely.  But I guess it's
   folded... *)
Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
(* FOLD *)
Proof.
  intros P b c Hhoare st st' Heval HP.
  (* We proceed by induction on [Heval], because, in the "keep
     looping" case, its hypotheses talk about the whole loop instead
     of just [c]. The [remember] is used to keep the original command
     in the hypotheses; otherwise, it would be lost in the
     [induction]. By using [inversion] we clear away all the cases
     except those involving [while]. *)
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval;
    try (inversion Horig; subst; clear Horig);
    eauto.
Qed.
(* /FOLD *)

(** TERSE: *** *)

(* SOONER: BCP 21: This definition / discussion could be clearer. *)

(* SOONER: BCP 23: Maja says: The wording of "we will never enter the
   loop" could definitely be improved. As is, it suggests a situation
   where the loop condition itself can never be satisfied. I suspect that
  a previous draft included a discussion that explicitly placed {{P}}
  before the while, perhaps along the lines of "a loop invariant P of
  [while b do c end] is also an invariant of [while b do c end]" (which
  is, FWIW, a (somewhat obtuse) way of stating a weaker variant of
  hoare_while, without the ~b in the postcondition). Combined with the
  fact that it is supposed to justify a somewhat surprising and
  unexpected fact — [X = 0] is not what I would intuitively consider an
  invariant of this loop — this sentence ends up being quite confusing.
  I only understood it when I came back to find this excerpt. *)

(** We call [P] a _loop invariant_ of [while b do c end] if
[[
      {{P /\ b}} c {{P}}
]]
    is a valid Hoare triple.

    This means that [P] will be true at the end of the loop body
    whenever the loop body executes. If [P] contradicts [b], this
    holds trivially since the precondition is false.

    For instance, [X = 0] is a loop invariant of
[[
      while X = 2 do X := 1 end
]]
    since the program will never enter the loop. *)

(* QUIZ *)
(** Is the assertion
[[
    Y = 0
]]
    a loop invariant of the following?
[[
    while X < 100 do X := X + 1 end
]]

    (A) Yes

    (B) No
*)
(* /QUIZ *)
(* INSTRUCTORS: YES *)
(* QUIZ *)
(** Is the assertion
[[
    X = 0
]]
    a loop invariant of the following?
[[
    while X < 100 do X := X + 1 end
]]

    (A) Yes

    (B) No
*)
(* /QUIZ *)
(* INSTRUCTORS: NO *)
(* QUIZ *)
(** Is the assertion
[[
    X < Y
]]
    a loop invariant of the following?
[[
    while true do X := X + 1; Y := Y + 1 end
]]

    (A) Yes

    (B) No
*)
(* /QUIZ *)
(* INSTRUCTORS: Yes *)
(* QUIZ *)
(** Is the assertion
[[
    X = Y + Z
]]
    a loop invariant of the following?
[[
    while Y > 10 do Y := Y - 1; Z := Z + 1 end
]]
    (A) Yes

    (B) No
*)
(* /QUIZ *)
(* INSTRUCTORS: YES *)
(* SOONER: This last quiz should be turned into a discussion in the
   text, at least in the full version -- indeed, maybe all these
   should be turned into a long discussion of what it means to be a
   loop invariant -- I think that would be pretty helpful. *)

(** FULL: The program
[[
    while Y > 10 do Y := Y - 1; Z := Z + 1 end
]]
    admits an interesting loop invariant:
[[
    X = Y + Z
]]
    Note that this doesn't contradict the loop guard but neither
    is it a command invariant of
[[
    Y := Y - 1; Z := Z + 1
]]
    since, if X = 5,
    Y = 0 and Z = 5, running the command will set Y + Z to 6. The
    loop guard [Y > 10] guarantees that this will not be the case.
    We will see many such loop invariants in the following chapter.
*)

(* HIDE *)
    (** For now, you have to accept on faith that the [hoare_while] rule
        is "powerful enough". It can be shown that the proof rules we
        develop here for Hoare logic are _complete_, in the sense that any
        valid Hoare triple can be proved simply by application of these
        theorems and an oracle for the underlying logic. In particular,
        given any while loop and a valid Hoare triple for it, it is always
        possible to find a loop invariant [P] that leads to the proof.

        We are not going to prove completeness formally here, but the
        exercises below should get you comfortable with identifying
        loop invariants in practice. *)

    (** Mukund: Possible motivation for [hoare_while]? *)

    (** CH: Maybe the [while] could indeed be explained better, but ...
        The examples you propose here are one order or magnitude more
        complex than any of the examples considered in this whole file,
        and they use language features that are beyond the scope of this
        course (arrays). Also, you don't explain at all how to come up
        with loop invariants, you just take extremely complicated
        invariants out of the hat. Finally, this whole discussion about
        loop invariants better belongs to the decorated programs section
        where loop invariants are first used. *)

    (** Let's look at the pseudo-code for two common procedures in
        introductory algorithms courses: insertion sort, and Euclid's GCD
        finding algorithm.

        Given: An array of n integers a[1...n].
        To calculate: Return an array A[1...n], containing the elements
          of a in sorted order.
        Do:
          Copy array a into A.
          Initialize i := 0.
          While i < n,
            Let j := i.
            While j > 0,
              Compare A[j] and A[j + 1].
              Swap if A[j] > A[j + 1].
            end
          end.

        Consider the following claim made of insertion sort. Always, just
        before the condition [i < n] is evaluated in the outer while loop,
        the following conditions hold:

        1. The elements A[1...i] are in sorted order.
        2. A[1...i] are a permutation of the elements a[1...i].
        3. The elements A[(i + 1)...n] are each equal to the elements of
           a[(i + 1)...n].
        4. i <= n.

        Observe that these conditions hold the first time the loop condition
        is evaluated. Also, if they hold before the loop body is evaluated,
        then they should hold afterwards. Thus, the conditions form a
        _loop invariant_.

        But why are they helpful? We now know that they hold after any finite
        number of iterations of the loop. In particular, they hold when
        (and if) the loop terminates. What happens then? Since the loop has
        terminated, we know that [i ~< n], and so [i = n]. Substituting n
        for i, we get that A[1...n] are a permutation of a[1...n], and in
        sorted order. And thus, (if insertion sort terminates), it is correct.

        Given: Two positive integers, a and b.
        To find: gcd(a, b)
        Do:
          Let A := a, B := b.
          If A = 0, return B.
          While B ~= 0,
            If A > B,
              A := A - B
            else
              B := B - A
            fi
          end
          Return A.

        We make the claim, just before the evaluation of the loop condition,
        the following condition always holds: "gcd(A, B) = gcd(a, b)".

        It is true at the beginning, and if they hold before executing the
        loop body, then they hold afterwards as well.

        This loop invariant allows us to prove the correctness of the algorithm:
        when the loop terminates, we know that gcd(A, B) = gcd(a, b), and that
        B = 0. But for all x, gcd(x, 0) = x, and so gcd(A, B) = gcd(A, 0) = A.
        Thus, A = gcd(a, b).

        In both cases, we did not answer the question: "Does this procedure
        always terminate?" But partial correctness is also a feature of Hoare
        logic -- we assume [st =[ c ]=> st'] before checking whether [st']
        satisfies the postcondition.

        The purpose of these two (extremely) informal proofs was to
        convince you that loop invariants are a common design pattern while
        proving the correctness of programs.

        We try to abstract this pattern into a Hoare rule.

        1. The loop invariant is itself an assertion [P]. Since it must
           hold at the beginning, [P] must be the precondition of the
           Hoare triple.
        2. The loop invariant is preserved by the loop body, but at termination,
           we know something more: recall how we finished the
           gcd-correctness proof -- "when the loop terminates, ..., and
           that B = 0. ..." Thus, the post-condition is [P /\ ~ b], where
           [b] is the loop condition.
        3. What do we demand of the loop body [c]? [{{ P }} c {{ P }}]
           might be a good first guess, since we want [P] to be
           invariant after [c]. But remember that we asserted [P] before evaluating
           the loop condition, and so we know that [b] must have
           evaluated to true. Thus, we want the loop body to satisfy
           the Hoare triple: [{{ P /\ b }} c {{ P }}].

        Putting these together, we get the Hoare proof rule for while:

    [[[
                   {{P /\ b}} c {{P}}
            ----------------------------------  (hoare_while)
            {{P}} while b do c end {{P /\ ~ b}}
    ]]]
    *)

(* /HIDE *)

(* FULL *)
(* SOONER: BCP 21: What is this example doing here?? Needs some text. *)
Example while_example :
  {{X <= 3}}
    while (X <= 2) do
      X := X + 1
    end
  {{X = 3}}.
(* FOLD *)
 Proof.
  eapply hoare_consequence_post.
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - assertion_auto''.
Qed.
(* /FOLD *)
(* /FULL *)

(* HIDE: CJC: Maybe also a good place to talk about the structure of
   our logic - that we've set up the hoare_* lemmas and they are all
   the reasoning about Hoare triples that they should have to use (in
   both formal or informal proofs)?  Probably should talk about this
   somewhere or else we'll get back lots of proofs that unfold
   valid_hoare_triple and reason at a low level everywhere.

   BCP 21: I think we do this now? *)

(* HIDE *)
    (* LATER: Next year, these should be moved up to the section on
       valid Hoare triples and proved directly there (using, in the
       second case, the fact that this loop does not terminate),
       rather than using the while rule. *)
    (* LATER: Point out the trick using intros to do the splitting. *)
    Theorem never_loop_hoare: forall P c,
      {{P}} while false do c end {{P}}.
    Proof.
      intros P c.
      eapply hoare_consequence_post.
      - apply hoare_while.
        (* loop body preserves loop invariant *)
        apply hoare_pre_false.
        intros st [HP HFalse]. inversion HFalse.
      - (* loop invariant and negation of guard imply postcondition *)
        simpl. intros st [Hinv Hguard]. assumption.
    Qed.
(* /HIDE *)

(* QUIZ *)
(** Is the assertion
[[
    X > 0
]]
    a loop invariant of the following?
[[
    while X = 0 do X := X - 1 end
]]

    (A) Yes

    (B) No
*)
(* INSTRUCTORS: BCP: According to how we defined the term, the answer
   should be Yes!  The reason is that a loop invariant is defined as a
   P that, _together with the fact that the guard is true_ implies
   P. *)
(* /QUIZ *)
(* QUIZ *)
(** Is the assertion
[[
    X < 100
]]
    a loop invariant of the following?
[[
    while X < 100 do X := X + 1 end
]]

    (A) Yes

    (B) No
*)
(* /QUIZ *)
(* INSTRUCTORS: NO *)
(* QUIZ *)
(** Is the assertion
[[
    X > 10
]]
    a loop invariant of the following?
[[
    while X > 10 do X := X + 1 end
]]

    (A) Yes

    (B) No
*)
(* /QUIZ *)
(* INSTRUCTORS: YES *)

(* FULL *)
(** If the loop never terminates, any postcondition will work. *)

(* INSTRUCTORS: This is good to work in class, but make sure you try
   it yourself beforehand!  Getting it to work smoothly depends on
   doing the right things at the beginning.

   MRC'20: Maybe I'm an outlier, but a WORKINCLASS that surprises me
   and maybe gets me stuck is not ideal. The truly interesting thing
   about this example is that it's provable --not the actual proof.
   I propose that it not be worked in class, but that the proof
   be provided.

   BCP 20: OK, fair enough. *)
(* LATER: MRC'20: It would be nice to automate the second bullet. *)
Theorem always_loop_hoare : forall Q,
  {{True}} while true do skip end {{Q}}.
(* FOLD *)
Proof.
  intros Q.
  eapply hoare_consequence_post.
  - apply hoare_while. apply hoare_post_true. auto.
  - simpl. intros st [Hinv Hguard]. congruence.
Qed.
(* /FOLD *)
(* /FULL *)

(* HIDE *)
(* A different way through the proof... *)
Theorem always_loop_hoare' : forall P Q,
  {{P}} while true do skip end {{Q}}.
  intros P Q.
  apply hoare_consequence_pre with (P' := (True:Assertion)).
  - eapply hoare_consequence_post.
    + apply hoare_while.
      (* Loop body preserves loop invariant *)
      apply hoare_post_true. intros st. apply I.
    +  (* Loop invariant and negated guard imply postcondition *)
      simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. reflexivity.
  - (* Precondition implies loop invariant *)
    intros st H. constructor.  Qed.

(* And, of course, there is also the low-level way to do it, without using
   Hoare logic... *)
Theorem always_loop_hoare'' : forall P Q,
  {{P}} while true do skip end {{Q}}.
Proof.
  intros. unfold valid_hoare_triple.
  intros. remember <{ while true do skip end}> as c.
  induction H; inversion Heqc; subst.
  - inversion H.
  - apply IHceval2; [reflexivity | inversion H1; subst; assumption].
Qed.
(* ... But this really misses the point! *)
(* /HIDE *)

(** FULL: Of course, this result is not surprising if we remember that
    the definition of [valid_hoare_triple] asserts that the postcondition
    must hold _only_ when the command terminates.  If the command
    doesn't terminate, we can prove anything we like about the
    post-condition.

    Hoare rules that specify what happens _if_ commands terminate,
    without proving that they do, are said to describe a logic of
    _partial_ correctness.  It is also possible to give Hoare rules
    for _total_ correctness, which additionally specifies that
    commands must terminate. Total correctness is out of the scope of
    this textbook. *)

(* FULL *)
(* ####################################################### *)
(** *** Exercise: [REPEAT] *)
(* HIDE: I (BCP) think I see a much simpler way to do the 'for' stuff.
   Instead of [for x from a to b do c] define [for x downfrom a do c]
   that steps from a down to 0.  This will be much simpler to specify,
   though still an interesting challenge. (CJC: This still seemed hard
   to me, but I'm deleting it for now to get things looking right)
*)
(* HIDE: Coming up with the precise rule for REPEAT is tricky, and so
   is proving formally that the precise rule passes the litmus
   test (at this point we only ask them to convince themselves
   informally there).
*)
(* LATER: PLW: Chapters Imp and Equiv have exercises based on extending
   Imp with C-style FOR loops. Either this chapter should use C-style
   for loops in place of repeat, or those chapters should use repeat
   in place of C-style for loops. *)
(* LATER: BCP 20: I think this exercise is not actually very nice --
   the hoare rule for repeat is really not that nice.  Let's do
   replace with FOR-DOWNTO as suggested.
   BCP 21: For the moment, I'm making it optional. *)

(* EX4AM? (hoare_repeat) *)
(** In this exercise, we'll add a new command to our language of
    commands: [REPEAT] c [until] b [end]. You will write the
    evaluation rule for [REPEAT] and add a new Hoare rule to the
    language for programs involving it.  (You may recall that the
    evaluation rule is given in an example in the \CHAPV1{Auto} chapter.
    Try to figure it out yourself here rather than peeking.) *)

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [while], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Notation "'repeat' e1 'until' b2 'end'" :=
          (CRepeat e1 b2)
              (in custom com at level 0,
               e1 custom com at level 99, b2 custom com at level 99).
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

(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [while] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true. *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
(* SOLUTION *)
  | E_RepeatEnd : forall st st' b c,
      ceval st c st' ->
      beval st' b = true ->
      st =[ repeat c until b end ]=> st'
  | E_RepeatLoop : forall st st' st'' b c,
      ceval st c st' ->
      beval st' b = false ->
      st' =[ repeat c until b end ]=> st'' ->
      st =[ repeat c until b end ]=> st''
(* /SOLUTION *)

where "st '=[' c ']=>' st'" := (ceval st c st').

(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)

Definition valid_hoare_triple (P : Assertion) (c : com) (Q : Assertion)
                        : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

(** To make sure you've got the evaluation rules for [repeat] right,
    prove that [ex1_repeat] evaluates correctly. *)

Definition ex1_repeat :=
  <{ repeat
       X := 1;
       Y := Y + 1
     until (X = 1) end }>.

Theorem ex1_repeat_works :
  empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
Proof.
  (* ADMITTED *)
  apply E_RepeatEnd.
  - eapply E_Seq.
    + apply E_Asgn. reflexivity.
    + apply E_Asgn. reflexivity.
  - reflexivity. Qed.
  (* /ADMITTED *)

(** Now state and prove a theorem, [hoare_repeat], that expresses an
    appropriate proof rule for [repeat] commands.  Use [hoare_while]
    as a model, and try to make your rule as precise as possible. *)

(* SOLUTION *)

(** Here is a very precise version of [hoare_repeat]. *)
(* LATER: A student in 2013 pointed out that this rule is OK as far
   as it goes, but it isn't going to lead to a nice rule for decorated
   programs, when we get to that, because it uses c twice, perhaps in
   different ways! *)

Theorem hoare_repeat : forall P Q (b:bexp) c,
  {{ P }} c {{ Q }} ->
  {{ Q /\ ~ b }} c {{ Q }} ->
  {{ P }} repeat c until b end {{ Q /\ b }}.
Proof.
  intros.
  remember <{ repeat c until b end }> as cr. unfold valid_hoare_triple.
  intros. generalize dependent P.
  induction H1; inversion Heqcr; subst; intros.

  - (* E_RepeatEnd *)
    split; [ apply H2 with (st := st) |]; assumption.

  - (* E_RepeatLoop *)
    apply IHceval2 with (P := {{ Q /\ ~b }});
    [ reflexivity | assumption |].
    split.
    + unfold valid_hoare_triple in H1; apply H1 with (st := st); assumption.
    + unfold bassertion. unfold not. intros.
      destruct (beval st' b); [ inversion H | inversion H3 ].
Qed.
(* /SOLUTION *)

(** For full credit, make sure (informally) that your rule can be used
    to prove the following valid Hoare triple:
[[
  {{ X > 0 }}
    repeat
      Y := X;
      X := X - 1
    until X = 0 end
  {{ X = 0 /\ Y > 0 }}
]]
*)
(* QUIETSOLUTION *)

(** Although it was not required by the exercise, we can show formally
    that [hoare_repeat] can handle this litmus test: *)

Definition ex2_repeat :=
  <{ repeat
       Y := X;
       X := X - 1
     until (X = 0) end }>.

(** Before we can show anything about this program we need to repeat
    the proofs of some more Hoare rules from above (remember we're in
    a separate module, with a different definition of commands). *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold valid_hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assertion_sub in HQ. assumption.  Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  intros st st' Hc HP.
  apply HQ'Q. apply (Hht st st').
  - assumption.
  - apply HPP'. assumption.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(** Now we are ready to show [ex2_repeat] correct using [hoare_repeat]. *)
(* NOTATION: IY -- I've noticed this oddity in previous lemmas, but
   it's especially noticable here that an explicit state is given to
   the conditional statements. *)
Lemma ex2_repeat_hoare_repeat :
  {{ X > 0 }}
    ex2_repeat
  {{ X = 0 /\ Y > 0 }}.
Proof.
  unfold ex2_repeat.
  eapply hoare_consequence.
  - apply hoare_repeat with (Q := {{ Y > 0 }}).
    + eapply hoare_seq; apply hoare_asgn.
    + eapply hoare_seq.
      * apply hoare_asgn.
      * eapply hoare_consequence_pre.
        -- apply hoare_asgn.
        -- unfold assert_implies. intros.
           unfold assertion_sub. simpl.
           rewrite t_update_neq; [| (intro X; inversion X)]. rewrite t_update_eq.
           destruct H as [H1 H2]. unfold bassertion in H2.
           rewrite not_true_iff_false in H2. simpl in H2.
           apply eqb_neq in H2. lia.
  - (* body of repeat if exiting right away *)
    unfold assert_implies. intros st H. unfold assertion_sub. simpl.
    rewrite t_update_neq; [| (intro X; inversion X)].
    rewrite t_update_eq. assumption.
  - (* final postcondition *)
    unfold assert_implies. intros. unfold bassertion in H. simpl in H.
    destruct H as [H1 H2]. apply eqb_eq in H2.
    split; assumption.
Qed.

(** A sound but less precise variant of the [hoare_repeat] rule looks
    like this: *)

(* NOTATION: Here, too, the printing isn't as we write the notation.
   (As soon as we start the proof context). Is this intended? *)
Lemma hoare_repeat' : forall P b c,
  {{P}} c {{P}} ->
  {{P}} repeat c until b end {{ P /\ b }}.
Proof.
  unfold valid_hoare_triple.
  intros P b c H st st' He HP.
  remember <{ repeat c until b end }> as rcom.
  induction He; try (inversion Heqrcom); subst.
  - (* E_RepeatEnd *)
    split.
    + apply H with st; assumption.
    + assumption.
  - (* E_RepeatLoop *)
    assert (P st'' /\ bassertion b st'') as C2.
    { (* Proof of assertion *) apply IHHe2.
      + reflexivity.
      + apply H with st; assumption. }
    inversion C2.
    split; assumption.
Qed.

(** First, let's show that [hoare_repeat'] is implied by [hoare_repeat]. *)

Lemma hoare_repeat_implies_hoare_repeat' :
  (forall P Q (b:bexp) c,
  {{ P }} c {{ Q }} ->
  {{ Q /\ ~ b }} c {{ Q }} ->
  {{ P }} repeat c until b end {{ Q /\ b }})
  ->
  (forall P b c,
  {{P}} c {{P}} ->
  {{P}} repeat c until b end {{ P /\  b}}).
Proof.
  intro hoare_repeat. intros. apply hoare_repeat; try assumption.
  eapply hoare_consequence_pre; try eassumption.
  unfold assert_implies. intros. destruct H0. assumption.
Qed.

(* However, we can't prove [ex2_repeat] correct using [hoare_repeat'],
   even with a stronger initial precondition on [Y]. Here is a first
   failed proof attempt. *)

Lemma ex2_repeat_hoare_repeat'_fails1 :
  {{ X > 0 /\  Y > 0}}
    ex2_repeat
  {{ X = 0 /\  Y > 0}}.
Proof.
  eapply hoare_consequence.
  - apply hoare_repeat' with (P := {{ Y > 0 }}).
    eapply hoare_seq.
    + apply hoare_asgn.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * (* body of repeat if looping *)
        unfold assert_implies. intros.
        unfold assertion_sub. simpl.
        rewrite t_update_neq; [| (intro X; inversion X)]. rewrite t_update_eq.
        admit. (* loop invariant too weak on its own,
              we need the value of the previous guard *)
  - (* initial precondition *)
    unfold assert_implies. intros. destruct H. assumption.
    (* this only works with an additional Y > 0 precondition *)
  - (* final postcondition *)
    unfold assert_implies. intros. unfold bassertion in H. simpl in H.
    destruct H as [H1 H2]. apply eqb_eq in H2.
    split; assumption.
Abort.

(* Here is a second failed attempt trying stronger loop invariant, but
   it is too strong. *)

Lemma ex2_repeat_hoare_repeat'_fails2 :
  {{ X > 0 /\ Y > 0}}
    ex2_repeat
  {{ X = 0 /\ Y > 0}}.
Proof.
  eapply hoare_consequence.
  - apply hoare_repeat' with (P := {{ X > 0 /\ Y > 0 }}).
    eapply hoare_seq.
    + apply hoare_asgn.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
        (* body of repeat if looping *)
      * simpl. unfold assert_implies. intros.
        unfold assertion_sub.
        repeat rewrite t_update_eq.
        rewrite t_update_neq; [| (intro X; inversion X)].
        rewrite t_update_eq. simpl.
        rewrite t_update_neq; [| (intro X; inversion X)].
        admit. (* loop invariant too strong *)
  - (* initial precondition *)
    unfold assert_implies. intros. assumption.
  - (* final postcondition *)
    unfold assert_implies. intros. unfold bassertion in H. simpl in H.
    destruct H as [ [H1 H2] H3]. apply eqb_eq in H3.
    split; assumption.
Abort.

(* /QUIETSOLUTION *)
End RepeatExercise.

(* GRADE_MANUAL 6: hoare_repeat *)
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** * Summary *)

(* LATER: Full version could use some more text. *)

(** FULL: So far, we've introduced Hoare Logic as a tool for reasoning about
    Imp programs. *)
(** The rules of Hoare Logic are:
[[[
             --------------------------- (hoare_asgn)
             {{Q [X |-> a]}} X:=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} skip {{ P }}

               {{ P }} c1 {{ Q }}
               {{ Q }} c2 {{ R }}
              ----------------------  (hoare_seq)
              {{ P }} c1;c2 {{ R }}

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} while b do c end {{P /\ ~ b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
]]]
 *)

(** TERSE: *** *)

(** Our main task in this chapter has been to _define_ the rules of
    Hoare logic, and prove that the definitions are sound.  Having
    done so, we can go on and work _within_ Hoare logic to prove that
    particular programs satisfy particular Hoare triples.  In the next
    chapter, we'll see how Hoare logic is can be used to prove that
    more interesting programs satisfy interesting specifications of
    their behavior.

    Crucially, we will do so without ever again [unfold]ing the
    definition of Hoare triples -- i.e., we will take the rules of
    Hoare logic as a closed world for reasoning about programs. *)

(* FULL *)
(* ####################################################### *)
(** * Additional Exercises *)

(* LATER: Possible exercise: Show that TRUE and FALSE are loop invariants
   of every while loop.  Explain why this is not useful. *)
(* LATER: Another interesting problem that we could try to work out in detail:
   total-correctness Hoare Logic.  The crucial rule would be something like this:

                 T not in vars(c)
         [P /\ b /\ a = T] c [P /\ a < T]
         --------------------------------
          [P] while b do c end [P /\ ~ b]

   We could define TC-triples, ask them to prove this rule, and then in
   Hoare2.v, as them to carry out some proofs as decorated programs.
   (Asking them to prove this rule might be a bit much, though -- probably
   requires some fanciness with Rocq...) *)

(** ** Havoc *)

(** In this exercise, we will derive proof rules for a [HAVOC]
    command, which is similar to the nondeterministic [any] expression
    from the the \CHAP{Imp} chapter.

    First, we enclose this work in a separate module, and recall the
    syntax and big-step semantics of Himp commands. *)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

Notation "'havoc' l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).
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


Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_Havoc : forall st x n,
      st =[ havoc x ]=> (x !-> n ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

(** The definition of Hoare triples is exactly as before. *)

Definition valid_hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Hint Unfold valid_hoare_triple : core.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

(** And the precondition consequence rule is exactly as before. *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof. eauto. Qed.

(* EX3A (hoare_havoc) *)
(* SOONER: BCP 21: This exercise turns out to be quite hard -- a lot
   of people get stuck.  We should make it advanced the next time
   through.  BCP 23: Made it advanced.  Can we also explain it better? *)

(** Complete the Hoare rule for [HAVOC] commands below by defining
    [havoc_pre], and prove that the resulting rule is correct. *)

Definition havoc_pre (X : string) (Q : Assertion) (st : total_map nat) : Prop
  (* ADMITDEF *) :=
  forall (n : nat), assertion_sub X <{n}> Q st.
(* /ADMITDEF *)

Theorem hoare_havoc : forall (Q : Assertion) (X : string),
  {{ $(havoc_pre X Q) }} havoc X {{ Q }}.
Proof.
  (* ADMITTED *)
  unfold valid_hoare_triple, havoc_pre.
  intros Q X st st' Heval Hpre.
  inversion Heval; subst. apply Hpre.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3A (havoc_post) *)
(** Complete the following proof without changing any of the provided
    commands. If you find that it can't be completed, your definition of
    [havoc_pre] is probably too strong. Find a way to relax it so that
    [havoc_post] can be proved.

    Hint: the [assertion_auto] tactics we've built won't help you here.
    You need to proceed manually. *)
(* INSTRUCTORS: for example, {{ false }} HAVOC X {{ P }} would
   be a sound but incomplete rule in which the precondition is
   too strong. *)
(* LATER: MRC'20: sure would be nice to automate this better. *)
(* INSTRUCTORS: can't unfold [havoc_pre] outside the ADMITTED block,
   because its definition is admitted. *)
(* SOONER: This exercise is kind of weird.  Should probably be
   optional. *)

Theorem havoc_post : forall (P : Assertion) (X : string),
  {{ P }} havoc X {{ $(fun st => exists (n:nat), ({{P [X |-> n] }}) st) }}.
Proof.
  intros P X. eapply hoare_consequence_pre.
  - apply hoare_havoc.
  - (* ADMITTED *)
    unfold havoc_pre, assert_implies, assertion_sub.
    intros st HP n.
    exists (st X).
    rewrite t_update_shadow. rewrite t_update_same.
    apply HP.
Qed.
(* /ADMITTED *)

(** [] *)

End Himp.

(** ** Assert and Assume *)

(* EX4 (assert_vs_assume) *)
(** In this exercise, we will extend IMP with two commands, [assert]
    and [assume]. Both commands are ways to indicate that a certain
    assertion should hold any time this part of the program is
    reached. However they differ as follows:

    - If an [assert] statement fails, it causes the program to go into
      an error state and exit.

    - If an [assume] statement fails, the program fails to evaluate at
      all. In other words, the program gets stuck and has no final
      state.

    The new set of commands is: *)

Module HoareAssertAssume.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAssert : bexp -> com
  | CAssume : bexp -> com.

(* NOTATION: LATER: Reconsider these precedences *)
Notation "'assert' l" := (CAssert l)
                           (in custom com at level 8, l custom com at level 0).
Notation "'assume' l" := (CAssume l)
                          (in custom com at level 8, l custom com at level 0).
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

(** To define the behavior of [assert] and [assume], we need to add
    notation for an error, which indicates that an assertion has
    failed. We modify the [ceval] relation, therefore, so that
    it relates a start state to either an end state or to [error].
    The [result] type indicates the end value of a program,
    either a state or an error: *)

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.

(** Now we are ready to give you the ceval relation for the new language. *)

Inductive ceval : com -> state -> result -> Prop :=
  (* Old rules, several modified *)
  | E_Skip : forall st,
      st =[ skip ]=> RNormal st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ while b do c end ]=> r ->
      st  =[ while b do c end ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ while b do c end ]=> RError
  (* Rules for Assert and Assume *)
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ assert b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ assert b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ assume b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).

(** We redefine hoare triples: Now, [{{P}} c {{Q}}] means that,
    whenever [c] is started in a state satisfying [P], and terminates
    with result [r], then [r] is not an error and the state of [r]
    satisfies [Q]. *)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r  -> P st  ->
     (exists st', r = RNormal st' /\ Q st').
(* LATER: I think the way I stated hoare triples may need cleaning
   up.  It doesn't work very well for the proofs of hoare rules to
   have [exists st'] in the conclusion.  BCP 10/18: Not sure what sort
   of cleaning up would be useful... *)

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

(** To test your understanding of this modification, give an example
    precondition and postcondition that are satisfied by the [assume]
    statement but not by the [assert] statement. *)

Theorem assert_assume_differ : exists (P:Assertion) b (Q:Assertion),
       ({{P}} assume b {{Q}})
  /\ ~ ({{P}} assert b {{Q}}).
(* ADMITTED *)
exists True.
exists <{ false }>.
exists False.
split.
- unfold valid_hoare_triple. intros st r E _.
  inversion E; subst. inversion H0.
- intros C. unfold valid_hoare_triple in C.
  specialize (C empty_st RError).
  assert (empty_st =[ assert false ]=> RError).
  { constructor. reflexivity. }
  simpl in C.
  apply C in H; auto.
  destruct H as [_ [_ Contra] ]; auto.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: assert_assume_differ *)

(** Then prove that any triple for an [assert] also works when
    [assert] is replaced by [assume]. *)

Theorem assert_implies_assume : forall P b Q,
     ({{P}} assert b {{Q}})
  -> ({{P}} assume b {{Q}}).
Proof.
(* ADMITTED *)
unfold valid_hoare_triple. intros P b Q HHoare st r HEval HP.
inversion HEval; subst.
exists st.
specialize (HHoare st (RNormal st)).
assert (st =[ assert b ]=> RNormal st).
    { constructor. assumption. }
apply HHoare in H; try assumption.
destruct H as [st' [H1 H2] ]. inversion H1; subst.
split; try reflexivity; try assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: assert_implies_assume *)

(** Next, here are proofs for the old hoare rules adapted to the new
    semantics.  You don't need to do anything with these. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
(* FOLD *)
Proof.
  unfold valid_hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  exists (X !-> aeval st a ; st). split; try reflexivity.
  assumption. Qed.
(* /FOLD *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
(* FOLD *)
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  - assumption.
  - apply Himp. assumption. Qed.
(* /FOLD *)

(* LATER: These proofs are a bit messy. Can it be made shorter? *)
Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
(* FOLD *)
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st r Hc HP.
  unfold valid_hoare_triple in Hhoare.
  assert (exists st', r = RNormal st' /\ Q' st').
  { apply (Hhoare st); assumption. }
  destruct H as [st' [Hr HQ'] ].
  exists st'. split; try assumption.
  apply Himp. assumption.
Qed.
(* /FOLD *)

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;c2 {{R}}.
(* FOLD *)
Proof.
  intros P Q R c1 c2 H1 H2 st r H12 Pre.
  inversion H12; subst.
  - eapply H1.
    + apply H6.
    + apply H2 in H3. apply H3 in Pre.
        destruct Pre as [st'0 [Heq HQ] ].
        inversion Heq; subst. assumption.
  - (* Find contradictory assumption *)
     apply H2 in H5. apply H5 in Pre.
     destruct Pre as [st' [C _] ].
     inversion C.
Qed.
(* /FOLD *)

(* LATER: HIDE *)
(** Here are the other proof rules (sanity check) *)
Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
(* FOLD *)
Proof.
  intros P st st' H HP. inversion H. subst.
  eexists. split.
  - reflexivity.
  - assumption.
Qed.
(* /FOLD *)

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b}} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
(* FOLD *)
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
    + assumption.
    + split; assumption.
  - (* b is false *)
    apply (HFalse st st').
    + assumption.
    + split.
      * assumption.
      * apply bexp_eval_false. assumption.
Qed.
(* /FOLD *)

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{ P /\ ~b}}.
(* FOLD *)
Proof.
  intros P b c Hhoare st st' He HP.
  remember <{while b do c end}> as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    eexists. split.
    + reflexivity.
    + split; try assumption.
      apply bexp_eval_false. assumption.
  - (* E_WhileTrueNormal *)
    clear IHHe1.
    apply IHHe2.
    + reflexivity.
    + clear IHHe2 He2 r.
      unfold valid_hoare_triple in Hhoare.
      apply Hhoare in He1.
      * destruct He1 as [st1 [Heq Hst1] ].
        inversion Heq; subst.
        assumption.
      * split; assumption.
  - (* E_WhileTrueError *)
     exfalso. clear IHHe.
     unfold valid_hoare_triple in Hhoare.
     apply Hhoare in He.
     + destruct He as [st' [C _] ]. inversion C.
     + split; assumption.
Qed.
(* /FOLD *)

(** Finally, state Hoare rules for [assert] and [assume] and use them
    to prove a simple program correct.  Name your rules [hoare_assert]
    and [hoare_assume]. *)

(* SOLUTION *)
(* HIDE: Equivalently, we could make the postcondition Q/\b or the
   precondition Q->b ... *)
Theorem hoare_assert : forall Q (b:bexp),
    {{Q /\ b}} assert b {{Q}}.
Proof.
intros Q b st r HEval [Hst Hb].
exists st. inversion HEval; subst.
- split; auto.
- rewrite Hb in H0. inversion H0.
Qed.

(* Stating this in a backwards-direction friendly way. *)
(* HIDE: Equivalently, we could make the postcondition Q/\b... *)
Theorem hoare_assume : forall (Q: state -> Prop) (b:bexp),
  {{b -> Q}}  assume b {{Q}}.
Proof.
intros P b st r HEval Hst.
exists st. inversion HEval; subst.
split; try reflexivity.
apply Hst. apply H0.
Qed.
(* /SOLUTION *)

(** Use your rules to prove the following triple. *)

Example assert_assume_example:
  {{True}}
    assume (X = 1);
    X := X + 1;
    assert (X = 2)
  {{True}}.
Proof.
(* ADMITTED *)
  eapply hoare_consequence_pre.
  - eapply hoare_seq.
    + eapply hoare_seq.
      * apply hoare_assert.
      * simpl. apply hoare_asgn.
    + unfold assertion_sub. simpl. apply hoare_assume.
  - unfold assert_implies.
    intros st _ Hst. split; try auto.
   rewrite t_update_eq.
   unfold beval in Hst. simpl in Hst.
   rewrite eqb_eq in Hst.
   rewrite -> Hst. simpl. reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 4: assert_assume_example *)

End HoareAssertAssume.
(** [] *)
(* /FULL *)

(* HIDE *)
(* LATER: A possible exercise on hoare logic with exceptions... *)
(* EX4A? (throw_hoare) *)
(** In the [exn_imp] exercise in chapter \CHAPV1{Imp} of _Logical
    Foundations_, we saw how to add a simple mechanism for raising and
    handling exceptions to Imp.  We now consider how to extend Hoare
    logic to reason about this language. *)
Module ThrowHoare.
Import ThrowImp.

Definition hoare_quad
           (P:Assertion) (c:com) (Q:Assertion) (S:Assertion) : Prop :=
  forall st st' s,
     st =[ c ]=> st' / s ->
     P st  ->
     (s = SNormal -> Q st') /\ (s = SThrow -> S st').


Notation "{{ P }} c {{ Q }} {{ S }}" :=
  (hoare_quad P c Q S)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99, S custom assn at level 99)
    : hoare_spec_scope.

Theorem hoare_skip : forall P S,
     {{P}} skip {{P}} {{S}}.
Proof.
  (* ADMITTED *)
  intros P S st st' s He HP. split; intros Hs; inversion He; subst.
  - assumption.
  - inversion H1.
Qed.
(* /ADMITTED *)

Theorem hoare_seq : forall P Q R S c1 c2,
     {{Q}} c2 {{R}} {{S}} ->
     {{P}} c1 {{Q}} {{S}} ->
     {{P}} c1;c2 {{R}} {{S}}.
Proof.
  (* ADMITTED *)
  intros P Q R S c1 c2 Hc2 Hc1 st st' s He Hp. split.
  - intros Hs. inversion He; subst.
    + destruct (Hc1 st st'0 SNormal); auto.
      destruct (Hc2 st'0 st' SNormal); auto.
    + inversion H2.
  - intros Hs. subst. inversion He; subst.
    + destruct (Hc1 st st'0 SNormal); auto.
      destruct (Hc2 st'0 st' SThrow); auto.
    + destruct (Hc1 st st' SThrow); auto.
Qed.
(* /ADMITTED *)

Theorem hoare_stop : forall Q S,
     {{S}} throw {{Q}} {{S}}.
Proof.
  (* ADMITTED *)
  intros Q S st st' s He HS. split.
  - inversion He. subst. intros C. inversion C.
  - intros Hs. inversion He. subst. assumption.
Qed.
(* /ADMITTED *)

Lemma hoare_try : forall P Q S1 S2 c1 c2,
  {{P}} c1 {{Q}} {{S1}} ->
  {{S1}} c2 {{Q}} {{S2}} ->
  {{P}} try c1 catch c2 end {{Q}} {{S2}}.
Proof.
  (* ADMITTED *)
  intros P Q S1 S2 c1 c2 Hc1 Hc2 st st' s He HP. split.
  - inversion He; subst; clear He; intros Hs.
    + apply (Hc1 st st' SNormal) in H4.
      * destruct H4. auto.
      * auto.
    + destruct (Hc1 st st'0 SThrow); subst; try auto.
      destruct (Hc2 st'0 st' SNormal); try auto.
  - intros Hs. inversion He; subst.
    + inversion H2.
    + destruct (Hc2 st'0 st' SThrow); try assumption.
      * apply (Hc1 st st'0 SThrow) in H1; try auto.
        apply (Hc2 st'0 st' SThrow) in H5; destruct H1; try auto.
      * auto.
Qed.
(* /ADMITTED *)

Lemma hoare_while : forall P S (b:bexp) c,
  {{ P /\ b}} c {{P}} {{S}} ->
  {{P}} while b do c end {{ P /\ ~ b}} {{S}}.
Proof.
  (* ADMITTED *)
  intros P S b c Hhoare st st' s He Hp. split; intros; subst.
  - remember <{while b do c end}> as wcom eqn:Heqwcom.
    remember SNormal as s.
    induction He; try (inversion Heqwcom).
    + (* E_WhileFalse *)
      subst. split.
      * assumption.
      * apply bexp_eval_false. assumption.
    + (* E_WhileTrue *)
      subst. apply IHHe2; try reflexivity. {
          destruct (Hhoare st st' SNormal); try assumption.
          - simpl. split; try assumption.
          - apply H0. reflexivity.
       }
    + (* E_WhileThrow *)
      inversion Heqs.
  - remember <{while b do c end}> as wcom eqn:Heqwcom.
    remember SThrow as s.
    induction He; try (inversion Heqwcom); subst; try (inversion Heqs).
    + (* E_WhileThrow *)
      clear IHHe Heqwcom.
      destruct (Hhoare st st' SThrow); try assumption.
      * simpl. split; try assumption.
      * auto.
Qed.
(* /ADMITTED *)
End ThrowHoare.
(** [] *)
(* /HIDE *)


(* HIDE *)
(* SAZ: Midterm 2 - 2022 scratch space. *)

(** ** Atomic Swap *)

From Stdlib Require Import ZArith.

Module Swap.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CSwap : string -> string -> com.

Notation "'swap' l m" := (CSwap l m)
                          (in custom com at level 60, l constr at level 0, m constr at level 0).
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

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_Swap : forall st x y,
      st =[ swap x y]=> (x !-> st y ; y !-> st x ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

(** The definition of Hoare triples is exactly as before. *)

Definition valid_hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Hint Unfold valid_hoare_triple : core.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

(** And the precondition consequence rule is exactly as before. *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof. eauto. Qed.

Definition swap_pre (X Y : string) (Q : Assertion) (st : total_map nat) :=
  ({{ (Q [X |-> st Y] [Y |-> st X]) }}) st.

Theorem hoare_swap : forall (Q : Assertion) (X Y : string),
  {{ $(swap_pre X Y Q) }} swap X Y {{ Q }}.
Proof.
  unfold valid_hoare_triple, swap_pre.
  intros Q X Y st st' Heval Hpre.
  inversion Heval; subst. apply Hpre.
Qed.

Theorem swap_post : forall (P : Assertion) (X Y : string),
  {{ P }} swap X Y {{ $(fun st => ({{ P [X |-> st Y][Y |-> st X] }}) st) }}.
Proof.
  intros P X Y. eapply hoare_consequence_pre.
  - apply hoare_swap.
  - (* ADMITTED *)
    unfold swap_pre, assert_implies, assertion_sub.
    intros st HP.
    cbn.
    destruct (String.eqb_spec X Y).
    + subst. repeat rewrite t_update_eq. repeat rewrite t_update_same. assumption.
    +
      rewrite (@t_update_neq _ _ X Y _ n).
      rewrite t_update_eq.
      rewrite t_update_permute; auto.
      rewrite t_update_shadow.
      rewrite t_update_permute; auto.
      rewrite t_update_shadow.
      rewrite t_update_eq.
      repeat rewrite t_update_same.
      assumption.
    (* /ADMITTED *)
Qed.

Definition Z_swap (x y : Z) :=
  (let x1 := x + y in
  let y1 := y - x1 in
  let y2 := 0 - y1 in
  let x2 := x1 + y1 in
  (x2, y2))%Z.

Lemma Z_swap_swaps: forall (x y : Z), Z_swap x y = (y, x).
Proof.
  intros.
  unfold Z_swap.
  assert ( (x + y + (y - (x + y)))%Z = y).
  { lia. }
  assert ((0 - (y - (x + y)))%Z = x).
  { lia. }
  rewrite H. rewrite H0. reflexivity.
Qed.

End Swap.
(* /HIDE *)

(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(\\*\\* \\*+\\|(\\* EX[1-5]..." *)
(* End: *)
(* mode: outline-minor *)
(* outline-heading-end-regexp: "\n" *)
(* /HIDE *)
