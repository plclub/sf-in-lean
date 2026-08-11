(** * MoreStlc: More on the Simply Typed Lambda-Calculus *)

(* SOONER: NDS'25. This file contains some improvements on notations:
   "atomic" escape (for natural numbers), and related change to the notation for maps.
   These should be backported. *)

(* SOONER: Sampsa:

    the commenting in the section `Preliminaries` is haphazard.

    It is not given explicitly,
    but the proposed record field name encoding seems to be the following.

    ```
    Import Ascii.
    Import String.

    Fixpoint fold_left {a : Type} (f : a -> ascii -> a) (x : a) (s : string) : a :=
     match s with
     | EmptyString => x
     | String c t => fold_left f (f x c) t
     end.

    Definition encode (s : string) : nat :=
     pred (fold_left (fun n c =>
     (1 + nat_of_ascii c - nat_of_ascii "a") +
     (1 + nat_of_ascii "z" - nat_of_ascii "a") * n) 0 s).
    ```

    I think this encoding would be greatly improved
    by removing the `pred` from the definition,
    because that would make it simpler and
    allow empty field names to be encoded as well.
*)
(* SOONER: Not enough quizzes?? *)
(* LATER: We've been a bit inconsistent about capitalization of types
   in informal examples.  I've tried to make this file, at least,
   consistent (type names always capitalized), but I'm sure there are
   some bits I've missed. *)
(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** * Simple Extensions to STLC *)

(** The simply typed lambda-calculus has a rich enough structure to make
    its theoretical properties interesting, but it is not much of a
    programming language!

    In this chapter, we begin to close the gap with real-world languages by
    introducing a number of familiar features that have straightforward
    treatments at the level of typing. *)

(** ** Numbers *)

(** FULL: As we saw in the [STLCArith] exercises at the end of the [StlcProp]
    chapter, adding types, constants, and primitive operations for
    natural numbers is easy -- basically just a matter of combining
    the \CHAP{Types} and \CHAP{Stlc} chapters.  Adding more realistic
    numeric types like machine integers and floats is also
    straightforward, though of course the specifications of the
    numeric primitives become more fiddly. *)
(** TERSE: Adding types, constants, and primitive operations for
    natural numbers is easy (as we saw in the [STLCArith] exercises). *)

(** ** Let Bindings *)

(** FULL: When writing a complex expression, it is useful to be able
    to give names to some of its subexpressions to avoid repetition
    and increase readability.  Most languages provide one or more ways
    of doing this.  In OCaml (and Rocq), for example, we can write [let
    x=t1 in t2] to mean "reduce the expression [t1] to a value and
    bind the name [x] to this value while reducing [t2]."

    Our [let]-binder follows OCaml in choosing a standard
    _call-by-value_ evaluation order, where the [let]-bound term must
    be fully reduced before reduction of the [let]-body can begin.
    The typing rule [T_Let] tells us that the type of a [let] can be
    calculated by calculating the type of the [let]-bound term,
    extending the context with a binding with this type, and in this
    enriched context calculating the type of the body (which is then
    the type of the whole [let] expression).

    At this point in the book, it's probably easier simply to look at
    the rules defining this new feature than to wade through a lot of
    English text conveying the same information.  Here they are: *)

(** TERSE: A more interesting extension... let-bindings.

    When writing a complex expression, it is often useful to give
    names to some of its subexpressions: this avoids repetition and
    often increases readability. *)

(** Syntax:
<<
       t ::=                Terms
           | ...               (other terms same as before)
           | let x=t1 in t2    let-binding
>>
*)

(** TERSE: *** *)
(**
    Reduction:
[[[
                                 t1 --> t1'
                     ----------------------------------               (ST_Let1)
                     let x=t1 in t2 --> let x=t1' in t2

                        ----------------------------              (ST_LetValue)
                        let x=v1 in t2 --> [x:=v1]t2
]]]
    Typing:
[[[
             Gamma |-- t1 \in T1      x|->T1; Gamma |-- t2 \in T2
             ----------------------------------------------------      (T_Let)
                        Gamma |-- let x=t1 in t2 \in T2
]]]
*)
(* LATER: Is this the first time they've seen BNF?  Should introduce
   it at some appropriate earlier point -- e.g., when they see
   informal inference rules. *)
(* LATER: (The [let]-binder in Rocq behaves a little different wrt evaluation
   order  But they may not have noticed this. *)
(* LATER: FIX: Argh -- we used y below in the definition, not x!  Better
   warn them about this!? *)

(* HIDE: CH: It may be worth mentioning that there is also a simple
   encoding for let in STLC: [let x=t1 in t2 =def (\x:T1, t2) t1].
   We don't show this to them because of the need for the [T1] annotation?
   (since otherwise we do talk about much more complex encodings below) *)

(** ** Pairs *)

(** FULL: Our functional programming examples in Rocq have made
    frequent use of _pairs_ of values.  The type of such a pair is
    called a _product type_.

    The formalization of pairs is almost too simple to be worth
    discussing.  However, let's look briefly at the various parts of
    the definition to emphasize the common pattern. *)

(** In Rocq, the primitive way of extracting the components of a pair
    is _pattern matching_.  An alternative is to take [fst] and
    [snd] -- the first- and second-projection operators -- as
    primitives.  Just for fun, let's do our pairs this way.  For
    example, here's how we'd write a function that takes a pair of
    numbers and returns the pair of their sum and difference:
<<
       \x : Nat*Nat,
          let sum = x.fst + x.snd in
          let diff = x.fst - x.snd in
          (sum,diff)
>>
*)

(** FULL: Adding pairs to the simply typed lambda-calculus, then, involves
    adding two new forms of term -- pairing, written [(t1,t2)], and
    projection, written [t.fst] for the first projection from [t] and
    [t.snd] for the second projection -- plus one new type constructor,
    [T1*T2], called the _product_ of [T1] and [T2].  *)

(** TERSE: *** *)
(** Syntax:
<<
       t ::=                Terms
           | ...
           | (t1,t2)           pair
           | t0.fst            first projection
           | t0.snd            second projection

       v ::=                Values
           | ...
           | (v1,v2)           pair value

       T ::=                Types
           | ...
           | T1 * T2           product type
>>
*)

(** TERSE: *** *)
(** FULL: For reduction, we need several new rules specifying how pairs and
    projection behave. *)
(** TERSE: Reduction... *)
(**
[[[
                              t1 --> t1'
                         --------------------                        (ST_Pair1)
                         (t1,t2) --> (t1',t2)

                              t2 --> t2'
                         --------------------                        (ST_Pair2)
                         (v1,t2) --> (v1,t2')

                               t0 --> t0'
                           ------------------                        (ST_Fst1)
                           t0.fst --> t0'.fst

                          ------------------                       (ST_FstPair)
                          (v1,v2).fst --> v1

                               t0 --> t0'
                           ------------------                        (ST_Snd1)
                           t0.snd --> t0'.snd

                          ------------------                       (ST_SndPair)
                          (v1,v2).snd --> v2
]]]
*)

(** FULL: Rules [ST_FstPair] and [ST_SndPair] say that, when a fully
    reduced pair meets a first or second projection, the result is
    the appropriate component.  The congruence rules [ST_Fst1] and
    [ST_Snd1] allow reduction to proceed under projections, when the
    term being projected from has not yet been fully reduced.
    [ST_Pair1] and [ST_Pair2] reduce the parts of pairs: first the
    left part, and then -- when a value appears on the left -- the right
    part.  The ordering arising from the use of the metavariables [v]
    and [t] in these rules enforces a left-to-right evaluation
    strategy for pairs.  (Note the implicit convention that
    metavariables like [v] and [v1] can only denote values.)  We've
    also added a clause to the definition of values, above, specifying
    that [(v1,v2)] is a value.  The fact that the components of a pair
    value must themselves be values ensures that a pair passed as an
    argument to a function will be fully reduced before the function
    body starts executing. *)
(* LATER: This convention should be explained and used earlier, in
   SmallStep.v *)

(** TERSE: *** *)
(** FULL: The typing rules for pairs and projections are straightforward. *)
(** TERSE: Typing: *)
(**
[[[
              Gamma |-- t1 \in T1     Gamma |-- t2 \in T2
              -------------------------------------------              (T_Pair)
                      Gamma |-- (t1,t2) \in T1*T2

                        Gamma |-- t0 \in T1*T2
                        -----------------------                        (T_Fst)
                        Gamma |-- t0.fst \in T1

                        Gamma |-- t0 \in T1*T2
                        -----------------------                        (T_Snd)
                        Gamma |-- t0.snd \in T2
]]]
*)

(** FULL: [T_Pair] says that [(t1,t2)] has type [T1*T2] if [t1] has
    type [T1] and [t2] has type [T2].  Conversely, [T_Fst] and [T_Snd]
    tell us that, if [t0] has a product type [T1*T2] (i.e., if it
    will reduce to a pair), then the types of the projections from
    this pair are [T1] and [T2]. *)

(** ** Unit *)

(** Another handy base type, found especially in functional languages,
    is the singleton type [Unit]. *)
(* FULL *)
(** It has a single element -- the term constant [unit] (with a small
    [u]) -- and a typing rule making [unit] an element of [Unit].  We
    also add [unit] to the set of possible values -- indeed, [unit] is
    the _only_ possible result of reducing an expression of type
    [Unit]. *)
(* /FULL *)

(** Syntax:
<<
       t ::=                Terms
           | ...               (other terms same as before)
           | unit              unit

       v ::=                Values
           | ...
           | unit              unit value

       T ::=                Types
           | ...
           | Unit              unit type
>>
    Typing:
[[[
                         -----------------------                       (T_Unit)
                         Gamma |-- unit \in Unit
]]]
*)

(** FULL: It may seem a little strange to bother defining a type that
    has just one element -- after all, wouldn't every computation
    living in such a type be trivial?

    This is a fair question, and indeed in the STLC the [Unit] type is
    not especially critical (though we'll see two uses for it below).
    Where [Unit] really comes in handy is in richer languages with
    _side effects_ -- e.g., assignment statements that mutate
    variables or pointers, exceptions and other sorts of nonlocal
    control structures, etc.  In such languages, it is convenient to
    have a type for the (trivial) result of an expression that is
    evaluated only for its effect. *)

(* QUIZ *)
(** Is [unit] the only term of type [Unit]?

    (A) Yes

    (B) No
*)
(* /QUIZ *)

(* FOLD *)
(** No! For instance (\x:Unit,x) unit is also a _term_ of type unit. *)
(* /FOLD *)

(** ** Sums *)

(** Many programs need to deal with values that can take two distinct
   forms.  For example, we might identify students in a university
   database using _either_ their name _or_ their id number. A search
   function might return _either_ a matching value _or_ an error code.

   These are specific examples of a binary _sum type_ (sometimes called
   a _disjoint union_), which describes a set of values drawn from
   one of two given types, e.g.:
<<
       Nat + Bool
>>
*)
(** TERSE: *** *)
(** TERSE:

    We create elements of these types by tagging elements of the
    component types, telling on which side of the sum we are putting
    them. E.g.,

<<
   inl 42   \in Nat + Bool
   inr true \in Nat + Bool
>>
*)
(** FULL: We create elements of these types by _tagging_ elements of
    the component types.  For example, if [n] is a [Nat] then [inl n]
    is an element of [Nat+Bool]; similarly, if [b] is a [Bool] then
    [inr b] is a [Nat+Bool].  The names of the tags [inl] and [inr]
    arise from thinking of them as functions
<<
       inl \in Nat  -> Nat + Bool
       inr \in Bool -> Nat + Bool
>>
    that "inject" elements of [Nat] or [Bool] into the left and right
    components of the sum type [Nat+Bool].  (But note that we don't
    actually treat them as functions in the way we formalize them:
    [inl] and [inr] are keywords, and [inl t] and [inr t] are primitive
    syntactic forms, not function applications.) *)

(** In general, the elements of a type [T1 + T2] consist of the
    elements of [T1] tagged with the token [inl], plus the elements of
    [T2] tagged with [inr]. *)

(** TERSE: *** *)
(** As we've seen in Rocq programming, one important use of sums is
    signaling errors:
<<
      div \in Nat -> Nat -> (Nat + Unit)
      div =
        \x:Nat, \y:Nat,
          if iszero y then
            inr unit
          else
            inl ...
>>
*)
(** FULL: The type [Nat + Unit] above is in fact isomorphic to [option
    nat] in Rocq -- i.e., it's easy to write functions that translate
    back and forth. *)

(** FULL: To _use_ elements of sum types, we introduce a [case]
    construct (a very simplified form of Rocq's [match]) to destruct
    them. For example, the following procedure converts a [Nat+Bool]
    into a [Nat]: *)
(** TERSE: *** *)
(** TERSE: Values of sum type are "destructed" by case analysis: *)
(**
<<
    getNat \in Nat+Bool -> Nat
    getNat =
      \x:Nat+Bool,
        case x of
          inl n => n
        | inr b => if b then 1 else 0
>>
*)

(** FULL: More formally... *)

(** TERSE: *** *)
(** Syntax:
<<
       t ::=                Terms
           | ...               (other terms same as before)
           | inl T2 t1         tagging (left)
           | inr T1 t2         tagging (right)
           | case t0 of        case analysis
               inl x1 => t1
             | inr x2 => t2

       v ::=                Values
           | ...
           | inl T2 v1         tagged value (left)
           | inr T1 v2         tagged value (right)

       T ::=                Types
           | ...
           | T1 + T2           sum type
>>
*)

(** TERSE: *** *)
(** Reduction:

[[[
                               t1 --> t1'
                        ------------------------                       (ST_Inl)
                        inl T2 t1 --> inl T2 t1'

                               t2 --> t2'
                        ------------------------                       (ST_Inr)
                        inr T1 t2 --> inr T1 t2'

                               t0 --> t0'
               -------------------------------------------            (ST_Case)
                case t0 of inl x1 => t1 | inr x2 => t2 -->
               case t0' of inl x1 => t1 | inr x2 => t2

            -----------------------------------------------        (ST_CaseInl)
            case (inl T2 v1) of inl x1 => t1 | inr x2 => t2
                           -->  [x1:=v1]t1

            -----------------------------------------------        (ST_CaseInr)
            case (inr T1 v2) of inl x1 => t1 | inr x2 => t2
                           -->  [x2:=v2]t2
]]]
*)

(** TERSE: *** *)
(** Typing:
[[[
                          Gamma |-- t1 \in T1
                   -------------------------------                      (T_Inl)
                   Gamma |-- inl T2 t1 \in T1 + T2


                          Gamma |-- t2 \in T2
                   --------------------------------                     (T_Inr)
                    Gamma |-- inr T1 t2 \in T1 + T2


                        Gamma |-- t0 \in T1+T2
                     x1|->T1; Gamma |-- t1 \in T3
                     x2|->T2; Gamma |-- t2 \in T3
         -------------------------------------------------------        (T_Case)
         Gamma |-- case t0 of inl x1 => t1 | inr x2 => t2 \in T3
]]]

    We use the type annotations on [inl] and [inr] to make the typing
    relation deterministic (each term has at most one type), as we
    did for functions. *)

(** FULL: Without this extra information, the typing rule [T_Inl], for
    example, would have to say that, once we have shown that [t1] is
    an element of type [T1], we can derive that [inl t1] is an element
    of [T1 + T2] for _any_ type [T2].  For example, we could derive both
    [inl 5 : Nat + Nat] and [inl 5 : Nat + Bool] (and infinitely many
    other types).  This peculiarity (technically, a failure of
    uniqueness of types) would mean that we cannot build a
    typechecking algorithm simply by "reading the rules from bottom to
    top" as we could for all the other features seen so far.

    There are various ways to deal with this difficulty.  One simple
    one -- which we've adopted here -- forces the programmer to
    explicitly annotate the "other side" of a sum type when performing
    an injection.  This is a bit heavy for programmers (so real
    languages adopt other solutions), but it is easy to understand and
    formalize. *)
(* LATER: AAA: The explanation above is not entirely accurate. The
   exact same problem appears with functions. Perhaps it would be
   better to remove this explanation and just say that we want to make
   the typing rules simpler.  BCP: Don't see in what way this is
   inaccurate... *)
(* QUIZ *)
(** What does the following term step to (in one step)?
[[
      let f = \x : Nat + Bool,
         case x of
           inl n => n + 3
           | inr b => 0 in
      f (inl Bool 4)
]]

[[
    (A)  (\x : Nat + Bool,
            case x of
              inl n => n + 3
              | inr b => 0
         ) (inl Bool 4)
]]

[[
    (B) 7
]]

[[
    (C)  case inl Bool 4 of
           inl n => n + 3
         | inr b => 0
]]


[[
    (D) f (inl Bool 4)
]]

*)
(* /QUIZ *)
(* QUIZ *)
(** What about this one?
[[
  (\x : Nat + Bool,
     case x of
     inl n => n + 3
     | inr b => 0
  ) (inl Bool 4)
]]

[[
   (A)  7
]]

[[
   (B)  case inl Bool 4 of
          inl n => n + 3
        | inr b => 0
]]

[[
   (C)  4 + 3
]]

*)
(* /QUIZ *)
(* QUIZ *)
(** What about this one?
[[
       case inl Bool 4 of
         inl n => n + 3
         | inr b => 0

   (A)  4 + 3

   (B)  7

   (C)  0
]]
*)
(* /QUIZ *)

(** ** Lists *)

(** FULL: The typing features we have seen can be classified into
    _base types_ like [Bool], and _type constructors_ like [->] and
    [*] that build new types from old ones.  Another useful type
    constructor is [List].  For every type [T], the type [List T]
    describes finite-length lists whose elements are drawn from [T].

    In principle, we could encode lists using pairs, sums, unit, and
    _recursive_ types. But giving semantics to recursive types is
    non-trivial. Instead, we'll just discuss the special case of lists
    directly.

    Below we give the syntax, semantics, and typing rules for lists.
    Except for the fact that explicit type annotations are mandatory
    on [nil] and cannot appear on [cons], these lists are essentially
    identical to those we built in Rocq.  We use [case], rather than
    [head] and [tail] operators, to destruct lists, to avoid dealing
    with questions like "what is the [head] of the empty list?" *)

(** FULL: For example, here is a function that calculates the sum of
    the first two elements of a list of numbers:
<<
      \x:List Nat,
      case x of
        nil   => 0
        | a::x' => case x' of
                     nil    => a
                     | b::x'' => a+b
>>
*)

(* LATER: Maybe the syntax of case should look more like match?  Or
   less like?  And we should give a couple of examples of the informal
   concrete syntax. *)
(**
    Syntax:
<<
       t ::=                Terms
           | ...
           | nil T             empty list
           | t1 :: t2          cons
           | case t1 of        case analysis
               nil      => t2
               | xh::xt => t3

       v ::=                Values
           | ...
           | nil T             nil value
           | v1 :: v2          cons value

       T ::=                Types
           | ...
           | List T            list of Ts
>>
*)

(** TERSE: *** *)
(** Reduction:
[[[
                                t1 --> t1'
                       --------------------------                    (ST_Cons1)
                         t1 :: t2 --> t1' :: t2

                                t2 --> t2'
                       --------------------------                    (ST_Cons2)
                         v1 :: t2 --> v1 :: t2'

                              t1 --> t1'
                -------------------------------------------         (ST_Lcase1)
                 (case t1 of nil => t2 | xh::xt => t3) -->
                (case t1' of nil => t2 | xh::xt => t3)

               ------------------------------------------          (ST_LcaseNil)
               (case nil T1 of nil => t2 | xh::xt => t3)
                                --> t2

              -------------------------------------------         (ST_LcaseCons)
              (case (vh::vt) of nil => t2 | xh::xt => t3)
                          --> [xh:=vh][xt:=vt]t3
]]]
*)

(** TERSE: *** *)
(** Typing:
[[[
                        ----------------------------                    (T_Nil)
                        Gamma |-- nil T1 \in List T1

            Gamma |-- t1 \in T1      Gamma |-- t2 \in List T1
            -------------------------------------------------           (T_Cons)
                    Gamma |-- t1 :: t2 \in List T1

                        Gamma |-- t1 \in List T1
                        Gamma |-- t2 \in T2
                (xh|->T1; xt|->List T1; Gamma) |-- t3 \in T2
          ----------------------------------------------------         (T_Lcase)
          Gamma |-- (case t1 of nil => t2 | xh::xt => t3) \in T2
]]]
*)

(** ** General Recursion *)

(** Another facility found in most programming languages (including
    Rocq) is the ability to define recursive functions.  For example,
    we would like to be able to define and use the factorial function
    like this:
<<
      let fact = \x:Nat,
                   if x=0 then 1 else x * (fact (pred x))) in
      fact 3.
>>
   Note that the right-hand side of this binder mentions [fact], the
   variable being bound -- something that is not allowed according
   to the way we defined [let] above. *)

(** FULL: (The body of a [let] is typechecked in the same context as the
   [let] itself, which means that the recursive occurrence of [fact] in the
   body will not have a type in the context when it is looked up by the
   [T_Var] rule.) *)

(** FULL: Changing the [let] rule to handle "recursive definitions"
   like this is possible, but it requires some extra effort -- e.g.,
   passing around an extra "environment" of recursive function
   definitions in the definition of the [step] relation.  We're going
   to take a simpler path here. *)

(** TERSE: Extending our formalization of [let]s to handle "recursive
    definitions" would require non-trivial effort. *)

(** TERSE: *** *)
(* SOONER: The explanations in this section are not clear enough! *)
(* HIDE *)
    (* HIDE: Lef 21: Took another turn on it, thoughts? *)
    (* HIDE: BCP 21: Not sure this is better -- let's leave it the old
       way for now and keep this for discussion... *)
    (** Let us postpone the recursion problem -- by passing a function [f] we
        call instead of the recursive [fact]. The above example can then
        be written
    <<
          let fact = \f: Nat -> Nat, \x: Nat,
                 if x=0 then 1 else x * (f (pred x))) in
          fact (fact (fact (fact id))) 3.
    >>
       Starting from the inner [fact id] where [id] is the
       identity function [\x: Nat, Nat]. This is the 4th
       time factorial will be called, and everytime the initial argument
       decreases, so [id] will be called with [0] as its argument.

       If we evaluate all beta-reductions and [pred] reductions for brevity,
       we see this simply an iterative unfolding of [f] calls
    >>
       if 3=0 then 1 else
          3 * (if 2=0 then 1 else
            2 * (if 1=0 then 1 else
              1 * (if 0=0 then 1 else
                0*(id 0))))
    >>

       This transformation is useful, but asking the programmer to know
       exactly how many times a recursive definition will be called is painful.
       Thankfully we can abstract that away by defining a new primitive -- the
       _fixed-point operator_ [fix] -- that calls the function any
       number of times.

        For example, instead of
    <<
          fact = \x:Nat,
                    if x=0 then 1 else x * (fact (pred x)))
    >>
        we will write:
    <<
          fact =
              fix
                (\f:Nat->Nat,
                   \x:Nat,
                      if x=0 then 1 else x * (f (pred x)))
    >>
    *)

    (** TERSE: *** *)
    (**
       The [fix] combinator postpones the unfolding of recursive calls
       for later, when the term is _closed_. For us, proof-engineers
       that means when we need to _prove_ things about the recursive
       function.

       To reiterate, this was our approach for embedding _recursion_
       in an Stlc function definition:

          - Add an abstraction binding [f] at the front, with an
            appropriate type annotation.  (Since we are using [f] in place
            of [fact], which had type [Nat->Nat], we should require [f]
            to have the same type.)  The new abstraction has type
            [(Nat->Nat) -> (Nat->Nat)].

          - Apply [fix] to this abstraction.  This application has
            type [Nat->Nat].

          - Use all of this as the right-hand side of an ordinary
            [let]-binding for [fact].
    *)
(* /HIDE *)
(* HIDE: Here is the original: *)
(** Here is another way of presenting recursive functions that is
    a bit more verbose but equally powerful and much more straightforward
    to formalize: instead of writing recursive definitions, we will define
    a _fixed-point operator_ called [fix] that performs the "unfolding"
    of the recursive definition in the right-hand side as needed, during
    reduction.

    For example, instead of
<<
      fact = \x:Nat,
                if x=0 then 1 else x * (fact (pred x)))
>>
    we will write:
<<
      fact =
          fix
            (\f:Nat->Nat,
               \x:Nat,
                  if x=0 then 1 else x * (f (pred x)))
>>
*)

(** FULL: We can derive the latter from the former as follows:

      - In the right-hand side of the definition of [fact], replace
        recursive references to [fact] by a fresh variable [f].

      - Add an abstraction binding [f] at the front, with an
        appropriate type annotation.  (Since we are using [f] in place
        of [fact], which had type [Nat->Nat], we should require [f]
        to have the same type.)  The new abstraction has type
        [(Nat->Nat) -> (Nat->Nat)].

      - Apply [fix] to this abstraction.  This application has
        type [Nat->Nat].

      - Use all of this as the right-hand side of an ordinary
        [let]-binding for [fact].
*)

(** FULL: For the mathematically inclined,
    the intuition here is that the higher-order function [f]
    passed to [fix] is a _generator_ for the [fact] function: if [f]
    is applied to a function that "approximates" the desired behavior
    of [fact] up to some number [n] (that is, a function that returns
    correct results on inputs less than or equal to [n] but we don't
    care what it does on inputs greater than [n]), then [f] returns a
    slightly better approximation to [fact] -- a function that returns
    correct results for inputs up to [n+1].  Applying [fix] to this
    generator returns its _fixed point_, which is a function that
    gives the desired behavior for all inputs [n].

    (The term "fixed point" is used here in exactly the same sense as
    in ordinary mathematics, where a fixed point of a function [f] is
    an input [x] such that [f(x) = x].  Here, a fixed point of a
    function [F] of type [(Nat->Nat)->(Nat->Nat)] is a function [f] of
    type [Nat->Nat] such that [F f] behaves the same as [f].) *)

(** TERSE: *** *)
(** Syntax:
<<
       t ::=                Terms
           | ...
           | fix t1            fixed-point operator
>>
   Reduction:
[[[
                                t1 --> t1'
                            ------------------                     (ST_Fix1)
                            fix t1 --> fix t1'

               --------------------------------------------      (ST_FixAbs)
               fix (\xf:T1.t1) --> [xf:=fix (\xf:T1.t1)] t1
]]]
   Typing:
[[[
                           Gamma |-- t1 \in T1->T1
                           -----------------------                    (T_Fix)
                           Gamma |-- fix t1 \in T1
]]]
 *)

(** TERSE: *** *)

(* HIDE: CH: Is it worth mentioning that in [ST_FixAbs] we substitute a
   non-value for a variable, but that's still okay? It may be good to give an
   informal explanation. Formally, one thing that saves the day is that in the
   substitution lemma we don't actually require [v] to be a value, which goes
   against the informal convention used in this file (e.g., we can't omit the
   value requirement in ST_LetValue without breaking determinism). *)

(* SOONER: Robert Rand: This isn't very clear if the students haven't done
   the nat exercises in the previous chapter. (Which is particularly likely
   if stlc and morestlc are subsequent lectures in the same week.) Also,
   removing the explicit annotations on the step relation might make this
   more readible. (Also, doesn't fit on a slide.)  BCP 23: Yes, this is a
   bit drinking from the firehose / lecturing with a firehose. Not sure
   what to replace it with, though. (And breaking it across slides in the
   terse version seems worse than scrolling in this -- rare --
   instance.)) *)

(** Let's see how [ST_FixAbs] works by reducing [fact 3 = fix F 3],
    where
<<
    F = (\f. \x. if x=0 then 1 else x * (f (pred x)))
>>
    (type annotations are omitted for brevity).
<<

    fix F 3
>>
[-->] [ST_FixAbs] + [ST_App1]
<<
    (\x. if x=0 then 1 else x * (fix F (pred x))) 3
>>
[-->] [ST_AppAbs]
<<
    if 3=0 then 1 else 3 * (fix F (pred 3))
>>
[-->] [ST_If0_Nonzero]
<<
    3 * (fix F (pred 3))
>>
[-->] [ST_FixAbs + ST_Mult2 + ST_App1]
<<
    3 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 3))
>>
[-->] [ST_PredNat + ST_Mult2 + ST_App2]
<<
    3 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 2)
>>
[-->] [ST_AppAbs + ST_Mult2]
<<
    3 * (if 2=0 then 1 else 2 * (fix F (pred 2)))
>>
[-->] [ST_If0_Nonzero + ST_Mult2]
<<
    3 * (2 * (fix F (pred 2)))
>>
[-->] [ST_FixAbs + 2 x ST_Mult2 + ST_App1]
<<
    3 * (2 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 2)))
>>
[-->] [ST_PredNat + 2 x ST_Mult2 + ST_App2]
<<
    3 * (2 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 1))
>>
[-->] [ST_AppAbs + 2 x ST_Mult2]
<<
    3 * (2 * (if 1=0 then 1 else 1 * (fix F (pred 1))))
>>
[-->] [ST_If0_Nonzero + 2 x ST_Mult2]
<<
    3 * (2 * (1 * (fix F (pred 1))))
>>
[-->] [ST_FixAbs + 3 x ST_Mult2 + ST_App1]
<<
    3 * (2 * (1 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 1))))
>>
[-->] [ST_PredNat + 3 x ST_Mult2 + ST_App2]
<<
    3 * (2 * (1 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 0)))
>>
[-->] [ST_AppAbs + 3 x ST_Mult2]
<<
    3 * (2 * (1 * (if 0=0 then 1 else 0 * (fix F (pred 0)))))
>>
[-->] [ST_If0Zero + 3 x ST_Mult2]
<<
    3 * (2 * (1 * 1))
>>
[-->] [ST_MultNats + 2 x ST_Mult2]
<<
    3 * (2 * 1)
>>
[-->] [ST_MultNats + ST_Mult2]
<<
    3 * 2
>>
[-->] [ST_MultNats]
<<
    6
>>
*)

(** TERSE: *** *)

(** The simply typed lambda-calculus with fixed points is a famous and
    extensively studied system. It is often called _PCF_ because it is a
    simple language of "partial computable functions". *)

(** TERSE: One important point to note is that, unlike [Fixpoint]
    definitions in Rocq, there is nothing to prevent functions defined
    using [fix] from diverging. *)
(* SOONER: It might be useful to say more, here, about why it makes
   sense to formalize a nonterminating language in a terminating one.
   Remind them that we did the same with Imp. *)

(* QUIZ *)
(** Is this a well-typed Stlc term? What does it evaluate to?
[[
        fix (\f: Nat->Nat, \x:Nat, f x) 0
]]

   (A) no

   (B) yes, diverges

   (C) yes, [42]

   (D) yes, [0]
*)
(* /QUIZ *)
(* QUIZ *)
(** Which of the following are (intuitively) true for Stlc + fixpoints.

   (A) deterministic

   (B) progress

   (C) preservation

   (D) normalizing (i.e. every well-typed term reduces to a normal form)
*)
(* /QUIZ *)

(* FULL *)
(* EX1? (halve_fix) *)
(** Translate this informal recursive definition into one using [fix]:
<<
      halve =
        \x:Nat,
           if x=0 then 0
           else if (pred x)=0 then 0
           else 1 + (halve (pred (pred x)))
>>
    (* SOLUTION *)
<<
      halve =
          fix
            (\f:Nat->Nat,
               \x:Nat,
                  if x=0 then 0
                  else if (pred x)=0 then 0
                  else 1 + (f (pred (pred x))))
>>
(* /SOLUTION *)
*)
(** [] *)

(* EX1? (fact_steps) *)
(** Write down the sequence of steps that the term [fact 1] goes
    through to reduce to a normal form (assuming the usual reduction
    rules for arithmetic operations).

    (* SOLUTION *)
<<
        fact 1
      = fix (\f:Nat->Nat, \x:Nat, if x=0 then 1 else x * (f (pred x))) 1
    --> (\x: Nat, if x = 0 then 1 else x * (fact (pred x))) 1
    --> if 1 = 0 then 1 else 1 * (fact (pred 1))
    --> 1 * (fact (pred 1))
    --> 1 * ((\x:Nat, if x=0 then 1 else x * (fact (pred x))) (pred 1))
    --> 1 * ((\x:Nat, if x=0 then 1 else x * (fact (pred x))) 0)
    --> 1 * (if 0=0 then 1 else 0 * (fact (pred 0)))
    --> 1 * 1
    --> 1
>>
    Also see the solution to exercise [fact_example] below.
(* /SOLUTION *)
*)
(** [] *)

(** The ability to form the fixed point of a function of type [T->T]
    for any [T] has some surprising consequences.  In particular, it
    implies that _every_ type is inhabited by some term.  To see this,
    observe that, for every type [T], we can define the term
[[
    fix (\x:T,x)
]]
    By [T_Fix]  and [T_Abs], this term has type [T].  By [ST_FixAbs]
    it reduces to itself, over and over again.  Thus it is a
    _diverging element_ of [T].

    More usefully, here's an example using [fix] to define a
    two-argument recursive function:
<<
    equal =
      fix
        (\eq:Nat->Nat->Bool,
           \m:Nat, \n:Nat,
             if m=0 then iszero n
             else if n=0 then false
             else eq (pred m) (pred n))
>>
*)
(** And finally, here is an example where [fix] is used to define a
    _pair_ of recursive functions (illustrating the fact that the type
    [T1] in the rule [T_Fix] need not be a function type):
<<
    let evenodd =
         fix
           (\eo: ((Nat -> Nat) * (Nat -> Nat)),
              (\n:Nat, if0 n then 1 else (eo.snd (pred n)),
               \n:Nat, if0 n then 0 else (eo.fst (pred n)))) in
    let even = evenodd.fst in
    let odd  = evenodd.snd in
    (even 3, even 4)}
>>
*)
(* /FULL *)

(* ###################################################################### *)
(** ** Records *)

(* SOONER: Needs a bit more text too.  And tersification. *)

(** FULL: As a final example of a basic extension of the STLC, let's look
    briefly at how to define _records_ and their types.  Intuitively,
    records can be obtained from pairs by two straightforward
    generalizations: they are n-ary (rather than just binary) and
    their fields are accessed by _label_ (rather than position). *)
(** TERSE: As a final example, records can be presented as a
    generalization of pairs:
       - they are n-ary (rather than binary);
       - they are accessed by _label_ (rather than position). *)
(* SOONER: Too terse? *)

(** TERSE: *** *)

(** Syntax:
<<
       t ::=                          Terms
           | ...
           | {i1=t1, ..., in=tn}         record
           | t0.i                        projection

       v ::=                          Values
           | ...
           | {i1=v1, ..., in=vn}         record value

       T ::=                          Types
           | ...
           | {i1:T1, ..., in:Tn}         record type
>>
*)

(** FULL: The generalization from products should be pretty obvious.  But
   it's worth noticing the ways in which what we've actually written is
   even _more_ informal than the informal syntax we've used in previous
   sections and chapters: we've used "[...]" in several places to mean "any
   number of these," and we've omitted explicit mention of the usual
   side condition that the labels of a record should not contain any
   repetitions. *)

(** TERSE: *** *)

(** TERSE: Note that this is a quite informal definition compared to
    previous ones:

    - it uses "[...]" in the syntax for records
    - it omits a usual side condition that the labels of a record should
      not contain repetitions. *)

(** TERSE: *** *)
(**
   Reduction:
[[[
                              ti --> ti'
                 ------------------------------------                  (ST_Rcd)
                     {i1=v1, ..., im=vm, in=ti , ...}
                 --> {i1=v1, ..., im=vm, in=ti', ...}

                              t0 --> t0'
                            --------------                           (ST_Proj1)
                            t0.i --> t0'.i

                      -------------------------                    (ST_ProjRcd)
                      {..., i=vi, ...}.i --> vi
]]]
*)

(** FULL: Again, these rules are a bit informal.  For example, the first rule
    is intended to be read "if [ti] is the leftmost field that is not a
    value and if [ti] steps to [ti'], then the whole record steps..."
    In the last rule, the intention is that there should be only one
    field called [i], and that all the other fields must contain values. *)
(** TERSE:
    - In the first rule, [ti] must be the leftmost field that is not a value;
    - In the last rule, there should be only one field called [i],
      and all the other fields must contain values. *)

(** TERSE: *** *)
(** The typing rules are also simple:
[[[
            Gamma |-- t1 \in T1     ...     Gamma |-- tn \in Tn
          -----------------------------------------------------        (T_Rcd)
          Gamma |-- {i1=t1, ..., in=tn} \in {i1:T1, ..., in:Tn}


                    Gamma |-- t0 \in {..., i:Ti, ...}
                    ---------------------------------                  (T_Proj)
                          Gamma |-- t0.i \in Ti
]]]
*)

(** FULL: There are several ways to approach formalizing the above
    definitions.

      - We can directly formalize the syntactic forms and inference
        rules, staying as close as possible to the form we've given
        them above.  This is conceptually straightforward, and it's
        probably what we'd want to do if we were building a real
        compiler (in particular, it will allow us to print error
        messages in the form that programmers will find easy to
        understand).  But the formal versions of the rules will not be
        very pretty or easy to work with, because all the [...]s above
        will have to be replaced with explicit quantifications or
        comprehensions.  For this reason, records are not included in
        the extended exercise at the end of this chapter.  (It is
        still useful to discuss them informally here because they will
        help motivate the addition of subtyping to the type system
        when we get to the \CHAP{Sub} chapter.)

      - Alternatively, we could look for a smoother way of presenting
        records -- for example, a binary presentation with one
        constructor for the empty record and another constructor for
        adding a single field to an existing record, instead of a
        single monolithic constructor that builds a whole record at
        once.  This is the right way to go if we are primarily
        interested in studying the metatheory of the calculi with
        records, since it leads to clean and elegant definitions and
        proofs.  Chapter \CHAP{Records} shows how this can be done.

      - Finally, if we like, we can avoid formalizing records
        altogether, by stipulating that record notations are just
        informal shorthands for more complex expressions involving
        pairs and product types.  We sketch this approach in the next
        section. *)
(** TERSE: Formalizing all this takes some work.  See the \CHAP{Records}
    chapter for details. *)

(* FULL *)
(* ###################################################################### *)
(** *** Encoding Records (Optional) *)

(** Let's see how records can be encoded using just pairs and
    [unit].  (This clever encoding, as well as the observation that it
    also extends to systems with subtyping, is due to Luca Cardelli.)

    First, observe that we can encode arbitrary-size _tuples_ using
    nested pairs and the [unit] value.  To avoid overloading the pair
    notation [(t1,t2)], we'll use curly braces without labels to write
    down tuples, so [{}] is the empty tuple, [{5}] is a singleton
    tuple, [{5,6}] is a 2-tuple (morally the same as a pair),
    [{5,6,7}] is a triple, etc.
<<
      {}                 ---->  unit
      {t1, t2, ..., tn}  ---->  (t1, trest)
                                where {t2, ..., tn} ----> trest
>>
    Similarly, we can encode tuple types using nested product types:
<<
      {}                 ---->  Unit
      {T1, T2, ..., Tn}  ---->  T1 * TRest
                                where {T2, ..., Tn} ----> TRest
>>
    The operation of projecting a field from a tuple can be encoded
    using a sequence of second projections followed by a first
    projection:
<<
      t.0        ---->  t.fst
      t.(n+1)    ---->  (t.snd).n
>>
    Next, suppose that there is some total ordering on record labels,
    so that we can associate each label with a unique natural number.
    This number is called the _position_ of the label.  For example,
    we might assign positions like this:
<<
      LABEL   POSITION
      a       0
      b       1
      c       2
      ...     ...
      bar     1395
      ...     ...
      foo     4460
      ...     ...
>>
    We use these positions to encode record values as tuples (i.e., as
    nested pairs) by sorting the fields according to their positions.
    For example:
<<
      {a=5,b=6}       ---->   {5,6}
      {a=5,c=7}       ---->   {5,unit,7}
      {c=7,a=5}       ---->   {5,unit,7}
      {c=5,b=3}       ---->   {unit,3,5}
      {f=8,c=5,a=7}   ---->   {7,unit,5,unit,unit,8}
      {f=8,c=5}       ---->   {unit,unit,5,unit,unit,8}
>>
    Note that each field appears in the position associated with its
    label, that the size of the tuple is determined by the label with
    the highest position, and that we fill in unused positions with
    [unit].

    We do exactly the same thing with record types:
<<
      {a:Nat,b:Nat}       ---->   {Nat,Nat}
      {c:Nat,a:Nat}       ---->   {Nat,Unit,Nat}
      {f:Nat,c:Nat}       ---->   {Unit,Unit,Nat,Unit,Unit,Nat}
>>
    Finally, record projection is encoded as a tuple projection from
    the appropriate position:
<<
      t.l ----> t.(position of l)
>>
    It is not hard to check that all the typing rules for the original
    "direct" presentation of records are validated by this
    encoding.  (The reduction rules are "almost validated" -- not
    quite, because the encoding reorders fields.) *)
(* LATER: This translation is not quite faithful in a certain sense,
   because a projection of a nonexistent field will be well typed (at
   type Unit), while it would be ill-typed in the language with real
   records.  Should this be mentioned? *)

(** FULL: Of course, this encoding will not be very efficient if we
    happen to use a record with label [foo]!  But things are not
    actually as bad as they might seem: for example, if we assume that
    our compiler can see the whole program at the same time, we can
    _choose_ the numbering of labels so that we assign small positions
    to the most frequently used labels.  Indeed, there are industrial
    compilers that essentially do this! *)
(* LATER: This trick is due to Cardelli.  He should be cited here, and
   in general there should be lots more citations everywhere! *)
(* /FULL *)

(* FULL *)
(** *** Variants (Optional) *)

(** Just as products can be generalized to records, sums can be
    generalized to n-ary labeled types called _variants_.  Instead of
    [T1+T2], we can write something like [<l1:T1,l2:T2,...ln:Tn>]
    where [l1],[l2],... are field labels which are used both to build
    instances and as case arm labels.

    These n-ary variants give us almost enough mechanism to build
    arbitrary inductive data types like lists and trees from
    scratch -- the only thing missing is a way to allow _recursion_ in
    type definitions.  We won't cover this here, but detailed
    treatments can be found in many textbooks -- e.g., Types and
    Programming Languages \CITE{Pierce 2002}. *)
(* /FULL *)


(* ###################################################################### *)
(** * Exercise: Formalizing the Extensions *)

(* FULL *)
Module STLCExtended.
(* /FULL *)

(** In this series of exercises, you will formalize some of the
    extensions described in this chapter.  We've provided the
    necessary additions to the syntax of terms and types, and we've
    included a few examples that you can test your definitions with to
    make sure they are working as expected.  You'll fill in the rest
    of the definitions and extend all the proofs accordingly.

    To get you started, we've provided implementations for:
     - numbers
     - sums
     - lists
     - unit

    You need to complete the implementations for:
     - pairs
     - let (which involves binding)
     - fix

    A good strategy is to work on the extensions one at a time (first
    pairs, then let, then fix), in separate passes, rather than trying
    to do all three at once in a single pass.  For each definition or
    proof, begin by reading carefully through the parts that are
    provided for you, referring to the text in the \CHAP{Stlc} chapter
    for high-level intuitions and the embedded comments for detailed
    mechanics. *)

(* FULL *)
(* ###################################################################### *)
(** *** Syntax *)

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty
  | Ty_Sum  : ty -> ty -> ty
  | Ty_List : ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty.

Inductive tm : Type :=
  (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* numbers *)
  | tm_const: nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* sums *)
  | tm_inl : ty -> tm -> tm
  | tm_inr : ty -> tm -> tm
  | tm_case : tm -> string -> tm -> string -> tm -> tm
          (* i.e., [case t0 of inl x1 => t1 | inr x2 => t2] *)
  (* lists *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., [case t1 of | nil => t2 | x::y => t3] *)
  (* unit *)
  | tm_unit : tm

  (* You are going to be working on the following extensions: *)

  (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
  (* let *)
  | tm_let : string -> tm -> tm -> tm
         (* i.e., [let x = t1 in t2] *)
  (* fix *)
  | tm_fix  : tm -> tm.

(** TERSE: *** *)
(** Note that, for brevity, we've omitted booleans and instead
    provided a single [if0] form combining a zero test and a
    conditional.  That is, instead of writing
<<
       if x = 0 then ... else ...
>>
    we'll write this:
<<
       if0 x then ... else ...
>>
*)
(* TERSE: HIDEFROMHTML *)
Definition w : string := "w".
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template stlc_ty *)
(* INSTRUCTORS: allow (global) identifiers,
  e.g. just a local variable or Fooo.bar.baz to appear as types. *)
Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.

(* INSTRUCTORS: quotation for shifting into stlc_ty parsing mode *)
Notation "<{{ x }}>" := x (x custom stlc_ty).

Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) : stlc_scope.
(* INSTRUCTORS: to extend this template, add new type constructs below. *)

(* NOTATION: SAZ 2024 - I recommend following the pattern below for all grammars *)
(* INSTRUCTORS: escape to arbitrary Rocq constr notation *)
Notation "$( t )" := t (in custom stlc_ty at level 0, t constr) : stlc_scope.
(* INSTRUCTORS: End Definition of template stlc_ty *)
(* INSTRUCTORS: ------------------------------------------------------------- *)

(* INSTRUCTORS: stcl_tm ----------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template stlc_tm *)
Notation "x" := x (in custom stlc_tm at level 0, x global) : stlc_scope.
Notation "'_'" := _ (in custom stlc_tm at level 0) : stlc_scope.
Notation "'$' x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'$(' x ')'" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "<{ e }>" := e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.

Notation "x y" := (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.
(* INSTRUCTORS: End Definition of template stlc_tm *)
(* INSTRUCTORS: ------------------------------------------------------------- *)

(* TERSE: /HIDEFROMHTML *)

(* HIDE *)
Check forall (T:ty), <{ \x : T , x }> = <{ \x : T, x }>.
Check forall (T:ty), <{ \x : T , x x }> = <{ \x : T, x x }>.
Fail Check forall (T:ty), <{ \x : T , x x }> = <{ \x : T, x $(S 0) }>.
(* /HIDE *)


(* NOTATION: SAZ 2024 [succ] and [pred] look like applications so they should
   be at the same precedence as application.  (Though these are right
   associative.)

   Question: I would prefer to *require* parentheses for [succ (succ x)] but
   Rocq's parser seems to allow [succ succ x] even if the term after [succ] is
   supposed to be at level 0 in the grammar as defined below.  I don't
   understand why [succ succ x] is even parsable.

   Answer: Rocq's notion of "grammar production" seems too be permissive.  If a
   production such as the one introduced for [succ] below calls into a another
   part of the grammar at a given level, e.g., [x custom stlc_tm at level 0]
   that *does not mean* that the *only* production that can parse [x] is at
   level 0 in the grammar.

   Seemingly the only way around this is to introduce *separate grammar entry*
   for each level, with explicit fall-through inclusions between them.  Then
   [level 0] of each such grammar can play the role of one production of the
   full term grammar. *)

(* HIDE *)
(*
Declare Custom Entry tm0.   (* terms at level 0 *)
Declare Custom Entry tm10.  (* terms at level 10 *)
Declare Custom Entry tm11.  (* etc. *)
Declare Custom Entry tm12.
Declare Custom Entry tm200.
Notation "x" := x (in custom tm10 at level 0, x custom tm0).
Notation "x" := x (in custom tm11 at level 0, x custom tm10).
Notation "x" := x (in custom tm12 at level 0, x custom tm11).
Notation "x" := x (in custom tm200 at level 0, x custom tm12).

Notation "succ x" := (tm_succ x) (in custom tm12 at level 0, x custom tm0 at level 0).
Notation "x y" := (tm_app x y) (in custom tm10 at level 0, x custom tm10, y custom tm 10).
*)
(* /HIDE *)
(* TERSE: HIDEFROMHTML *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template stlc_nat *)
Notation "'Nat'" := Ty_Nat (in custom stlc_ty at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc_tm at level 10,
                                     x custom stlc_tm at level 0) : stlc_scope.
Notation "'pred' x" := (tm_pred x) (in custom stlc_tm at level 10,
                                     x custom stlc_tm at level 0) : stlc_scope.
Notation "x * y" := (tm_mult x y) (in custom stlc_tm at level 95,
                                      right associativity) : stlc_scope.
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc_tm at level 0,
                    x custom stlc_tm at level 0,
                    y custom stlc_tm at level 0,
                    z custom stlc_tm at level 0) : stlc_scope.

Coercion tm_const : nat >-> tm.
(* INSTRUCTORS: End Definition of template stlc_nat *)
(* INSTRUCTORS: ------------------------------------------------------------- *)

(* HIDE *)
Check <{ succ x y }>.
Check <{ succ (x y) }>.
Check <{ succ $0 }>.
Check <{ $0 * $1 }>.
Check <{ $0 * pred $1 }>.
Check (fun (n:nat) => <{ $(S n) * $1 }>).
(* /HIDE *)

(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template stlc_sum *)
Notation "S + T" :=
  (Ty_Sum S T) (in custom stlc_ty at level 3, left associativity).
Notation "'inl' T t" := (tm_inl T t) (in custom stlc_tm at level 10,
                                         T custom stlc_ty,
                                         t custom stlc_tm at level 0).
Notation "'inr' T t" := (tm_inr T t) (in custom stlc_tm at level 10,
                                         T custom stlc_ty,
                                         t custom stlc_tm at level 0).
Notation "'case' t0 'of' '|' 'inl' x1 '=>' t1 '|' 'inr' x2 '=>' t2" :=
  (tm_case t0 x1 t1 x2 t2) (in custom stlc_tm at level 200,
                               t0 custom stlc_tm at level 200,
                               x1 global,
                               t1 custom stlc_tm at level 200,
                               x2 global,
                               t2 custom stlc_tm at level 200,
                               left associativity).
(* INSTRUCTORS: End Definition of template stlc_sum *)
(* INSTRUCTORS: ------------------------------------------------------------- *)


(* INSTRUCTORS: Begin template stlc_prod *)
Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc_ty at level 2, X custom stlc_ty, Y custom stlc_ty at level 0) : stlc_scope.

Notation "( x ',' y )" := (tm_pair x y) (in custom stlc_tm at level 0,
                                                x custom stlc_tm,
                                                y custom stlc_tm) : stlc_scope.
Notation "t '.fst'" := (tm_fst t) (in custom stlc_tm at level 1) : stlc_scope.
Notation "t '.snd'" := (tm_snd t) (in custom stlc_tm at level 1) : stlc_scope.
(* INSTRUCTORS: End Definition of template stlc_prod *)
(* INSTRUCTORS: ------------------------------------------------------------- *)

(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template stlc_list *)
Notation "'List' T" :=
  (Ty_List T) (in custom stlc_ty at level 4) : stlc_scope.
Notation "'List' T" := (Ty_List T) (at level 0) : stlc_scope.
Notation "'nil' T" := (tm_nil T) (in custom stlc_tm at level 0, T custom stlc_ty) : stlc_scope.
Notation "h '::' t" := (tm_cons h t) (in custom stlc_tm at level 2, right associativity) : stlc_scope.
Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tm_lcase t1 t2 x y t3) (in custom stlc_tm at level 200,
                              t1 custom stlc_tm at level 200,
                              t2 custom stlc_tm at level 0,
                              x global,
                              y global,
                              t3 custom stlc_tm at level 0,
                              left associativity) : stlc_scope.
(* INSTRUCTORS: End Definition of template stlc_list *)


(* INSTRUCTORS: Begin Definition of template stlc_unit *)
Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc_ty at level 0) : stlc_scope.
Notation "'unit'" := tm_unit (in custom stlc_tm at level 0) : stlc_scope.
(* INSTRUCTORS: End Definition of template stlc_unit *)

(* INSTRUCTORS: Begin Definition of template stlc_let *)
Notation "'let' x '=' t1 'in' t2" :=
  (tm_let x t1 t2) (in custom stlc_tm at level 200) : stlc_scope.
(* INSTRUCTORS: End Definition template of stlc_let *)

(* INSTRUCTORS: Begin Definition of template stlc_fix *)
Notation "'fix' t" := (tm_fix t) (in custom stlc_tm at level 200) : stlc_scope.
(* INSTRUCTORS: End Definition of template stlc_fix *)

(* HIDE *)
Check <{{Nat -> Nat}}>.
Check <{x}>.
Check <{x y}>.
Check <{(x y) (x y)}>.
Check <{x (y x) y x y}>.

Check <{x}>.

Check <{ x y }>.

Check <{ \ x : Unit , x }>.

Check <{ \x : Unit, x * x }>.

Check <{ \x : Unit * Unit , x }>.

Check fun x => <{ \y : x, y }>.

Check <{ \x : Unit , $(S 1) }>.

Check <{ if0 $0 then $0 else $1 }>.
Check <{ if0 $0 * $2 then $0 else $1 }>.
Check <{ if0 ($0 * $2) then $0 else $1 }>.
Check <{ case x of | inl y => $1 | inr z => $(S 0) }>.
Check <{ case x of | nil => $1 | y :: z => $2 }>.
Check <{ case (inl Nat $1) of | inl x => x | inr x => x }>.

Check <{ \x: Unit, (x,x)  }>.
(* /HIDE *)
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** *** Substitution *)

(* TERSE: HIDEFROMHTML *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template subst *)
(* NOTATION: SAZ 2024 - I think this notation should bind tigher than
application, which is a good reason to put application higher than
level 1 in the base stlc_tm grammar. *)
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).
(* INSTRUCTORS: End Definition of subst subst *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* TERSE: /HIDEFROMHTML *)

(* EX3 (STLCExtended.subst) *)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ ([x := s] t1)}>
  | <{pred t1}> =>
      <{pred ([x := s] t1)}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  (* sums *)
  | <{inl T2 t1}> =>
      <{inl T2 ( [x:=s] t1) }>
  | <{inr T1 t2}> =>
      <{inr T1 ( [x:=s] t2) }>
  | <{case t0 of | inl y1 => t1 | inr y2 => t2}> =>
      <{case ([x:=s] t0) of
         | inl y1 => $(if String.eqb x y1 then t1 else <{ [x:=s] t1 }> )
         | inr y2 => $(if String.eqb x y2 then t2 else <{ [x:=s] t2 }> ) }>
  (* lists *)
  | <{nil T}> =>
      t
  | <{t1 :: t2}> =>
      <{ ([x:=s] t1) :: [x:=s] t2 }>
  | <{case t1 of | nil => t2 | y1 :: y2 => t3}> =>
      <{case ( [x:=s] t1 ) of
        | nil => [x:=s] t2
        | y1 :: y2 =>
        $(if String.eqb x y1 then
           t3
         else if String.eqb x y2 then t3
              else <{ [x:=s] t3 }>) }>
  (* unit *)
  | <{unit}> => <{unit}>

  (* Complete the following cases. *)

  (* pairs *)
  (* SOLUTION *)
  | <{(t1, t2)}> =>
      <{ ([x:=s] t1 , [x:=s] t2) }>
  | <{t0.fst}> =>
      <{ ([x:=s] t0).fst}>
  | <{t0.snd}> =>
      <{ ([x:=s] t0).snd}>
  (* /SOLUTION *)
  (* let *)
  (* SOLUTION *)
  | <{let y = t1 in t2}> =>
      <{let y = [x:=s] t1
        in $(if String.eqb x y then t2 else <{ [x:=s] t2 }>) }>
  (* /SOLUTION *)
  (* fix *)
  (* SOLUTION *)
  | <{ fix t1 }> =>
      <{ fix ([x:=s] t1) }>
  (* /SOLUTION *)
(* UNCOMMENT WHEN HIDING SOLUTIONS
  | _ => t  (* ... and delete this line when you finish the exercise *)
/UNCOMMENT *)
  end
(* SOONER: We need to add a test case somewhere that exercises the
   situation "[x:=s] (let x = foo in bar)" *)
(* SOONER: Also, a common failure mode seems to be that the definition
   of subst for the let construct used the variable x without binding
   it with an universal quantifier. So the let rule was specialized to
   the specific variable x rather than quantifying over all
   variables. How could we help people avoid this? *)

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm) : stlc_scope.

(* INSTRUCTORS: BCP23: a common failure mode seems to be that the
   definition of subst for the let construct used the variable x without
   binding it with an universal quantifier. So the let rule was specialized
   to the specific variable x rather than quantifying over all
   variables. Hopefully the following unit tests will help! *)
(* Make sure the following tests are valid by reflexivity: *)
Example substeg1 :
  <{ [z:=$0] (let w = z in z) }> = <{ let w = $0 in $0 }>.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  reflexivity.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)

Example substeg2 :
  <{ [z:=$0] (let w = z in w) }> = <{ let w = $0 in w }>.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  reflexivity.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)

Example substeg3 :
  <{ [z:=$0] (let y = succ $0 in z) }> = <{ let y = succ $0 in $0 }>.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  reflexivity.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)

(** [] *)

(* ###################################################################### *)
(** *** Reduction *)

(** Next we define the values of our language. *)

(* HIDE: arguably the "most correct" definition of list values uses
   mutual induction:

       Inductive lvalue : tm -> Prop :=
         | lv_nil : forall T,
           lvalue (tm_nil T)
         | lv_cons : forall v1 v2,
           value v1 ->
           lvalue v2 ->
           lvalue (tm_cons v1 v2)
       with value ...

   The definition below is ... wrong!?  [BCP: Well, it's more the idea
   of cons-cells and less the idea of lists.  But I don't think it's
   straight-up wrong.]
   [Lef: I don't think this is better or "more correct",
   as long as we use typing for well-formedness in conjunction
   with [value], it should be equivalent.]
*)

Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  (* Numbers are values: *)
  | v_nat : forall n : nat,
      value <{n}>
  (* A tagged value is a value:  *)
  | v_inl : forall v T1,
      value v ->
      value <{inl T1 v}>
  | v_inr : forall v T1,
      value v ->
      value <{inr T1 v}>
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T1, value <{nil T1}>
  | v_lcons : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{v1 :: v2}>
  (* A unit is always a value *)
  | v_unit : value <{unit}>
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>.

Hint Constructors value : core.

(* HIDEFROMHTML *)
Reserved Notation "t '-->' t'" (at level 40).
(* /HIDEFROMHTML *)

(** TERSE: *** *)

(* INSTRUCTORS: One gotcha with the new notation.  If a student writes
   something like [<{ pred n }> --> <{ $(pred n) }>] that will fail to
   parse because [pred] is now treated as notation for `tm_pred`.  The
   fix is to write it as shown below.
 *)

(* EX3 (STLCExtended.step) *)
Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  (* numbers *)
  | ST_Succ : forall t1 t1',
         t1 --> t1' ->
         <{succ t1}> --> <{succ t1'}>
  | ST_SuccNat : forall n : nat,
         <{succ n}> --> <{ $(S n) }>
  | ST_Pred : forall t1 t1',
         t1 --> t1' ->
         <{pred t1}> --> <{pred t1'}>
  | ST_PredNat : forall n:nat,
         <{pred n}> --> <{ $(n - 1) }>
  | ST_Mulconsts : forall n1 n2 : nat,
         <{n1 * n2}> --> <{ $(n1 * n2) }>
  | ST_Mult1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 * t2}> --> <{t1' * t2}>
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 * t2}> --> <{v1 * t2'}>
  | ST_If0 : forall t1 t1' t2 t3,
         t1 --> t1' ->
         <{if0 t1 then t2 else t3}> --> <{if0 t1' then t2 else t3}>
  | ST_If0_Zero : forall t2 t3,
         <{if0 $0 then t2 else t3}> --> t2
  | ST_If0_Nonzero : forall n t2 t3,
         <{if0 $(S n) then t2 else t3}> --> t3
  (* sums *)
  | ST_Inl : forall t1 t1' T2,
        t1 --> t1' ->
        <{inl T2 t1}> --> <{inl T2 t1'}>
  | ST_Inr : forall t2 t2' T1,
        t2 --> t2' ->
        <{inr T1 t2}> --> <{inr T1 t2'}>
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        <{case t0 of | inl x1 => t1 | inr x2 => t2}> -->
        <{case t0' of | inl x1 => t1 | inr x2 => t2}>
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T2,
        value v0 ->
        <{case inl T2 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x1:=v0]t1 }>
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T1,
        value v0 ->
        <{case inr T1 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x2:=v0]t2 }>
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{t1 :: t2}> --> <{t1' :: t2}>
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{v1 :: t2}> --> <{v1 :: t2'}>
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       <{case t1 of | nil => t2 | x1 :: x2 => t3}> -->
       <{case t1' of | nil => t2 | x1 :: x2 => t3}>
  | ST_LcaseNil : forall T1 t2 x1 x2 t3,
       <{case nil T1 of | nil => t2 | x1 :: x2 => t3}> --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       <{case v1 :: vl of | nil => t2 | x1 :: x2 => t3}>
         -->  <{ [x2 := vl] ([x1 := v1] t3) }>

  (* Add rules for the following extensions. *)

  (* pairs *)
  (* SOLUTION *)
  | ST_Pair1 : forall t1 t1' t2,
        t1 --> t1' ->
        <{ (t1,t2) }> --> <{ (t1' , t2) }>
  | ST_Pair2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        <{ (v1, t2) }> -->  <{ (v1, t2') }>
  | ST_Fst1 : forall t0 t0',
        t0 --> t0' ->
        <{ t0.fst }> --> <{ t0'.fst }>
  | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ (v1,v2).fst }> --> v1
  | ST_Snd1 : forall t0 t0',
        t0 --> t0' ->
        <{ t0.snd }> --> <{ t0'.snd }>
  | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ (v1,v2).snd }> --> v2
  (* /SOLUTION *)
  (* let *)
  (* SOLUTION *)
  | ST_Let1 : forall x t1 t1' t2,
       t1 --> t1' ->
       <{ let x = t1 in t2}> --> <{ let x = t1' in t2 }>
  | ST_LetValue : forall x v1 t2,
       value v1 ->
       <{ let x = v1 in t2 }> --> <{ [x:=v1]t2 }>
  (* /SOLUTION *)
  (* fix *)
  (* SOLUTION *)
  | ST_Fix1 : forall t1 t1',
       t1 --> t1' ->
       <{ fix t1 }> --> <{ fix t1' }>
   | ST_FixAbs : forall x T1 t1,
      <{ fix (\ x : T1, t1) }> -->
      <{ [x := fix \x : T1, t1 ] t1 }>
  (* /SOLUTION *)

  where "t '-->' t'" := (step t t').

(** [] *)

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

(* ###################################################################### *)
(** *** Typing *)

(** TERSE: *** *)

(* TERSE: HIDEFROMHTML *)
Definition context := partial_map ty.
(* TERSE: /HIDEFROMHTML *)

(** Next we define the typing rules.  These are nearly direct
    transcriptions of the inference rules shown above. *)

(* HIDEFROMHTML *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template STCL has_type notation *)
Notation "x '|->' v ';' m " := (update m x v)
  (in custom stlc_tm at level 0, x global, v custom stlc_ty, right associativity) : stlc_scope.

Notation "x '|->' v " := (update empty x v)
  (in custom stlc_tm at level 0, x global, v custom stlc_ty) : stlc_scope.

(* NOTATION: If we don't include the following, then <{ empty |-- t : T }>
   will print as <{ $(empty) |-- t : T }>
 *)
Notation "'empty'" := empty (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
            (at level 0, Gamma custom stlc_tm at level 200, t custom stlc_tm, T custom stlc_ty).
(* INSTRUCTORS: End STCL has_type notation *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* /HIDEFROMHTML *)


(* EX3 (STLCExtended.has_type) *)
Inductive has_type : context -> tm -> ty -> Prop :=
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      <{ Gamma |-- x \in T1 }>
  | T_Abs : forall Gamma x T1 T2 t1,
(* NOTATION: NOWISH: Ori: again, in previous files I did not parantheses*)
    <{ x |-> T2 ; Gamma |-- t1 \in T1 }> ->
    <{ Gamma |-- \x:T2, t1 \in T2 -> T1 }>
  | T_App : forall T1 T2 Gamma t1 t2,
      <{ Gamma |-- t1 \in T2 -> T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- t1 t2 \in T1 }>
  (* numbers *)
  | T_Nat : forall Gamma (n : nat),
      <{ Gamma |-- n \in Nat }>
  | T_Succ : forall Gamma t,
      <{ Gamma |-- t \in Nat }> ->
      <{ Gamma |-- succ t \in Nat }>
  | T_Pred : forall Gamma t,
      <{ Gamma |-- t \in Nat }> ->
      <{ Gamma |-- pred t \in Nat }>
  | T_Mult : forall Gamma t1 t2,
      <{ Gamma |-- t1 \in Nat }> ->
      <{ Gamma |-- t2 \in Nat }> ->
      <{ Gamma |-- t1 * t2 \in Nat }>
  | T_If0 : forall Gamma t1 t2 t3 T0,
      <{ Gamma |-- t1 \in Nat }> ->
      <{ Gamma |-- t2 \in T0 }> ->
      <{ Gamma |-- t3 \in T0 }> ->
      <{ Gamma |-- if0 t1 then t2 else t3 \in T0 }>
  (* sums *)
  | T_Inl : forall Gamma t1 T1 T2,
      <{ Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- (inl T2 t1) \in T1 + T2 }>
  | T_Inr : forall Gamma t2 T1 T2,
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- (inr T1 t2) \in T1 + T2 }>
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T3,
      <{ Gamma |-- t0 \in T1 + T2 }> ->
      <{ x1 |-> T1 ; Gamma |-- t1 \in T3 }> ->
      <{ x2 |-> T2 ; Gamma |-- t2 \in T3 }> ->
      <{ Gamma |-- case t0 of | inl x1 => t1 | inr x2 => t2 \in T3 }>
  (* lists *)
  | T_Nil : forall Gamma T1,
      <{ Gamma |-- nil T1 \in List T1 }>
  | T_Cons : forall Gamma t1 t2 T1,
      <{ Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- t2 \in List T1 }> ->
      <{ Gamma |-- t1 :: t2 \in List T1 }>
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      <{ Gamma |-- t1 \in List T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ x1 |-> T1 ; x2 |-> List T1 ; Gamma |-- t3 \in T2 }> ->
      <{ Gamma |-- case t1 of | nil => t2 | x1 :: x2 => t3 \in T2 }>
  (* unit *)
  | T_Unit : forall Gamma,
      <{ Gamma |-- unit \in Unit }>

  (* Add rules for the following extensions. *)

  (* pairs *)
  (* SOLUTION *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      <{ Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- (t1, t2) \in T1 * T2 }>
  | T_Fst : forall Gamma t0 T1 T2,
      <{ Gamma |-- t0 \in T1 * T2 }> ->
      <{ Gamma |-- t0.fst \in T1 }>
  | T_Snd : forall Gamma t0 T1 T2,
      <{ Gamma |-- t0 \in T1 * T2 }> ->
      <{ Gamma |-- t0.snd \in T2 }>
  (* /SOLUTION *)
  (* let *)
  (* SOLUTION *)
  | T_Let : forall Gamma x t1 T1 t2 T2,
      <{ Gamma |-- t1 \in T1 }> ->
      <{ x |-> T1 ; Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- let x = t1 in t2 \in T2 }>
  (* /SOLUTION *)
  (* fix *)
  (* SOLUTION *)
  | T_Fix : forall Gamma t1 T1,
      <{ Gamma |-- t1 \in T1 -> T1 }> ->
      <{ Gamma |-- fix t1 \in T1 }>
  (* /SOLUTION *)

where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T).

(** [] *)

Hint Constructors has_type : core.

(* ###################################################################### *)
(** ** Examples *)

(* EX5? (STLCExtended_examples) *)
(** This section presents formalized versions of the examples from
    above (plus several more).

    For each example, uncomment proofs and replace [Admitted] by
    [Qed] once you've implemented enough of the definitions for
    the tests to pass.

    The examples at the beginning focus on specific features; you can
    use these to make sure your definition of a given feature is
    reasonable before moving on to extending the proofs later in the
    file with the cases relating to this feature.
    The later examples require all the features together, so you'll
    need to come back to these when you've got all the definitions
    filled in. *)

Module Examples.

(** *** Preliminaries *)

(** FULL: First, let's define a few variable names: *)

Open Scope string_scope.
(* NOTATION: LATER: These can all be Notations -- just make sure to add a
   [Hint Unfold] for each one. *)
Notation x := "x".
Notation y := "y".
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".
Notation processSum := "processSum".
Notation n := "n".
Notation eq := "eq".
Notation m := "m".
Notation evenodd := "evenodd".
Notation even := "even".
Notation odd := "odd".
Notation eo := "eo".

(** Next, a bit of Rocq hackery to automate searching for typing
    derivations.  You don't need to understand this bit in detail --
    just have a look over it so that you'll know what to look for if
    you ever find yourself needing to make custom extensions to
    [auto].

    The following [Hint] declarations say that, whenever [auto]
    arrives at a goal of the form [(Gamma |-- (tm_app e1 e1) \in T)], it
    should consider [eapply T_App], leaving an existential variable
    for the middle type T1, and similar for [lcase]. That variable
    will then be filled in during the search for type derivations for
    [e1] and [e2].  We also include a hint to "try harder" when
    solving equality goals; this is useful to automate uses of
    [T_Var] (which includes an equality as a precondition). *)

Hint Extern 2 (has_type _ (tm_app _ _) _) =>
  eapply T_App; auto : core.
Hint Extern 2 (has_type _ (tm_lcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

(** *** Numbers *)

(* SOONER: BCP 21: Two students this year got very stuck because they
   had forgotten a quantifier for x in a reduction rule, and this
   prevented the examples from working even though the rest of the
   rule is perfect. We should give some advice about debugging (this
   and other issues).
     - The [normalize] tactic is opaque.  We should explain what to do
       if it isn't doing anything.  Namely try doing stuff like
           eapply multi_step.
           apply ST_Let1.
       instead and see where the rule you think should apply does not.
     - If you see errors like this, it means you forgot a quantifier (for x):
          Error: Unable to unify
           "tm_let STLCExtended.x ?M2001 ?M2003 -->
                   tm_let STLCExtended.x ?M2002 ?M2003"
          with
           "tm_let "evenodd"
              (tm_fix
                 <{
                 \ "eo" : (Nat -> Nat) * (Nat -> Nat),
                 (\ "n" : Nat, if0 "n" then 1 else (tm_snd "eo") pred "n",
                 \ "n" : Nat, if0 "n" then 0 else (tm_fst "eo") pred "n") }>)
              (tm_let "even" (tm_fst "evenodd")
                 (tm_let "odd" (tm_snd "evenodd")
                         <{ ("even" 3, "even" 4) }>)) -->
            ?y".
  - BCP 23: Hopefully I've added enough examples that the issue with LET
    is better now, at least.
 *)
(* HIDEFROMHTML *)
Module Numtest.
(* /HIDEFROMHTML *)

Definition tm_test :=
  <{if0
    (pred
      (succ
        (pred
          ($2 * $0))))
    then $5
    else $6}>.

Example typechecks :
  <{ empty |-- tm_test \in Nat }>.
Proof.
  unfold tm_test.
  (* This typing derivation is quite deep, so we need
     to increase the max search depth of [auto] from the
     default 5 to 10. *)
  auto 10.
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: typechecks *)

Example reduces :
  tm_test -->* 5.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  unfold tm_test. normalize.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: reduces *)

End Numtest.

(** *** Products *)

Module ProdTest.

Definition tm_test :=
  <{(($5,$6),$7).fst.snd}>.

Example typechecks :
  <{ empty |-- tm_test \in Nat }>.
Proof. unfold tm_test. eauto. (* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: typechecks *)

Example reduces :
  tm_test -->* 6.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  unfold tm_test. normalize.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: reduces *)

End ProdTest.

(** *** [let] *)

Module LetTest.

Definition tm_test :=
  <{let x = (pred $6) in
    (succ x)}>.

Example typechecks :
  <{ empty |-- tm_test \in Nat }>.
Proof. unfold tm_test. eauto.
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: typechecks *)

Example reduces :
  tm_test -->* 6.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  unfold tm_test. normalize.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: reduces *)

End LetTest.

Module LetTest1.

Definition tm_test :=
  <{ let z = pred $6 in
     (succ z) }>.

Example typechecks :
  <{ empty |-- tm_test \in Nat }>.
Proof. unfold tm_test. eauto.
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: typechecks *)

Example reduces :
  tm_test -->* 6.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  unfold tm_test. normalize.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: reduces *)

End LetTest1.

(** *** Sums *)

Module Sumtest1.

Definition tm_test :=
  <{ case (inl Nat $5) of
     | inl x => x
     | inr y => y }>.

Example typechecks :
  <{ empty |-- tm_test \in Nat }>.
Proof. unfold tm_test. eauto. (* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: typechecks *)

Example reduces :
  tm_test -->* 5.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  unfold tm_test. normalize.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: reduces *)

End Sumtest1.

Module Sumtest2.

(* let processSum =
     \x:Nat+Nat.
        case x of
          inl n => n
          inr n => tm_test0 n then 1 else 0 in
   (processSum (inl Nat 5), processSum (inr Nat 5))    *)

Definition tm_test :=
  <{ let processSum =
     (\x:Nat + Nat,
       case x of
        | inl n => n
        | inr n => (if0 n then $1 else $0)) in
     (processSum (inl Nat $5), processSum (inr Nat $5)) }>.

Example typechecks :
  <{ empty |-- tm_test \in Nat * Nat }>.
Proof. unfold tm_test. eauto 10. (* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: typechecks *)

Example reduces :
  tm_test -->* <{ ($5, $0) }>.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  unfold tm_test. normalize.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: reduces *)

End Sumtest2.

(** *** Lists *)

Module ListTest.

(* let l = cons 5 (cons 6 (nil Nat)) in
   case l of
     nil => 0
   | x::y => x*x *)

Definition tm_test :=
  <{ let l = ($5 :: $6 :: (nil Nat)) in
     case l of
     | nil => $0
     | x :: y => (x * x) }>.

Example typechecks :
  <{ empty |-- tm_test \in Nat }>.
Proof. unfold tm_test. eauto. (* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: typechecks *)

Example reduces :
  tm_test -->* 25.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  unfold tm_test. normalize.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: reduces *)

End ListTest.


(** *** [fix] *)

Module FixTest1.

Definition fact :=
  <{ fix
      (\f:Nat->Nat,
        \a:Nat,
         if0 a then $1 else (a * (f (pred a)))) }>.

(** (Warning: you may be able to typecheck [fact] but still have some
    rules wrong!) *)
(* LATER: add more tests to help? *)

Example typechecks :
  <{ empty |-- fact \in Nat -> Nat }>.
Proof. unfold fact. auto 10. (* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: typechecks *)

Example reduces :
  <{ fact $4 }> -->* 24.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  unfold fact. normalize.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: reduces *)

End FixTest1.

Module FixTest2.

Definition map :=
  <{ \g:Nat->Nat,
       fix
         (\f:(List Nat)->(List Nat),
            \l:List Nat,
               case l of
               | nil => nil Nat
               | x::l => ((g x)::(f l))) }>.

Example typechecks :
  <{ empty |-- map \in
     (Nat -> Nat) -> (List Nat) -> (List Nat) }>.
Proof. unfold map. auto 10. (* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: typechecks *)

Example reduces :
  <{ map (\a:Nat, succ a) ($1 :: $2 :: (nil Nat)) }>
  -->* <{ $2 :: $3 :: (nil Nat) }>.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  unfold map. normalize.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: reduces *)

End FixTest2.

Module FixTest3.

Definition equal :=
  <{ fix
        (\eq:Nat->Nat->Nat,
           \m:Nat, \n:Nat,
             if0 m then (if0 n then $1 else $0)
             else (if0 n
                   then $0
                   else (eq (pred m) (pred n)))) }>.

Example typechecks :
 <{ empty |-- equal \in Nat -> Nat -> Nat }>.
Proof. unfold equal. auto 10. (* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: typechecks *)

Example reduces :
  <{ equal $4 $4 }> -->* 1.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  unfold equal. normalize.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.25: reduces *)

Example reduces2 :
  <{ equal $4 $5 }> -->* 0.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  unfold equal. normalize.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.25: reduces2 *)

End FixTest3.

Module FixTest4.

Definition eotest :=
  <{ let evenodd =
           fix
           (\eo: (Nat -> Nat) * (Nat -> Nat),
              (\n:Nat, if0 n then $1 else (eo.snd (pred n)),
               \n:Nat, if0 n then $0 else (eo.fst (pred n)))) in
     let even = evenodd.fst in
     let odd  = evenodd.snd in
     (even $3, even $4) }>.

Example typechecks :
  <{ empty |-- eotest \in Nat * Nat }>.
Proof. unfold eotest. eauto 30. (* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: typechecks *)

Example reduces :
  eotest -->* <{ ($0, $1) }>.
Proof.
(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
  unfold eotest. eauto 10. normalize.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* GRADE_THEOREM 0.5: reduces *)

End FixTest4.
End Examples.
(** [] *)

(* ###################################################################### *)
(** ** Properties of Typing *)

(** The proofs of progress and preservation for this enriched system
    are essentially the same (though of course longer) as for the pure
    STLC. *)
(* INSTRUCTORS: These need to be graded manually, because if
   the relevant definitions aren't implemented above and below, then
   the missing cases don't appear in the proofs. *)
(* LATER: These are not as automated as the ones currently in
   Stlc.v -- is that what we want?  (I think so, because it will make
   the exercise make more sense. --BCP) *)

(* ###################################################################### *)
(** *** Progress *)

(* EX3 (STLCExtended.progress) *)
(** Complete the proof of [progress].

    Theorem: Suppose empty |-- t \in T.  Then either
      1. t is a value, or
      2. t --> t' for some t'.

    Proof: By induction on the given typing derivation. *)
Theorem progress : forall t T,
     <{ empty |-- t \in T }> ->
     value t \/ exists t', t --> t'.
(* FOLD *)
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst.
  - (* T_Var *)
    (* The final rule in the given typing derivation cannot be
       [T_Var], since it can never be the case that
       [empty |-- x \in T] (since the context is empty). *)
    discriminate H.
  - (* T_Abs *)
    (* If the [T_Abs] rule was the last used, then
       [t = \ x0 : T2, t1], which is a value. *)
    left...
  - (* T_App *)
    (* If the last rule applied was T_App, then [t = t1 t2],
       and we know from the form of the rule that
         [empty |-- t1 \in T1 -> T2]
         [empty |-- t2 \in T1]
       By the induction hypothesis, each of t1 and t2 either is
       a value or can take a step. *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        (* If both [t1] and [t2] are values, then we know that
           [t1 = \x0 : T0, t11], since abstractions are the
           only values that can have an arrow type.  But
           [(\x0 : T0, t11) t2 --> [x:=t2]t11] by [ST_AppAbs]. *)
        destruct H; try solve_by_invert.
        exists <{ [x0 := t2]t1 }>...
      * (* t2 steps *)
        (* If [t1] is a value and [t2 --> t2'],
           then [t1 t2 --> t1 t2'] by [ST_App2]. *)
        destruct H0 as [t2' Hstp]. exists <{t1 t2'}>...
    + (* t1 steps *)
      (* Finally, If [t1 --> t1'], then [t1 t2 --> t1' t2]
         by [ST_App1]. *)
      destruct H as [t1' Hstp]. exists <{t1' t2}>...
  - (* T_Nat *)
    left...
  - (* T_Succ *)
    right.
    destruct IHHt...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      exists <{ $(S n) }>...
    + (* t1 steps *)
      destruct H as [t' Hstp].
      exists <{succ t'}>...
  - (* T_Pred *)
    right.
    destruct IHHt...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      exists <{ $(n - 1) }>...
    + (* t1 steps *)
      destruct H as [t' Hstp].
      exists <{pred t'}>...
  - (* T_Mult *)
    right.
    destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is a value *)
        destruct H; try solve_by_invert.
        destruct H0; try solve_by_invert.
        exists <{ $(n * n0) }>...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp].
        exists <{t1 * t2'}>...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      exists <{t1' * t2}>...
  - (* T_Test0 *)
    right.
    destruct IHHt1...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      destruct n as [|n'].
      * (* n1=0 *)
        exists t2...
      * (* n1<>0 *)
        exists t3...
    + (* t1 steps *)
      destruct H as [t1' H0].
      exists <{if0 t1' then t2 else t3}>...
  - (* T_Inl *)
    destruct IHHt...
    + (* t1 steps *)
      right. destruct H as [t1' Hstp]...
      (* exists (tm_inl _ t1')... *)
  - (* T_Inr *)
    destruct IHHt...
    + (* t1 steps *)
      right. destruct H as [t1' Hstp]...
      (* exists (tm_inr _ t1')... *)
  - (* T_Case *)
    right.
    destruct IHHt1...
    + (* t0 is a value *)
      destruct H; try solve_by_invert.
      * (* t0 is inl *)
        exists <{ [x1:=v]t1 }>...
      * (* t0 is inr *)
        exists <{ [x2:=v]t2 }>...
    + (* t0 steps *)
      destruct H as [t0' Hstp].
      exists <{case t0' of | inl x1 => t1 | inr x2 => t2}>...
  - (* T_Nil *)
    left...
  - (* T_Cons *)
    destruct IHHt1...
    + (* head is a value *)
      destruct IHHt2...
      * (* tail steps *)
        right. destruct H0 as [t2' Hstp].
        exists <{t1 :: t2'}>...
    + (* head steps *)
      right. destruct H as [t1' Hstp].
      exists <{t1' :: t2}>...
  - (* T_Lcase *)
    right.
    destruct IHHt1...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      * (* t1=tm_nil *)
        exists t2...
      * (* t1=tm_cons v1 v2 *)
        exists <{ [x2:=v2]([x1:=v1]t3) }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      exists <{case t1' of | nil => t2 | x1 :: x2 => t3}>...
  - (* T_Unit *)
    left...

  (* Complete the proof. *)

  (* pairs *)
  (* SOLUTION *)
  - (* T_Pair *)
    destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 steps *)
        right.  destruct H0 as [t2' Hstp].
        exists <{ (t1, t2') }>...
    + (* t1 steps *)
      right. inversion H as [t1' Hstp].
      exists <{ (t1', t2) }> ...
  - (* T_Fst *)
    right.
    destruct IHHt...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      exists v1...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      exists <{ t1'.fst }>...
  - (* T_Snd *)
    right.
    destruct IHHt...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      exists v2...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      exists <{ t1'.snd }>...
  (* /SOLUTION *)
  (* let *)
  (* SOLUTION *)
  - (* T_Let *)
    right.
    destruct IHHt1...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      exists <{ let x0 = t1' in t2 }>...
  (* /SOLUTION *)
  (* fix *)
  (* SOLUTION *)
  - (* T_Fix *)
    right.
    destruct IHHt...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      exists <{ [x0:=fix \x0:T2,t1]t1 }>...
    + (* t1 steps *)
      destruct H as [t1' H].
      exists <{ fix t1' }>...
  (* /SOLUTION *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* /FOLD *)

(** [] *)

(* ###################################################################### *)
(** ** Weakening *)

(** The weakening claim and (automated) proof are exactly the
    same as for the original STLC. (We only need to increase the
    search depth of eauto to 7.) *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     <{ Gamma  |-- t \in T }> ->
     <{ Gamma' |-- t \in T }>.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto 7 using includedin_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     <{ empty |-- t \in T }> ->
     <{ Gamma |-- t \in T }>.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* HIDE *)
(* ###################################################################### *)
(** *** Context Invariance *)

(* EX3 (STLCExtended.appears_free_in) *)
(** Complete the definition of [appears_free_in], and the proofs of
   [context_invariance] and [free_in_context]. *)

Inductive appears_free_in (x : string): tm -> Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : forall t1 t2,
      appears_free_in x t1 -> appears_free_in x <{t1 t2}>
  | afi_app2 : forall t1 t2,
      appears_free_in x t2 -> appears_free_in x <{t1 t2}>
  | afi_abs : forall y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x <{\y:T11, t12}>
  (* numbers *)
  | afi_succ : forall t,
     appears_free_in x t ->
     appears_free_in x <{succ t}>
  | afi_pred : forall t,
     appears_free_in x t ->
     appears_free_in x <{pred t}>
  | afi_mult1 : forall t1 t2,
     appears_free_in x t1 ->
     appears_free_in x <{t1 * t2}>
  | afi_mult2 : forall t1 t2,
     appears_free_in x t2 ->
     appears_free_in x <{t1 * t2}>
  | afi_test01 : forall t1 t2 t3,
     appears_free_in x t1 ->
     appears_free_in x <{if0 t1 then t2 else t3}>
  | afi_test02 : forall t1 t2 t3,
     appears_free_in x t2 ->
     appears_free_in x <{if0 t1 then t2 else t3}>
  | afi_test03 : forall t1 t2 t3,
     appears_free_in x t3 ->
     appears_free_in x <{if0 t1 then t2 else t3}>
  (* sums *)
  | afi_inl : forall t T,
      appears_free_in x t ->
      appears_free_in x <{inl T t}>
  | afi_inr : forall t T,
      appears_free_in x t ->
      appears_free_in x <{inr T t}>
  | afi_case0 : forall t0 x1 t1 x2 t2,
      appears_free_in x t0 ->
      appears_free_in x <{case t0 of | inl x1 => t1 | inr x2 => t2}>
  | afi_case1 : forall t0 x1 t1 x2 t2,
      x1 <> x ->
      appears_free_in x t1 ->
      appears_free_in x <{case t0 of | inl x1 => t1 | inr x2 => t2}>
  | afi_case2 : forall t0 x1 t1 x2 t2,
      x2 <> x ->
      appears_free_in x t2 ->
      appears_free_in x <{case t0 of | inl x1 => t1 | inr x2 => t2}>
  (* lists *)
  | afi_cons1 : forall t1 t2,
     appears_free_in x t1 ->
     appears_free_in x <{t1 :: t2}>
  | afi_cons2 : forall t1 t2,
     appears_free_in x t2 ->
     appears_free_in x <{t1 :: t2}>
  | afi_lcase1 : forall t1 t2 y1 y2 t3,
     appears_free_in x t1 ->
     appears_free_in x <{case t1 of | nil => t2 | y1 :: y2 => t3}>
  | afi_lcase2 : forall t1 t2 y1 y2 t3,
     appears_free_in x t2 ->
     appears_free_in x <{case t1 of | nil => t2 | y1 :: y2 => t3}>
  | afi_lcase3 : forall t1 t2 y1 y2 t3,
     y1 <> x ->
     y2 <> x ->
     appears_free_in x t3 ->
     appears_free_in x <{case t1 of | nil => t2 | y1 :: y2 => t3}>

  (* Add rules for the following extensions. *)

  (* pairs *)
  (* SOLUTION *)
  | afi_pair1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ (t1, t2) }>
  | afi_pair2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ (t1, t2) }>
  | afi_fst : forall t,
      appears_free_in x t ->
      appears_free_in x <{ t.fst }>
  | afi_snd : forall t,
      appears_free_in x t ->
      appears_free_in x <{ t.snd }>
  (* /SOLUTION *)
  (* let *)
  (* SOLUTION *)
  | afi_let1 : forall y t1 t2,
     appears_free_in x t1 ->
     appears_free_in x <{ let y = t1 in t2 }>
  | afi_let2 : forall y t1 t2,
     y <> x ->
     appears_free_in x t2 ->
     appears_free_in x <{ let y = t1 in t2 }>
  (* /SOLUTION *)
  (* fix *)
  (* SOLUTION *)
  | afi_fix : forall t,
     appears_free_in x t ->
     appears_free_in x <{ fix t }>
  (* /SOLUTION *)
.

(** [] *)

Hint Constructors appears_free_in : core.

(* EX3 (STLCExtended.context_invariance) *)
Lemma context_invariance : forall Gamma Gamma' t S,
     <{ Gamma |-- t \in S }> ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     <{ Gamma' |-- t \in S }>.
(* FOLD *)
(* Increasing the depth of [eauto] allows some more simple cases to
   be dispatched automatically. *)
Proof with eauto 30.
  intros. generalize dependent Gamma'.
  induction H;
    intros Gamma' Heqv...
  - (* T_Var *)
    apply T_Var... rewrite <- Heqv...
  - (* T_Abs *)
    apply T_Abs... apply IHhas_type. intros y Hafi.
    destruct (eqb_spec x0 y); subst.
    + rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + rewrite update_neq; [|assumption].
      rewrite update_neq; [|assumption].
      auto.
  - (* T_Case *)
    eapply T_Case...
    + apply IHhas_type2. intros y Hafi.
      destruct (eqb_spec x1 y); subst.
      * rewrite update_eq.
        rewrite update_eq.
        reflexivity.
      * rewrite update_neq; [|assumption].
        rewrite update_neq; [|assumption].
        auto.
    + apply IHhas_type3. intros y Hafi.
      destruct (eqb_spec x2 y); subst.
      * rewrite update_eq.
        rewrite update_eq.
        reflexivity.
      * rewrite update_neq; [|assumption].
        rewrite update_neq; [|assumption].
        auto.
  - (* T_Lcase *)
    eapply T_Lcase... apply IHhas_type3. intros y Hafi.
      destruct (eqb_spec x1 y); subst.
      * rewrite update_eq.
        rewrite update_eq.
        reflexivity.
      * rewrite update_neq; [|assumption].
        rewrite (update_neq _ _ _ _ _ n).
        destruct (eqb_spec x2 y); subst.
        -- rewrite update_eq.
           rewrite update_eq.
           reflexivity.
        -- rewrite update_neq; [|assumption].
           rewrite update_neq; [|assumption].
           auto.
  (* Complete the proof. *)

  (* ADMITTED *)
  - (* T_Let *)
    eapply T_Let... apply IHhas_type2. intros y Hafi.
    destruct (eqb_spec x0 y); subst.
    + rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + rewrite update_neq; [|assumption].
      rewrite update_neq; [|assumption].
      auto.
Qed. (* /ADMITTED *)
(* /FOLD *)

(** [] *)

(* EX3 (STLCExtended.free_in_context) *)
Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   <{ Gamma |-- t \in T }> ->
   exists T', Gamma x = Some T'.
(* FOLD *)
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  - (* T_Abs *)
    destruct IHHtyp as [T' Hctx]... exists T'.
    rewrite update_neq in Hctx; assumption.
  (* T_Case *)
  - (* left *)
    destruct IHHtyp2 as [T' Hctx]... exists T'.
    rewrite update_neq in Hctx; assumption.
  - (* right *)
    destruct IHHtyp3 as [T' Hctx]... exists T'.
    rewrite update_neq in Hctx; assumption.
  - (* T_Lcase *)
    clear Htyp1 IHHtyp1 Htyp2 IHHtyp2.
    destruct IHHtyp3 as [T' Hctx]... exists T'.
    rewrite update_neq in Hctx; [|assumption].
    rewrite update_neq in Hctx; assumption.

  (* Complete the proof. *)

  (* ADMITTED *)
  - (* T_Let *)
    clear Htyp1 IHHtyp1.
    destruct IHHtyp2 as [T' Hctx]... exists T'.
    rewrite update_neq in Hctx; assumption.
Qed. (* /ADMITTED *)
(* /FOLD *)

(** [] *)
(* /HIDE *)

(* ###################################################################### *)
(** *** Substitution *)

(* EX2 (STLCExtended.substitution_preserves_typing) *)
(** Complete the proof of [substitution_preserves_typing]. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ empty |-- v \in U }>  ->
  <{ Gamma |-- [x:=v]t \in T }>.
(* NOTATION: NOWISH: Ori: In this file, for some reason I need to use
 paratheses for (x |-> U ; Gamma) *)
(* FOLD *)
Proof with eauto.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  (* Proof: By induction on the term [t].  Most cases follow
     directly from the IH, with the exception of [var]
     and [abs]. These aren't automatic because we must
     reason about how the variables interact. The proofs
     of these cases are similar to the ones in STLC.
     We refer the reader to StlcProp.v for explanations. *)
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.

  - (* tm_case *)
    rename s into x1, s0 into x2.
    eapply T_Case...
    + (* left arm *)
      destruct (eqb_spec x x1); subst.
      * (* x = x1 *)
        rewrite update_shadow in H8. assumption.
      * (* x <> x1 *)
        apply IHt2.
        rewrite update_permute; auto.
    + (* right arm *)
      destruct (eqb_spec x x2); subst.
      * (* x = x2 *)
        rewrite update_shadow in H9. assumption.
      * (* x <> x2 *)
        apply IHt3.
        rewrite update_permute; auto.
  - (* tm_lcase *)
    rename s into y1, s0 into y2.
    eapply T_Lcase...
    destruct (eqb_spec x y1); subst.
    + (* x=y1 *)
      destruct (eqb_spec y2 y1); subst.
      * (* y2=y1 *)
        repeat rewrite update_shadow in H9.
        rewrite update_shadow.
        assumption.
      * rewrite update_permute in H9; [|assumption].
        rewrite update_shadow in H9.
        rewrite update_permute;  assumption.
    + (* x<>y1 *)
      destruct (eqb_spec x y2); subst.
      * (* x=y2 *)
        rewrite update_shadow in H9.
        assumption.
      * (* x<>y2 *)
        apply IHt3.
        rewrite (update_permute _ _ _ _ _ _ n0) in H9.
        rewrite (update_permute _ _ _ _ _ _ n) in H9.
        assumption.

  (* Complete the proof. *)

  (* ADMITTED *)
  - (* tm_let *)
    simpl. rename s into y.
    eapply T_Let...
    destruct (eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_shadow in H6. assumption.
    + (* x<>y *)
      apply IHt2.
      rewrite update_permute; auto.
Qed. (* /ADMITTED *)
(* /FOLD *)

(** [] *)

(* ###################################################################### *)
(** *** Preservation *)

(* EX3 (STLCExtended.preservation) *)
(** Complete the proof of [preservation]. *)

(* LATER: There's a better version of the informal proof in 2009's
   final exam at Penn. *)
Theorem preservation : forall t t' T,
     <{ empty |-- t \in T }> ->
     t --> t'  ->
     <{ empty |-- t' \in T }>.
(* FOLD *)
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  (* Proof: By induction on the given typing derivation.  Many
     cases are contradictory ([T_Var], [T_Abs]).  We show just
     the interesting ones. Again, we refer the reader to
     StlcProp.v for explanations. *)
  induction HT;
    intros t' HE; subst; inversion HE; subst...
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
  (* T_Case *)
  - (* ST_CaseInl *)
    inversion HT1; subst.
    eapply substitution_preserves_typing...
  - (* ST_CaseInr *)
    inversion HT1; subst.
    eapply substitution_preserves_typing...
  - (* T_Lcase *)
    + (* ST_LcaseCons *)
      inversion HT1; subst.
      apply substitution_preserves_typing with <{{List T1}}>...
      apply substitution_preserves_typing with T1...

  (* Complete the proof. *)

  (* fst and snd *)
  (* SOLUTION *)
  - (* T_Fst *)
    inversion HT...
  - (* T_Snd *)
    inversion HT...
  (* /SOLUTION *)
  (* let *)
  (* SOLUTION *)
  - (* T_Let *)
    apply substitution_preserves_typing with T1...
  (* /SOLUTION *)
  (* fix *)
  (* SOLUTION *)
  - (* T_Fix *)
    inversion HT; subst.
    apply substitution_preserves_typing with T1...
  (* /SOLUTION *)
(* ADMITTED *) Qed. (* /ADMITTED *)
(* /FOLD *)

(** [] *)

End STLCExtended.
(* /FULL *)
