(** * Stlc: The Simply Typed Lambda-Calculus *)

(* INSTRUCTORS: This chapter needs about one (80-minute) lecture.  It
   makes up maybe half of a good weekly homework assignment.
*)
(* SOONER: Beginning at the Typing chapter and continuing here, the
   text gets a bit sparse!

*)
(* SOONER: BCP 23: Notation stuff...
   - The <{{...}}> notation for types from MoreStlc should be
     transferred back to this file. BCP 21: Hmm -- I've forgotten what
     the advantage is of that notation (at least for this
     chapter)... is it just consistency with later material?  (BCP 23:
     Hopefully there will be a better way soon for all this!)
   - Important: the notation hack for associating variables with
     strings and then allowing strings to be used instead of (tm_var
     "x") is getting in the way later.  Would work MUCH better to
     eliminate this coercion and just define separate notations for
     all the variables we want to use to represent strings (i.e., make
     a separate production in the custom stlc grammar for x, y, a, b,
     etc.).  Similarly for numeric constants.  BCP 21: ... But will
     this actually work? If we define x as a keyword, can it also be
     used as a bound variable outside the custom grammar?
   - Sometimes \in typesets as a symbol, sometimes in tt. Can we fix
     that?  (Or, as proposed in Types.v, just turn it into [in] or
     [::] or [:].)

 *)
(* SOONER: SAZ 2024: I've done a full pass on notation, and it seems
   like an improvement over the past attempts.  The summary is:

   - STLC types [ty] are written in [<{{ Bool -> Bool }}>] brackets.

   - STLC terms [tm] are written in [<{ \x:Bool, x }>] brackets.

   - STLC typing judgments [has_type} are also written in [<{ .. }>]:
        [<{ Gamma |-- \x:Bool, x \in Bool -> Bool }>]

   - the notation [$(...)] is the "antiquote" escape-to-Rocq syntax.
 *)
(* LATER: consider a global rename of Gamma to C. (BCP 23: Too many
   other notation things in the air right now, but it still seems
   sensible to consider.) *)
(* LATER: (BCP) Anthony's comments later in the course:

        I had a few students want to discuss material from References;
        in particular the Objects section. The difficulty seemed to
        result from a few things coming together:

        - We don't talk about closures in the course...

        - ... because we said we'd work with closed terms in our own
        languages. This left some students unclear what an "open" term
        is.

        - We defined program identifiers at a global scope for
        convenience, so some students inferred that a lambda term with
        a free x is referring to some kind of global variable x. This
        confuses how local bindings introduced by let connect to the
        languages we've implemented.

        TA field report: the connection to OO classes made a lot of
        sense, but lexical scope took some work to get to and I don't
        know that it really clicked.

    So, it seems like we need to emphasize closures and lexical scope
    here!  Also, in the references chapter, we need to be more
    explicit about how the OO examples reduce.

    This might also be an argument for trying the coercion approach to
    variable names.
*)
(* LATER: We're inconsistent here (and probably in other files) about
  whether we hide things like [Hint Constructors] from the full HTML
   version.
*)
(* SOONER: There are some notational choices that need to be made
   consistently throughout the rest of the notes: naming of inference
   rules, naming of constructors, naming of syntactic categories,
   ...
*)
(* LATER: There are a bunch of slides from earlier offerings of
   CIS500 that might be useful additions to the TERSE notes.
     https://www.seas.upenn.edu/~cis500/cis500-f06/lectures/1002.pdf
     https://www.seas.upenn.edu/~cis500/cis500-f06/lectures/1004.pdf
*)

(** FULL: The simply typed lambda-calculus (STLC) is a tiny core
    calculus embodying the key concept of _functional abstraction_.
    This concept shows up in pretty much every real-world programming
    language in some form (functions, procedures, methods, etc.).

    We will follow exactly the same pattern as in the previous chapter
    when formalizing this calculus (syntax, small-step semantics,
    typing rules) and its main properties (progress and preservation).
    The new technical challenges arise from the mechanisms of
    _variable binding_ and _substitution_.  It will take some work to
    deal with these. *)
(* HIDE:
      We've already seen how to formalize a language with
      variables (Imp).  There, however, the variables were all global.
      In the STLC, we need to handle the variables that name the
      parameters to functions, and these are _bound_ variables.

      Moreover, instead of just looking up variables in a global store,
      we'll need to reduce function applications by substituting
      arguments for parameters in function bodies. *)
(** TERSE: Our job for this chapter: Formalize a small _functional_
    language and its type system.

    Language: The _simply typed lambda-calculus_ (STLC).
       - A small subset of Rocq's built-in functional language...
       - ...but we'll use different concrete syntax (to avoid
         confusion, and for consistency with standard treatments)

    Main new technical challenges:
      - variable binding
      - substitution *)
(** TERSE: *** *)

(** The STLC lives in the lower-left front corner of the famous
    _lambda cube_ (also called the _Barendregt Cube_), which
    visualizes three sets of features that can be added to its
    simple core:
[[
                               Calculus of Constructions
      type operators +--------+
                    /|       /|
                   / |      / |
     polymorphism +--------+  |
                  |  |     |  |
                  |  +-----|--+
                  | /      | /
                  |/       |/
                  +--------+ dependent types
                STLC
]]
    Moving from bottom to top in the cube corresponds to adding
    _polymorphic types_ like [forall X, X -> X].  Adding _just_
    polymorphism gives us the famous Girard-Reynolds calculus, System F.

    Moving from front to back corresponds to adding _type operators_
    like [list].

    Moving from left to right corresponds to adding _dependent types_
    like [forall n, array-of-size n].

    The top right corner on the back, which combines all three features,
    is called the _Calculus of Constructions_.  First studied by
    Coquand and Huet, it forms the foundation of Rocq's logic. *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** * Overview *)

(** FULL: The STLC is built on some collection of _base types_:
    booleans, numbers, strings, etc.  The exact choice of base types
    doesn't matter much -- the definition of the language as well as
    its theoretical properties work out the same no matter what we
    choose -- so for the sake of brevity let's take just [Bool] for
    the moment.  In the next chapter we'll see how to add more
    base types, and in later chapters we'll enrich the pure STLC with
    other useful constructs like pairs, records, subtyping, and
    mutable state.

    Starting from boolean constants and conditionals, we add three
    things:
        - variables
        - function abstractions
        - application

    This gives us the following collection of abstract syntax
    constructors (written out first in informal BNF notation -- we'll
    formalize it below).
[[
       t ::= x                         (variable)
           | \x:T,t                    (abstraction)
           | t1 t2                     (application)
           | true                      (constant true)
           | false                     (constant false)
           | if t1 then t2 else t3     (conditional)
]]
*)
(** TERSE: Begin with some set of _base types_ (here, just [Bool])

    Add: variables, function abstractions, and applications *)
(* TERSE *)

(* /TERSE *)
(** TERSE: Informal concrete syntax:
[[
       t ::= x                         (variable)
           | \x:T,t                    (abstraction)
           | t1 t2                     (application)
           | true                      (constant true)
           | false                     (constant false)
           | if t1 then t2 else t3     (conditional)
]]
*)
(** FULL: The [\] symbol in a function abstraction [\x:T,t] is usually
    written as a Greek letter "lambda" (hence the name of the
    calculus).  The variable [x] is called the _parameter_ to the
    function; the term [t] is its _body_.  The annotation [:T]
    specifies the type of arguments that the function can be applied
    to. *)

(** FULL: If you've seen lambda-calculus notation elsewhere, you might
    be wondering why abstraction is written here as [\x:T,t] instead
    of the usual "[\x:T.t]". The reason is that some user interfaces
    for interacting with Rocq use periods to separate a file into
    "sentences" to be passed separately to the Rocq top level. *)

(* LATER: Robert Rand: The examples below make good in-class quizzes *)

(** TERSE: *** *)
(** Some examples:

      - [\x:Bool, x]

        The identity function for booleans.

      - [(\x:Bool, x) true]

        The identity function for booleans, applied to the boolean [true].

      - [\x:Bool, if x then false else true]

        The boolean "not" function.

      - [\x:Bool, true]

        The constant function that takes every (boolean) argument to
        [true]. *)
(** TERSE: *** *)

(**
      - [\x:Bool, \y:Bool, x]

        A two-argument function that takes two booleans and returns
        the first one. *)

(** FULL: (As in Rocq, a two-argument function in the
    lambda-calculus is really a one-argument function whose body
    is also a one-argument function.) *)

(**   - [(\x:Bool, \y:Bool, x) false true]

        A two-argument function that takes two booleans and returns
        the first one, applied to the booleans [false] and [true]. *)

(** FULL: (As in Rocq, application associates to the left -- i.e., this
    expression is parsed as [((\x:Bool, \y:Bool, x) false) true].) *)

(**
      - [\f:Bool->Bool, f (f true)]

        A higher-order function that takes a _function_ [f] (from
        booleans to booleans) as an argument, applies [f] to [true],
        and applies [f] again to the result.

      - [(\f:Bool->Bool, f (f true)) (\x:Bool, false)]

        The same higher-order function, applied to the constantly
        [false] function. *)

(** TERSE: *** *)
(** TERSE: Note that _all_ functions are anonymous.

    We'll see how to add named function declarations as "syntactic
    sugar" in the \CHAP{MoreStlc} chapter.

*)
(** FULL: As the last several examples show, the STLC is a language of
    _higher-order_ functions: we can write down functions that take
    other functions as arguments and/or return other functions as
    results.

    The STLC doesn't provide any primitive syntax for defining _named_
    functions: i.e., all functions are "anonymous."  We'll see in chapter
    \CHAP{MoreStlc} that it is easy to add named functions -- indeed, the
    fundamental naming and binding mechanisms are exactly the same.

    The _types_ of the STLC include [Bool], which classifies the
    boolean constants [true] and [false] as well as more complex
    computations that yield booleans, plus _arrow types_ that classify
    functions.
[[
      T ::= Bool
          | T -> T
]]
*)
(** TERSE: *** *)
(** TERSE: The _types_ of the STLC include the base type [Bool] for
    boolean values and arrow types for functions.
[[
      T ::= Bool
          | T -> T
]]
*)
(**
    For example:

      - [\x:Bool, false] has type [Bool->Bool]

      - [\x:Bool, x] has type [Bool->Bool]

      - [(\x:Bool, x) true] has type [Bool]

      - [\x:Bool, \y:Bool, x] has type [Bool->Bool->Bool]
                              (i.e., [Bool -> (Bool->Bool)])

      - [(\x:Bool, \y:Bool, x) false] has type [Bool->Bool]

      - [(\x:Bool, \y:Bool, x) false true] has type [Bool] *)

(* QUIZ *)
(** What is the type of the following term?
[[
       \f:Bool->Bool, f (f true)
]]

    (A) [Bool -> (Bool -> Bool)]

    (B) [(Bool->Bool) -> Bool]

    (C) [Bool->Bool]

    (D) [Bool]

    (E) none of the above

*)
(* /QUIZ *)
(* QUIZ *)
(** How about the type of this one?
[[
         (\f:Bool->Bool, f (f true)) (\x:Bool, false)
]]

    (A) [Bool-> (Bool -> Bool)]

    (B) [(Bool->Bool) -> Bool]

    (C) [Bool->Bool]

    (D) [Bool]

    (E) none of the above

*)
(* /QUIZ *)

(* ###################################################################### *)
(** * Syntax *)

(** We next formalize the syntax of the STLC. *)

(* TERSE: HIDEFROMHTML *)
(* LATER: Do we need this?? LY: There are a couple of conflicts
   with SmallStep and Types (at least [tm], [step], and the notation
   [-->]), which might be resolved by being a bit more careful with
   namespacing. *)
Module STLC.
(* TERSE: /HIDEFROMHTML *)

(* ################################### *)
(** ** Types *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

(* ################################### *)
(** ** Terms *)

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

(** TERSE: *** *)
(** We need some notation magic to set up the concrete syntax, as
    we did in the [Imp] chapter... *)

(* TERSE: HIDEFROMHTML *)
(* INSTRUCTORS: If anything ever changes here, make sure to do the same
   adjustment in all the other grammars for Stlc-like languages... *)
(* INSTRUCTORS: Pro tip: You might be tempted to use . instead of , in
   the definition of lambda abstractions, to follow standard
   mathematical notation; indeed, this will work fine for Rocq itself,
   but it will confuse UIs (i.e. RocqIDE and Proof General), which use
   simple regexps to figure out where "sentences" end! *)

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

(* INSTRUCTORS: stlc_ty ----------------------------------------------------- *)
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

(* INSTRUCTORS: Begin Definition of template stlc_bool *)
Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0) : stlc_scope.
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc_tm at level 200,
                    x custom stlc_tm,
                    y custom stlc_tm,
                    z custom stlc_tm at level 200,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc_tm at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc_tm at level 0).
(* INSTRUCTORS: End Definition of template stlc_bool *)

(* TERSE: /HIDEFROMHTML *)
(** We'll write types inside of [<{{ ... }}>] brackets: *)

Check <{{ Bool }}>.
Check <{{ Bool -> Bool }}>.
Check <{{ (Bool -> Bool) -> Bool }}>.

(* HIDE *)
(* INSTRUCTORS: note that the [t] below parses as a "global" *)
Check forall (t:ty), <{{ t -> Bool }}> = <{{ Bool -> ((t -> t) -> t) }}>.

(* INSTRUCTORS: example of using the escape to Rocq *)
Definition foo (t:ty) := Ty_Arrow t t.
Check <{{ $(foo <{{ Bool }}>) -> Bool }}>.
Check <{{ $(foo Ty_Bool) -> $(foo Ty_Bool) }}>.
(* /HIDE *)


(* TERSE: HIDEFROMHTML *)
(* INSTRUCTORS: stcl_tm ----------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template stlc_tm *)
Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
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

(* HIDEFROMHTML *)
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
(* /HIDEFROMHTML *)

(* HIDE *)
Check <{ \ x : Bool, \ y : Bool, x }>.
Check <{ \ x : Bool, \ y : Bool, x }>.
Fail Check <{ \ w : Bool, \ y : Bool, x }>.
(* /HIDE *)

(* NOTATION: NOWISH: Explain it!!! (BCP) *)
(* NOTATION: LATER: These definitions are problematic: they cause
   confusion in later chapters (in particular, MoreStlc) because, if
   someone accidentally omits a quantifier for, say x, Rocq will find
   this x in the global environment (and with, fortuitiously, the
   right type)!  I wonder whether they could be replaced by notations
   in the stlc context only?

   Hugo: About having `Definition x : string := "x".' available only
   In the stlc.v context, I'm not fully sure about the question. In
   any case, you can certainly add a rule
      Notation "'x'" := "x" (in custom stlc at level 0).

Not quite working (Error: No interpretation for string "x".):
Notation "'x'" := "x" (in custom stlc at level 0).
Notation "'y'" := "y" (in custom stlc at level 0).
Notation "'z'" := "z" (in custom stlc at level 0).

But hugo says this is a bad idea anyway:

      You need to open the string scope. For instance, writing "x"%string works.

      The drawback of making "x" a token will be that you will not be able
      to use at all elsewhere, even in constr (there is only one phase of
      lexical analysis and no token local to a grammar :( ). So, if you want
      to use this approach, you should reserve letter less common than x, y,
      z.

      Also, with the « Notation "'x'" := "x"%string (in custom stlc at level 0). »
      approach, you'd need to change the "\" rule as follows:

       Notation "\ x : t , y" :=
         (tm_abs x t y)
         (in custom stlc at level 2, x at level 0, left associativity).
*)

(* HIDE *)
Check <{{Bool -> Bool}}>.
Check <{{Bool -> Bool -> Bool}}>.
Check <{x}>.
Check <{x y}>.
Check <{(x y) (x y)}>.
Check <{x (y x) y x y}>.
Check <{\x:Bool, x}>.
Check <{(\x:Bool, x) y}>.
Check <{ if x then x else x }>.
Check <{ if x y then x else x }>.
Check <{ if (x y) then x else x }>.
Check <{ if x then if x then y else x else y z }>.
Check <{ (if x then if x then y else x else y) z }>.
(* /HIDE *)

(** FULL: The upshot of these notation definitions is that we can
    write STLC terms in these brackets: [<{ .. }>] (similar to how we
    wrote Imp commands) and STLC types in these brackets: [<{{ .. }}>].

    As before, we can use [$(..)] to "escape" to arbitrary Rocq notation.
 *)

(** TERSE: *** *)
(** And terms inside of [<{ .. }>] brackets: *)

(** Examples... *)

(* LATER: Write some better / more interesting examples using
   conditionals.  (And then use them in various places later...) *)

Notation idB :=
  <{ \x:Bool, x }>.

Notation idBB :=
  <{ \x:Bool->Bool, x }>.

Notation idBBBB :=
  <{ \x: (Bool->Bool)->(Bool->Bool), x}>.

Notation k := <{ \x:Bool, \y:Bool, x }>.

(** TERSE: *** *)

Notation notB := <{ \x:Bool, if x then false else true }>.

(** Note that an abstraction [\x:T,t] (formally, [tm_abs x T t]) is
    always annotated with the type [T] of its parameter, in contrast
    to Rocq (and other functional languages like ML, Haskell, etc.),
    which use type inference to fill in missing annotations.  We're
    not considering type inference at all here. *)

(* LATER: Consider making these definitions too.  (But a preliminary
   experiment suggests that this may not be a good idea -- the
   [normalize] examples below then get stuck!) *)
(* LATER: CJC: If we DO want to introduce [Hint Resolve], proving a
   lemma (value id_A) here and adding it to the hints would be
   helpful (and with k).
   BCP 19: might be a good idea to try this again? *)
(** FULL: (We write these as [Notation]s rather than [Definition]s to make
    things easier for [auto].) *)

(* ###################################################################### *)
(** * Operational Semantics *)

(* HIDEFROMADVANCED *)
(** FULL: To define the small-step semantics of STLC terms, we begin,
    as always, by defining the set of values.  Next, we define the
    critical notions of _free variables_ and _substitution_, which are
    used in the reduction rule for application expressions.  And
    finally we give the small-step relation itself. *)
(** TERSE: To define the small-step semantics of STLC terms...

    - We begin by defining the set of values.

    - Next, we define _free variables_ and _substitution_.  These are
      used in the reduction rule for application expressions.

    - Finally, we give the small-step relation itself.
*)

(* /HIDEFROMADVANCED *)
(* ################################### *)
(** ** Values *)

(* HIDEFROMADVANCED *)
(** To define the values of the STLC, we have a few cases to consider.

    First, for the boolean part of the language, the situation is
    clear: [true] and [false] are the only values.  An [if] expression
    is never a value. *)

(** TERSE: *** *)
(** Second, an application is not a value: it represents a function
    being invoked on some argument, which clearly still has work left
    to do. *)

(** TERSE: *** *)
(* SOONER: There is going to be some work making the metavariable
   choices consistent in comments... *)
(** Third, for abstractions, we have a choice:

      - We can say that [\x:T, t] is a value only when [t] is a
        value -- i.e., only if the function's body has been
        reduced (as much as it can be without knowing what argument it
        is going to be applied to).

      - Or we can say that [\x:T, t] is always a value, no matter
        whether [t] is one or not -- in other words, we can say that
        reduction stops at abstractions.

    Our usual way of evaluating expressions in Gallina makes the first
    choice -- for example,
[[
         Compute (fun x:bool => 3 + 4)
]]
    yields:
[[
         fun x:bool => 7
]]
    But Gallina is rather unusual in this respect.  Most functional
    programming languages make the second choice -- reduction of a
    function's body only begins when the function is actually applied
    to an argument.

    We also make the second choice here. *)

(* /HIDEFROMADVANCED *)
(** TERSE: *** *)
Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.
(* TERSE: HIDEFROMHTML *)

Hint Constructors value : core.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: ** STLC Programs *)

(** Finally, we must consider what constitutes a _complete_ program.

    Intuitively, a "complete program" must not refer to any undefined
    variables.  We'll see shortly how to define the _free_ variables
    in a STLC term.  A complete program, then, is one that is
    _closed_ -- that is, that contains no free variables.

    (Conversely, a term that may contain free variables is often
    called an _open term_.) *)

(* SOONER: CH: Is the "shortly" above setting wrong expectations?
   Where exactly are we defining the free variables in a STLC term?
   BCP 25: Indeed, we need to define "free"! *)

(** TERSE: *** *)
(** Having made the choice not to reduce under abstractions, we don't
    need to worry about whether variables are values, since we'll
    always be reducing programs "from the outside in," and that means
    the [step] relation will always be working with closed terms. *)

(* ###################################################################### *)
(** ** Substitution *)

(* HIDEFROMADVANCED *)
(** Now we come to the heart of the STLC: the operation of
    substituting one term for a variable in another term.  This
    operation is used below to define the operational semantics of
    function application, where we will need to substitute the
    argument term for the function parameter in the function's body.
    For example, we reduce
[[
       (\x:Bool, if x then true else x) false
]]
    to
[[
       if false then true else false
]]
    by substituting [false] for the parameter [x] in the body of the
    function.

    In general, we need to be able to substitute some given term [s]
    for occurrences of some variable [x] in another term [t].
    Informally, this is written [ [x:=s]t ] and pronounced "substitute
    [s] for [x] in [t]." *)

(** TERSE: *** *)
(** Here are some examples:

      - [[x:=true] (if x then true else false)]
           yields [if true then true else false]

      - [[x:=true] x] yields [true]

      - [[x:=true] (if x then x else y)] yields [if true then true else y]

      - [[x:=true] y] yields [y]

      - [[x:=true] false] yields [false] (vacuous substitution)

      - [[x:=true] (\y:Bool, if y then x else false)]
           yields [\y:Bool, if y then true else false]

      - [[x:=true] (\y:Bool, x)] yields [\y:Bool, true]

      - [[x:=true] (\y:Bool, y)] yields [\y:Bool, y]

      - [[x:=true] (\x:Bool, x)] yields [\x:Bool, x]

    The last example is key: substituting [x] with [true] in
    [\x:Bool, x] does _not_ yield [\x:Bool, true]!  The reason for
    this is that the [x] in the body of [\x:Bool, x] is _bound_ by the
    abstraction: it is a new, local name that just happens to be
    spelled the same as some global name [x]. *)

(* /HIDEFROMADVANCED *)
(** TERSE: *** *)
(** Here is the definition, informally...
[[
       [x:=s]x               = s
       [x:=s]y               = y                     if x <> y
       [x:=s](\x:T, t)       = \x:T, t
       [x:=s](\y:T, t)       = \y:T, [x:=s]t         if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)
       [x:=s]true            = true
       [x:=s]false           = false
       [x:=s](if t1 then t2 else t3) =
                       if [x:=s]t1 then [x:=s]t2 else [x:=s]t3
]]
*)

(** TERSE: *** *)
(** ... and formally: *)

(* LATER: explain better about alpha-conversion. *)

(* TERSE: HIDEFROMHTML *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of templat subst *)
(* NOTATION: SAZ 2024 - I think this notation should bind tigher than
application, which is a good reason to put application higher than
level 1 in the base stlc_tm grammar. *)
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).
(* INSTRUCTORS: End Definition of subst subst *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* TERSE: /HIDEFROMHTML *)

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 [x:=s] t2}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if [x:=s] t1 then [x:=s] t2 else [x:=s] t3}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).

(* HIDE *)
(* NOTATION: these are useful checks *)
Check <{ [x := x]x }>.
Check <{ [x := x][x := y]z }>.
Check <{ [x := x] \y:Bool, x }>.
Check <{ [x := x] \y:Bool, x y }>.
Check <{ [x := x] (\y:Bool, [x:=x]x y)}>.
Check <{ ([x := z]y) ([x := z]x) }>.
Check <{ [x := \y:Bool, y](x z) }>.
(* /HIDE *)

(* QUIZ *)
(** What is the result of the following substitution?
[[
       [x:=s](\y:T1, x (\x:T2, x))
]]

    (1) [(\y:T1, x (\x:T2, x))]

    (2) [(\y:T1, s (\x:T2, s))]

    (3) [(\y:T1, s (\x:T2, x))]

    (4) none of the above

*)
(* /QUIZ *)

(** _Technical note_: Substitution also becomes trickier to define if
    we consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables. *)

(** TERSE: *** *)
(* LATER: This bit might need more tersification *)

(** Here is an example of how things would become trickier if one were
    to substitute _open_ terms. Using the simple definition of
    substitution above to substitute the open term
[[
      s = \x:Bool, r
]]
    (where [r] is a _free_ reference to some global resource) for
    the free variable [z] in the term
[[
      t = \r:Bool, z
]]
    where [r] is a bound variable, we would get
[[
      \r:Bool, \x:Bool, r
]]
    where the free reference to [r] in [s] has been "captured" by
    the binder at the beginning of [t]. *)

(** TERSE: *** *)

(** Why would this be bad?  Because it violates the principle that the
    names of bound variables do not matter.  For example, if we rename
    the bound variable in [t], e.g., let
[[
      t' = \w:Bool, z
]]
    then [[z:=s]t'] is
[[
      \w:Bool, \x:Bool, r
]]
    which does not behave the same as the substituting in the original t:
[[
      [z:=s]t = \r:Bool, \x:Bool, r
]]
    That is, renaming a bound variable in [t] would change how [t]
    behaves under our simple substitution. So substitution gets more
    complicated in that setting, but fortunately we don't have that
    problem in our STLC variant. *)

(** FULL: See, for example, \CITE{Aydemir 2008} for further discussion
    of this issue. *)

(** TERSE: *** *)

(** Fortunately, since we are only interested here in defining the
    [step] relation on _closed_ terms (i.e., terms like [\x:Bool, x]
    that include binders for all of the variables they mention), we
    can sidestep this extra complexity, but it must be dealt with when
    formalizing richer languages. *)
(* FULL *)
(** TERSE: *** *)
(* EX3 (substi_correct) *)
(** The definition that we gave above uses Rocq's [Fixpoint] facility
    to define substitution as a _function_.  Suppose, instead, we
    wanted to define substitution as an inductive _relation_ [substi].
    We've begun the definition by providing the [Inductive] header and
    one of the constructors; your job is to fill in the rest of the
    constructors and prove that the relation you've defined coincides
    with the function given above. *)

Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (tm_var x) s
  (* SOLUTION *)
  | s_var2 : forall x',
      x <> x' ->
      substi s x (tm_var x') (tm_var x')
  | s_abs1 : forall T2 t1,
      substi s x <{\x:T2, t1}> <{\x:T2, t1}>
  | s_abs2 : forall x' T1 t1 t1',
      x <> x' ->
      substi s x t1 t1' ->
      substi s x <{\x':T1, t1}> <{\x':T1, t1'}>
  | s_app : forall t1 t2 t1' t2',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x <{t1 t2}> <{t1' t2'}>
  | s_true :
      substi s x <{true}> <{true}>
  | s_false :
      substi s x <{false}> <{false}>
  | s_if : forall t1 t2 t3 t1' t2' t3',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x t3 t3' ->
      substi s x <{if t1 then t2 else t3}> <{if t1' then t2' else t3'}>
(* /SOLUTION *)
.
(* TERSE: HIDEFROMHTML *)

Hint Constructors substi : core.
(* TERSE: /HIDEFROMHTML *)

Theorem substi_correct : forall s x t t',
  <{ [x:=s]t }> = t' <-> substi s x t t'.
Proof.
  (* ADMITTED *)
  intros s x t t'.
  split.
  - (* -> *)
    generalize dependent t'.
    (induction t); intros; unfold subst in H; subst; fold subst in *; auto.
    + (* var *)
      destruct (String.eqb_spec x s0) as [H | H]; subst; auto.
    + (* abs *)
      destruct (String.eqb_spec x s0) as [H | H]; subst; auto.
  - (* <- *)
    generalize dependent t'.
    induction t;
       intros; unfold subst; subst; fold subst in *; auto;
       try solve [inversion H; auto].
    + (* var *)
      inversion H; subst.
      * rewrite String.eqb_refl; auto.
      * rewrite <- String.eqb_neq in H1. rewrite H1. auto.
    + (* app *)
      inversion H; subst.
      rewrite -> (IHt1 t1'); auto. rewrite -> (IHt2 t2'); auto.
    + (* abs *)
      inversion H; subst.
      * rewrite String.eqb_refl; auto.
      * rewrite <- String.eqb_neq in H4. rewrite H4. auto.
        rewrite (IHt t1'); auto.
    + (* if *)
      inversion H; subst.
      rewrite (IHt1 t1'); auto. rewrite (IHt2 t2'); auto.
      rewrite (IHt3 t3'); auto. Qed.
  (* /ADMITTED *)
(** [] *)
(* /FULL *)

(* ################################### *)
(** ** Reduction *)

(** FULL: The small-step reduction relation for STLC now follows the
    same pattern as the ones we have seen before.  Intuitively, to
    reduce a function application, we first reduce its left-hand
    side (the function) until it becomes an abstraction; then we
    reduce its right-hand side (the argument) until it is also a
    value; and finally we substitute the argument for the bound
    variable in the body of the abstraction.  This last rule, written
    informally as
[[
      (\x:T,t12) v2 --> [x:=v2] t12
]]
    is traditionally called _beta-reduction_. *)

(** [[[
                              value v
                       -----------------------                      (ST_AppAbs)
                       (\x:T,t) v --> [x:=v]t

                              t1 --> t1'
                           ----------------                           (ST_App1)
                           t1 t2 --> t1' t2

                              value v1
                              t2 --> t2'
                           ----------------                           (ST_App2)
                           v1 t2 --> v1 t2'
]]]
*)
(** TERSE: (plus the usual rules for conditionals). *)
(** FULL: ... plus the usual rules for conditionals:
[[[
                    --------------------------------               (ST_IfTrue)
                    (if true then t1 else t2) --> t1

                    ---------------------------------              (ST_IfFalse)
                    (if false then t1 else t2) --> t2

                             t1 --> t1'
      --------------------------------------------------------     (ST_If)
      (if t1 then t2 else t3) --> (if t1' then t2 else t3)
]]]
*)

(* HIDEFROMADVANCED *)
(** TERSE: The [ST_AppAbs] rule is often called _beta-reduction_. *)

(** This is _call by value_ reduction: to reduce an
    application [(t1 t2)], we
      - first reduce [t1] to a value: a function [\x:T,t]
      - then reduce the argument [t2] to a value [v]
      - then reduce the application itself by substituting [v] for
        the bound variable [x] in the body [t]. *)

(* /HIDEFROMADVANCED *)
(* FULL *)
(** Formally: *)

(* /FULL *)
(* TERSE: HIDEFROMHTML *)
Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t v,
         value v ->
         <{(\x:T, t) v}> --> <{ [x:=v]t }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
(* TERSE: /HIDEFROMHTML *)
(* QUIZ *)
(** What does the following term step to?
[[
    (\x:Bool->Bool, x) (\x:Bool, x) --> ???
]]

(A) [ \x:Bool, x ]

(B) [ \x:Bool->Bool, x ]

(C) [ (\x:Bool->Bool, x) (\x:Bool, x) ]

(D) none of the above

*)
(* /QUIZ *)
(* QUIZ *)
(** What does the following term step to?
[[
   (\x:Bool->Bool, x)
       ((\x:Bool->Bool, x) (\x:Bool, x))
   --> ???
]]

(A) [ \x:Bool, x ]

(B) [ \x:Bool->Bool, x ]

(C) [ (\x:Bool->Bool, x) (\x:Bool, x) ]

(D) [ (\x:Bool->Bool, x) ((\x:Bool->Bool, x) (\x:Bool, x)) ]

(E) none of the above

*)
(* /QUIZ *)
(* QUIZ *)
(** What does the following term _normalize_ to?
[[
   (\x:Bool->Bool, x) notB true  -->* ???
]]
where [notB] abbreviates [\x:Bool, if x then false else true]


(A) [ \x:Bool, x ]

(B) [ true ]

(C) [ false ]

(D) [ notB ]

(E) none of the above

*)
(* /QUIZ *)
(* QUIZ *)
(** What does the following term normalize to?
[[
  (\x:Bool, x) (notB true) -->* ???
]]

(A) [ \x:Bool, x ]

(B) [ true ]

(C) [ false ]

(D) [ notB true ]

(E) none of the above

*)
(* /QUIZ *)

(* HIDEFROMADVANCED *)
(* ##################################### *)
(** ** Examples *)

(** Example:
[[
      (\x:Bool->Bool, x) (\x:Bool, x) -->* \x:Bool, x
]]
    i.e.,
[[
      idBB idB -->* idB
]]
*)

(* TERSE: HIDEFROMHTML *)
Lemma step_example1 :
  <{idBB idB}> -->* idB.
Proof.
  eapply multi_step.
  - apply ST_AppAbs.
    apply v_abs.
  - simpl.
    apply multi_refl.  Qed.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** Example:
[[
      (\x:Bool->Bool, x) ((\x:Bool->Bool, x) (\x:Bool, x))
            -->* \x:Bool, x
]]
    i.e.,
[[
      (idBB (idBB idB)) -->* idB.
]]
*)

(* TERSE: HIDEFROMHTML *)
Lemma step_example2 :
  <{idBB (idBB idB)}> -->* idB.
Proof.
  eapply multi_step.
  - apply ST_App2.
    + auto.
    + apply ST_AppAbs. auto.
  - eapply multi_step.
    + apply ST_AppAbs. simpl. auto.
    + simpl. apply multi_refl.  Qed.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** Example:
[[
      (\x:Bool->Bool, x)
         (\x:Bool, if x then false else true)
         true
            -->* false
]]
    i.e.,
[[
       (idBB notB) true -->* false.
]]
*)

(* TERSE: HIDEFROMHTML *)
Lemma step_example3 :
  <{idBB notB true}> -->* <{false}>.
Proof.
  eapply multi_step.
  - apply ST_App1. apply ST_AppAbs. auto.
  - simpl. eapply multi_step.
    + apply ST_AppAbs. auto.
    + simpl. eapply multi_step.
      * apply ST_IfTrue.
      * apply multi_refl.  Qed.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** Example:
[[
      (\x:Bool -> Bool, x)
         ((\x:Bool, if x then false else true) true)
            -->* false
]]
    i.e.,
[[
      idBB (notB true) -->* false.
]]
    (Note that this term doesn't actually typecheck; even so, we can
    ask how it reduces.)
*)

(* TERSE: HIDEFROMHTML *)
Lemma step_example4 :
  <{idBB (notB true)}> -->* <{false}>.
Proof.
  eapply multi_step.
  - apply ST_App2; auto.
  - eapply multi_step.
    + apply ST_App2; auto.
      apply ST_IfTrue.
    + eapply multi_step.
      * apply ST_AppAbs. auto.
      * simpl. apply multi_refl.  Qed.
(* TERSE: /HIDEFROMHTML *)


(* QUIZ *)
(** Do values and normal forms coincide in the language presented so far?

    (A) yes

    (B) no

*)
(* /QUIZ *)
(* INSTRUCTORS: No, because we haven't come to the type system yet.
   E.g., [true true] is a normal form but not a value. *)

(* FULL *)
(** We can use the [normalize] tactic defined in the \CHAP{Smallstep} chapter
    to simplify these proofs. *)

Lemma step_example1' :
  <{idBB idB}> -->* idB.
Proof. normalize.  Qed.

Lemma step_example2' :
  <{idBB (idBB idB)}> -->* idB.
Proof. normalize. Qed.

Lemma step_example3' :
  <{idBB notB true}> -->* <{false}>.
Proof. normalize.  Qed.

Lemma step_example4' :
  <{idBB (notB true)}> -->* <{false}>.
Proof. normalize.  Qed.

(* EX2 (step_example5) *)
(** Try to do this one both with and without [normalize]. *)

Lemma step_example5 :
       <{idBBBB idBB idB}>
  -->* idB.
Proof.
  (* ADMITTED *)
  eapply multi_step.
  - apply ST_App1.
    apply ST_AppAbs;
    auto.
  - eapply multi_step.
    + simpl. apply ST_AppAbs; auto.
    + simpl. apply multi_refl.  Qed.
(* /ADMITTED *)

Lemma step_example5_with_normalize :
       <{idBBBB idBB idB}>
  -->* idB.
Proof.
  (* ADMITTED *)
  normalize. Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* /HIDEFROMADVANCED *)
(* ###################################################################### *)
(** * Typing *)

(** Next we consider the typing relation of the STLC, which is
    meant to prevent reduction from getting stuck. *)

(** FULL: For instance, the following two STLC terms are both stuck
    [if \x:Bool,x then true else false] (where we branch on a function
    as a boolean) and [true false] (where we apply a boolean as a
    function). *)

(* ################################### *)
(** ** Contexts *)

(* HIDEFROMADVANCED *)
(** FULL: Although we are primarily interested in the binary relation
    [|-- t \in T], relating a closed term [t] to its type [T], we need
    to generalize a bit to make the definitions work.

    Consider checking that [\x:T11,t12] has type
    [T11->T12]. Intuitively, we need to check that [t12] has type
    [T12]. However, we have removed the binder [\x], so [x] may occur
    free in [t12] (that is, [t12] may be _open_).  While checking that
    [t12] has type [T12], we must remember that [x] has type [T11], in
    order to deal with these free occurrences of [x]. Similarly, [t12]
    itself could contain abstractions, and typechecking their bodies
    could require looking up the declared types of yet more free
    variables.

    To keep track of all this, we add a third element to the relation,
    a _typing context_ [Gamma], which records the types of the
    variables that may occur free in a term -- that is, Gamma is a
    partial map from variables to types.

    The new _typing judgment_ is written [Gamma |-- t \in T] and
    informally read as "term [t] has type [T], given the types of free
    variables in [t] as specified by [Gamma]".

    We'll also write [x |-> T ; Gamma] for "update the partial map
    [Gamma] so that it maps [x] to [T]," following the notation from
    the \CHAP{Maps} chapter.

    With these refinements, we are ready to give informal and formal
    specifications of the typing relation.
*)

(* SOONER: CH: I find the FULL explanation above much better than the
   TERSE one below, since the question below seems ill-posed without
   extra context. Why would one want to type a term [x y] if we've
   just said that we will just look at closed terms as our programs? *)

(** TERSE: _Question_: What is the type of the term "[x y]"?

    _Answer_: It depends on the types of [x] and [y]!

    I.e., in order to assign a type to a term, we need to know
    what assumptions we should make about the types of its free
    variables.

    This leads us to a three-place _typing judgment_, informally
    written [Gamma |-- t \in T], where [Gamma] is a
    "typing context" -- a mapping from variables to their types. *)

Definition context := partial_map ty.

(** TERSE: Following the usual notation for partial maps, we write
    [(x |-> T, Gamma)] for "update the partial function [Gamma] so
    that it maps [x] to [T]." *)
(* /HIDEFROMADVANCED *)

(* SOONER: CH: [Gamma] is a mouthful. What's wrong with [G]?  BCP 25:
   Indeed.  I'd be happy to see it changed. *)

(* ################################### *)
(** ** Typing Relation *)

(* SOONER: BCP 25: Catalin made lots of changes to metavariable names
   in this file. They ought to be reflected in all the other files
   that depend on this one! *)
(* SOONER: More text needed? (YES!) *)

(** [[[
                            Gamma x = T1
                          ------------------                             (T_Var)
                          Gamma |-- x \in T1

                      x |-> T2 ; Gamma |-- t1 \in T1
                      ------------------------------                     (T_Abs)
                       Gamma |-- \x:T2,t1 \in T2->T1

                        Gamma |-- t1 \in T2->T1
                          Gamma |-- t2 \in T2
                         ----------------------                          (T_App)
                         Gamma |-- t1 t2 \in T1

                         -----------------------                         (T_True)
                         Gamma |-- true \in Bool

                         ------------------------                       (T_False)
                         Gamma |-- false \in Bool

    Gamma |-- t1 \in Bool    Gamma |-- t2 \in T    Gamma |-- t3 \in T
    -----------------------------------------------------------------    (T_If)
                  Gamma |-- if t1 then t2 else t3 \in T
]]]

    We can read the three-place relation [Gamma |-- t \in T] as:
    "under the assumptions in Gamma, the term [t] has the type [T]." *)

(** FULL: In the formal development, we write this judgment in
    [<{ .. }>] brackets, as introduced by the following notational
    conventions. *)

(** TERSE: In the formal development, we write this judgment in
    [<{ .. }>] brackets. *)

(* NOTATION: NOWISH: The HTML typesetting of the final turnstile is ugly!
   And there are a bunch of similar ones below.  Seems like the
   spacing inside square brackets is different from inside triple
   brackets. :-( (BCP) *)
(* NOTATION: NOWISH: BCP 20: I'm wondering whether we could / should
   allow whole typing jusgements inside <{...}> brackets.  Having
   gotten used to seeing the brackets around object-language stuff, I
   actually find it confusing NOT to see it here.  Another alternative
   would be to put the brackets just after |-- and before \in. *)

(* NOTATION: SAZ 2024: I have implemnted the suggestion above about
   putting the whole judgment inside [ <{ }> ] brackets.

   I changed the context portion of the judgment syntax to be parsed
   as a stlc_tm.  That means that we have to add the "map update"
   syntax from Maps.v to the stlc_tm grammar, but that doesn't seem
   like too big of a problem.  One advantage is that we can use the
   same [ <{ ... }> ] brackets to quote both typing judgments *and*
   stlc terms, since they both start with the same prefix that can be
   disambiguated by the LL parser.

   Another advantage is that we don't have to parenthesize the types
   that appear after ther [\in] in the judgment. *)

(* NOTATION: SAZ 2024 - Per the comments above, this includes the
   map update notation into the stlc_tm grammar.  However, I also
   specialized it so that [x] is a (global) identifier and [v]
   must be a type. *)

(* TERSE: HIDEFROMHTML *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template STCL has_type notation *)
Notation "x '|->' v ';' m " := (update m x v)
  (in custom stlc_tm at level 0, x constr at level 0, v  custom stlc_ty, right associativity) : stlc_scope.

Notation "x '|->' v " := (update empty x v)
  (in custom stlc_tm at level 0, x constr at level 0, v custom stlc_ty) : stlc_scope.

(* NOTATION: If we don't include the following, then <{ empty |-- t : T }>
   will print as <{ $(empty) |-- t : T }>
 *)
Notation "'empty'" := empty (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
            (at level 0, Gamma custom stlc_tm at level 200, t custom stlc_tm, T custom stlc_ty).
(* INSTRUCTORS: End STCL has_type notation *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* TERSE: /HIDEFROMHTML *)

(* TERSE: HIDEFROMHTML *)
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      <{ Gamma |-- x \in T1 }>
  | T_Abs : forall Gamma x T1 T2 t1,
      <{ x |-> T2 ; Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- \x:T2, t1 \in T2 -> T1 }>
  | T_App : forall T1 T2 Gamma t1 t2,
      <{ Gamma |-- t1 \in T2 -> T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- t1 t2 \in T1 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall t1 t2 t3 T1 Gamma,
       <{ Gamma |-- t1 \in Bool }> ->
       <{ Gamma |-- t2 \in T1 }> ->
       <{ Gamma |-- t3 \in T1 }> ->
       <{ Gamma |-- if t1 then t2 else t3 \in T1 }>

where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T) : stlc_scope.

(* HIDE *)
Check <{ true }>.
Check <{ empty |-- true \in Bool }>.
(* /HIDE *)

(* NOWISH: Ori: In Records.v, the context is a parameter,
   like in the next defintion. Which one is better? why?
   anyway, we better be consistent.
Reserved Notation "Gamma '|-a' t '\in' T"
                  (at level 101,
                   t custom stlc, T custom stlc at level 0).

Inductive has_type_a (Gamma : context) : tm -> ty -> Prop :=
  | T_Vara : forall x T1,
      Gamma x = Some T1 ->
      Gamma |-a x \in T1
  | T_Absa : forall x T1 T2 t1,
      x |-> T2 ; Gamma |-a t1 \in T1 ->
      Gamma |-a \x:T2, t1 \in (T2 -> T1)
  | T_Appa : forall T1 T2 t1 t2,
      Gamma |-a t1 \in (T2 -> T1) ->
      Gamma |-a t2 \in T2 ->
      Gamma |-a t1 t2 \in T1
  | T_Truea : Gamma |-a true \in Bool
  | T_Falsea : Gamma |-a false \in Bool
  | T_Ifa : forall t1 t2 t3 T1,
       Gamma |-a t1 \in Bool ->
       Gamma |-a t2 \in T1 ->
       Gamma |-a t3 \in T1 ->
       Gamma |-a if t1 then t2 else t3 \in T1

where "Gamma '|-a' t '\in' T" := (has_type_a Gamma t T). *)

Hint Constructors has_type : core.
(* TERSE: /HIDEFROMHTML *)

(* HIDEFROMADVANCED *)
(* ################################### *)
(** ** Examples *)

Example typing_example_1 :
  <{ empty |-- \x:Bool, x \in Bool -> Bool }>.
Proof. eauto. Qed.

(** Note that, since we added the [has_type] constructors to the hints
    database, [eauto] can solve this one immediately. *)

(* FULL *)
(** For what it's worth, in this case [auto] works too, since our term
    contains no application nodes: *)
Example typing_example_1' :
  <{ empty |-- \x:Bool, x \in Bool -> Bool }>.
Proof. auto.  Qed.
(* /FULL *)

(** TERSE: *** *)
(** More examples:
[[
       empty |-- \x:Bool, \y:Bool->Bool, y (y x)
             \in Bool -> (Bool->Bool) -> Bool.
]]
*)
(* FOLD *)

Example typing_example_2 :
  <{ empty |--
    \x:Bool,
       \y:Bool->Bool,
          (y (y x)) \in
    Bool -> (Bool -> Bool) -> Bool }>.
Proof. eauto 20. Qed.
(* /FOLD *)

(* FULL *)
(* EX2? (typing_example_2_full) *)
(** Prove the same result without using [auto], [eauto], or
    [eapply] (or [...]). *)

Example typing_example_2_full :
 <{ empty |--
    \x:Bool,
       \y:Bool->Bool,
          (y (y x)) \in
    Bool -> (Bool -> Bool) -> Bool }>.
Proof.
  (* ADMITTED *)
  apply T_Abs.
  apply T_Abs.
  apply T_App with (T2 := <{{ Bool }}>).
  - apply T_Var. reflexivity.
  - apply T_App with (T2 := <{{ Bool }}> ).
    + apply T_Var. reflexivity.
    + apply T_Var. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* FULL *)
(* EX2 (typing_example_3) *)
(** Formally prove the following typing derivation holds: *)
(* /FULL *)
(** [[
    exists T,
       empty |-- \x:Bool->Bool, \y:Bool->Bool, \z:Bool,
                   y (x z)
             \in T.
]]
*)

(* FULL *)
Example typing_example_3 :
  exists T,
   <{ empty |--
      \x:Bool->Bool,
         \y:Bool->Bool,
            \z:Bool,
               (y (x z)) \in
      T }>.
Proof.
  (* ADMITTED *)
  exists <{{ (Bool -> Bool) ->
            (Bool -> Bool) ->
            (Bool -> Bool) }}>.
  (* LATER : Why doesn't [eauto 30] do anything??? *)
  apply T_Abs.
  apply T_Abs.
  apply T_Abs.
  apply T_App with (T2 := <{{ Bool }}> ); auto.
  apply T_App with (T2 := <{{ Bool }}> ); auto.  Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)
(** We can also show that some terms are _not_ typable.  For example,
    we can check that there is no typing derivation assigning a type
    to the term [\x:Bool, \y:Bool, x y] -- i.e.,
[[
    ~ exists T,
        empty |-- \x:Bool, \y:Bool, x y \in T.
]]
*)
(* FOLD *)

Example typing_nonexample_1 :
  ~ exists T,
    <{  empty |--
        \x:Bool,
            \y:Bool,
               (x y) \in
        T }>.
Proof.
  intros Hc. destruct Hc as [T Hc].
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion Hc; subst; clear Hc.
  inversion H4; subst; clear H4.
  inversion H5; subst; clear H5 H4.
  inversion H2; subst; clear H2.
  discriminate H1.
Qed.
(* /FOLD *)

(* FULL *)
(* EX3? (typing_nonexample_3) *)
(* /FULL *)
(** Another nonexample:
[[
    ~ (exists S T,
          empty |-- \x:S, x x \in T).
]]
*)

(* FULL *)
Example typing_nonexample_3 :
  ~ (exists S T,
      <{ empty |--
          \x:S, x x \in T }>).
Proof.
  (* ADMITTED *)
  intros Hc. destruct Hc as [S [T Hc]].
  inversion Hc; subst; clear Hc.
  inversion H4; subst; clear H4.
  inversion H2; subst; clear H2.
  inversion H5; subst; clear H5.
  rewrite H1 in H2. clear H1.
  injection H2 as H2.
  (* At this point, we have an assumption that [T2] is equal
     to [T2->T1].  But there can't be any such (finite) [T2]. *)
  induction T2.
    - (* Bool *) discriminate.
    - (* Arrow *)
      (* NOTATION: NOWISH: Ori: error with associativity of arrow in H2?! *)
      injection H2 as H2. apply IHT2_1. rewrite H. assumption.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* QUIZ *)
(** Which of the following propositions is _not_ provable?

    (A) [y:Bool |-- \x:Bool, x \in Bool->Bool]

    (B) [exists T,  empty |-- \y:Bool->Bool, \x:Bool, y x \in T]

    (C) [exists T,  empty |-- \y:Bool->Bool, \x:Bool, x y \in T]

    (D) [exists S, x:S |-- \y:Bool->Bool, y x \in (Bool->Bool)->S]

*)
(* /QUIZ *)
(* QUIZ *)
(** Which of these is not provable?

    (A) [exists T,  empty |-- \y:Bool->Bool->Bool, \x:Bool, y x \in T]

    (B) [exists S T,  x:S |-- x x x \in T]

    (C) [exists S U T,  x:S, y:U |-- \z:Bool, x (y z) \in T]

    (D) [exists S T,  x:S |-- \y:Bool, x (x y) \in T]

*)
(* /QUIZ *)
(* HIDE *)
(* LATER: Turn this into a quiz!  Maybe the next one too. *)

(* EX1? (typing_statements) *)

(** Which of the following propositions are provable?
       - [y:Bool |-- \x:Bool,x \in Bool->Bool]
(* QUIETSOLUTION *)
            - Yes
(* /QUIETSOLUTION *)
       - [exists T,  empty |-- \y:Bool->Bool, \x:Bool, y x \in T]
(* QUIETSOLUTION *)
            - Yes
(* /QUIETSOLUTION *)
       - [exists T,  empty |-- \y:Bool->Bool, \x:Bool, x y \in T]
(* QUIETSOLUTION *)
            - No
(* /QUIETSOLUTION *)
       - [exists S, x:S |-- \y:Bool->Bool, y x \in (Bool->Bool)->S]
(* QUIETSOLUTION *)
            - Yes
(* /QUIETSOLUTION *)
       - [exists S T,  x:S |-- x x x \in T]
(* QUIETSOLUTION *)
            - No
(* /QUIETSOLUTION *)
*)
(** [] *)

(* EX1M (more_typing_statements) *)
(* HIDE: Should we change A/B/C to Bool?  BAY: No, these get much less
   interesting if A/B/C are all changed to Bool. *)
(** Which of the following propositions are provable (where [A], [B],
    and [C] stand for arbitrary types)?  For the ones that are, give
    witnesses for the existentially bound variables.
       - [exists T,  empty |-- \y:B->B->B, \x:B, y x \in T]
(* QUIETSOLUTION *)
         - Answer: Yes
[[
           T = (B->B->B)->B->(B->B)
]]
(* /QUIETSOLUTION *)
       - [exists T,  empty |-- \x:A->B, \y:B->C, \z:A, y (x z) \in T]
(* QUIETSOLUTION *)
         - Answer: Yes
[[
           T = (A->B)->(B->C)->A->C
]]
(* /QUIETSOLUTION *)
       - [exists S U T,  x:S, y:U |-- \z:A, x (y z) \in T]
(* QUIETSOLUTION *)
         - Answer: Yes
[[
           S == B->C
           U == A->B
           T == A->C
]]
or
[[
           S = A -> A
           U = A -> A
           T = A -> A
]]
(* /QUIETSOLUTION *)
       - [exists S T,  x:S |-- \y:A, x (x y) \in T]
(* QUIETSOLUTION *)
         - Answer: Yes
[[
           S == A->A
           T == A->A
]]
(* /QUIETSOLUTION *)
       - [exists S U T,  x:S |-- x (\z:U, z x) \in T]
(* QUIETSOLUTION *)
         - Answer: No
(* /QUIETSOLUTION *)
*)

(* GRADE_MANUAL 1: more_typing_statements *)
(** [] *)

(* /HIDE *)
(* /HIDEFROMADVANCED *)
(* TERSE: HIDEFROMHTML *)
End STLC.
(* TERSE: /HIDEFROMHTML *)

(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(\\*\\* \\*+\\|(\\* EX[1-5]..." *)
(* End: *)
(* mode: outline-minor *)
(* outline-heading-end-regexp: "\n" *)
(* /HIDE *)
