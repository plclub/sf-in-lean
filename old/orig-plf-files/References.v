(** * References: Typing Mutable References *)

(* INSTRUCTORS: The proof of preservation for this system is actually
   very interesting.  It is given as an exercise, but if there's
   enough class time it would be well worth devoting a lecture to
   it! *)
(* SOONER: The text in this chapter -- especially the terse version --
   does not do a great job, early on, of connecting the concepts to
   things that students will already know about. This makes the later
   parts unnecessarily puzzling.  (Also, the terse slides have way too
   much text and not NEARLY enough examples, quizzes, etc.) *)
(* SOONER: Sampsa:
    The exercise `factorial_ref` is tricky,
    because the definition of `tseq` is unhygienic
    with respect to the variable `x`.
    Thus, the following does not work unless the variable `x` is renamed.

    ```
    fact = \ x : Nat , (\ r : Ref (Nat -> Nat) ,
     r := \ x : Nat , if x == 0 then 1 else x * !r (pred x);
     !r x) (ref (\ x : Nat , 0))
    ```
*)
(* LATER: For the TERSE version, there are a bunch of slides in the
   two 2006 Chapter 13 lectures that would be great to include
   here. *)
(* LATER: The UPenn 2011 final exam has some good simple questions that
   should be repeated here (question 5). *)
(* SOONER: More of the exercises should be marked recommended. *)

(** FULL: Up to this point, we have considered a variety of _pure_
    language features, including functional abstraction, basic types
    such as numbers and booleans, and structured types such as records
    and variants.  These features form the backbone of most
    programming languages -- including purely functional languages
    such as Haskell and "mostly functional" languages such as ML, as
    well as imperative languages such as C and object-oriented
    languages such as Java, C[#], and Scala.

    Most practical languages also include various _impure_
    features that cannot be described in the simple semantic framework
    we have used so far.  In particular, besides just yielding
    results, computation in these languages may assign to mutable
    variables (reference cells, arrays, mutable record fields, etc.);
    perform input and output to files, displays, or network
    connections; make non-local transfers of control via exceptions,
    jumps, or continuations; engage in inter-process synchronization
    and communication; and so on.  In the literature on programming
    languages, such "side effects" of computation are collectively
    referred to as _computational effects_.

    In this chapter, we'll see how one sort of computational effect --
    mutable references -- can be added to the calculi we have studied.
    The main extension will be dealing explicitly with a _store_ (or
    _heap_) and _pointers_ that name store locations.  This extension
    is fairly straightforward to define; the most interesting part is
    the refinement we need to make to the statement of the type
    preservation theorem. *)
(** TERSE: Most real languages include _impure_ features
    ("computational effects")...
       - mutable pointer structures
       - non-local control constructs (exceptions, continuations, etc.)
       - inter-process synchronization and communication
       - etc.

    Goal for this chapter: Formalize pointers. *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-deprecated-syntactic-definition".
From Stdlib Require Import Strings.String.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From PLF Require Import Maps.
(* LATER: Arguably this should not depend on Smallstep, which defines
   Imp.  The only reason it is this way now is to get definitions of
   relation, deterministic, multi, etc. *)
From PLF Require Import Smallstep.
From Stdlib Require Import List. Import Datatypes.
Check length.

Import Nat.
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** * Definitions *)

(* SOONER: A bit too abrupt. *)
(** FULL: Pretty much every programming language provides some form of
    assignment operation that changes the contents of a previously
    allocated piece of storage.  (Rocq's internal language Gallina is a
    rare exception!)

    In some languages -- notably ML and its relatives -- the
    mechanisms for name binding and those for assignment are kept
    separate.  We can have a variable [x] whose _value_ is the number
    [5], or we can have a variable [y] whose value is a
    _reference_ (or _pointer_) to a mutable cell whose current
    contents is [5].  These are different things, and the difference
    is visible to the programmer.  We can add [x] to another number,
    but not assign to it.  We can use [y] to assign a new value to the
    cell that it points to (by writing [y:=84]), but we cannot use [y]
    directly as an argument to an operation like [+].  Instead, we
    must explicitly _dereference_ it, writing [!y] to obtain its
    current contents.

    In most other languages -- in particular, in all members of the C
    family, including Java -- _every_ variable name refers to a
    mutable cell, and the operation of dereferencing a variable to
    obtain its current contents is implicit.

    For purposes of formal study, it is useful to keep these
    mechanisms separate.  The development in this chapter will closely
    follow ML's model.  Applying the lessons learned here to C-like
    languages is a straightforward matter of collapsing some
    distinctions and rendering some operations such as dereferencing
    implicit instead of explicit. *)
(** TERSE: In most real-world programming languages, the mechanisms of
    _name binding_ and _storage allocation_ are (intentionally)
    confused: every name refers to a mutable piece of storage.

    Conceptually, it's cleaner to separate the two:
       - use the mechanisms we already have for name binding
         (abstraction, let);
       - introduce new operations for allocating, changing,
         and looking up the contents of references (pointers). *)

(* ###################################################################### *)
(** * Syntax *)

(** FULL: In this chapter, we study adding mutable references to the
    simply-typed lambda calculus with natural numbers. *)

(* TERSE: HIDEFROMHTML *)
Module STLCRef.
(* TERSE: /HIDEFROMHTML *)

(** The basic operations on references are _allocation_,
    _dereferencing_, and _assignment_.

       - To allocate a reference, we use the [ref] operator, providing
         an initial value for the new cell.

         For example, [ref 5] creates a new cell containing the value
         [5] and reduces to a reference to that cell.

       - To read the current value of this cell, we use the
         dereferencing operator [!].

         For example, [!(ref 5)] reduces to [5].

       - To change the value stored in a cell, we use the assignment
         operator.

         If [r] is a reference, [r := 7] will store the value [7] in
         the cell referenced by [r]. *)

(* ################################### *)
(** *** Types *)

(** FULL: We start with the simply typed lambda calculus over the
    natural numbers. Besides the base natural-number type and arrow
    types, we add two more types to deal with references. First, we
    need the _unit type_, which we will use as the result type of an
    assignment operation.  We then add _reference types_. *)

(** If [T] is a type, then [Ref T] is the type of references to
    cells holding values of type [T].
[[
      T ::= Nat
          | Unit
          | T -> T
          | Ref T
]]
*)

(* TERSE: HIDEFROMHTML *)
Inductive ty : Type :=
  | Ty_Nat   : ty
  | Ty_Unit  : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Ref   : ty -> ty.
(* TERSE: /HIDEFROMHTML *)

(* ################################### *)
(** *** Terms *)

(** Besides the usual variables, abstractions, applications,
    terms related to natural numbers, and [unit], we need four
    more sorts of terms to handle mutable references:
<<
      t ::= ...              Terms
          | ref t              allocation
          | !t                 dereference
          | t := t             assignment
          | l                  location
>>
*)

(* TERSE: HIDEFROMHTML *)
Inductive tm  : Type :=
  (* STLC with numbers: *)
  | tm_var    : string -> tm
  | tm_app    : tm -> tm -> tm
  | tm_abs    : string -> ty -> tm -> tm
  | tm_const  : nat -> tm
  | tm_succ    : tm -> tm
  | tm_pred    : tm -> tm
  | tm_mult    : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* New terms: *)
  | tm_unit   : tm
  | tm_ref    : tm -> tm
  | tm_deref  : tm -> tm
  | tm_assign : tm -> tm -> tm
  | tm_loc    : nat -> tm.

(* INSTRUCTORS: If we don't import a variant of Stlc.v we need to re-declare
   the grammars.
 *)
Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.
Declare Scope stlc_scope.
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template stlc_ty *)
(* INSTRUCTORS: allow (global) identifiers,
  e.g. just a local variable or Fooo.bar.baz to appear as types. *)
Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.

(* INSTRUCTORS: quotation for shifting into stlc_ty parsing mode *)
Notation "<{{ x }}>" := x (x custom stlc_ty).

Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" :=
  (Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) : stlc_scope.
(* INSTRUCTORS: to extend this template, add new type constructs below. *)

(* NOTATION: SAZ 2024 - I recommend following the pattern below for all grammars *)
(* INSTRUCTORS: escape to arbitrary Rocq constr notation *)
Notation "$( t )" := t (in custom stlc_ty at level 0, t constr) : stlc_scope.
(* INSTRUCTORS: End Definition of template stlc_ty *)
(* INSTRUCTORS: ------------------------------------------------------------- *)

(* INSTRUCTORS: stcl_tm ----------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template stlc_tm *)
Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.

Notation "x y" :=
  (tm_app x y) (in custom stlc_tm at level 10, left associativity)
  : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.
(* INSTRUCTORS: End Definition of template stlc_tm *)
(* INSTRUCTORS: ------------------------------------------------------------- *)

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

(* INSTRUCTORS: Begin Definition of template stlc_unit *)
Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc_ty at level 0) : stlc_scope.
Notation "'unit'" := tm_unit (in custom stlc_tm at level 0) : stlc_scope.
(* INSTRUCTORS: End Definition of template stlc_unit *)

(* INSTRUCTORS: Begin Definition of template stlc_ref *)
Notation "'Ref' t" :=
  (Ty_Ref t) (in custom stlc_ty at level 4).
Notation "'loc' x" := (tm_loc x) (in custom stlc_tm at level 2) : stlc_scope.
Notation "'ref' x" := (tm_ref x) (in custom stlc_tm at level 2) : stlc_scope.
Notation "'!' x " := (tm_deref x) (in custom stlc_tm at level 2) : stlc_scope.
Notation " e1 ':=' e2 " := (tm_assign e1 e2) (in custom stlc_tm at level 21) : stlc_scope.
(* INSTRUCTORS: End Definition of template stlc_ref *)

Open Scope stlc_scope.

(* HIDE *)
Check <{ loc 0 }>.
Check <{ loc $(S 1) }>.
(* /HIDE *)
(* TERSE: /HIDEFROMHTML *)

(** FULL: Intuitively:
    - [ref t] (formally, [ref t]) allocates a new reference cell
      with the value [t] and reduces to the location of the newly
      allocated cell;

    - [!t] (formally, [deref t]) reduces to the contents of the
      cell referenced by [t];

    - [t1 := t2] (formally, [assign t1 t2]) assigns [t2] to the
      cell referenced by [t1]; and

    - [l] (formally, [loc l]) is a reference to the cell at
      location [l].  We'll discuss locations later. *)

(** FULL: In informal examples, we'll also freely use the extensions
    of the STLC developed in the \CHAP{MoreStlc} chapter; however, to keep
    the proofs small, we won't bother formalizing them again here.  (It
    would be easy to do so, since there are no very interesting
    interactions between those features and references.) *)

(* ################################### *)
(** *** Typing (Preview) *)

(** Informally, the typing rules for allocation, dereferencing, and
    assignment look roughly like this:
[[[
                           Gamma |-- t1 \in T1
                       ---------------------------                    (T_Ref)
                       Gamma |-- ref t1 \in Ref T1

                        Gamma |-- t1 \in Ref T1
                        -----------------------                     (T_Deref)
                          Gamma |-- !t1 \in T1

                        Gamma |-- t1 \in Ref T2
                          Gamma |-- t2 \in T2
                       -------------------------                   (T_Assign)
                       Gamma |-- t1 := t2 : Unit
]]]
    The rule for locations will require a bit more machinery, and this
    will motivate some changes to the other rules; we'll come back to
    this later. *)

(* ################################### *)
(** *** Values and Substitution *)

(** Besides abstractions, numbers, and the unit value, we have one new
    type of value: locations.

    A location is a concrete pointer value -- think of it like an address
    in memory. Locations should never be written directly by programmers;
    they are used to keep track of the intermediate states of programs
    involving references. In particular, the result of a [ref] expression
    is a location. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_nat : forall n : nat ,
      value <{ n }>
  | v_unit :
      value <{ unit }>
  | v_loc : forall l,
      value <{ loc l }>.

(* TERSE: HIDEFROMHTML *)
Hint Constructors value : core.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)

(** Extending substitution to handle the new syntax of terms is
    straightforward: substituting into a pointer leaves it
    unchanged.  *)
(* TERSE: HIDEFROMHTML *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of templat subst *)
(* NOTATION: SAZ 2024 - I think this notation should bind tigher than
   application, which is a good reason to put application higher than
   level 1 in the base stlc_tm grammar. *)
Reserved Notation "'[' x ':=' s ']' t"
     (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).
(* INSTRUCTORS: End Definition of subst subst *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* TERSE: /HIDEFROMHTML *)

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
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  (* unit *)
  | <{ unit }> =>
    t
  (* references *)
  | <{ ref t1 }> =>
      <{ ref ([x:=s] t1) }>
  | <{ !t1 }> =>
      <{ !([x:=s] t1) }>
  | <{ t1 := t2 }> =>
    <{ ([x:=s] t1) := ([x:=s] t2) }>
  | <{ loc _ }> =>
      t
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm) : stlc_scope.
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** * Pragmatics *)

(* ################################### *)
(** ** Side Effects and Sequencing *)

(** FULL: The fact that we've chosen the result of an assignment
    expression to be the trivial value [unit] allows a nice
    abbreviation for _sequencing_.  For example, we can write
<<
       r:=succ(!r); !r
>>
    as an abbreviation for
<<
       (\x:Unit, !r) (r:=succ(!r)).
>>
    This has the effect of reducing two expressions in order and
    returning the value of the second.  Restricting the type of the
    first expression to [Unit] helps the typechecker to catch some
    silly errors by permitting us to throw away the first value only
    if it is really guaranteed to be trivial.

    Notice that, if the second expression is also an assignment, then
    the type of the whole sequence will be [Unit], so we can validly
    place it to the left of another [;] to build longer sequences of
    assignments:
<<
       r:=succ(!r); r:=succ(!r); r:=succ(!r); r:=succ(!r); !r
>>
*)
(** TERSE: We can write (for example)
<<
       r:=succ(!r); !r
>>
   as an abbreviation for
<<
       (\x:Unit, !r) (r := succ(!r)).
>>
*)
(** FULL: Formally, we introduce sequencing as a _derived form_
    [tseq] that expands into an abstraction and an application. *)

(* TERSE: HIDEFROMHTML *)
(* SOONER: BCP 21: What are these doing here? *)
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Definition tseq t1 t2 :=
  <{ (\ x : Unit, t2)  t1 }>.

Notation "t1 ; t2" := (tseq t1 t2) (in custom stlc_tm at level 3) : stlc_scope.
(* TERSE: /HIDEFROMHTML *)

(* HIDE *)
(** If we were building a full-blown programming language instead of
    just a theoretical model, this derived form could be implemented
    by giving the parser a production for expressions of the form
    [t1;t2] but immediately expanding such expressions into an
    abstraction and an application instead of defining a separate
    [tseq] constructor for the abstract syntax tree datatype. *)
(* /HIDE *)

(* ################################### *)
(** ** References and Aliasing *)

(** It is important to bear in mind the difference between the
    _reference_ that is bound to some variable [r] and the _cell_
    in the store that is pointed to by this reference.

    If we make a copy of [r], for example by binding its value to
    another variable [s], what gets copied is only the reference,
    not the contents of the cell itself.

    For example, after reducing
<<
      let r = ref 5 in
      let s = r in
      s := 82;
      (!r)+1
>>
(* SOONER: Easy to get confused between the two forms of "assignment"!  Say
           something about this... *)
    the cell referenced by [r] will contain the value [82], while the
    result of the whole expression will be [83].  The references [r]
    and [s] are said to be _aliases_ for the same cell. *)

(** TERSE: *** *)

(** The possibility of aliasing can make programs with references
    quite tricky to reason about.  For example, the expression
<<
      r := 5; r := !s
>>
    assigns [5] to [r] and then immediately overwrites it with [s]'s
    current value; this has exactly the same effect as the single
    assignment
<<
      r := !s
>>
    _unless_ we happen to do it in a context where [r] and [s] are
    aliases for the same cell!
<<
      let r = ref 0 in
      let s = r in
      r := 5; r := !s
>>
*)

(* ################################### *)
(** ** Shared State *)

(** Of course, aliasing is also a large part of what makes references
    useful.  In particular, it allows us to set up "implicit
    communication channels" -- shared state -- between different parts
    of a program.  For example, suppose we define a reference cell and
    two functions that manipulate its contents:
<<
      let c = ref 0 in
      let incc = \_:Unit, (c := succ (!c); !c) in
      let decc = \_:Unit, (c := pred (!c); !c) in
      ...
>>
*)

(** FULL: Note that, since their argument types are [Unit], the
    arguments to the abstractions in the definitions of [incc] and
    [decc] are not providing any useful information to the bodies of
    these functions (using the wildcard [_] as the name of the bound
    variable is a reminder of this).  Instead, their purpose of these
    abstractions is to "slow down" the execution of the function
    bodies.  Since function abstractions are values, the two [let]s are
    executed simply by binding these functions to the names [incc] and
    [decc], rather than by actually incrementing or decrementing [c].
    Later, each call to one of these functions results in its body
    being executed once and performing the appropriate mutation on
    [c].  Such functions are often called _thunks_.

    In the context of these declarations, calling [incc] results in
    changes to [c] that can be observed by calling [decc].  For
    example, if we replace the [...] with [(incc unit; incc unit; decc
    unit)], the result of the whole program will be [1]. *)
(* SOONER: the program [(incc unit; incc unit; decc unit)] does not
   typecheck because [incc unit] has type nat. What's the least awkward
   way to fix this? (Ignore it? Make the result type Unit and add a [read]
   method?) *)

(** TERSE: The [Unit]-abstractions ("thunks") are used here to prevent
    reduction until later. *)

(* ################################### *)
(** ** Objects *)

(** We can go a step further and write a _function_ that creates [c],
    [incc], and [decc], packages [incc] and [decc] together into a
    record, and returns this record:
<<
      newcounter =
          \_:Unit,
             let c = ref 0 in
             let incc = \_:Unit, (c := succ (!c); !c) in
             let decc = \_:Unit, (c := pred (!c); !c) in
             {i=incc, d=decc}
>>
*)

(** TERSE: *** *)

(** Now, each time we call [newcounter], we get a new record of
    functions that share access to the same storage cell [c].  The
    caller of [newcounter] can't get at this storage cell directly,
    but can affect it indirectly by calling the two functions.  In
    other words, we've created a simple form of _object_.
<<
      let c1 = newcounter unit in
      let c2 = newcounter unit in
      // we've allocated two separate storage cells now!
      let r1 = c1.i unit in
      let r2 = c2.i unit in
      r2  // yields 1, not 2!
>>
 *)

(* FULL *)
(* EX1M? (store_draw) *)
(** Draw (on paper) the contents of the store at the point in
    execution where the first two [let]s have finished and the third
    one is about to begin. *)

(* SOLUTION *)
(* LATER: Solution! *)
(* /SOLUTION *)
(** [] *)
(* /FULL *)

(* ################################### *)
(** ** References to Compound Types *)

(** A reference cell need not contain just a number: the primitives
    we've defined above allow us to create references to values of any
    type, including functions.  For example, we can use references to
    functions to give a(n inefficient) implementation of arrays of
    numbers as follows.

    Write [NatArray] for the type [Ref (Nat->Nat)]. *)

(** FULL: Recall the [equal] function from the \CHAP{MoreStlc} chapter:
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

(** TERSE: *** *)

(** To build a new array, we allocate a reference cell and fill
    it with a function that, when given an index, always returns [0].
<<
      newarray = \_:Unit, ref (\n:Nat,0)
>>
*)

(** TERSE: *** *)

(** To look up an element of an array, we apply the function
    to the desired index.
<<
      lookup = \a:NatArray, \n:Nat, (!a) n
>>
*)

(** TERSE: *** *)

(** The interesting part of the encoding is the [update] function.  It
    takes an array, an index, and a new value to be stored at that index, and
    it does its job by creating (and storing in the reference) a new function
    that, when it is asked for the value at this very index, returns the new
    value that was given to [update], while on all other indices it passes the
    lookup to the function that was previously stored in the reference.
<<
      update = \a:NatArray, \m:Nat, \v:Nat,
                   let oldf = !a in
                   a := (\n:Nat, if equal m n then v else oldf n);
>>
*)

(** TERSE: *** *)

(** References to values containing other references can also be very
    useful, allowing us to define data structures such as mutable
    lists and trees. *)
(* LATER: (Such structures generally also involve \defterm{recursive
   types}...)  (Maybe refer people to TAPL?) *)

(* FULL *)
(* EX2M! (compact_update) *)
(** If we defined [update] more compactly like this
<<
      update = \a:NatArray, \m:Nat, \v:Nat,
                  a := (\n:Nat, if equal m n then v else (!a) n)
>>
would it behave the same? *)

(* SOLUTION *)
(** No: calls to [lookup] with any index other than the one given to
    [update] will now diverge.  The point is that we need to make sure
    we look up the value stored in [a] _before_ we overwrite it with
    the new function.  Otherwise, when we get around to doing the
    lookup, we will find the new function, not the original one. *)
(* /SOLUTION *)

(* GRADE_MANUAL 2: compact_update *)
(** [] *)
(* /FULL *)

(* ################################### *)
(** ** Null References *)

(** FULL: There is one final significant difference between our
    references and C-style mutable variables: in C-like languages,
    variables holding pointers into the heap may sometimes have the
    value [NULL].  Dereferencing such a "null pointer" is an error,
    and results either in a clean exception (Java and C[#]) or in
    arbitrary and possibly insecure behavior (C and relatives like
    C++).  Null pointers cause significant trouble in C-like
    languages: the fact that any pointer might be null means that any
    dereference operation in the program can potentially fail.

    Even in ML-like languages, there are sometimes situations where
    we may or may not have a valid pointer in our hands.  Fortunately,
    there is no need to extend the basic mechanisms of references to
    represent such situations: the sum types introduced in the
    \CHAP{MoreStlc} chapter already give us what we need.

    First, we can use sums to build an analog of the [option] types
    introduced in the \CHAPV1{Lists} chapter of _Logical Foundations_.
    Define [Option T] to be an abbreviation for [Unit + T].

    Then a "nullable reference to a [T]" is simply an element of the
    type [Option (Ref T)].  *)
(** TERSE: One more difference between our references and C-style
    mutable variables: _null pointers_.

      - In C, a pointer variable can contain either a valid pointer
        into the heap or the special value [NULL].

      - A source of many errors and much tricky reasoning:
          - (any pointer may potentially be "not there")
          - but occasionally useful

      - Nullable pointers are easy to implement using references
        plus options (which can be built out of disjoint sum types):
<<
            Option T       =  Unit + T
            NullableRef T  =  Ref (Option T)
>>
*)

(* ################################### *)
(** ** Garbage Collection *)

(** A last issue that we should mention before we move on with formalizing
    references is storage _de_-allocation.  We have not provided any
    primitives for freeing reference cells when they are no longer needed.
    Instead, like many modern languages (including OCaml, Haskell, Java,
    etc.) we rely on the run-time system to perform _garbage collection_,
    automatically identifying and reusing cells that can no longer be
    reached by the program. *)

(** TERSE: *** *)

(** This is _not_ just a question of taste in language design: it is
    extremely difficult to achieve type safety in the presence of an
    explicit deallocation operation.

    One reason for this is the familiar _dangling reference_ problem:
    we allocate a cell holding a number, save a reference to it in
    some data structure, use it for a while, then deallocate it and
    allocate a new cell holding a boolean, possibly reusing the same
    storage.  Now we can have two names for the same storage cell --
    one with type [Ref Nat] and the other with type [Ref Bool]. *)

(* FULL *)
(* EX2M (type_safety_violation) *)
(** Show how this can lead to a violation of type safety. *)

(* SOLUTION *)
(** Suppose the language provides a primitive [free] that takes a
    reference cell as argument and releases its storage so that (say)
    the very next allocation of a reference cell will obtain the same
    piece of memory.  Then the program
<<
    let r = ref 0 in
    let s = r in
    free r;
    let t = ref true in
    t := false;
    succ (!s)
>>
    will reduce to the stuck term [succ false].  Note that aliasing
    plays a crucial role here in setting up the problem, since it
    prevents us from detecting invalid deallocations by simply making
    [free r] illegal if the variable [r] appears free in the remainder
    of the expression.

    This sort of example is easy to mimic in a language like C with
    manual memory management (our [ref] constructor corresponds to C's
    [malloc], our [free] to a simplified version of C's [free]). *)
(* /SOLUTION *)

(* GRADE_MANUAL 2: type_safety_violation *)
(** [] *)
(* /FULL *)

(* ###################################################################### *)
(** * Operational Semantics *)

(* ################################### *)
(** ** Locations *)

(** FULL: The most subtle aspect of the treatment of references
    appears when we consider how to formalize their operational
    behavior.  One way to see why is to ask, "What should be the
    _values_ of type [Ref T]?"  The crucial observation that we need
    to take into account is that reducing a [ref] operator should
    _do_ something -- namely, allocate some storage -- and the result
    of the operation should be a reference to this storage.

    What, then, is a reference?

    The run-time store in most programming-language implementations is
    essentially just a big array of bytes.  The run-time system keeps
    track of which parts of this array are currently in use.  When we
    need to allocate a new reference cell, we allocate a large enough
    segment from the free region of the store (4 bytes for integer
    cells, 8 bytes for cells storing [Float]s, etc.), record somewhere
    that it is being used, and return the index (typically, a 32- or
    64-bit integer) of the start of the newly allocated region.  These
    indices are references.

    For present purposes, there is no need to be quite so concrete.
    We can think of the store as an array of _values_, rather than an
    array of bytes, abstracting away from the different sizes of the
    run-time representations of different values.  A reference, then,
    is simply an index into the store.  (If we like, we can even
    abstract away from the fact that these indices are numbers, but
    for purposes of formalization in Rocq it is convenient to use
    numbers.)  We use the word _location_ instead of _reference_ or
    _pointer_ to emphasize this abstract quality.

    Treating locations abstractly in this way will prevent us from
    modeling the _pointer arithmetic_ found in low-level languages
    such as C.  This limitation is intentional.  While pointer
    arithmetic is occasionally very useful, especially for
    implementing low-level services such as garbage collectors, it
    cannot be tracked by most type systems: knowing that location [n]
    in the store contains a [float] doesn't tell us anything useful
    about the type of location [n+4].  In C, pointer arithmetic is a
    notorious source of type-safety violations. *)
(** TERSE: A reference names a location in the _store_ (a.k.a. heap).

    What is the store?

      - Concretely: An array of 8-bit bytes, indexed by 32-bit integers.

      - More abstractly: a list or array, of values

      - Even more abstractly: a partial function from locations to values.

    We'll choose the middle way here: A store is a list of values, and
    a location is a natural-number index into this list.
*)

(* ################################### *)
(** ** Stores *)

(** FULL: Recall that, in the small-step operational semantics for
    Imp, the step relation needed to carry along an auxiliary state in
    addition to the program being executed.  In the same way, once we
    have added reference cells to the STLC, our step relation must
    carry along a store to keep track of the contents of reference
    cells.

    We could re-use the same functional representation we used for
    states in Imp, but for carrying out the proofs in this chapter it
    is actually more convenient to represent a store simply as a
    _list_ of values.  (The reason we didn't use this representation
    before is that, in Imp, a program could modify any location at any
    time, so states had to be ready to map _any_ variable to a value.
    However, in the STLC with references, the only way to create a
    reference cell is with [ref t1], which puts the value of [t1]
    in a new reference cell and reduces to the location of the newly
    created reference cell. When reducing such an expression, we can
    just add a new reference cell to the end of the list representing
    the store.) *)

(** TERSE: A store is just a _list_ of values.  (This more concrete
    representation will be more convenient for proofs than the
    functional representation we used in Imp.) *)

(* INSTRUCTORS: Warning: We won't be able to use list notations like
   [[]] and [[one]] in this file because they conflict with our
   notation for substitution. *)

Definition store := list tm.

(** We use [store_lookup n st] to retrieve the value of the reference
    cell at location [n] in the store [st].  Note that we must give a
    default value to [nth] in case we try looking up an index which is
    too large. (In fact, we never actually do this, but _proving_
    that we don't will require a bit of work.) *)

Definition store_lookup (n:nat) (st:store) :=
  nth n st <{ unit }>.

(** TERSE: *** *)

(** To update the store, we use the [replace] function, which replaces
    the contents of a cell at a particular index. *)

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil    => nil
  | h :: t =>
    match n with
    | O    => x :: t
    | S n' => h :: replace n' x t
    end
  end.

(** FULL: As might be expected, we will also need some technical
    lemmas about [replace]; they are straightforward to prove. *)

(* TERSE: HIDEFROMHTML *)
Lemma replace_nil : forall A n (x:A),
  replace n x nil = nil.
(* FOLD *)
Proof.
  destruct n; auto.
Qed.
(* /FOLD *)

Lemma length_replace : forall A n x (l:list A),
  length (replace n x l) = length l.
(* FOLD *)
Proof with auto.
  intros A n x l. generalize dependent n.
  induction l; intros n.
    destruct n...
    destruct n...
      simpl. rewrite IHl...
Qed.
(* /FOLD *)

Lemma lookup_replace_eq : forall l t st,
  l < length st ->
  store_lookup l (replace l t st) = t.
(* FOLD *)
Proof with auto.
  intros l t st.
  unfold store_lookup.
  generalize dependent l.
  induction st as [|t' st']; intros l Hlen.
  - (* st = [] *)
   inversion Hlen.
  - (* st = t' :: st' *)
    destruct l; simpl...
    apply IHst'. simpl in Hlen. lia.
Qed.
(* /FOLD *)

Lemma lookup_replace_neq : forall l1 l2 t st,
  l1 <> l2 ->
  store_lookup l1 (replace l2 t st) = store_lookup l1 st.
(* FOLD *)
Proof with auto.
  unfold store_lookup.
  induction l1 as [|l1']; intros l2 t st Hneq.
  - (* l1 = 0 *)
    destruct st.
    + (* st = [] *) rewrite replace_nil...
    + (* st = _ :: _ *) destruct l2... contradict Hneq...
  - (* l1 = S l1' *)
    destruct st as [|t2 st2].
    + (* st = [] *) destruct l2...
    + (* st = t2 :: st2 *)
      destruct l2...
      simpl; apply IHl1'...
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* ################################### *)
(** ** Reduction *)

(** TERSE: First, we augment existing reduction rules with stores:
[[[
                               value v2
                -------------------------------------               (ST_AppAbs)
                (\x:T2,t1) v2 / st --> [x:=v2]t1 / st

                        t1 / st --> t1' / st'
                     ---------------------------                      (ST_App1)
                     t1 t2 / st --> t1' t2 / st'

                  value v1     t2 / st --> t2' / st'
                  ----------------------------------                  (ST_App2)
                     v1 t2 / st --> v1 t2' / st'
]]]
*)

(** TERSE: *** *)

(** Now we can give the rules for the new constructs:
[[[
                   ------------------------------                  (ST_RefValue)
                   ref v / st --> loc |st| / st,v

                        t1 / st --> t1' / st'
                    -----------------------------                    (ST_Ref)
                    ref t1 / st --> ref t1' / st'

                               l < |st|
                     ----------------------------------            (ST_DerefLoc)
                     !(loc l) / st --> lookup l st / st

                        t1 / st --> t1' / st'
                       -----------------------                       (ST_Deref)
                       !t1 / st --> !t1' / st'

                               l < |st|
                ------------------------------------------         (ST_Assign)
                loc l := v / st --> unit / replace l v st

                        t1 / st --> t1' / st'
                 -----------------------------------               (ST_Assign1)
                 t1 := t2 / st --> t1' := t2 / st'

                        t2 / st --> t2' / st'
                 -----------------------------------               (ST_Assign2)
                 v1 := t2 / st --> v1 := t2' / st'
]]]
*)

(** FULL: Next, we need to extend the operational semantics to take
    stores into account.  Since the result of reducing an expression
    will in general depend on the contents of the store in which it is
    reduced, the evaluation rules should take not just a term but
    also a store as argument.  Furthermore, since the reduction of a
    term can cause side effects on the store, and these may affect the
    reduction of other terms in the future, the reduction rules need
    to return a new store.  Thus, the shape of the single-step
    reduction relation needs to change from [t --> t'] to [t / st --> t' /
    st'], where [st] and [st'] are the starting and ending states of
    the store.

    To carry through this change, we first need to augment all of our
    existing reduction rules with stores:
[[[
                               value v2
                ------------------------------------- (ST_AppAbs)
                (\x:T2,t1) v2 / st --> [x:=v2]t1 / st

                        t1 / st --> t1' / st'
                     --------------------------- (ST_App1)
                     t1 t2 / st --> t1' t2 / st'

                  value v1     t2 / st --> t2' / st'
                  ---------------------------------- (ST_App2)
                     v1 t2 / st --> v1 t2' / st'
]]]
    Note that the first rule here returns the store unchanged, since
    function application, in itself, has no side effects.  The other
    two rules simply propagate side effects from premise to
    conclusion.

    Now, the result of reducing a [ref] expression will be a fresh
    location; this is why we included locations in the syntax of terms
    and in the set of values.  It is crucial to note that making this
    extension to the syntax of terms does not mean that we intend
    _programmers_ to write terms involving explicit, concrete locations:
    such terms will arise only as intermediate results during reduction.
    This may seem odd, but it follows naturally from our design decision
    to represent the result of every reduction step by a modified _term_.
    If we had chosen a more "machine-like" model, e.g., with an explicit
    stack to contain values of bound identifiers, then the idea of adding
    locations to the set of allowed values might seem more obvious.

    In terms of this expanded syntax, we can state reduction rules
    for the new constructs that manipulate locations and the store.
    First, to reduce a dereferencing expression [!t1], we must first
    reduce [t1] until it becomes a value:
[[[
                        t1 / st --> t1' / st'
                       --------------------- (ST_Deref)
                       !t1 / st --> !t1' / st'
]]]
    Once [t1] has finished reducing, we should have an expression of
    the form [!l], where [l] is some location.  (A term that attempts
    to dereference any other sort of value, such as a function or
    [unit], is erroneous, as is a term that tries to dereference a
    location that is larger than the size [|st|] of the currently
    allocated store; the reduction rules simply get stuck in this
    case.  The type-safety properties established below assure us
    that well-typed terms will never misbehave in this way.)
[[[
                               l < |st|
                     ---------------------------------- (ST_DerefLoc)
                     !(loc l) / st --> lookup l st / st
]]]

    Next, to reduce an assignment expression [t1:=t2], we must first
    reduce [t1] until it becomes a value (a location), and then
    reduce [t2] until it becomes a value (of any sort):
[[[
                        t1 / st --> t1' / st'
                 ----------------------------------- (ST_Assign1)
                 t1 := t2 / st --> t1' := t2 / st'

                        t2 / st --> t2' / st'
                  --------------------------------- (ST_Assign2)
                  v1 := t2 / st --> v1 := t2' / st'
]]]
    Once we have finished with [t1] and [t2], we have an expression of
    the form [l:=v], which we execute by updating the store to make
    location [l] contain [v]:
[[[
                               l < |st|
                -----------------------------------   (ST_Assign)
                loc l := v / st --> unit / [l:=v]st
]]]
    The notation [[l:=v]st] means "the store that maps [l] to [v]
    and maps all other locations to the same thing as [st.]"  Note
    that the term resulting from this reduction step is just [unit];
    the interesting result is the updated store.

    Finally, to reduct an expression of the form [ref t1], we first
    reduce [t1] until it becomes a value:
[[[
                        t1 / st --> t1' / st'
                    --------------------------- (ST_Ref)
                    ref t1 / st --> ref t1' / st'
]]]
    Then, to reduce the [ref] itself, we choose a fresh location at
    the end of the current store -- i.e., location [|st|] -- and yield
    a new store that extends [st] with the new value [v].
[[[
                   -------------------------------- (ST_RefValue)
                   ref v / st --> loc |st| / st,v
]]]
    The value resulting from this step is the newly allocated location
    itself.  (Formally, [st,v] means [st ++ v::nil] -- i.e., to add
    a new reference cell to the store, we append it to the end.)

    Note that these reduction rules do not perform any kind of
    garbage collection: we simply allow the store to keep growing
    without bound as reduction proceeds.  This does not affect the
    correctness of the results of reduction (after all, the
    definition of "garbage" is precisely parts of the store that are
    no longer reachable and so cannot play any further role in
    reduction), but it means that a naive implementation of our
    evaluator might run out of memory where a more sophisticated
    evaluator would be able to continue by reusing locations whose
    contents have become garbage.

    Here are the rules again, formally: *)

(* HIDEFROMHTML *)
Reserved Notation "t '/' st '-->' t' '/' st'"
  (at level 40, st at next level, t' at next level, left associativity).
(* /HIDEFROMHTML *)

(* TERSE: HIDEFROMHTML *)
Inductive step : tm * store -> tm * store -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2 st,
         value v2 ->
         <{ (\x : T2, t1) v2 }> / st --> <{ [x := v2] t1 }> / st
  | ST_App1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 t2 }> / st --> <{ t1' t2 }> / st'
  | ST_App2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 t2 }> / st --> <{ v1 t2' }> / st'
  (* numbers *)
  | ST_SuccNat : forall (n : nat) st,
         <{ succ n }> / st --> tm_const (S n) / st
  | ST_Succ : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ succ t1 }> / st --> <{ succ t1' }> / st'
  | ST_PredNat : forall (n : nat) st,
         <{ pred n }> / st --> tm_const (n - 1) / st
  | ST_Pred : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ pred t1 }> / st --> <{ pred t1' }> / st'
  | ST_MultNats : forall (n1 n2 : nat) st,
      <{ n1 * n2 }> / st -->  tm_const (n1 * n2) / st
  | ST_Mult1 : forall t1 t2 t1' st st',
         t1 / st --> t1' / st' ->
         <{ t1 * t2 }> / st --> <{ t1' * t2 }> / st'
  | ST_Mult2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 * t2 }> / st --> <{ v1 * t2' }> / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st --> t1' / st' ->
         <{ if0 t1 then t2 else t3 }> / st --> <{ if0 t1' then t2 else t3 }> / st'
  | ST_If0_Zero : forall t2 t3 st,
         <{ if0 0 then t2 else t3 }> / st --> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
         <{ if0 $(S n) then t2 else t3 }> / st --> t3 / st
  (* references *)
  | ST_RefValue : forall v st,
         value v ->
         <{ ref v }> / st --> <{ loc $(length st) }> / (st ++ v::nil)
  | ST_Ref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ref t1 }> /  st --> <{ ref t1' }> /  st'
  | ST_DerefLoc : forall st l,
         l < length st ->
         <{ !(loc l) }> / st --> <{ $(store_lookup l st) }> / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ! t1 }> / st --> <{ ! t1' }> / st'
  | ST_Assign : forall v l st,
         value v ->
         l < length st ->
         <{ (loc l) := v }> / st --> <{ unit }> / replace l v st
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 := t2 }> / st --> <{ t1' := t2 }> / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 := t2 }> / st --> <{ v1 := t2' }> / st'

where "t '/' st '-->' t' '/' st'" := (step (t,st) (t',st')).

(** FULL: One slightly ugly point should be noted here: In the
    [ST_RefValue] rule, we extend the state by writing [st ++ v::nil]
    rather than the more natural [st ++ [v]].  The reason for this is
    that the notation we've defined for substitution uses square
    brackets, which clash with the standard library's notation for
    lists. *)

Hint Constructors step : core.

Definition multistep := (multi step).
Notation "t '/' st '-->*' t' '/' st'" :=
               (multistep (t,st) (t',st'))
               (at level 40, st at level 39, t' at level 39).
(* TERSE: /HIDEFROMHTML *)

(* ################################### *)
(** * Typing *)

(** The contexts assigning types to free variables are exactly the
    same as for the STLC: partial maps from identifiers to types. *)

Definition context := partial_map ty.

(* ################################### *)

(** ** Store typings *)

(** FULL: Having extended our syntax and reduction rules to accommodate
    references, our last job is to write down typing rules for the new
    constructs (and, of course, to check that these rules are sound!).

    Naturally, the key question is, "What is the type of a location?"
*)
(** TERSE: Naturally, the key question is, "What is the type of a
    location?" *)

(** FULL: First of all, notice that this question doesn't arise when
    typechecking terms that programmers actually write.  Concrete
    location constants arise only in terms that are the intermediate
    results of reduction; they are not in the language that
    programmers write.  So we only need to determine the type of a
    location when we're in the middle of a reduction sequence, e.g.,
    trying to apply the progress or preservation lemmas.  Thus, even
    though we normally think of typing as a _static_ program property,
    it makes sense for the typing of locations to depend on the
    _dynamic_ progress of the program too.

    As a first try, note that when we reduce a term containing
    concrete locations, the type of the result depends on the contents
    of the store that we start with.  For example, if we reduce the
    term [!(loc 1)] in the store [[unit, unit]], the result is [unit];
    if we reduce the same term in the store [[unit, \x:Unit,x]], the
    result is [\x:Unit,x].  With respect to the former store, the
    location [1] has type [Unit], and with respect to the latter it
    has type [Unit->Unit]. This observation leads us immediately to a
    first attempt at a typing rule for locations:
 *)
(** TERSE: As a first try, observe that the type of a location is
    connected to the contents of the store [[st]].
*)
(**
[[[
                             Gamma |-- lookup l st : T1
                             --------------------------
                             Gamma |-- loc l : Ref T1
]]]
 *)
(** TERSE: But where does [[st]] come from? *)
(** FULL: That is, to find the type of a location [l], we look up the
    current contents of [l] in the store and calculate the type [T1]
    of the contents.  The type of the location is then [Ref T1].

    Having begun in this way, we need to go a little further to reach a
    consistent state.  In effect, by making the type of a term depend on
    the store, we have changed the typing relation from a three-place
    relation (between contexts, terms, and types) to a four-place relation
    (between contexts, _stores_, terms, and types).  Since the store is,
    intuitively, part of the context in which we calculate the type of a
    term, let's write this four-place relation with the store to the left
    of the turnstile: [Gamma; st |-- t : T].  Our rule for typing
    references now has the form
 *)
(** TERSE: *** *)
(** TERSE: We could try adding [st] to the judgment: [Gamma; st |-- t : T],
    which gives us this rule:
*)
(**
[[[
                     Gamma; st |-- lookup l st : T1
                     ------------------------------
                      Gamma; st |-- loc l : Ref T1
]]]
*)
(** TERSE: But that means the _whole_ store [st], including all dynamically
    created values, is needed _during typechecking_.  This does not seem
    like something we want.

    Worse yet, it doesn't work at all for _cyclic_ stores.
*)
(** FULL:
    and all the rest of the typing rules in the system are extended
    similarly with stores.  (The other rules do not need to do anything
    interesting with their stores -- just pass them from premise to
    conclusion.)

    However, this rule will not quite do.  For one thing, typechecking
    is rather inefficient, since calculating the type of a location [l]
    involves calculating the type of the current contents [v] of [l].  If
    [l] appears many times in a term [t], we will re-calculate the type of
    [v] many times in the course of constructing a typing derivation for
    [t].  Worse, if [v] itself contains locations, then we will have to
    recalculate _their_ types each time they appear.  Worse yet, the
    proposed typing rule for locations may not allow us to derive
    anything at all if the store contains a _cycle_.  For example,
    there is no finite typing derivation for the location [0] with respect
    to this store:
 *)
(** TERSE: For example, what is the type of location [0] in the
    following store? *)
(**
<<
   [\x:Nat, (!(loc 1)) x, \x:Nat, (!(loc 0)) x]
>>
*)
(* FULL *)
(* EX3 (cyclic_store) *)
(** Can you find a term whose reduction will create this particular
    cyclic store? *)

Theorem cyclic_store:
  exists t,
    t / nil -->*
    <{ unit }> / (<{ \x:Nat, (!(loc 1)) x }> :: <{ \x:Nat, (!(loc 0)) x }> :: nil).
Proof.
  (* ADMITTED *)
  Notation "'let' x ':' T '=' t1 'in' t2" :=
    <{ (\x:T, t2) t1 }> (in custom stlc_tm at level 3, T custom stlc_ty).
  remember ("r0"%string) as r0.
  remember ("r1"%string) as r1.
  exists <{ let r0 : (Ref (Nat -> Nat)) = ref (\x:Nat, x) in
            let r1 : (Ref (Nat -> Nat)) = ref (\x:Nat, (!r0) x) in
            (r0 := \x:Nat, (!r1) x) }>.
  subst.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  eapply multi_step. { apply ST_Assign. auto. simpl. auto. } simpl.
  eapply multi_refl.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)
(** TERSE: *** *)

(** FULL: These problems arise from the fact that our proposed
    typing rule for locations requires us to recalculate the type of a
    location every time we mention it in a term.  But this,
    intuitively, should not be necessary.  After all, when a location
    is first created, we know the type of the initial value that we
    are storing into it.  Suppose we are willing to enforce the
    invariant that the type of the value contained in a given location
    _never changes_; that is, although we may later store other values
    into this location, those other values will always have the same
    type as the initial one.  In other words, we always have in mind a
    single, definite type for every location in the store, which is
    fixed when the location is allocated.  Then these intended types
    can be collected together as a _store typing_ -- a finite function
    mapping locations to types.

    As with the other type systems we've seen, this conservative typing
    restriction on allowed updates means that we will rule out as
    ill-typed some programs that could reduce perfectly well without
    getting stuck.

    Just as we did for stores, we will represent a store type simply
    as a list of types: the type at index [i] records the type of the
    values that we expect to be stored in cell [i]. *)
(** TERSE: Instead, we establish an _invariant_ that the type of
    value stored in a location never changes.

     This _static_ representation of the store contents is called a
     _store typing_: *)

Definition store_ty := list ty.

(** TERSE: Here we represent locations as indices into a _list_ of
    types so the type at index [i] is the type of the values stored in
    cell [i]. *)

(** The [store_Tlookup] function retrieves the type at a particular
    index. *)

Definition store_Tlookup (n:nat) (ST:store_ty) :=
  nth n ST <{{ Unit }}>.

(** TERSE: *** *)

(** FULL: Suppose we are given a store typing [ST] describing the store
    [st] in which some term [t] will be reduced.  Then we can use
    [ST] to calculate the type of the result of [t] without ever
    looking directly at [st].  For example, if [ST] is [[Unit,
    Unit->Unit]], then we can immediately infer that [!(loc 1)] has
    type [Unit->Unit].  More generally, the typing rule for locations
    can be reformulated in terms of store typings like this: *)
(** TERSE: We can use the store typing [ST] to give a type to
    any location [l] like this: *)
(**
[[[
                                 l < |ST|
                   ----------------------------------------------
                   Gamma; ST |-- loc l : Ref (store_Tlookup l ST)
]]]
*)
(** FULL: That is, as long as [l] is a valid location, we can compute the
    type of [l] just by looking it up in [ST].  Typing is again a
    four-place relation, but it is parameterized on a store _typing_
    rather than a concrete store.  The rest of the typing rules are
    analogously augmented with store typings. *)

(* ################################### *)
(** ** The Typing Relation *)

(** FULL: We can now formalize the typing relation for the STLC with
    references.  Here, again, are the rules we're adding to the base
    STLC (with numbers and [Unit]): *)

(**
[[[
                               l < |ST|
             ----------------------------------------------             (T_Loc)
             Gamma; ST |-- loc l : Ref (store_Tlookup l ST)

                         Gamma; ST |-- t1 : T1
                     -----------------------------                      (T_Ref)
                     Gamma; ST |-- ref t1 : Ref T1

                      Gamma; ST |-- t1 : Ref T1
                      -------------------------                       (T_Deref)
                        Gamma; ST |-- !t1 : T1

                      Gamma; ST |-- t1 : Ref T2
                        Gamma; ST |-- t2 : T2
                    -----------------------------                    (T_Assign)
                    Gamma; ST |-- t1 := t2 : Unit
]]]
*)

(* HIDEFROMHTML *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template STCL has_type notation MODIFIED *)
Notation "x '|->' v ';' m " := (update m x v)
  (in custom stlc_tm at level 0, x constr at level 0,
   v custom stlc_ty, right associativity) : stlc_scope.

Notation "x '|->' v " := (update empty x v)
  (in custom stlc_tm at level 0, x constr at level 0, v custom stlc_ty) : stlc_scope.

(* NOTATION: If we don't include the following, then <{ empty |-- t : T }>
   will print as <{ $(empty) |-- t : T }> *)
Notation "'empty'" := empty (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '/' ST '|--' t '\in' T }>"
            (at level 0, Gamma custom stlc_tm at level 200, t custom stlc_tm, T custom stlc_ty).
(* INSTRUCTORS: End STCL has_type notation MODIFIED *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* /HIDEFROMHTML *)

(* TERSE: HIDEFROMHTML *)
Inductive has_type (ST : store_ty) : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      <{ Gamma / ST |-- x \in T1 }>
  | T_Abs : forall Gamma x T1 T2 t1,
      <{ x |-> T2; Gamma  / ST |-- t1 \in T1 }> ->
      <{ Gamma / ST |-- \x:T2, t1 \in T2 -> T1 }>
  | T_App : forall T1 T2 Gamma t1 t2,
      <{ Gamma / ST |-- t1 \in T2 -> T1 }> ->
      <{ Gamma / ST |-- t2 \in T2 }> ->
      <{ Gamma / ST |-- t1 t2 \in T1 }>
  | T_Nat : forall Gamma (n : nat),
      <{ Gamma / ST |-- n \in Nat }>
  | T_Succ : forall Gamma t1,
      <{ Gamma / ST |-- t1 \in Nat }> ->
      <{ Gamma / ST |-- succ t1 \in Nat }>
  | T_Pred : forall Gamma t1,
      <{ Gamma / ST |-- t1 \in Nat }> ->
      <{ Gamma / ST |-- pred t1 \in Nat }>
  | T_Mult : forall Gamma t1 t2,
      <{ Gamma / ST |-- t1 \in Nat }> ->
      <{ Gamma / ST |-- t2 \in Nat }> ->
      <{ Gamma / ST |-- t1 * t2 \in Nat }>
  | T_If0 : forall Gamma t1 t2 t3 T0,
      <{ Gamma / ST |-- t1 \in Nat }> ->
      <{ Gamma / ST |-- t2 \in T0 }> ->
      <{ Gamma / ST |-- t3 \in T0 }> ->
      <{ Gamma / ST |-- if0 t1 then t2 else t3 \in T0 }>
  | T_Unit : forall Gamma,
      <{ Gamma / ST |-- unit \in Unit }>
  | T_Loc : forall Gamma l,
      l < length ST ->
      <{ Gamma / ST |-- (loc l) \in Ref $(store_Tlookup l ST) }>
  | T_Ref : forall Gamma t1 T1,
      <{ Gamma / ST |-- t1 \in T1 }> ->
      <{ Gamma / ST |-- (ref t1) \in Ref T1 }>
  | T_Deref : forall Gamma t1 T1,
      <{ Gamma / ST |-- t1 \in Ref T1 }> ->
      <{ Gamma / ST |-- (! t1) \in T1 }>
  | T_Assign : forall Gamma t1 t2 T2,
      <{ Gamma / ST |-- t1 \in Ref T2 }> ->
      <{ Gamma / ST |-- t2 \in T2 }> ->
      <{ Gamma / ST |-- (t1 := t2) \in Unit }>

where "<{ Gamma '/' ST '|--' t '\in' T }>" := (has_type ST Gamma t T).

Hint Constructors has_type : core.
(* TERSE: /HIDEFROMHTML *)

(** FULL: Of course, these typing rules will accurately predict the results
    of reduction only if the concrete store used during reduction
    actually conforms to the store typing that we assume for purposes
    of typechecking.  This proviso exactly parallels the situation
    with free variables in the basic STLC: the substitution lemma
    promises that, if [Gamma |-- t : T], then we can replace the free
    variables in [t] with values of the types listed in [Gamma] to
    obtain a closed term of type [T], which, by the type preservation
    theorem will reduce to a final result of type [T] if it yields
    any result at all.  We will see below how to formalize an
    analogous intuition for stores and store typings.

    However, for purposes of typechecking the terms that programmers
    actually write, we do not need to do anything tricky to guess what
    store typing we should use.  Concrete locations arise only in
    terms that are the intermediate results of reduction; they are
    not in the language that programmers write.  Thus, we can simply
    typecheck the programmer's terms with respect to the _empty_ store
    typing.  As reduction proceeds and new locations are created, we
    will always be able to see how to extend the store typing by
    looking at the type of the initial values being placed in newly
    allocated cells; this intuition is formalized in the statement of
    the type preservation theorem below.  *)

(* ################################### *)
(** * Properties *)

(** FULL: Our final task is to check that standard type safety
    properties continue to hold for the STLC with references.  The
    progress theorem ("well-typed terms are not stuck") can be stated
    and proved almost as for the STLC; we just need to add a few
    straightforward cases to the proof to deal with the new
    constructs.  The preservation theorem is a bit more interesting,
    so let's look at it first.  *)
(** TERSE: Standard theorems...
      - Progress -- pretty much same as always
      - Preservation -- needs to be stated more carefully! *)

(* ################################### *)
(** ** Well-Typed Stores *)

(** FULL: Since we have extended both the reduction relation (with
    initial and final stores) and the typing relation (with a store
    typing), we need to change the statement of preservation to
    include these parameters.  But clearly we cannot just add stores
    and store typings without saying anything about how they are
    related -- i.e., this is wrong: *)
(** TERSE: The evaluation and typing relations take more parameters
    now, so at a minumum we have to add these to the statement of
    preservation... *)

Theorem preservation_wrong : forall ST T t st t' st',
  <{ empty / ST |-- t \in T }> ->
  t / st --> t' / st' ->
  <{ empty / ST |-- t' \in T }>.
Abort.

(** FULL: If we typecheck with respect to some set of assumptions
    about the types of the values in the store and then reduce with
    respect to a store that violates these assumptions, the result
    will be disaster.  We say that a store [st] is _well typed_ with
    respect a store typing [ST] if the term at each location [l] in
    [st] has the type at location [l] in [ST].  Since only closed
    terms ever get stored in locations (why?), it suffices to type
    them in the empty context. The following definition of
    [store_well_typed] formalizes this.  *)
(** TERSE: Obviously wrong: no relation between assumed store typing
    and provided store! *)

(** TERSE: *** *)

(** TERSE: We need a way of saying "this store satisfies the
    assumptions of that store typing"... *)

Definition store_well_typed (ST:store_ty) (st:store) :=
  length ST = length st /\
  (forall l, l < length st ->
     <{ empty / ST |-- $(store_lookup l st)
                           \in $(store_Tlookup l ST) }>).

(** Informally, we will write [ST |-- st] for [store_well_typed ST st]. *)

(** FULL: Intuitively, a store [st] is consistent with a store typing
    [ST] if every value in the store has the type predicted by the
    store typing.  The only subtle point is the fact that, when typing
    the values in the store, we supply the very same store typing to
    the typing relation.  This allows us to type circular stores like
    the one we saw above. *)

(* FULL *)
(* EX3 (store_not_unique) *)
(** Can you find a store [st], and two
    different store typings [ST1] and [ST2] such that both
    [ST1 |-- st] and [ST2 |-- st]? *)

(* SOLUTION *)
(* Let [st] be a store with a single location [0], such that
      [st]  =  [\x:Unit, (!(loc 0))(x)].
   Then [st] is well typed with
   respect to both of the following store typings:
      ST1  =  [Unit -> Unit]
      ST2  =  [Unit -> (Unit->Unit)].
   In fact, it is well typed with respect to any store typing of the form
      ST   =  [Unit -> T]
   for any type [T]. *)
(* /SOLUTION *)

Theorem store_not_unique:
  exists st, exists ST1, exists ST2,
    store_well_typed ST1 st /\
    store_well_typed ST2 st /\
    ST1 <> ST2.
Proof.
  (* ADMITTED *)
  exists (<{ \x:Unit, (!(loc 0)) x }> :: nil).
  exists (<{{ Unit -> Unit }}> :: nil).
  exists (<{{ Unit -> Nat }}> :: nil).
  unfold store_well_typed; simpl. repeat split.
  { intros [|l'].
    { intros _. repeat econstructor.
      replace (<{{ Unit -> Unit }}>)
      with (store_Tlookup 0 (<{{ Unit -> Unit }}>::nil)) at 2
        by reflexivity.
      repeat econstructor. }
    { intros H. solve_by_inverts 2. } }
  { intros [|l'].
    { intros _. repeat econstructor.
      replace (<{{ Unit -> Nat }}>)
      with (store_Tlookup 0 (<{{ Unit -> Nat }}>::nil)) at 2
        by reflexivity.
      repeat econstructor. }
    { intros H. solve_by_inverts 2. } }
  { congruence. }
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)

(** We can now state something closer to the desired preservation
    property: *)

Theorem preservation_lesswrong : forall ST T t st t' st',
  <{ empty / ST |-- t \in T }> ->
  t / st --> t' / st' ->
  store_well_typed ST st ->
  <{ empty / ST |-- t' \in T }>.
Abort.

(** FULL: This statement is fine for all of the reduction rules except
    the allocation rule [ST_RefValue].  The problem is that this rule
    yields a store with a larger domain than the initial store, which
    falsifies the conclusion of the above statement: if [st'] includes
    a binding for a fresh location [l], then [l] cannot be in the
    domain of [ST], and it will not be the case that [t'] (which
    definitely mentions [l]) is typable under [ST]. *)
(** TERSE: This works... for all but _one_ of the reduction rules!
    (Which?) *)
(** TERSE: *** *)
(** TERSE: The [ST_RefValue] rule is the problem:
[[[
                   -------------------------------- (ST_RefValue)
                   ref v / st --> loc |st| / st,v
]]]
    It allocates a fresh location [l] and adds it to the store, but
    the store typing [ST] doesn't know about [l], so [t'] won't be
    typeable under [ST]. *)
(** TERSE: *** *)

(** For example, the term [ref 5] is typeable in the empty context and
    empty store typing, but it steps to [loc 0], which is not typeable
    with an empty store typing. *)

(* ############################################ *)
(** ** Extending Store Typings *)

(** FULL: Evidently, since the store can increase in size during
    reduction, we need to allow the store _typing_ to grow during
    reduction as well. This motivates the following definition.  We
    say that the store type [ST'] _extends_ [ST] if [ST'] is just [ST]
    with some new types added to the end. *)
(** TERSE: Intuition: Since the store can grow during reduction, we
    need to let the store _typing_ grow too... *)

Inductive extends : store_ty -> store_ty -> Prop :=
  | extends_nil  : forall ST',
      extends ST' nil
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).

(** For example, the store typing [ [Nat] ] with a single location of
    type [Nat] extends the empty store typing. *)

(* TERSE: HIDEFROMHTML *)
Hint Constructors extends : core.

(** We'll need a few technical lemmas about extended contexts.

    First, looking up a type in an extended store typing yields the
    same result as in the original: *)

Lemma extends_lookup : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  store_Tlookup l ST' = store_Tlookup l ST.
(* FOLD *)
Proof with auto.
  intros l ST.
  generalize dependent l.
  induction ST as [|a ST2]; intros l ST' Hlen HST'.
  - (* nil *) inversion Hlen.
  - (* cons *) unfold store_Tlookup in *.
    destruct ST'.
    + (* ST' = nil *) inversion HST'.
    + (* ST' = a' :: ST'2 *)
      inversion HST'; subst.
      destruct l as [|l'].
      * (* l = 0 *) auto.
      * (* l = S l' *) simpl. apply IHST2...
        simpl in Hlen; lia.
Qed.
(* /FOLD *)

(** Next, if [ST'] extends [ST], the length of [ST'] is at least that
    of [ST]. *)

Lemma length_extends : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  l < length ST'.
(* FOLD *)
Proof with eauto.
  intros. generalize dependent l. induction H0; intros l Hlen.
    - inversion Hlen.
    - simpl in *.
      destruct l; try lia.
        apply ->Nat.succ_lt_mono. apply IHextends. lia.
Qed.
(* /FOLD *)

(** Finally, [ST ++ T] extends [ST], and [extends] is reflexive. *)

Lemma extends_app : forall ST T,
  extends (ST ++ T) ST.
(* FOLD *)
Proof.
  induction ST; intros T.
  auto.
  simpl. auto.
Qed.
(* /FOLD *)

Lemma extends_refl : forall ST,
  extends ST ST.
(* FOLD *)
Proof.
  induction ST; auto.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* ################################### *)
(** ** Preservation, Finally *)

(** We can now give the final, correct statement of the type
    preservation property: *)

Definition preservation_theorem := forall ST t t' T st st',
  <{ empty / ST |-- t \in T }> ->
  store_well_typed ST st ->
  t / st --> t' / st' ->
  exists ST',
     extends ST' ST /\
     <{ empty / ST' |-- t' \in T }> /\
     store_well_typed ST' st'.

(** FULL: Note that the preservation theorem merely asserts that there
    is _some_ store typing [ST'] extending [ST] (i.e., agreeing with
    [ST] on the values of all the old locations) such that the new
    term [t'] is well typed with respect to [ST']; it does not tell us
    exactly what [ST'] is.  It is intuitively clear, of course, that
    [ST'] is either [ST] or else exactly [ST ++ T1::nil], where [T1]
    is the type of the value [v1] in the extended store [st ++
    v1::nil], but stating this explicitly would complicate the
    statement of the theorem without making it any more useful: the
    weaker version above is already in the right form (because its
    conclusion implies its hypothesis) to "turn the crank" repeatedly
    and conclude that every _sequence_ of reduction steps preserves
    well-typedness.  Combining this with the progress property, we
    obtain the usual guarantee that "well-typed programs never go
    wrong."

    In order to prove this, we'll need a few lemmas, as usual. *)
(** TERSE: This gives us just what we need to "turn the
    crank" when applying the theorem to multi-step reduction
    sequences. *)

(* TERSE: HIDEFROMHTML *)
(* ################################### *)
(** ** Substitution Lemma *)

(** TERSE: To prove preservation, we need to re-develop the rest of
    the machinery that we saw for the pure STLC (plus a couple of new
    things about store typings and extension)... *)
(** FULL: First, we need an easy extension of the standard substitution
    lemma, along with the same machinery about context invariance that
    we used in the proof of the substitution lemma for the STLC. *)

Lemma weakening : forall Gamma Gamma' ST t T,
     includedin Gamma Gamma' ->
     <{ Gamma / ST |-- t \in T }> ->
     <{ Gamma' / ST |-- t \in T }>.
Proof.
  intros Gamma Gamma' ST t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Lemma weakening_empty : forall Gamma ST t T,
     <{ empty / ST |-- t \in T }> ->
     <{ Gamma / ST |-- t \in T }>.
Proof.
  intros Gamma ST t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma ST x U t v T,
  <{ x |-> U; Gamma / ST |-- t \in T }> ->
  <{ empty / ST |-- v \in U }>  ->
  <{ Gamma / ST |-- [x:=v]t \in T }>.
(* FOLD *)
Proof.
  intros Gamma ST x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (String.eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
(* INSTRUCTORS: Inconsistent between 8.12.0 and 8.12.1!
   rename t0 into T. *)
    rename s into y.
    destruct (String.eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* ################################### *)
(** ** Assignment Preserves Store Typing *)

(** Next, we must show that replacing the contents of a cell in the
    store with a new value of appropriate type does not change the
    overall type of the store.  (This is needed for the [ST_Assign]
    rule.) *)

Lemma assign_pres_store_typing : forall ST st l t,
  l < length st ->
  store_well_typed ST st ->
  <{ empty / ST |-- t \in $(store_Tlookup l ST) }> ->
  store_well_typed ST (replace l t st).
(* FOLD *)
Proof with auto.
  intros ST st l t Hlen HST Ht.
  inversion HST; subst.
  split. rewrite length_replace...
  intros l' Hl'.
  destruct (l' =? l) eqn: Heqll'.
  - (* l' = l *)
    apply eqb_eq in Heqll'; subst.
    rewrite lookup_replace_eq...
  - (* l' <> l *)
    apply eqb_neq in Heqll'.
    rewrite lookup_replace_neq...
    rewrite length_replace in Hl'.
    apply H0...
Qed.
(* /FOLD *)

(* ######################################## *)
(** ** Weakening for Stores *)

(** Finally, we need a lemma on store typings, stating that, if a
    store typing is extended with a new location, the extended one
    still allows us to assign the same types to the same terms as the
    original. *)

Lemma store_weakening : forall Gamma ST ST' t T,
  extends ST' ST ->
  <{ Gamma / ST |-- t \in T }> ->
  <{ Gamma / ST' |-- t \in T }>.
(* FOLD *)
Proof with eauto.
  intros. induction H0; eauto.
  - (* T_Loc *)
    rewrite <- (extends_lookup _ _ ST')...
    apply T_Loc.
    eapply length_extends...
Qed.
(* /FOLD *)

(** TERSE: *** *)

(** We can use the [store_weakening] lemma to prove that if a store is
    well typed with respect to a store typing, then the store extended
    with a new term [t] will still be well typed with respect to the
    store typing extended with [t]'s type. *)

Lemma store_well_typed_app : forall ST st t1 T1,
  store_well_typed ST st ->
  <{ empty / ST |-- t1 \in T1 }> ->
  store_well_typed (ST ++ T1::nil) (st ++ t1::nil).
(* FOLD *)
Proof with auto.
  intros.
  unfold store_well_typed in *.
  destruct H as [Hlen Hmatch].
  rewrite app_length, add_comm. simpl.
  rewrite app_length, add_comm. simpl.
  split...
  - (* types match. *)
    intros l Hl.
    unfold store_lookup, store_Tlookup.
    apply le_lt_eq_dec in Hl; destruct Hl as [Hlt | Heq].
    + (* l < length st *)
      apply <-Nat.succ_lt_mono in Hlt.
      rewrite !app_nth1...
      * apply store_weakening with ST. apply extends_app.
        apply Hmatch...
      * rewrite Hlen...
    + (* l = length st *)
      injection Heq as Heq; subst.
      rewrite app_nth2; try lia.
      rewrite <- Hlen.
      rewrite sub_diag. simpl.
      apply store_weakening with ST...
      { apply extends_app. }
      rewrite app_nth2; [|lia].
      rewrite sub_diag. simpl. assumption.
Qed.
(* /FOLD *)

(* ################################### *)
(** ** Preservation! *)

(** Now that we've got everything set up right, the proof of
    preservation is actually quite straightforward.  *)

(* TERSE: HIDEFROMHTML *)
(** Begin with one technical lemma: *)

Lemma nth_eq_last : forall A (l:list A) x d,
  nth (length l) (l ++ x::nil) d = x.
(* FOLD *)
Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ].
Qed.
(* /FOLD *)

(** And here, at last, is the preservation theorem: *)

Theorem preservation : forall ST t t' T st st',
  <{ empty / ST |-- t \in T }> ->
  store_well_typed ST st ->
  t / st --> t' / st' ->
  exists ST',
     extends ST' ST /\
     <{ empty / ST' |-- t' \in T }> /\
     store_well_typed ST' st'.
(* FOLD *)
Proof with eauto using store_weakening, extends_refl.
  remember empty as Gamma.
  intros ST t t' T st st' Ht.
  generalize dependent t'.
  induction Ht; intros t' HST Hstep;
    subst; try solve_by_invert; inversion Hstep; subst;
    try (eauto using store_weakening, extends_refl).
  (* T_App *)
  - (* ST_AppAbs *) exists ST.
    inversion Ht1; subst.
    split; try split... eapply substitution_preserves_typing...
  - (* ST_App1 *)
    eapply IHHt1 in H0...
    destruct H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* ST_App2 *)
    eapply IHHt2 in H5...
    destruct H5 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* T_Succ *)
    + (* ST_Succ *)
      eapply IHHt in H0...
      destruct H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  - (* T_Pred *)
    + (* ST_Pred *)
      eapply IHHt in H0...
      destruct H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  (* T_Mult *)
  - (* ST_Mult1 *)
    eapply IHHt1 in H0...
    destruct H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* ST_Mult2 *)
    eapply IHHt2 in H5...
    destruct H5 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* T_If0 *)
    + (* ST_If0_1 *)
      eapply IHHt1 in H0...
      destruct H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'. split...
  (* T_Ref *)
  - (* ST_RefValue *)
    exists (ST ++ T1::nil).
    inversion HST; subst.
    split.
    { apply extends_app. }
    split.
    { replace <{{ Ref T1 }}>
        with <{{ Ref $(store_Tlookup (length st) (ST ++ T1::nil)) }}>.
      { apply T_Loc.
        rewrite <- H. rewrite app_length, add_comm. simpl. lia. }
      unfold store_Tlookup. rewrite <- H. rewrite nth_eq_last.
      reflexivity. }
    apply store_well_typed_app; assumption.
  - (* ST_Ref *)
    eapply IHHt in H0...
    destruct H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  (* T_Deref *)
  - (* ST_DerefLoc *)
    exists ST. split; try split...
    destruct HST as [_ Hsty].
    replace T1 with (store_Tlookup l ST).
    apply Hsty...
    inversion Ht; subst...
  - (* ST_Deref *)
    eapply IHHt in H0...
    destruct H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  (* T_Assign *)
  - (* ST_Assign *)
    exists ST. split; try split...
    eapply assign_pres_store_typing...
    inversion Ht1; subst...
  - (* ST_Assign1 *)
    eapply IHHt1 in H0...
    destruct H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* ST_Assign2 *)
    eapply IHHt2 in H5...
    destruct H5 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* TERSE: HIDEFROMHTML *)
(* EX3M? (preservation_informal) *)
(** Write a careful informal proof of the preservation theorem,
    concentrating on the [T_App], [T_Deref], [T_Assign], and [T_Ref]
    cases.

(* SOLUTION *)
    _Proof_: By induction on a derivation of [empty / [] |-- t : T].

    - If the last rule in the derivation is [T_App], then [t = t1 t2]
      for some [t1] and [t2] and [T = T12], with [empty / ST |-- t1 :
      T11->T12] and [empty / ST |-- t1 : T11].  There are three cases to
      consider, one for each rule that could have been used to show
      that [t1 t2] takes a step to [t'].

        - Suppose [t1 t2] takes a step by [ST_App1], with [t1]
          stepping to [t1'] and new store [st'].  Then by the IH there
          is some store typing [ST'] such that [ST'] extends [ST],
          [st'] is well typed with respect to [ST'], and [empty / ST'
          |-- t1' : T11->T12].  We also know [empty / ST' |-- t2 : T11]
          by the [store_weakening] lemma.  Hence, [empty / ST' |-- t1'
          t2] by [T_App].

        - The [ST_App2] case is similar.

        - Suppose [t1 t2] takes a step by [ST_AppAbs].  Then [t1 =
          \x:T11,t12] and [t1 t2] steps to [[x:=t2]t12]; the
          desired result now follows from the substitution lemma,
          taking [ST' = ST].

    - If the last rule in the derivation is [T_Ref], then [t = ref t1]
      for some [t1] and [empty / ST |-- t1 : T1] for some [T1], with [T
      = Ref T1].  There are two cases to consider, one for each rule
      that could have been used to show that [ref t1] takes a step to
      [t'].

        - Suppose [ref t1] takes a step by [ST_Ref], with [t1]
          stepping to [t1'] and new store [st'].  Then by the IH there
          is some store typing [ST'] such that [ST'] extends [ST],
          [st'] is well typed with respect to [ST'], and [empty / ST'
          |-- t1' : T1].  Hence, [empty / ST' |-- ref t1' : Ref T1] by
          [T_Ref].

        - Suppose [ref t1] takes a step by [ST_RefValue].  Then [t1]
          is a value, [st' = st ++ t1::nil], and [t'] is the length of
          [st] -- i.e., the location of [t1] in [st'].  If we choose
          [ST' = ST ++ T1::nil], we obtain
             - [ST'] extends [ST] by construction
             - [st'] is well typed with respect to [ST'] because [st]
               is well typed with respect to [ST] and the last
               element, [t1], has type [T1] under [ST],
               hence also under [ST'] by the store
               weakening lemma
             - [empty / ST' |-- l : Ref T1] by [T_Loc]
          as required.

    - If the last rule in the derivation is [T_Deref], then [t = !t1]
      for some [t1] and [empty / ST |-- t1 : Ref T].  There are two
      cases to consider, one for each rule that could have been used
      to show that [!t1] takes a step to [t'].

        - Suppose [!t1] takes a step by [ST_Deref], with [t1] stepping
          to [t1'] and new store [st'].  Then by the IH there is some
          store typing [ST'] such that [ST'] extends [ST], [st'] is
          well typed with respect to [ST'], and [empty / ST' |-- t1' :
          Ref T].  Hence, [empty / ST' |-- !t1' : T] by [T_Deref].

        - Suppose [ref t1] takes a step by [ST_DerefLoc].  Then [t1]
          is some location [l] and [t'] is the contents of [st] at
          location [l].  Moreover, the typing rule used to derive
          [empty / ST |-- l : Ref T] must be [T_Loc], so the contents of
          [ST] at location [l] is [T].  Now, since [st] is well typed
          with respect to [ST], we know that [empty / ST |-- t' : T], as
          required.

    - If the last rule in the derivation is [T_Assign], then [t = t1
      := t2] for some [t1] and [t2], with [empty / ST |-- t1 : Ref T2]
      and [empty / ST |-- t2 : T2] for some [T2]; moreover, [T = Unit].
      There are now three cases to consider, one for each rule that
      could have been used to show that [t1 := t2] takes a step to
      [t'].

        - The cases where [t1 := t2] takes a step by either
          [ST_Assign1] or [ST_Assign2] are similar to the congruence
          rule cases above.

        - Suppose [t1 := t2] takes a step by [ST_Assign].  Then [t1]
          is some location [l], [t2] is some value, [t'] is [unit],
          and [st'] is formed from [st] by updating the contents of
          location [l] with [t2].

          Moreover, the typing rule used to derive [empty / ST |-- l :
          Ref T2] must be [T_Loc], so the contents of [ST] at location
          [l] is [T2].  Now, [empty / ST |-- unit : Unit] by [T_Unit].
          Moreover, since [st] is well typed with respect to [ST] and
          we know [empty / ST |-- t2 : T2], we know that [st'] is well
          typed with respect to [ST] by lemma
          [assign_pres_store_typing].  So we can take [ST' = ST] and
          finish this case.

    - (Other cases elided...)

(* /SOLUTION *)
*)

(* GRADE_MANUAL 3: preservation_informal *)
(** [] *)
(* TERSE: /HIDEFROMHTML *)

(* ################################### *)
(** ** Progress *)

(** As we've said, progress for this system is pretty easy to prove;
    the proof is very similar to the proof of progress for the STLC,
    with a few new cases for the new syntactic constructs. *)

Theorem progress : forall ST t T st,
  <{ empty / ST |-- t \in T }> ->
  store_well_typed ST st ->
  (value t \/ exists t' st', t / st --> t' / st').
(* FOLD *)
Proof with eauto.
  intros ST t T st Ht HST. remember empty as Gamma.
  induction Ht; subst; try solve_by_invert...
  - (* T_App *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve_by_invert.
      destruct IHHt2 as [Ht2p | Ht2p]...
      * (* t2 steps *)
        destruct Ht2p as [t2' [st' Hstep]].
        exists <{ (\ x0 : T0, t0) t2' }>, st'...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ t1' t2 }>, st'...
  - (* T_Succ *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve [ inversion Ht ].
      * (* t1 is a const *)
        exists <{ $(S n) }>, st...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ succ t1' }>, st'...
  - (* T_Pred *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve [inversion Ht ].
      * (* t1 is a const *)
        exists <{ $(n - 1) }>, st...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ pred t1' }>, st'...
  - (* T_Mult *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve [inversion Ht1].
      destruct IHHt2 as [Ht2p | Ht2p]...
      * (* t2 is a value *)
        inversion Ht2p; subst; try solve [inversion Ht2].
        exists <{ $(n * n0) }>, st...
      * (* t2 steps *)
        destruct Ht2p as [t2' [st' Hstep]].
        exists <{ n * t2' }>, st'...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ t1' * t2 }>, st'...
  - (* T_If0 *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve [inversion Ht1].
      destruct n.
      * (* n = 0 *) exists t2, st...
      * (* n = S n' *) exists t3, st...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ if0 t1' then t2 else t3 }>, st'...
  - (* T_Ref *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ref t1'}>, st'...
  - (* T_Deref *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve_by_invert.
      eexists. eexists. apply ST_DerefLoc...
      inversion Ht; subst. inversion HST; subst.
      rewrite <- H...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ ! t1' }>, st'...
  - (* T_Assign *)
    right. destruct IHHt1 as [Ht1p|Ht1p]...
    + (* t1 is a value *)
      destruct IHHt2 as [Ht2p|Ht2p]...
      * (* t2 is a value *)
        inversion Ht1p; subst; try solve_by_invert.
        eexists. eexists. apply ST_Assign...
        inversion HST; subst. inversion Ht1; subst.
        rewrite H in H4...
      * (* t2 steps *)
        destruct Ht2p as [t2' [st' Hstep]].
        exists <{ t1 := t2' }>, st'...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ t1' := t2 }>, st'...
Qed.
(* /FOLD *)

(* ################################### *)
(** * References and Nontermination *)

(** An important fact about the STLC (proved in chapter \CHAP{Norm})
    is that it is is _normalizing_ -- that is, every well-typed term
    can be reduced to a value in a finite number of steps.

    What about STLC + references?  Surprisingly, adding references
    causes us to lose the normalization property: there exist
    well-typed terms in the STLC + references which can continue to
    reduce forever, without ever reaching a normal form! *)

(** TERSE: *** *)

(** How can we construct such a term?  The main idea is to make a
    function which calls itself.  We first make a function which calls
    another function stored in a reference cell; the trick is that we
    then smuggle in a reference to itself!
<<
   (\r:Ref (Unit -> Unit),
        r := (\x:Unit,(!r) unit); (!r) unit)
   (ref (\x:Unit,unit))
>>
*)

(** FULL: First, [ref (\x:Unit,unit)] creates a reference to a cell of
    type [Unit -> Unit].  We then pass this reference as the argument
    to a function which binds it to the name [r], and assigns to it
    the function [\x:Unit,(!r) unit] -- that is, the function which
    ignores its argument and calls the function stored in [r] on the
    argument [unit]; but of course, that function is itself!  To start
    the divergent loop, we execute the function stored in the cell by
    evaluating [(!r) unit].

   Here is the divergent term in Rocq: *)
(* SOONER: Anton suggests that the program given above would be easier to
   understand for the reader if it was first presented in the form
   [let r = ref (fun (x : unit) -> ()) in
    r := (fun (x : unit) -> !r ());
    !r ()]
   or even
   [let r = ref (fun (_ : unit) -> ()) in
    r := (fun (_ : unit) -> !r ());
    !r ()] *)

(* TERSE: HIDEFROMHTML *)
Module ExampleVariables.

(* NOTATION: LATER: Urg: Here they are definitions, not notations.  Try to make
   this consistent with MoreStlc, Stlc, etc. *)

Open Scope string_scope.

Definition x := "x".
Definition y := "y".
Definition r := "r".
Definition s := "s".

End ExampleVariables.

Module RefsAndNontermination.
Import ExampleVariables.

Definition loop_fun :=
  <{ \x : Unit, (!r) unit }>.

Definition loop :=
  <{ (\r : Ref (Unit -> Unit),
        (( r := loop_fun );
        ( (! r) unit ) ))
     (ref (\x : Unit, unit)) }> .
(** This term is well typed: *)

Import ListNotations.

Lemma loop_typeable : exists T, <{ empty / [] |-- loop \in T }>.
(* FOLD *)
Proof with eauto.
  eexists. unfold loop. unfold loop_fun.
  eapply T_App...
  eapply T_Abs...
  eapply T_App...
    eapply T_Abs. eapply T_App. eapply T_Deref. eapply T_Var.
    rewrite update_neq; [|intros; discriminate].
    rewrite update_eq. reflexivity. auto.
  eapply T_Assign.
    eapply T_Var. rewrite update_eq. reflexivity.
  eapply T_Abs.
    eapply T_App...
      eapply T_Deref. eapply T_Var. reflexivity.
Qed.
(* /FOLD *)

(** To show formally that the term diverges, we first define the
    [step_closure] of the single-step reduction relation, written
    [-->+].  This is just like the reflexive step closure of
    single-step reduction (which we're been writing [-->*]), except
    that it is not reflexive: [t -->+ t'] means that [t] can reach
    [t'] by _one or more_ steps of reduction. *)

Inductive step_closure {X:Type} (R: relation X) : X -> X -> Prop :=
  | sc_one  : forall (x y : X),
                R x y -> step_closure R x y
  | sc_step : forall (x y z : X),
                R x y ->
                step_closure R y z ->
                step_closure R x z.

Definition multistep1 := (step_closure step).
Notation "t1 '/' st '-->+' t2 '/' st'" :=
        (multistep1 (t1,st) (t2,st'))
        (at level 40, st at level 39, t2 at level 39).

(** Now, we can show that the expression [loop] reduces to the
    expression [!(loc 0) unit] and the size-one store
    [[r:=(loc 0)]loop_fun]. *)

(* LATER: Maybe this one belongs in MoreStlc.v? *)
(** As a convenience, we introduce a slight variant of the [normalize]
    tactic, called [reduce], which tries solving the goal with
    [multi_refl] at each step, instead of waiting until the goal can't
    be reduced any more. Of course, the whole point is that [loop]
    doesn't normalize, so the old [normalize] tactic would just go
    into an infinite loop reducing it forever! *)

Ltac print_goal := match goal with |- ?x => idtac x end.
Ltac reduce :=
    repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | compute];
            try solve [apply multi_refl]).

(** Next, we use [reduce] to show that [loop] steps to
    [!(loc 0) unit], starting from the empty store. *)

Lemma loop_steps_to_loop_fun :
  loop / nil -->*
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil.
Proof.
  unfold loop.
  reduce.
Qed.

(** Finally, we show that the latter expression reduces in
    two steps to itself! *)

Lemma loop_fun_step_self :
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil -->+
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil.
(* FOLD *)
Proof with eauto.
  unfold loop_fun; simpl.
  eapply sc_step. apply ST_App1...
  eapply sc_one. compute. apply ST_AppAbs...
Qed.
(* /FOLD *)

(* EX4 (factorial_ref) *)
(* GRADE_THEOREM 3: factorial *)
(* GRADE_THEOREM 3: factorial_type *)
(** Use the above ideas to implement a factorial function in STLC with
    references.  (There is no need to prove formally that it really
    behaves like the factorial.  Just uncomment the example below to make
    sure it gives the correct result when applied to the argument
    [4].) *)
(* SOONER: a bit more explanation here?  (YES!) *)

Definition factorial : tm
  (* ADMITDEF *) :=
<{
  (\r : (Ref (Nat -> Nat) ),
        (r := (\ x : Nat, if0 x then 1 else (x * ( (!r) (pred x) ) ))); !r  )
  (ref (\x : Nat, x))
  }>.
(* /ADMITDEF *)

Lemma factorial_type : <{ empty / nil |-- factorial \in (Nat -> Nat) }>.
Proof with eauto.
  (* ADMITTED *)
  unfold factorial.
  eapply T_App...
  eapply T_Abs...
  eapply T_App...
  eapply T_Assign...
  eapply T_Abs...
  eapply T_If0...
  eapply T_Mult...
  eapply T_App...
  eapply T_Deref...
Qed.
(* /ADMITTED *)

(** If your definition is correct, you should be able to just
    uncomment the example below; the proof should be fully
    automatic using the [reduce] tactic. *)

(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
Lemma factorial_4 : exists st,
  <{ factorial 4 }> / nil -->* tm_const 24 / st.
Proof.
  eexists. unfold factorial. reduce.
Qed.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(** [] *)

(* ################################### *)
(** * Additional Exercises *)

(* EX5? (garbage_collector) *)
(** Challenge problem: modify our formalization to include an account
    of garbage collection, and prove that it satisfies whatever nice
    properties you can think to prove about it. *)
(** [] *)

End RefsAndNontermination.
End STLCRef.
(* TERSE: /HIDEFROMHTML *)
