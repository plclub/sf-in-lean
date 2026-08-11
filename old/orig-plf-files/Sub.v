(** * Sub: Subtyping *)

(* SOONER: Make sure that <{...}> doesn't show up in informal contexts
   in this or later chapters. *)
(* SOONER: SAZ 22: We have different meanings for base types across
   the same file. In one version base types include Top, Bool, and
   Nat. In the other version it doesn't. This is confusing
   students. Maybe opt with only introducing one version or providing
   a new name for either version. *)
(* LATER: Would be nice to add some text like "Formally:" between
   informal and formal proofs. *)
(* LATER: The Penn 2010 final exam (question 9) has a nice
   subtype-tree-drawing exercise. Also (questions 10 and 11) some nice
   problems about combining subtyping and references.  Would need to
   be optional, of course.  (It would be nice, sometime, to add at
   least a little informal discussion of extensions and variants --
   e.g., subtyping references and arrays.) *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(* ###################################################### *)
(* TERSE: HIDEFROMHTML *)
(** * Concepts *)
(* TERSE: /HIDEFROMHTML *)

(** FULL: We now turn to _subtyping_, a key feature of -- in
    particular -- object-oriented programming languages. *)

(* ###################################################### *)
(** ** A Motivating Example *)

(** Suppose we are writing a program involving two record types
    defined as follows:
<<
      Person  = {name:String, age:Nat}
      Student = {name:String, age:Nat, gpa:Nat}
>>
*)

(** FULL: In the simply typed lamdba-calculus with records, the term
<<
      (\r:Person, (r.age)+1) {name="Pat",age=21,gpa=1}
>>
   is not typable, since it applies a function that wants a two-field
   record to an argument that actually provides three fields, while the
   [T_App] rule demands that the domain type of the function being
   applied must match the type of the argument precisely.

   But this is silly: we're passing the function a _better_ argument
   than it needs!  The only thing the body of the function can
   possibly do with its record argument [r] is project the field [age]
   from it: nothing else is allowed by the type, and the presence or
   absence of an extra [gpa] field makes no difference at all.  So,
   intuitively, it seems that this function should be applicable to
   any record value that has at least an [age] field.

   More generally, a record with more fields is "at least as good in
   any context" as one with just a subset of these fields, in the
   sense that any value belonging to the longer record type can be
   used _safely_ in any context expecting the shorter record type.  If
   the context expects something with the shorter type but we actually
   give it something with the longer type, nothing bad will
   happen (formally, the program will not get stuck).

   The principle at work here is called _subtyping_.  We say that "[S]
   is a subtype of [T]", written [S <: T], if a value of type [S] can
   safely be used in any context where a value of type [T] is
   expected.  The idea of subtyping applies not only to records, but
   to all of the type constructors in the language -- functions,
   pairs, etc. *)
(** TERSE: _Problem_: In the pure STLC with records, the following term is not
    typable:
<<
    (\r:Person, (r.age)+1) {name="Pat",age=21,gpa=1}
>>
    This is a shame. *)

(** TERSE: *** *)
(** TERSE: _Idea_: Introduce _subtyping_, formalizing the observation that
    "some types are better than others." *)

(** Safe substitution principle:

       - [S] is a subtype of [T], written [S <: T], if a value of type
         [S] can safely be used in any context where a value of type
         [T] is expected.
*)

(** ** Subtyping and Object-Oriented Languages *)

(** FULL: Subtyping plays a fundamental role in many programming
    languages -- in particular, it is central to the design of
    object-oriented languages and their libraries.

    An _object_ in Java, C[#], etc. can be thought of as a record,
    some of whose fields are functions ("methods") and some of whose
    fields are data values ("fields" or "instance variables").
    Invoking a method [m] of an object [o] on some arguments [a1..an]
    roughly consists of projecting out the [m] field of [o] and
    applying it to [a1..an].

    The type of an object is called a _class_ -- or, in some
    languages, an _interface_.  It describes which methods and which
    data fields the object offers.  Classes and interfaces are related
    by the _subclass_ and _subinterface_ relations.  An object
    belonging to a subclass (or subinterface) is required to provide
    all the methods and fields of one belonging to a superclass (or
    superinterface), plus possibly some more.

    The fact that an object from a subclass can be used in place of
    one from a superclass provides a degree of flexibility that is
    extremely handy for organizing complex libraries.  For example, a
    GUI toolkit like Java's Swing framework might define an abstract
    interface [Component] that collects together the common fields and
    methods of all objects having a graphical representation that can
    be displayed on the screen and interact with the user, such as the
    buttons, checkboxes, and scrollbars of a typical GUI.  A method
    that relies only on this common interface can now be applied to
    any of these objects.

    Of course, real object-oriented languages include many other
    features besides these.  For example, fields can be updated.
    Fields and methods can be declared "private".  Classes can give
    _initializers_ that are used when constructing objects.  Code in
    subclasses can cooperate with code in superclasses via
    _inheritance_.  Classes can have static methods and fields.  Etc.,
    etc.

    To keep things simple here, we won't deal with any of these
    issues -- in fact, we won't even talk any more about objects or
    classes.  (There is a lot of discussion in \CITE{Pierce 2002}, if
    you are interested.)  Instead, we'll study the core concepts
    behind the subclass / subinterface relation in the simplified
    setting of the STLC. *)
(** TERSE: Subtyping plays a fundamental role in OO programming
    languages.

    Roughly, an _object_ can be thought of as a record of
    functions ("methods") and data values ("fields" or "instance
    variables").

       - Invoking a method [m] of an object [o] on some arguments
         [a1..an] consists of projecting out the [m] field of [o] and
         applying it to [a1..an].

    The type of an object is a _class_ (or an _interface_).

    Classes are related by the _subclass_ relation.

       - An object belonging to a subclass must provide all the
         methods and fields of one belonging to a superclass, plus
         possibly some more.

       - Thus a subclass object can be used anywhere a superclass
         object is expected.

       - Very handy for organizing large libraries *)
(** TERSE: *** *)
(** TERSE: Of course, real OO languages have lots of other features...
       - mutable fields
       - "private" and other visibility modifiers
       - method inheritance
       - static components
       - etc., etc.

    We'll ignore all these and focus on core mechanisms. *)

(** ** The Subsumption Rule *)

(** Our goal for this chapter is to add subtyping to the simply typed
    lambda-calculus (with some of the basic extensions from [MoreStlc]).
    This involves two steps:

      - Defining a binary _subtype relation_ between types.

      - Enriching the typing relation to take subtyping into account.

    The second step is actually very simple.  We add just a single rule
    to the typing relation: the so-called _rule of subsumption_:
[[[
                         Gamma |-- t1 \in T1     T1 <: T2
                         --------------------------------           (T_Sub)
                               Gamma |-- t1 \in T2
]]]
    This rule says, intuitively, that it is OK to "forget" some of
    what we know about a term. *)

(** FULL: For example, we may know that [t1] is a record with two
    fields (e.g., [T1 = {x:A->A, y:B->B}]), but choose to forget about
    one of the fields ([T2 = {y:B->B}]) so that we can pass [t1] to a
    function that requires just a single-field record. *)

(** ** The Subtype Relation *)

(** The first step -- the definition of the relation [S <: T] -- is
    where all the action is.  Let's look at each of the clauses of its
    definition.  *)

(** *** Structural Rules *)

(** To start off, we impose two "structural rules" that are
    independent of any particular type constructor: a rule of
    _transitivity_, which says intuitively that, if [S] is
    better (richer, safer) than [U] and [U] is better than [T],
    then [S] is better than [T]...
[[[
                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T
]]]
    ... and a rule of _reflexivity_, since certainly any type [T] is
    as good as itself:
[[[
                                   ------                              (S_Refl)
                                   T <: T
]]]
*)

(** *** Products *)

(** Now we consider the individual type constructors, one by one,
    beginning with product types.  We consider one pair to be a subtype
    of another if each of its components is.
[[[
                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                             S1 * S2 <: T1 * T2
]]]
*)

(** *** Arrows *)
(* HIDE: Sampsa: I would prefer changing the variable names in `S_Arrow`,
    because I think the contravariance should be
    apparent in the conclusion, not in the hypotheses.
       ```
       S1 <: T1    S2 <: T2
       --------------------  (S_Arrow)
       T1 -> S2 <: S1 -> T2
       ```
    BCP 11/18: I see the value in this suggestion, but the current naming
    is the standard one in the literature, and it's consistent with our
    other naming conventions, so I'm not too inclined to change it. *)

(* FULL *)
(** The subtyping rule for arrows is a little less intuitive.
    Suppose we have functions [f] and [g] with these types:
[[
       f : C -> Student
       g : (C->Person) -> D
]]
    That is, [f] is a function that yields a record of type [Student],
    and [g] is a (higher-order) function that expects its argument to be
    a function yielding a record of type [Person].  Also suppose that
    [Student] is a subtype of [Person].  Then the application [g f] is
    safe even though their types do not match up precisely, because
    the only thing [g] can do with [f] is to apply it to some
    argument (of type [C]); the result will actually be a [Student],
    while [g] will be expecting a [Person], but this is safe because
    the only thing [g] can then do is to project out the two fields
    that it knows about ([name] and [age]), and these will certainly
    be among the fields that are present.

    This example suggests that the subtyping rule for arrow types
    should say that two arrow types are in the subtype relation if
    their results are:
[[[
                                  S2 <: T2
                              ----------------                     (S_Arrow_Co)
                            S1 -> S2 <: S1 -> T2
]]]

    We can generalize this to allow the arguments of the two arrow
    types to be in the subtype relation as well:
[[[
                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2
]]]
    But notice that the argument types are subtypes "the other way round":
    in order to conclude that [S1->S2] to be a subtype of [T1->T2], it
    must be the case that [T1] is a subtype of [S1].  The arrow
    constructor is said to be _contravariant_ in its first argument
    and _covariant_ in its second.

    Here is an example that illustrates this:
[[
       f : Person -> C
       g : (Student -> C) -> D
]]
    The application [g f] is safe, because the only thing the body of
    [g] can do with [f] is to apply it to some argument of type
    [Student].  Since [f] requires records having (at least) the
    fields of a [Person], this will always work. So [Person -> C] is a
    subtype of [Student -> C] since [Student] is a subtype of
    [Person].

    The intuition is that, if we have a function [f] of type [S1->S2],
    then we know that [f] accepts elements of type [S1]; clearly, [f]
    will also accept elements of any subtype [T1] of [S1]. The type of
    [f] also tells us that it returns elements of type [S2]; we can
    also view these results belonging to any supertype [T2] of
    [S2]. That is, any function [f] of type [S1->S2] can also be
    viewed as having type [T1->T2]. *)
(* /FULL *)
(* TERSE *)
(** Suppose we have functions [f] and [g] with these types:
[[
       f : C -> Student
       g : (C->Person) -> D
]]
    Is it safe to allow the application [g f]?

    Yes.

    So we want:
[[
      C->Student  <:  C->Person
]]
    I.e., arrow is _covariant_ in its right-hand argument. *)

(** TERSE: *** *)
(** Now suppose we have:
[[
       f : Person -> C
       g : (Student->C) -> D
]]
    Is it safe to allow the application [g f]?

    Again yes.

    So we want:
[[
      Person -> C  <:  Student -> C
]]
    I.e., arrow is _contravariant_ in its left-hand argument. *)

(** TERSE: *** *)
(** Putting these together...
[[[
                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2
]]]
*)
(* /TERSE *)

(* QUIZ *)
(** Suppose we have  [S <: T] and [U <: V].  Which of the following
    subtyping assertions is _false_?

    (A) [S*U <: T*V]

    (B) [T->U <: S->U]

    (C) [(S->U) -> (S*V)  <:  (S->U) -> (T*U)]

    (D) [(T*U) -> V  <:  (S*U) -> V]

    (E) [S->U <: S->V]
*)
(* /QUIZ *)

(* QUIZ *)
(** Suppose again that we have [S <: T] and [U <: V].  Which of the
    following is incorrect?

    (A) [(T->T)*U  <: (S->T)*V]

    (B) [T->U <: S->V]

    (C) [(S->U) -> (S->V)  <:  (T->U) -> (T->V)]

    (D) [(S->V) -> V  <:  (T->U) -> V]

    (E) [S -> (V->U) <: S -> (U->U)]
*)
(* /QUIZ *)

(** *** Records *)

(* LATER: Add more text to FULL version, and make a separate TERSE
   version. *)
(** What about subtyping for record types? *)

(** TERSE: *** *)
(** The basic intuition is that it is always safe to use a "bigger"
    record in place of a "smaller" one.  That is, given a record type,
    adding extra fields will always result in a subtype.  If some code
    is expecting a record with fields [x] and [y], it is perfectly safe
    for it to receive a record with fields [x], [y], and [z]; the [z]
    field will simply be ignored.  For example,
[[
    {name:String, age:Nat, gpa:Nat} <: {name:String, age:Nat}
    {name:String, age:Nat} <: {name:String}
    {name:String} <: {}
]]
    This is known as "width subtyping" for records. *)

(** TERSE: *** *)
(** We can also create a subtype of a record type by replacing the type
    of one of its fields with a subtype.  If some code is expecting a
    record with a field [x] of type [T], it will be happy with a record
    having a field [x] of type [S] as long as [S] is a subtype of
    [T]. For example,
[[
    {x:Student} <: {x:Person}
]]
    This is known as "depth subtyping". *)

(** TERSE: *** *)
(** Finally, although the fields of a record type are written in a
    particular order, the order does not really matter. For example,
[[
    {name:String,age:Nat} <: {age:Nat,name:String}
]]
    This is known as "permutation subtyping". *)

(** TERSE: *** *)
(** We _could_ formalize these requirements in a single subtyping rule
    for records as follows:
[[[
                        forall jk in j1..jn,
                    exists ip in i1..im, such that
                          jk=ip and Sp <: Tk
                  ----------------------------------                    (S_Rcd)
                  {i1:S1...im:Sm} <: {j1:T1...jn:Tn}
]]]
    That is, the record on the left should have all the field labels of
    the one on the right (and possibly more), while the types of the
    common fields should be in the subtype relation.

    However, this rule is rather heavy and hard to read, so it is often
    decomposed into three simpler rules, which can be combined using
    [S_Trans] to achieve all the same effects. *)

(** TERSE: *** *)
(** First, adding fields to the end of a record type gives a subtype:
[[[
                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}
]]]
    We can use [S_RcdWidth] to drop later fields of a multi-field
    record while keeping earlier fields, showing for example that
    [{age:Nat,name:String} <: {age:Nat}]. *)

(** TERSE: *** *)
(** Second, subtyping can be applied inside the components of a compound
    record type:
[[[
                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}
]]]
    For example, we can use [S_RcdDepth] and [S_RcdWidth] together to
    show that [{y:Student, x:Nat} <: {y:Person}]. *)

(** TERSE: *** *)
(** Third, subtyping can reorder fields.  For example, we
    want [{name:String, gpa:Nat, age:Nat} <: Person], but we
    haven't quite achieved this yet: using just [S_RcdDepth] and
    [S_RcdWidth] we can only drop fields from the _end_ of a record
    type.  So we add:
[[[
         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}
]]]
*)

(** TERSE: *** *)
(** It is worth noting that full-blown language designs may choose not
    to adopt all of these subtyping rules. For example, in Java:

    - Each class member (field or method) can be assigned a single
      index, adding new indices "on the right" as more members are
      added in subclasses (i.e., no permutation for classes).

    - A class may implement multiple interfaces -- so-called "multiple
      inheritance" of interfaces (i.e., permutation is allowed for
      interfaces).

    - In early versions of Java, a subclass could not change the
      argument or result types of a method of its superclass (i.e., no
      depth subtyping or no arrow subtyping, depending how you look at
      it). *)
(* HIDE: Sampsa points out that the last comment does not apply to
   more recent versions of Java.  E.g., this typechecks:

         import java.util.*;

         class Super {
          List<Object> method() {
            return null;
          }
         }

         class Sub extends Super {
          @Override
          ArrayList<Object> method() {
            return null;
          }
         }
*)

(* FULL *)
(* SOONER: As before, the exercise `arrow_sub_wrong` and many others
    are missing `FILL IN HERE`.  [BCP: But note that, in MoreStlc, the
    way I added these came out a bit awkward!] *)
(* EX2M! (arrow_sub_wrong) *)
(** Suppose we had incorrectly defined subtyping as covariant on both
    the right and the left of arrow types:
[[[
                            S1 <: T1    S2 <: T2
                            --------------------                (S_Arrow_wrong)
                            S1 -> S2 <: T1 -> T2
]]]
    Give a concrete example of functions [f] and [g] with the following
    types...
[[
       f : Student -> Nat
       g : (Person -> Nat) -> Nat
]]
    ... such that the application [g f] will get stuck during
    execution.  (Use informal syntax.  No need to prove formally that
    the application gets stuck.)
(* QUIETSOLUTION *)

    Answer:
[[
       f = \r:Student, r.gpa
       g = \f:Person->Nat, f {name="Alex",age=20}
]]
(* /QUIETSOLUTION *)
*)

(* GRADE_MANUAL 2: arrow_sub_wrong *)
(** [] *)
(* /FULL *)

(** *** Top *)

(** Finally, it is convenient to give the subtype relation a maximum
    element -- a type that lies above every other type and is
    inhabited by all (well-typed) values.  We do this by adding to the
    language one new type constant, called [Top], together with a
    subtyping rule that places it above every other type in the
    subtype relation:
[[[
                                   --------                             (S_Top)
                                   S <: Top
]]]
    The [Top] type is an analog of the [Object] type in Java and C##. *)

(* ############################################### *)
(** *** Summary *)

(** In summary, we form the STLC with subtyping by starting with the
    pure STLC (over some set of base types) and then...

    - adding a base type [Top],

    - adding the rule of subsumption
[[[
                         Gamma |-- t1 \in T1     T1 <: T2
                         --------------------------------            (T_Sub)
                               Gamma |-- t1 \in T2
]]]
      to the typing relation, and

    - defining a subtype relation as follows:
[[[
                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

                                   ------                              (S_Refl)
                                   T <: T

                                   --------                             (S_Top)
                                   S <: Top

                            S1 <: T1    S2 <: T2
                            --------------------                       (S_Prod)
                             S1 * S2 <: T1 * T2

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}
]]]
*)

(* QUIZ *)
(** Suppose we have  [S <: T] and [U <: V].  Which of the following
    subtyping assertions is false?

    (A) [S*U <: Top]

    (B) [{i1:S,i2:T}->U <: {i1:S,i2:T,i3:V}->U]

    (C) [(S->T) -> (Top -> Top)  <:  (S->T) -> Top]

    (D) [(Top -> Top) -> V  <:  Top -> V]

    (E) [S -> {i1:U,i2:V} <: S -> {i2:V,i1:U}]
*)
(* /QUIZ *)

(* QUIZ *)
(** How about these?

    (A) [ {i1:Top} <: Top]

    (B) [Top -> (Top -> Top)  <:  Top -> Top]

    (C) [{i1:T} -> {i1:T}  <:  {i1:T,i2:S} -> Top]

    (D) [{i1:T,i2:V,i3:V} <: {i1:S,i2:U} * {i3:V}]

    (E) [Top -> {i1:U,i2:V} <: {i1:S} -> {i2:V,i1:V}]
*)
(* /QUIZ *)

(* FULL *)
(* ############################################### *)
(** ** Exercises *)

(** The following "thought exercises" are repeated later as formal
    exercises. *)

(* EX1? (subtype_instances_tf_1) *)
(** Suppose we have types [S], [T], [U], and [V] with [S <: T]
    and [U <: V].  Which of the following subtyping assertions
    are then true?  Write _true_ or _false_ after each one.
    ([A], [B], and [C] here are base types like [Bool], [Nat], etc.)

    - [T->S <: T->S]
(* QUIETSOLUTION *)
      Answer: True
(* /QUIETSOLUTION *)
    - [Top->U <: S->Top]
(* QUIETSOLUTION *)
      Answer: True
(* /QUIETSOLUTION *)
    - [(C->C) -> (A*B)  <:  (C->C) -> (Top*B)]
(* QUIETSOLUTION *)
      Answer: True
(* /QUIETSOLUTION *)
    - [T->T->U <: S->S->V]
(* QUIETSOLUTION *)
      Answer: True
(* /QUIETSOLUTION *)
    - [(T->T)->U <: (S->S)->V]
(* QUIETSOLUTION *)
      Answer: False
(* /QUIETSOLUTION *)
    - [((T->S)->T)->U <: ((S->T)->S)->V]
(* QUIETSOLUTION *)
      Answer: True
(* /QUIETSOLUTION *)
    - [S*V <: T*U]
(* QUIETSOLUTION *)
      Answer: False
(* /QUIETSOLUTION *)
*)
(** [] *)

(* EX2M (subtype_order) *)
(** The following types happen to form a linear order with respect to subtyping:
    - [Top]
    - [Top -> Student]
    - [Student -> Person]
    - [Student -> Top]
    - [Person -> Student]

Write these types in order from the most specific to the most general.
(* QUIETSOLUTION *)

Answer: [Top->Student <: Person->Student <: Student->Person <: Student->Top <: Top]

(* /QUIETSOLUTION *)
Where does the type [Top->Top->Student] fit into this order?
That is, state how [Top -> (Top -> Student)] compares with each
of the five types above. It may be unrelated to some of them.  (* QUIETSOLUTION *)

Answer: It is less than [Student->Top] (and [Top]) and unrelated to the others.

(* /QUIETSOLUTION *)
*)

(* GRADE_MANUAL 2: subtype_order *)
(** [] *)
(* LATER: It's unfortunate that -> is so overloaded below.  Is there
   anything to do about it?  (Of course, the reason for the
   overloading is that they are deeply the same thing.  So probably
   there is *not* anything worth doing about it.  But the
   object/metalanguage pun is a bit confusing, potentially.) *)
(* LATER: We also need to double-check the typesetting of all the
   arrows and products everywhere in this file, in the HTML version!
   Spacing matters. *)

(* EX1M (subtype_instances_tf_2) *)
(** Which of the following statements are true?  Write _true_ or
    _false_ after each one.
[[
      forall S T,
          S <: T  ->
          S->S   <:  T->T(* QUIETSOLUTION *)
      Answer: False
(* /QUIETSOLUTION *)

      forall S,
           S <: A->A ->
           exists T,
              S = T->T  /\  T <: A(* QUIETSOLUTION *)
      Answer: False
(* /QUIETSOLUTION *)

      forall S T1 T2,
           (S <: T1 -> T2) ->
           exists S1 S2,
              S = S1 -> S2  /\  T1 <: S1  /\  S2 <: T2 (* QUIETSOLUTION *)
      Answer: True
(* /QUIETSOLUTION *)

      exists S,
           S <: S->S (* QUIETSOLUTION *)
      Answer: False
(* /QUIETSOLUTION *)

      exists S,
           S->S <: S  (* QUIETSOLUTION *)
      Answer: True
(* /QUIETSOLUTION *)

      forall S T1 T2,
           S <: T1*T2 ->
           exists S1 S2,
              S = S1*S2  /\  S1 <: T1  /\  S2 <: T2  (* QUIETSOLUTION *)
      Answer: True
(* /QUIETSOLUTION *)
]]
*)

(* GRADE_MANUAL 1: subtype_instances_tf_2 *)
(** [] *)

(* EX1M (subtype_concepts_tf) *)
(** Which of the following statements are true, and which are false?
    - There exists a type that is a supertype of every other type.
(* QUIETSOLUTION *)
      True
(* /QUIETSOLUTION *)
    - There exists a type that is a subtype of every other type.
(* QUIETSOLUTION *)
      False
(* /QUIETSOLUTION *)
    - There exists a pair type that is a supertype of every other
      pair type.
(* QUIETSOLUTION *)
      True
(* /QUIETSOLUTION *)
    - There exists a pair type that is a subtype of every other
      pair type.
(* QUIETSOLUTION *)
      False
(* /QUIETSOLUTION *)
    - There exists an arrow type that is a supertype of every other
      arrow type.
(* QUIETSOLUTION *)
      False
(* /QUIETSOLUTION *)
    - There exists an arrow type that is a subtype of every other
      arrow type.
(* QUIETSOLUTION *)
      False
(* /QUIETSOLUTION *)
    - There is an infinite descending chain of distinct types in the
      subtype relation---that is, an infinite sequence of types
      [S0], [S1], etc., such that all the [Si]'s are different and
      each [S(i+1)] is a subtype of [Si].
(* QUIETSOLUTION *)
      True
(* /QUIETSOLUTION *)
    - There is an infinite _ascending_ chain of distinct types in
      the subtype relation---that is, an infinite sequence of types
      [S0], [S1], etc., such that all the [Si]'s are different and
      each [S(i+1)] is a supertype of [Si].
(* QUIETSOLUTION *)
      True
(* /QUIETSOLUTION *)
*)

(* GRADE_MANUAL 1: subtype_concepts_tf *)
(** [] *)

(* FULL *)
(* EX2M (proper_subtypes) *)
(* SOONER: The "Base n" stuff is really confusing for students.  Can
   we just delete it? *)
(** Is the following statement true or false?  Briefly explain your
    answer.  (Here [Base n] stands for a base type, where [n] is
    a string standing for the name of the base type.  See the
    Syntax section below.)
[[
    forall T,
         ~(T = Bool \/ exists n, T = Base n) ->
         exists S,
            S <: T  /\  S <> T
]]
*)

(* GRADE_MANUAL 2: proper_subtypes *)
(** [] *)
(* QUIETSOLUTION *)
(** Answer: False. [T = Top->Bool] is a counterexample. *)
(* /QUIETSOLUTION *)

(* SOONER: We should be explicit about the convention that A
   represents a base type! *)
(* EX2M (small_large_1) *)
(**
   - What is the _smallest_ type [T] ("smallest" in the subtype
     relation) that makes the following assertion true?  (Assume we
     have [Unit] among the base types and [unit] as a constant of this
     type.)
[[
       empty |-- (\p:T*Top, p.fst) ((\z:A,z), unit) \in A->A
]]
(* QUIETSOLUTION *)
[[
       T = A -> A
]]
(* /QUIETSOLUTION *)
   - What is the _largest_ type [T] that makes the same assertion true?
(* QUIETSOLUTION *)
[[
       T = A -> A
]]
(* /QUIETSOLUTION *)
*)

(* GRADE_MANUAL 2: small_large_1 *)
(** [] *)

(* EX2M (small_large_2) *)
(**
   - What is the _smallest_ type [T] that makes the following
     assertion true?
[[
       empty |-- (\p:(A->A * B->B), p) ((\z:A,z), (\z:B,z)) \in T
]]
(* QUIETSOLUTION *)
[[
       T  =  (A->A * B->B)
]]
(* /QUIETSOLUTION *)
   - What is the _largest_ type [T] that makes the same assertion true?
(* QUIETSOLUTION *)
[[
       T  =  Top
]]
(* /QUIETSOLUTION *)
*)

(* GRADE_MANUAL 2: small_large_2 *)
(** [] *)

(* EX2? (small_large_3) *)
(**
   - What is the _smallest_ type [T] that makes the following
     assertion true?
[[
       a:A |-- (\p:(A*T), (p.snd) (p.fst)) (a, \z:A,z) \in A
]]
(* QUIETSOLUTION *)
[[
       T = A->A
]]
(* /QUIETSOLUTION *)
   - What is the _largest_ type [T] that makes the same assertion true?
(* QUIETSOLUTION *)
     The same.

     Here's the reasoning in more detail:

     Clearly, [T] must have the form [T1->T2].

     Now we can read off the following constraints from the program:
     - [A  <:  T1]                 (from the application of p.snd to p.fst)
     - [T2  <:  A]                 (from the final result type)
     - [(A * A->A)  <:  (A * T)]   (from the outer application)

     Inverting the last constraint tells us
[[
       A->A  <:  T1->T2
]]
     and hence
[[
         T1 <: A
         A <: T2.
]]
     So
[[
         T = A->A
]]
     is both the largest and the smallest type that makes
     the whole typing statement true.
(* /QUIETSOLUTION *)
*)
(** [] *)
(* /FULL *)
(* QUIZ *)
(**
   What is the _smallest_ type [T] that makes the following
   assertion true?
[[
       a:A |-- (\p:(A*T), (p.snd) (p.fst)) (a, \z:A,z) \in A
]]

   (A) [Top]

   (B) [A]

   (C) [Top->Top]

   (D) [Top->A]

   (E) [A->A]

   (6) [A->Top]
*)
(* /QUIZ *)

(* QUIZ *)
(**
   What is the _largest_ type [T] that makes the following
   assertion true?
[[
       a:A |-- (\p:(A*T), (p.snd) (p.fst)) (a, \z:A,z) \in A
]]

   (A) [Top]

   (B) [A]

   (C) [Top->Top]

   (D) [Top->A]

   (E) [A->A]

   (6) [A->Top]
*)
(* /QUIZ *)

(* QUIZ *)
(**
   "The type [Bool] has no proper subtypes."  (I.e., the only
   type smaller than [Bool] is [Bool] itself.)

   (A) True

   (B) False
*)
(* /QUIZ *)

(* QUIZ *)
(**
   "Suppose [S], [T1], and [T2] are types with [S <: T1 -> T2].  Then
   [S] itself is an arrow type -- i.e., [S = S1 -> S2] for some [S1]
   and [S2] -- with [T1] <: [S1] and [S2 <: T2]."

   (A) True

   (B) False
*)
(* /QUIZ *)
(* FULL *)

(* EX2M (small_large_4) *)
(**
   - What is the _smallest_ type [T] (if one exists) that makes the
     following assertion true?
[[
       exists S,
         empty |-- (\p:(A*T), (p.snd) (p.fst)) \in S
]]
(* QUIETSOLUTION *)
     There is no smallest such type -- any type of the form [A -> S] for some
     type [S] will make the assertion true, but there is no smallest one of
     these (there are infinitely many and they are incomparable).
(* /QUIETSOLUTION *)
   - What is the _largest_ type [T] that makes the same
     assertion true?
(* QUIETSOLUTION *)
[[
       T  =  A -> Top
]]
(* /QUIETSOLUTION *)
*)

(* GRADE_MANUAL 2: small_large_4 *)
(** [] *)

(* EX2M (smallest_1) *)
(** What is the _smallest_ type [T] (if one exists) that makes
    the following assertion true?
[[
      exists S t,
        empty |-- (\x:T, x x) t \in S
]]
*)

(* GRADE_MANUAL 2: smallest_1 *)
(** [] *)
(* QUIETSOLUTION *)
(** Answer: Any type of the form [T = Top->U] will make the assertion
    true, but there is no smallest one of these: [Top->A->A] and
    [Top->B->B] are both solutions, but they have no common
    subtype. *)
(* /QUIETSOLUTION *)

(* EX2M (smallest_2) *)
(** What is the _smallest_ type [T] that makes the following
    assertion true?
[[
      empty |-- (\x:Top, x) ((\z:A,z) , (\z:B,z)) \in T
]]
*)

(* GRADE_MANUAL 2: smallest_2 *)
(** [] *)
(* QUIETSOLUTION *)
(**
[[
      T  =  Top
]]
*)
(* /QUIETSOLUTION *)

(* FULL *)
(* EX3? (count_supertypes) *)
(** How many supertypes does the record type [{x:A, y:C->C}] have?  That is,
    how many different types [T] are there such that [{x:A, y:C->C} <:
    T]?  (We consider two types to be different if they are written
    differently, even if each is a subtype of the other.  For example,
    [{x:A,y:B}] and [{y:B,x:A}] are different.)
(* QUIETSOLUTION *)
Answer: Nineteen!
[[
   { x:A, y:C->C }                 { y:Top, x:A }
   { x:Top, y:C->C }               { y:Top, x:Top }
   { x:A, y:C->Top }               { x:A }
   { x:Top, y:C->Top }             { x:Top }
   { x:A, y:Top }                  { y:C->C }
   { x:Top, y:Top }                { y:C->Top }
   { y:C->C, x:A }                 { y:Top }
   { y:C->C, x:Top }               { }
   { y:C->Top, x:A }               Top
   { y:C->Top, x:Top }
]]
(* /QUIETSOLUTION *)
*)
(** [] *)

(* EX2M (pair_permutation) *)
(** The subtyping rule for product types
[[[
                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                               S1*S2 <: T1*T2
]]]
    intuitively corresponds to the "depth" subtyping rule for records.
    Extending the analogy, we might consider adding a "permutation" rule
[[[
                                   --------------
                                   T1*T2 <: T2*T1
]]]
    for products.  Is this a good idea? Briefly explain why or why not.
(* QUIETSOLUTION *)
  Answer: No, since it will break preservation: [(tru,unit).1] has
  type [Unit] according to this rule, but reduces to [tru], which
  does not have type [Unit].
(* /QUIETSOLUTION *)
*)

(* GRADE_MANUAL 2: pair_permutation *)
(** [] *)
(* /FULL *)

(* LATER: It would be great to be able to FOLD this whole coming
   section in the TERSE version -- it's not needed, and then we could
   skip straight to Properties... *)
(* ###################################################### *)
(** * Formal Definitions *)

(* TERSE: HIDEFROMHTML *)
Module STLCSub.
(* TERSE: /HIDEFROMHTML *)

(** Most of the definitions needed to formalize what we've discussed
    above -- in particular, the syntax and operational semantics of
    the language -- are identical to what we saw in the last chapter.
    We just need to extend the typing relation with the subsumption
    rule and add a new [Inductive] definition for the subtyping
    relation.  Let's first do the identical bits. *)

(** FULL: We include products in the syntax of types and terms, but not,
    for the moment, anywhere else; the [products] exercise below will
    ask you to extend the definitions of the value relation, operational
    semantics, subtyping relation, and typing relation and to extend
    the proofs of progress and preservation to fully support products. *)

(* ###################################################### *)
(** FULL: ** Core Definitions *)

(* ################################### *)
(** *** Syntax *)

(* FULL *)
(** In the rest of the chapter, we formalize just base types,
    booleans, arrow types, [Unit], and [Top], omitting record types
    and leaving product types as an exercise.  For the sake of more
    interesting examples, we'll add an arbitrary set of base types
    like [String], [Float], etc.  (Since they are just for examples,
    we won't bother adding any operations over these base types, but
    we could easily do so.) *)
(* /FULL *)
(** TERSE: (Omitting records, to avoid dealing with "[...]" stuff.) *)

(* LATER: The formatting of the solutions doesn't look all that pretty.
   We might be able to improve this if we taught Rocqsplit how to deal
   with a close-QUIETSOLUTION with a . immediately after it on the
   same line...  (Give it a quick try!) *)
(* QUIETSOLUTION *)
(* N.B.: This file extends the language with products,
   as a solution for the [product] exercise at the end. *)
(* /QUIETSOLUTION *)
Inductive ty : Type :=
  | Ty_Top   : ty
  | Ty_Bool  : ty
  | Ty_Base  : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Unit  : ty
(* FULL *)
  | Ty_Prod : ty -> ty -> ty
(* /FULL *)
.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_unit : tm
(* FULL *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
(* /FULL *)
.

(* TERSE: HIDEFROMHTML *)
(** TERSE: Standard [Custom Entry] nonsense... *)
Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.
Declare Scope stlc_scope.
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

(* INSTRUCTORS: Begin template stlc_base *)
Notation "'Base' x" := (Ty_Base x) (in custom stlc_ty at level 0, x constr at level 0) : stlc_scope.
(* INSTRUCTORS: End template stlc_base *)

(* INSTRUCTORS: Begin Definition of template stlc_unit *)
Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc_ty at level 0) : stlc_scope.
Notation "'unit'" := tm_unit (in custom stlc_tm at level 0) : stlc_scope.
(* INSTRUCTORS: End Definition of template stlc_unit *)


(* FULL *)
(* INSTRUCTORS: Begin template stlc_prod *)
Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc_ty at level 2, X custom stlc_ty, Y custom stlc_ty at level 0).

Notation "( x ',' y )" := (tm_pair x y) (in custom stlc_tm at level 0,
                                                x custom stlc_tm,
                                                y custom stlc_tm) : stlc_scope.
Notation "t '.fst'" := (tm_fst t) (in custom stlc_tm at level 1) : stlc_scope.
Notation "t '.snd'" := (tm_snd t) (in custom stlc_tm at level 1) : stlc_scope.
(* INSTRUCTORS: End Definition of template stlc_prod *)
(* INSTRUCTORS: ------------------------------------------------------------ *)
(* /FULL *)

(* INSTRUCTORS: Begin Definition of stlc_top *)
Notation "'Top'" := (Ty_Top) (in custom stlc_ty at level 0) : stlc_scope.
(* INSTRUCTORS: End Definition of stlc_top *)


(* TERSE: /HIDEFROMHTML *)
(* ################################### *)
(** *** Substitution *)

(** The definition of substitution remains exactly the same as for the
    pure STLC. *)

(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template subst *)
(* NOTATION: SAZ 2024 - I think this notation should bind tigher than
application, which is a good reason to put application higher than
level 1 in the base stlc_tm grammar. *)
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).
(* INSTRUCTORS: End Definition of subst subst *)
(* INSTRUCTORS: ------------------------------------------------------------- *)

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{unit}> =>
      <{unit}>
(* FULL *)
  | <{ (t1, t2) }> =>
      <{( [x:=s] t1, [x:=s] t2 )}>
  | <{t0.fst}> =>
      <{ ([x:=s] t0).fst}>
  | <{t0.snd}> =>
      <{ ([x:=s] t0).snd}>
(* /FULL *)
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm) : stlc_scope.

(* ################################### *)
(** *** Reduction *)

(** Likewise the definitions of [value] and [step]. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_unit :
      value <{unit}>(* QUIETSOLUTION *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>
(* /QUIETSOLUTION *)
.

(* TERSE: HIDEFROMHTML *)
Hint Constructors value : core.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)

(* TERSE: HIDEFROMHTML *)
Reserved Notation "t '-->' t'" (at level 40).
(* TERSE: /HIDEFROMHTML *)

Inductive step : tm -> tm -> Prop :=
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
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>(* QUIETSOLUTION *)
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
(* /QUIETSOLUTION *)
where "t '-->' t'" := (step t t').

(* TERSE: HIDEFROMHTML *)
Hint Constructors step : core.
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** ** Subtyping *)

(** FULL: Now we come to the interesting part.  We begin by defining
    the subtyping relation and developing some of its important
    technical properties. *)

(** The definition of subtyping is just what we sketched in the
    motivating discussion. *)

(* TERSE: HIDEFROMHTML *)
Reserved Notation "T '<:' U" (at level 40).
(* TERSE: /HIDEFROMHTML *)

(* NOTATION: Wondering if there would be a way to make both arguments
   to <: automatically / always be parsed with the stlc grammar... (Or
   if this would be a good idea!) KK: I think it would make sense, but
   I had trouble doing that for --> in Stlc.

   UPDATE: The problem is that <: is an infix notation, so the parser
   has no way of knowing that it should switch from constr to stlc at
   the beginning.  We should mayber just live with this.

   Or, better, perhaps we could include <: in the stlc grammar, so
   that we can uniformly enclose subtyping statements in brackets.
 *)
(* NOTATION: SAZ 2024 - An alternative to the proposal above would
   be to put the subtyping judgment in the <{{ }}> brackets like types.
   That would be possible (I think), and would make the Arrow rule
   look like:

    <{{ T1 <: S1 }}> ->
    <{{ S2 <: T2 }}> ->
    <{{ S1 -> S2 <: T1 <: T2 }}>

   This would parallel the use of <{ }> for terms and term typing.
   I've held off on doing that for now, though.

   BCP 25: I tried adding this...

         Notation "S <: T" := (subtype S T)
                                 (in custom stlc_ty at level 99,
                                  S custom stlc_ty,
                                  T custom stlc_ty).

   but it did not work (the precedence levels are wrong).  I agree that
   it *should* work if someone can push through the details.

   Once it doesn, we will need to add boilerpate for tracking common parts of files.
   Also, need to figure out how to make the definitioon of subtyping itself use this
   notation in the Reserved Notation declaration! *)

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: <{{ Top }}>
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      <{{ S1->S2 }}> <: <{{ T1->T2 }}>(* QUIETSOLUTION *)
  | S_Prod : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      <{{ S1 * S2 }}> <: <{{ T1 * T2 }}>
(* /QUIETSOLUTION *)
where "T '<:' U" := (subtype T U).

(** Note that we don't need any special rules for base types ([Bool]
    and [Base]): they are automatically subtypes of themselves (by
    [S_Refl]) and [Top] (by [S_Top]), and that's all we want. *)

(* TERSE: HIDEFROMHTML *)
Hint Constructors subtype : core.
(* TERSE: /HIDEFROMHTML *)

(* FULL *)
Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".

Notation A := <{{ Base "A" }}>.
Notation B := <{{ Base "B" }}>.
Notation C := <{{ Base "C" }}>.

Notation String := <{{ Base "String" }}>.
Notation Float := <{{ Base "Float" }}>.
Notation Integer := <{{ Base "Integer" }}>.

Example subtyping_example_0 :
  <{{ C->Bool }}> <: <{{ C->Top }}>.
Proof. auto. Qed.

(* EX2? (subtyping_judgements) *)
(** (Leave this exercise [Admitted] until after you have finished adding product
    types to the language -- see exercise [products] -- at least up to
    this point in the file).

    Recall that, in chapter \CHAP{MoreStlc}, the optional section
    "Encoding Records" describes how records can be encoded as pairs.
    Using this encoding, define pair types representing the following
    record types:
[[
    Person := { name : String }
    Student := { name : String ; gpa : Float }
    Employee := { name : String ; ssn : Integer }
]]
*)
Definition Person : ty
  (* ADMITDEF *) :=
  <{{ String * Top }}>.
(* /ADMITDEF *)
Definition Student : ty
  (* ADMITDEF *) :=
  <{{ String * (Top * Float) }}>.
(* /ADMITDEF *)
Definition Employee : ty
  (* ADMITDEF *) :=
  <{{ String * (Integer * Top) }}>.
(* /ADMITDEF *)

(** Now use the definition of the subtype relation to prove the following: *)

Example sub_student_person :
  Student <: Person.
Proof.
(* ADMITTED *)
  unfold Student. unfold Person. auto.
Qed.
(* /ADMITTED *)

Example sub_employee_person :
  Employee <: Person.
Proof.
(* ADMITTED *)
  unfold Employee. unfold Person. auto.
Qed.
(* /ADMITTED *)
(** [] *)

(** The following facts are mostly easy to prove in Rocq.  To get
    full benefit from the exercises, make sure you also
    understand how to prove them on paper! *)

(* EX1? (subtyping_example_1) *)
Example subtyping_example_1 :
  <{{ Top->Student }}> <:  <{{ (C->C)->Person }}>.
Proof with eauto.
  (* ADMITTED *)
  apply S_Arrow...
  apply sub_student_person.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX1? (subtyping_example_2) *)
Example subtyping_example_2 :
  <{{ Top->Person }}> <: <{{ Person->Top }}>.
Proof with eauto.
  (* ADMITTED *)
  apply S_Arrow...
Qed.
(* /ADMITTED *)
(** [] *)

End Examples.
(* /FULL *)

(* ###################################################################### *)
(** ** Typing *)

(** The only change to the typing relation is the addition of the rule
    of subsumption, [T_Sub]. *)

Definition context := partial_map ty.

(* HIDEFROMHTML *)
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
(* /HIDEFROMHTML *)


(* HIDE: The parens around arrow types in T_Abs, etc. are
   unfortunate.  Wondering again if we should put <{...}> around the
   whole typing judgement instead. KK: I think it might be a bit too
   heavyweight. Also it suffers from the same problem as the notation
   in subst. We cannot reserve the notation to be in stlc.  *)
(* NOTATION: SAZ 2024 - I went wit hthe <{ ... }> everywhere. *)
Inductive has_type : context -> tm -> ty -> Prop :=
  (* Pure STLC, same as before: *)
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
  | T_Unit : forall Gamma,
      <{ Gamma |-- unit \in Unit }>(* QUIETSOLUTION *)
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
(* /QUIETSOLUTION *)
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      <{ Gamma |-- t1 \in T1 }> ->
      T1 <: T2 ->
      <{ Gamma |-- t1 \in T2 }>

where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T) : stlc_scope.

(* TERSE: HIDEFROMHTML *)
Hint Constructors has_type : core.
(* TERSE: /HIDEFROMHTML *)

(* FULL *)
Module Examples2.
Import Examples.

(** Do the following exercises after you have added product types to
    the language.  For each informal typing judgement, write it as a
    formal statement in Rocq and prove it. *)

(* LATER: This would be more interesting if it used subsumption *)
(* EX1? (typing_example_0) *)
(* empty |-- ((\z:A,z), (\z:B,z)) \in (A->A * B->B) *)
(* SOLUTION *)
(* NOTATION: NOWISH: Lots of cleaning up to do once the notation stabilizes! (Lucas) *)
Example typing_example_0 :
  <{ empty |--
    ((\z:A, z),(\z:B, z)) \in
        ((A -> A) * (B -> B)) }>.
Proof.
  auto.
Qed.
(* /SOLUTION *)
(** [] *)

(* EX2? (typing_example_1) *)
(* empty |-- (\x:(Top * B->B), x.snd) ((\z:A,z), (\z:B,z))
         \in B->B *)
(* SOLUTION *)
Example typing_example_1 :
  <{ empty |--
   (\x:(Top * (B -> B)), x.snd) (((\z:A, z), (\z:B, z)))
  \in (B->B) }>.
Proof with eauto.
  eapply T_App.
  (* Ty_Arrow *)
  - apply T_Abs.
    eapply T_Snd.
    apply T_Var. reflexivity.
  - eapply T_Sub.
    + apply typing_example_0.
    + auto.
Qed.
(* /SOLUTION *)
(** [] *)

(* EX2? (typing_example_2) *)
(* empty |-- (\z:(C->C)->(Top * B->B), (z (\x:C,x)).snd)
              (\z:C->C, ((\z:A,z), (\z:B,z)))
         \in B->B *)
(* SOLUTION *)
Example typing_example_2 :
  <{ empty |--
           (\z:((C -> C) -> (Top * (B -> B))), (z (\x:C, x)).snd)
                   (\z:(C -> C), (((\z:A, z), (\z:B, z)))) \in
           (B->B) }>.
Proof.
  (* INSTRUCTORS: BCP 2021: Not sure why the automation suddenly
     didn't work in this proof and the one above it -- this file
     compiles fine, but the generated .../sol/Sub.v does not. *)
  eapply T_App.
  - apply T_Abs.
    eapply T_Snd.
    eapply T_App.
    + apply T_Var. reflexivity.
    + apply T_Abs.
      apply T_Var. reflexivity.
  - apply T_Abs.
    apply T_Pair.
    + eapply T_Sub.
      * apply T_Abs.
        apply T_Var. reflexivity.
      * apply S_Top.
    + apply T_Abs.
      apply T_Var. reflexivity.
Qed.
(* /SOLUTION *)
(** [] *)

End Examples2.
(* /FULL *)

(* ###################################################################### *)
(** * Properties *)

(** FULL: The fundamental properties of the system that we want to
    check are the same as always: progress and preservation.  Unlike
    the extension of the STLC with references (chapter \CHAP{References}),
    we don't need to change the _statements_ of these properties to
    take subtyping into account.  However, their proofs do become a
    little bit more involved. *)
(** TERSE: We want the same properties as always: progress + preservation.

      - _Statements_ of these theorems don't need to change, compared
        to pure STLC

      - But _proofs_ are a bit more involved, to account for the
        additional flexibility in the typing relation *)

(* ###################################################################### *)
(** ** Inversion Lemmas for Subtyping *)

(** Before we look at the properties of the typing relation, we need
    to establish a couple of critical structural properties of the
    subtype relation:
       - [Bool] is the only subtype of [Bool], and
       - every subtype of an arrow type is itself an arrow type. *)

(** FULL: These are called _inversion lemmas_ because they play a
    similar role in proofs as the built-in [inversion] tactic: given a
    hypothesis that there exists a derivation of some subtyping
    statement [S <: T] and some constraints on the shape of [S] and/or
    [T], each inversion lemma reasons about what this derivation must
    look like to tell us something further about the shapes of [S] and
    [T] and the existence of subtype relations between their parts. *)
(** TERSE: Formally: *)

(* FULL: EX2? (sub_inversion_Bool) *)
Lemma sub_inversion_Bool : forall U,
     U <: <{{ Bool }}> ->
     U = <{{ Bool }}>.
(* FOLD *)
Proof with auto.
  intros U Hs.
  remember <{{ Bool }}> as V.
  (* ADMITTED *)
  induction Hs; try solve_by_invert...
  - (* S_Trans *)
  replace T with U in *; auto.
Qed.
(* /ADMITTED *)
(* /FOLD *)
(** FULL: [] *)

(* FULL: EX3 (sub_inversion_arrow) *)
Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{{ V1->V2 }}> ->
     exists U1 U2,
     U = <{{ U1->U2 }}> /\ V1 <: U1 /\ U2 <: V2.
(* FOLD *)
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{{ V1->V2 }}> as V.
  generalize dependent V2. generalize dependent V1.
  (* ADMITTED *)
  induction Hs; subst; intros; try solve_by_invert.
    - (* S_Refl *)
      exists V1, V2. subst...
    - (* S_Trans *)
      apply IHHs2 in HeqV. destruct HeqV as [U1 [U2 [HeqS [HU1 HU2]]]].
      apply IHHs1 in HeqS. destruct HeqS as [S1 [S2 [HeqS1 [HS1 HS2]]]].
      exists S1, S2. subst...
    - (* S_Arrow *)
      exists S1, S2. injection HeqV as HeqV; subst...  Qed.
(* /ADMITTED *)
(* /FOLD *)
(** FULL: [] *)

(** FULL: There are additional _inversion lemmas_ for the other types:
       - [Unit] is the only subtype of [Unit], and
       - [Base n] is the only subtype of [Base n], and
       - [Top] is the only supertype of [Top]. *)

(* FULL *)
(* EX2? (sub_inversion_Unit) *)
Lemma sub_inversion_Unit : forall U,
     U <: <{{ Unit }}> ->
     U = <{{ Unit }}>.
(* FOLD *)
Proof with auto.
  intros U Hs.
  remember <{{ Unit }}> as V.
  (* ADMITTED *)
  induction Hs; try solve_by_invert...
  - (* S_Trans *) subst. assert (U = <{{ Unit }}>); subst...
Qed.
(* /ADMITTED *)
(* /FOLD *)
(** [] *)

(* EX2? (sub_inversion_Base) *)
Lemma sub_inversion_Base : forall U s,
     U <: <{{ Base s }}> ->
     U = <{{ Base s }}>.
(* FOLD *)
Proof with auto.
  intros U s Hs.
  remember <{{ Base s }}> as V.
  (* ADMITTED *)
  induction Hs; try solve_by_invert...
  - (* S_Trans *) subst. assert (U = <{{ Base s }}>); subst...
Qed.
(* /ADMITTED *)
(* /FOLD *)
(** [] *)

(* EX2? (sub_inversion_Top) *)
Lemma sub_inversion_Top : forall U,
     <{{ Top }}> <: U ->
     U = <{{ Top }}>.
(* FOLD *)
Proof with auto.
  intros U Hs.
  remember <{{ Top }}> as V.
  (* ADMITTED *)
  induction Hs; try solve_by_invert...
  - (* S_Trans *) subst. assert (U = <{{ Top }}>); subst...
Qed.
(* /ADMITTED *)
(* /FOLD *)
(** [] *)
(* /FULL *)

(* QUIETSOLUTION *)

Lemma sub_inversion_prod : forall S T1 T2,
     S <: <{{ T1 * T2 }}> ->
     exists S1 S2,
       S = <{{ S1 * S2 }}> /\ S1 <: T1 /\ S2 <: T2.
Proof with eauto.
  intros S T1 T2 Hsub. remember <{{ T1 * T2 }}> as Prod.
  generalize dependent T2. generalize dependent T1.
  induction Hsub; intros;
    try solve_by_invert.
  - (* S_Refl *)
    subst. subst. exists T1, T2...
  - (* S_Trans *)
    destruct (IHHsub2 T1 T2) as [S1 [S2 [HeqUprod [S1subT1 S2subT2]]]]...
    destruct (IHHsub1 S1 S2) as [U1 [U2 [HeqSprod [U1subS1 U2subS2]]]]...
    exists U1, U2...
  - (* S_Prod *)
    injection HeqProd as HeqProd. subst.
    exists S1, S2...
Qed.

(* /QUIETSOLUTION *)
(* ########################################## *)
(** ** Canonical Forms *)

(** FULL: The proof of the progress theorem -- that a well-typed
    non-value can always take a step -- doesn't need to change too
    much: we just need one small refinement.  When we're considering
    the case where the term in question is an application [t1 t2]
    where both [t1] and [t2] are values, we need to know that [t1] has
    the _form_ of a lambda-abstraction, so that we can apply the
    [ST_AppAbs] reduction rule.  In the ordinary STLC, this is
    obvious: we know that [t1] has a function type [T11->T12], and
    there is only one rule that can be used to give a function type to
    a value -- rule [T_Abs] -- and the form of the conclusion of this
    rule forces [t1] to be an abstraction.

    In the STLC with subtyping, this reasoning doesn't quite work
    because there's another rule that can be used to show that a value
    has a function type: subsumption.  Fortunately, this possibility
    doesn't change things much: if the last rule used to show [Gamma
    |-- t1 \in T11->T12] is subsumption, then there is some
    _sub_-derivation whose subject is also [t1], and we can reason by
    induction until we finally bottom out at a use of [T_Abs].

    This bit of reasoning is packaged up in the following lemma, which
    tells us the possible "canonical forms" (i.e., values) of function
    type. *)
(** TERSE: The proof of progress uses facts of the form "every value
    belonging to an arrow type is an abstraction."

    In the pure STLC, such facts are "immediate from the
    definition" (formally, they follow directly by [inversion]).

    With subtyping, they require real proofs by induction... *)

(* FULL: EX3? (canonical_forms_of_arrow_types) *)
Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  <{ Gamma |-- s \in T1->T2 }> ->
  value s ->
  exists x S1 s2,
     s = <{\x:S1,s2}>.
(* FOLD *)
Proof with eauto.
  (* ADMITTED *)
  intros Gamma s T1 T2 Hty Hv.
  remember <{{ T1->T2 }}> as T.
  generalize dependent T2. generalize dependent T1.
  induction Hty; intros; try solve_by_invert.
  - (* T_Abs *)
    exists x, T2, t1...
  - (* T_Sub *)
    subst.
    destruct (sub_inversion_arrow _ _ _ H) as
      [S1 [S2 [HeqS [Hsub1 Hsub2]]]]...  Qed.
(* /ADMITTED *)
(* /FOLD *)
(** FULL: [] *)

(** Similarly, the canonical forms of type [Bool] are the constants
    [tm_true] and [tm_false]. *)

Lemma canonical_forms_of_Bool : forall Gamma s,
  <{ Gamma |-- s \in Bool }> ->
  value s ->
  s = tm_true \/ s = tm_false.
(* FOLD *)
Proof with eauto.
  intros Gamma s Hty Hv.
  remember <{{ Bool }}> as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.
(* /FOLD *)
(* QUIETSOLUTION *)

Lemma canonical_forms_of_product_types : forall Gamma t T1 T2,
     <{ Gamma |-- t \in T1 * T2 }> ->
     value t ->
     exists t1 t2,
       t = <{ (t1, t2) }>.
Proof with eauto.
  intros Gamma t T1 T2 Htyp Hval.
  remember <{{ T1 * T2 }}> as Prod.
  generalize dependent T1. generalize dependent T2.
  induction Htyp; intros; try solve_by_invert.
  - (* T_Pair *)
    exists t1, t2...
  - (* T_Sub *)
    rewrite HeqProd in H. apply sub_inversion_prod in H.
    destruct H as [S1 [S2 [HeqSprod [_ _]]]]...
Qed.

(* /QUIETSOLUTION *)
(* ########################################## *)
(** ** Progress *)

(** FULL: The proof of progress now proceeds just like the one for the
    pure STLC, except that in several places we invoke canonical forms
    lemmas... *)
(** _Theorem_ (Progress): For any term [t] and type [T], if [empty |--
    t \in T] then [t] is a value or [t --> t'] for some term [t'].

    _Proof_: Let [t] and [T] be given, with [empty |-- t \in T].
    Proceed by induction on the typing derivation.

    The cases for [T_Abs], [T_Unit], [T_True] and [T_False] are
    immediate because abstractions, [unit], [true], and
    [false] are already values.  The [T_Var] case is vacuous
    because variables cannot be typed in the empty context.  The
    remaining cases are more interesting:

    - If the last step in the typing derivation uses rule [T_App],
      then there are terms [t1] [t2] and types [T1] and [T2] such that
      [t = t1 t2], [T = T2], [empty |-- t1 \in T1 -> T2], and [empty
      |-- t2 \in T1].  Moreover, by the induction hypothesis, either
      [t1] is a value or it steps, and either [t2] is a value or it
      steps.  There are three possibilities to consider:

      - First, suppose [t1 --> t1'] for some term [t1'].  Then [t1
        t2 --> t1' t2] by [ST_App1].

      - Second, suppose [t1] is a value and [t2 --> t2'] for some term
        [t2'].  Then [t1 t2 --> t1 t2'] by rule [ST_App2] because [t1]
        is a value.

      - Third, suppose [t1] and [t2] are both values.  By the
        canonical forms lemma for arrow types, we know that [t1] has
        the form [\x:S1,s2] for some [x], [S1], and [s2].  But then
        [(\x:S1,s2) t2 --> [x:=t2]s2] by [ST_AppAbs], since [t2] is a
        value.

    - If the final step of the derivation uses rule [T_If], then
      there are terms [t1], [t2], and [t3] such that [t = if t1
      then t2 else t3], with [empty |-- t1 \in Bool] and with [empty
      |-- t2 \in T] and [empty |-- t3 \in T].  Moreover, by the
      induction hypothesis, either [t1] is a value or it steps.

       - If [t1] is a value, then by the canonical forms lemma for
         booleans, either [t1 = true] or [t1 = false].  In
         either case, [t] can step, using rule [ST_IfTrue] or
         [ST_IfFalse].

       - If [t1] can step, then so can [t], by rule [ST_If].

    - If the final step of the derivation is by [T_Sub], then there is
      a type [T2] such that [T1 <: T2] and [empty |-- t1 \in T1].  The
      desired result is exactly the induction hypothesis for the
      typing subderivation. *)

(** TERSE: *** *)
(** Formally: *)

Theorem progress : forall t T,
     <{ empty |-- t \in T }> ->
     value t \/ exists t', t --> t'.
(* FOLD *)
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
  - (* T_Var *)
    discriminate.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        eapply canonical_forms_of_arrow_types in Ht1; [|assumption].
        destruct Ht1 as [x [S1 [s2 H1]]]. subst.
        exists (<{ [x:=t2]s2 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_If *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + apply canonical_forms_of_Bool in Ht1; [|assumption].
      destruct Ht1; subst...
    + destruct H. rename x into t1'. eauto. (* QUIETSOLUTION *)
  - (* T_Pair *)
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 steps *)
        right. destruct H0 as [t2' Hstp].
        exists <{(t1, t2')}>...
    + (* t1 steps *)
      right. destruct H as [t1' Hstp].
      exists <{(t1', t2)}>...
  - (* T_Fst *)
    right. destruct IHHt...
    + (* t is a value *)
      apply canonical_forms_of_product_types in Ht...
      destruct Ht as [t1 [t2 teq]]. subst.
      inversion H. subst. exists t1...
    + (* t steps *)
      destruct H as [t' Hstp]. exists <{t'.fst}>...
  - (* T_Snd *)
    right. destruct IHHt...
    + (* t is a value *)
      apply canonical_forms_of_product_types in Ht...
      destruct Ht as [t1 [t2 teq]]. subst.
      inversion H. subst. exists t2...
    + (* t steps *)
      destruct H as [t' Hstp]. exists <{t'.snd}>...
(* /QUIETSOLUTION *)
Qed.
(* /FOLD *)

(* ########################################## *)
(** ** Inversion Lemmas for Typing *)

(** FULL: The proof of the preservation theorem also becomes a little more
    complex with the addition of subtyping.  The reason is that, as
    with the "inversion lemmas for subtyping" above, there are a
    number of facts about the typing relation that are immediate from
    the definition in the pure STLC (formally: that can be obtained
    directly from the [inversion] tactic) but that require real proofs
    in the presence of subtyping because there are multiple ways to
    derive the same [has_type] statement.

    The following inversion lemma tells us that, if we have a
    derivation of some typing statement [Gamma |-- \x:S1,t2 \in T] whose
    subject is an abstraction, then there must be some subderivation
    giving a type to the body [t2]. *)
(** TERSE: We also need to prove an inversion lemma corresponding to a
    structural fact about the typing relation that is "obvious from
    the definition" in pure STLC. *)

(** _Lemma_: If [Gamma |-- \x:S1,t2 \in T], then there is a type [S2]
    such that [x|->S1; Gamma |-- t2 \in S2] and [S1 -> S2 <: T].

    Notice that the lemma does _not_ say, "then [T] itself is an arrow
    type" -- this is tempting, but false!  (Why?) *)

(** TERSE: *** *)

(** TERSE: _Lemma_: If [Gamma |-- \x:S1,t2 \in T], then there is a type [S2]
    such that [x|->S1; Gamma |-- t2 \in S2] and [S1 -> S2 <: T]. *)

(** _Proof_: Let [Gamma], [x], [S1], [t2] and [T] be given as
     described.  Proceed by induction on the derivation of [Gamma |--
     \x:S1,t2 \in T].  The cases for [T_Var] and [T_App] are vacuous
     as those rules cannot be used to give a type to a syntactic
     abstraction.

     - If the last step of the derivation is a use of [T_Abs] then
       there is a type [T12] such that [T = S1 -> T12] and [x:S1;
       Gamma |-- t2 \in T12].  Picking [T12] for [S2] gives us what we
       need, since [S1 -> T12 <: S1 -> T12] follows from [S_Refl].


     - If the last step of the derivation is a use of [T_Sub] then
       there is a type [S] such that [S <: T] and [Gamma |-- \x:S1,t2
       \in S].  The IH for the typing subderivation tells us that there
       is some type [S2] with [S1 -> S2 <: S] and [x:S1; Gamma |-- t2
       \in S2].  Picking type [S2] gives us what we need, since [S1 ->
       S2 <: T] then follows by [S_Trans]. *)

(** TERSE: *** *)
(** Formally: *)

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     <{ Gamma |-- \x:S1,t2 \in T }> ->
     exists S2,
       <{{ S1->S2 }}> <: T
       /\ <{ x |-> S1 ; Gamma |-- t2 \in S2 }>.
(* FOLD *)
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember <{\x:S1,t2}> as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    exists T1...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
  Qed.
(* /FOLD *)

(** TERSE: *** *)
(** TERSE: Similarly: *)
(* FULL: EX3? (typing_inversion_var) *)
Lemma typing_inversion_var : forall Gamma (x:string) T,
  <{ Gamma |-- x \in T }> ->
  exists S,
    Gamma x = Some S /\ S <: T.
(* FOLD *)
Proof with eauto.
  (* ADMITTED *)
  intros Gamma x T Hty.
  remember (tm_var x) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_Var *)
    exists T1...
  - (* T_Sub *)
    destruct IHHty as [U [Hctx HsubU]]... Qed.
(* /ADMITTED *)
(** FULL: [] *)
(* /FOLD *)

(* FULL: EX3? (typing_inversion_app) *)
Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  <{ Gamma |-- t1 t2 \in T2 }> ->
  exists T1,
    <{ Gamma |-- t1 \in T1->T2 }> /\
    <{ Gamma |-- t2 \in T1 }>.
(* FOLD *)
Proof with eauto.
  (* ADMITTED *)
  intros Gamma t1 t2 T2 Hty.
  remember (<{t1 t2}>) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_App *)
    exists T2...
  - (* T_Sub *)
    destruct IHHty as [U1 [Hty1 Hty2]]...
Qed.
(* /ADMITTED *)
(** FULL: [] *)
(* /FOLD *)

(* HIDE *)
Lemma typing_inversion_true : forall Gamma T,
  <{ Gamma |-- true \in T }> ->
  <{{ Bool }}> <: T.
(* FOLD *)
Proof with eauto.
  intros Gamma T Htyp. remember <{ true }> as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.
(* /FOLD *)

Lemma typing_inversion_false : forall Gamma T,
  <{ Gamma |-- false \in T }> ->
  <{{ Bool }}> <: T.
(* FOLD *)
Proof with eauto.
  intros Gamma T Htyp. remember <{ false }> as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.
(* /FOLD *)

Lemma typing_inversion_if : forall Gamma t1 t2 t3 T,
  <{ Gamma |-- if t1 then t2 else t3 \in T }> ->
     <{ Gamma |-- t1 \in Bool }>
  /\ <{ Gamma |-- t2 \in T }>
  /\ <{ Gamma |-- t3 \in T }>.
(* FOLD *)
Proof with eauto.
  intros Gamma t1 t2 t3 T Hty.
  remember (<{ if t1 then t2 else t3 }> ) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_If *)
    auto.
  - (* T_Sub *)
    destruct (IHHty H0) as [H1 [H2 H3]]...
Qed.
(* /FOLD *)
(* /HIDE *)

Lemma typing_inversion_unit : forall Gamma T,
  <{ Gamma |-- unit \in T }> ->
  <{{ Unit }}> <: T.
(* FOLD *)
Proof with eauto.
  intros Gamma T Htyp. remember <{ unit }> as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.
(* /FOLD *)

(* QUIETSOLUTION *)

Lemma typing_inversion_pair : forall Gamma t1 t2 T,
  <{ Gamma |-- (t1, t2) \in T }> ->
  exists T1 T2,
    <{{ T1 * T2 }}> <: T /\
    <{ Gamma |-- t1 \in T1 }> /\ <{ Gamma |-- t2 \in T2 }>.
Proof with eauto.
  intros Gamma t1 t2 T Htyp.  remember <{ (t1, t2) }> as pair.
  induction Htyp;
    inversion Heqpair; subst; intros...
  - (* T_Sub *)
    destruct IHHtyp as [T3 [T4 [Hsub [Htyp1 Htyp2]]]]...
    exists T3, T4...
Qed.

Lemma typing_inversion_fst : forall Gamma t T,
  <{ Gamma |-- t.fst \in T }> ->
  exists T1 T2,
    T1 <: T /\ <{ Gamma |-- t \in T1 * T2 }>.
Proof with eauto.
  intros Gamma t T Htyp. remember <{t.fst}> as fst.
  induction Htyp;
    inversion Heqfst; subst; intros...
  - (* T_Sub *)
    destruct IHHtyp as [T3 [T4 [Hsub Htyp1]]]...
Qed.

Lemma typing_inversion_snd : forall Gamma t T,
  <{ Gamma |-- t.snd \in T }> ->
  exists T1 T2,
    T2 <: T /\ <{ Gamma |-- t \in T1 * T2 }>.
Proof with eauto.
  intros Gamma t T Htyp. remember <{t.snd}> as snd.
  induction Htyp;
    inversion Heqsnd; subst; intros...
  - (* T_Sub *)
    destruct IHHtyp as [T3 [T4 [Hsub Htyp1]]]...
Qed.

(* /QUIETSOLUTION *)

(* TERSE: HIDEFROMHTML *)
(** The inversion lemmas for typing and for subtyping between arrow
    types can be packaged up as a useful "combination lemma" telling
    us exactly what we'll actually require below. *)

Lemma abs_arrow : forall x S1 s2 T1 T2,
  <{ empty |-- \x:S1,s2 \in T1->T2 }> ->
  T1 <: S1
  /\ <{ x |-> S1 |-- s2 \in T2 }>.
(* FOLD *)
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  injection Heq as Heq; subst...  Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* ########################################## *)
(** ** Weakening *)

(** The weakening lemma is proved as in pure STLC. *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     <{ Gamma  |-- t \in T }> ->
     <{ Gamma' |-- t \in T }>.
(* FOLD *)
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.
(* /FOLD *)

Corollary weakening_empty : forall Gamma t T,
     <{ empty |-- t \in T }> ->
     <{ Gamma |-- t \in T }>.
(* FOLD *)
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.
(* /FOLD *)

(* HIDE *)
(* SOONER: BCP 20: This can all be deleted now, yes?  BCP 21: Oops --
   needed by UseTactics.v!!  This should be fixed. *)

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x <{x}>
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x <{t1 t2}>
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x <{t1 t2}>
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x <{\y:T11,t12}>
  | afi_test1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_test2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_test3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x <{if t1 then t2 else t3}>(* QUIETSOLUTION *)
  | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{(t1, t2)}>
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{(t1, t2)}>
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x <{t.fst}>
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x <{t.snd}>
(* /QUIETSOLUTION *)
.

(* TERSE: HIDEFROMHTML *)
Hint Constructors appears_free_in : core.
(* TERSE: /HIDEFROMHTML *)

Lemma context_invariance : forall Gamma Gamma' t S,
     <{ Gamma |-- t \in S }>  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     <{ Gamma' |-- t \in S }>.
(* FOLD *)
Proof with eauto.
  intros. generalize dependent Gamma'.
  induction H;
    intros Gamma' Heqv...
  - (* T_Var *)
    apply T_Var... rewrite <- Heqv...
  - (* T_Abs *)
    apply T_Abs. apply IHhas_type. intros x1 Hafi.
    destruct (eqb_spec x x1) as [Hxx1|Hxx1]; subst.
    + rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + rewrite update_neq; [| assumption].
      rewrite update_neq; [| assumption].
      auto.
  - (* T_App *)
    eapply T_App...
  - (* T_If *)
    eapply T_If...
  - (* T_Pair *)
    apply T_Pair...
Qed.
(* /FOLD *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   <{ Gamma |-- t \in T }> ->
   exists T', Gamma x = Some T'.
(* FOLD *)
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp;
      subst; inversion Hafi; subst...
  - (* T_Abs *)
    destruct (IHHtyp H4) as [T Hctx]. exists T.
    rewrite update_neq in Hctx; assumption. Qed.
(* /FOLD *)

(* /HIDE *)

(* ########################################## *)
(** ** Substitution *)

(** FULL: When subtyping is involved proofs are generally easier
    when done by induction on typing derivations, rather than on terms.
    The _substitution lemma_ is proved as for pure STLC, but using
    induction on the typing derivation this time (see Exercise
    substitution_preserves_typing_from_typing_ind in StlcProp.v). *)
(** TERSE: The _substitution lemma_ is stated exactly as in pure STLC.

    The proof is also the same except that here it is easier to use
    induction on typing derivations rather than on terms. *)

(* NOTATION: SOONER: why (x |-> U ; Gamma) and not x |-> U ; Gamma ? *)
Lemma substitution_preserves_typing : forall Gamma x U t v T,
   <{ x |-> U ; Gamma |-- t \in T }> ->
   <{ empty |-- v \in U }>  ->
   <{ Gamma |-- [x:=v]t \in T }>.
(* FOLD *)
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
 (* ADMITTED *)
  - (* T_Var *)
    rename x0 into y.
    destruct (eqb_spec x y) as [Hxy|Hxy]; subst.
    + (* x = y *)
      rewrite update_eq in H.
      injection H as H. subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var.
      rewrite update_neq in H; assumption.
  - (* T_Abs *)
    rename x0 into y. subst.
    destruct (eqb_spec x y) as [Hxy|Hxy]; apply T_Abs.
    + (* x=y *)
      subst. rewrite update_shadow in Ht. assumption.
    + (* x <> y *)
      subst. apply IHHt.
      rewrite update_permute; auto.
Qed.
(* /ADMITTED *)
(* /FOLD *)

(* ########################################## *)
(** ** Preservation *)

(** The proof of preservation now proceeds pretty much as in earlier
    chapters, using the substitution lemma at the appropriate point
    and the inversion lemma from above to extract structural
    information from typing assumptions. *)

(** TERSE: *** *)

(** _Theorem_ (Preservation): If [t], [t'] are terms and [T] is a type
    such that [empty |-- t \in T] and [t --> t'], then [empty |-- t'
    \in T].

    _Proof_: Let [t] and [T] be given such that [empty |-- t \in T].
    We proceed by induction on the structure of this typing
    derivation. The [T_Abs], [T_Unit], [T_True], and [T_False] cases
    are vacuous because abstractions and constants don't step.  Case
    [T_Var] is vacuous as well, since the context is empty.

     - If the final step of the derivation is by [T_App], then there
       are terms [t1] and [t2] and types [T1] and [T2] such that [t =
       t1 t2], [T = T2], [empty |-- t1 \in T1 -> T2], and [empty |--
       t2 \in T1].

       By the definition of the step relation, there are three ways
       [t1 t2] can step.  Cases [ST_App1] and [ST_App2] follow
       immediately by the induction hypotheses for the typing
       subderivations and a use of [T_App].

       Suppose instead [t1 t2] steps by [ST_AppAbs].  Then [t1 =
       \x:S,t12] for some type [S] and term [t12], and [t' =
       [x:=t2]t12].

       By lemma [abs_arrow], we have [T1 <: S] and [x:S1 |-- s2 \in
       T2].  It then follows by the substitution
       lemma ([substitution_preserves_typing]) that [empty |-- [x:=t2]
       t12 \in T2] as desired.

     - If the final step of the derivation uses rule [T_If], then
       there are terms [t1], [t2], and [t3] such that [t = if t1 then
       t2 else t3], with [empty |-- t1 \in Bool] and with [empty |--
       t2 \in T] and [empty |-- t3 \in T].  Moreover, by the induction
       hypothesis, if [t1] steps to [t1'] then [empty |-- t1' : Bool].
       There are three cases to consider, depending on which rule was
       used to show [t --> t'].

          - If [t --> t'] by rule [ST_If], then [t' = if t1' then t2
            else t3] with [t1 --> t1'].  By the induction hypothesis,
            [empty |-- t1' \in Bool], and so [empty |-- t' \in T] by
            [T_If].

          - If [t --> t'] by rule [ST_IfTrue] or [ST_IfFalse], then
            either [t' = t2] or [t' = t3], and [empty |-- t' \in T]
            follows by assumption.

     - If the final step of the derivation is by [T_Sub], then there
       is a type [S] such that [S <: T] and [empty |-- t \in S].  The
       result is immediate by the induction hypothesis for the typing
       subderivation and an application of [T_Sub].  [] *)

(** TERSE: *** *)

Theorem preservation : forall t t' T,
     <{ empty |-- t \in T }> ->
     t --> t'  ->
     <{ empty |-- t' \in T }>.
(* FOLD *)
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; eauto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T0... (* QUIETSOLUTION *)
  - (* T_Fst *)
    inversion HE; subst...
    destruct (typing_inversion_pair _ _ _ _ HT) as
      [S1 [S2 [HSub [HTyp1 HTyp2]]]].
    destruct (sub_inversion_prod _ _ _ HSub) as
      [T1' [T2' [Heq [Hsub1 Hsub2]]]].
    injection Heq as Heq. subst...
  - (* T_Snd *)
    inversion HE; subst...
    destruct (typing_inversion_pair _ _ _ _ HT) as
      [S1 [S2 [HSub [HTyp1 HTyp2]]]].
    destruct (sub_inversion_prod _ _ _ HSub) as
      [T1' [T2' [Heq [Hsub1 Hsub2]]]].
    injection Heq as Heq. subst...
(* /QUIETSOLUTION *)
Qed.
(* /FOLD *)

(* FULL *)
(** ** Records, via Products and Top *)

(** This formalization of the STLC with subtyping omits record
    types for brevity.  If we want to deal with them more seriously,
    we have two choices.

    First, we can treat them as part of the core language, writing
    down proper syntax, typing, and subtyping rules for them.  Chapter
    [RecordSub] shows how this extension works.

    On the other hand, if we are treating them as a derived form that
    is desugared in the parser, then we shouldn't need any new rules:
    we should just check that the existing rules for subtyping product
    and [Unit] types give rise to reasonable rules for record
    subtyping via this encoding. To do this, we just need to make one
    small change to the encoding described earlier: instead of using
    [Unit] as the base case in the encoding of tuples and the "don't
    care" placeholder in the encoding of records, we use [Top].  So:
<<
    {a:Nat, b:Nat} ----> {Nat,Nat}       i.e., (Nat,(Nat,Top))
    {c:Nat, a:Nat} ----> {Nat,Top,Nat}   i.e., (Nat,(Top,(Nat,Top)))
>>
    The encoding of record values doesn't change at all.  It is
    easy (and instructive) to check that the subtyping rules above are
    validated by the encoding. *)
(* LATER: Perhaps it would be good to say something about subtyping
   for other constructors, like lists, pairs, etc.  More ambitious
   would be to say something about references, arrays, etc. *)
(* /FULL *)

(* FULL *)
(* ###################################################### *)
(** ** Exercises *)

(* EX2M (variations) *)
(** Each part of this problem suggests a different way of changing the
    definition of the STLC with Unit and subtyping.  (These changes
    are not cumulative: each part starts from the original language.)
    In each part, list which properties (Progress, Preservation, both,
    or neither) become false.  If a property becomes false, give a
    counterexample.

    - Suppose we add the following typing rule:
[[[
                           <{ Gamma |-- t \in S1->S2
                    S1 <: T1     T1 <: S1      S2 <: T2
                    -----------------------------------     (T_Funny1)
                           <{ Gamma |-- t \in T1->T2
]]]
(* QUIETSOLUTION *) Answer: NONE
(* /QUIETSOLUTION *)
    - Suppose we add the following reduction rule:
[[[
                             --------------------          (ST_Funny2)
                             unit --> (\x:Top. x)
]]]
(* QUIETSOLUTION *) Answer: Preservation fails.  For example, [unit]
      has type [Unit] but steps to [(\x:Top. x)], which does not have
      type [Unit].
(* /QUIETSOLUTION *)
    - Suppose we add the following subtyping rule:
[[[
                               ----------------            (S_Funny3)
                               Unit <: Top->Top
]]]
(* QUIETSOLUTION *) Answer: Progress fails.  For example,
      [unit (\x:Top,Top)] is well typed but stuck.
(* /QUIETSOLUTION *)
    - Suppose we add the following subtyping rule:
[[[
                               ----------------            (S_Funny4)
                               Top->Top <: Unit
]]]
(* QUIETSOLUTION *) Answer: NONE
(* /QUIETSOLUTION *)
    - Suppose we add the following reduction rule:
[[[
                             ---------------------        (ST_Funny5)
                             (unit t) --> (t unit)
]]]
(* QUIETSOLUTION *) Answer: NONE
(* /QUIETSOLUTION *)
    - Suppose we add the same reduction rule _and_ a new typing rule:
[[[
                             ---------------------        (ST_Funny5)
                             (unit t) --> (t unit)

                           ---------------------------     (T_Funny6)
                           empty |-- unit \in Top->Top
]]]
(* QUIETSOLUTION *) Answer: Preservation fails. For example,
      [unit (\x:A,x)] has type [Top], but it steps to [(\x:A,x) unit],
      which is ill typed,
(* /QUIETSOLUTION *)
    - Suppose we _change_ the arrow subtyping rule to:
[[[
                          S1 <: T1   S2 <: T2
                          -------------------              (S_Arrow')
                          S1->S2 <: T1->T2
]]]
(* QUIETSOLUTION *) Answer: Preservation fails.  For example,
      [(\x:Unit*Unit, x.fst) unit] has type [Unit], but steps to
      [unit.fst] which is ill typed. (In order to type
      [(\x:Unit*Unit, x.fst) unit] we use [T_Sub] twice; once to give
      [unit] the type [Top], and once to give [\x:Unit*Unit, x.fst]
      the type [Top -> Unit] using [S_Arrow']).
(* /QUIETSOLUTION *)
*)

(* GRADE_MANUAL 2: variations *)
(** [] *)

(* ###################################################################### *)
(** * Exercise: Adding Products *)

(* EX5M (products) *)
(** Adding pairs, projections, and product types to the system we have
    defined is a relatively straightforward matter.  Carry out this
    extension by modifying the definitions and proofs above:

    - Constructors for pairs, first and second projections, and
      product types have already been added to the definitions of
      [ty] and [tm].  Also, the definition of substitution has been
      extended.

    - Extend the surrounding definitions accordingly (refer to chapter
      \CHAP{MoreSTLC}):

        - value relation
        - operational semantics
        - typing relation

    - Extend the subtyping relation with this rule:
[[[
                        S1 <: T1    S2 <: T2
                        --------------------   (S_Prod)
                         S1 * S2 <: T1 * T2
]]]

    - Extend the proofs of progress, preservation, and all their
      supporting lemmas to deal with the new constructs.  (You'll also
      need to add a couple of completely new lemmas.) *)

(** INSTRUCTORS: Summary of things to check:

    - [step] should have six new rules related to products.

    - [subtype] should have the one more rule given above.

    - [has_type] should have three more rules for [pair], [fst], [snd].

    - [progress] should be [Qed]. Also look for the
      [canonical_forms_of_product_types] (or whatever the student named it)
      in the proof.

    - [preservation] should be [Qed]. Also look for inversion lemmas for the
      new constructs.
*)

(* SOLUTION *)
(* The solution can be found in-line earlier in this chapter. *)
(* /SOLUTION *)

(* GRADE_MANUAL 2: products_value_step *)
(* GRADE_MANUAL 2: products_subtype_has_type *)
(* GRADE_MANUAL 3: products_progress *)
(* GRADE_MANUAL 3: products_preservation *)
(** [] *)
(* /FULL *)

(* LATER: Another great hard exercise (probably just for the advanced
   track) is to get them to figure out how to add sums and case.  Note
   that this gets into thinking about joins, if you extend it to the
   algorithmic version. *)

(* FULL *)
(** ** Formalized "Thought Exercises" *)

(** The following are formal exercises based on the previous "thought
    exercises." *)

Module FormalThoughtExercises.
Import Examples.
Notation p := "p".
Notation a := "a".

Definition TF P := P \/ ~P.

(* EX1? (formal_subtype_instances_tf_1a) *)
Theorem formal_subtype_instances_tf_1a:
  TF (forall S T U V, S <: T -> U <: V ->
         <{{ T->S }}> <: <{{ T->S }}>).
Proof.
  (* ADMITTED *)
  left. intros S T U V S_sub_T U_sub_V.
  apply S_Arrow.
  * apply S_Refl.
  * apply S_Refl.
Qed. (* /ADMITTED *)
(** [] *)

(* EX1? (formal_subtype_instances_tf_1b) *)
Theorem formal_subtype_instances_tf_1b:
  TF (forall S T U V, S <: T -> U <: V ->
         <{{ Top->U }}> <: <{{ S->Top }}>).
Proof.
  (* ADMITTED *)
  left. intros S T U V S_sub_T U_sub_V.
  apply S_Arrow.
  * apply S_Top.
  * apply S_Top.
Qed. (* /ADMITTED *)
(** [] *)

(* EX1? (formal_subtype_instances_tf_1c) *)
Theorem formal_subtype_instances_tf_1c:
  TF (forall S T U V, S <: T -> U <: V ->
         <{{ (C->C)->(A*B) }}> <: <{{ (C->C)->(Top*B) }}>).
Proof.
  (* ADMITTED *)
  left. intros S T U V S_sub_T U_sub_V.
  apply S_Arrow.
  * apply S_Arrow.
    ** apply S_Refl.
    ** apply S_Refl.
  * apply S_Prod.
    ** apply S_Top.
    ** apply S_Refl.
Qed. (* /ADMITTED *)
(** [] *)

(* EX1? (formal_subtype_instances_tf_1d) *)
Theorem formal_subtype_instances_tf_1d:
  TF (forall S T U V, S <: T -> U <: V ->
         <{{ T->(T->U) }}> <: <{{ S->(S->V) }}>).
Proof.
  (* ADMITTED *)
  left. intros S T U V S_sub_T U_sub_V.
  apply S_Arrow.
  * apply S_sub_T.
  * apply S_Arrow.
    ** apply S_sub_T.
    ** apply U_sub_V.
Qed. (* /ADMITTED *)
(** [] *)

(* EX1? (formal_subtype_instances_tf_1e) *)
Theorem formal_subtype_instances_tf_1e:
  TF (forall S T U V, S <: T -> U <: V ->
         <{{ (T->T)->U }}> <: <{{ (S->S)->V }}>).
Proof.
  (* ADMITTED *)
  right. intros C.
  assert (H: <{{ (Top->Top)->Bool }}> <: <{{ (Bool->Bool)->Top }}>).
  { apply C.
    * apply S_Top.
    * apply S_Top. }
  destruct (sub_inversion_arrow _ _ _ H) as [U1 [U2 [H0 [H1 H2]]]].
  inversion H0; subst.
  destruct (sub_inversion_arrow _ _ _ H1) as [V1 [V2 [H3 [H4 H5]]]].
  inversion H3; subst.
  apply sub_inversion_Bool in H4. inversion H4.
Qed. (* /ADMITTED *)
(** [] *)

(* EX1? (formal_subtype_instances_tf_1f) *)
Theorem formal_subtype_instances_tf_1f:
  TF (forall S T U V, S <: T -> U <: V ->
         <{{ ((T->S)->T)->U }}> <: <{{ ((S->T)->S)->V }}>).
Proof.
  (* ADMITTED *)
  left. intros S T U V S_sub_T U_sub_V.
  apply S_Arrow.
  * apply S_Arrow.
    ** apply S_Arrow.
       *** apply S_sub_T.
       *** apply S_sub_T.
    ** apply S_sub_T.
  * apply U_sub_V.
Qed. (* /ADMITTED *)
(** [] *)

(* EX1? (formal_subtype_instances_tf_1g) *)
Theorem formal_subtype_instances_tf_1g:
  TF (forall S T U V, S <: T -> U <: V ->
         <{{ S*V }}> <: <{{ T*U }}>).
Proof.
  (* ADMITTED *)
  right. intros C.
  assert (H: <{{ Bool*Top }}> <: <{{ Top*Bool }}>).
  { apply C.
    * apply S_Top.
    * apply S_Top. }
  destruct (sub_inversion_prod _ _ _ H) as [U1 [U2 [H0 [H1 H2]]]].
  inversion H0; subst.
  apply sub_inversion_Bool in H2. inversion H2.
Qed. (* /ADMITTED *)
(** [] *)

(* EX2? (formal_subtype_instances_tf_2a) *)
Theorem formal_subtype_instances_tf_2a:
  TF (forall S T,
         S <: T ->
         <{{ S->S }}> <: <{{ T->T }}>).
Proof.
  (* ADMITTED *)
  right. intros C.
  assert (H: <{{ Bool->Bool }}> <: <{{ Top->Top }}>).
  { apply C. apply S_Top. }
  destruct (sub_inversion_arrow _ _ _ H) as [U1 [U2 [H0 [H1 H2]]]].
  inversion H0; subst.
  apply sub_inversion_Bool in H1. inversion H1.
Qed. (* /ADMITTED *)
(** [] *)

(* EX2? (formal_subtype_instances_tf_2b) *)
Theorem formal_subtype_instances_tf_2b:
  TF (forall S,
         S <: <{{ A->A }}> ->
         exists T,
           S = <{{ T->T }}> /\ T <: A).
Proof.
  (* ADMITTED *)
  right. intros C.
  destruct (C <{{ Top->A }}>) as [T [H0 H1]].
  { apply S_Arrow; [ apply S_Top | apply S_Refl ]. }
  inversion H0; subst. inversion H3.
Qed. (* /ADMITTED *)
(** [] *)

(* EX2? (formal_subtype_instances_tf_2d) *)
(** Hint: Assert a generalization of the statement to be proved and
    use induction on a type (rather than on a subtyping
    derviation). *)
Theorem formal_subtype_instances_tf_2d:
  TF (exists S,
         S <: <{{ S->S }}>).
Proof.
  (* ADMITTED *)
  assert (G: forall S T, ~(S <: <{{ T->S }}>)).
  { unfold not. induction S; intros T H.
    - destruct (sub_inversion_arrow _ _ _ H) as [? [? [? [? ?]]]]; discriminate.
    - destruct (sub_inversion_arrow _ _ _ H) as [? [? [? [? ?]]]]; discriminate.
    - destruct (sub_inversion_arrow _ _ _ H) as [? [? [? [? ?]]]]; discriminate.
    - destruct (sub_inversion_arrow _ _ _ H) as [S1' [S2' [? [? ?]]]].
      injection H0 as ? ?; subst.
      eapply IHS2. apply H2.
    - destruct (sub_inversion_arrow _ _ _ H) as [? [? [? [? ?]]]]; discriminate.
    - destruct (sub_inversion_arrow _ _ _ H) as [? [? [? [? ?]]]]; discriminate. }
  right. intros [S H].
  apply G in H. assumption.
Qed. (* /ADMITTED *)
(** [] *)

(* EX2? (formal_subtype_instances_tf_2e) *)
Theorem formal_subtype_instances_tf_2e:
  TF (exists S,
         <{{ S->S }}> <: S).
Proof.
  (* ADMITTED *)
  left. exists <{{ Top }}>. apply S_Top.
Qed. (* /ADMITTED *)
(** [] *)

(* EX2? (formal_subtype_concepts_tfa) *)
Theorem formal_subtype_concepts_tfa:
  TF (exists T, forall S, S <: T).
Proof.
  (* ADMITTED *)
  left. exists <{{ Top }}>. intros S. apply S_Top.
Qed. (* /ADMITTED *)
(** [] *)

(* EX2? (formal_subtype_concepts_tfb) *)
Theorem formal_subtype_concepts_tfb:
  TF (exists T, forall S, T <: S).
Proof.
  (* ADMITTED *)
  right. intros [T H].
  assert (T = <{{ Bool }}>) by (apply sub_inversion_Bool; auto).
  assert (T = <{{ Unit }}>) by (apply sub_inversion_Unit; auto).
  congruence.
Qed. (* /ADMITTED *)
(** [] *)

(* EX2? (formal_subtype_concepts_tfc) *)
Theorem formal_subtype_concepts_tfc:
  TF (exists T1 T2, forall S1 S2, <{{ S1*S2 }}> <: <{{ T1*T2 }}>).
Proof.
  (* ADMITTED *)
  left. exists <{{ Top }}>. exists <{{ Top }}>. intros S1 S2.
  apply S_Prod; apply S_Top.
Qed. (* /ADMITTED *)
(** [] *)

(* EX2? (formal_subtype_concepts_tfd) *)
Theorem formal_subtype_concepts_tfd:
  TF (exists T1 T2, forall S1 S2, <{{ T1*T2 }}> <: <{{ S1*S2 }}>).
Proof.
  (* ADMITTED *)
  right. intros [T1 [T2 H]].
  destruct (sub_inversion_prod _ _ _ (H <{{ Bool }}> <{{ Bool }}>)) as [U1 [U2 [H1 [H2 H3]]]].
  inversion H1; subst.
  destruct (sub_inversion_prod _ _ _ (H <{{ Unit }}> <{{ Unit }}>)) as [V1 [V2 [H4 [H5 H6]]]].
  inversion H4; subst.
  assert (V1 = <{{ Bool }}>) by (apply sub_inversion_Bool; auto).
  assert (V1 = <{{ Unit }}>) by (apply sub_inversion_Unit; auto).
  congruence.
Qed. (* /ADMITTED *)
(** [] *)

(* EX2? (formal_subtype_concepts_tfe) *)
Theorem formal_subtype_concepts_tfe:
  TF (exists T1 T2, forall S1 S2, <{{ S1->S2 }}> <: <{{ T1->T2 }}>).
Proof.
  (* ADMITTED *)
  right. intros [T1 [T2 H]].
  destruct (sub_inversion_arrow _ _ _ (H <{{ Bool }}> <{{ Bool }}>)) as [U1 [U2 [H1 [H2 H3]]]].
  inversion H1; subst.
  destruct (sub_inversion_arrow _ _ _ (H <{{ Unit }}> <{{ Unit }}>)) as [V1 [V2 [H4 [H5 H6]]]].
  inversion H4; subst.
  assert (T1 = <{{ Bool }}>) by (apply sub_inversion_Bool; auto).
  assert (T1 = <{{ Unit }}>) by (apply sub_inversion_Unit; auto).
  congruence.
Qed. (* /ADMITTED *)
(** [] *)

(* EX2? (formal_subtype_concepts_tff) *)
Theorem formal_subtype_concepts_tff:
  TF (exists T1 T2, forall S1 S2, <{{ T1->T2 }}> <: <{{ S1->S2 }}>).
Proof.
  (* ADMITTED *)
  right. intros [T1 [T2 H]].
  destruct (sub_inversion_arrow _ _ _ (H <{{ Bool }}> <{{ Bool }}>)) as [U1 [U2 [H1 [H2 H3]]]].
  inversion H1; subst.
  destruct (sub_inversion_arrow _ _ _ (H <{{ Unit }}> <{{ Unit }}>)) as [V1 [V2 [H4 [H5 H6]]]].
  inversion H4; subst.
  assert (V2 = <{{ Bool }}>) by (apply sub_inversion_Bool; auto).
  assert (V2 = <{{ Unit }}>) by (apply sub_inversion_Unit; auto).
  congruence.
Qed. (* /ADMITTED *)
(** [] *)

(* EX2? (formal_subtype_concepts_tfg) *)
(* QUIETSOLUTION *)
Fixpoint inf_desc_chain (n: nat) :=
  match n with
    | O => <{{ Top }}>
    | S n => <{{ Top->$(inf_desc_chain n) }}>
  end.
(* /QUIETSOLUTION *)
Theorem formal_subtype_concepts_tfg:
  TF (exists f : nat -> ty,
         (forall i j, i <> j -> f i <> f j) /\
         (forall i, f (S i) <: f i)).
Proof.
  (* ADMITTED *)
  left. exists inf_desc_chain. split.
  { induction i as [|i']; simpl; intros j H; intro C.
    - destruct j as [|j']; simpl in C; try solve_by_invert; auto.
    - destruct j as [|j']; simpl in C; try solve_by_invert.
      assert (H': i' <> j') by auto.
      apply IHi' in H'.
      congruence. }
  { induction i; simpl; auto. }
Qed. (* /ADMITTED *)
(** [] *)

(* EX2? (formal_subtype_concepts_tfh) *)
Theorem formal_subtype_concepts_tfh:
  TF (exists f : nat -> ty,
         (forall i j, i <> j -> f i <> f j) /\
         (forall i, f i <: f (S i))).
Proof.
  (* ADMITTED *)
  left. exists (fun n => <{{ $(inf_desc_chain n)->Top }}>). split.
  { induction i as [|i']; simpl; intros j H; intro C.
    - destruct j as [|j']; simpl in C; try solve_by_invert; auto.
    - destruct j as [|j']; simpl in C; try solve_by_invert.
      assert (H': i' <> j') by auto.
      apply IHi' in H'.
      congruence. }
  { induction i; simpl in *.
    { auto. }
    { destruct (sub_inversion_arrow _ _ _ IHi) as [U1 [U2 [? [? ?]]]].
      inversion H; subst; auto. } }
Qed. (* /ADMITTED *)
(** [] *)

(* EX3? (formal_proper_subtypes) *)
Theorem formal_proper_subtypes:
  TF (forall T,
         ~(T = <{{ Bool }}> \/ (exists n, T = <{{ Base n }}>) \/ T = <{{ Unit }}>) ->
         exists S,
           S <: T /\ S <> T).
Proof.
  (* ADMITTED *)
  right. intros H.
  assert (exists S : ty, S <: <{{ Top->Bool }}> /\ S <> <{{ Top->Bool }}>) as [S [? ?]].
  { apply H. intros [C|[[x C]|C]]; inversion C. }
  destruct (sub_inversion_arrow _ _ _ H0) as [U1 [U2 [? [? ?]]]].
  apply sub_inversion_Bool in H4.
  apply sub_inversion_Top in H3.
  subst. apply H1. reflexivity.
Qed. (* /ADMITTED *)
(** [] *)

(* HIDE *)
(** *Note*: This definition does not quite say the right thing. It
    needs to be fixed, but that will take a little work, so until that
    happens...

    - The first clause is OK, though stated in a perhaps-unintuitive
      way.  If the set of types satisfying the constraint HT has a
      least and greatest element, then a given type T satisfies HT iff
      it lies between these.

    - The other clauses are wrong: For example, the first conjunct of
      the fourth clause -- [~(exists TS, forall T, TS <: T <-> HT
      T)] -- does not say that the set of types T satisfying HT has no
      least element; it says that there is no type TS such that
      *every* supertype of TS satisfies HT.

      But consider the expression [(\x:T. (\z:A.z) x)], which is well
      typed when [T=A] but ill-typed for every other choice for [T] --
      in particular, for [T=Top].  So [A] is indeed the smallest type
      that makes the expression well typed, but it's not the case that
      every type larger than [A] also makes the expression well typed.

    Many thanks to Charles Averill for bringing this issue to our
    attention! *)
Definition smallest_largest HT :=
  (* There exists a smallest and a largest. *)
  (exists TS TL, forall T, TS <: T /\ T <: TL <-> HT T)
  \/
  (* There exists a smallest, but no largest. *)
  ((exists TS, forall T, TS <: T <-> HT T) /\
   ~(exists TL, forall T, T <: TL <-> HT T))
  \/
  (* There exists a largest, but not smallest. *)
  (~(exists TS, forall T, TS <: T <-> HT T) /\
   (exists TL, forall T, T <: TL <-> HT T))
  \/
  (* There exists neither a smallest nor a largest. *)
  (~(exists TS, forall T, TS <: T <-> HT T) /\
   ~(exists TL, forall T, T <: TL <-> HT T)).
(* /HIDE *)

(* HIDE *)
(* SOONER: Some potential warm-up problems, from *)
(* charlesaverill20@gmail.com *)

(*
(* Smallest and largest *)
Example warmup_sl :
  smallest_largest
    (fun T => empty |-- (unit, unit) \in <{{ T * T }}>).
Proof.
  left. exists <{{ Unit }}>, <{{ Top }}>.
  intro. split.
  - intros [TS TL]. eauto.
  - intro. apply typing_inversion_pair in H. destruct H as
      [T1 [T2 [Ty1 [Ty2 Sub]]]]. destruct (sub_inversion_Prod _ _ _ Sub)
        as [U1 [U2 [Eq [Sub1 Sub2]]]]. inversion Eq; subst; clear Eq.
    apply typing_inversion_unit in Ty1; eauto.
Qed.

(* Largest but no smallest *)
Example warmup_l :
  smallest_largest
    (fun T => empty |-- \p:A, p \in <{{ T->T }}>).
Proof.
  right. right. left. split.
  - intros [TS contra]. specialize (contra <{{ Top }}>).
    assert (empty |-- \ "p" : A, "p" \in (Top -> Top)).
      now apply contra.
    apply typing_inversion_abs in H. destruct H as
      [S2 [Sub Typ]]. destruct (sub_inversion_arrow _ _ _ Sub)
      as [U1 [U2 [Eq [Sub1 Sub2]]]]. inversion Eq; subst.
    apply sub_inversion_Top in Sub1. inversion Sub1.
  - exists <{{ A }}>. intro. split; intro.
    -- apply sub_inversion_Base in H. subst; auto.
    -- apply typing_inversion_abs in H. destruct H as
        [S2 [Sub Typ]]. destruct (sub_inversion_arrow _ _ _ Sub)
          as [U1 [U2 [Eq [Sub1 Sub2]]]]. now inversion Eq; subst.
Qed.
*)
(* /HIDE *)

(* HIDE *)
(* EX3A? (formal_small_large_1) *)
Theorem formal_small_large_1:
  smallest_largest
  (fun T =>
   <{ empty |--  (\p:T*Top, p.fst) ((\z:A, z), unit)\in  A->A }>).
Proof.
  (* ADMITTED *)
  left. exists <{{ A->A }}>. exists <{{ A->A }}>.
  intros T. split.
  * intros [HS HL].
    { apply T_Sub with T.
      { apply T_App with <{{ (A->A)*Top }}>.
        { apply T_Sub with <{{ (T*Top)->T }}>.
          { apply T_Abs.
            { eapply T_Fst with <{{ Top }}>.
              { apply T_Var; auto. } } }
          { apply S_Arrow.
            { apply S_Prod.
              { apply HS. }
              { apply S_Refl. } }
            { apply S_Refl. } } }
        { apply T_Pair.
          { apply T_Abs.
            { apply T_Var; auto. } }
          { apply T_Sub with <{{ Unit }}>.
            { apply T_Unit. }
            { apply S_Top. } } } }
      { apply HL. } }
  * intros H.
    apply typing_inversion_app in H as [T1 [ ? ? ]].
    apply typing_inversion_abs in H as [T2 [? ?]].
    apply typing_inversion_fst in H1 as [T3 [T4 [? ?]]].
    apply typing_inversion_var in H2 as [T5 [? ?]].
    inversion H2; subst; clear H2.
    apply typing_inversion_pair in H0 as [T6 [T7 [ ? [ ? ? ]]]].
    apply typing_inversion_abs in H2 as [T8 [? ?]].
    apply typing_inversion_var in H5 as [T9 [? ?]].
    inversion H5; subst; clear H5.
    apply typing_inversion_unit in H4.
    destruct (sub_inversion_arrow _ _ _ H) as [U1 [U2 [? [? ?]]]]; clear H; subst.
    inversion H5; subst; clear H5.
    destruct (sub_inversion_prod _ _ _ H3) as [U3 [U4 [? [? ?]]]]; clear H3; subst.
    inversion H; subst; clear H.
    destruct (sub_inversion_prod _ _ _ H7) as [U5 [U6 [? [? ?]]]]; clear H7; subst.
    destruct (sub_inversion_prod _ _ _ H0) as [U7 [U8 [? [? ?]]]]; clear H4; subst.
    inversion H; subst; clear H.
    split.
    ** { apply S_Trans with <{{ A->T8 }}>.
         { apply S_Arrow.
           { apply S_Refl. }
           { assumption. } }
         { apply S_Trans with U7.
           { assumption. }
           { apply S_Trans with U5.
             { assumption. }
             { assumption. } } } }
    ** { apply S_Trans with T3.
         { assumption. }
         { apply S_Trans with U2.
           { assumption. }
           { assumption. } } }
Qed. (* /ADMITTED *)
(** [] *)

(* EX3A? (formal_small_large_2) *)
Theorem formal_small_large_2:
  smallest_largest
  (fun T =>
   <{ empty |-- (\p:(A->A)*(B->B), p) ((\z:A, z), (\z:B, z)) \in T }>).
Proof.
  (* ADMITTED *)
  left. exists <{{ (A->A)*(B->B) }}>. exists <{{ Top }}>.
  intros T. split.
  * intros [HS HL].
    { apply T_App with <{{ (A->A)*(B->B) }}>.
      { apply T_Abs.
        { apply T_Sub with <{{ (A->A)*(B->B) }}>.
          { apply T_Var; auto. }
          { apply HS. } } }
      { apply T_Pair.
        { apply T_Abs.
          { apply T_Var; auto. } }
        { apply T_Abs.
          { apply T_Var; auto. } } } }
  * intros H.
    apply typing_inversion_app in H as [T1 [ ? ? ]].
    apply typing_inversion_abs in H as [T2 [? ?]].
    apply typing_inversion_var in H1 as [T3 [? ?]].
    inversion H1; subst; clear H1.
    apply typing_inversion_pair in H0 as [T4 [T5 [ ? [ ? ? ]]]].
    apply typing_inversion_abs in H1 as [T6 [? ?]].
    apply typing_inversion_var in H4 as [T7 [? ?]].
    inversion H4; subst; clear H4.
    apply typing_inversion_abs in H3 as [T8 [? ?]].
    apply typing_inversion_var in H4 as [T9 [? ?]].
    inversion H4; subst; clear H4.
    destruct (sub_inversion_arrow _ _ _ H) as [U1 [U2 [? [? ?]]]]; clear H; subst.
    inversion H4; subst; clear H4.
    split.
    ** { apply S_Trans with U2.
         { assumption. }
         { assumption. } }
    ** { apply S_Top. }
Qed. (* /ADMITTED *)
(** [] *)

(* EX4A? (formal_small_large_3) *)
Theorem formal_small_large_3:
  smallest_largest
  (fun T =>
   <{ a |-> A |-- (\p:A*T, (p.snd) (p.fst)) (a, \z:A, z) \in A }>).
Proof.
  (* ADMITTED *)
  left. exists <{{ A->A }}>. exists <{{ A->A }}>.
  intros T. split.
  * intros [HS HL].
    { apply T_App with <{{ A*T }}>.
      { apply T_Abs.
        { apply T_App with A.
          { apply T_Snd with A.
            { apply T_Sub with <{{ A*T }}>.
              { apply T_Var; auto. }
              { apply S_Prod.
                { apply S_Refl. }
                { apply HL. } } } }
          { apply T_Fst with T.
            { apply T_Var; auto. } } } }
      { apply T_Pair.
        { apply T_Var; auto. }
        { apply T_Sub with <{{ A->A }}>.
          { apply T_Abs.
            { apply T_Var; auto. } }
          { apply HS. } } } }
  * intros H.
    apply typing_inversion_app in H as [T1 [ ? ? ]].
    apply typing_inversion_abs in H as [T2 [ ? ? ]].
    apply typing_inversion_app in H1 as [T3 [ ? ? ]].
    apply typing_inversion_snd in H1 as [T4 [ T5 [ ? ? ]]].
    apply typing_inversion_var in H3 as [T6 [ ? ? ]].
    inversion H3; subst; clear H3.
    apply typing_inversion_fst in H2 as [T7 [ T8 [ ? ? ]]].
    apply typing_inversion_var in H3 as [T9 [ ? ? ]].
    inversion H3; subst; clear H3.
    apply typing_inversion_pair in H0 as [T10 [T11 [? [? ?]]]].
    apply typing_inversion_var in H3 as [T12 [ ? ? ]].
    inversion H3; subst; clear H3.
    apply typing_inversion_abs in H6 as [T13 [ ? ? ]].
    apply typing_inversion_var in H6 as [T14 [ ? ? ]].
    inversion H6; subst; clear H6.
    destruct (sub_inversion_arrow _ _ _ H) as [U1 [U2 [? [? ?]]]]; subst; clear H.
    inversion H6; subst; clear H6.
    destruct (sub_inversion_prod _ _ _ H4) as [U3 [U4 [? [? ?]]]]; subst; clear H4.
    inversion H; subst; clear H.
    destruct (sub_inversion_arrow _ _ _ H1) as [U5 [U6 [? [? ?]]]]; subst; clear H1.
    destruct (sub_inversion_prod _ _ _ H5) as [U7 [U8 [? [? ?]]]]; subst; clear H5.
    inversion H; subst; clear H.
    destruct (sub_inversion_prod _ _ _ H9) as [U9 [U10 [? [? ?]]]]; subst; clear H9.
    destruct (sub_inversion_arrow _ _ _ H11) as [U11 [U12 [? [? ?]]]]; subst; clear H11.
    destruct (sub_inversion_prod _ _ _ H0) as [U13 [U14 [? [? ?]]]]; subst; clear H0.
    inversion H; subst; clear H.
    destruct (sub_inversion_arrow _ _ _ H14) as [U15 [U16 [? [? ?]]]]; subst; clear H14.
    destruct (sub_inversion_arrow _ _ _ H16) as [U17 [U18 [? [? ?]]]]; subst; clear H16.
    destruct (sub_inversion_arrow _ _ _ H3) as [U19 [U20 [? [? ?]]]]; subst; clear H3.
    inversion H; subst; clear H.
    split.
    ** { apply S_Arrow.
         { eapply S_Trans; [|eapply S_Trans].
           { apply H0. }
           { apply H14. }
           { apply H16. } }
         { eapply S_Trans; [|eapply S_Trans;[|eapply S_Trans]].
           { apply H8. }
           { apply H19. }
           { apply H18. }
           { apply H17. } } }
    ** { apply S_Arrow.
         { eapply S_Trans; [|eapply S_Trans; [|eapply S_Trans]].
           { apply H1. }
           { apply H2. }
           { apply H4. }
           { apply H9. } }
         { eapply S_Trans; [|eapply S_Trans].
           { apply H15. }
           { apply H12. }
           { apply H10. } } }
Qed. (* /ADMITTED *)
(** [] *)

(* EX4A? (formal_small_large_4) *)
Theorem formal_small_large_4:
  smallest_largest
  (fun T =>
   exists S,
     <{ empty |-- \p:A*T, (p.snd) (p.fst) \in S }>).
Proof.
  (* ADMITTED *)
  right. right. left. split.
  - intros [TS ?].
    assert (TS <: <{{ Top->A }}>).
    { apply H. exists <{{ (A*(Top->A))->A }}>.
      { apply T_Abs.
        { apply T_App with <{{ Top }}>.
          { apply T_Snd with A.
            { apply T_Var; auto. } }
          { apply T_Sub with A.
            { apply T_Fst with <{{ Top->A }}>.
              { apply T_Var; auto. } }
            { apply S_Top. } } } } }
    assert (TS <: <{{ Top->B }}>).
    { apply H. exists <{{ (A*(Top->B))->B }}>.
      { apply T_Abs.
        { apply T_App with <{{ Top }}>.
          { apply T_Snd with A.
            { apply T_Var; auto. } }
          { apply T_Sub with A.
            { apply T_Fst with <{{ Top->B }}>.
              { apply T_Var; auto. } }
            { apply S_Top. } } } } }
    destruct (sub_inversion_arrow _ _ _ H0) as [U1 [U2 [? [? ?]]]]; subst; clear H0.
    destruct (sub_inversion_arrow _ _ _ H1) as [U3 [U4 [? [? ?]]]]; subst; clear H1.
    inversion H0; subst; clear H0.
    apply sub_inversion_Base in H5; subst.
    apply sub_inversion_Base in H4; subst.
    inversion H4.
  - exists <{{ A->Top }}>.
    intros T. split.
    * intros HL.
      exists <{{ (A*T)->Top }}>.
      { apply T_Abs.
        { apply T_App with A.
          { apply T_Snd with A.
            { apply T_Sub with <{{ A*T }}>.
              { apply T_Var; auto. }
              { apply S_Prod.
                { apply S_Refl. }
                { apply HL. } } } }
          { apply T_Fst with T.
            { apply T_Var; auto. } } } }
    * intros [S H].
      apply typing_inversion_abs in H as [T1 [ ? ? ]].
      apply typing_inversion_app in H0 as [T2 [ ? ? ]].
      apply typing_inversion_snd in H0 as [T3 [ T4 [ ? ? ]]].
      apply typing_inversion_var in H2 as [T5 [ ? ? ]].
      inversion H2; subst; clear H2.
      apply typing_inversion_fst in H1 as [T6 [ T7 [ ? ? ]]].
      apply typing_inversion_var in H2 as [T8 [ ? ? ]].
      inversion H2; subst; clear H2.
      destruct (sub_inversion_arrow _ _ _ H0) as [U1 [U2 [? [? ?]]]]; clear H2; subst.
      destruct (sub_inversion_prod _ _ _ H4) as [U3 [U4 [? [? ?]]]]; clear H4; subst.
      inversion H2; subst; clear H2.
      destruct (sub_inversion_prod _ _ _ H3) as [U5 [U6 [? [? ?]]]]; clear H3; subst.
      inversion H2; subst; clear H2.
      { eapply S_Trans; [eapply S_Trans|].
        { apply H9. }
        { apply H0. }
        { apply S_Arrow.
          { eapply S_Trans.
            { apply H7. }
            { apply H1. } }
          { apply S_Top. } } }
Qed. (* /ADMITTED *)
(** [] *)

Definition smallest P :=
  TF (exists TS, forall T, TS <: T <-> P T).

(* EX3? (formal_smallest_1) *)
Theorem formal_smallest_1:
  smallest
  (fun T =>
   exists S t,
     <{ empty |-- (\x:T, x x) t \in S }>).
Proof.
  (* ADMITTED *)
  right. intros [TS H].
  assert (TS <: <{{ Top->Unit }}>).
  { apply H. exists <{{ Unit }}>. exists <{ \z:Top, unit }>.
    { apply T_App with <{{ Top->Unit }}>.
      { apply T_Abs.
        { apply T_App with <{{ Top }}>.
          { apply T_Var; auto. }
          { apply T_Sub with <{{ Top->Unit }}>.
            { apply T_Var; auto. }
            { apply S_Top. } } } }
      { apply T_Abs.
        { apply T_Unit. } } } }
  assert (TS <: <{{ Top->Bool }}>).
  { apply H. exists <{{ Bool }}>. exists <{ \z:Top, true }>.
    { apply T_App with <{{ Top->Bool }}>.
      { apply T_Abs.
        { apply T_App with <{{ Top }}>.
          { apply T_Var; auto. }
          { apply T_Sub with <{{ Top->Bool }}>.
            { apply T_Var; auto. }
            { apply S_Top. } } } }
      { apply T_Abs.
        { apply T_True. } } } }
    destruct (sub_inversion_arrow _ _ _ H0) as [U1 [U2 [? [? ?]]]]; subst; clear H0.
    destruct (sub_inversion_arrow _ _ _ H1) as [U3 [U4 [? [? ?]]]]; subst; clear H1.
    inversion H0; subst; clear H0.
    apply sub_inversion_Bool in H5; subst.
    apply sub_inversion_Unit in H4; subst.
    discriminate.
Qed. (* /ADMITTED *)
(** [] *)

(* EX3? (formal_smallest_2) *)
Theorem formal_smallest_2:
  smallest
  (fun T =>
   <{ empty |-- (\x:Top, x) ((\z:A, z), (\z:B, z)) \in T }>).
Proof.
  (* ADMITTED *)
  left. exists <{{ Top }}>.
  intros T. split.
  * intros HS.
    { apply T_App with <{{ Top }}>.
      { apply T_Abs.
        { apply T_Sub with <{{ Top }}>.
          { apply T_Var; auto. }
          { apply HS. } } }
      { apply T_Sub with <{{ (A->A)*(B->B) }}>.
        { apply T_Pair.
          { apply T_Abs.
            { apply T_Var; auto. } }
          { apply T_Abs.
            { apply T_Var; auto. } } }
        { apply S_Top. } } }
  * intros H.
    apply typing_inversion_app in H as [T1 [ ? ? ]].
    apply typing_inversion_abs in H as [T2 [? ?]].
    apply typing_inversion_var in H1 as [T3 [? ?]].
    inversion H1; subst; clear H1.
    destruct (sub_inversion_arrow _ _ _ H) as [U1 [U2 [? [? ?]]]]; clear H; subst.
    inversion H1; subst; clear H1.
    { apply S_Trans with U2.
      { assumption. }
      { assumption. } }
Qed. (* /ADMITTED *)
(** [] *)
(* /HIDE *)

End FormalThoughtExercises.
(* /FULL *)

(* TERSE: HIDEFROMHTML *)
End STLCSub.
(* TERSE: /HIDEFROMHTML *)

(* HIDE *)
(* ################################################## *)
(* ############ CURRENT FILE ENDS HERE ############## *)
(* ################################################## *)

(* This bit of text is not quite there yet... *)
(**
Subtyping references and arrays results in some potential ambiguities
due to the types of the dereference and assignment
operations. Consider a reference cell containing a value of type [S],
and that [S <: T]. Can this reference cell, of type [Ref S], be used
wherever a value of type [Ref T] is expected? Yes, as long as the
recipient expecting a [Ref T] _only_ dereferences the cell. When the
cell is dereferenced, the value of type [S] can, by the definition of
subtyping, be used anywhere a value of type [T] is needed. We say that
the read-only reference cell type [RefRO] is covariant in its type
parameter as we have,

[[[
                                S <: T
                           ------------------        (Sub_RefRO)
                           RefRO S <: RefRO T
]]]

However, if a [Ref S] is provided when a [Ref T] is wanted, attempts
to assign to the cell cause things to fall apart. If the assignment is
allowed, any other use of the original reference cell will be
ill-typed as the cell will now hold a value of type [T] when an [S]
was expected, and [T] is not a subtype of [S].

Instead, assignment to references is contravariant. A reference cell
with type [Ref T] can safely be assigned a value of type [S] as long
as [S <: T], because any use of the [Ref T] will still get a suitable
value. A write-only reference cell, [RefWO], is contravariant in its
type parameter.

[[[
                              S <: T
                         ------------------          (Sub_RefWO)
                         RefWO T <: RefWO S
]]]

Putting the two sides together, we have that reading from an array or
reference cell is covariant, while writing, or assignment, is
contravariant. These two properties follow from the subtyping rule for
arrow types, and ensure that all uses of a mutable cell are well
typed.
*)

(* ################## *)
(* UNUSED / OLD STUFF *)
(*
Lemma sub_inversion_top : forall T,
  subtype Top T -> T = Top.
Proof.
  intros T Hsub.
  remember Top as S.
  induction Hsub;
    inversion HeqS; subst; try solve_by_inverts; try reflexivity.
  - (* S_Trans *)
    apply IHHsub1 in H. subst. apply IHHsub2. reflexivity.  Qed.

Lemma sub_inversion_rcd : forall Sr T,
  subtype (TRcd Sr) T ->
    T = Top \/ exists Tr, T = TRcd Tr /\ subtype Sr Tr.
Proof.
  intros Sr T Hsub.
  remember (TRcd Sr) as S. generalize dependent Sr.
  induction Hsub; intros;
    inversion HeqS; subst; try solve_by_invert.
  - (* S_Refl *)
    right. exists Sr. split. reflexivity. apply S_Refl.
  - (* S_Trans *)
    destruct (IHHsub1 _ H) as [HeqU | [Ur [HeqU HsubUr}]; subst; clear H.
    + (* U = Top *)
      apply sub_inversion_top in Hsub2. left; assumption.
    + (* U = TRcd Ur *)
      assert (TRcd Ur = TRcd Ur) as H by reflexivity.
      destruct (IHHsub2 _ H) as [HeqS | [Tr [HeqT HsubTr]]]; subst; clear H.
      * (* T = Top *)
        left. reflexivity.
      * (* T = TRcd Tr *)
        right. exists Tr. split. reflexivity. eapply S_Trans; eassumption.
  - (* S_Top *)
    left. reflexivity.
  - (* S_Rcd *)
    right. exists Tr. split. reflexivity. assumption.  Qed.

Lemma types_of_records_are_record_tys_or_top : forall Gamma tr T,
  <{{  Gamma |-- (trcd tr) \in T ->
  T = Top \/ exists Tr Sr, T = TRcd Tr /\ <{{  Gamma |-- tr \in Sr /\ subtype Sr Tr.
Proof.
  intros Gamma tr T Hty.
  remember (trcd tr) as t.
  induction Hty; inversion Heqt; subst; try solve_by_invert.
  - (* T_Rcd *)
    right. exists Tr Tr. split. reflexivity. split. assumption. apply S_Refl.
  - (* T_Sub *)
    destruct (IHHty H1) as [HeqS | [Tr [Sr [HeqS [Htyr Hsub]]]]]; subst.
    + (* S = Top *)
      apply sub_inversion_top in H0.
      left; assumption.
    + (* S = TRcd... *)
      clear IHHty.
      apply sub_inversion_rcd in H0.
      inversion H0 as [HeqT | [Tr0 [HeqT HsubTr}].
        left; assumption.
        right.
        exists Tr0, Sr. split. assumption. split. assumption.
        eapply S_Trans; eassumption.  Qed.

Lemma get_nonrow : forall Tr,
  is_ty Tr -> forall i Ti, : (Trlookup i Tr = Some Ti).
Proof.
  intros Tr Histy i Ti.
  inversion Histy; intros C; subst; simpl in C; solve_by_invert.  Qed.

Lemma supertypes_of_types_are_types : forall S T,
  subtype S T ->
  is_ty S ->
  is_ty T.
Proof.
  intros S T Hsub.
  induction Hsub; intros; auto; try solve_by_invert.
  inversion H; subst; inversion H0.
Qed.
*)

(* ###################################################################### *)
(** * Algorithmic Subtyping -- Motivations *)

(*

(* FIX: THIS IS FROM LAST YEAR, IN CASE IT'S USEFUL... *)

(* We've done a lot of work over the past several weeks with
   DEFINITIONS of programming languages -- formal, abstract
   descriptions of their syntax, operational semantics, and
   typing rules such as might be included in a language
   reference manual.  We have also looked at IMPLEMENTATIONS
   of syntax and operational semantics (as evaluation
   functions), but we have not yet considered how to
   implement the typing and subtyping relations.

   For the plain simply typed lambda-calculus (without
   subtyping), implementing a typechecker is
   straightforward.  Notice that the typing relation for
   this system...

      Inductive typing : context -> tm -> ty -> Prop :=
        | T_Var : forall Gamma x T,
               binds _ x T Gamma  ->
               Gamma |-- (!x) \in T
        | T_Abs : forall Gamma x T1 T2 t,
               [(x,T1)] ++ Gamma |-- t \in T2 ->
               Gamma |-- (\x:T1, t) : T1->T2
        | T_App : forall S T Gamma t1 t2,
               Gamma |-- t1 \in (S->T) ->
               Gamma |-- t2 \in S ->
               Gamma |-- (t1 @ t2) \in T
        | T_Rcdnil : forall Gamma,
               Gamma |-- trcdnil \in TRcdnil
        | T_Rcdcons : forall Gamma k t1 t2 T1 T2,
               Gamma |-- t1 \in T1 ->
               Gamma |-- t2 \in T2 ->
               record_ty T2 ->
               Gamma |-- {k=t1;t2} \in [{k:T1;T2}]
        | T_Proj : forall Gamma k Tk t T,
               Gamma |-- t \in T ->
               record_ty T ->
               type_rcd_binds k Tk T ->
               Gamma |-- t # k \in Tk

   ... is SYNTAX-DIRECTED: For each syntactic form of the
   language, there is exactly one typing rule that can be
   used to type expressions of this form.  Moreover, all of
   the metavariables that appear in premises of this rule
   also appear in the conclusion, so it is easy to write out
   a Fixpoint definition that "runs the rules backwards"
   without having to do any hard work to fill in
   metavariables on recursive calls:

    Fixpoint check_typing Gamma t : option ty :=
      match t with
      | !x =>
           lookup _ x Gamma
      | \x:T1,t2 =>
           check_typing ([(x,T1)] ++ Gamma) t2
      | t1 @ t2 =>
           match check_typing Gamma t1 with
           | Some (T11->T12) =>
               match check_typing Gamma t2 with
               | Some T2 =>
                   if check_eqty T2 T11
                     then Some T12
                     else None
               | None => None
               end
           | _ => None
           end
      | trcdnil =>
          Some TRcdnil
      | {k=t1;t2} =>
           match check_typing Gamma t1 with
           | Some T1 =>
               match check_typing Gamma t2 with
               | Some T2 =>
                   let T := [{k:T1;T2}] in
                   if check_well_formed T
                     then Some T
                     else None
               | None => None
               end
           | _ => None
           end
      | t1 # k =>
           match check_typing Gamma t1 with
           | Some T1 => TRcd_lookup k T1
           | None => None
           end
      end.

   When we add subtyping, however, things become a little
   more complicated and we need to work a little harder to
   implement what we have defined.  The problem, of course,
   is the addition of the rule of SUBSUMPTION

           | T_Sub : forall Gamma t S T,
                  Gamma |-- t \in S ->
                  S <: T ->
                  Gamma |-- t \in T

   which overlaps ALL of the other rules.  Moreover, the
   principle argument [t] is the same in the premise as in
   the conclusion, so a direct translation of this rule into
   a clause of a Fixpoint would yield a non-terminating
   function (and Rocq would reject it!).

   Not only does the typing relation require some work to
   implement, but so does the subtyping relation.  The
   reason is similar: Some of the rules overlap
   others (e.g., in particular, S_Refl overlaps all the
   other rules in a somewhat trivial way and S_Trans
   overlaps in a more serious way); also, the rule S_Trans
   has a metavariable in its premises that does not appear
   in its conclusion.

          | S_Trans : forall S U T,
                 S <: U ->
                 U <: T ->
                 S <: T

   The plan for addressing these issues goes like this:

      - For subtyping...
          - define a SYNTAX-DIRECTED (or ALGORITHMIC)
            SUBTYPING relation that
              - restricts S_Refl to a few particular cases
              - combines the three record subtyping rules
                into a single "monster rule" that captures
                all of their effects together
              - drop the S_Trans rule
          - show that this definition yields the same
            relation as the ordinary subtyping rules --
            i.e., that the new rules are SOUND and COMPLETE
          - define a SUBTYPE CHECKER -- a recursive function
            that takes two types and returns a [bool]
          - show that this function is a decision procedure
            for subtyping by comparing its definition to the
            algorithmic subtyping rules.

      - For typing...
          - define a SYNTAX-DIRECTED (or ALGORITHMIC) TYPING
            relation that
              - adds subtype checks to the premises of other
                rules (in particular, to T_App)
              - drops the T_Sub rule
          - show that this definition yields the same
            relation as the ordinary typing rules -- i.e.,
            that the new rules are SOUND and COMPLETE
          - define a TYPE CHECKER -- a recursive function
            that takes a context and a term and returns an
            [option ty]
          - show that this function is a decision procedure
            for the typing relation by comparing its
            definition to the algorithmic typing rules.

   We don't have time to go into the details of all these
   steps, but let's look at them in a little more detail.

   First, let's look at subtyping...
*)

Module Examples.

Notation k := (S (S (S (S O)))).
Notation x := (S (S (S (S (S O))))).
Notation y := (S (S (S (S (S (S O)))))).

(* The [Variable] command lets us introduce some assumptions
   that we'll use in the following examples... *)
Variable S1 S2 U1 U2 T1 T2 : ty.
Variable WF_T1 : well_formed T1.
Variable WF_T2 : well_formed T2.
Variable WF_T1T2 : well_formed (T1->T2).

Lemma wf_A : well_formed A.
Proof. auto. Qed.

Lemma wf_RA : well_formed [{k:A}].
Proof. auto. Qed.

(* The reflexivity rule is more general than we need... *)

(* Here we apply S_Refl to an arrow type: *)
Definition refl_proof_1 :=
  S_Refl (T1->T2) WF_T1T2.
Check refl_proof_1.

(* But we could just as well have used S_Arrow for this
   proof, using S_Refl only on smaller types: *)
Definition refl_proof_2 :=
  S_Arrow T1 T2 T1 T2 (S_Refl T1 WF_T1) (S_Refl T2 WF_T2).
Check refl_proof_2.

(* Similarly, here we apply S_Refl to Top: *)
Definition refl_proof_3 :=
  S_Refl (Top) wf_top.
Check refl_proof_3.

(* But we could just as well have achieved this using the
   S_Top rule: *)
Definition refl_proof_4 :=
  S_Top Top wf_top.
Check refl_proof_4.

(* These examples suggest that we can, intuitively, keep
   "pushing reflexivity down" from more complex types to
   simpler ones.

   If we repeat this process long enough, most uses of
   S_Refl will disappear.  Which ones will not? *)

(* What about this one? *)
Definition refl_proof_5 :=
  S_Refl A wf_A.
Check refl_proof_5.
(* No: There is no other way to prove this. *)

(* What about this one? *)
Definition refl_proof_6 :=
  S_Refl [{k:A}] wf_RA.
Check refl_proof_6.

(* Yes: We can push the reflexivity through the TRcdcons
   constructor. *)
Definition refl_proof_7 :=
  S_RcdDepth k A TRcdnil A TRcdnil
    (S_Refl A wf_A)
    (S_Refl TRcdnil wf_rcdnil)
    wf_RA wf_RA.
Check refl_proof_7.
(* Can we go further and get rid of the remaining ones?  Not quite:
   The first one can go, but we need S_Refl to show that TRcdnil is
   a subtype of itself. *)

(* What we've learned so far is that S_Refl is not needed to prove
   reflexivity of arrow types, cons-records, or Top, but it _is_
   needed for base types and empty records. *)


(* What about transitivity? *)

(* Let's assume that we've got derivations (evidence)
   establishing the following subtyping relations: *)
Variable D1 : U1 <: S1.
Variable D2 : S2 <: U2.
Variable E1 : T1 <: U1.
Variable E2 : U2 <: T2.

Definition arrow_proof_1 :=
  S_Trans (S1->S2) (U1->U2) (T1->T2)
    (S_Arrow S1 S2 U1 U2 D1 D2)
    (S_Arrow U1 U2 T1 T2 E1 E2).
Check arrow_proof_1.

(* Can we "push down" these uses of S_Trans? *)

(* Yes: Like this... *)
Definition arrow_proof_1' :=
  S_Arrow S1 S2 T1 T2
    (S_Trans T1 U1 S1 E1 D1)
    (S_Trans S2 U2 T2 D2 E2).
Check arrow_proof_1'.

(* In fact, ALL uses of S_Trans can be pushed down in this
   fashion, except the ones used to "paste together"
   instances of the record subtyping rules.  For example,
   there is no way to prove

       [{x:A, y:B, z:C}]  <:  [{z:C, y:B, x:A}]

   without using transitivity. *)

(* These experiments tell us what we need to do to produce a
   syntax-directed subtyping relation:
      - replace the three "fine-grained" record subtyping
        rules by a single "coarse-grained" rule that can,
        for example, take into account multiple permutations
        at the same time.
      - replace general reflexivity by reflexivity on base
        types (the coarse-grained record rule will also
        handle reflexivity of empty records, so there's no
        need for a special rule for that). *)

(* ------------------------------------------------------ *)

(* Typing... *)

Variable t s : tm.
Variable wf_S1 : well_formed S1.
Variable Et : [(x,S1)] |-- t : S2.
Variable Es : empty |-- s : S1.

(* A very basic typing proof *)
Definition typing_proof_1 :=
  T_App S1 S2 empty (\x:S1,t) s
     (T_Abs empty x S1 S2 t wf_S1 Et)
     Es.
Check typing_proof_1.

(* A more interesting typing proof involving subsumption *)
Variable Es' : empty |-- s : T1.
Definition typing_proof_2 :=
  T_App T1 T2 empty (\x:S1,t) s
     (T_Sub empty (\x:S1,t) (S1->S2) (T1->T2)
       (T_Abs empty x S1 S2 t wf_S1 Et)
       arrow_proof_1')
     Es'.
Check typing_proof_2.

(* Can we "push down" this use of subsumption? *)
(* SOLUTION: Give an alternate proof of the SAME SUBTYPING
   FACT using two instances of the T_Sub rule -- one around
   the argument Es' (promoting T1 to S1) and another on the
   outside (promoting S2 to T2). *)
(* SOLUTION *)
Definition typing_proof_3 :=
  T_App T1 T2 empty (\x:S1,t) s
     (T_Sub empty (\x:S1,t) (S1->S2) (T1->T2)
       (T_Abs empty x S1 S2 t wf_S1 Et)
       arrow_proof_1')
     Es'.
Check typing_proof_3.
(* /SOLUTION *)

End Examples.

(* ====================================================== *)
(* Some technical preliminaries *)

(* Please skip over this section -- it defines some
   low-level technical properties that are needed to make
   Rocq happy with the definitions we are going to give
   later.  The details are not important. *)

Fixpoint max (m n : nat) : nat :=
  match m with
  | O => n
  | S m' => match n with
            | O => m
            | S n' => S (max m' n')
            end
  end.
Inductive height : ty -> nat -> Prop :=
  | h_base : forall n, height (Base n) O
  | h_top : height Top O
  | h_arrow : forall T1 T2 h1 h2,
         height T1 h1 ->
         height T2 h2 ->
         height (T1->T2) (S (max h1 h2))
  | h_rcdnil :
         height TRcdnil O
  | h_rcdcons : forall k T1 T2 h1 h2,
         height T1 h1 ->
         height T2 h2 ->
         height [{k:T1;T2}] (S (max h1 h2)).
(* FIX: But I can't use the {measure...} ordering because it
   assumes real nats, not my funny ones.  Boo hoo.  But
   probably in the next installment of the course I should
   introduce real nats anyway -- i.e., I should define my
   own nats inside a module that later gets closed so that
   people can use the real ones (including actual numbers as
   concrete syntax!)  (Later: I did this.) *)

Inductive proper_subexpression : ty -> ty -> Prop :=
  | se_arrow1 : forall T1 T2,
         proper_subexpression T1 (T1->T2)
  | se_arrow2 : forall T1 T2,
         proper_subexpression T2 (T1->T2)
  | se_arrow1' : forall S T1 T2,
         proper_subexpression S T1 ->
         proper_subexpression S (T1->T2)
  | se_arrow2' : forall S T1 T2,
         proper_subexpression S T2 ->
         proper_subexpression S (T1->T2)
  | se_rcd1 : forall k T1 T2,
         proper_subexpression T1 [{k:T1;T2}]
  | se_rcd2 : forall k T1 T2,
         proper_subexpression T2 [{k:T1;T2}]
  | se_rcd1' : forall S k T1 T2,
         proper_subexpression S T1 ->
         proper_subexpression S [{k:T1;T2}]
  | se_rcd2' : forall S k T1 T2,
         proper_subexpression S T2 ->
         proper_subexpression S [{k:T1;T2}].

Inductive proper_subexpressions
             : (ty*ty) -> (ty*ty) -> Prop :=
    se_pair : forall S1 S2 T1 T2,
       proper_subexpression S1 T1 ->
       proper_subexpression S2 T2 ->
       proper_subexpressions (S1,S2) (T1,T2).

Require Recdef.

(* =================================================== *)
(* Algorithmic subtyping relation *)

(* HIDEFROMHTML *)
Reserved Notation "S <:: T" (at level 70).
(* /HIDEFROMHTML *)

Inductive alg_subtyping : ty -> ty -> Prop :=
  | SA_ReflBase : forall n,
         Base n <:: Base n
  | SA_Top : forall S,
         well_formed S ->
         S <:: Top
  | SA_Arrow : forall S1 S2 T1 T2,
         T1 <:: S1 ->
         S2 <:: T2 ->
         S1->S2 <:: T1->T2
  | SA_Rcd : forall S T,
         well_formed S ->
         well_formed T ->
         record_ty S ->
         record_ty T ->
         (forall k Tk,
               type_rcd_binds k Tk T  ->
               exists Sk,
                     type_rcd_binds k Sk S
                  /\ Sk <:: Tk) ->
         S <:: T

where "S <:: T" := (alg_subtyping S T).

(* Subtype checker *)

Fixpoint check_record_ty (T : ty) : bool :=
  match T with
  | TRcdnil => true
  | [{k:T1;T2}] => true
  | _ => false
  end.

Fixpoint check_doesn't_bind (k : nat) (T : ty)
                            : bool :=
  match T with
  | [{k':T1;T2}] =>
      andb (negb (eqb_nat k k')) (check_doesn't_bind k T2)
  | _ =>
      true
  end.

Fixpoint check_well_formed (T : ty) : bool :=
  match T with
  | Top => true
  | Base n => true
  | T1->T2 =>
      andb (check_well_formed T1) (check_well_formed T2)
  | TRcdnil => true
  | [{k:T1;T2}] =>
        andb (check_well_formed T1)
             (andb (check_well_formed T2)
                   (andb (check_record_ty T2)
                         (check_doesn't_bind k T2)))
  end.

(* Note that we use here a slightly more powerful form of
   recursive function definition -- [Function] rather than
   [Fixpoint].  This is needed to convince Rocq that subtype
   checking always terminates, because the arguments to
   recursive calls are not immediate subphrases of one of a
   single "principle argument" (in the arrow and record
   cases). *)

(* This is commented out for now -- I am having trouble
   getting Rocq to accept the definition.  (In the meantime,
   I know a better way of formalizing it that does not use
   these rather experimental features of Rocq!  But there
   isn't time to carry it through or explain it right now.)

Function check_subtyping (UV : ty * ty)
            {wf proper_subexpressions UV}
            : bool :=
  match UV with
  | (U,Top) =>
       check_well_formed U
  | (Base m, Base n) =>
       eqb_nat m n
  | (U1->U2, V1->V2) =>
       andb (check_subtyping (V1,U1)) (check_subtyping (U2,V2))
  | (U, TRcdnil) => andb (check_well_formed U) (check_record_ty U)
  | (U, [{k:V1;V2}]) =>
       match TRcd_lookup k U with
       | None => false
       | Some Uk =>
            andb (check_well_formed U)
           (andb (check_well_formed [{k:V1;V2}])
           (andb (check_record_ty U)
           (andb (check_subtyping (Uk,V1))
                     (check_subtyping (U,V2)))))
       end
  | (_,_) => false
  end.
Proof.
Admitted.
*)

(* Bogus replacement version for now, just so that we have
   something of the right type for later definitions. *)
Definition check_subtyping (S T : ty) : bool := true.

(* ====================================================== *)
(* Algorithmic typing relation *)

(* HIDEFROMHTML *)
Reserved Notation "Gamma |-- t :: T" (at level 69).
(* /HIDEFROMHTML *)

Inductive alg_typing : context -> tm -> ty -> Prop :=
  | TA_Var : forall Gamma x T,
         binds _ x T Gamma ->
         well_formed T ->
         Gamma |-- (!x) :: T
  | TA_Abs : forall Gamma x T1 T2 t,
         well_formed T1 ->
         [(x,T1)] ++ Gamma |-- t :: T2 ->
         Gamma |-- (\x:T1, t) :: T1->T2
  | TA_App : forall S S' T Gamma t1 t2,
         Gamma |-- t1 :: (S->T)
      (* These two lines... *) ->
         Gamma |-- t2 :: S'
      (* ...are the crucial difference *) ->
         S' <:: S                         ->
         Gamma |-- (t1 @ t2) :: T
  | TA_Rcdnil : forall Gamma,
         Gamma |-- trcdnil :: TRcdnil
  | TA_Rcdcons : forall Gamma k t1 t2 T1 T2,
         Gamma |-- t1 :: T1 ->
         Gamma |-- t2 :: T2 ->
         well_formed [{k:T1;T2}] ->
         Gamma |-- {k=t1;t2} :: [{k:T1;T2}]
  | TA_Proj : forall Gamma k Tk t T,
         Gamma |-- t :: T ->
         type_rcd_binds k Tk T ->
         Gamma |-- t # k :: Tk
(* ...and note that T_Sub is omitted! *)

where "Gamma |-- t :: T" := (alg_typing Gamma t T).

Module Example.
Notation r := (S (S (S (S (S (S (S (S O)))))))).
Notation s := (S (S (S (S (S (S (S (S (S O))))))))).
Notation x := (S (S (S (S (S O))))).
Notation y := (S (S (S (S (S (S O)))))).
Notation z := (S (S (S (S (S (S (S O))))))).

(* SOLUTION: Prove the following assertion about algorithmic
   typing. *)
Lemma typing_example_1 :
  empty |--   (\r:[{y:B->B}], r # y)
           @ {x=(\z:A,z),y=(\z:B,z)}
        :: B->B.
Proof.
  (* ADMITTED *)
  eapply TA_App.
    apply TA_Abs. auto. eapply TA_Proj.
      apply TA_Var. unfold binds. simpl. reflexivity. auto.
      auto.
      unfold type_rcd_binds. simpl. reflexivity.
      apply TA_Rcdcons.
        apply TA_Abs. auto. apply TA_Var. unfold binds.
        simpl. reflexivity. auto.
        apply TA_Rcdcons. apply TA_Abs. auto. apply TA_Var.
        unfold binds. simpl. reflexivity. auto.
        apply TA_Rcdnil.
        auto. auto.
    apply SA_Rcd; auto.
    intros k Tk BINDS.
    remember (eqb_nat k x) as r. destruct r.
      - (* k = x *)
        unfold type_rcd_binds. apply eq_symm in Heqr.
        apply eqb_nat__eq in Heqr. subst. solve_by_invert.
      - (* k <> x *)
        remember (eqb_nat k y) as rr. destruct rr.
        + (* k = y *)
          apply ex_intro with (witness := B->B).
          apply conj. simpl.
          unfold type_rcd_binds. apply eq_symm in Heqrr.
          apply eqb_nat__eq in Heqrr. subst. simpl. reflexivity.
          unfold type_rcd_binds in BINDS. simpl in BINDS.
          rewrite <- Heqrr in BINDS. inversion BINDS.
          apply SA_Arrow. apply SA_ReflBase. apply SA_ReflBase.
        + (* k <> y *)
          unfold type_rcd_binds in BINDS. simpl in BINDS.
          rewrite <- Heqrr in BINDS. solve_by_invert.
Qed.
(* /ADMITTED *)

End Example.

(* Type checker *)

Fixpoint check_typing Gamma t : option ty :=
  match t with
  | !x =>
       lookup _ x Gamma
  | \x:T1,t2 =>
       if check_well_formed T1 then
         check_typing ([(x,T1)] ++ Gamma) t2
       else None
  | t1 @ t2 =>
       match check_typing Gamma t1 with
       | Some (T11->T12) =>
           match check_typing Gamma t2 with
           | Some T2 =>
               if check_subtyping T2 T11
                 then Some T12
                 else None
           | None => None
           end
       | _ => None
       end
  | trcdnil =>
      Some TRcdnil
  | {k=t1;t2} =>
       match check_typing Gamma t1 with
       | Some T1 =>
           match check_typing Gamma t2 with
           | Some T2 =>
               let T := [{k:T1;T2}] in
               if check_well_formed T
                 then Some T
                 else None
           | None => None
           end
       | _ => None
       end
  | t1 # k =>
       match check_typing Gamma t1 with
       | Some T1 => TRcd_lookup k T1
       | None => None
       end
  end.


(* ===================================================== *)
(* Correctness of the algorithmic subtyping *)

(* LATER: Commentary! *)

Lemma alg_subtyping_ind2 :
       forall P : ty -> ty -> Prop,
       (forall n : nat, P (Base n) (Base n)) ->
       (forall S : ty, well_formed S -> P S Top) ->
       (forall S1 S2 T1 T2 : ty,
        T1 <:: S1 ->
        P T1 S1 ->
        S2 <:: T2 ->
        P S2 T2 ->
        P (S1 -> S2) (T1 -> T2)) ->
       (forall S T : ty,
        well_formed S ->
        well_formed T ->
        record_ty S ->
        record_ty T ->
        (forall (k : nat) (Tk : ty),
         type_rcd_binds k Tk T ->
         exists Sk : ty, type_rcd_binds k Sk S /\ P Sk Tk) ->
        P S T) -> forall S T : ty, S <:: T -> P S T.
Proof.
  intros P HReflBase HTop HArrow HRcd.
  fix r 3.
  intros S T SUB. destruct SUB; auto.
  (* Only the record case is non-trivial *)
  apply HRcd; auto.
  intros k Tk B.
  assert (exists Sk : ty, type_rcd_binds k Sk S /\ Sk <:: Tk)
    by auto.
  destruct H4. rename witness into Sk. destruct H4.
  apply ex_intro with (witness := Sk). apply conj. auto.
  apply r. assumption.
Qed.

Lemma alg_subtyping__well_formed : forall S T,
     S <:: T ->
     well_formed S /\ well_formed T.
Proof.
  intros. induction H; apply conj; auto.
  destruct IHalg_subtyping1. destruct IHalg_subtyping2. auto.
  destruct IHalg_subtyping1. destruct IHalg_subtyping2. auto.
Qed.

(* To help with automation, let's break this lemma apart
   into two separate statements and add them both to the
   hints database. *)
Lemma alg_subtyping__well_formed_1 : forall S T,
     S <:: T ->
     well_formed S.
Proof.
  intros. pose proof (alg_subtyping__well_formed S T H).
  destruct H0. auto.
Qed.
Lemma alg_subtyping__well_formed_2 : forall S T,
     S <:: T ->
     well_formed T.
Proof.
  intros. pose proof (alg_subtyping__well_formed S T H).
  destruct H0. auto.
Qed.
Hint Resolve alg_subtyping__well_formed_1 : core.
Hint Resolve alg_subtyping__well_formed_2 : core.
(* While we're at it, let's do the same for ordinary subtyping. *)
(* LATER: Put this in earlier file! *)
Lemma subtypes__well_formed_1 : forall S T,
     S <: T ->
     well_formed S.
Proof.
  intros. pose proof (subtypes__well_formed S T H).
  destruct H0. auto.
Qed.
Lemma subtypes__well_formed_2 : forall S T,
     S <: T ->
     well_formed T.
Proof.
  intros. pose proof (subtypes__well_formed S T H).
  destruct H0. auto.
Qed.
Hint Resolve subtypes__well_formed_1 : core.
Hint Resolve subtypes__well_formed_2 : core.

Lemma alg_subtyping_refl : forall T,
     well_formed T ->
     T <:: T.
Proof.
  intros T WF.
  induction T; inversion WF.
    - (* Top *) apply SA_Top. auto.
    - (* Base *) apply SA_ReflBase.
    - (* Arrow *) auto using SA_Arrow.
    - (* TRcdnil *) apply SA_Rcd; auto.
      intros k Tk R. inversion R.
    - (* TRcdcons *) apply SA_Rcd; auto.
      subst.
      intros k Tk R.
      unfold type_rcd_binds in R. simpl in R.
      unfold type_rcd_binds. simpl.
      remember (eqb_nat k n) as E. destruct E.
        + (* k = n *)
          inversion R. subst.
          apply ex_intro with (witness := Tk). auto using conj.
        + (* k <> n *)
          pose proof (IHT2 H3).
          inversion H; subst; try solve [solve_by_inverts].
          unfold type_rcd_binds in H8.
          pose proof (H8 k Tk R).
          assumption.
Qed.
(* HIDE: This proof involves a slightly tricky little trip around
   the block! *)

Lemma alg_subtyping_inversion_top_right : forall T,
  Top <:: T -> T = Top.
Proof.
  intros. inversion H. subst. reflexivity. subst.
  solve_by_invert.
Qed.

Lemma alg_subtyping_inversion_base_left : forall n T,
     (Base n) <:: T  ->
     T = Top \/ T = (Base n).
Proof.
  intros. inversion H. subst.
    apply or_intror. auto.
    apply or_introl. auto.
    solve_by_invert.
Qed.

Lemma alg_subtyping_inversion_arrow_left : forall S T1 T2,
     S <:: T1->T2  ->
     exists S1 S2,
           S = S1->S2
        /\ T1 <:: S1
        /\ S2 <:: T2.
Proof.
  intros. inversion H. subst.
    eauto using ex_intro, SA_Arrow, conj.
    solve_by_invert.
Qed.

Lemma alg_subtyping_inversion_arrow_right : forall S1 S2 T,
     S1->S2 <:: T ->
     T = Top
     \/ exists T1 T2,
              T = T1->T2
           /\ T1 <:: S1
           /\ S2 <:: T2.
Proof.
  intros. inversion H; subst.
    apply or_introl. auto.
    apply or_intror. eauto using ex_intro, SA_Arrow, conj.
    solve_by_invert.
Qed.

Lemma alg_subtyping_inversion_rcd_left : forall S T,
     S <:: T  ->
     record_ty T ->
     record_ty S
     /\ (forall k Tk,
               type_rcd_binds k Tk T  ->
               exists Sk,
                     type_rcd_binds k Sk S
                  /\ Sk <:: Tk).
Proof.
  intros. inversion H; subst; try solve [solve_by_inverts].
  eauto using ex_intro, conj.
Qed.

Lemma alg_subtyping_inversion_rcd_right : forall S T,
     S <:: T  ->
     record_ty S ->
     T = Top
     \/ (record_ty T
         /\ (forall k Tk,
                   type_rcd_binds k Tk T  ->
                   exists Sk,
                         type_rcd_binds k Sk S
                      /\ Sk <:: Tk)).
Proof.
  intros. inversion H; subst; try solve [solve_by_inverts].
    apply or_introl. auto.
    apply or_intror. eauto using ex_intro, conj.
Qed.

(* LATER: Note that [pose proof] is new.  Explain it, or use something
   else. *)

Lemma alg_subtyping_trans_aux : forall S T,
     S <:: T ->
     (forall U, U <:: S -> U <:: T)
  /\ (forall U, T <:: U -> S <:: U).
Proof.
  intros S T H.
  induction H using alg_subtyping_ind2; split;
    [ intros U SubUS
    | intros U SubTU ].
    - (* SA_ReflBase *) + (* U on the left *)
      assumption.
    - (* SA_ReflBase *) + (* U on the right *)
      assumption.
    - (* SA_Top *) + (* U on the left *)
      eauto using SA_Top.  (* FIX: Why eauto? *)
    - (* SA_Top *) + (* U on the right *)
      assert (U = Top)
        by (auto using alg_subtyping_inversion_top_right).
      subst. auto using SA_Top.
    - (* SA_Arrow *) + (* U on the left *)
      pose proof
        (alg_subtyping_inversion_arrow_left U S1 S2 SubUS).
      (* Or: remember
           (alg_subtyping_inversion_arrow_left U S1 S2 SubUS)
           as RR. *)
      destruct H1. rename witness into U1. destruct H1.
      rename witness into U2.
      destruct H1. destruct H2.
      subst.
      destruct IHalg_subtyping1. destruct IHalg_subtyping2.
      auto using SA_Arrow.
    - (* SA_Arrow *) + (* U on the right *)
      pose proof (alg_subtyping_inversion_arrow_right T1 T2 U SubTU).
      inversion H1.
        * (* U = Top *) subst. eauto using SA_Top.
        * (* U is an arrow type *)
          destruct H2. rename witness into U1. destruct H2.
          rename witness into U2.
          destruct H2. destruct H3. subst.
          destruct IHalg_subtyping1. destruct IHalg_subtyping2.
          auto using SA_Arrow.
    - (* SA_Rcd *) + (* U on the left *)
      assert
        (record_ty U
     /\ (forall k Sk,
            type_rcd_binds k Sk S ->
            exists Uk,
              type_rcd_binds k Uk U
           /\ Uk <:: Sk))
        as R by (auto using alg_subtyping_inversion_rcd_left).
      destruct R.
      assert (well_formed U /\ well_formed S)
        as W by (auto using alg_subtyping__well_formed).
      destruct W.
      apply SA_Rcd; auto.
      intros k Tk B.
      assert
        (exists Sk : ty,
          type_rcd_binds k Sk S /\
          (forall U : ty, U <:: Sk -> U <:: Tk) /\
          (forall U : ty, Tk <:: U -> Sk <:: U)) as E by auto.
      destruct E. rename witness into Sk. destruct H8. destruct H9.
      assert (exists Uk : ty, type_rcd_binds k Uk U /\ Uk <:: Sk) by auto.
      destruct H11. rename witness into Uk. destruct H11.
      apply ex_intro with (witness := Uk). auto using conj.
    - (* SA_Rcd *) + (* U on the right *)
      assert
        (U = Top
     \/ (record_ty U
           /\ (forall k Uk,
                 type_rcd_binds k Uk U  ->
                 exists Tk,
                   type_rcd_binds k Tk T
                /\ Tk <:: Uk)))
        as R by (auto using alg_subtyping_inversion_rcd_right).
      destruct R.
        * (* U = Top *)
          subst. eapply SA_Top. assumption.
        * (* U is a record *)
          destruct H4.
          assert (well_formed T /\ well_formed U)
            as W by (auto using alg_subtyping__well_formed).
          destruct W.
          apply SA_Rcd; auto.
          intros k Uk B.
          assert (exists Tk : ty,
                     type_rcd_binds k Tk T /\ Tk <:: Uk)
            by auto.
          destruct H8. rename witness into Tk. destruct H8.
          assert
            (exists Sk : ty,
              type_rcd_binds k Sk S /\
              (forall U : ty, U <:: Sk -> U <:: Tk) /\
              (forall U : ty, Tk <:: U -> Sk <:: U))
            as E by auto.
          destruct E. rename witness into Sk. destruct H10.
          destruct H11.
          apply ex_intro with (witness := Sk). auto using conj.
Qed.

Lemma alg_subtyping_trans : forall S U T,
     S <:: U ->
     U <:: T ->
     S <:: T.
Proof.
  intros.
  assert ((forall T, T <:: S -> T <:: U)
          /\ (forall T, U <:: T -> S <:: T))
    by (auto using alg_subtyping_trans_aux).
  destruct H1. eauto.
Qed.

(* LATER: FIX: It's a little ugly, but it does the job! *)
Lemma bring_a_field_to_the_front : forall S k Sk,
     well_formed S ->
     type_rcd_binds k Sk S ->
     exists S2,
          (forall k', doesn't_bind k' S  ->
                 doesn't_bind k' [{k:Sk;S2}])
       /\ S <: [{k:Sk;S2}]
       /\ [{k:Sk;S2}] <: S.
Proof.
  induction S;
       intros k Sk W B; try solve [solve_by_inverts].
  (* Only the TRcdcons case is interesting *)
  unfold type_rcd_binds in B. simpl in B.
  remember (eqb_nat k n) as E. destruct E.
    + (* k = n *) inversion B. subst.
      apply eq_symm in HeqE. apply eqb_nat__eq in HeqE. subst.
      eauto 7 using ex_intro, S_Refl, conj.
    + (* k <> n *) inversion W. subst.
    apply eq_symm in HeqE. pose proof HeqE as NEQ.
      apply eqnat_no in NEQ.
      apply eqnat_symm in HeqE. apply eqnat_no in HeqE.
      pose proof (IHS2 k Sk H3 B).
      destruct H. rename witness into S3. destruct H.
      apply ex_intro with (witness := [{n:S1;S3}]).
      clear IHS1.
      apply conj; [idtac | apply conj].
        * (* first part *)
          intros k' DB.
          inversion DB. subst.
          pose proof (H k' H9). inversion H1. subst. auto.
        * (* second part *)
          destruct H0.
          assert (well_formed [{k : Sk; S3}]) by eauto.
          inversion H6. subst.
          apply S_Trans with (U := [{n:S1;[{k:Sk;S3}]}]).
            apply S_RcdDepth; eauto. apply S_Refl; auto.
            apply S_RcdPerm. apply wf_rcdcons; auto. auto.
        * (* third part *)
          destruct H0.
          assert (well_formed [{k : Sk; S3}]) by eauto.
          inversion H6. subst.
          apply S_Trans with (U := [{n:S1;[{k:Sk;S3}]}]).
          { apply S_RcdPerm. apply wf_rcdcons; auto.
            assert (doesn't_bind n [{k : Sk; S3}]) by auto.
            inversion H7. subst. auto. auto. }
          { apply S_RcdDepth. auto using S_Refl.
            assumption. auto. auto. }
Qed.

Lemma doesn't_bind__not_bound : forall k Tk T,
     doesn't_bind k T ->
     : type_rcd_binds k Tk T.
Proof.
  intros k Tk T D.
  induction T; try solve [solve_by_inverts].
    - (* empty record *) intros C. inversion C.
    - (* cons record *) inversion D. subst.
     unfold type_rcd_binds. simpl.
     apply eqb_nat_refl' in H1. rewrite H1.
     unfold type_rcd_binds in IHT2. auto.
Qed.

Lemma fields_sub__subtype : forall S T,
     fields_sub S T ->
     well_formed S ->
     well_formed T ->
     record_ty S ->
     record_ty T ->
     S <: T.
Proof.
  intros S T B WFS WFT RS RT.
  generalize dependent S.
  induction WFT; inversion RT; subst; intros S B WFS RS.
    - (* T empty *)
      inversion RS. apply S_Refl. auto. apply S_RcdWidth.
      subst. assumption.
    - (* T nonempty *)
      unfold fields_sub in B.
      assert (exists Sk, type_rcd_binds k Sk S /\ Sk <: T1).
        + (* Pf *) apply B. unfold type_rcd_binds. simpl.
          assert (eqb_nat k k = true). apply eqb_nat_refl.
          rewrite H1. reflexivity.
      destruct H1. rename witness into Sk. destruct H1.
      assert
        (exists S2,
          (forall k',
              doesn't_bind k' S -> doesn't_bind k' [{k:Sk;S2}])
              /\ S <: [{k:Sk;S2}] /\ [{k:Sk;S2}] <: S).
        apply bring_a_field_to_the_front. assumption. assumption.
      destruct H3. rename witness into S2. destruct H3. destruct H4.
      assert (fields_sub [{k:Sk; S2}] [{k:T1;T2}]).
        + (* Pf *)
          apply fields_sub_trans with (U:=S).
          apply subtype__fields_sub.
          assumption. assumption.
      assert (fields_sub S2 T2).
        + (* Pf *) unfold fields_sub. intros k' Tk' B'.
          remember (eqb_nat k k') as E. destruct E.
            * (* k = k' *)
              apply eq_symm in HeqE.
              apply eqb_nat__eq in HeqE. subst k'.
              assert (: type_rcd_binds k Tk' T2).
              apply doesn't_bind__not_bound. subst. assumption.
              contradiction.
            * (* k <> k' *)
              unfold fields_sub in H6.
              apply eq_symm in HeqE. apply eqnat_symm in HeqE.
              assert
                (exists Sk0,
                  type_rcd_binds k' Sk0 [{k : Sk; S2}]
                  /\ Sk0 <: Tk').
                apply H6. unfold type_rcd_binds. simpl.
                rewrite HeqE. assumption.
              destruct H7. rename witness into Sk0.
              destruct H7.
              unfold type_rcd_binds in H7. simpl in H7.
              rewrite HeqE in H7.
              apply ex_intro with (witness := Sk0). auto.
      apply S_Trans with (U := [{k : Sk; S2}]).
        assumption. (* LATER: This case seems messy! *)
        assert (well_formed [{k : Sk; S2}]).
          + (* Pf *)
            assert (well_formed [{k : Sk; S2}]
                    /\ well_formed S).
            auto using subtypes__well_formed. destruct H8.
            assumption.
        apply S_RcdDepth. assumption. apply IHWFT2.
        assumption. inversion H8. assumption. subst. inversion H8.
        assumption. inversion H8. assumption. assumption.
        auto.
Qed.

Theorem alg_subtyping_correctness : forall S T,
  S<:T <-> S<::T.
Proof.
  unfold iff. intros. apply conj.
  - (* -> *)
    intros H. induction H.
      + (* S_Refl *) auto using alg_subtyping_refl.
      + (* S_Trans *) eauto using alg_subtyping_trans.
      + (* S_Top *) auto using SA_Top.
      + (* S_Arrow *) auto using SA_Arrow.
      + (* S_RcdWidth *) apply SA_Rcd; auto. intros.
        solve_by_invert.
      + (* S_RcdDepth *) apply SA_Rcd; auto.
        intros k' Tk' B.
        unfold type_rcd_binds in B. simpl in B.
        unfold type_rcd_binds. simpl.
        remember (eqb_nat k' k) as E. destruct E.
          * (* k' = k *)
            inversion B. subst.
            apply eq_symm in HeqE. apply eqb_nat__eq in HeqE. subst.
            apply ex_intro with (witness := S1). auto using conj.
          * (* k' <> k *)
            inversion IHsubtyping2; subst;
              try solve [solve_by_inverts].
            unfold type_rcd_binds in H7.
            apply H7. auto.
      + (* S_RcdPerm *)
        inversion H. subst. inversion H5. subst.
        inversion H7. subst.
        assert (k2<>k1). intros C. apply eq_symm in C.
        contradiction. apply SA_Rcd; auto.
        unfold type_rcd_binds. simpl.
        intros k Tk B.
        remember (eqb_nat k k1) as E1. destruct E1.
          * (* k = k1 *)
            apply eq_symm in HeqE1.
            apply eqb_nat__eq in HeqE1. subst.
            apply eqb_nat_refl' in H3. rewrite H3 in B.
            inversion B. subst.
            eauto 6 using ex_intro, conj, alg_subtyping_refl.
          * (* k <> k1 *)
            destruct (eqb_nat k k2); inversion B; subst.
            eauto 6 using ex_intro, conj, alg_subtyping_refl.
            unfold type_rcd_binds.
            apply ex_intro with (witness := Tk).
            apply conj. auto. apply alg_subtyping_refl.
            eapply fields_of_well_formed_types_are_well_formed.
            apply H9. unfold type_rcd_binds. eauto.
  - (* <- *)
    intros H.
    induction H using alg_subtyping_ind2.
      + (* SA_ReflBase *) auto using S_Refl.
      + (* SA_Top *) auto using S_Top.
      + (* SA_Arrow *) auto using S_Arrow.
      + (* SA_Rcd *) auto using fields_sub__subtype.
Qed.
(* LATER: Now we should reason that the algorithm itself is correct! *)

(* Still to be filled in: Similar proofs for the typing
   relation. *)

*)

(* LATER:  (replace {} with unit/Unit)

   In this problem, we examine possible variations of the simply-typed lambda calculus with
   subtyping.
   (a) Suppose we remove the S_Arrow rule from the subtyping relation. Do progress and preservation
   continue to hold after this change, or does one (or do both) fail? If either fails, give a counterex-
   ample.
   Answer: Neither breaks. Intuitively, we added subtyping to a language that was already sound in
   order to allow more terms to have types. Reducing some of that freedom maintains soundness.
   Grading scheme: One point if only one is identied as still holding; 0 if both are given as failing.
   (b) Suppose we change the S_Arrow rule to:
   T1 <: S1 T2 <: S2
   ---------------------- (S_Arrow_Odd)
   S1 -> S2 <: T1 -> T2
   Do progress and preservation continue to hold after this change, or does one (or do both) fail? If
   either fails, give a counterexample.

   Answer: Preservation breaks. Consider empty |-- ((\x:{}, {})
   {}).i : A->A. We can show {i:A->A} <: {}, so {} -> {} <: {} ->
   {i:A->A}, and so the inner application has type {i:A->A}. But
   when we take a step, we must show that empty |-- {}.i : A->A,
   but we cannot -- {} can only be typed as {} or Top.

   _____________________________________________________________________

   The subtyping rule for products in the nal homework assignment
   S1 <: T1 S2 <: T2
   --------------------- (S_Prod)
   S1 * S2 <: T1 * T2
   intuitively corresponds to the depth subtyping rule for records. Extending the analogy, we might
   consider adding a width rule
   ------------- (S_ProdW)
   S1 * S2 <: S1
   for products.
   Is this a good idea? Briey explain why or why not.
   Answer: No, since it will break progress: ({i=\y:A,y},{}).i cannot take a step even though it is well
   typed using this rule.

   ____________________________________________________________

   Write a careful informal proof of the following theorem.
   Theorem: If S1*S2 <: T, then either T = Top or else T = T1*T2, with S1 <: T1 and S2 <: T2.
   You may use the following result in your proof (you do not need to prove it):
   Lemma [sub-inversion-Top]: For any type S, if Top <: S then S = Top.
   Answer:
   Proof: By induction on the given derivation.
    If the last rule is S_Refl, then T = S1*S2 and the result follows by two uses of S_Refl.
    If the last rule is S_Trans, then S <: U and U <: T for some U. By the IH, either U = Top or else
   U = U1*U2 with S1 <: U1 and S2 <: U2. In the rst case, a straightforward inner induction on
   the derivation of Top <: T shows that T = Top. In the second case, applying the IH to U1*U2 <: T
   tells us that either T = Top or else T = T1*T2 with U1 <: T1 and U2 <: T2. If T = Top, we are
   nished. If T = T1*T2, then by S_Trans we have S1 <: T1 and S2 <: T2, as required.
    If the last rule is S_Top, then T = Top immediately.
    If the last rule is S_Prod, then T = T1*T2 with S1 <: T1 and S2 <: T2, and the result is imme-
   diate.
    None of the other rules (S_Arrow, S_RcdWidth, S_RcdDepth, or S_RcdPerm) are possible.
*)

(* /HIDE *)

(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(\\*\\* \\*+\\|(\\* EX[1-5]..." *)
(* End: *)
(* mode: outline-minor *)
(* outline-heading-end-regexp: "\n" *)
(* /HIDE *)
