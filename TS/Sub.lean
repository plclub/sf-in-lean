import SFLMeta
import TS.Stlc
import TS.Types
import LF.CustomTactics
import LF.Typeclasses
open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Sub: Subtyping" =>
%%%
tag := "Sub"
htmlSplit := .never
file := some "Sub"
%%%

# Concepts

:::full
We now turn to _subtyping_, a key feature of - in particular -
object-oriented programming languages.
:::

## A Motivating Example

Suppose we are writing a program involving two record types
defined as follows:

```display
      Person  = {name:String, age:Nat}
      Student = {name:String, age:Nat, gpa:Nat}
```

::::full
In the simply typed lamdba-calculus with records, the term

```display
    (λ r:Person. (r.age)+1) {name="Pat", age=21, gpa=1}
```
is not typable, since it applies a function that wants a two-field
record to an argument that actually provides three fields, while the
`app` rule demands that the domain type of the function being
applied must match the type of the argument precisely.

But this is silly: we're passing the function a _better_ argument
than it needs!  The only thing the body of the function can
possibly do with its record argument `r` is project the field `age`
from it: nothing else is allowed by the type, and the presence or
absence of an extra `gpa` field makes no difference at all.  So,
intuitively, it seems that this function should be applicable to
any record value that has at least an `age` field.

More generally, a record with more fields is "at least as good in
any context" as one with just a subset of these fields, in the
sense that any value belonging to the longer record type can be
used _safely_ in any context expecting the shorter record type.  If
the context expects something with the shorter type but we actually
give it something with the longer type, nothing bad will
happen (formally, the program will not get stuck).

The principle at work here is called _subtyping_.  We say that "`σ`
is a subtype of `τ`", written `σ <: τ`, if a value of type `σ` can
safely be used in any context where a value of type `τ` is
expected.  The idea of subtyping applies not only to records, but
to all of the type constructors in the language -- functions,
pairs, etc.
::::

::::terse
_Problem_: In the pure STLC with records, the following term is not
typable:

```display
    (λr:Person. (r.age)+1) {name="Pat",age=21,gpa=1}
```
This is a shame.
::::

::::terse
_Idea_: Introduce _subtyping_, formalizing the observation that
"some types are better than others."
::::

Safe substitution principle:
- `σ` is a subtype of `τ`, written `σ <: τ`, if a value of type
  `σ` can safely be used in any context where a value of type
  `τ` is expected.

## Subtyping and Object-Oriented Languages

::::full
Subtyping plays a fundamental role in many programming
languages -- in particular, it is central to the design of
object-oriented languages and their libraries.

An _object_ in Java, C#, etc. can be thought of as a record,
some of whose fields are functions ("methods") and some of whose
fields are data values ("fields" or "instance variables").
Invoking a method `m` of an object `o` on some arguments `a₁..an`
roughly consists of projecting out the `m` field of `o` and
applying it to `a₁..an`.

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
interface `Component` that collects together the common fields and
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
classes.  (There is a lot of discussion in {citet Bib.pierce2002}[], if
you are interested.)  Instead, we'll study the core concepts
behind the subclass / subinterface relation in the simplified
setting of the STLC.
::::

::::terse
Subtyping plays a fundamental role in OO programming
languages.

Roughly, an _object_ can be thought of as a record of
functions ("methods") and data values ("fields" or "instance
variables").

    - Invoking a method `m` of an object `o` on some arguments
      `a₁..an` consists of projecting out the `m` field of `o` and
      applying it to `a₁..an`.

The type of an object is a _class_ (or an _interface_).

Classes are related by the _subclass_ relation.

    - An object belonging to a subclass must provide all the
      methods and fields of one belonging to a superclass, plus
      possibly some more.

    - Thus a subclass object can be used anywhere a superclass
      object is expected.

    - Very handy for organizing large libraries
::::

::::terse
"Of course, real OO languages have lots of other features...
  - mutable fields
  - "private" and other visibility modifiers
  - method inheritance
  - static components
  - etc., etc.

We'll ignore all these and focus on core mechanisms.
::::

## The Subsumption Rule

τ₂
Our goal for this chapter is to add subtyping to the simply typed
lambda-calculus (with some basic extensions). This involves two steps:

  - Defining a binary _subtype relation_ between types.

  - Enriching the typing relation to take subtyping into account.

The second step is actually very simple.  We add just a single rule
to the typing relation: the so-called _rule of subsumption_:

```display
                         Γ ⊢ t₁ ⦂ τ₁     τ₁ <: τ₂
                         --------------------------           (sub)
                               Γ ⊢ t₁ ⦂ τ₂
```

This rule says, intuitively, that it is OK to "forget" some of
what we know about a term.

::::full
For example, we may know that `t₁` is a record with two
fields (e.g., `τ₁ = {x:α→α, y:β→β}`, but choose to forget about
one of the fields (`τ₂ = {y:β→β}`) so that we can pass `t₁` to a
function that requires just a single-field record.
::::

## The Subtype Relation

The first step -- the definition of the relation `σ <: τ` -- is
where all the action is.  Let's look at each of the clauses of its
definition.

### Structural Rules

To start off, we impose two "structural rules" that are
independent of any particular type constructor: a rule of
_transitivity_, which says intuitively that, if `σ` is
better (richer, safer) than `υ` and `υ` is better than `τ`,
then `σ` is better than `τ`...

```display
                              σ <: υ    υ <: τ
                              ----------------                        (trans)
                                   σ <: τ
```
... and a rule of _reflexivity_, since certainly any type `τ` is
as good as itself:
```display
                                   ------                              (refl)
                                   τ <: τ
```


### Products

Now we consider the individual type constructors, one by one,
beginning with product types.  We consider one pair to be a subtype
of another if each of its components is.

```display
                            σ₁ <: τ₁    σ₂ <: τ₂
                            --------------------                        (prod)
                             σ₁ × σ₂ <: τ₁ × τ₂
```


::::full
The subtyping rule for arrows is a little less intuitive.
Suppose we have functions `f` and `g` with these types:

```display
       f : C → Student
       g : (C→Person) → D
```

That is, `f` is a function that yields a record of type `Student`,
and `g` is a (higher-order) function that expects its argument to be
a function yielding a record of type `Person`.  Also suppose that
`Student` is a subtype of `Person`.  Then the application `g f` is
safe even though their types do not match up precisely, because
the only thing `g` can do with `f` is to apply it to some
argument (of type `C`); the result will actually be a `Student`,
while `g` will be expecting a `Person`, but this is safe because
the only thing `g` can then do is to project out the two fields
that it knows about (`name` and `age`), and these will certainly
be among the fields that are present.

This example suggests that the subtyping rule for arrow types
should say that two arrow types are in the subtype relation if
their results are:

```display
                                  σ₂ <: τ₂
                              ----------------                     (arrow_co)
                            σ₁ → σ₂ <: σ₁ → τ₂
```

We can generalize this to allow the arguments of the two arrow
types to be in the subtype relation as well:

```display
                            τ₁ <: σ₁    σ₂ <: τ₂
                            --------------------                      (arrow)
                              σ₁ → σ₂ <: τ₁ → τ₂
```

But notice that the argument types are subtypes "the other way round":
in order to conclude that `σ₁→σ₂` to be a subtype of `τ₁→τ₂`, it
must be the case that `τ₁` is a subtype of `σ₁`.  The arrow
constructor is said to be _contravariant_ in its first argument
and _covariant_ in its second.

Here is an example that illustrates this:
```display
       f : Person → C
       g : (Student → C) → D
```

The application `g f` is safe, because the only thing the body of
`g` can do with `f` is to apply it to some argument of type
`Student`.  Since `f` requires records having (at least) the
fields of a `Person`, this will always work. So `Person → C` is a
subtype of `Student → C` since `Student` is a subtype of
`Person`.

The intuition is that, if we have a function `f` of type `σ₁→σ₂`,
then we know that `f` accepts elements of type `σ₁`; clearly, `f`
will also accept elements of any subtype `τ₁` of `σ₁`. The type of
`f` also tells us that it returns elements of type `σ₂`; we can
also view these results belonging to any supertype `τ₂` of
`σ₂`. That is, any function `f` of type `σ₁→σ₂` can also be
viewed as having type `τ₁→τ₂`.
::::

::::terse
Suppose we have functions `f` and `g` with these types:

```display
    f : C → Student
    g : (C→Person) → D
```

Is it safe to allow the application `g f`?

Yes.

So we want:

```display
      C→Student  <:  C→Person
```

I.e., arrow is _covariant_ in its right-hand argument.

Now suppose we have:

```display
       f : Person → C
       g : (Student→C) → D
```

Is it safe to allow the application `g f`?

Again yes.

So we want:

```display
      Person → C  <:  Student → C
```

I.e., arrow is _contravariant_ in its left-hand argument.

Putting these together...

```display
                            τ₁ <: σ₁    σ₂ <: τ₂
                            --------------------                      (arrow)
                            σ₁ → σ₂ <: τ₁ → τ₂
```
::::

::::quiz
Suppose we have  `σ <: τ` and `υ <: δ`.  Which of the following
subtyping assertions is _false_?

    (A) `σ×υ <: τ×δ`

    (B) `τ→υ <: σ→υ`

    (C) `(σ→υ) → (σ×δ)  <:  (σ→υ) → (τ×υ)`

    (D) `(τ×υ) → δ  <:  (σ×υ) → δ`

    (E) `σ→υ <: σ→δ`
::::

::::quiz
Suppose again that we have `σ <: τ` and `υ <: δ`.  Which of the
following is incorrect?

    (A) `(τ→τ)×υ  <: (σ→τ)×δ`

    (B) `τ→υ <: σ→δ`

    (C) `(σ→υ) → (σ→δ)  <:  (τ→υ) → (τ→δ)`

    (D) `(σ→δ) → δ  <:  (τ→υ) → δ`

    (E) `σ → (δ→υ) <: σ → (υ→υ)`
::::

### Records

What about subtyping for record types?


The basic intuition is that it is always safe to use a "bigger"
record in place of a "smaller" one.  That is, given a record type,
adding extra fields will always result in a subtype.  If some code
is expecting a record with fields `x` and `y`, it is perfectly safe
for it to receive a record with fields `x`, `y`, and `z`; the `z`
field will simply be ignored.  For example,

```display
    {name:String, age:Nat, gpa:Nat} <: {name:String, age:Nat}
    {name:String, age:Nat} <: {name:String}
    {name:String} <: {}
```

This is known as "width subtyping" for records.


We can also create a subtype of a record type by replacing the type
of one of its fields with a subtype.  If some code is expecting a
record with a field `x` of type `τ`, it will be happy with a record
having a field `x` of type `σ` as long as `σ` is a subtype of
`τ`. For example,

```display
    {x:Student} <: {x:Person}
```

This is known as "depth subtyping".


Finally, although the fields of a record type are written in a
particular order, the order does not really matter. For example,

```display
    {name:String,age:Nat} <: {age:Nat,name:String}
```
This is known as "permutation subtyping".


We _could_ formalize these requirements in a single subtyping rule
for records as follows:

```display
                        ∀ jk in j₁..jn,
                    ∃ ip in i₁..im, such that
                        jk=ip and σp <: τk
                  ----------------------------------                    (rcd)
                  {i₁:σ₁...im:σm} <: {j₁:τ₁...jn:τn}
```

That is, the record on the left should have all the field labels of
the one on the right (and possibly more), while the types of the
common fields should be in the subtype relation.

However, this rule is rather heavy and hard to read, so it is often
decomposed into three simpler rules, which can be combined using
`trans` to achieve all the same effects.


First, adding fields to the end of a record type gives a subtype:

```display
                               n > m
                 ---------------------------------                 (rcdWidth)
                 {i₁:τ₁...in:τn} <: {i₁:τ₁...im:τm}
```

We can use `rcdWidth` to drop later fields of a multi-field
record while keeping earlier fields, showing for example that
`{age:Nat,name:String} <: {age:Nat}`.


Second, subtyping can be applied inside the components of a compound
record type:

```display
                       σ₁ <: τ₁  ...  σn <: τn
                  ----------------------------------               (rcdDepth)
                  {i₁:σ₁...in:σn} <: {i₁:τ₁...in:τn}
```

For example, we can use `rcdDepth` and `rcdWidth` together to
show that `{y:Student, x:Nat} <: {y:Person}`.

Third, subtyping can reorder fields.  For example, we
want `{name:String, gpa:Nat, age:Nat} <: Person`, but we
haven't quite achieved this yet: using just `rcdDepth` and
`rcdWidth` we can only drop fields from the _end_ of a record
type.  So we add:

```display
         {i₁:σ₁...in:σn} is a permutation of {j₁:τ₁...jn:τn}
         ---------------------------------------------------        (rcdPerm)
                  {i₁:σ₁...in:σn} <: {j₁:τ₁...jn:τn}
```



It is worth noting that full-blown language designs may choose not
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
  it).


:::::full

::::exercise (rating := 2) (name := "arrow_sub_wrong") (manual := true)

Suppose we had incorrectly defined subtyping as covariant on both
the right and the left of arrow types:

```display
                            σ₁ <: τ₁    σ₂ <: τ₂
                            --------------------                (arrowWrong)
                            σ₁ → σ₂ <: τ₁ → τ₂
```

Give a concrete example of functions `f` and `g` with the following
types...

```display
       f : Student → Nat
       g : (Person → Nat) → Nat
```

... such that the application `g f` will get stuck during
execution.  (Use informal syntax.  No need to prove formally that
the application gets stuck.)

:::solution
Answer:
```display
       f = λr:Student. r.gpa
       g = λf:Person→Nat. f {name="Alex",age=20}
```
:::

:::grade
`GRADE_MANUAL 2: arrow_sub_wrong`
:::

::::
:::::

### ⊤

Finally, it is convenient to give the subtype relation a maximum
element -- a type that lies above every other type and is
inhabited by all (well-typed) values.  We do this by adding to the
language one new type constant, called `⊤` (pronounced "⊤" and written \⊤),
together with a subtyping rule that places it above every other type in the
subtype relation:

```display
                                   --------                             (⊤)
                                   σ <: ⊤
```

The `⊤` type is an analog of the `Object` type in Java and C#.


### Summary

In summary, we form the STLC with subtyping by starting with the
pure STLC (over some set of base types) and then...

  - adding a base type `⊤`,

  - adding the rule of subsumption

```display
                         Γ ⊢ t₁ ⦂ τ₁     τ₁ <: τ₂
                         --------------------------------            (sub)
                               Γ ⊢ t₁ ⦂ τ₂
```
  to the typing relation, and

  - defining a subtype relation as follows:

```display
                              σ <: υ    υ <: τ
                              ----------------                        (trans)
                                   σ <: τ

                                   ------                              (refl)
                                   τ <: τ

                                   --------                             (⊤)
                                   σ <: ⊤

                            σ₁ <: τ₁    σ₂ <: τ₂
                            --------------------                       (prod)
                             σ₁ × σ₂ <: τ₁ × τ₂

                            τ₁ <: σ₁    σ₂ <: τ₂
                            --------------------                      (arrow)
                            σ₁ → σ₂ <: τ₁ → τ₂

                               n > m
                 ---------------------------------                 (rcdWidth)
                 {i₁:τ₁...in:τn} <: {i₁:τ₁...im:τm}

                       σ₁ <: τ₁  ...  σn <: τn
                  ----------------------------------               (rcdDepth)
                  {i₁:σ₁...in:σn} <: {i₁:τ₁...in:τn}

         {i₁:σ₁...in:σn} is a permutation of {j₁:τ₁...jn:τn}
         ---------------------------------------------------        (rcdPerm)
                  {i₁:σ₁...in:σn} <: {j₁:τ₁...jn:τn}
```

::::quiz
Suppose we have  `σ <: τ` and `υ <: δ`.  Which of the following
subtyping assertions is false?

  (A) `σ×υ <: ⊤`

  (B) `{i₁:σ,i₂:τ}→υ <: {i₁:σ,i₂:τ,i₃:δ}→υ`

  (C) `(σ→τ) → (⊤ → ⊤)  <:  (σ→τ) → ⊤`

  (D) `(⊤ → ⊤) → δ  <:  ⊤ → δ`

  (E) `σ → {i₁:υ,i₂:δ} <: σ → {i₂:δ,i₁:υ}`
::::

::::quiz
How about these?

  (A) `{i₁:⊤} <: ⊤`

  (B) `⊤ → (⊤ → ⊤)  <:  ⊤ → ⊤`

  (C) `{i₁:τ} → {i₁:τ}  <:  {i₁:τ,i₂:σ} → ⊤`

  (D) `{i₁:τ,i₂:δ,i₃:δ} <: {i₁:σ,i₂:υ} × {i₃:δ}`

  (E) `⊤ → {i₁:υ,i₂:δ} <: {i₁:σ} → {i₂:δ,i₁:δ}`
::::

## Exercises

:::::full

The following "thought exercises" are repeated later as formal
exercises.

::::exercise (rating := 1) (name := "subtype_instances_tf_1") (optional := true)

Suppose we have types `σ`, `τ`, `υ`, and `δ` with `σ <: τ`
and `υ <: δ`.  Which of the following subtyping assertions
are then true?  Write _true_ or _false_ after each one.
(`A`, `B`, and `C` here are base types like `Bool`, `Nat`, etc.

- `τ→σ <: τ→σ`
:::solution
      Answer: True
:::

- `⊤→υ <: σ→⊤`
:::solution
      Answer: True
:::
- `(C→C) → (A*B)  <:  (C→C) → (⊤*B)`
:::solution
      Answer: True
:::
- `τ→τ→υ <: σ→σ→V`
:::solution
      Answer: True
:::
- `(τ→τ)→υ <: (σ→σ)→V`
:::solution
      Answer: False
:::
- `((τ→σ)→τ)→υ <: ((σ→τ)→σ)→V`
:::solution
      Answer: True
:::
- `σ*δ <: τ*υ`
:::solution
      Answer: False
:::
::::

::::exercise (rating := 1) (name := "subtype_order") (manual := true)
The following types happen to form a linear order with respect to subtyping:
  - `⊤`
  - `⊤ → Student`
  - `Student → Person`
  - `Student → ⊤`
  - `Person → Student`

Write these types in order from the most specific to the most general.

:::solution
Answer: `⊤→Student <: Person→Student <: Student→Person <: Student→⊤ <: ⊤`
:::

Where does the type `⊤→⊤→Student` fit into this order?
That is, state how `⊤ → (⊤ → Student)` compares with each
of the five types above. It may be unrelated to some of them.

:::solution
Answer: It is less than `Student→⊤` (and `⊤`) and unrelated to the others.
:::

:::grade
`GRADE_MANUAL 2: subtype_order`
:::

::::

::::exercise (rating := 1) (name := "subtype_instances_tf_2") (manual := true)
Which of the following statements are true?  Write _true_ or
_false_ after each one. ∀
```display
      ∀ σ τ,
          σ <: τ  →
          σ→σ   <:  τ→τ
:::solution
      Answer: False
:::
```
```display
      ∀ σ,
           σ <: υ→υ →
           ∃ τ,
              σ = τ→τ  ∧  τ <: υ
```
:::solution
      Answer: False
:::

```display
      ∀ σ τ₁ τ₂,
           (σ <: τ₁ → τ₂) →
           ∃ σ₁ σ₂,
              σ = σ₁ → σ₂  ∧  τ₁ <: σ₁  ∧  σ₂ <: τ₂
```

:::solution
      Answer: True
:::

```display
      ∃ σ, σ <: σ → σ
```
:::solution
      Answer: False
:::

      ∃ σ,
           σ→σ <: σ
:::solution
      Answer: True
:::

```display
      ∀ σ τ₁ τ₂,
           σ <: τ₁×τ₂ →
           ∃ σ₁ σ₂,
              σ = σ₁×σ₂  ∧  σ₁ <: τ₁  ∧  σ₂ <: τ₂
```
:::solution
      Answer: True
:::

:::grade
`GRADE_MANUAL 2: subtype_instances_tf_2`
:::
::::

::::exercise (rating := 1) (name := "subtype_concepts_tf") (manual := true)

Which of the following statements are true, and which are false?
  - There exists a type that is a supertype of every other type.
:::solution
      True
:::
  - There exists a type that is a subtype of every other type.
:::solution
      False
:::
  - There exists a pair type that is a supertype of every other
    pair type.
:::solution
      True
:::
  - There exists a pair type that is a subtype of every other
    pair type.
:::solution
      False
:::
  - There exists an arrow type that is a supertype of every other
    arrow type.
:::solution
      False
:::
  - There exists an arrow type that is a subtype of every other
    arrow type.
:::solution
      False
:::
  - There is an infinite descending chain of distinct types in the
    subtype relation---that is, an infinite sequence of types
    `σ₀`, `σ₁`, etc., such that all the `σi`'s are different and
    each `σ(i+1)` is a subtype of `σi`.
:::solution
      True
:::
  - There is an infinite _ascending_ chain of distinct types in
    the subtype relation---that is, an infinite sequence of types
    `σ₀`, `σ₁`, etc., such that all the `σi`'s are different and
    each `σ(i+1)` is a supertype of `σi`.
:::solution
      True
:::

:::grade
`GRADE_MANUAL 1: subtype_concepts_tf`
:::
::::
:::::

:::::full
::::exercise (rating := 1) (name := "proper_subtypes") (manual := true)

Is the following statement true or false?  Briefly explain your
answer. (`A` here and below represents an arbitrary base type.)

```display
    ∀ τ,
         ~(τ = Bool ∨ ∃ n, τ = A) →
         ∃ σ,
            σ <: τ  ∧  σ <> τ
```

:::solution
Answer: False. `τ = ⊤→Bool` is a counterexample.
:::

:::grade
`GRADE_MANUAL 1: proper_subtypes`
:::
::::

::::exercise (rating := 2) (name := "small_large_1") (manual := true)
- What is the _smallest_ type `τ` ("smallest" in the subtype
  relation) that makes the following assertion true?  (Assume we
  have `Unit` among the base types and `unit` as a constant of this
  type. )

```display
  ∅ ⊢ (λp:τ×⊤. p.fst) ((λz:A,z). unit) ⦂ A→A
```

:::solution
```display
  τ = A → A
```
:::

- What is the _largest_ type `τ` that makes the same assertion true?
:::solution
```display
  τ = A → A
```
:::

:::grade
`GRADE_MANUAL 2: small_large_1`
:::
::::

::::exercise (rating := 2) (name := "small_large_2") (manual := true)
- What is the _smallest_ type `τ` that makes the following
  assertion true?

```display
       ∅ ⊢ (λp:(A→A × B→B), p) ((λz:A.z), (λz:B.z)) ⦂ τ
```

:::solution
```display
       τ  =  (A→A × B→B)
```

:::
   - What is the _largest_ type `τ` that makes the same assertion true?
:::solution
```display
       τ  =  ⊤
```
:::

:::grade
`GRADE_MANUAL 2: small_large_2`
:::
::::

::::exercise (rating := 2) (name := "small_large_3") (optional := true)
- What is the _smallest_ type `τ` that makes the following
  assertion true?
```display
       a:A ⊢ (λp:(A×τ). (p.snd) (p.fst)) (a. λz:A.z) ⦂ A
```
:::solution
```display
       τ = A→A
```
:::
- What is the _largest_ type `τ` that makes the same assertion true?

:::solution
     The same.

     Here's the reasoning in more detail:

     Clearly, `τ` must have the form `τ₁→τ₂`.

     Now we can read off the following constraints from the program:
     - `A  <:  τ₁`                 (from the application of p.snd to p.fst)
     - `τ₂  <:  A`                 (from the final result type)
     - `(A × A→A)  <:  (A × τ)`   (from the outer application)

     Inverting the last constraint tells us
```display
       A→A  <:  τ₁→τ₂
```
     and hence
```display
         τ₁ <: A
         A <: τ₂.
```
     So
```display
         τ = A→A
```
     is both the largest and the smallest type that makes
     the whole typing statement true.
:::
::::
:::::

::::quiz
What is the _smallest_ type `τ` that makes the following
assertion true?

```display
    a:A ⊢ (λp:(A×τ). (p.snd) (p.fst)) (a, λz:A. z) ⦂ A
```

   (A) `⊤`

   (B) `A`

   (C) `⊤→⊤`

   (D) `⊤→A`

   (E) `A→A`

   (F) `A→⊤`
::::

::::quiz
What is the _largest_ type `τ` that makes the following
assertion true?

```display
       a:A ⊢ (λp:(A×τ). (p.snd) (p.fst)) (a, λz:A.z) ⦂ A
```

   (A) `⊤`

   (B) `A`

   (C) `⊤→⊤`

   (D) `⊤→A`

   (E) `A→A`

   (F) `A→⊤`
::::

::::quiz

"The type `Bool` has no proper subtypes."  (I.e., the only
type smaller than `Bool` is `Bool` itself.)

(A) True

(B) False
::::

::::quiz

"Suppose `σ`, `τ₁`, and `τ₂` are types with `σ <: τ₁ → τ₂`.  Then
`σ` itself is an arrow type -- i.e., `σ = σ₁ → σ₂` for some `σ₁`
and `σ₂` -- with `τ₁` <: `σ₁` and `σ₂ <: τ₂`."

(A) True

(B) False

::::

:::::full
::::exercise (rating := 2) (name := "small_large_4") (manual := true)

- What is the _smallest_ type `τ` (if one exists) that makes the
  following assertion true?
```display
       ∃ σ,
         ∅ ⊢ (λp:(A*τ), (p.snd) (p.fst)) ⦂ σ
```
:::solution
     There is no smallest such type -- any type of the form `A → σ` for some
     type `σ` will make the assertion true, but there is no smallest one of
     these (there are infinitely many and they are incomparable).
:::
   - What is the _largest_ type `τ` that makes the same
     assertion true?
:::solution
```display
       τ  =  A → ⊤
```
:::

:::grade
`GRADE_MANUAL 2: small_large_4`
:::
::::

::::exercise (rating := 2) (name := "smallest_1") (manual := true)
What is the _smallest_ type `τ` (if one exists) that makes
the following assertion true?
```display
      exists σ t,
        ∅ ⊢ (\x:τ, x x) t ⦂ σ
```

:::grade
`GRADE_MANUAL 2: smallest_1`
:::

:::solution
Answer: Any type of the form `τ = ⊤→υ` will make the assertion
true, but there is no smallest one of these: 1⊤→A→A1 and
`⊤→B→B` are both solutions, but they have no common
subtype.
:::
::::

::::exercise (rating := 2) (name := "smallest_2") (manual := true)
What is the _smallest_ type `τ` that makes the following
assertion true?
```display
      ∅ ⊢ (\x:⊤, x) ((λz:A,z) , (λz:B,z)) ⦂ τ
```

:::grade
`GRADE_MANUAL 2: smallest_2`
:::
:::solution
```display
      τ  =  ⊤
```
:::
::::
:::::

:::::full
::::exercise (rating := 3) (name := "count_supertypes") (optional := true)
  How many supertypes does the record type `{x:A, y:C→C}` have?  That is,
  how many different types `τ` are there such that `{x:A, y:C→C} <: τ`?
  (We consider two types to be different if they are written
  differently, even if each is a subtype of the other.  For example,
  `{x:A,y:B}` and `{y:B,x:A}` are different.)

:::solution
Answer: Nineteen!
```display
   { x:A, y:C→C }                 { y:⊤, x:A }
   { x:⊤, y:C→C }               { y:⊤, x:⊤ }
   { x:A, y:C→⊤ }               { x:A }
   { x:⊤, y:C→⊤ }             { x:⊤ }
   { x:A, y:⊤ }                  { y:C→C }
   { x:⊤, y:⊤ }                { y:C→⊤ }
   { y:C→C, x:A }                 { y:⊤ }
   { y:C→C, x:⊤ }               { }
   { y:C→⊤, x:A }               ⊤
   { y:C→⊤, x:⊤ }
```
:::
::::

::::exercise (rating := 2) (name := "pair_permutation") (manual := true)
The subtyping rule for product types
```display
                            σ₁ <: τ₁    σ₂ <: τ₂
                            --------------------                        (prod)
                               σ₁*σ₂ <: τ₁*τ₂
```
intuitively corresponds to the "depth" subtyping rule for records.
Extending the analogy, we might consider adding a "permutation" rule
```display
                                   --------------
                                   τ₁*τ₂ <: τ₂*τ₁
```
for products.  Is this a good idea? Briefly explain why or why not.

:::solution
  Answer: No, since it will break preservation: `(tru,unit).1` has
  type `Unit` according to this rule, but reduces to `tru`, which
  does not have type `Unit`.
:::


:::grade
`GRADE_MANUAL 2: pair_permutation`
:::
::::
:::::

# Formal Definitions

```lean
namespace StlcSub

open scoped MyGetElem
```

Most of the definitions needed to formalize what we've discussed
above -- in particular, the syntax and operational semantics of
the language -- are identical to what we saw in the last chapter.
We just need to extend the typing relation with the subsumption
rule and add a new `inductive` definition for the subtyping
relation.  Let's first do the identical bits.

::::full
We include products in the syntax of types and terms, but not,
for the moment, anywhere else; the `products` exercise below will
ask you to extend the definitions of the value relation, operational
semantics, subtyping relation, and typing relation and to extend
the proofs of progress and preservation to fully support products.
::::

## Core Definitions

### Syntax

::::full
In the rest of the chapter, we formalize just base types,
booleans, arrow types, `Unit`, and `⊤`, omitting record types
and leaving product types as an exercise.  For the sake of more
interesting examples, we'll add an arbitrary set of base types
like `String`, `Float`, etc.  (Since they are just for examples,
we won't bother adding any operations over these base types, but
we could easily do so.)
::::

::::terse
Omitting records, to avoid dealing with "..." stuff.
::::

```lean
inductive Ty : Type where
  | top   : Ty
  | bool  : Ty
  | base  : String → Ty
  | arrow : Ty → Ty → Ty
  | unit  : Ty
  | prod : Ty → Ty → Ty

inductive Tm : Type where
  | var : String → Tm
  | app : Tm → Tm → Tm
  | abs : String → Ty → Tm → Tm
  | tru : Tm
  | fls : Tm
  | ite : Tm → Tm → Tm → Tm
  | unit : Tm
  | pair : Tm → Tm → Tm
  | fst : Tm → Tm
  | snd : Tm → Tm
```

::::details "Notation"
```lean
syntax:50 stlcTy:51 " × " stlcTy:50 : stlcTy
syntax:50 stlcTy:51 " + " stlcTy:50 : stlcTy
syntax:max " ⊤ " : stlcTy
syntax:51 " [ " stlcTy:50  " ] " : stlcTy

open Lean in
scoped macro_rules (kind := Stlc.tyBracket)
  | `(<{ ~$τ:term }>)    => pure τ
  | `(<{ ($τ:stlcTy) }>) => `(<{ $τ:stlcTy }>)
  | `(<{ ⊤ }>) => `(Ty.top)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Bool" => `(Ty.bool)
      | "Unit" => `(Ty.unit)
      | _ => `(Ty.base  $(quote x.getId.toString))
  | `(<{ $τ₁:stlcTy → $τ₂:stlcTy }>)  => `(Ty.arrow <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)
  | `(<{ $τ₁:stlcTy × $τ₂:stlcTy }>)  => `(Ty.prod <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)
  | `(<{ $τ₁:stlcTy -> $τ₂:stlcTy }>) => `(Ty.arrow <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)
```

```lean
#check <{ ⊤ × ⊤ }>
#check <{ Bool → ⊤ }>
#check <{ (Bool × Unit) -> Nat }>
```

```lean
scoped syntax:50 "if " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

scoped syntax:max " ( " stlcTm:60 " , " stlcTm:60 " ) " : stlcTm

open Lean in
scoped macro_rules (kind := Stlc.tmBracket)
  | `(<{ ~$e:term }>)    => pure e
  | `(<{ ($t:stlcTm) }>) => `(<{ $t:stlcTm }>)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Nat"  => Macro.throwErrorAt x "`Nat` is a type, not a term"
      | "Unit"  => Macro.throwErrorAt x "`Unit` is a type, not a term"
      | "fst" => Macro.throwErrorAt x "`fst` must be applied to an argument"
      | "snd" => Macro.throwErrorAt x "`snd` must be applied to an argument"
      | "unit" =>  `(Tm.unit)
      | "true" =>  `(Tm.tru)
      | "false" =>  `(Tm.fls)
      | _      => `(Tm.var $(quote x.getId.toString))
  | `(<{ λ $x : $τ . $t }>) => do
      `(Tm.abs $(← Stlc.varStr x) <{ $τ:stlcTy }> <{ $t:stlcTm }>)
  | `(<{ $t₁:stlcTm $t₂:stlcTm }>) =>
      match t₁ with
      | `(stlcTm| $f:ident) =>
          match f.getId.toString with
          | "fst" => `(Tm.fst <{ $t₂:stlcTm }>)
          | "snd" => `(Tm.snd <{ $t₂:stlcTm }>)
          | _      => `(Tm.app  <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
      | _ => `(Tm.app <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
  | `(<{ if $c then $t else $e }>) =>
      `(Tm.ite <{ $c:stlcTm }> <{ $t:stlcTm }> <{ $e:stlcTm }>)

  | `(<{ ( $t₁:stlcTm , $t₂:stlcTm ) }>) => `(Tm.pair <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
```

```lean
open Lean in
/-- Is `s` usable as a bare variable in `stlcTm` rather than as reserved syntax? -/
def isPlainTmVarName (s : String) : Bool :=
  Stlc.isPlainName s && s != "Bool" && s != "unit" && s != "Unit" && s != "if"

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTy` concrete syntax from a `Ty` value. -/
partial def delabTyInner : DelabM (TSyntax `stlcTy) := do
  let stx ←
    match_expr ← getExpr with
    | Ty.bool => `(stlcTy| $(mkIdent `Bool):ident)
    | Ty.unit => `(stlcTy| $(mkIdent `Unit):ident)
    | Ty.top => `(stlcTy| ⊤)
    | Ty.arrow _ _ => do
        let a ← withAppFn <| withAppArg delabTyInner
        let b ← withAppArg delabTyInner
        `(stlcTy| $a → $b)
    | Ty.prod _ _ => do
        let a ← withAppFn <| withAppArg delabTyInner
        let b ← withAppArg delabTyInner
        `(stlcTy| $a × $b)
    | Ty.base _ => do
        let b ← withAppArg delab
        `(stlcTy| ~($b))
    | _ => do
        match ← delab with
        | `($i:ident) => `(stlcTy| $i:ident)
        | e => `(stlcTy| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTm` concrete syntax from a `Tm` value. -/
partial def delabTmInner : DelabM (TSyntax `stlcTm) := do
  let stx ←
    match_expr ← getExpr with
    | Tm.var _ => do
        let x ← withAppArg delab
        match x with
        | `($s:str) =>
            if isPlainTmVarName s.getString then
              `(stlcTm| $(mkIdent (Name.mkSimple s.getString)):ident)
            else
              let var : Term := mkIdent ``Tm.var
              `(stlcTm| ~($var $x))
        | _ =>
            let var : Term := mkIdent ``Tm.var
            `(stlcTm| ~($var $x))
    | Tm.app _ _ => do
        let f ← withAppFn <| withAppArg delabTmInner
        let a ← withAppArg delabTmInner
        `(stlcTm| $f $a)
    | Tm.abs _ _ _ => do
        let x ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
        let τ ← withAppFn <| withAppArg delabTyInner
        let t ← withAppArg delabTmInner
        `(stlcTm| λ $x : $τ . $t)
    | Tm.ite _ _ _ => do
        let c ← withAppFn <| withAppFn <| withAppArg delabTmInner
        let t ← withAppFn <| withAppArg delabTmInner
        let e ← withAppArg delabTmInner
        `(stlcTm| if $c then $t else $e)
    | Tm.pair _ _ => do
        let a ← withAppFn <| withAppArg delabTmInner
        let b ← withAppArg delabTmInner
        `(stlcTm| ( $a , $b ) )
    | Tm.fst _ => do
        let b ← withAppArg delabTmInner
        `(stlcTm| $(mkIdent `fst):ident $b )
    | Tm.snd _ => do
        let b ← withAppArg delabTmInner
        `(stlcTm| $(mkIdent `snd):ident $b )
    | Tm.unit => do
        `(stlcTm| $(mkIdent `unit):ident)
    | Tm.tru => do
      `(stlcTm| $(mkIdent `true):ident)
    | Tm.fls => do
      `(stlcTm| $(mkIdent `false):ident)
    | _ => do
        -- `subst` is defined below, so it is matched by name rather than with
        -- `match_expr`; a substitution prints in its own bracket notation.
        let e ← getExpr
        if e.getAppFn.constName? == some `SltcExtended.subst && e.getAppNumArgs == 3 then
          let x ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
          let s ← withAppFn <| withAppArg delabTmInner
          let t ← withAppArg delabTmInner
          `(stlcTm| [$x := $s] $t)
        else
          match ← delab with
          | `($i:ident) => `(stlcTm| $i:ident)
          | e => `(stlcTm| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.StlcSub.Ty.bool, delab app.StlcSub.Ty.arrow, delab app.StlcSub.Ty.unit,
  delab app.StlcSub.Ty.prod, delab app.StlcSub.Ty.base, delab app.StlcSub.Ty.top]
def delabTy : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Ty.bool => true | Ty.arrow _ _ => true
    | Ty.prod _ _ => true | Ty.base _ => true | Ty.top => true
    | Ty.unit => true | _ => false
  match ← delabTyInner with
  | `(stlcTy| ~$e) => pure e
  | e => `(<{ $e:stlcTy }>)

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.StlcSub.Tm.var, delab app.StlcSub.Tm.app, delab app.StlcSub.Tm.abs,
  delab app.StlcSub.Tm.ite, delab app.StlcSub.Tm.pair,
  delab app.StlcSub.Tm.fst, delab app.StlcSub.Tm.snd, delab app.StlcSub.Tm.unit,
  delab app.StlcSub.Tm.tru, delab app.StlcSub.Tm.fls ]
def delabTm : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Tm.var _ => true | Tm.app _ _ => true | Tm.abs _ _ _ => true
    | Tm.ite _ _ _ => true | Tm.unit => true | Tm.tru => true | Tm.fls => true
    | Tm.pair _ _ => true | Tm.fst _ => true | Tm.snd _ => true
    | _ => false
  match ← delabTmInner with
  | `(stlcTm| ~($e)) => pure e
  | `(stlcTm| ~$e) => pure e
  | e => `(<{ $e:stlcTm }>)
```
::::

:::ignore
Checks that the extended grammar parses the way it should.

```lean -show
#check <{ λx : Nat. x }>
#check <{ if x then x else x }>
#check <{ if y x then x else x }>
#check <{ if (y x) then x else x }>
#check <{ (x , y) }>
#check <{ fst x }>
#check <{ fst (x , y) }>
#check <{ x (succ y) }>
#check <{ λ x : Bool . λ y : ⊤ . if x then true else false }>
```
:::


## Substitution

The definition of substitution remains exactly the same as for the
pure STLC.

```lean
section
set_option hygiene false in
local macro_rules (kind := Stlc.tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← Stlc.varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  -- pure STLC
  | .var y =>
      if x = y then s else t
  | <{ λ ~y : ~τ . ~t₁}> =>
      if x = y then t else <{ λ ~y : ~τ . [~x := ~s] ~t₁ }>
  | <{ ~t₁ ~t₂ }> =>
      <{ ([~x := ~s] ~t₁) ([~x := ~s] ~t₂) }>
  -- unit
  | .unit => <{ unit }>
  -- bools
  | <{ true }> => <{ true }>
  | <{ false }> => <{ false }>
  | <{ if ~t₁ then ~t₂ else ~t₃ }> =>
      <{ if [~x := ~s] ~t₁ then [~x := ~s] ~t₂ else [~x := ~s] ~t₃ }>

  -- Complete the following cases when you do the `products` exercise later
  | <{(~t₁, ~t₂)}> =>
      solution!(<{ ([~x := ~s] ~t₁ , [~x := ~s] ~t₂) }>)
  | Tm.fst t =>
      solution!(<{ fst ([~x := ~s] ~t)}>)
  | Tm.snd t =>
      solution!(<{ snd ([~x := ~s] ~t)}>)

end

macro_rules (kind := Stlc.tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← Stlc.varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)
```

## Reduction

Likewise the definitions of `IsValue` and `Step`.

```lean
inductive Tm.IsValue : Tm → Prop where
  | abs : ∀ x τ₂ t₁,
      IsValue <{λ ~x : ~τ₂ . ~t₁}>
  | tru :
      IsValue <{true}>
  | fls :
      IsValue <{false}>
  | unit :
      IsValue .unit

-- Fill in more rules when you do the `products` exercise later
-- SOLUTION
  | pair : ∀ v₁ v₂,
      IsValue v₁ →
      IsValue v₂ →
      IsValue <{(~v₁, ~v₂)}>

attribute [StlcSubEval] Tm.IsValue.pair
-- END SOLUTION

attribute [StlcSubEval] Tm.IsValue.abs Tm.IsValue.tru Tm.IsValue.fls Tm.IsValue.unit
```

```lean
section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
  -- pure STLC
  | appAbs (x : String) (τ₂ : Ty) (t₁ v₂ : Tm) :
        v₂.IsValue →
         <{(λ ~x: ~τ₂ . ~t₁) ~v₂}> ⟶ <{ [~x := ~v₂] ~t₁ }>
  | app₁ (t₁ t₁' t₂ : Tm) :
         t₁ ⟶ t₁' →
         <{~t₁ ~t₂}> ⟶ <{~t₁' ~t₂}>
  | app₂ (v₁ t₂ t₂' : Tm) :
        v₁.IsValue →
         t₂ ⟶ t₂' →
         <{~v₁ ~t₂}> ⟶ <{~v₁  ~t₂'}>
  -- booleans
  | ifStep (t₁ t₁' t₂ t₃ : Tm) (h : t₁ ⟶ t₁') :
      <{ if ~t₁ then ~t₂ else ~t₃ }> ⟶ <{ if ~t₁' then ~t₂ else ~t₃ }>
  | ifTrue (t₂ t₃ : Tm) :
      <{ if true then ~t₂ else ~t₃ }> ⟶ t₂
  | ifFalse (t₂ t₃ : Tm) :
      <{ if false then ~t₂ else ~t₃ }> ⟶ t₃

  -- Fill in more rules when you do the `products` exercise later
  -- SOLUTION
  | pair₁  (t₁ t₁' t₂ : Tm) :
        t₁ ⟶ t₁' →
        <{ (~t₁, ~t₂) }> ⟶ <{ (~t₁' , ~t₂) }>
  | pair₂ (v₁ t₂ t₂' : Tm) :
        v₁.IsValue →
        t₂ ⟶ t₂' →
        <{ (~v₁, ~t₂) }> ⟶  <{ (~v₁, ~t₂') }>
  | fst₁ (t t' : Tm) :
        t ⟶ t' →
        <{ fst ~t }> ⟶ <{ fst ~t' }>
  | fstPair (v₁ v₂ : Tm) :
        v₁.IsValue →
        v₂.IsValue →
        Tm.fst  <{ (~v₁ , ~v₂) }> ⟶ v₁
  | snd₁ (t t' : Tm) :
        t ⟶ t' →
        <{ snd ~t }> ⟶ <{ snd ~t' }>
  | sndPair (v₁ v₂ : Tm) :
        v₁.IsValue →
        v₂.IsValue →
        Tm.snd  <{ (~v₁, ~v₂) }> ⟶ v₂
  -- END SOLUTION
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

-- Be sure to add your constructors for pairs to this list later
attribute [StlcSubEval] Step.appAbs Step.app₁ Step.app₂
    Step.ifStep Step.ifTrue Step.ifFalse
-- SOLUTION
    Step.pair₁ Step.pair₂ Step.fst₁ Step.fstPair
    Step.snd₁ Step.sndPair
-- END SOLUTION
```

## Subtyping

::::full
Now we come to the interesting part.  We begin by defining
the subtyping relation and developing some of its important
technical properties.

The definition of subtyping is just what we sketched in the
motivating discussion.
::::

```lean
section
set_option hygiene false in
local notation:40 τ:41 " <: " τ':41 => Subtype τ τ'

inductive Subtype : Ty → Ty → Prop where
  | refl {τ : Ty} :
      τ <: τ
  | trans {σ υ τ: Ty}
      (h₁ : σ <: υ)
      (h₂ : υ <: τ) :
      σ <: τ
  | top {σ : Ty} :
      σ <: <{ ⊤ }>
  | arrow { σ₁ σ₂ τ₁ τ₂ : Ty}
      (h₁ : τ₁ <: σ₁)
      (h₂ : σ₂ <: τ₂) :
      <{ ~σ₁→~σ₂ }> <: <{ ~τ₁→~τ₂ }>

-- Fill in more rules when you do the `products` exercise later
-- SOLUTION
  | prod { σ₁ σ₂ τ₁ τ₂ : Ty}
      (h₁ : σ₁ <: τ₁)
      (h₂ : σ₂ <: τ₂) :
      <{ ~σ₁ × ~σ₂ }> <: <{ ~τ₁ × ~τ₂ }>
-- END SOLUTION
end

scoped notation:40 τ:41 " <: " τ':41 => Subtype τ τ'

attribute [StlcSubTyping] Subtype.refl Subtype.trans Subtype.top Subtype.arrow
-- SOLUTION
Subtype.prod
-- END SOLUTION
```

Note that we don't need any special rules for base types (`Bool`
and `Base`): they are automatically subtypes of themselves (by
`refl`) and `⊤` (by `top`), and that's all we want.

:::::full
```lean
namespace Examples

abbrev A := Ty.base "A"
abbrev B := Ty.base "B"
abbrev C := Ty.base "C"

abbrev String := Ty.base "String"
abbrev Float := Ty.base "Flat"
abbrev Int := Ty.base "Int"

example : <{ ~C → Bool }> <: <{ ~C → ⊤ }> := by
  solve_by_elim using StlcSubTyping
```

Note that, because the `Subtype` rules are not "syntax directed"
(e.g., given a goal of the form `⊤ <: ⊤`, you could apply the `top` rule,
the `refl` rule, the `trans` rule), we have to use {tactic}`solve_by_elim` here
instead of {tactic}`apply_rules`.

:::dev "Daniel Sainati (@dsainati)" PotentialImprovement
Potentially we could introduce the syntax-directed version of the subtyping judgment
here as a fix for this.
:::

::::exercise (rating := 2) (name := "subtyping_judgements") (optional := true)
Leave this exercise until after you have finished adding product
types to the language - see exercise `products` - at least up to
this point in the file.

Recall that, in chapter {ref "MoreStlc"}[MoreStlc], the optional section
"Encoding Records" describes how records can be encoded as pairs.
Using this encoding, define pair types representing the following
record types:

```display
    Person := { name : String }
    Student := { name : String ; gpa : Float }
    Employee := { name : String ; ssn : Integer }
```

```lean
def person : Ty := solution!(<{ String × ⊤ }>)
def student : Ty := solution!(<{ String × (⊤ × Float) }>)
def employee : Ty := solution!(<{ String × (Integer × ⊤) }>)
```

Now use the definition of the subtype relation to prove the following:

```lean
example : student <: person := by
  solution!
    rw [student, person]; solve_by_elim using StlcSubTyping

example : employee <: person := by
  solution!
    rw [employee, person]; solve_by_elim using StlcSubTyping
```
::::

The following facts are mostly easy to prove in Lean.  To get
full benefit from the exercises, make sure you also
understand how to prove them on paper!

::::exercise (rating := 1) (name := "subtyping_example_1") (optional := true)

```lean
example : <{ ⊤ → ~student }> <:  <{ (C → C) → ~person }> := by
  solution!
    rw [student, person]; solve_by_elim using StlcSubTyping
```
::::

::::exercise (rating := 1) (name := "subtyping_example_2") (optional := true)
```lean
example : <{ ⊤ → ~person }> <: <{ ~person → ⊤ }> := by
  solution!
    rw [person]; solve_by_elim using StlcSubTyping
```
::::

```lean
end Examples
```
:::::

## Typing

The only change to the typing relation is the addition of the rule
of subsumption, `sub`.

```lean
abbrev Context := PartialMap String Ty
```

:::details "Notation encoding: contexts and judgments"
The context grammar `stlcCtx` is reused as well; only the map it denotes is new,
since the types it stores are this language's.  As with `subst`, the judgment
rule is introduced twice: `local` and hygiene-free while the relation is being
declared, then again for real.

```lean
open Lean in
/-- The `Context` denoted by a context expression. -/
partial def ctxTerm (G : TSyntax `stlcCtx) : MacroM Term :=
  match G with
  | `(stlcCtx| ∅)   => `((∅ : Context))
  | `(stlcCtx| ~$e) => pure e
  | `(stlcCtx| $x:stlcVar ↦ $τ:stlcTy ; $G:stlcCtx) => do
      `(PartialMap.update $(← ctxTerm G) $(← Stlc.varStr x) <{ $τ:stlcTy }>)
  | _ => Macro.throwUnsupported

section StlcExtended
set_option hygiene false in
local macro_rules (kind := Stlc.judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $τ:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $τ:stlcTy }>)
```
:::

```lean
inductive HasType : Context → Tm → Ty → Prop where
  -- pure STLC
  | var (Γ : Context) (x : String) (τ₁ : Ty) (h : Γ[x] = some τ₁) :
      <{ ~Γ ⊢ ~(Tm.var x) ⦂ ~τ₁ }>
  | abs (Γ : Context) (x : String) (τ₁ τ₂ : Ty) (t₁ : Tm)
      (h : <{ ~x ↦ ~τ₂ ; ~Γ ⊢ ~t₁ ⦂ ~τ₁ }>) :
      <{ ~Γ ⊢ λ ~x : ~τ₂ . ~t₁ ⦂ ~τ₂ → ~τ₁ }>
  | app (Γ : Context) (τ₁ τ₂ : Ty) (t₁ t₂ : Tm)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ ~τ₂ → ~τ₁ }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~τ₂ }>) :
      <{ ~Γ ⊢ ~t₁ ~t₂ ⦂ ~τ₁ }>
  -- booleans
  | tru (Γ : Context) :
      <{ ~Γ ⊢ true ⦂ Bool }>
  | fls (Γ : Context) :
      <{ ~Γ ⊢ false ⦂ Bool }>
  | ite (Γ : Context) (t₁ t₂ t₃ : Tm) (τ : Ty)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ Bool }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~τ }>)
      (h₃ : <{ ~Γ ⊢ ~t₃ ⦂ ~τ }>) :
      <{ ~Γ ⊢ if ~t₁ then ~t₂ else ~t₃ ⦂ ~τ }>
  -- unit
  | unit (Γ : Context) :
      <{ ~Γ ⊢ unit ⦂ Unit }>
  -- subsumption
  | sub (Γ : Context) (t₁ : Tm) (τ₁ τ₂ : Ty)
      (ht : <{ ~Γ ⊢ ~t₁ ⦂ ~τ₁ }>)
      (hs : τ₁ <: τ₂) :
      <{ ~Γ ⊢ ~t₁ ⦂ ~τ₂ }>

  -- Fill in more rules when you do the `products` exercise later
  -- SOLUTION
  | pair (Γ : Context) (t₁ t₂ : Tm) (τ₁ τ₂ : Ty)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ ~τ₁ }>)
      (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~τ₂ }>) :
      <{ ~Γ ⊢ (~t₁, ~t₂) ⦂ ~τ₁ × ~τ₂ }>
  | fst (Γ : Context) (t : Tm) (τ₁ τ₂ : Ty)
      (h : <{ ~Γ ⊢ ~t ⦂ ~τ₁ × ~τ₂ }>) :
      <{ ~Γ ⊢ fst ~t ⦂ ~τ₁ }>
  | snd (Γ : Context) (t : Tm) (τ₁ τ₂ : Ty)
      (h : <{ ~Γ ⊢ ~t ⦂ ~τ₁ × ~τ₂ }>) :
      <{ ~Γ ⊢ snd ~t ⦂ ~τ₂ }>
  -- END SOLUTION

-- Make sure to add your constructors here
attribute [StlcSubTyping] HasType.var HasType.abs HasType.app
    HasType.ite HasType.tru HasType.fls HasType.unit
-- SOLUTION
    HasType.pair HasType.fst HasType.snd
-- END SOLUTION
```

We deliberately exclude `HasType.sub` from the list of constructors with the
`StlcSubTyping`. `apply_rules using StlcSubTyping` will search for derivations
without using the subtyping rule; if you want to make use of it in a derivation you will
need to do so yourself.

::::details "Notation encoding: the judgment, for real"
Closing the section retires the hygiene-free rule; the same rule is then
declared again, hygienically, for every later use, and a pair of unexpanders
prints judgments back in their own notation.

```lean
end StlcExtended

scoped macro_rules (kind := Stlc.judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $τ:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $τ:stlcTy }>)

open Lean PrettyPrinter in
/-- Rebuild `stlcCtx` syntax from the term syntax of a `Context`, so that a
context prints as `x ↦ Nat ; Γ` rather than as a chain of map updates. -/
partial def unexpandCtx : Term → UnexpandM (TSyntax `stlcCtx)
  | `(∅) => `(stlcCtx| ∅)
  | `($x:str →ₚ $τ) => do
      unexpandCtx (← `($x →ₚ $τ ; ∅))
  | `($x:str →ₚ $τ ; $G) => do
      let G' ← unexpandCtx G
      let x' : TSyntax `stlcVar ←
        if Stlc.isPlainName x.getString then
          `(stlcVar| $(mkIdent (Name.mkSimple x.getString)):ident)
        else `(stlcVar| ~$x)
      match τ with
      | `(<{ $T':stlcTy }>) => `(stlcCtx| $x':stlcVar ↦ $T' ; $G')
      | _                   => `(stlcCtx| $x':stlcVar ↦ ~($τ) ; $G')
  | G => `(stlcCtx| ~($G))

open Lean PrettyPrinter in
@[app_unexpander HasType]
def HasType.unexpand : Unexpander
  | `($_ $G <{ $t:stlcTm }> <{ $τ:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ $τ }>)
  | `($_ $G <{ $t:stlcTm }> $τ) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ ~($τ) }>)
  | `($_ $G $t <{ $τ:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ $τ }>)
  | `($_ $G $t $τ) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ ~($τ) }>)
  | _ => throw ()
```
::::

:::::full

```lean
namespace Examples
```

Do the following exercises after you have added product types to
the language.  For each informal typing judgement, write it as a
formal statement in Lean and prove it.

::::exercise (rating := 1) (name := "typing_example_0") (optional := true)
```display
∅ ⊢ ((λz:A.z), (λz:B,z)) ⦂ (A→A × B→B)
```

:::solution
```lean
example : <{ ∅ ⊢ ((λz : ~A . z), (λz : ~B . z)) ⦂ ((~A → ~A) × (~B → ~B)) }> := by
  apply_rules using StlcSubTyping
```
:::
::::

::::exercise (rating := 2) (name := "typing_example_1") (optional := true)

```display
∅ ⊢ (λx:(⊤ × B→B). snd x) ((λz:A. z), (λz:B. z)) ⦂ B→B
```

:::solution
```lean
example : <{ ∅ ⊢ (λx: (⊤ × (~B → ~B)). snd x) (((λz: ~A . z), (λz: ~B . z))) ⦂ ( ~B → ~B) }> := by
  apply_rules using StlcSubTyping
  apply HasType.sub
  · apply HasType.abs; apply HasType.var; rfl
  · apply Subtype.top
```
:::
::::

::::exercise (rating := 2) (name := "typing_example_2") (optional := true)
```display
∅ ⊢ (λz:(C→C)→(⊤ × B→B). snd (z (λx:C.x))) (λz:C→C. ((λz:A. z), (λz:B. z))) ⦂ B→B
```

:::solution
```lean
example :
  <{ ∅ ⊢(λz : (~C → ~C) → (⊤ × ~B → ~B) . snd (z (λx: ~C . x)))
          (λz: ~C → ~C . ((λ z : ~A . z), (λ z : ~B . z))) ⦂ (~B → ~B) }> := by
    apply_rules using StlcSubTyping
    apply HasType.sub
    · apply HasType.abs; apply HasType.var; rfl
    · apply Subtype.top
```
:::
::::

```lean
end Examples
```
:::::

# Properties

::::full
The fundamental properties of the system that we want to
check are the same as always: progress and preservation.
However, their proofs do become a little bit more involved.
::::

::::terse
We want the same properties as always: progress + preservation.

- _Statements_ of these theorems don't need to change, compared
  to pure STLC

- But _proofs_ are a bit more involved, to account for the
  additional flexibility in the typing relation
::::

## Inversion Lemmas for Subtyping

Before we look at the properties of the typing relation, we need
to establish a couple of critical structural properties of the
subtype relation:
  - `Bool` is the only subtype of `Bool`, and
  - every subtype of an arrow type is itself an arrow type.

:::full
These are called _inversion lemmas_ because they play a
similar role in proofs as the `inversion` tactic: given a
hypothesis that there exists a derivation of some subtyping
statement `σ <: τ` and some constraints on the shape of `σ` and/or
`τ`, each inversion lemma reasons about what this derivation must
look like to tell us something further about the shapes of `σ` and
`τ` and the existence of subtype relations between their parts.
:::

:::terse
Formally:
:::

:::::full
::::exercise (rating := 2) (name := "sub_inversion_bool") (optional := true)
```lean
theorem sub_inversion_bool (τ : Ty)
    (h : τ <: <{ Bool }>) :
    τ = Ty.bool := by
  solution!
    generalize heq : Ty.bool = σ at h
    induction h with (subst_vars; try contradiction)
    | refl => rfl
    | trans h₁ h₂ ih₁ ih₂ =>
        rw [ih₁]; apply ih₂ rfl
        symm; apply ih₂ rfl
```
::::
:::::

:::::full
::::exercise (rating := 3) (name := "sub_inversion_arrow")
```lean
theorem sub_inversion_arrow {σ τ₁ τ₂ : Ty}
     (h : σ <: <{ ~τ₁ → ~τ₂ }>) :
     ∃ σ₁ σ₂,
     σ = <{ ~σ₁ → ~σ₂ }> ∧ τ₁ <: σ₁ ∧ σ₂ <: τ₂ := by
  solution!
    generalize heq : <{ ~τ₁ → ~τ₂ }> = τ at h
    induction h generalizing τ₁ τ₂ with (subst_vars; try contradiction)
    | refl =>
        exists τ₁, τ₂; constructor; rfl
        constructor <;> constructor
    | @arrow σ₁ σ₂ _ _ h₁ h₂ ih₁ ih₂ =>
        inversion heq; exists σ₁, σ₂
    | trans h₁ h₂ ih₁ ih₂ =>
        obtain ⟨σ₁, σ₂, _, hs₁, hs₂⟩ := ih₂ rfl; clear ih₂; subst_vars
        obtain ⟨σ₁', σ₂', _, hs₁', hs₂'⟩ := ih₁ rfl; subst_vars; clear ih₁
        exists σ₁', σ₂'; constructor; rfl; constructor
        · exact Subtype.trans hs₁ hs₁'
        · exact Subtype.trans hs₂' hs₂
```

:::gradeTheorem 3 sub_inversion_arrow
:::

::::
:::::

::::full
There are additional _inversion lemmas_ for the other types:
- `Unit` is the only subtype of `Unit`, and
- `Base n` is the only subtype of `Base n`, and
- `⊤` is the only supertype of `⊤`.
::::

:::::full
::::exercise (rating := 2) (name := "sub_inversion_unit") (optional := true)
```lean
theorem sub_inversion_unit {τ : Ty} (h : τ <: <{ Unit }>) : τ = Ty.unit := by
  solution!
    generalize heq : Ty.unit = σ at h
    induction h with (subst_vars; try contradiction)
    | refl => rfl
    | trans h₁ h₂ ih₁ ih₂ =>
        rw [ih₁]; apply ih₂ rfl
        symm; apply ih₂ rfl
```
::::

::::exercise (rating := 2) (name := "sub_inversion_base") (optional := true)
```lean
theorem sub_inversion_base {τ : Ty} {s : String} (h : τ <: Ty.base s) : τ = Ty.base s := by
  solution!
    generalize heq : Ty.base s = σ at h
    induction h with (subst_vars; try contradiction)
    | refl => rfl
    | trans h₁ h₂ ih₁ ih₂ =>
        rw [ih₁]; apply ih₂ rfl
        symm; apply ih₂ rfl
```
::::

::::exercise (rating := 2) (name := "sub_inversion_top") (optional := true)
```lean
theorem sub_inversion_top {τ : Ty} (h : Ty.top <: τ) : τ = Ty.top := by
  solution!
    generalize heq : Ty.top = σ at h
    induction h with (subst_vars; try contradiction)
    | refl => rfl
    | top => rfl
    | trans h₁ h₂ ih₁ ih₂ =>
        rw [ih₂]; apply ih₁ rfl
        symm; apply ih₁ rfl
```
::::
:::::

::::full
When you do the `products` exercise, add your inversion lemma for products here:
```lean
-- SOLUTION
theorem sub_inversion_prod {σ τ₁ τ₂ : Ty} (h : σ <: <{ ~τ₁ × ~τ₂ }>) :
     ∃ σ₁ σ₂, σ = <{ ~σ₁ × ~σ₂ }> ∧ σ₁ <: τ₁ ∧ σ₂ <: τ₂ := by
  solution!
    generalize heq : <{ ~τ₁ × ~τ₂ }> = V at h
    induction h generalizing τ₁ τ₂ with (subst_vars; try contradiction)
    | refl =>
        exists τ₁, τ₂; constructor; rfl
        constructor <;> constructor
    | @prod σ₁ σ₂ _ _ h₁ h₂ ih₁ ih₂ =>
        inversion heq; exists σ₁, σ₂
    | trans h₁ h₂ ih₁ ih₂ =>
        obtain ⟨σ₁, σ₂, _, hs₁, hs₂⟩ := ih₂ rfl; clear ih₂; subst_vars
        obtain ⟨σ₁', σ₂', _, hs₁', hs₂'⟩ := ih₁ rfl; subst_vars; clear ih₁
        exists σ₁', σ₂'; constructor; rfl; constructor
        · exact Subtype.trans hs₁' hs₁
        · exact Subtype.trans hs₂' hs₂
-- END SOLUTION
```
::::

## Canonical Forms

:::full
The proof of the progress theorem -- that a well-typed
non-value can always take a step -- doesn't need to change too
much: we just need one small refinement.  When we're considering
the case where the term in question is an application `t₁ t₂`
where both `t₁` and `t₂` are values, we need to know that `t₁` has
the _form_ of a lambda-abstraction, so that we can apply the
`abs` reduction rule.  In the ordinary STLC, this is
obvious: we know that `t₁` has a function type `τ₁₁→τ₁₂`, and
there is only one rule that can be used to give a function type to
a value - rule `abs` - and the form of the conclusion of this
rule forces `t₁` to be an abstraction.

In the STLC with subtyping, this reasoning doesn't quite work
because there's another rule that can be used to show that a value
has a function type: subsumption.  Fortunately, this possibility
doesn't change things much: if the last rule used to show `Γ ⊢ t₁ ⦂ τ₁₁→τ₁₂` is subsumption,
then there is some _sub_-derivation whose subject is also `t₁`, and we can reason by
induction until we finally bottom out at a use of `abs`.

This bit of reasoning is packaged up in the following lemma, which
tells us the possible "canonical forms" (i.e., values) of function
type.
:::

:::terse
The proof of progress uses facts of the form "every value
belonging to an arrow type is an abstraction."

In the pure STLC, such facts are "immediate from the
definition" (formally, they follow directly by {tactic}`inversion`).

With subtyping, they require real proofs by induction...
:::

:::::full
::::exercise (rating := 3) (name := "canonical_forms_of_arrow_types") (optional := true)
```lean
theorem canonical_forms_of_arrow_types {Γ : Context} {t : Tm} {τ₁ τ₂ : Ty}
  (ht : <{ ~Γ ⊢ ~t ⦂ ~τ₁ → ~τ₂ }>)
  (hv : t.IsValue) :
  ∃ x σ₁ t₂, t = <{λ ~x : ~σ₁ . ~t₂}> := by
  solution!
    generalize heq : <{ ~τ₁ → ~τ₂ }> = τ at ht
    induction ht generalizing τ₁ τ₂ with (subst_vars; try contradiction)
    | abs Γ x τ₁ τ₂ t₁ h ih => inversion heq; exists x, τ₂, t₁
    | sub Γ t₁ τ₁ τ₂ ht hs ih =>
        obtain ⟨σ₁, σ₂, _, hs₁, hs₂⟩ := sub_inversion_arrow hs; subst_vars
        exact ih hv rfl
```
::::


Similarly, the canonical forms of type `Bool` are the constants
`tru` and `fls`

```lean
theorem canonical_forms_of_bool {Γ : Context} {t : Tm}
  (ht : <{ ~Γ ⊢ ~t ⦂ Bool }>)
  (hv : t.IsValue) :
  t = Tm.tru ∨ t = Tm.fls := by

  generalize heq : Ty.bool = τ at ht
  induction ht with (subst_vars; first | trivial | try lia)
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
    apply sub_inversion_bool at hs; subst_vars
    exact ih hv rfl
```


When you do the `products` exercise, add your canonical forms lemma for products here:

```lean
-- SOLUTION
theorem canonical_forms_of_product_types {Γ : Context} {t : Tm} {τ₁ τ₂ : Ty}
  (ht : <{ ~Γ ⊢ ~t ⦂ ~τ₁ × ~τ₂ }>)
  (hv : t.IsValue) :
  ∃ t₁ t₂, t = <{ (~t₁, ~t₂) }> := by
    generalize heq : <{ ~τ₁ × ~τ₂ }> = τ at ht
    induction ht generalizing τ₁ τ₂ with (subst_vars; try contradiction)
    | pair Γ t₁ t₂ τ₁ τ₂ h ih => inversion heq; exists t₁, t₂
    | sub Γ t₁ τ₁ τ₂ ht hs ih =>
        obtain ⟨σ₁, σ₂, _, hs₁, hs₂⟩ := sub_inversion_prod hs; subst_vars
        exact ih hv rfl
-- END SOLUTION
```
:::::

## Progress

:::::full
The proof of progress now proceeds just like the one for the
pure STLC, except that in several places we invoke canonical forms
lemmas...

_Theorem_ (Progress): For any term `t` and type `τ`, if `∅ ⊢ t ⦂ τ` then `t` is a value or
  `t ⟶ t'` for some term `t'`.

_Proof_: Let `t` and `τ` be given, with `∅ ⊢ t ⦂ τ`.
Proceed by induction on the typing derivation.

The cases for `abs`, `unit`, `tru` and `fls` are
immediate because abstractions, `unit`, `true`, and
`false` are already values.  The `var` case is vacuous
because variables cannot be typed in the empty context.  The
remaining cases are more interesting:

- If the last step in the typing derivation uses rule `app`,
  then there are terms `t₁` `t₂` and types `τ₁` and `τ₂` such that
  `t = t₁ t₂`, `τ = τ₂`, `∅ ⊢ t₁ ⦂ τ₁ → τ₂`, and `∅ ⊢ t₂ ⦂ τ₁`.
  Moreover, by the induction hypothesis, either
  `t₁` is a value or it steps, and either `t₂` is a value or it
  steps.  There are three possibilities to consider:

  - First, suppose `t₁ ⟶ t₁'` for some term `t₁'`.  Then `t₁ t₂ ⟶ t₁' t₂` by `app₁'`.

  - Second, suppose `t₁` is a value and `t₂ ⟶ t₂'` for some term
    `t₂'`.  Then `t₁ t₂ ⟶ t₁ t₂'` by rule `app₂` because `t₁`
    is a value.

  - Third, suppose `t₁` and `t₂` are both values.  By the
    canonical forms lemma for arrow types, we know that `t₁` has
    the form `λ x : σ₁ . t₂` for some `x`, `σ₁`, and `s₂`.  But then
    `(λ x : σ₁ . s₂) t₂ ⟶ [x := t₂] s₂` by `appAbs`, since `t₂` is a
    value.

- If the final step of the derivation uses rule `if`, then
  there are terms `t₁`, `t₂`, and `t₃` such that `t = if t₁ then t₂ else t₃`,
  with `∅ ⊢ t₁ ⦂ Bool` and with `∅ ⊢ t₂ ⦂ τ` and `∅ ⊢ t₃ ⦂ τ`.  Moreover, by the
  induction hypothesis, either `t₁` is a value or it steps.

    - If `t₁` is a value, then by the canonical forms lemma for
      booleans, either `t₁ = true` or `t₁ = false`.  In
      either case, `t` can step, using rule `ifTrue` or
      `ifFalse`.

    - If `t₁` can step, then so can `t`, by rule `if`.

- If the final step of the derivation is by `sub`, then there is
  a type `τ₂` such that `τ₁ <: τ₂` and `∅ ⊢ t₁ ⦂ τ₁`.  The
  desired result is exactly the induction hypothesis for the
  typing subderivation.
:::::

Formally:

```lean
theorem progress (t : Tm) (τ : Ty) (h : <{ ∅ ⊢ ~t ⦂ ~τ }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  generalize heq : (∅ : Context) = Γ at h
  induction h with (subst_vars; first
    | contradiction
    -- discharge cases where `t` is obviously a value
    | try (left; constructor; done)
  )
  | app Γ τ₁ τ₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      right; cases ih₁ rfl
      -- t₁ is a value
      case _ ht₁ =>
        cases ih₂ rfl
        -- t₂ is a value
        case _ ht₂ =>
          apply canonical_forms_of_arrow_types at h₁
          let ⟨x, σ, v, hv⟩ := h₁ ht₁
          exists <{ [~x := ~t₂] ~v }>; simp [hv]
          apply_rules using StlcSubEval
        -- t₂ is not a value
        case _ ht₂ =>
          obtain ⟨t₂', ht₂⟩ := ht₂
          exists <{~t₁ ~t₂'}>; apply_rules using StlcSubEval
      -- t₁ is not a value
      case _ ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        exists <{~t₁' ~t₂}>; apply_rules using StlcSubEval
  | ite Γ t₁ t₂ t₃ τ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    right; cases ih₁ rfl
    -- t₁ is a value
    case _ ht₁ =>
      apply canonical_forms_of_bool at h₁
      obtain h₁ | h₁ := h₁ ht₁ <;> subst_vars
      · exists t₂; apply_rules using StlcSubEval
      · exists t₃; apply_rules using StlcSubEval
    -- t₁ is not a value
    case _ ht₁ =>
      obtain ⟨t₁', ht₁⟩ := ht₁
      exists <{if ~t₁' then ~t₂ else ~t₃}>; apply_rules using StlcSubEval
  | sub Γ t₁ τ₁ τ₂ ht hs ih => apply ih; rfl
-- Fill in products here later
-- SOLUTION
  | pair Γ t₁ t₂ τ₁ τ₂ h₁ h₂ ih₁ ih₂ =>
      cases ih₁ rfl
      -- t₁ is a value
      case _ ht₁ =>
        cases ih₂ rfl
        -- t₂ is a value
        case _ ht₂ =>
          left; apply_rules using StlcSubEval
        -- t₂ is not a value
        case _ ht₂ =>
          obtain ⟨t₂', ht₂⟩ := ht₂
          right; exists <{(~t₁, ~t₂')}>; apply_rules using StlcSubEval
      -- t₁ is not a value
      case _ ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        right; exists <{(~t₁', ~t₂)}>; apply_rules using StlcSubEval
  | fst Γ t τ₁ τ₂ h ih =>
      right; cases ih rfl
      -- t₁ is a value
      case _ ht₁ =>
        apply canonical_forms_of_product_types at h
        obtain ⟨v₁, v₂, hv⟩ := h ht₁; rw [hv]; subst_vars; inversion ht₁
        exists v₁; apply_rules using StlcSubEval
      -- t₁ is not a value
      case _ ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        exists <{fst ~t₁'}>; apply_rules using StlcSubEval
  | snd Γ t τ₁ τ₂ h ih =>
      right; cases ih rfl
      -- t₁ is a value
      case _ ht₁ =>
        apply canonical_forms_of_product_types at h
        obtain ⟨v₁, v₂, hv⟩ := h ht₁; rw [hv]; subst_vars; inversion ht₁
        exists v₂; apply_rules using StlcSubEval
      -- t₁ is not a value
      case _ ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        exists <{snd ~t₁'}>; apply_rules using StlcSubEval
-- END SOLUTION
```

## Inversion Lemmas for Typing

::::full
The proof of the preservation theorem also becomes a little more
complex with the addition of subtyping.  The reason is that, as
with the "inversion lemmas for subtyping" above, there are a
number of facts about the typing relation that are immediate from
the definition in the pure STLC (formally: that can be obtained
directly from the {tactic}`inversion` tactic) but that require real proofs
in the presence of subtyping because there are multiple ways to
derive the same `HasType` statement.

The following inversion lemma tells us that, if we have a
derivation of some typing statement `Γ ⊢ λ x : σ₁ . t₂ ⦂ τ` whose
subject is an abstraction, then there must be some subderivation
giving a type to the body `t₂`.
::::

::::terse
We also need to prove an inversion lemma corresponding to a
structural fact about the typing relation that is "obvious from
the definition" in pure STLC.
::::

::::full
_Lemma_: If `Γ ⊢ λ x : σ₁ . t₂ ⦂ τ`, then there is a type `σ₂`
  such that `x ↦ σ₁ ;  Γ ⊢ t₂ ⦂ σ` and `σ₁ → σ₂ <: τ`.

  Notice that the lemma does _not_ say, "then `τ` itself is an arrow
  type" -- this is tempting, but false!  (Why?)
::::

::::terse
_Lemma_: If `Γ ⊢ λ x : σ₁ . t₂ ⦂ τ`, then there is a type `σ₂`
  such that `x ↦ σ₁ ;  Γ ⊢ t₂ ⦂ σ` and `σ₁ → σ₂ <: τ`.
::::

_Proof_: Let `Γ`, `x`, `σ₁`, `t₂` and `τ` be given as
    described.  Proceed by induction on the derivation of `Γ ⊢ λ x : σ₁ . t₂ ⦂ τ`.
     The cases for `var` and `app` are vacuous
    as those rules cannot be used to give a type to a syntactic
    abstraction.

  - If the last step of the derivation is a use of `abs` then
    there is a type `τ₁₂` such that `τ = σ₁ → τ₁₂` and `x ↦ σ₁; Γ ⊢ t₂ ⦂ τ₁₂`.
    Picking `τ₁₂` for `σ₂` gives us what we
    need, since `σ₁ → τ₁₂ <: σ₁ → τ₁₂` follows from {tactic}`rfl`.


  - If the last step of the derivation is a use of `sub` then
    there is a type `σ` such that `σ <: τ` and `Γ ⊢ λx : σ₁, t₂ ⦂ σ`.
    The IH for the typing subderivation tells us that there
    is some type `σ₂` with `σ₁ → σ₂ <: σ` and `x↦σ₁; Γ ⊢ t₂ ⦂ σ₂`.
    Picking type `σ₂` gives us what we need, since `σ₁ → σ₂ <: τ` then follows by `trans`.


Formally:

```lean
theorem typing_inversion_abs {Γ : Context} {x : String} {σ₁ : Ty} {t₂ : Tm} {τ : Ty}
  (h : <{ ~Γ ⊢ λ ~x : ~σ₁ . ~t₂ ⦂ ~τ }>) :
    ∃ σ₂, <{ ~σ₁ → ~σ₂ }> <: τ ∧ <{ ~x ↦ ~σ₁ ; ~Γ ⊢ ~t₂ ⦂ ~σ₂ }> := by

  generalize heq : <{ λ ~x : ~σ₁ . ~t₂ }> = t at h
  induction h with (subst_vars; try contradiction)
  | abs Γ x τ₁ τ₂ t₁ h i =>
      inversion heq; exists τ₁; solve_by_elim using StlcSubTyping
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
      obtain ⟨σ₂, hs', ht'⟩ := ih rfl
      exists σ₂; solve_by_elim using StlcSubTyping
```

:::terse
Similarly:
:::

:::::full
::::exercise (rating := 3) (name := "typing_inversion_var") (optional := true)
```lean
theorem typing_inversion_var {Γ : Context} {x : String} {τ : Ty}
  (h : <{ ~Γ ⊢ ~(.var x) ⦂ ~τ }>) :
  ∃ σ, Γ[x] = some σ ∧ σ <: τ := by

  solution!
    generalize heq : Tm.var x = t at h
    induction h with (subst_vars; try contradiction)
    | var Γ y τ₁ h => inversion heq; solve_by_elim using StlcSubTyping
    | sub Γ t₁ τ₁ τ₂ ht hs ih =>
        obtain ⟨σ₂, hs', ht'⟩ := ih rfl
        exists σ₂; solve_by_elim using StlcSubTyping
```
::::
:::::

:::::full
::::exercise (rating := 3) (name := "typing_inversion_app") (optional := true)
```lean
theorem typing_inversion_app {Γ : Context} {t₁ t₂ : Tm} {τ₂ : Ty}
  (h : <{ ~Γ ⊢ ~t₁ ~t₂ ⦂ ~τ₂ }>) :
  ∃ τ₁, <{ ~Γ ⊢ ~t₁ ⦂ ~τ₁ → ~τ₂ }> ∧ <{ ~Γ ⊢ ~t₂ ⦂ ~τ₁ }> := by
  solution!
    generalize heq : <{ ~t₁ ~t₂ }> = t at h
    induction h with (subst_vars; try contradiction)
    | app => inversion heq; solve_by_elim using StlcSubTyping
    | sub Γ t₁ τ₁ τ₂ ht hs ih =>
        obtain ⟨σ₂, hs', ht'⟩ := ih rfl
        exists σ₂; constructor <;> try assumption
        apply HasType.sub _ _ _ _ hs'
        solve_by_elim using StlcSubTyping
```
::::
:::::

```lean
theorem typing_inversion_unit (Γ : Context) (τ : Ty)
  (h : <{ ~Γ ⊢ unit ⦂ ~τ }>) :
  <{ Unit }> <: τ := by

  generalize heq : Tm.unit = t at h
  induction h with (subst_vars; try contradiction)
  | unit => inversion heq; solve_by_elim using StlcSubTyping
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
      specialize ih rfl
      solve_by_elim using StlcSubTyping
```

-- Add your lemmas for products here when you get to that exercise

```lean
-- SOLUTION
theorem typing_inversion_pair {Γ : Context} {t₁ t₂ : Tm} {τ : Ty}
  (h : <{ ~Γ ⊢ (~t₁, ~t₂) ⦂ ~τ }>) :
  ∃ τ₁ τ₂, <{ ~τ₁ × ~τ₂ }> <: τ ∧ <{ ~Γ ⊢ ~t₁ ⦂ ~τ₁ }> ∧ <{ ~Γ ⊢ ~t₂ ⦂ ~τ₂ }> := by

    generalize heq : <{ (~t₁, ~t₂) }> = t at h
    induction h generalizing t₁ t₂ with (subst_vars; try contradiction)
    | pair Γ t₁ t₂ τ₁ τ₂ h₁ h₂ ih₁ ih₂ =>
        inversion heq; exists τ₁, τ₂; solve_by_elim using StlcSubTyping
    | sub Γ t₁ τ₁ τ₂ ht hs ih =>
      obtain ⟨σ₁, σ₂, hs', ht₁, ht₂⟩ := ih rfl
      exists σ₁, σ₂; solve_by_elim (maxDepth := 10) using StlcSubTyping

theorem typing_inversion_fst {Γ : Context} {t : Tm} {τ: Ty}
  (h : <{ ~Γ ⊢ fst ~t ⦂ ~τ }>) :
  ∃ τ₁ τ₂,
    τ₁ <: τ ∧ <{ ~Γ ⊢ ~t ⦂ ~τ₁ × ~τ₂ }> := by

  generalize heq : <{ fst ~t }> = t' at h
  induction h generalizing t with (subst_vars; try contradiction)
    | fst Γ t τ₁ τ₂ h ih =>
        inversion heq; exists τ₁, τ₂; solve_by_elim using StlcSubTyping
    | sub Γ t₁ τ₁ τ₂ ht hs ih =>
      obtain ⟨σ₁, σ₂, hs', ht'⟩ := ih rfl
      exists σ₁, σ₂; solve_by_elim using StlcSubTyping

theorem typing_inversion_snd {Γ : Context} {t : Tm} {τ: Ty}
  (h : <{ ~Γ ⊢ snd ~t ⦂ ~τ }>) :
  ∃ τ₁ τ₂,
    τ₂ <: τ ∧ <{ ~Γ ⊢ ~t ⦂ ~τ₁ × ~τ₂ }> := by

  generalize heq : <{ snd ~t }> = t' at h
  induction h generalizing t with (subst_vars; try contradiction)
  | snd Γ t τ₁ τ₂ h ih =>
      inversion heq; exists τ₁, τ₂; solve_by_elim using StlcSubTyping
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
    obtain ⟨σ₁, σ₂, hs', ht'⟩ := ih rfl
    exists σ₁, σ₂; solve_by_elim using StlcSubTyping
-- END SOLUTION
```

The inversion lemmas for typing and for subtyping between arrow
types can be packaged up as a useful "combination lemma" telling
us exactly what we'll actually require below.

```lean
theorem abs_arrow {x : String} {t₂ : Tm} {σ₁ τ₁ τ₂ : Ty}
  (h : <{ ∅ ⊢ λ ~x : ~σ₁ . ~t₂ ⦂ ~τ₁ → ~τ₂ }> ) :
  τ₁ <: σ₁ ∧ <{ ~x ↦ ~σ₁ ; ∅ ⊢ ~t₂ ⦂ ~τ₂ }> := by
    obtain ⟨σ₂, hs, ht⟩ := typing_inversion_abs h; clear h
    obtain ⟨_, _, heq, hs₁, hs₂⟩ := sub_inversion_arrow hs; clear hs
    inversion heq; constructor
    · solve_by_elim using StlcSubTyping
    · apply HasType.sub <;> solve_by_elim using StlcSubTyping
```

## Weakening

The weakening lemma is proved as in pure STLC, with the exception of the `sub` case,
which requires a manual use of the `sub` rule.

```lean
theorem weakening {Γ Γ' : Context} {t : Tm} {τ: Ty}
    (hi : Γ ⊆ Γ')
    (ht : <{ ~Γ ⊢ ~t ⦂ ~τ }>) :
     <{ ~Γ' ⊢ ~t ⦂ ~τ }> := by
  induction ht generalizing Γ' with (try apply_rules [PartialMap.update_subset] using StlcSubTyping)
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
    apply HasType.sub <;> solve_by_elim using StlcSubTyping

theorem weakening_empty {Γ : Context} {t : Tm} {τ: Ty}
    (ht :<{ ∅ ⊢ ~t ⦂ ~τ }>) :
    <{ ~Γ ⊢ ~t ⦂ ~τ }> := by
  apply weakening _ ht
  intro _ _ h
  rw [PartialMap.getElem_empty] at h
  contradiction
```

## Substitution

:::full
When subtyping is involved proofs are generally easier
when done by induction on typing derivations, rather than on terms.
The _substitution lemma_ is proved as for pure STLC, but using
induction on the typing derivation this time (see Exercise
`substitution_preserves_typing_from_typing_ind` in {ref "StlcProp"}[StlcProp]).
:::


:::terse
The _substitution lemma_ is stated exactly as in pure STLC.

The proof is also the same except that here it is easier to use
induction on typing derivations rather than on terms.
:::

```lean
theorem substitution_preserves_typing {Γ : Context} {x : String} {τ₁ : Ty} {t v : Tm} {τ : Ty}
    (ht : <{ ~x ↦ ~τ₁ ; ~Γ ⊢ ~t ⦂ ~τ }>)
    (hv : <{ ∅ ⊢ ~v ⦂ ~τ₁ }>) :
    <{ ~Γ ⊢ [~x := ~v] ~t ⦂ ~τ }> := by

  generalize heq : x →ₚ τ₁ ; Γ = Γ' at ht
  induction ht generalizing x Γ with (
    subst_vars; try rw [subst]; try (apply_rules using StlcSubTyping; done))
  | var Γ y σ h =>
      by_cases h₁ : x = y
      · subst h₁; simp at h; subst h;
        apply weakening_empty at hv
        simp; assumption
      · rw [PartialMap.update_neq] at h <;> simp_all
        apply_rules using StlcSubTyping
  | abs _ y _ _ _ h ih =>
      by_cases h₁ : x = y
      · simp_all [PartialMap.update_shadow]; apply_rules using StlcSubTyping
      · simp_all; constructor; apply ih; rw [PartialMap.update_permute]; lia
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
      apply HasType.sub <;> solve_by_elim using StlcSubTyping
```

## Preservation

The proof of preservation now proceeds pretty much as in earlier
chapters, using the substitution lemma at the appropriate point
and the inversion lemma from above to extract structural
information from typing assumptions.

_Theorem_ (Preservation): If `t`, `t'` are terms and `τ` is a type
  such that `∅ ⊢ t ⦂ τ` and `t ⟶ t'`, then `∅ ⊢ t' ⦂ τ`.

_Proof_: Let `t` and `τ` be given such that `∅ ⊢ t ⦂ τ`.
We proceed by induction on the structure of this typing
derivation. The `abs`, `unit`, `tru`, and `fls` cases
are vacuous because abstractions and constants don't step.  Case
`var` is vacuous as well, since the context is empty.

  - If the final step of the derivation is by `app`, then there
    are terms `t₁` and `t₂` and types `τ₁` and `τ₂` such that `t = t₁ t₂`,
    `τ = τ₂`, `∅ ⊢ t₁ ⦂ τ₁ → τ₂`, and `∅ ⊢ t₂ ⦂ τ₁`.

    By the definition of the step relation, there are three ways
    `t₁ t₂` can step.  Cases `app₁'` and `app₂` follow
    immediately by the induction hypotheses for the typing
    subderivations and a use of `app`.

    Suppose instead `t₁ t₂` steps by `appAbs`.  Then `t₁ = λ x:σ . τ₁₂`
    for some type `σ` and term `τ₁₂`, and `t' = [x:=t₂] τ₁₂`.

    By lemma `abs_arrow`, we have `τ₁ <: σ` and `x:σ₁ ⊢ t₂ ⦂ τ₂`.  It then follows by the substitution lemma ({name}`substitution_preserves_typing`) that
    `∅ ⊢ [x:=t₂] τ₁₂ ⦂ τ₂` as desired.

  - If the final step of the derivation uses rule `if`, then
    there are terms `t₁`, `t₂`, and `t₃` such that `t = if t₁ then t₂ else t₃`,
    with `∅ ⊢ t₁ ⦂ Bool` and with `∅ ⊢ t₂ ⦂ τ` and `∅ ⊢ t₃ ⦂ τ`.  Moreover, by the induction
    hypothesis, if `t₁` steps to `t₁'` then `∅ ⊢ t₁' : Bool`.
    There are three cases to consider, depending on which rule was
    used to show `t ⟶ t'`.

      - If `t ⟶ t'` by rule `if`, then `t' = if t₁' then t₂ else t₃` with
       `t₁ ⟶ t₁'`.  By the induction hypothesis,
        `∅ ⊢ t₁' ⦂ Bool`, and so `∅ ⊢ t' ⦂ τ` by
        `if`.

      - If `t ⟶ t'` by rule `ifTrue` or `ifFalse`, then
        either `t' = t₂` or `t' = t₃`, and `∅ ⊢ t' ⦂ τ`
        follows by assumption.

  - If the final step of the derivation is by `sub`, then there
    is a type `σ` such that `σ <: τ` and `∅ ⊢ t ⦂ σ`.  The
    result is immediate by the induction hypothesis for the typing
    subderivation and an application of `sub`.

Qed.

```lean
theorem preservation {t t' : Tm} {τ : Ty}
  (ht : <{ ∅ ⊢ ~t ⦂ ~τ }>)
  (hs : t ⟶ t') :
  <{ ∅ ⊢ ~t' ⦂ ~τ }> := by

  generalize heq : (∅ : Context) = Γ at ht
  induction ht generalizing t' with (subst_vars; first
    -- discharge the goals where `t` doesn't step
    | inversion hs <;> constructor <;> simp_all; done
    | try (inversion hs; apply_rules using StlcSubTyping; done))
  | app Γ τ₁' τ₂' t₁' t₂ h₁ h₂ ih₁ ih₂ =>
    inversion hs with (try (constructor <;> apply_rules; done))
    | appAbs _ τ₂ t₁ h =>
        obtain ⟨h₁, h₂⟩ := abs_arrow h₁
        apply substitution_preserves_typing (τ₁:=τ₂)
        · assumption
        · apply HasType.sub <;> apply_rules using StlcSubTyping
  | ite Γ t₁ t₂ t₃ τ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    inversion hs with (try (constructor <;> solve_by_elim using StlcSubEval))
  | sub Γ t₁ τ₁ τ₂ ht hs ih =>
      apply HasType.sub <;> solve_by_elim using StlcSubTyping
-- SOLUTION
  | fst Γ t τ₁ τ₂ h ih  =>
      inversion hs with (try solve_by_elim using StlcSubTyping)
      | fstPair =>
          obtain ⟨σ₁, σ₂, hs', ht₁, ht₂⟩ := typing_inversion_pair h
          obtain ⟨σ₁, σ₂, heq, hs₁, hs₂⟩ := sub_inversion_prod hs'
          inversion heq; apply HasType.sub <;> assumption
  | snd Γ t τ₁ τ₂ h ih  =>
      inversion hs with (try solve_by_elim using StlcSubTyping)
      | sndPair =>
          obtain ⟨σ₁, σ₂, hs', ht₁, ht₂⟩ := typing_inversion_pair h
          obtain ⟨σ₁, σ₂, heq, hs₁, hs₂⟩ := sub_inversion_prod hs'
          inversion heq; apply HasType.sub <;> assumption
  | pair Γ t₁ t₂ τ₁ τ₂ h₁ h₂ ih₁ ih₂ =>
      inversion hs with solve_by_elim using StlcSubTyping
-- END SOLUTION
```


::::full
This formalization of the STLC with subtyping omits record
types for brevity.  If we want to deal with them more seriously,
we have two choices.

First, we can treat them as part of the core language, writing
down proper syntax, typing, and subtyping rules for them.

On the other hand, if we are treating them as a derived form that
is desugared in the parser, then we shouldn't need any new rules:
we should just check that the existing rules for subtyping product
and `Unit` types give rise to reasonable rules for record
subtyping via this encoding. To do this, we just need to make one
small change to the encoding described earlier: instead of using
`Unit` as the base case in the encoding of tuples and the "don't
care" placeholder in the encoding of records, we use `⊤`.  So:

```display
    {a:Nat, b:Nat} --⟶ {Nat,Nat}       i.e., (Nat,(Nat,⊤))
    {c:Nat, a:Nat} --⟶ {Nat,⊤,Nat}   i.e., (Nat,(⊤,(Nat,⊤)))
```

The encoding of record values doesn't change at all.  It is
easy (and instructive) to check that the subtyping rules above are
validated by the encoding.

:::dev PotentialImprovement
Perhaps it would be good to say something about subtyping
for other constructors, like lists, pairs, etc.  More ambitious
would be to say something about references, arrays, etc.
:::
::::

:::::full
::::exercise (rating := 2) (name := "variations") (manual := true)
Each part of this problem suggests a different way of changing the
definition of the STLC with Unit and subtyping.  (These changes
are not cumulative: each part starts from the original language.)
In each part, list which properties (Progress, Preservation, both,
or neither) become false.  If a property becomes false, give a
counterexample.

- Suppose we add the following typing rule:

```display
                           <{ Γ ⊢ t ⦂ σ₁→σ₂ }>
                    σ₁ <: τ₁     τ₁ <: σ₁      σ₂ <: τ₂
                    -----------------------------------     (funny₁)
                           <{ Γ ⊢ t ⦂ τ₁→τ₂ }>
```
:::solution
Answer: NONE
:::

- Suppose we add the following reduction rule:
```display
                             --------------------          (funny₂)
                             unit ⟶ (\x:⊤. x)
```
:::solution
Answer: Preservation fails.  For example, `unit`
has type `Unit` but steps to `(\x:⊤. x)`, which does not have
type `Unit`.
:::

- Suppose we add the following subtyping rule:

```display
                              ----------------            (funny₃)
                               Unit <: ⊤→⊤
```

:::solution
Answer: Progress fails.  For example,
`unit (\x:⊤,⊤)` is well typed but stuck.
:::

- Suppose we add the following subtyping rule:

```display
                               ----------------            (funny₄)
                               ⊤→⊤ <: Unit
```

:::solution
Answer: NONE
:::

- Suppose we add the following reduction rule:

```display
                             ---------------------        (funny₅)
                             (unit t) ⟶ (t unit)
```
:::solution
Answer: NONE
:::

- Suppose we add the same reduction rule _and_ a new typing rule:

```display
                             ---------------------        (funny₅)
                             (unit t) ⟶ (t unit)

                           ---------------------------     (funny₆)
                           ∅ ⊢ unit ⦂ ⊤→⊤
```

:::solution
Answer: Preservation fails. For example,
1unit (\x:A,x)1 has type `⊤`, but it steps to `(\x:A,x) unit`,
which is ill typed,
:::

- Suppose we _change_ the arrow subtyping rule to:
```display
                          σ₁ <: τ₁   σ₂ <: τ₂
                          -------------------              (arrow')
                          σ₁→σ₂ <: τ₁→τ₂
```

:::solution
Answer: Preservation fails.  For example,
`(\x:Unit*Unit, x.fst) unit`has type `Unit`, but steps to
`unit.fst` which is ill typed. (In order to type
`(\x:Unit*Unit, x.fst) unit` we use `sub` twice; once to give
`unit` the type `⊤`, and once to give `\x:Unit*Unit, x.fst`
the type `⊤ → Unit` using `S_Arrow'`).
:::


:::grade
`GRADE_MANUAL 2: variations`
:::
::::
:::::

### Exercise: Adding Products

:::suppressPreviousHeaderWhenTerse
:::

:::::full
::::exercise (rating := 5) (name := "products") (manual := true)
Adding pairs, projections, and product types to the system we have
defined is a relatively straightforward matter.  Carry out this
extension by modifying the definitions and proofs above:

- Constructors for pairs, first and second projections, and
product types have already been added to the definitions of
`Ty` and `Tm`.  Also, the definition of substitution has been
extended.

- Extend the surrounding definitions accordingly (refer to chapter {ref "MoreStlc"}[MoreStlc]):
- value relation
- operational semantics
- typing relation

- Extend the subtyping relation with this rule:
```display
                        σ₁ <: τ₁    σ₂ <: τ₂
                        --------------------   (prod)
                         σ₁ × σ₂ <: τ₁ × τ₂
```

- Extend the proofs of progress, preservation, and all their
  supporting lemmas to deal with the new constructs.  (You'll also
  need to add a couple of completely new lemmas.)

:::instructors
Summary of things to check:

- `step` should have six new rules related to products.

- `subtype` should have the one more rule given above.

- `has_type` should have three more rules for `pair`, `fst`, `snd`.

- `progress` should check. Also look for the
  `canonical_forms_of_product_types` (or whatever the student named it)
  in the proof.

- `preservation` should check. Also look for inversion lemmas for the
  new constructs.
:::


:::solution
The solution can be found in-line earlier in this chapter.
:::

:::grade
`GRADE_MANUAL 2: products_value_step`
:::
:::grade
`GRADE_MANUAL 2: products_subtype_has_type`
:::
:::grade
`GRADE_MANUAL 3: products_progress`
:::
:::grade
`GRADE_MANUAL 3: products_preservation`
:::
::::
:::::

:::dev PotentialImprovement
Another great hard exercise (probably just for the advanced
track) is to get them to figure out how to add sums and case.  Note
that this gets into thinking about joins, if you extend it to the
algorithmic version.
:::

## Formalized "Thought Exercises"

:::suppressPreviousHeaderWhenTerse
:::

:::::full

The following are formal exercises based on the previous "thought exercises."

```lean
namespace FormalThoughtExercises
open Examples
abbrev p := "p"
abbrev a := "a"

abbrev tf p := p ∨ ¬p
```

::::exercise (rating := 1) (name := "formal_subtype_instances_tf_1a") (optional := true)
```lean
theorem formal_subtype_instances_tf_1a:
  tf (∀ σ τ υ δ, σ <: τ → υ <: δ → <{ ~τ → ~σ }> <: <{ ~τ → ~σ }>) := by
  solution!
    left; intro σ τ υ δ h₁ h₂; solve_by_elim using StlcSubTyping
```
::::


::::exercise (rating := 1) (name := "formal_subtype_instances_tf_1b") (optional := true)
```lean
theorem formal_subtype_instances_tf_1b:
  tf (∀ σ τ υ δ, σ <: τ → υ <: δ → <{ ⊤ → ~υ }> <: <{ ~σ → ⊤ }>) := by
  solution!
    left; intro σ τ υ δ h₁ h₂; solve_by_elim using StlcSubTyping
```
::::


::::exercise (rating := 1) (name := "formal_subtype_instances_tf_1c") (optional := true)
```lean
theorem formal_subtype_instances_tf_1c:
  tf (∀ σ τ υ δ, σ <: τ → υ <: δ →
         <{ (~C → ~C)→(~A × ~B) }> <: <{ (~C → ~C)→(⊤ × ~B) }>) := by
  solution!
    left; intro σ τ υ δ h₁ h₂; solve_by_elim using StlcSubTyping
```
::::
:::::

:::::full
::::exercise (rating := 1) (name := "formal_subtype_instances_tf_1d") (optional := true)
```lean
theorem formal_subtype_instances_tf_1d:
  tf (∀ σ τ υ δ, σ <: τ → υ <: δ → <{ ~τ → (~τ → ~υ) }> <: <{ ~σ → (~σ → ~δ) }>) := by
  solution!
    left; intro σ τ υ δ h₁ h₂; solve_by_elim using StlcSubTyping
```
::::

::::exercise (rating := 1) (name := "formal_subtype_instances_tf_1e") (optional := true)
```lean
theorem formal_subtype_instances_tf_1e:
  tf (∀ σ τ υ δ, σ <: τ → υ <: δ → <{ (~τ → ~τ) → ~υ }> <: <{ (~σ → ~σ)→ ~δ }>) := by
  solution!
    right; intro contra
    have h : <{ (⊤ → ⊤) → Bool }> <: <{ (Bool → Bool) → ⊤ }> := by
      solve_by_elim using StlcSubTyping
    obtain ⟨_, _, h₁, h₂, _⟩ := sub_inversion_arrow h
    inversion h₁
    obtain ⟨_, _, h₁, h₂, _⟩ := sub_inversion_arrow h₂
    inversion h₁
    apply sub_inversion_bool at h₂; contradiction
```
::::


::::exercise (rating := 1) (name := "formal_subtype_instances_tf_1f") (optional := true)
```lean
theorem formal_subtype_instances_tf_1f:
  tf (∀ σ τ υ δ, σ <: τ → υ <: δ → <{ ((~τ → ~σ) → ~τ)→ ~υ }> <: <{ ((~σ → ~τ)→ ~σ) → ~δ }>) := by
  solution!
    left; intro σ τ υ δ h₁ h₂; solve_by_elim (maxDepth:=10) using StlcSubTyping
```
::::
:::::

:::::full
::::exercise (rating := 1) (name := "formal_subtype_instances_tf_1g") (optional := true)
```lean
theorem formal_subtype_instances_tf_1g:
  tf (∀ σ τ υ δ, σ <: τ → υ <: δ → <{ ~σ × ~δ }> <: <{ ~τ × ~υ }>) := by

  solution!
    right; intro contra
    have h : <{ Bool × ⊤ }> <: <{ ⊤ × Bool }> := by solve_by_elim using StlcSubTyping
    obtain ⟨_, _, h₁, _, h₃⟩ := sub_inversion_prod h
    inversion h₁; apply sub_inversion_bool at h₃; contradiction
```
::::



::::exercise (rating := 2) (name := "formal_subtype_instances_tf_2a") (optional := true)
```lean
theorem formal_subtype_instances_tf_2a:
  tf (∀ σ τ, σ <: τ →  <{ ~σ → ~σ }> <: <{ ~τ → ~τ }>) := by

  solution!
    right; intro contra
    have h : <{ Bool→Bool }> <: <{ ⊤→⊤ }> := by solve_by_elim using StlcSubTyping
    obtain ⟨_, _, h₁, h₂, h₃⟩ := sub_inversion_arrow h
    inversion h₁; apply sub_inversion_bool at h₂; contradiction
```
::::

::::exercise (rating := 2) (name := "formal_subtype_instances_tf_2b") (optional := true)
```lean
theorem formal_subtype_instances_tf_2b:
  tf (∀ σ, σ <: <{ ~A → ~A }> → ∃ τ, σ = <{ ~τ → ~τ }> ∧ τ <: A) := by

  solution!
    right; intros contra
    obtain ⟨τ, h₁, h₂⟩ := contra <{ ⊤→ ~A }> (by solve_by_elim using StlcSubTyping)
    inversion h₁
```
::::
:::::

:::::full
::::exercise (rating := 2) (name := "formal_subtype_instances_tf_2d") (optional := true)
Hint: Assert a generalization of the statement to be proved and
use induction on a type (rather than on a subtyping derviation).

```lean
theorem formal_subtype_instances_tf_2d: tf (∃ σ, σ <: <{ ~σ → ~σ }>) := by

  solution!
    have h : ∀ σ τ, ¬ σ <: <{ ~τ → ~σ }> := by
      intro σ τ contra
      induction σ generalizing τ with (
          obtain ⟨σ₁, σ₁, h₁, h₂, h₃⟩ := sub_inversion_arrow contra; try contradiction)
      | arrow τ₁ τ₂ ih₁ ih₂ =>
        inversion h₁; apply ih₂; apply h₃
    right; intro contra
    obtain ⟨σ, contra⟩ := contra
    apply h at contra; assumption
```
::::
:::::

:::::full
::::exercise (rating := 2) (name := "formal_subtype_instances_tf_2e") (optional := true)
```lean
theorem formal_subtype_instances_tf_2e: tf (∃ σ, <{ ~σ → ~σ }> <: σ) := by
  solution!
    left; exists Ty.top; solve_by_elim using StlcSubTyping
```
::::


::::exercise (rating := 2) (name := "formal_subtype_concepts_tfa") (optional := true)
```lean
theorem formal_subtype_concepts_tfa: tf (∃ τ, ∀ σ, σ <: τ) := by
  solution!
    left; exists Ty.top; solve_by_elim using StlcSubTyping
```
::::

::::exercise (rating := 2) (name := "formal_subtype_concepts_tfb") (optional := true)
```lean
theorem formal_subtype_concepts_tfb: tf (∃ τ, ∀ σ, τ <: σ) := by
  solution!
    right; intro contra
    obtain ⟨σ, contra⟩ := contra
    have h : σ = Ty.bool := by
      apply sub_inversion_bool; apply contra
    have h₂ : σ = Ty.unit := by
      apply sub_inversion_unit; apply contra
    subst_vars; contradiction
```
::::
:::::

:::::full
::::exercise (rating := 2) (name := "formal_subtype_concepts_tfc") (optional := true)
```lean
theorem formal_subtype_concepts_tfc:
  tf (∃ τ₁ τ₂, ∀ σ₁ σ₂, <{ ~σ₁ ×  ~σ₂ }> <: <{ ~τ₁ × ~τ₂ }>) := by
  solution!
    left; exists Ty.top, Ty.top; solve_by_elim using StlcSubTyping
```
::::

::::exercise (rating := 2) (name := "formal_subtype_concepts_tfd") (optional := true)
```lean
theorem formal_subtype_concepts_tfd:
  tf (∃ τ₁ τ₂, ∀ σ₁ σ₂, <{ ~τ₁ × ~τ₂ }> <: <{ ~σ₁ × ~σ₂ }>) := by
  solution!
    right; intro contra
    obtain ⟨τ₁, τ₂, h⟩ := contra
    obtain ⟨_, _, h₁, h₂, _⟩ := sub_inversion_prod (h <{ Bool }> <{ Bool }>)
    inversion h₁
    obtain ⟨_, _, h₃, h₄, _⟩ := sub_inversion_prod (h <{ Unit }> <{ Unit }>)
    inversion h₃
    apply sub_inversion_bool at h₂; apply sub_inversion_unit at h₄
    subst_vars; contradiction
```
::::

::::exercise (rating := 2) (name := "formal_subtype_concepts_tfe") (optional := true)
```lean
theorem formal_subtype_concepts_tfe:
  tf (∃ τ₁ τ₂, ∀ σ₁ σ₂, <{ ~σ₁ → ~σ₂ }> <: <{ ~τ₁→ ~τ₂ }>) := by

  solution!
    right; intro contra
    obtain ⟨τ₁, τ₂, h⟩ := contra
    obtain ⟨_, _, h₁, h₂, _⟩ := sub_inversion_arrow (h <{ Bool }> <{ Bool }>)
    inversion h₁
    obtain ⟨_, _, h₃, h₄, _⟩ := sub_inversion_arrow (h <{ Unit }> <{ Unit }>)
    inversion h₃
    apply sub_inversion_bool at h₂; apply sub_inversion_unit at h₄
    subst_vars; contradiction
```
::::
:::::

:::::full
::::exercise (rating := 2) (name := "formal_subtype_concepts_tff") (optional := true)
```lean
theorem formal_subtype_concepts_tff :
  tf (∃ τ₁ τ₂, ∀ σ₁ σ₂, <{ ~τ₁ → ~τ₂ }> <: <{ ~σ₁ → ~σ₂ }>) := by

  solution!
    right; intro contra
    obtain ⟨τ₁, τ₂, h⟩ := contra
    obtain ⟨_, _, h₁, h₂, h₃⟩ := sub_inversion_arrow (h <{ Bool }> <{ Bool }>)
    inversion h₁
    obtain ⟨_, _, h₄, h₅, h₆⟩ := sub_inversion_arrow (h <{ Unit }> <{ Unit }>)
    inversion h₄
    apply sub_inversion_bool at h₃; apply sub_inversion_unit at h₆
    subst_vars; contradiction
```
::::

::::exercise (rating := 2) (name := "formal_subtype_concepts_tfg") (optional := true)
:::solution
```lean
def inf_desc_chain (n: Nat) : Ty :=
  match n with
    | 0 => <{ ⊤ }>
    | n + 1 => <{ ⊤ → ~(inf_desc_chain n) }>
```
:::

```lean
theorem formal_subtype_concepts_tfg:
  tf (∃ f : Nat → Ty,
         (∀ i j, i ≠ j → f i ≠ f j) ∧
         (∀ i, f (i + 1) <: f i)) := by
  solution!
    left; exists inf_desc_chain; constructor
    · intro i j h; induction i generalizing j with (intro contra)
      | zero =>
          cases j; contradiction
          simp only [inf_desc_chain] at contra; contradiction
      | succ i' ih =>
          cases j with
          | zero => contradiction
          | succ j' =>
              have h' : i' ≠ j' := by lia
              apply ih at h'
              simp only [inf_desc_chain] at contra
              inversion contra; lia
    · intro i; induction i with solve_by_elim using StlcSubTyping
```
::::
:::::

:::::full
::::exercise (rating := 2) (name := "formal_subtype_concepts_tfh") (optional := true)
```lean
theorem formal_subtype_concepts_tfh:
  tf (∃ f : Nat → Ty, (∀ i j, i ≠ j → f i ≠ f j) ∧ (∀ i, f i <: f (i + 1))) := by
  solution!
    left; exists (fun n => <{ ~(inf_desc_chain n) → ⊤ }>); constructor
    · intro i j h; induction i generalizing j with (intro contra)
      | zero =>
          cases j; contradiction
          simp only [inf_desc_chain] at contra; inversion contra
      | succ i' ih =>
          cases j with
          | zero => simp only [inf_desc_chain] at contra; inversion contra
          | succ j' =>
              have h' : i' ≠ j' := by lia
              apply ih at h'
              simp only [inf_desc_chain] at contra
              inversion contra; lia
    · intro i; induction i with
      | zero => solve_by_elim using StlcSubTyping
      | succ i' ih =>
        obtain ⟨_, _, h₁, h₂, h₃⟩ := sub_inversion_arrow ih
        inversion h₁; solve_by_elim using StlcSubTyping
```
::::

::::exercise (rating := 3) (name := "formal_proper_subtypes") (optional := true)
```lean
theorem formal_proper_subtypes:
  tf (∀ τ,
         ¬(τ = Ty.bool ∨ (∃ n, τ = Ty.base n) ∨ τ = Ty.unit) →
         ∃ σ, σ <: τ ∧ σ ≠ τ) := by
  solution!
    right; intro contra
    have h : ∃ σ : Ty, σ <: <{ ⊤ → Bool }> ∧ σ ≠ <{ ⊤ → Bool }> := by
      apply contra; intro contra
      obtain h | ⟨_, h⟩ | h := contra <;> contradiction
    obtain ⟨σ, h₁, h₂⟩ := h
    obtain ⟨_, _, h₁, h₂, h₃⟩ := sub_inversion_arrow h₁
    apply sub_inversion_bool at h₃
    apply sub_inversion_top at h₂
    subst_vars; apply h₂; rfl
```
::::
:::::

:::::full
```lean
end FormalThoughtExercises
```
:::::

```lean
end StlcSub
```
