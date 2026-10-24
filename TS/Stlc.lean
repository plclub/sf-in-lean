import SFLMeta
import TS.StlcCommon
import TS.Smallstep

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Stlc: The Simply Typed Lambda-Calculus" =>
%%%
tag := "Stlc"
htmlSplit := .never
file := some "Stlc"
%%%

:::instructors
This chapter needs about one (80-minute) lecture.  It
makes up maybe half of a good weekly homework assignment.
:::


:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement
Anthony's comments later in the course:

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
:::

:::dev PotentialImprovement
There are a bunch of slides from earlier offerings of
CIS500 that might be useful additions to the TERSE notes.
  https://www.seas.upenn.edu/~cis500/cis500-f06/lectures/1002.pdf
  https://www.seas.upenn.edu/~cis500/cis500-f06/lectures/1004.pdf
:::

::::full
The simply typed lambda-calculus (STLC) is a tiny core
calculus embodying the key concept of _functional abstraction_.
This concept shows up in pretty much every real-world programming
language in some form (functions, procedures, methods, etc.).

We will follow exactly the same pattern as in the {ref "Smallstep"}[previous chapter]
when formalizing this calculus (syntax, small-step semantics,
typing rules) and its main properties (progress and preservation).
The new technical challenges arise from the mechanisms of
{deftech}_variable binding_ and {deftech}_substitution_.  It will take some work to
deal with these.
::::

::::terse
Our job for this chapter: Formalize a small _functional_
language and its type system.

Language: The _simply typed lambda-calculus_ (STLC).
   - A small subset of Lean's built-in functional language...
   - ...but we'll use different concrete syntax (to avoid
     confusion, and for consistency with standard treatments)

Main new technical challenges:
  - variable binding
  - substitution
::::

:::slidebreak
:::

The STLC lives in the lower-left front corner of the famous
{deftech}_lambda cube_ (also called the {deftech}_Barendregt Cube_), which
visualizes three sets of features that can be added to its
simple core:

:::diagramWithAlt
```diagram (cssWidth := "28em") (texWidth := "20em")
SFLMeta.Diagrams.lambdaCubeDiagram
```

```
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
```
:::

Moving from bottom to top in the cube corresponds to adding
{deftech}_polymorphic types_ like {lean}`∀ α : Type, α → α`.  Adding _just_
polymorphism gives us the famous Girard-Reynolds calculus, System F.

Moving from front to back corresponds to adding _type operators_
like {name}`List`.

Moving from left to right corresponds to adding _dependent types_
like {lean}`∀ n m : Nat, n = m`.

The top right corner on the back, which combines all three features,
is called the {deftech}_Calculus of Constructions_.  First studied by
Coquand and Huet, it forms the foundation of Lean's logic.

# Overview

::::full
The STLC is built on some collection of _base types_:
booleans, numbers, strings, etc.  The exact choice of base types
doesn't matter much — the definition of the language as well as
its theoretical properties work out the same no matter what we
choose — so for the sake of brevity let's take just `Bool` for
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
constructors (written out first in informal BNF notation — we'll
formalize it below) for STLC terms `t`.
::::

::::terse
Begin with some set of _base types_ (here, just `Bool`)

Add: variables, function abstractions, and applications

Informal grammar for terms (where `x` and `t` stand for arbitrary variables
and terms):
::::

```bnf
t ::= x ("variable")
    | "λ" x ":" T "." t ("abstraction")
    | t t ("application")
    | "true" ("constant true")
    | "false" ("constant false")
    | "if" t "then" t "else" t ("conditional") ;
```

::::full
The Greek letter λ ("lambda") in a function abstraction `λx:T. t` is what gives
the calculus its name.  The variable `x` is called the _parameter_ to the
function; the term `t` is its _body_.  The annotation `:T`
specifies the _type_ of arguments that the function can be applied to.

The types of the STLC include `Bool`, which classifies the
boolean constants `true` and `false` as well as more complex
computations that yield booleans, plus _arrow types_ that classify
functions (as is the case in Lean).
::::

::::terse
The _types_ of the STLC include the base type `Bool` for
boolean values and arrow types for functions.
::::

```bnf
T ::= "Bool"
    | T "→" T ;
```

:::slidebreak
:::

Some examples of STLC terms:

: `λx:Bool. x`

  The identity function for booleans.

: `(λx:Bool. x) true`

  The identity function for booleans, applied to the boolean `true`.

: `λx:Bool. if x then false else true`

  The boolean "not" function.

: `λx:Bool. true`

  The constant function that takes every (boolean) argument to
  `true`.

:::slidebreak
:::

: `λx:Bool. λy:Bool. x`

  A two-argument function that takes two booleans and returns
  the first one.

  ::::full
  (As in Lean, a two-argument function in the
  lambda-calculus is really a one-argument function whose body
  is also a one-argument function.)
  ::::

: `(λx:Bool. λy:Bool. x) false true`

  A two-argument function that takes two booleans and returns
  the first one, applied to the booleans `false` and `true`.

  ::::full
  (As in Lean, application associates to the left — i.e., this
  expression is parsed as `((λx:Bool. λy:Bool. x) false) true`.)
  ::::

: `λf:Bool → Bool. f (f true)`

  A higher-order function that takes a _function_ `f` (from
  booleans to booleans) as an argument, applies `f` to `true`,
  and applies `f` again to the result.

: `(λf:Bool → Bool. f (f true)) (λx:Bool. false)`

  The same higher-order function, applied to the constantly
  `false` function.

:::slidebreak
:::

::::full
The last two examples show, the STLC is a language of
{deftech}_higher-order_ functions: we can write down functions that take
other functions as arguments and/or return other functions as results.

The STLC doesn't provide any primitive syntax for defining _named_
functions: i.e., all functions are "anonymous."  We'll see in chapter
`MoreStlc` that it is easy to add named functions — indeed, the
fundamental naming and binding mechanisms are exactly the same.
::::

Now reconsider our examples, each along with its type:

- `λx:Bool. x` has type `Bool → Bool`

- `(λx:Bool. x) true` has type `Bool`

- `λx:Bool. if x then false else true` has type `Bool → Bool`

- `λx:Bool. true` has type `Bool → Bool`

- `λx:Bool. λy:Bool. x` has type `Bool → Bool → Bool`
                        (i.e., `Bool → (Bool → Bool)`)

- `(λx:Bool. λy:Bool. x) false true` has type `Bool`

The last two, higher-order examples are left off the list on purpose — working out
their types is the subject of the quizzes that follow.

::::terse
Note that _all_ functions are anonymous.

We'll see how to add named function declarations as "syntactic
sugar" in the `MoreStlc` chapter.
::::

:::slidebreak
:::

::::quiz
What is the type of the following term?

```display
λf:Bool → Bool. f (f true)
```

(A) `Bool → (Bool → Bool)`

(B) `(Bool → Bool) → Bool`

(C) `Bool → Bool`

(D) `Bool`

(E) none of the above
::::

::::quiz
How about the type of this one?

```display
(λf:Bool → Bool. f (f true)) (λx:Bool. false)
```

(A) `Bool → (Bool → Bool)`

(B) `(Bool → Bool) → Bool`

(C) `Bool → Bool`

(D) `Bool`

(E) none of the above
::::

# Syntax

We next formalize the syntax of the STLC.

```lean
namespace Stlc

open scoped MyGetElem
```

## Types

```lean
inductive Ty where
  | bool
  | arrow (τ₁ τ₂ : Ty)
```

## Terms

```lean
inductive Tm where
  | var (x : String)
  | app (t₁ t₂ : Tm)
  | abs (x : String) (τ : Ty) (t : Tm)
  | tru
  | fls
  | ite (c t e : Tm)
```

:::slidebreak
:::

The constructors above give us a precise representation of STLC syntax, but
expressions written directly with them quickly become hard to read.
We need some notation magic to set up the concrete syntax, as
we did in the {ref "Types"}[Types] chapter...

We will write STLC syntax inside `<{ ... }>` brackets. For example,
`<{ λ X : Bool . X }>` represents the term
{lean}`Tm.abs "X" Ty.bool (Tm.var "X")`.

::::full
This notation must also support definitions and proofs about *arbitrary* piece of STLC
syntax. For example, a theorem may introduce Lean variables `t : Tm` and
`τ : Ty`, representing an arbitrary STLC term and type. Inside the brackets,
we can then write `<{ λ X : τ . t }>`.
Here `X` is the name of a variable in the
STLC term being represented, while `τ` and `t` refer to the Lean variables in
the surrounding theorem.

The notation distinguishes these two uses by naming convention, which we will follow
throughout the STLC chapters:

- A name beginning with a capital Latin letter is taken literally as a name in
  the STLC syntax. Thus `X`, `Y`, and `Z` are STLC term variables. Such a
  name must be a single Lean identifier and cannot contain a dot. In languages
  with named base types, which we will see in the {ref "Sub"}[Sub] chapter,
  names such as `A`, `Int`, and `Bool` name those types.
- A name beginning with a lowercase letter or a Greek letter refers to a Lean
  variable in the surrounding definition or proof. This lets us use the usual
  names `x` and `y` for strings, `t` and `u` for terms, `τ` for types, and `Γ`
  for contexts without additional punctuation.
- To insert a larger Lean expression, prefix it with `~`. For example,
  `<{ ~(Tm.var "X") t }>` inserts the expression {lean}`Tm.var "X"` as the function
  and the Lean variable `t` as its argument. The same escape is needed to
  insert a capitalized Lean variable, since an unescaped capitalized name is
  assumed to be an STLC name.

This capitalization convention applies to actual variable names in concrete
STLC examples and inside `<{ ... }>` brackets. In grammars, inference rules,
and general explanations, symbols such as `x`, `t`, and `T` instead stand for
an arbitrary variable name, term, or type. We keep the conventional lowercase
notation for these schematic symbols.

::::

::::terse
We write STLC syntax inside `<{ ... }>` brackets. Capital Latin names are
literal STLC names. Lowercase and Greek names refer to Lean variables in the
surrounding proof. Larger Lean expressions are inserted with `~`.
::::

::::details "Notation encoding"
```lean
syntax:50 "if " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

namespace Elab

open StlcCommon
open Lean Meta Elab Term

def language : Language where
  tyType := ``Ty
  tmType := ``Tm
  arrowCtor := ``Ty.arrow
  varCtor := ``Tm.var
  appCtor := ``Tm.app
  absCtor := ``Tm.abs

  -- defined later
  subst := `Stlc.subst
  hasType := `Stlc.HasType

def boolTyHandler : TyElabHandler :=
  fun _recur k T => do
    match T with
    | `(stlcTy| Bool) =>
        return mkConst ``Ty.bool
    | _ => k T

def tyHandlers : TyElabHandler :=
  boolTyHandler.orElse (commonTyHandler language)

partial def elabTy : TyElab :=
  tyHandlers elabTy <| unsupportedTy language

def boolTmHandler : TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    | `(stlcTm| true) => do
        return (mkConst ``Tm.tru, free)
    | `(stlcTm| false) => do
        return (mkConst ``Tm.fls, free)
    | `(stlcTm| Bool) => do
        throwError "`Bool` is not a valid term."
    | `(stlcTm| if $c:stlcTm then $t:stlcTm else $e:stlcTm) => do
        let (c, free) ← recur Γ free c
        let (t, free) ← recur Γ free t
        let (e, free) ← recur Γ free e
        return (mkApp3 (mkConst ``Tm.ite) c t e, free)
    | _ => k Γ free t

def tmHandlers : TmElabHandler :=
  boolTmHandler.orElse (commonTmHandler language elabTy)

partial def elabTm : TmElab :=
  tmHandlers elabTm unsupportedTm

def elabCtx : CtxElab := elabCtxCommon language elabTy

@[scoped term_elab StlcCommon.bracket]
def elabBracket : TermElab :=
  fun stx expectedType? => do
    let `(<{ $q:stlcQuoted }>) := stx
      | throwUnsupportedSyntax
    elabQuoted language elabTy elabTm elabCtx q expectedType?

end Elab

open scoped Elab

namespace Delab

open StlcCommon Delab
open Lean PrettyPrinter Delaborator

@[app_unexpander Ty.bool]
private def Ty.unexpandBool : Unexpander
  | _ => do
    let T ← `(stlcTy| $(mkIdent `Bool):ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.arrow]
private def Ty.unexpandArrow : Unexpander := Delab.unexpandArrow

@[app_unexpander Tm.tru]
private def Tm.unexpandTru : Unexpander
  | _ => do
    let t ← `(stlcTm| $(mkIdent `true):ident)
    `(<{ $t:stlcTm }>)

@[app_unexpander Tm.fls]
private def Tm.unexpandFls : Unexpander
  | _ => do
    let t ← `(stlcTm| $(mkIdent `false):ident)
    `(<{ $t:stlcTm }>)

private def reservedNames : String → Bool
  | "true" | "false" | "Bool" => true
  | _ => false

@[app_unexpander Tm.var]
private def Tm.unexpandVar : Unexpander := Delab.unexpandVar reservedNames ``Tm.var

@[app_delab Tm.var]
private def Tm.delabVar : Delab := Delab.delabVar ``Tm.var

@[app_unexpander Tm.app]
private def Tm.unexpandApp : Unexpander := Delab.unexpandApp

@[app_unexpander Tm.abs]
private def Tm.unexpandAbs : Unexpander := Delab.unexpandAbs

@[app_unexpander Tm.ite]
private def Tm.unexpandIte : Unexpander
  | `($_ $c $t $e) =>
      `(<{ if $(getTm c) then $(getTm t) else $(getTm e) }>)
  | _ => throw ()

end Delab
```
::::

:::ignore
```lean -show
/-- info: <{ λ X : Bool . λ X : Bool . X }> : Tm -/
#guard_msgs in
#check <{ λ X : Bool . λ X : Bool . X }>


/--
info: Try this:
  [apply] ~"x"
---
error: unknown metalanguage name identifier `x`
-/
#guard_msgs in
#check <{ λ x : Bool . x }>


/-- info: <{ Bool → Bool }> : Ty -/
#guard_msgs in
#check <{ Bool → Bool }>

/-- info: <{ Bool → Bool → Bool }> : Ty -/
#guard_msgs in
#check <{ Bool → Bool → Bool }>

/-- info: <{ X }> : Tm -/
#guard_msgs in
#check (<{ X }> : Tm)

example (x : Tm) : (<{ x }> : Tm) = x := rfl

/--
warning: Variable name `x` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _x

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
example (x : String) : (<{ X }> : Tm) = Tm.var "X" := rfl

example : (<{ X }> : Stlc.Tm) = Tm.var "X" := rfl

example (x : Tm) : (<{ x }> : Tm) = x := rfl

example (X : Tm) : (<{ ~X }> : Tm) = X := rfl

example (x : String) (τ : Ty) :
    <{ λ x : τ . ~(Tm.var x) }> =
      Tm.abs x τ (Tm.var x) := rfl

example (τ : Ty) :
    (<{ λ X : τ . X }>) =
      Tm.abs "X" τ (Tm.var "X") := rfl

/-- info: <{ X Y }> : Tm -/
#guard_msgs in
#check <{ X Y }>

/-- info: <{ X Y (X Y) }> : Tm -/
#guard_msgs in
#check <{ (X Y) (X Y) }>

/-- info: <{ X (Y X) Y X Y }> : Tm -/
#guard_msgs in
#check <{ X (Y X) Y X Y }>

/-- info: <{ λ X : Bool . X }> : Tm -/
#guard_msgs in
#check <{ λ X : Bool . X }>

/-- info: <{ (λ X : Bool . X) Y }> : Tm -/
#guard_msgs in
#check <{ (λ X : Bool . X) Y }>

/-- info: <{ if X then X else X }> : Tm -/
#guard_msgs in
#check <{ if X then X else X }>

/-- info: <{ if X Y then X else X }> : Tm -/
#guard_msgs in
#check <{ if X Y then X else X }>

/-- info: <{ if X Y then X else X }> : Tm -/
#guard_msgs in
#check <{ if (X Y) then X else X }>

/-- info: <{ if X then if X then Y else X else Y Z }> : Tm -/
#guard_msgs in
#check <{ if X then if X then Y else X else Y Z }>

/-- info: <{ (if X then if X then Y else X else Y) Z }> : Tm -/
#guard_msgs in
#check <{ (if X then if X then Y else X else Y) Z }>

/-- info: <{ λ ~"z" : Bool . Z Z }> : Tm -/
#guard_msgs in
#check <{ λ ~"z" : Bool . Z Z }>

/--
info: Try this:
  [apply] ~(Stlc.Tm.var z)
---
error: metalanguage term identifier `z` has type
    String
  but this position expects
    Tm
---
info: fun x z => sorry : (x : Ty) → (z : String) → ?m.2 x z
-/
#guard_msgs in
#check fun (x : Ty) (z : String) => <{ λ z : x . z z }>

/-- info: Stlc.Tm.var "z" : Tm -/
#guard_msgs in
#check <{~(Tm.var "z")}>

/-- info: Tm.abs "Z" Ty.bool (((Tm.var "ZZ").app (Tm.var "ZZ")).app (Tm.var "Z")) -/
#guard_msgs in
set_option pp.notation false in
#reduce let p := Tm.var "ZZ"; <{ λ Z : Bool . p p Z }>

example : (<{ Bool → Bool → Bool }> : Ty) =
    Ty.arrow Ty.bool (Ty.arrow Ty.bool Ty.bool) := rfl

example : (<{ (Bool → Bool) → Bool }> : Ty) =
    Ty.arrow (Ty.arrow Ty.bool Ty.bool) Ty.bool := rfl

example : (<{ X Y Z }> : Tm) =
    Tm.app (Tm.app (Tm.var "X") (Tm.var "Y")) (Tm.var "Z") := rfl

example : (<{ (if X then Y else Z) X }> : Tm) =
    Tm.app (Tm.ite (Tm.var "X") (Tm.var "Y") (Tm.var "Z")) (Tm.var "X") := rfl

example : (<{ true }> : Tm) = Tm.tru := rfl

example : (<{ false }> : Tm) = Tm.fls := rfl

example : (<{ if X then Y else Z }> : Tm) =
    Tm.ite (Tm.var "X") (Tm.var "Y") (Tm.var "Z") := rfl

example (t : Tm) : (<{ t }> : Tm) = t := rfl

example (τ : Ty) : (<{ τ }> : Ty) = τ := rfl

example (binder : String) : (<{ λ binder : Bool . ~(Tm.var "binder") }> : Tm) =
    Tm.abs binder Ty.bool (Tm.var "binder") := rfl

/--
warning: Variable name `X` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _X

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Variable name `term` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _term

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
example (X : String) (term : Tm) : (<{ λ X : Bool . true }> : Tm) =
    Tm.abs "X" .bool Tm.tru := rfl

example (t u : Tm) : (<{ ~(Tm.app t u) }> : Tm) = Tm.app t u := rfl

/-- error: `Bool` is not a valid term. -/
#guard_msgs in
#check (<{ Bool }> : Tm)

/-- info: (Ty.bool.arrow Ty.bool).arrow Ty.bool : Ty -/
#guard_msgs in
set_option pp.notation false in
#check <{ (Bool → Bool) → Bool }>

/-- info: Stlc.Tm.var "true" : Tm -/
#guard_msgs in
#check Tm.var "true"

/-- info: Stlc.Tm.var "false" : Tm -/
#guard_msgs in
#check Tm.var "false"

/-- info: Stlc.Tm.var "Bool" : Tm -/
#guard_msgs in
#check Tm.var "Bool"

/-- info: Stlc.Tm.var "x" : Tm -/
#guard_msgs in
#check Tm.var "x"

/-- info: <{ X }> : Tm -/
#guard_msgs in
#check Tm.var "X"

/-- info: Stlc.Tm.var "if" : Tm -/
#guard_msgs in
#check Tm.var "if"

/-- info: Stlc.Tm.var "succ" : Tm -/
#guard_msgs in
#check Tm.var "succ"

/-- info: Stlc.Tm.var "x-y" : Tm -/
#guard_msgs in
#check Tm.var "x-y"

/-- info: Stlc.Tm.var "1x" : Tm -/
#guard_msgs in
#check Tm.var "1x"

/-- info: Stlc.Tm.var "_" : Tm -/
#guard_msgs in
#check Tm.var "_"

/-- info: <{ X Y Z (λ X : Bool . X Y (λ X : Bool . X)) }> : Tm -/
#guard_msgs in
#check (<{ X Y Z (λ X : Bool . X Y (λ X : Bool . X))}>)

/--
error: ambiguous STLC quotation

This syntax has multiple valid interpretations:
  context, term, type

Add a Lean type annotation to select the intended interpretation.
---
info: fun x => sorry : (x : ?m.1) → ?m.3 x
-/
#guard_msgs in
#check fun x => <{ x }>

/--
error: this STLC quotation has no valid interpretation

Tried: context, term, type

Add a Lean type annotation to select an interpretation and obtain a more specific error.
---
info: fun x => sorry : (x : String) → ?m.2 x
-/
#guard_msgs in
#check fun (x : String) => <{ x }>

/-- info: fun x => x : Tm → Tm -/
#guard_msgs in
#check fun (x : Tm) => <{ x }>
```
:::

:::slidebreak
:::

Here are the terms we will use as running examples, written in the new
notation:

```lean
abbrev idB := <{ λ X : Bool . X }>

abbrev idBB := <{ λ X : Bool → Bool . X }>

abbrev idBBBB := <{ λ X : (Bool → Bool) → (Bool → Bool) . X }>

abbrev k := <{ λ X : Bool . λ Y : Bool . X }>
```

:::slidebreak
:::

```lean
abbrev notB := <{ λ X : Bool . if X then false else true }>
```

Note that an abstraction `λ x : T . t` (formally, {name}`Tm.abs` applied to
`x`, `T`, and `t`) is
always annotated with the type `T` of its parameter, in contrast
to Lean (and other functional languages like ML, Haskell, etc.),
which use type inference to fill in missing annotations.  We're
not considering type inference at all here.

# Operational Semantics

::::full
To define the small-step semantics of STLC terms, we begin,
as always, by defining the set of values.  Next, we define the
critical notions of {deftech}_free variables_ and {tech}_substitution_, which are
used in the reduction rule for application expressions.  And
finally we give the small-step relation itself.
::::

::::terse
To define the small-step semantics of STLC terms...

- We begin by defining the set of values.

- Next, we define _free variables_ and _substitution_.  These are
  used in the reduction rule for application expressions.

- Finally, we give the small-step relation itself.
::::

## Values

To define the values of the STLC, we have a few cases to consider.

First, for the boolean part of the language, the situation is
clear: `true` and `false` are the only values.  An `if` expression
is never a value.

:::slidebreak
:::

Second, an application is not a value: it represents a function
being invoked on some argument, which clearly still has work left
to do.

:::slidebreak
:::

Third, for abstractions, we have a choice:

- We can say that `λx:T. t` is a value only when `t` is a
  value — i.e., only if the function's body has been
  reduced (as much as it can be without knowing what argument it
  is going to be applied to).

- Or we can say that `λx:T. t` is always a value, no matter
  whether `t` is one or not — in other words, we can say that
  reduction stops at abstractions.

Our usual way of evaluating expressions in Lean makes the first
choice — for example,

```lean
#reduce fun _x : Bool => 3 + 4
```

yields:

```display
fun _x => 7
```

But Lean is rather unusual in this respect.  Most functional
programming languages make the second choice — reduction of a
function's body only begins when the function is actually applied
to an argument.

We also make the second choice here.

:::slidebreak
:::

```lean
inductive Tm.IsValue : Tm → Prop where
  | abs (x : String) (τ₂ : Ty) (t₁ : Tm) : IsValue <{ λ x : τ₂ . t₁ }>
  | tru : IsValue <{ true }>
  | fls : IsValue <{ false }>

attribute [StlcEval] Tm.IsValue.abs Tm.IsValue.tru Tm.IsValue.fls
```

::::full
The example terms named above are all abstractions, hence all values.  We
record that once each, so that the reduction examples can cite the fact by name
instead of unfolding the definition again at every use.
::::

:::dev "Yipeng Liu (berberman)"
Did we explain the `..` syntax earlier?
:::

```lean
theorem idB_value : Tm.IsValue idB := .abs ..
theorem idBB_value : Tm.IsValue idBB := .abs ..
theorem notB_value : Tm.IsValue notB := .abs ..
```

## STLC Programs

Finally, we must consider what constitutes a _complete_ program.

Intuitively, a "complete program" must not refer to any undefined
variables.  We'll see shortly how to define the _free_ variables
in a STLC term.  A complete program, then, is one that is
{deftech}_closed_ — that is, that contains no free variables.

(Conversely, a term that may contain free variables is often
called an {deftech}_open term_.)

:::dev "Chris Henson (chenson2018)" BeforeNextRelease
Is the "shortly" above setting wrong expectations?
Where exactly are we defining the free variables in a STLC term?
BCP 25: Indeed, we need to define "free"!
:::

:::slidebreak
:::

Having made the choice not to reduce under abstractions, we don't
need to worry about whether variables are values, since we'll
always be reducing programs "from the outside in," and that means
the `step` relation will always be working with closed terms.

## Substitution

Now we come to the heart of the STLC: the operation of
_substituting_ one term for a variable in another term.  This
operation is used below to define the operational semantics of
function application, where we will need to substitute the
argument term for the function parameter in the function's body.
For example, we reduce

```display
(λX:Bool. if X then true else X) false
```

to

```display
if false then true else false
```

by substituting `false` for the parameter `X` in the body of the
function.

In general, we need to be able to substitute some given term `s`
for occurrences of some variable `x` in another term `t`.
Informally, this is written `[x:=s]t` and pronounced "substitute
`s` for `x` in `t`."

:::slidebreak
:::

Here are some examples:

- `[X:=true] (if X then true else false)`
     yields `if true then true else false`

- `[X:=true] X` yields `true`

- `[X:=true] (if X then X else Y)` yields `if true then true else Y`

- `[X:=true] Y` yields `Y`

- `[X:=true] false` yields `false` (vacuous substitution)

- `[X:=true] (λY:Bool. if Y then X else false)`
     yields `λY:Bool. if Y then true else false`

- `[X:=true] (λY:Bool. X)` yields `λY:Bool. true`

- `[X:=true] (λY:Bool. Y)` yields `λY:Bool. Y`

- `[X:=true] (λX:Bool. X)` yields `λX:Bool. X`

The last example is illuminating: substituting `X` with `true` in
`λX:Bool. X` does _not_ yield `λX:Bool. true`!  The reason for
this is that the `X` in the body of `λX:Bool. X` is _bound_ by the
abstraction: it is a new, local name that just happens to be
spelled the same as some global name `X`.

:::slidebreak
:::

Here is the definition, informally...

```display
[x:=s]x               = s
[x:=s]y               = y                     if x ≠ y
[x:=s](λx:T. t)       = λx:T. t
[x:=s](λy:T. t)       = λy:T. [x:=s]t         if x ≠ y
[x:=s](t₁ t₂)         = ([x:=s]t₁) ([x:=s]t₂)
[x:=s]true            = true
[x:=s]false           = false
[x:=s](if t₁ then t₂ else t₃) =
                if [x:=s]t₁ then [x:=s]t₂ else [x:=s]t₃
```

:::slidebreak
:::

... and formally:

:::dev PotentialImprovement
1) explain better about alpha-conversion below.
2) Fix formatting of subst above to line up more nicely.
:::

```lean
def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  | .var y =>
      if x = y then s else t
  | .abs y τ t₁ =>
      if x = y then t else <{ λ y : τ . [x := s] t₁ }>
  | .app t₁ t₂ =>
      <{ ([x := s] t₁) ([x := s] t₂) }>
  | .tru => .tru
  | .fls => .fls
  | .ite t₁ t₂ t₃ =>
      <{ if [x := s] t₁ then [x := s] t₂ else [x := s] t₃ }>
```

:::full
Note that due to an unfortunate limitation of Lean's notation system, we
must use constructor names for match statements rather than our custom syntax.
:::

::::details "Notation encoding"
```lean
open Lean PrettyPrinter in
@[app_unexpander subst]
def unexpandSubst : Unexpander := StlcCommon.Delab.unexpandSubst
```
::::

::::full
As we did for the evaluators in the {ref "Slang"}[Slang] chapter, we pair the
definition with one _simplification lemma_ per constructor, saying how `subst`
behaves on that constructor. The variable and abstraction cases
each need two lemmas, since substitution treats a bound name differently
depending on whether it is the name being substituted for.
::::

```lean
variable (x y : String) (s t t₁ t₂ t₃ : Tm) (τ : Ty)

@[simp] theorem subst_var_eq : <{ [x := s] ~(Tm.var x) }> = s := by
  simp [subst]

@[simp] theorem subst_var_ne (h : x ≠ y) : <{ [x := s] ~(Tm.var y) }> = .var y := by
  simp [subst, h]

@[simp] theorem subst_abs_eq : <{ [x := s] (λ x : τ . t) }> = <{ λ x : τ . t }> := by
  simp [subst]

@[simp] theorem subst_abs_ne (h : x ≠ y) :
    <{ [x := s] (λ y : τ . t) }> = <{ λ y : τ . [x := s] t }> := by
  simp [subst, h]

@[simp] theorem subst_app :
    <{ [x := s] (t₁ t₂) }> = <{ ([x := s] t₁) ([x := s] t₂) }> := rfl

@[simp] theorem subst_tru : <{ [x := s] true }> = <{ true }> := rfl

@[simp] theorem subst_fls : <{ [x := s] false }> = <{ false }> := rfl

@[simp] theorem subst_ite :
    <{ [x := s] (if t₁ then t₂ else t₃) }> =
      <{ if [x := s] t₁ then [x := s] t₂ else [x := s] t₃ }> := rfl
```

:::ignore
```lean -show
/-- info: <{ [X := X] X }> : Tm -/
#guard_msgs in
#check <{ [X := X] X }>

/-- info: <{ [X := X] [X := Y] Z }> : Tm -/
#guard_msgs in
#check <{ [X := X] [X := Y] Z }>

/-- info: <{ [X := X] (λ Y : Bool . X) }> : Tm -/
#guard_msgs in
#check <{ [X := X] (λ Y : Bool . X) }>

/-- info: <{ [X := X] (λ Y : Bool . X Y) }> : Tm -/
#guard_msgs in
#check <{ [X := X] (λ Y : Bool . X Y) }>

/-- info: <{ [X := X] (λ Y : Bool . [X := X] X Y) }> : Tm -/
#guard_msgs in
#check <{ [X := X] (λ Y : Bool . ([X := X] X) Y) }>

/-- info: <{ [X := Z] Y [X := Z] X }> : Tm -/
#guard_msgs in
#check <{ ([X := Z] Y) ([X := Z] X) }>

/-- info: <{ [X := λ Y : Bool . Z] (X Z) }> : Tm -/
#guard_msgs in
#check <{ [X := (λ Y : Bool . Z)] (X Z) }>
```
:::

:::dev "mwhicks1" PotentialImprovement
Make one or two of the above `example` to make sure they produce the right term?
:::

::::quiz
What is the result of the following substitution?

```display
[X:=s](λY:T₁. X (λX:T₂. X))
```

(1) `(λY:T₁. X (λX:T₂. X))`

(2) `(λY:T₁. s (λX:T₂. s))`

(3) `(λY:T₁. s (λX:T₂. X))`

(4) none of the above
::::

_Technical note_: Substitution becomes trickier to define if
we consider the case where `s`, the term being substituted for a
variable in some other term, may itself contain free variables.
We say that `s` is an _open_ term.

:::slidebreak
:::

Here is an example. Using the above definition to substitute the open term

```display
s = λX:Bool. R
```

(where `R` is a _free_ reference to some global resource) for
the free variable `Z` in the term

```display
t = λR:Bool. Z
```

where `R` is a bound variable, we would get

```display
λR:Bool. λX:Bool. R
```

where the free reference to `R` in `s` has been "captured" by the
binder at the beginning of `t`.

:::slidebreak
:::

Why would this be bad?  Because it violates the principle that the
names of bound variables do not matter.  For example, if we rename
the bound variable in `t`, e.g., let

```display
t' = λW:Bool. Z
```

then `[Z:=s]t'` is

```display
λW:Bool. λX:Bool. R
```

which does not behave the same as the substituting in the original `t`:

```display
[Z:=s]t = λR:Bool. λX:Bool. R
```

That is, renaming a bound variable in `t` would change how `t`
behaves under our simple substitution. So substitution gets more
complicated in that setting, but fortunately we don't have that
problem in our STLC variant.

:::slidebreak
:::

Fortunately, since we are only interested here in defining the
`step` relation on {tech}_closed_ terms (i.e., terms like `λX:Bool. X`
that include binders for all of the variables they mention), we
can sidestep this extra complexity, but it must be dealt with when
formalizing richer languages.

:::slidebreak
:::

::::::full
:::::exercise (rating := 3) (name := "substi_correct")
The definition that we gave above defines substitution as a
_function_.  Suppose, instead, we wanted to define substitution as an
inductive _relation_ `Substi`.
We've begun the definition by providing the `inductive` header and
one of the constructors; your job is to fill in the rest of the
constructors and prove that the relation you've defined coincides
with the function given above.

```lean
inductive Substi (s : Tm) (x : String) : Tm → Tm → Prop where
  | var1 :
      Substi s x (.var x) s
-- SOLUTION
  | var2 (x' : String) (h : x ≠ x') :
      Substi s x (.var x') (.var x')
  | abs1 (τ₂ : Ty) (t₁ : Tm) :
      Substi s x <{ λ x : τ₂ . t₁ }> <{ λ x : τ₂ . t₁ }>
  | abs2 (x' : String) (τ₁ : Ty) (t₁ t₁' : Tm)
      (hx : x ≠ x') (h : Substi s x t₁ t₁') :
      Substi s x <{ λ x' : τ₁ . t₁ }> <{ λ x' : τ₁ . t₁' }>
  | app (t₁ t₂ t₁' t₂' : Tm)
      (h₁ : Substi s x t₁ t₁') (h₂ : Substi s x t₂ t₂') :
      Substi s x <{ t₁ t₂ }> <{ t₁' t₂' }>
  | tru :
      Substi s x <{ true }> <{ true }>
  | fls :
      Substi s x <{ false }> <{ false }>
  | ite (t₁ t₂ t₃ t₁' t₂' t₃' : Tm)
      (h₁ : Substi s x t₁ t₁') (h₂ : Substi s x t₂ t₂') (h₃ : Substi s x t₃ t₃') :
      Substi s x <{ if t₁ then t₂ else t₃ }> <{ if t₁' then t₂' else t₃' }>
-- END SOLUTION

theorem substi_correct (s : Tm) (x : String) (t t' : Tm) :
    <{ [x := s] t }> = t' ↔ Substi s x t t' := by
  solution!
    constructor
    · -- →
      intro h
      subst h
      induction t with
      | var y =>
          by_cases hxy : x = y
          · subst hxy; simp; exact .var1
          · simp [hxy]; exact .var2 y hxy
      | app t₁ t₂ ih₁ ih₂ => exact .app _ _ _ _ ih₁ ih₂
      | abs y T t₁ ih =>
          by_cases hxy : x = y
          · subst hxy; simp; exact .abs1 T t₁
          · simp [hxy]; exact .abs2 y T t₁ _ hxy ih
      | tru => exact .tru
      | fls => exact .fls
      | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ => exact .ite _ _ _ _ _ _ ih₁ ih₂ ih₃
    · -- ←
      intro h
      induction h <;> simp_all
```
:::::

::::::

## Reduction

::::full
The small-step reduction relation for STLC now follows the
same pattern as the ones we have seen before.  Intuitively, to
reduce a function application, we first reduce its left-hand
side (the function) until it becomes an abstraction; then we
reduce its right-hand side (the argument) until it is also a
value; and finally we substitute the argument for the bound
variable in the body of the abstraction.  This last rule, written
informally as

```display
(λx:T. t₁₂) v₂ ⟶ [x:=v₂] t₁₂
```

is traditionally called {deftech}_beta-reduction_.
::::

```
                              v.IsValue
                       -----------------------      (appAbs)
                        (λx:T. t) v ⟶ [x:=v]t

                              t₁ ⟶ t₁'
                          ----------------          (app1)
                           t₁ t₂ ⟶ t₁' t₂

                              v.IsValue
                              t₂ ⟶ t₂'
                          ----------------          (app2)
                           v₁ t₂ ⟶ v₁ t₂'
```

::::terse
(plus the usual rules for conditionals).
::::

::::full
... plus the usual rules for conditionals:

```
                  --------------------------------                (ifTrue)
                   (if true then t₁ else t₂) ⟶ t₁

                  ---------------------------------               (ifFalse)
                   (if false then t₁ else t₂) ⟶ t₂

                              t₁ ⟶ t₁'
        ----------------------------------------------------      (ifStep)
         (if t₁ then t₂ else t₃) ⟶ (if t₁' then t₂ else t₃)
```
::::

::::terse
The `appAbs` rule is often called {deftech}_beta-reduction_.
::::

This is {deftech}_call by value_ reduction: to reduce an
application `(t₁ t₂)`, we
  - first reduce `t₁` to a value: a function `λx:T. t`
  - then reduce the argument `t₂` to a value `v`
  - then reduce the application itself by substituting `v` for
    the bound variable `x` in the body `t`.

::::full
Formally:
::::

```lean
section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
  | appAbs (x : String) (τ : Ty) (t v : Tm) (hv : v.IsValue) :
      <{ (λ x : τ . t) v }> ⟶ <{ [x := v] t }>
  | app1 (t₁ t₁' t₂ : Tm) (h : t₁ ⟶ t₁') :
      <{ t₁ t₂ }> ⟶ <{ t₁' t₂ }>
  | app2 (v₁ t₂ t₂' : Tm) (hv : v₁.IsValue) (h : t₂ ⟶ t₂') :
      <{ v₁ t₂ }> ⟶ <{ v₁ t₂' }>
  | ifTrue (t₁ t₂ : Tm) :
      <{ if true then t₁ else t₂ }> ⟶ t₁
  | ifFalse (t₁ t₂ : Tm) :
      <{ if false then t₁ else t₂ }> ⟶ t₂
  | ifStep (t₁ t₁' t₂ t₃ : Tm) (h : t₁ ⟶ t₁') :
      <{ if t₁ then t₂ else t₃ }> ⟶ <{ if t₁' then t₂ else t₃ }>
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

-- for later use with `normalize`
attribute [StlcEval] Step.appAbs Step.app1 Step.app2 Step.ifTrue Step.ifFalse Step.ifStep
```

::::full
As in the {ref "Smallstep"}[Smallstep] chapter, `⟶*` is the multi-step closure
of `⟶` — that is, {name}`Multi` applied to this chapter's step relation.  We
inherit its reflexivity lemma along with it, so a zero-step execution goal
`t ⟶* t` is closed by `rfl`.
::::

::::quiz
What does the following term step to?

```display
(λX:Bool → Bool. X) (λX:Bool. X) ⟶ ???
```

(A) ` λX:Bool. X `

(B) ` λX:Bool → Bool. X `

(C) ` (λX:Bool → Bool. X) (λX:Bool. X) `

(D) none of the above
::::

::::quiz
What does the following term step to?

```display
(λX:Bool → Bool. X)
    ((λX:Bool → Bool. X) (λX:Bool. X))
⟶ ???
```

(A) ` λX:Bool. X `

(B) ` λX:Bool → Bool. X `

(C) ` (λX:Bool → Bool. X) (λX:Bool. X) `

(D) ` (λX:Bool → Bool. X) ((λX:Bool → Bool. X) (λX:Bool. X)) `

(E) none of the above
::::

::::quiz
What does the following term _normalize_ to?

```display
(λX:Bool → Bool. X) notB true  ⟶* ???
```

where `notB` abbreviates `λX:Bool. if X then false else true`

(A) ` λX:Bool. X `

(B) ` true `

(C) ` false `

(D) ` notB `

(E) none of the above
::::

::::quiz
What does the following term normalize to?

```display
(λX:Bool. X) (notB true) ⟶* ???
```

(A) ` λX:Bool. X `

(B) ` true `

(C) ` false `

(D) ` notB true `

(E) none of the above
::::

## Examples

Example:

```display
(λX:Bool → Bool. X) (λX:Bool. X) ⟶* λX:Bool. X
```

i.e.,

```display
idBB idB ⟶* idB
```

```lean
example : <{ idBB idB }> ⟶* idB := by
  apply Multi.step (y := idB)
  · exact .appAbs "X" <{ Bool → Bool }> <{ X }> idB idB_value
  · rfl
```

:::slidebreak
:::

Example:

```display
(λX:Bool → Bool. X) ((λX:Bool → Bool. X) (λX:Bool. X))
      ⟶* λX:Bool. X
```

i.e.,

```display
(idBB (idBB idB)) ⟶* idB.
```

```lean
example : <{ idBB (idBB idB) }> ⟶* idB := by
  -- the same reduction happens twice, so we name it
  have step₁ : <{ idBB idB }> ⟶ idB := by
    exact .appAbs "X" <{ Bool → Bool }> <{ X }> idB idB_value
  apply Multi.step (y := <{ idBB idB }>)
  · exact .app2 idBB <{ idBB idB }> idB idBB_value step₁
  apply Multi.step (y := idB)
  · exact step₁
  · rfl
```

:::slidebreak
:::

Example:

```display
(λX:Bool → Bool. X)
   (λX:Bool. if X then false else true)
   true
      ⟶* false
```

i.e.,

```display
(idBB notB) true ⟶* false.
```

```lean
example : <{ idBB notB true }> ⟶* <{ false }> := by
  apply Multi.step (y := <{ notB true }>)
  · exact .app1 <{ idBB notB }> notB <{ true }>
      (.appAbs "X" <{ Bool → Bool }> <{ X }> notB notB_value)
  apply Multi.step (y := <{ if true then false else true }>)
  · exact .appAbs "X" <{ Bool }> <{ if X then false else true }> <{ true }> .tru
  apply Multi.step (y := <{ false }>)
  · exact .ifTrue <{ false }> <{ true }>
  · rfl
```

:::slidebreak
:::

Example:

```display
(λX:Bool → Bool. X)
   ((λX:Bool. if X then false else true) true)
      ⟶* false
```

i.e.,

```display
idBB (notB true) ⟶* false.
```

(Note that this term doesn't actually typecheck; even so, we can
ask how it reduces.)

```lean
example : <{ idBB (notB true) }> ⟶* <{ false }> := by
  apply Multi.step (y := <{ idBB (if true then false else true) }>)
  · exact .app2 idBB <{ notB true }> <{ if true then false else true }> idBB_value
      (.appAbs "X" <{ Bool }> <{ if X then false else true }> <{ true }> .tru)
  apply Multi.step (y := <{ idBB false }>)
  · exact .app2 idBB <{ if true then false else true }> <{ false }> idBB_value
      (.ifTrue <{ false }> <{ true }>)
  apply Multi.step (y := <{ false }>)
  · exact .appAbs "X" <{ Bool → Bool }> <{ X }> <{ false }> .fls
  · rfl
```

As in the {ref "Smallstep"}[Smallstep] chapter, we can use the `normalize` tactic to simplify
these proofs:

```lean
example : <{ idBB idB }> ⟶* idB := by
  normalize using StlcEval

example : <{ idBB (idBB idB) }> ⟶* idB := by
  normalize using StlcEval

example : <{ idBB notB true }> ⟶* <{ false }> := by
  normalize using StlcEval

example : <{ idBB (notB true) }> ⟶* <{ false }> := by
  normalize using StlcEval
```

::::quiz
Do values and normal forms coincide in the language presented so far?

(A) yes

(B) no
::::

:::instructors
No, because we haven't come to the type system yet.
E.g., `true true` is a normal form but not a value.
:::

::::::full
:::::exercise (rating := 2) (name := "step_example5")
Try to do this one both with and without normalize.

```lean
theorem stepExample5 : <{ idBBBB idBB idB }> ⟶* idB := by
  solution!
    apply Multi.step (y := <{ idBB idB }>)
    · exact .app1 <{ idBBBB idBB }> idBB idB
        (.appAbs "X" <{ (Bool → Bool) → Bool → Bool }> <{ X }> idBB idBB_value)
    apply Multi.step (y := idB)
    · exact .appAbs "X" <{ Bool → Bool }> <{ X }> idB idB_value
    · rfl
```

:::gradeTheorem "1.5" stepExample5
:::

```lean
theorem stepExample5' : <{ idBBBB idBB idB }> ⟶* idB := by
  solution!
    normalize using StlcEval
```

:::gradeTheorem "0.5" stepExample5'
:::

:::::

::::::

# Typing

Next we consider the typing relation of the STLC, which is
meant to prevent reduction from getting stuck.

::::full
For instance, the following two STLC terms are both stuck:

: `if λX:Bool. X then true else false`

  Here we branch on a function as though it were a boolean.

: `true false`

  Here we apply a boolean as though it were a function.
::::

## Contexts

::::full
Although we are primarily interested in the binary relation
`⊢ t ⦂ T`, relating a closed term `t` to its type `T`, we need
to generalize a bit to make the definitions work.

Consider checking that `λx:T₁₁. t₁₂` has type
`T₁₁ → T₁₂`. Intuitively, we need to check that `t₁₂` has type
`T₁₂`. However, we have removed the binder `λx`, so `x` may occur
free in `t₁₂` (that is, `t₁₂` may be _open_).  While checking that
`t₁₂` has type `T₁₂`, we must remember that `x` has type `T₁₁`, in
order to deal with these free occurrences of `x`. Similarly, `t₁₂`
itself could contain abstractions, and typechecking their bodies
could require looking up the declared types of yet more free
variables.

To keep track of all this, we add a third element to the relation,
a {deftech}_typing context_ `Γ`, which records the types of the
variables that may occur free in a term — that is, Γ is a
partial map from variables to types.

The new {deftech}_typing judgment_ is written `Γ ⊢ t ⦂ T` and
informally read as "term `t` has type `T`, given the types of free
variables in `t` as specified by `Γ`".

We'll also write `x ↦ T ; Γ` for "update the partial map
`Γ` so that it maps `x` to `T`," following the notation from
the `Typeclasses` chapter.

With these refinements, we are ready to give informal and formal
specifications of the typing relation.
::::

:::dev "Chris Henson (chenson2018)" BeforeNextRelease
I find the FULL explanation above much better than the
TERSE one below, since the question below seems ill-posed without
extra context. Why would one want to type a term `X Y` if we've
just said that we will just look at closed terms as our programs?
:::

::::terse
_Question_: What is the type of the term "`X Y`"?

_Answer_: It depends on the types of `X` and `Y`!

I.e., in order to assign a type to a term, we need to know
what assumptions we should make about the types of its free
variables.

This leads us to a three-place _typing judgment_, informally
written `Γ ⊢ t ⦂ T`, where `Γ` is a
"typing context" — a mapping from variables to their types.
::::

```lean
abbrev Context := PartialMap String Ty
```

::::full
A context is a {name}`PartialMap` from variable names to types — the partial
maps of the `Typeclasses` chapter, which are total maps whose values are
optional, so that {name}`none` at a variable means "not bound here".
::::

::::terse
Following the usual notation for partial maps, we write
`(x ↦ T, Γ)` for "update the partial function `Γ` so
that it maps `x` to `T`."
::::

## Typing Relation

```
                              Γ x = τ₁
                            ------------                       (var)
                             Γ ⊢ x ⦂ τ₁

                        x ↦ τ₂ ; Γ ⊢ t₁ ⦂ τ₁
                      -------------------------                (abs)
                       Γ ⊢ λx:τ₂. t₁ ⦂ τ₂ → τ₁

                          Γ ⊢ t₁ ⦂ τ₂ → τ₁
                            Γ ⊢ t₂ ⦂ τ₂
                         ------------------                    (app)
                           Γ ⊢ t₁ t₂ ⦂ τ₁

                          -----------------                    (tru)
                           Γ ⊢ true ⦂ Bool

                         ------------------                    (fls)
                          Γ ⊢ false ⦂ Bool

             Γ ⊢ t₁ ⦂ Bool    Γ ⊢ t₂ ⦂ τ₁    Γ ⊢ t₃ ⦂ τ₁
            ---------------------------------------------      (ite)
                   Γ ⊢ if t₁ then t₂ else t₃ ⦂ τ₁
```

We can read the three-place relation `Γ ⊢ t ⦂ T` as:
"under the assumptions in Γ, the term `t` has the type `T`."

::::full
In the formal development, we write this judgment inside the same
`<{ .. }>` brackets we use for types and terms, as introduced by the
following notational conventions.
::::

::::terse
In the formal development, we write this judgment inside the same
`<{ .. }>` brackets.
::::

::::full
A context is written `∅` when empty and `x ↦ τ ; Γ` when extended with a
binding. The whole judgment then goes inside the same `<{ … }>` brackets as terms, written
with the turnstile and colon of the {ref "Types"}[Types] chapter:
`<{ Γ ⊢ t ⦂ τ }>`.
::::


```lean
inductive HasType : Context → Tm → Ty → Prop where
  | var (Γ : Context) (x : String) (τ₁ : Ty)
      (h : Γ[x] = some τ₁) :
      <{ Γ ⊢ ~(Tm.var x) ⦂ τ₁ }>
  | abs (Γ : Context) (x : String)
      (τ₁ τ₂ : Ty) (t₁ : Tm)
      (h : <{ x ↦ τ₂ ; Γ ⊢ t₁ ⦂ τ₁ }>) :
      <{ Γ ⊢ λ x : τ₂ . t₁ ⦂ τ₂ → τ₁ }>
  | app (Γ : Context) (τ₁ τ₂ : Ty)
      (t₁ t₂ : Tm)
      (h₁ : <{ Γ ⊢ t₁ ⦂ τ₂ → τ₁ }>)
      (h₂ : <{ Γ ⊢ t₂ ⦂ τ₂ }>) :
      <{ Γ ⊢ t₁ t₂ ⦂ τ₁ }>
  | tru (Γ : Context) :
       <{ Γ ⊢ true ⦂ Bool }>
  | fls (Γ : Context) :
       <{ Γ ⊢ false ⦂ Bool }>
  | ite (Γ : Context) (t₁ t₂ t₃ : Tm) (τ₁ : Ty)
      (h₁ : <{ Γ ⊢ t₁ ⦂ Bool }>)
      (h₂ : <{ Γ ⊢ t₂ ⦂ τ₁ }>)
      (h₃ : <{ Γ ⊢ t₃ ⦂ τ₁ }>) :
      <{ Γ ⊢ if t₁ then t₂ else t₃ ⦂ τ₁ }>


attribute [StlcTyping] HasType.var HasType.abs HasType.app HasType.tru HasType.fls HasType.ite
```

::::details "Notation encoding"
```lean
open Lean PrettyPrinter in
@[app_unexpander HasType]
def HasType.unexpand : Unexpander := StlcCommon.Delab.unexpandHasType
```
::::

:::ignore
```lean -show
/-- info: <{ ∅ ⊢ true ⦂ Bool }> : Prop -/
#guard_msgs in
#check <{ ∅ ⊢ true ⦂ Bool }>

/-- info: <{ X ↦ Bool ; ∅ ⊢ X ⦂ Bool }> : Prop -/
#guard_msgs in
#check HasType
  (PartialMap.update (∅ : Context) "X" Ty.bool)
  (Tm.var "X")
  Ty.bool

/-- info: fun Γ t τ => <{ Z ↦ Bool ; Γ ⊢ t ⦂ τ }> : Context → Tm → Ty → Prop -/
#guard_msgs in
#check fun (Γ : Context) (t : Tm) (τ : Ty) => <{ Z ↦ Bool ; Γ ⊢ t ⦂ τ }>
```
:::

## Examples

```lean
example : <{ ∅ ⊢ λ X : Bool . X ⦂ Bool → Bool }> := by
  apply HasType.abs
  apply HasType.var; rfl
```

The derivation is small enough to write out directly: an abstraction rule
whose premise is the variable rule, and the variable rule's premise — that the
extended context maps `X` to `Bool` — holds by computation, hence `rfl`.

:::slidebreak
:::

Much like reduction sequences, long derivations of typing rules can grow
quite tedious to prove. Luckily, we can have Lean automate proofs of this sort,
using another tactic: {tactic}`apply_rules`. This tactic works much like
{tactic}`normalize`, but is more efficient and will make progress even if it cannot
solve the goal outright. Like {tactic}`normalize`, {tactic}`apply_rules` also
takes a `using` argument which tells Lean which set of constructors to draw from.

```display
∅ ⊢ λX:Bool. λY:Bool → Bool. Y (Y X)
      ⦂ Bool → (Bool → Bool) → Bool.
```

```lean
example :
    <{ ∅ ⊢ λ X : Bool . λ Y : Bool → Bool . Y (Y X) ⦂
       Bool → (Bool → Bool) → Bool }> := by
  apply_rules using StlcTyping
```

It's worth noting that  {tactic}`apply_rules` relies on an important property
of our typing rules - namely, that they are _syntax directed_. A syntax directed
judgment is one where the syntax of a term completely determines which rule
can be applied at any given time; only one rule can be applied to each term.
This is important because {tactic}`apply_rules` just applies the first rule in
its set of constructors or lemmas that it can - it doesn't backtrack if that rule
isn't correct. So, making sure that only one rule can apply to any given term
is important to ensure that {tactic}`apply_rules` always discovers a valid
derivation, if one exists.

::::::full
:::::exercise (rating := 2) (name := "typing_example_2_full") (optional := true)
Prove the same result, applying one rule at a time and
naming the argument type of each application explicitly.

```lean
example :
    <{ ∅ ⊢ λ X : Bool . λ Y : Bool → Bool . Y (Y X) ⦂
       Bool → (Bool → Bool) → Bool }> := by
  solution!
    apply HasType.abs
    apply HasType.abs
    apply HasType.app (τ₂ := <{ Bool }>)
    · apply HasType.var; rfl
    · apply HasType.app (τ₂ := <{ Bool }>)
      · apply HasType.var; rfl
      · apply HasType.var; rfl
```
:::::
::::::

::::::full
:::::exercise (rating := 2) (name := "typing_example_3")
Formally prove the following typing derivation holds:

```display
∃ τ,
   ∅ ⊢ λX : Bool → Bool . λY : Bool → Bool . λZ : Bool .
               Y (X Z)
         ⦂ τ
```

```lean
example :
    ∃ τ, <{ ∅ ⊢ λ X : Bool → Bool . λ Y : Bool → Bool . λ Z : Bool . Y (X Z)
            ⦂ τ }> := by
  solution!
    exists <{ (Bool → Bool) → (Bool → Bool) → (Bool → Bool) }>
    apply_rules using StlcTyping
```
:::::

::::::

:::slidebreak
:::

We can also show that some terms are _not_ typable.  For example,
we can check that there is no typing derivation assigning a type
to the term `λX:Bool. λY:Bool. X Y` — i.e.,

```display
¬ ∃ τ, ∅ ⊢ λX:Bool. λY:Bool. X Y ⦂ τ
```

```lean
example : ¬ ∃ τ, <{ ∅ ⊢ λ X : Bool . λ Y : Bool . X Y ⦂ τ }> := by
  intro ⟨τ, hc⟩
  -- Each `cases` peels off one rule of the derivation, naming the premise it
  -- leaves behind; the context stays small because the old hypothesis goes away.
  cases hc with
  | abs _ _ _ _ _ h₁ =>
    cases h₁ with
    | abs _ _ _ _ _ h₂ =>
      cases h₂ with
      | app _ _ _ _ _ hf _ =>
        cases hf with
        | var _ _ _ hx =>
          -- `X` is bound to `Bool` in the context, but the application rule
          -- needs it to have an arrow type.
          exact Ty.noConfusion (Option.some.inj hx)
```

Another nonexample:

```display
¬ ∃ σ τ, ∅ ⊢ λX:σ. X X ⦂ τ
```

::::full
```lean
example : ¬ ∃ τ σ, <{ ∅ ⊢ λ X : τ . X X ⦂ σ }> := by
  solution!
    -- The two occurrences of `X` force its type `τ` to satisfy `τ = τ → σ`,
    -- and no (finite) type does.
    have arrow_ne : ∀ (τ₁ τ₂ : Ty), τ₁ ≠ Ty.arrow τ₁ τ₂ := by
      intro τ₁
      induction τ₁ with
      | bool => intro τ₂ h; cases h
      | arrow A B ihA _ => intro τ₂ h; injection h with h₁ _; exact ihA B h₁
    intro ⟨τ, σ, hc⟩
    cases hc with
    | abs _ _ _ _ _ h₁ =>
      cases h₁ with
      | app _ _ _ _ _ hf ha =>
        cases hf with
        | var _ _ _ hx =>
          cases ha with
          | var _ _ _ hy =>
            exact arrow_ne _ _ ((Option.some.inj hy).symm.trans (Option.some.inj hx))
```
::::

::::quiz
Which of the following propositions is _not_ provable?

(A) `Y ↦ Bool ; ∅ ⊢ λX:Bool. X ⦂ Bool → Bool`

(B) `∃ τ,  ∅ ⊢ λY:Bool → Bool. λX:Bool. Y X ⦂ τ`

(C) `∃ τ,  ∅ ⊢ λY:Bool → Bool. λX:Bool. X Y ⦂ τ`

(D) `∃ σ, X ↦ σ ; ∅ ⊢ λY:Bool → Bool. Y X ⦂ (Bool → Bool) → σ`
::::

::::quiz
Which of these is not provable?

(A) `∃ τ,  ∅ ⊢ λY:Bool → Bool → Bool. λX:Bool. Y X ⦂ τ`

(B) `∃ σ τ, X ↦ σ ; ∅ ⊢ X X X ⦂ τ`

(C) `∃ σ υ τ, X ↦ σ ; Y ↦ υ ; ∅ ⊢ λZ:Bool. X (Y Z) ⦂ τ`

(D) `∃ σ τ, X ↦ σ ; ∅ ⊢ λY:Bool. X (X Y) ⦂ τ`
::::

::::hide
```
/- LATER: Turn this into a quiz!  Maybe the next one too. -/

-- EX1? (typing_statements)

/- Which of the following propositions are provable?
       - [Y:Bool ⊢ λX:Bool. X ⦂ Bool → Bool] -/
-- QUIETSOLUTION
/-             - Yes -/
-- /QUIETSOLUTION
/-        - [∃ τ,  ∅ ⊢ λY:Bool → Bool. λX:Bool. Y X ⦂ τ] -/
-- QUIETSOLUTION
/-             - Yes -/
-- /QUIETSOLUTION
/-        - [∃ τ,  ∅ ⊢ λY:Bool → Bool. λX:Bool. X Y ⦂ τ] -/
-- QUIETSOLUTION
/-             - No -/
-- /QUIETSOLUTION
/-        - [∃ σ, X:σ ⊢ λY:Bool → Bool. Y X ⦂ (Bool → Bool) → σ] -/
-- QUIETSOLUTION
/-             - Yes -/
-- /QUIETSOLUTION
/-        - [∃ σ τ,  X:σ ⊢ X X X ⦂ τ] -/
-- QUIETSOLUTION
/-             - No -/
-- /QUIETSOLUTION
-- []

-- EX1M (more_typing_statements)
/- HIDE: Should we change A/B/C to Bool?  BAY: No, these get much less
interesting if A/B/C are all changed to Bool. -/
/- Which of the following propositions are provable (where [A], [B],
    and [C] stand for arbitrary types)?  For the ones that are, give
    witnesses for the existentially bound variables.
       - [∃ τ,  ∅ ⊢ λY:B → B → B. λX:B. Y X ⦂ τ] -/
-- QUIETSOLUTION
/-          - Answer: Yes
[[
           τ = (B → B → B) → B → (B → B)
]] -/
-- /QUIETSOLUTION
/-        - [∃ τ,  ∅ ⊢ λX:A → B. λY:B → C. λZ:A. Y (X Z) ⦂ τ] -/
-- QUIETSOLUTION
/-          - Answer: Yes
[[
           τ = (A → B) → (B → C) → A → C
]] -/
-- /QUIETSOLUTION
/-        - [∃ σ υ τ,  X:σ, Y:υ ⊢ λZ:A. X (Y Z) ⦂ τ] -/
-- QUIETSOLUTION
/-          - Answer: Yes
[[
           σ == B → C
           υ == A → B
           τ == A → C
]]
or
[[
           σ = A → A
           υ = A → A
           τ = A → A
]] -/
-- /QUIETSOLUTION
/-        - [∃ σ τ,  X:σ ⊢ λY:A. X (X Y) ⦂ τ] -/
-- QUIETSOLUTION
/-          - Answer: Yes
[[
           σ == A → A
           τ == A → A
]] -/
-- /QUIETSOLUTION
/-        - [∃ σ υ τ,  X:σ ⊢ X (λZ:υ. Z X) ⦂ τ] -/
-- QUIETSOLUTION
/-          - Answer: No -/
-- /QUIETSOLUTION

-- GRADE_MANUAL 1: more_typing_statements
-- []
```
::::

```lean
end Stlc
```
