import SFLMeta
import SFLMeta.Diagrams
import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer
import LF.Typeclasses
import TS.Smallstep

open Verso.Genre Manual
open SFLMeta
open InlineLean hiding lean

/-- An array that contains precisely `n` numbers.  Used only as an example of a
dependent type in the opening discussion of the lambda cube. -/
structure ArrayOfSize (n : Nat) : Type where
  nats : Array Nat
  nats_size_eq_n : nats.size = n

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
like {lean}`∀ n, ArrayOfSize n`.

The top right corner on the back, which combines all three features,
is called the {deftech}_Calculus of Constructions_.  First studied by
Coquand and Huet, it forms the foundation of Lean's logic.

# Overview

::::full
The STLC is built on some collection of _base types_:
booleans, numbers, strings, etc.  The exact choice of base types
doesn't matter much -- the definition of the language as well as
its theoretical properties work out the same no matter what we
choose -- so for the sake of brevity let's take just `Bool` for
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
formalize it below) for STLC terms `t`.
::::

::::terse
Begin with some set of _base types_ (here, just `Bool`)

Add: variables, function abstractions, and applications

Informal concrete syntax of terms `t`:
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
  (As in Lean, application associates to the left -- i.e., this
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
`MoreStlc` that it is easy to add named functions -- indeed, the
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

The last two, higher-order examples are left off the list on purpose -- working out
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
```

## Types

```lean
inductive Ty where
  | bool
  | arrow (T₁ T₂ : Ty)
```

## Terms

```lean
inductive Tm where
  | var (x : String)
  | app (t₁ t₂ : Tm)
  | abs (x : String) (T : Ty) (t : Tm)
  | tru
  | fls
  | ite (c t e : Tm)
```

:::slidebreak
:::

We need some notation magic to set up the concrete syntax, as
we did in the {ref "Types"}[Types] chapter...

::::full
The upshot of this section is that STLC types and terms are both written
inside one pair of brackets, `<{ … }>`, and that `~e` inside the brackets
escapes back to an arbitrary Lean expression:

- `<{ Bool → Bool }>` is a type;
- `<{ λ x : Bool . x }>` is a term -- a bare identifier inside the brackets is
  the object-language variable of that name, so `<{ x }>` is the variable `x`;
- `<{ ~t₁ ~t₂ }>` applies one Lean-level term to another.

Lean works out from context which of the two a given bracket holds, so the same
brackets serve for types, for terms, and -- when we come to typing -- for
typing judgments too.  How that works is in the collapsed blocks below; nothing
later in the chapter depends on it.
::::

::::terse
Types and terms are both written inside `<{ … }>`; `~e` escapes to Lean.
::::

:::instructors
If anything ever changes here, make sure to do the same
adjustment in all the other grammars for Stlc-like languages...
:::

::::details (summary := "Notation encoding: types")
The `stlcTy` grammar covers `Bool`, arrows (written `→` or `->`, associating to
the right), parentheses, and `~e`.  A bare identifier other than `Bool` is
spliced in as a Lean term, so a local `T` -- or any Lean expression of type
{name}`Ty` -- can appear directly inside the brackets.

To extend the grammar, a later chapter adds a `syntax` line to the category and
a matching `macro_rules` case; that is all it takes to add a new type construct.

```lean
declare_syntax_cat stlcTy
syntax:max "~" term:max : stlcTy
syntax:max "(" stlcTy ")" : stlcTy
syntax:max ident : stlcTy
syntax:50 stlcTy:51 " → " stlcTy:50 : stlcTy
syntax:50 stlcTy:51 " -> " stlcTy:50 : stlcTy
syntax:max (name := tyBracket) "<{ " stlcTy " }>" : term

macro_rules (kind := tyBracket)
  | `(<{ ~$T:term }>)    => pure T
  | `(<{ ($T:stlcTy) }>) => `(<{ $T:stlcTy }>)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Bool" => `(Ty.bool)
      | _ => `(($x : Ty))
  | `(<{ $T₁:stlcTy → $T₂:stlcTy }>)  => `(Ty.arrow <{ $T₁:stlcTy }> <{ $T₂:stlcTy }>)
  | `(<{ $T₁:stlcTy -> $T₂:stlcTy }>) => `(Ty.arrow <{ $T₁:stlcTy }> <{ $T₂:stlcTy }>)
```
::::

We'll write types inside of `<{ ... }>` brackets:

```lean
#check <{ Bool }>
#check <{ Bool -> Bool }>
#check <{ (Bool -> Bool) -> Bool }>
```

::::details (summary := "Notation encoding: terms")
Terms are built from variables, application (associating to the left),
abstraction, the two boolean constants, and conditionals.  A binding
occurrence -- the `x` in `λ x : T . t` -- has a small grammar of its own,
`stlcVar`, and `varStr` turns it into the string that {name}`Tm.abs` stores.

Because types and terms share the brackets, each `macro_rules` group says which
bracket it belongs to (`kind := tyBracket`, `kind := tmBracket`), and each
antiquote in a nested quotation says which grammar it came from.  A bare
identifier is the one genuinely overlapping case: `Bool` in term position would
otherwise quietly become a variable named `Bool`, so that rule rejects it, which
also settles which grammar a lone `<{ Bool }>` belongs to.

The last production, `[x := s] t`, is the notation for substitution; we give it
its meaning when we define substitution below.  It binds tighter than
application, so `[x:=s] t₁ t₂` is the application of `[x:=s] t₁` to `t₂`, and a
`λ` or `if` body must be parenthesized: `[x:=s] (λ y : Bool . x)`.

```lean
declare_syntax_cat stlcVar
syntax:max ident : stlcVar
syntax:max "~" term:max : stlcVar

open Lean in
/-- The string named by a variable in binding position. -/
def varStr (x : TSyntax `stlcVar) : MacroM Term :=
  match x with
  | `(stlcVar| $i:ident) => pure (quote i.getId.toString : Term)
  | `(stlcVar| ~$e)      => pure e
  | _ => Macro.throwUnsupported

declare_syntax_cat stlcTm
syntax:max "~" term:max : stlcTm
syntax:max "(" stlcTm ")" : stlcTm
syntax:max ident : stlcTm
syntax:75 stlcTm:75 ppSpace stlcTm:76 : stlcTm
syntax:50 "λ " stlcVar " : " stlcTy " . " stlcTm:50 : stlcTm
syntax:50 "if " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm
syntax:max "[" stlcVar " := " stlcTm "] " stlcTm:max : stlcTm
syntax:max (name := tmBracket) "<{ " stlcTm " }>" : term

open Lean in
macro_rules (kind := tmBracket)
  | `(<{ ~$e:term }>)    => pure e
  | `(<{ ($t:stlcTm) }>) => `(<{ $t:stlcTm }>)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "true"  => `(Tm.tru)
      | "false" => `(Tm.fls)
      | "Bool"  => Macro.throwErrorAt x "`Bool` is a type, not a term"
      | _       => `(Tm.var $(quote x.getId.toString))
  | `(<{ $t₁:stlcTm $t₂:stlcTm }>) => `(Tm.app <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
  | `(<{ λ $x : $T . $t }>) => do
      `(Tm.abs $(← varStr x) <{ $T:stlcTy }> <{ $t:stlcTm }>)
  | `(<{ if $c then $t else $e }>) =>
      `(Tm.ite <{ $c:stlcTm }> <{ $t:stlcTm }> <{ $e:stlcTm }>)
```
::::

::::details (summary := "Notation encoding: printing it back")
A _delaborator_ runs the grammar backwards: it rebuilds the concrete syntax
from a {name}`Ty` or {name}`Tm` value, so that types and terms appearing in
goals and in `#check` output print as `<{ λ x : Bool . x }>` rather than as a
pile of constructors.  (Setting `pp.notation false` turns it off, revealing the
underlying representation.)

```lean
open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
/-- Re-inserts parentheses in `stlcTy` output according to the grammar's precedences. -/
@[category_parenthesizer stlcTy]
def stlcTy.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `stlcTy true wrapParens prec <|
    parenthesizeCategoryCore `stlcTy prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(stlcTy| ($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
/-- Re-inserts parentheses in `stlcTm` output according to the grammar's precedences. -/
@[category_parenthesizer stlcTm]
def stlcTm.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `stlcTm true wrapParens prec <|
    parenthesizeCategoryCore `stlcTm prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(stlcTm| ($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTy` concrete syntax from a `Ty` value. -/
partial def delabTyInner : DelabM (TSyntax `stlcTy) := do
  let stx ←
    match_expr ← getExpr with
    | Ty.bool => `(stlcTy| $(mkIdent `Bool):ident)
    | Ty.arrow _ _ => do
        let a ← withAppFn <| withAppArg delabTyInner
        let b ← withAppArg delabTyInner
        `(stlcTy| $a → $b)
    | _ => do
        match ← delab with
        | `($i:ident) => `(stlcTy| $i:ident)
        | e => `(stlcTy| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean in
/-- Is `s` usable as a bare identifier in the object syntax? -/
def isPlainName (s : String) : Bool :=
  !s.isEmpty && !s.front.isDigit && s.all fun c => c.isAlphanum || c == '_'

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcVar` concrete syntax from the string in a binding position. -/
def delabVarInner : DelabM (TSyntax `stlcVar) := do
  match ← delab with
  | `($s:str) =>
      if isPlainName s.getString then
        `(stlcVar| $(mkIdent (Name.mkSimple s.getString)):ident)
      else `(stlcVar| ~$s)
  | e => `(stlcVar| ~$e)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTm` concrete syntax from a `Tm` value. -/
partial def delabTmInner : DelabM (TSyntax `stlcTm) := do
  let stx ←
    match_expr ← getExpr with
    | Tm.tru => `(stlcTm| $(mkIdent `true):ident)
    | Tm.fls => `(stlcTm| $(mkIdent `false):ident)
    | Tm.var _ => do
        match ← withAppArg delab with
        | `($s:str) =>
            if isPlainName s.getString then
              `(stlcTm| $(mkIdent (Name.mkSimple s.getString)):ident)
            else `(stlcTm| ~($(⟨← delab⟩)))
        | _ => `(stlcTm| ~($(⟨← delab⟩)))
    | Tm.app _ _ => do
        let f ← withAppFn <| withAppArg delabTmInner
        let a ← withAppArg delabTmInner
        `(stlcTm| $f $a)
    | Tm.abs _ _ _ => do
        let x ← withAppFn <| withAppFn <| withAppArg delabVarInner
        let T ← withAppFn <| withAppArg delabTyInner
        let t ← withAppArg delabTmInner
        `(stlcTm| λ $x : $T . $t)
    | Tm.ite _ _ _ => do
        let c ← withAppFn <| withAppFn <| withAppArg delabTmInner
        let t ← withAppFn <| withAppArg delabTmInner
        let e ← withAppArg delabTmInner
        `(stlcTm| if $c then $t else $e)
    | _ => do
        -- `subst` is defined below, so it is matched by name rather than with
        -- `match_expr`; a substitution prints in its own bracket notation.
        let e ← getExpr
        if e.getAppFn.constName? == some `Stlc.subst && e.getAppNumArgs == 3 then
          let x ← withAppFn <| withAppFn <| withAppArg delabVarInner
          let s ← withAppFn <| withAppArg delabTmInner
          let t ← withAppArg delabTmInner
          `(stlcTm| [$x := $s] $t)
        else
          match ← delab with
          | `($i:ident) => `(stlcTm| $i:ident)
          | e => `(stlcTm| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Stlc.Ty.bool, delab app.Stlc.Ty.arrow]
def delabTy : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Ty.bool => true | Ty.arrow _ _ => true | _ => false
  match ← delabTyInner with
  | `(stlcTy| ~$e) => pure e
  | e => `(<{ $e:stlcTy }>)

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Stlc.Tm.var, delab app.Stlc.Tm.app, delab app.Stlc.Tm.abs,
  delab app.Stlc.Tm.tru, delab app.Stlc.Tm.fls, delab app.Stlc.Tm.ite]
def delabTm : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Tm.var _ => true | Tm.app _ _ => true | Tm.abs _ _ _ => true
    | Tm.tru => true | Tm.fls => true | Tm.ite _ _ _ => true
    | _ => false
  match ← delabTmInner with
  | `(stlcTm| ~$e) => pure e
  | e => `(<{ $e:stlcTm }>)
```
::::

:::ignore
A few checks that the grammar parses the way it should -- application
associating to the left, conditionals nesting without parentheses, and `~`
escaping to Lean:

```lean -show
#check <{ λ x : Bool . λ y : Bool . x }>
#check <{ Bool → Bool }>
#check <{ Bool → Bool → Bool }>
#check <{ x }>
#check <{ x y }>
#check <{ (x y) (x y) }>
#check <{ x (y x) y x y }>
#check <{ λ x : Bool . x }>
#check <{ (λ x : Bool . x) y }>
#check <{ if x then x else x }>
#check <{ if x y then x else x }>
#check <{ if (x y) then x else x }>
#check <{ if x then if x then y else x else y z }>
#check <{ (if x then if x then y else x else y) z }>
#check <{ λ ~"z" : Bool . z z }>
```
:::

:::slidebreak
:::

Here are the terms we will use as running examples, written in the new
notation:

```lean
abbrev idB := <{ λ x : Bool . x }>

abbrev idBB := <{ λ x : Bool → Bool . x }>

abbrev idBBBB := <{ λ x : (Bool → Bool) → (Bool → Bool) . x }>

abbrev k := <{ λ x : Bool . λ y : Bool . x }>
```

:::slidebreak
:::

```lean
abbrev notB := <{ λ x : Bool . if x then false else true }>
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
  value -- i.e., only if the function's body has been
  reduced (as much as it can be without knowing what argument it
  is going to be applied to).

- Or we can say that `λx:T. t` is always a value, no matter
  whether `t` is one or not -- in other words, we can say that
  reduction stops at abstractions.

Our usual way of evaluating expressions in Lean makes the first
choice -- for example,

```lean
#reduce fun _x : Bool => 3 + 4
```

yields:

```display
fun _x => 7
```

But Lean is rather unusual in this respect.  Most functional
programming languages make the second choice -- reduction of a
function's body only begins when the function is actually applied
to an argument.

We also make the second choice here.

:::slidebreak
:::

```lean
inductive Tm.IsValue : Tm → Prop where
  | abs (x : String) (T₂ : Ty) (t₁ : Tm) : Tm.IsValue <{ λ ~x : ~T₂ . ~t₁ }>
  | tru : Tm.IsValue <{ true }>
  | fls : Tm.IsValue <{ false }>
```

::::full
The example terms named above are all abstractions, hence all values.  We
record that once each, so that the reduction examples can cite the fact by name
instead of unfolding the definition again at every use.
::::

```lean
theorem idB_value : idB.IsValue := .abs ..
theorem idBB_value : idBB.IsValue := .abs ..
theorem notB_value : notB.IsValue := .abs ..
```

:::dev
The Rocq source follows each inductive definition in this chapter with a
`Hint Constructors … : core`, registering the constructors with `auto`; the
proofs then lean on `auto`/`eauto` to assemble derivations.  We have no
counterpart here: the proofs below name their constructors explicitly, in the
style of the {ref "Types"}[Types] chapter.  Lean's `grind` would be the closest
analogue if a later pass wants automation.

:::

## STLC Programs

Finally, we must consider what constitutes a _complete_ program.

Intuitively, a "complete program" must not refer to any undefined
variables.  We'll see shortly how to define the _free_ variables
in a STLC term.  A complete program, then, is one that is
{deftech}_closed_ -- that is, that contains no free variables.

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
(λx:Bool. if x then true else x) false
```

to

```display
if false then true else false
```

by substituting `false` for the parameter `x` in the body of the
function.

In general, we need to be able to substitute some given term `s`
for occurrences of some variable `x` in another term `t`.
Informally, this is written `[x:=s]t` and pronounced "substitute
`s` for `x` in `t`."

:::slidebreak
:::

Here are some examples:

- `[x:=true] (if x then true else false)`
     yields `if true then true else false`

- `[x:=true] x` yields `true`

- `[x:=true] (if x then x else y)` yields `if true then true else y`

- `[x:=true] y` yields `y`

- `[x:=true] false` yields `false` (vacuous substitution)

- `[x:=true] (λy:Bool. if y then x else false)`
     yields `λy:Bool. if y then true else false`

- `[x:=true] (λy:Bool. x)` yields `λy:Bool. true`

- `[x:=true] (λy:Bool. y)` yields `λy:Bool. y`

- `[x:=true] (λx:Bool. x)` yields `λx:Bool. x`

The last example is illuminating: substituting `x` with `true` in
`λx:Bool. x` does _not_ yield `λx:Bool. true`!  The reason for
this is that the `x` in the body of `λx:Bool. x` is _bound_ by the
abstraction: it is a new, local name that just happens to be
spelled the same as some global name `x`.

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
explain better about alpha-conversion.
:::

```lean
section
set_option hygiene false in
local macro_rules (kind := tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  -- `.var y`, not `<{ ~y }>`: `y` is the variable's *name*, a `String`
  -- (see the note below the definition).
  | .var y =>
      if x = y then s else t
  | <{ λ ~y : ~T . ~t₁ }> =>
      if x = y then t else <{ λ ~y : ~T . [~x := ~s] ~t₁ }>
  | <{ ~t₁ ~t₂ }> =>
      <{ ([~x := ~s] ~t₁) ([~x := ~s] ~t₂) }>
  | <{ true }> =>
      <{ true }>
  | <{ false }> =>
      <{ false }>
  | <{ if ~t₁ then ~t₂ else ~t₃ }> =>
      <{ if [~x := ~s] ~t₁ then [~x := ~s] ~t₂ else [~x := ~s] ~t₃ }>
end

macro_rules (kind := tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)
```

::::instructors
About the definition above:
the variable case matches `.var y` rather than `<{ ~y }>`, because the
two `~`s mean different things.  Inside `<{ … }>` at a *term* position, `~e`
splices a Lean expression of type {name}`Tm`; at the *variable* position of a
`λ` (or of a substitution), `~e` splices a {name}`String`.  Destructuring
{name}`Tm.var` binds `y` to the variable's name -- a {name}`String` -- so
`<{ ~y }>` would be a type error.  The grammar has no production for "the
variable with this name", because naming a variable is what a bare identifier
already does, and a bare identifier is a literal rather than a splice.
::::

::::details (summary := "Notation encoding: substitution")
One more line registers substitutions with the printer, so that a goal
mentioning one reads as `[x := s] t` rather than as a `subst` application.

```lean
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Stlc.subst]
def delabSubst : Delab := whenPPOption getPPNotation do
  match ← delabTmInner with
  | `(stlcTm| ~$e) => pure e
  | e => `(<{ $e:stlcTm }>)
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
variable (x y : String) (s t t₁ t₂ t₃ : Tm) (T : Ty)

@[simp] theorem subst_var_eq : <{ [~x := ~s] ~(Tm.var x) }> = s := by
  simp [subst]

@[simp] theorem subst_var_ne (h : x ≠ y) : <{ [~x := ~s] ~(Tm.var y) }> = .var y := by
  simp [subst, h]

@[simp] theorem subst_abs_eq : <{ [~x := ~s] (λ ~x : ~T . ~t) }> = <{ λ ~x : ~T . ~t }> := by
  simp [subst]

@[simp] theorem subst_abs_ne (h : x ≠ y) :
    <{ [~x := ~s] (λ ~y : ~T . ~t) }> = <{ λ ~y : ~T . [~x := ~s] ~t }> := by
  simp [subst, h]

@[simp] theorem subst_app :
    <{ [~x := ~s] (~t₁ ~t₂) }> = <{ ([~x := ~s] ~t₁) ([~x := ~s] ~t₂) }> := rfl

@[simp] theorem subst_tru : <{ [~x := ~s] true }> = <{ true }> := rfl

@[simp] theorem subst_fls : <{ [~x := ~s] false }> = <{ false }> := rfl

@[simp] theorem subst_ite :
    <{ [~x := ~s] (if ~t₁ then ~t₂ else ~t₃) }> =
      <{ if [~x := ~s] ~t₁ then [~x := ~s] ~t₂ else [~x := ~s] ~t₃ }> := rfl
```

:::ignore
Checks that the substitution notation parses and nests as intended.

```lean -show
#check <{ [x := x] x }>
#check <{ [x := x] [x := y] z }>
#check <{ [x := x] (λ y : Bool . x) }>
#check <{ [x := x] (λ y : Bool . x y) }>
#check <{ [x := x] (λ y : Bool . ([x := x] x) y) }>
#check <{ ([x := z] y) ([x := z] x) }>
#check <{ [x := (λ y : Bool . y)] (x z) }>
```
:::

::::quiz
What is the result of the following substitution?

```display
[x:=s](λy:T₁. x (λx:T₂. x))
```

(1) `(λy:T₁. x (λx:T₂. x))`

(2) `(λy:T₁. s (λx:T₂. s))`

(3) `(λy:T₁. s (λx:T₂. x))`

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
s = λx:Bool. r
```

(where `r` is a _free_ reference to some global resource) for
the free variable `z` in the term

```display
t = λr:Bool. z
```

where `r` is a bound variable, we would get

```display
λr:Bool. λx:Bool. r
```

where the free reference to `r` in `s` has been "captured" by
the binder at the beginning of `t`.

:::slidebreak
:::

Why would this be bad?  Because it violates the principle that the
names of bound variables do not matter.  For example, if we rename
the bound variable in `t`, e.g., let

```display
t' = λw:Bool. z
```

then `[z:=s]t'` is

```display
λw:Bool. λx:Bool. r
```

which does not behave the same as the substituting in the original `t`:

```display
[z:=s]t = λr:Bool. λx:Bool. r
```

That is, renaming a bound variable in `t` would change how `t`
behaves under our simple substitution. So substitution gets more
complicated in that setting, but fortunately we don't have that
problem in our STLC variant.

:::slidebreak
:::

Fortunately, since we are only interested here in defining the
`step` relation on {tech}_closed_ terms (i.e., terms like `λx:Bool. x`
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
  | abs1 (T₂ : Ty) (t₁ : Tm) :
      Substi s x <{ λ ~x : ~T₂ . ~t₁ }> <{ λ ~x : ~T₂ . ~t₁ }>
  | abs2 (x' : String) (T₁ : Ty) (t₁ t₁' : Tm)
      (hx : x ≠ x') (h : Substi s x t₁ t₁') :
      Substi s x <{ λ ~x' : ~T₁ . ~t₁ }> <{ λ ~x' : ~T₁ . ~t₁' }>
  | app (t₁ t₂ t₁' t₂' : Tm)
      (h₁ : Substi s x t₁ t₁') (h₂ : Substi s x t₂ t₂') :
      Substi s x <{ ~t₁ ~t₂ }> <{ ~t₁' ~t₂' }>
  | tru :
      Substi s x <{ true }> <{ true }>
  | fls :
      Substi s x <{ false }> <{ false }>
  | ite (t₁ t₂ t₃ t₁' t₂' t₃' : Tm)
      (h₁ : Substi s x t₁ t₁') (h₂ : Substi s x t₂ t₂') (h₃ : Substi s x t₃ t₃') :
      Substi s x <{ if ~t₁ then ~t₂ else ~t₃ }> <{ if ~t₁' then ~t₂' else ~t₃' }>
-- END SOLUTION

theorem substi_correct (s : Tm) (x : String) (t t' : Tm) :
    <{ [~x := ~s] ~t }> = t' ↔ Substi s x t t' := by
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
                               value v
                       -----------------------      (appAbs)
                        (λx:T. t) v ⟶ [x:=v]t

                              t₁ ⟶ t₁'
                          ----------------          (app1)
                           t₁ t₂ ⟶ t₁' t₂

                              value v₁
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
  | appAbs (x : String) (T : Ty) (t v : Tm) (hv : v.IsValue) :
      <{ (λ ~x : ~T . ~t) ~v }> ⟶ <{ [~x := ~v] ~t }>
  | app1 (t₁ t₁' t₂ : Tm) (h : t₁ ⟶ t₁') :
      <{ ~t₁ ~t₂ }> ⟶ <{ ~t₁' ~t₂ }>
  | app2 (v₁ t₂ t₂' : Tm) (hv : v₁.IsValue) (h : t₂ ⟶ t₂') :
      <{ ~v₁ ~t₂ }> ⟶ <{ ~v₁ ~t₂' }>
  | ifTrue (t₁ t₂ : Tm) :
      <{ if true then ~t₁ else ~t₂ }> ⟶ t₁
  | ifFalse (t₁ t₂ : Tm) :
      <{ if false then ~t₁ else ~t₂ }> ⟶ t₂
  | ifStep (t₁ t₁' t₂ t₃ : Tm) (h : t₁ ⟶ t₁') :
      <{ if ~t₁ then ~t₂ else ~t₃ }> ⟶ <{ if ~t₁' then ~t₂ else ~t₃ }>
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'
```

::::full
As in the {ref "Smallstep"}[Smallstep] chapter, `⟶*` is the multi-step closure
of `⟶` -- that is, {name}`Multi` applied to this chapter's step relation.  We
inherit its reflexivity lemma along with it, so a zero-step execution goal
`t ⟶* t` is closed by `rfl`.
::::

::::quiz
What does the following term step to?

```display
(λx:Bool → Bool. x) (λx:Bool. x) ⟶ ???
```

(A) ` λx:Bool. x `

(B) ` λx:Bool → Bool. x `

(C) ` (λx:Bool → Bool. x) (λx:Bool. x) `

(D) none of the above
::::

::::quiz
What does the following term step to?

```display
(λx:Bool → Bool. x)
    ((λx:Bool → Bool. x) (λx:Bool. x))
⟶ ???
```

(A) ` λx:Bool. x `

(B) ` λx:Bool → Bool. x `

(C) ` (λx:Bool → Bool. x) (λx:Bool. x) `

(D) ` (λx:Bool → Bool. x) ((λx:Bool → Bool. x) (λx:Bool. x)) `

(E) none of the above
::::

::::quiz
What does the following term _normalize_ to?

```display
(λx:Bool → Bool. x) notB true  ⟶* ???
```

where `notB` abbreviates `λx:Bool. if x then false else true`

(A) ` λx:Bool. x `

(B) ` true `

(C) ` false `

(D) ` notB `

(E) none of the above
::::

::::quiz
What does the following term normalize to?

```display
(λx:Bool. x) (notB true) ⟶* ???
```

(A) ` λx:Bool. x `

(B) ` true `

(C) ` false `

(D) ` notB true `

(E) none of the above
::::

## Examples

Example:

```display
(λx:Bool → Bool. x) (λx:Bool. x) ⟶* λx:Bool. x
```

i.e.,

```display
idBB idB ⟶* idB
```

```lean
example : <{ ~idBB ~idB }> ⟶* idB := by
  apply Multi.step (y := idB)
  · exact .appAbs "x" <{ Bool → Bool }> <{ x }> idB idB_value
  · rfl
```

:::slidebreak
:::

Example:

```display
(λx:Bool → Bool. x) ((λx:Bool → Bool. x) (λx:Bool. x))
      ⟶* λx:Bool. x
```

i.e.,

```display
(idBB (idBB idB)) ⟶* idB.
```

```lean
example : <{ ~idBB (~idBB ~idB) }> ⟶* idB := by
  -- the same reduction happens twice, so we name it
  have step₁ : <{ ~idBB ~idB }> ⟶ idB := by
    exact .appAbs "x" <{ Bool → Bool }> <{ x }> idB idB_value
  apply Multi.step (y := <{ ~idBB ~idB }>)
  · exact .app2 idBB <{ ~idBB ~idB }> idB idBB_value step₁
  apply Multi.step (y := idB)
  · exact step₁
  · rfl
```

:::slidebreak
:::

Example:

```display
(λx:Bool → Bool. x)
   (λx:Bool. if x then false else true)
   true
      ⟶* false
```

i.e.,

```display
(idBB notB) true ⟶* false.
```

```lean
example : <{ ~idBB ~notB true }> ⟶* <{ false }> := by
  apply Multi.step (y := <{ ~notB true }>)
  · exact .app1 <{ ~idBB ~notB }> notB <{ true }>
      (.appAbs "x" <{ Bool → Bool }> <{ x }> notB notB_value)
  apply Multi.step (y := <{ if true then false else true }>)
  · exact .appAbs "x" <{ Bool }> <{ if x then false else true }> <{ true }> .tru
  apply Multi.step (y := <{ false }>)
  · exact .ifTrue <{ false }> <{ true }>
  · rfl
```

:::slidebreak
:::

Example:

```display
(λx:Bool → Bool. x)
   ((λx:Bool. if x then false else true) true)
      ⟶* false
```

i.e.,

```display
idBB (notB true) ⟶* false.
```

(Note that this term doesn't actually typecheck; even so, we can
ask how it reduces.)

```lean
example : <{ ~idBB (~notB true) }> ⟶* <{ false }> := by
  apply Multi.step (y := <{ ~idBB (if true then false else true) }>)
  · exact .app2 idBB <{ ~notB true }> <{ if true then false else true }> idBB_value
      (.appAbs "x" <{ Bool }> <{ if x then false else true }> <{ true }> .tru)
  apply Multi.step (y := <{ ~idBB false }>)
  · exact .app2 idBB <{ if true then false else true }> <{ false }> idBB_value
      (.ifTrue <{ false }> <{ true }>)
  apply Multi.step (y := <{ false }>)
  · exact .appAbs "x" <{ Bool → Bool }> <{ x }> <{ false }> .fls
  · rfl
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
:::dev
The Rocq source repeats the four examples above using the `normalize` tactic
defined in its `Smallstep` chapter, and the exercise below asks for
`step_example5` both with and without it.  We have no such tactic: the
{ref "Smallstep"}[Smallstep] chapter here does not define one, so the repeats
are dropped and the exercise is stated once, proved by hand.  Writing a
`normalize` tactic -- repeatedly applying {name}`Multi.step` with the unique
available reduction, then closing with reflexivity -- is the natural follow-up,
and it belongs in the Smallstep chapter, not here.
:::

:::::exercise (rating := 2) (name := "step_example5")
```lean
example : <{ ~idBBBB ~idBB ~idB }> ⟶* idB := by
  solution!
    apply Multi.step (y := <{ ~idBB ~idB }>)
    · exact .app1 <{ ~idBBBB ~idBB }> idBB idB
        (.appAbs "x" <{ (Bool → Bool) → Bool → Bool }> <{ x }> idBB idBB_value)
    apply Multi.step (y := idB)
    · exact .appAbs "x" <{ Bool → Bool }> <{ x }> idB idB_value
    · rfl
```
:::::

::::::

# Typing

Next we consider the typing relation of the STLC, which is
meant to prevent reduction from getting stuck.

::::full
For instance, the following two STLC terms are both stuck:

: `if λx:Bool. x then true else false`

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
variables that may occur free in a term -- that is, Γ is a
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
extra context. Why would one want to type a term `x y` if we've
just said that we will just look at closed terms as our programs?
:::

::::terse
_Question_: What is the type of the term "`x y`"?

_Answer_: It depends on the types of `x` and `y`!

I.e., in order to assign a type to a term, we need to know
what assumptions we should make about the types of its free
variables.

This leads us to a three-place _typing judgment_, informally
written `Γ ⊢ t ⦂ T`, where `Γ` is a
"typing context" -- a mapping from variables to their types.
::::

```lean
abbrev Context := TotalMap String (Option Ty)
```

::::full
A context is a _partial map_ from variable names to types, which we build --
as the `Typeclasses` chapter does -- as a total map whose values are
optional: {name}`none` at a variable means "not bound here".
::::

::::terse
Following the usual notation for partial maps, we write
`(x ↦ T, Γ)` for "update the partial function `Γ` so
that it maps `x` to `T`."
::::

## Typing Relation

```
                              Γ x = T₁
                            ------------                       (var)
                             Γ ⊢ x ⦂ T₁

                        x ↦ T₂ ; Γ ⊢ t₁ ⦂ T₁
                      -------------------------                (abs)
                       Γ ⊢ λx:T₂. t₁ ⦂ T₂ → T₁

                          Γ ⊢ t₁ ⦂ T₂ → T₁
                            Γ ⊢ t₂ ⦂ T₂
                         ------------------                    (app)
                           Γ ⊢ t₁ t₂ ⦂ T₁

                          -----------------                    (tru)
                           Γ ⊢ true ⦂ Bool

                         ------------------                    (fls)
                          Γ ⊢ false ⦂ Bool

             Γ ⊢ t₁ ⦂ Bool    Γ ⊢ t₂ ⦂ T₁    Γ ⊢ t₃ ⦂ T₁
            ---------------------------------------------      (ite)
                   Γ ⊢ if t₁ then t₂ else t₃ ⦂ T₁
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
A context is written `∅` when empty and `x ↦ T ; Γ` when extended with a
binding, and `~e` escapes to a Lean expression of type {name}`Context`.  The
whole judgment then goes inside the same `<{ … }>` brackets as terms, written
with the turnstile and colon of the {ref "Types"}[Types] chapter:
`<{ Γ ⊢ t ⦂ T }>`.
::::

::::details (summary := "Notation encoding: contexts and judgments")
Contexts get a grammar of their own, `stlcCtx`.  The *meaning* is the map update
we already have -- `x ↦ T ; Γ` expands to exactly the `Typeclasses` chapter's
update on `Γ` -- but its surface syntax has to be our own, because inside these
brackets all three positions are in object syntax.  Writing the map notation
directly would mean writing the binding as `"x" →ₜ some <{ Bool → Bool }> ; Γ`:
the name quoted, the value wrapped in {name}`some`, and the type escaped back
out of the brackets it belongs in.  The grammar hides those three encoding
details, and nothing else.

```lean
declare_syntax_cat stlcCtx
syntax:max "∅" : stlcCtx
syntax:max "~" term:max : stlcCtx
syntax:max stlcVar " ↦ " stlcTy " ; " stlcCtx : stlcCtx

syntax:max (name := judgeBracket) "<{ " stlcCtx " ⊢ " stlcTm " ⦂ " stlcTy " }>" : term

open Lean in
/-- The `Context` denoted by a context expression. -/
partial def ctxTerm (G : TSyntax `stlcCtx) : MacroM Term :=
  match G with
  | `(stlcCtx| ∅)   => `((∅ : Context))
  | `(stlcCtx| ~$e) => pure e
  | `(stlcCtx| $x:stlcVar ↦ $T:stlcTy ; $G:stlcCtx) => do
      `(TotalMap.update $(← ctxTerm G) $(← varStr x) (some <{ $T:stlcTy }>))
  | _ => Macro.throwUnsupported
```

As with `subst`, the judgment notation is used inside the definition it names,
so it is introduced in two steps: the rule below is declared `local` with
hygiene off, so the `HasType` in its expansion resolves to the relation being
declared, and after the `section` closes it is declared again for real use.

```lean
section
set_option hygiene false in
local macro_rules (kind := judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $T:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $T:stlcTy }>)
```
::::

```lean
inductive HasType : Context → Tm → Ty → Prop where
  | var (Γ : Context) (x : String) (T₁ : Ty) (h : Γ[x] = some T₁) :
      <{ ~Γ ⊢ ~(Tm.var x) ⦂ ~T₁ }>
  | abs (Γ : Context) (x : String) (T₁ T₂ : Ty) (t₁ : Tm)
      (h : <{ ~x ↦ ~T₂ ; ~Γ ⊢ ~t₁ ⦂ ~T₁ }>) :
      <{ ~Γ ⊢ λ ~x : ~T₂ . ~t₁ ⦂ ~T₂ → ~T₁ }>
  | app (Γ : Context) (T₁ T₂ : Ty) (t₁ t₂ : Tm)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ ~T₂ → ~T₁ }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~T₂ }>) :
      <{ ~Γ ⊢ ~t₁ ~t₂ ⦂ ~T₁ }>
  | tru (Γ : Context) :
      <{ ~Γ ⊢ true ⦂ Bool }>
  | fls (Γ : Context) :
      <{ ~Γ ⊢ false ⦂ Bool }>
  | ite (Γ : Context) (t₁ t₂ t₃ : Tm) (T₁ : Ty)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ Bool }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~T₁ }>)
      (h₃ : <{ ~Γ ⊢ ~t₃ ⦂ ~T₁ }>) :
      <{ ~Γ ⊢ if ~t₁ then ~t₂ else ~t₃ ⦂ ~T₁ }>
```

::::details (summary := "Notation encoding: the judgment, for real")
Closing the `section` retires the hygiene-free rule; the same rule is then
declared again, hygienically, for every later use.

```lean
end

macro_rules (kind := judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $T:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $T:stlcTy }>)
```
::::

::::details (summary := "Notation encoding: printing judgments back")
As with terms, a judgment prints back in its own notation, so that a goal reads
as `<{ x ↦ Bool ; ∅ ⊢ x ⦂ Bool }>` rather than as a `HasType` applied to a chain
of map updates.

```lean
open Lean PrettyPrinter in
/-- Rebuild `stlcCtx` syntax from the term syntax of a `Context`, so that a
context prints as `x ↦ Bool ; Γ` rather than as a chain of map updates. -/
partial def unexpandCtx : Term → UnexpandM (TSyntax `stlcCtx)
  | `(∅) => `(stlcCtx| ∅)
  | `($x:str →ₜ some $T ; $G) => do
      let G' ← unexpandCtx G
      let x' : TSyntax `stlcVar ←
        if isPlainName x.getString then
          `(stlcVar| $(mkIdent (Name.mkSimple x.getString)):ident)
        else `(stlcVar| ~$x)
      match T with
      | `(<{ $T':stlcTy }>) => `(stlcCtx| $x':stlcVar ↦ $T' ; $G')
      | _                   => `(stlcCtx| $x':stlcVar ↦ ~($T) ; $G')
  | G => `(stlcCtx| ~($G))

open Lean PrettyPrinter in
@[app_unexpander Stlc.HasType]
def HasType.unexpand : Unexpander
  | `($_ $G <{ $t:stlcTm }> <{ $T:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ $T }>)
  | `($_ $G <{ $t:stlcTm }> $T) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ ~($T) }>)
  | `($_ $G $t <{ $T:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ $T }>)
  | `($_ $G $t $T) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ ~($T) }>)
  | _ => throw ()
```
::::

:::ignore
```lean -show
#check <{ true }>
#check <{ ∅ ⊢ true ⦂ Bool }>
```
:::

## Examples

```lean
example : <{ ∅ ⊢ λ x : Bool . x ⦂ Bool → Bool }> :=
  .abs _ "x" _ _ _ (.var _ "x" _ rfl)
```

The derivation is small enough to write out directly: an abstraction rule
whose premise is the variable rule, and the variable rule's premise -- that the
extended context maps `x` to `Bool` -- holds by computation, hence `rfl`.

:::dev
The Rocq source proves this one, and the next, by `eauto`, having registered
the `has_type` constructors in the `core` hint database; it also observes that
plain `auto` suffices here because the term contains no application nodes.  We
have no hint database, so both derivations are given explicitly.
:::

:::slidebreak
:::

More examples:

```display
∅ ⊢ λx:Bool. λy:Bool → Bool. y (y x)
      ⦂ Bool → (Bool → Bool) → Bool.
```

```lean
example :
    <{ ∅ ⊢ λ x : Bool . λ y : Bool → Bool . y (y x) ⦂
       Bool → (Bool → Bool) → Bool }> :=
  .abs _ _ _ _ _ (.abs _ _ _ _ _
    (.app _ _ Ty.bool _ _ (.var _ "y" _ rfl)
      (.app _ _ Ty.bool _ _ (.var _ "y" _ rfl) (.var _ "x" _ rfl))))
```

::::::full
:::::exercise (rating := 2) (name := "typing_example_2_full")
Prove the same result in tactic mode, applying one rule at a time and
naming the argument type of each application explicitly.

```lean
example :
    <{ ∅ ⊢ λ x : Bool . λ y : Bool → Bool . y (y x) ⦂
       Bool → (Bool → Bool) → Bool }> := by
  solution!
    apply HasType.abs
    apply HasType.abs
    apply HasType.app (T₂ := <{ Bool }>)
    · apply HasType.var; rfl
    · apply HasType.app (T₂ := <{ Bool }>)
      · apply HasType.var; rfl
      · apply HasType.var; rfl
```
:::::

::::::

::::::full
:::::exercise (rating := 2) (name := "typing_example_3")
Formally prove the following typing derivation holds:

```display
∃ T,
   ∅ ⊢ λ x : Bool → Bool . λ y : Bool → Bool . λ z : Bool .
               y (x z)
         ⦂ T
```

```lean
example :
    ∃ T, <{ ∅ ⊢ λ x : Bool → Bool . λ y : Bool → Bool . λ z : Bool . y (x z)
            ⦂ ~T }> :=
  solution!(
    ⟨<{ (Bool → Bool) → (Bool → Bool) → (Bool → Bool) }>,
     .abs _ _ _ _ _ (.abs _ _ _ _ _ (.abs _ _ _ _ _
       (.app _ _ Ty.bool _ _ (.var _ "y" _ rfl)
         (.app _ _ Ty.bool _ _ (.var _ "x" _ rfl) (.var _ "z" _ rfl)))))⟩)
```
:::::

::::::

:::slidebreak
:::

We can also show that some terms are _not_ typable.  For example,
we can check that there is no typing derivation assigning a type
to the term `λx:Bool. λy:Bool. x y` -- i.e.,

```display
¬ ∃ T, ∅ ⊢ λx:Bool. λy:Bool. x y ⦂ T
```

```lean
example : ¬ ∃ T, <{ ∅ ⊢ λ x : Bool . λ y : Bool . x y ⦂ ~T }> := by
  intro ⟨T, hc⟩
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
          -- `x` is bound to `Bool` in the context, but the application rule
          -- needs it to have an arrow type.
          exact Ty.noConfusion (Option.some.inj hx)
```


Another nonexample:

```display
¬ ∃ S T, ∅ ⊢ λx:S. x x ⦂ T
```

::::full
```lean
example : ¬ ∃ S T, <{ ∅ ⊢ λ x : ~S . x x ⦂ ~T }> := by
  solution!
    -- The two occurrences of `x` force its type `S` to satisfy `S = S → T`,
    -- and no (finite) type does.
    have arrow_ne : ∀ (T₁ T₂ : Ty), T₁ ≠ Ty.arrow T₁ T₂ := by
      intro T₁
      induction T₁ with
      | bool => intro T₂ h; cases h
      | arrow A B ihA _ => intro T₂ h; injection h with h₁ _; exact ihA B h₁
    intro ⟨S, T, hc⟩
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

:::dev
The Rocq proof gets to the same contradiction through a chain of `inversion`s
and then an induction on the offending type; the `LATER` note there asks why
`eauto 30` makes no progress on the previous example, and a `NOTATION` note
from Ori reports an error with the associativity of the arrow in one of the
inversion hypotheses.  Neither issue arises in this encoding.
:::

::::quiz
Which of the following propositions is _not_ provable?

(A) `y ↦ Bool ; ∅ ⊢ λx:Bool. x ⦂ Bool → Bool`

(B) `∃ T,  ∅ ⊢ λy:Bool → Bool. λx:Bool. y x ⦂ T`

(C) `∃ T,  ∅ ⊢ λy:Bool → Bool. λx:Bool. x y ⦂ T`

(D) `∃ S, x ↦ S ; ∅ ⊢ λy:Bool → Bool. y x ⦂ (Bool → Bool) → S`
::::

::::quiz
Which of these is not provable?

(A) `∃ T,  ∅ ⊢ λy:Bool → Bool → Bool. λx:Bool. y x ⦂ T`

(B) `∃ S T, x ↦ S ; ∅ ⊢ x x x ⦂ T`

(C) `∃ S U T, x ↦ S ; y ↦ U ; ∅ ⊢ λz:Bool. x (y z) ⦂ T`

(D) `∃ S T, x ↦ S ; ∅ ⊢ λy:Bool. x (x y) ⦂ T`
::::

::::hide
```
/- LATER: Turn this into a quiz!  Maybe the next one too. -/

-- EX1? (typing_statements)

/- Which of the following propositions are provable?
       - [y:Bool ⊢ λx:Bool. x ⦂ Bool → Bool] -/
-- QUIETSOLUTION
/-             - Yes -/
-- /QUIETSOLUTION
/-        - [∃ T,  ∅ ⊢ λy:Bool → Bool. λx:Bool. y x ⦂ T] -/
-- QUIETSOLUTION
/-             - Yes -/
-- /QUIETSOLUTION
/-        - [∃ T,  ∅ ⊢ λy:Bool → Bool. λx:Bool. x y ⦂ T] -/
-- QUIETSOLUTION
/-             - No -/
-- /QUIETSOLUTION
/-        - [∃ S, x:S ⊢ λy:Bool → Bool. y x ⦂ (Bool → Bool) → S] -/
-- QUIETSOLUTION
/-             - Yes -/
-- /QUIETSOLUTION
/-        - [∃ S T,  x:S ⊢ x x x ⦂ T] -/
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
       - [∃ T,  ∅ ⊢ λy:B → B → B. λx:B. y x ⦂ T] -/
-- QUIETSOLUTION
/-          - Answer: Yes
[[
           T = (B → B → B) → B → (B → B)
]] -/
-- /QUIETSOLUTION
/-        - [∃ T,  ∅ ⊢ λx:A → B. λy:B → C. λz:A. y (x z) ⦂ T] -/
-- QUIETSOLUTION
/-          - Answer: Yes
[[
           T = (A → B) → (B → C) → A → C
]] -/
-- /QUIETSOLUTION
/-        - [∃ S U T,  x:S, y:U ⊢ λz:A. x (y z) ⦂ T] -/
-- QUIETSOLUTION
/-          - Answer: Yes
[[
           S == B → C
           U == A → B
           T == A → C
]]
or
[[
           S = A → A
           U = A → A
           T = A → A
]] -/
-- /QUIETSOLUTION
/-        - [∃ S T,  x:S ⊢ λy:A. x (x y) ⦂ T] -/
-- QUIETSOLUTION
/-          - Answer: Yes
[[
           S == A → A
           T == A → A
]] -/
-- /QUIETSOLUTION
/-        - [∃ S U T,  x:S ⊢ x (λz:U. z x) ⦂ T] -/
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
