import SFLMeta

import TS.Stlc
import TS.Smallstep
import LF.CustomTactics

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "References: Typing Mutable References" =>
%%%
tag := "References"
htmlSplit := .never
file := some "References"
%%%

::::instructors
The proof of preservation for this system is actually
very interesting.  It is given as an exercise, but if there's
enough class time it would be well worth devoting a lecture to
it!
::::

::::dev PotentialImprovement
The text in this chapter — especially the terse version —
does not do a great job, early on, of connecting the concepts to
things that students will already know about. This makes the later
parts unnecessarily puzzling.  (Also, the terse slides have way too
much text and not NEARLY enough examples, quizzes, etc.)
Sampsa:
The exercise `factorial_ref` is tricky,
because the definition of `tseq` is unhygienic
with respect to the variable `x`.
Thus, the following does not work unless the variable `x` is renamed.

```
fact = λx : Nat , (λr : Ref (Nat → Nat) ,
  r := λx : Nat , if x == 0 then 1 else x * !r (pred x);
  !r x) (ref (λx : Nat , 0))
```

For the TERSE version, there are a bunch of slides in the
two 2006 Chapter 13 lectures that would be great to include
here.

The UPenn 2011 final exam has some good simple questions that
should be repeated here (question 5).

More of the exercises should be marked recommended.
::::

::::full
Up to this point, we have considered a variety of _pure_
language features, including functional abstraction, basic types
such as numbers and booleans, and structured types such as records
and variants.  These features form the backbone of most
programming languages — including purely functional languages
such as Haskell and "mostly functional" languages such as ML, as
well as imperative languages such as C and object-oriented
languages such as Java, C#, and Scala.

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

In this chapter, we'll see how one sort of computational effect —
mutable references — can be added to the calculi we have studied.
The main extension will be dealing explicitly with a _store_ (or
_heap_) and _pointers_ that name store locations.  This extension
is fairly straightforward to define; the most interesting part is
the refinement we need to make to the statement of the type
preservation theorem.
::::

::::terse
Most real languages include _impure_ features
("computational effects")...
- mutable pointer structures
- non-local control constructs (exceptions, continuations, etc.)
- inter-process synchronization and communication
- etc.

Goal for this chapter: Formalize pointers.
::::

# Definitions

::::full
Pretty much every programming language provides some form of
assignment operation that changes the contents of a previously
allocated piece of storage.  (Lean is a rare exception!)

In some languages — notably ML and its relatives — the
mechanisms for name binding and those for assignment are kept
separate.  We can have a variable `x` whose _value_ is the number
`5`, or we can have a variable `y` whose value is a
_reference_ (or _pointer_) to a mutable cell whose current
contents is `5`.  These are different things, and the difference
is visible to the programmer.  We can add `x` to another number,
but not assign to it.  We can use `y` to assign a new value to the
cell that it points to (by writing `y:=84`), but we cannot use `y`
directly as an argument to an operation like `+`.  Instead, we
must explicitly _dereference_ it, writing `!y` to obtain its
current contents.

In most other languages — in particular, in all members of the C
family, including Java — _every_ variable name refers to a
mutable cell, and the operation of dereferencing a variable to
obtain its current contents is implicit.

For purposes of formal study, it is useful to keep these
mechanisms separate.  The development in this chapter will closely
follow ML's model.  Applying the lessons learned here to C-like
languages is a straightforward matter of collapsing some
distinctions and rendering some operations such as dereferencing
implicit instead of explicit.
::::

::::terse
In most real-world programming languages, the mechanisms of
_name binding_ and _storage allocation_ are (intentionally)
confused: every name refers to a mutable piece of storage.

Conceptually, it's cleaner to separate the two:
    - use the mechanisms we already have for name binding
      (abstraction, let);
    - introduce new operations for allocating, changing,
      and looking up the contents of references (pointers).
::::

## Syntax

::::full
In this chapter, we study adding mutable references to the
simply-typed lambda calculus with natural numbers.
::::

```lean
namespace STLCRef

open scoped MyGetElem
```

The basic operations on references are _allocation_,
_dereferencing_, and _assignment_.

- To allocate a reference, we use the `ref` operator, providing
  an initial value for the new cell.

  For example, `ref 5` creates a new cell containing the value
  `5` and reduces to a reference to that cell.

- To read the current value of this cell, we use the
  dereferencing operator `!`.

  For example, `!(ref 5)` reduces to `5`.

- To change the value stored in a cell, we use the assignment
  operator.

  If `r` is a reference, `r := 7` will store the value `7` in
  the cell referenced by `r`.

## Types

::::full
We start with the simply typed lambda calculus over the
natural numbers. Besides the base natural-number type and arrow
types, we add two more types to deal with references. First, we
need the _unit type_, which we will use as the result type of an
assignment operation.  We then add _reference types_.
::::

If `τ` is a type, then `Ref τ` is the type of references to
cells holding values of type `τ`.

```bnf
τ ::= Nat
    | Unit
    | τ "→" τ
    | "Ref" τ ;
```

```lean
inductive Ty : Type :=
  | nat : Ty
  | unit : Ty
  | arrow : Ty → Ty → Ty
  | ref : Ty → Ty
```

## Terms

Besides the usual variables, abstractions, applications,
terms related to natural numbers, and `unit`, we need four
more sorts of terms to handle mutable references:

```bnf
t ::= "ref" t    ("reference")
    | "!"t       ("dereference")
    | t ":=" t   ("assignment")
    | l          ("location");
```

```lean
inductive Tm  : Type :=
  -- STLC with numbers:
  | var    : String → Tm
  | app    : Tm → Tm → Tm
  | abs    : String → Ty → Tm → Tm
  | const  : Nat → Tm
  | succ    : Tm → Tm
  | pred    : Tm → Tm
  | mult    : Tm → Tm → Tm
  | ite0  : Tm → Tm → Tm → Tm
  -- New terms:
  | unit   : Tm
  | ref    : Tm → Tm
  | deref  : Tm → Tm
  | assign : Tm → Tm → Tm
  | loc    : Nat → Tm
```

::::details "Notation"
```lean
scoped syntax:max num : stlcTm
scoped syntax:60 stlcTm:60 " * " stlcTm:61 : stlcTm
scoped syntax:50 "if0 " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

scoped syntax:60 stlcTm:60 " := " stlcTm:61 : stlcTm
scoped syntax:60 "Ref " stlcTy:61 : stlcTy
scoped syntax:60 "ref " stlcTm:61 : stlcTm
scoped syntax:60 "loc " stlcTm:61 : stlcTm
scoped syntax:60 "!" stlcTm:61 : stlcTm
scoped syntax:55 stlcTm:56 " ; " stlcTm:55 : stlcTm

scoped syntax stlcCtx " / " term:max " ⊢ " stlcTm " ⦂ " stlcTy : stlcQuoted

abbrev Tm.tseq t₁ t₂ :=
  Tm.app (.abs "X" .unit t₂) t₁

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
  subst := `STLCRef.subst
  hasType := `STLCRef.HasType

def extendedTyHandler : TyElabHandler :=
  fun recur k T => do
    match T with
    | `(stlcTy| Nat) =>
        return mkConst ``Ty.nat
    | `(stlcTy| Unit) =>
        return mkConst ``Ty.unit
    | `(stlcTy| Ref $τ:stlcTy) => do
        let τ ← recur τ
        return mkApp (mkConst ``Ty.ref) τ
    | _ => k T

def tyHandlers : TyElabHandler :=
  extendedTyHandler.orElse (commonTyHandler language)

partial def elabTy : TyElab :=
  tyHandlers elabTy <| unsupportedTy language

def extendedTmHandler : TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    | `(stlcTm| $n:num) => do
        return (mkApp (mkConst ``Tm.const) (mkNatLit n.getNat), free )

    | `(stlcTm| Nat) => do
        throwError "`Nat` is not a valid term."

    | `(stlcTm| succ $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.succ) t, free)

    | `(stlcTm| pred $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.pred) t, free)

    | `(stlcTm| $t₁:stlcTm * $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.mult) t₁ t₂, free)

    | `(stlcTm| if0 $c:stlcTm then $t:stlcTm else $e:stlcTm) => do
        let (c, free) ← recur Γ free c
        let (t, free) ← recur Γ free t
        let (e, free) ← recur Γ free e
        return (mkApp3 (mkConst ``Tm.ite0) c t e, free)

    | `(stlcTm| Unit) => do
        throwError "`Unit` is not a valid term."

    | `(stlcTm| unit) => do
        return (mkConst ``Tm.unit, free)

    | `(stlcTm| ref $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.ref) t, free)

    | `(stlcTm| !$t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.deref) t, free)

    | `(stlcTm| loc $n:num) => do
        return (mkApp (mkConst ``Tm.loc) (mkNatLit n.getNat), free )

    | `(stlcTm| $t₁:stlcTm := $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.assign) t₁ t₂, free)

    | `(stlcTm| $t₁:stlcTm ; $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.tseq) t₁ t₂, free)

    | _ => k Γ free t

def tmHandlers : TmElabHandler :=
  extendedTmHandler.orElse (commonTmHandler language elabTy)

partial def elabTm : TmElab :=
  tmHandlers elabTm unsupportedTm

def elabCtx : CtxElab := elabCtxCommon language elabTy

-- `HasType` takes the store typing as an extra first argument,
-- so we build typing judgments here instead of in `elabQuoted`.
def mkHasType (δ Γ t T : Expr) : TermElabM Expr := do
  let some hasType ← resolveId? (mkIdent language.hasType)
    | throwError "unknown declaration `{language.hasType}`"
  return mkApp4 hasType δ Γ t T

@[scoped term_elab StlcCommon.bracket]
def elabBracket : TermElab :=
  fun stx expectedType? => do
    match stx with
    | `(<{ $Γ:stlcCtx / $δ:term ⊢ $t:stlcTm ⦂ $T:stlcTy }>) => do
        let (Γ, scope) ← elabCtx Γ
        let (t, _) ← elabTm scope [] t
        let T ← elabTy T
        let δ ← elabTermEnsuringType δ (mkApp (mkConst ``List [levelZero]) (mkConst ``Ty))
        mkHasType δ Γ t T
    | `(<{ $_:stlcCtx ⊢ $_:stlcTm ⦂ $_:stlcTy }>) =>
        throwError "typing judgments need a store typing: write `Γ / δ ⊢ t ⦂ τ`"
    | `(<{ $q:stlcQuoted }>) =>
        elabQuoted language elabTy elabTm elabCtx q expectedType?
    | _ => throwUnsupportedSyntax

end Elab

open scoped Elab

namespace Delab

open StlcCommon Elab Delab
open Lean PrettyPrinter Delaborator

@[app_unexpander Ty.nat]
private def Ty.unexpandNat : Unexpander
  | stx => do
    let Nat := mkObjectIdentFrom stx "Nat"
    let T ← `(stlcTy| $Nat:ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.unit]
private def Ty.unexpandUnit : Unexpander
  | stx => do
    let Unit := mkObjectIdentFrom stx "Unit"
    let T ← `(stlcTy| $Unit:ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.arrow]
private def Ty.unexpandArrow : Unexpander := Delab.unexpandArrow

@[app_unexpander Ty.ref]
private def Ty.unexpandRef : Unexpander
  | `($_ $T) => do
      let T' := getTy T
      `(<{ Ref $T':stlcTy }>)
  | _ => throw ()

private def reservedNames : String → Bool
  | "Nat" | "Unit" | "succ" | "pred"
  | "if0" | "ref" | "loc" | "Ref"
  | "unit" => true
  | _ => false

@[app_unexpander Tm.var]
private def Tm.unexpandVar : Unexpander := Delab.unexpandVar reservedNames ``Tm.var

@[app_delab Tm.var]
private def Tm.delabVar : Delab := Delab.delabVar ``Tm.var

@[app_unexpander Tm.app]
private def Tm.unexpandApp : Unexpander := Delab.unexpandApp

@[app_unexpander Tm.abs]
private def Tm.unexpandAbs : Unexpander := Delab.unexpandAbs

@[app_unexpander Tm.const]
private def Tm.unexpandConst : Unexpander
  | `($_ $n:num) => `(<{ $n:num }>)
  | _ => throw ()

@[app_unexpander Tm.succ]
private def Tm.unexpandSucc : Unexpander
  | stx@`($_ $t) => do
      let succ := mkObjectIdentFrom stx "succ"
      let t' := getTm t
      `(<{ $succ:ident $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.pred]
private def Tm.unexpandPred : Unexpander
  | stx@`($_ $t) => do
      let pred := mkObjectIdentFrom stx "pred"
      let t' := getTm t
      `(<{ $pred:ident $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.mult]
private def Tm.unexpandMult : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm * $t₂':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.tseq]
private def Tm.unexpandTseq : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm ; $t₂':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.ite0]
private def Tm.unexpandIte0 : Unexpander
  | `($_ $c $t $e) => do
      let c' := getTm c
      let t' := getTm t
      let e' := getTm e
      `(<{ if0 $c':stlcTm then $t':stlcTm else $e':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.unit]
private def Tm.unexpandUnit : Unexpander
  | stx => do
      let unit := mkObjectIdentFrom stx "unit"
      let t ← `(stlcTm| $unit:ident)
      `(<{ $t:stlcTm }>)

@[app_unexpander Tm.assign]
private def Tm.unexpandAssign : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm := $t₂':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.ref]
private def Tm.unexpandRef : Unexpander
  | `($_ $t₁) => do
      let t₁' := getTm t₁
      `(<{ ref $t₁':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.deref]
private def Tm.unexpandDeref : Unexpander
  | `($_ $t₁) => do
      let t₁' := getTm t₁
      `(<{ !$t₁':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.loc]
private def Tm.unexpandLoc : Unexpander
  | `($_ $n:num) => `(<{ loc $n:num }>)
  | _ => throw ()

end Delab
```
::::

:::ignore
```lean -show
/-- info: <{ unit }> : Tm -/
#guard_msgs in
#check <{ unit }>

/-- info: <{ Nat }> : Ty -/
#guard_msgs in
#check (Ty.nat : Ty)

/-- info: <{ Ref Nat }> : Ty -/
#guard_msgs in
#check (Ty.ref Ty.nat : Ty)

/-- info: <{ Unit }> : Ty -/
#guard_msgs in
#check (Ty.unit : Ty)

/-- info: <{ unit }> : Tm -/
#guard_msgs in
#check (Tm.unit : Tm)

/-- info: <{ 0 }> : Tm -/
#guard_msgs in
#check (Tm.const 0 : Tm)

example (x : Tm) : (<{ x }> : Tm) = x := by rfl

/-- info: <{ λ X : Nat . X }> : Tm -/
#guard_msgs in
#check <{ λ X : Nat. X }>

/-- info: <{ if0 X then X else X }> : Tm -/
#guard_msgs in
#check <{ if0 X then X else X }>

/-- info: <{ if0 Y X then X else X }> : Tm -/
#guard_msgs in
#check <{ if0 Y X then X else X }>

/-- info: <{ if0 Y X then X else X }> : Tm -/
#guard_msgs in
#check <{ if0 (Y X) then X else X }>

/-- info: <{ X * Y * Z }> : Tm -/
#guard_msgs in
#check <{ X * Y * Z }>

/-- info: <{ succ (pred X) }> : Tm -/
#guard_msgs in
#check <{ succ (pred X) }>

/-- info: <{ succ X Y }> : Tm -/
#guard_msgs in
#check <{ succ X Y }>

/-- info: <{ ref (λ X : Unit . X) }> : Tm -/
#guard_msgs in
#check <{ ref (λ X : Unit . X) }>

/-- info: <{ !X }> : Tm -/
#guard_msgs in
#check <{ !X }>

/-- info: <{ loc 3 }> : Tm -/
#guard_msgs in
#check <{ loc 3 }>
```
:::

::::full
Intuitively:
- `ref t` (formally, `ref t`) allocates a new reference cell
  with the value `τ` and reduces to the location of the newly
  allocated cell;

- `!t` (formally, `deref t`) reduces to the contents of the
  cell referenced by `τ`;

- `t₁ := t₂` (formally, `assign t₁ t₂`) assigns `t₂` to the
  cell referenced by `t₁`; and

- `l` (formally, `loc l`) is a reference to the cell at
  location `l`.  We'll discuss locations later.
::::

::::full
In informal examples, we'll also freely use the extensions
of the STLC developed in the {ref "MoreStlc"}[MoreStlc] chapter; however, to keep
the proofs small, we won't bother formalizing them again here.  (It
would be easy to do so, since there are no very interesting
interactions between those features and references.)
::::

## Typing (Preview)

Informally, the typing rules for allocation, dereferencing, and
assignment look roughly like this:

```display +centered
      Γ ⊢ t₁ ⦂ τ₁
---------------------  (ref)
  Γ ⊢ ref t₁ ⦂ Ref τ₁

      Γ ⊢ t₁ ⦂ Ref τ₁
---------------------  (deref)
     Γ ⊢ !t₁ ⦂ τ₁

      Γ ⊢ t₁ ⦂ Ref τ₂
      Γ ⊢ t₂ ⦂ τ₂
---------------------  (assign)
Γ ⊢ t₁ := t₂ ⦂ Unit
```

The rule for locations will require a bit more machinery, and this
will motivate some changes to the other rules; we'll come back to
this later.

## Values and Substitution

Besides abstractions, numbers, and the unit value, we have one new
type of value: locations.

A location is a concrete pointer value — think of it like an address
in memory. Locations should never be written directly by programmers;
they are used to keep track of the intermediate states of programs
involving references. In particular, the result of a `ref` expression
is a location.

```lean
inductive Tm.IsValue : Tm → Prop :=
  | abs : forall x τ₂ t₁,
      IsValue <{λx : τ₂. t₁}>
  | nat : forall (n : Nat),
      IsValue (.const n)
  | unit :
      IsValue <{ unit }>
  | loc_ : forall (l : Nat),
      IsValue (.loc l)

attribute [StlcRefEval] Tm.IsValue.abs Tm.IsValue.nat Tm.IsValue.unit Tm.IsValue.loc_
```
Extending substitution to handle the new syntax of terms is
straightforward: substituting into a pointer leaves it
unchanged.
```lean
def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  -- pure STLC
  | .var y =>
      if x = y then s else t
  | .abs y τ t₁ =>
      if x = y then t else <{ λ y : τ . [x := s] t₁ }>
  | .app t₁ t₂ =>
      <{ ([x := s] t₁) ([x := s] t₂) }>
  -- numbers
  | .const _ =>
      t
  | .succ t₁ =>
      <{ succ ([x := s] t₁) }>
  | .pred t₁ =>
      <{ pred ([x := s] t₁) }>
  | .mult t₁ t₂ =>
      <{ ([x := s] t₁) * ([x := s] t₂) }>
  | .ite0 t₁ t₂ t₃ =>
      <{
        if0 [x := s] t₁
        then [x := s] t₂
        else [x := s] t₃
      }>
  -- unit
  | .unit => <{ unit }>
  -- references
  | .ref t₁ =>  <{ ref ([x := s] t₁) }>
  | .deref t₁ =>  <{ !([x := s] t₁) }>
  | .loc n => .loc n
  | .assign t₁ t₂ =>
      <{ ([x := s] t₁) := ([x := s] t₂) }>
```

:::details "Notation encoding"
```lean
open Lean PrettyPrinter in
@[app_unexpander subst]
def unexpandSubst : Unexpander := StlcCommon.Delab.unexpandSubst
```
:::

# Pragmatics

## Side Effects and Sequencing

::::full
The fact that we've chosen the result of an assignment
expression to be the trivial value `unit` allows a nice
abbreviation for _sequencing_.  For example, we can write

```
R:=succ(!R); !R
```

as an abbreviation for

```
(λX:Unit, !R) (R:=succ(!R))
```

This has the effect of reducing two expressions in order and
returning the value of the second.  Restricting the type of the
first expression to `Unit` helps the typechecker to catch some
silly errors by permitting us to throw away the first value only
if it is really guaranteed to be trivial.

Notice that, if the second expression is also an assignment, then
the type of the whole sequence will be `Unit`, so we can validly
place it to the left of another `;` to build longer sequences of
assignments:

```
R:=succ(!R); R:=succ(!R); R:=succ(!R); R:=succ(!R); !R
```
::::

::::terse
We can write (for example)

```
R := succ (!R); !R
```

as an abbreviation for

```
(λX:Unit. !R) (r := succ(!R)).
```
::::

::::full
Formally, we introduce sequencing as a _derived form_
`tseq` that expands into an abstraction and an application.
::::

```recall
abbrev Tm.tseq (t₁ t₂ : Tm) : Tm :=
  Tm.app (.abs "X" .unit t₂) t₁
```

::::full
We also give it its own sequencing notation, using semi-colon.
::::

```lean
/-- info: <{ R := succ (!R) ; !R }> : Tm -/
#guard_msgs in
#check Tm.tseq <{R := succ (!R)}> <{!R}>
```

## References and Aliasing

It is important to bear in mind the difference between the
_reference_ that is bound to some variable `r` and the _cell_
in the store that is pointed to by this reference.

If we make a copy of `r`, for example by binding its value to
another variable `s`, what gets copied is only the reference,
not the contents of the cell itself.

For example, after reducing

```display
let R = ref 5 in
let S = R in
S := 82;
(!R)+1
```

the cell referenced by `R` will contain the value `82`, while the
result of the whole expression will be `83`.  The references `R`
and `S` are said to be _aliases_ for the same cell.

The possibility of aliasing can make programs with references
quite tricky to reason about.  For example, the expression

```display
R := 5; R := !S
```

assigns `5` to `R` and then immediately overwrites it with `S`'s
current value; this has exactly the same effect as the single
assignment

```display
R := !S
```
_unless_ we happen to do it in a context where `R` and `S` are
aliases for the same cell!

```display
let R = ref 0 in
let S = R in
R := 5; R := !S
```

## Shared State

Of course, aliasing is also a large part of what makes references
useful.  In particular, it allows us to set up "implicit
communication channels" — shared state — between different parts
of a program.  For example, suppose we define a reference cell and
two functions that manipulate its contents:

```display
let C = ref 0 in
let Incc = λ_:Unit. (C := succ (!C); !C) in
let Decc = λ_:Unit. (C := pred (!C); !C) in
  ...
```

::::full
Note that, since their argument types are `Unit`, the
arguments to the abstractions in the definitions of `Incc` and
`Decc` are not providing any useful information to the bodies of
these functions (using the wildcard `_` as the name of the bound
variable is a reminder of this).  Instead, the purpose of these
abstractions is to "slow down" the execution of the function
bodies.  Since function abstractions are values, the two `let`s are
executed simply by binding these functions to the names `Incc` and
`Decc`, rather than by actually incrementing or decrementing `C`.
Later, each call to one of these functions results in its body
being executed once and performing the appropriate mutation on
`C`.  Such functions are often called _thunks_.

In the context of these declarations, calling `Incc` results in
changes to `C` that can be observed by calling `Decc`.  For
example, if we replace the `...` with `(Incc unit; Incc unit; Decc
unit)`, the result of the whole program will be `1`.
::::

::::terse
The `Unit`-abstractions ("thunks") are used here to prevent
reduction until later.
::::

## Objects

We can go a step further and write a _function_ that creates `C`,
`Incc`, and `Decc`, packages `Incc` and `Decc` together into a
record, and returns this record:
```
Newcounter =
  λ_:Unit.
      let C = ref 0 in
      let Incc = λ_:Unit. (C := succ (!C); !C) in
      let Decc = λ_:Unit. (C := pred (!C); !C) in
      {i=Incc, d=Decc}
```

Now, each time we call `Newcounter`, we get a new record of
functions that share access to the same storage cell `C`.  The
caller of `Newcounter` can't get at this storage cell directly,
but can affect it indirectly by calling the two functions.  In
other words, we've created a simple form of _object_.
```
let C₁ = newcounter unit in
let C₂ = newcounter unit in
// we've allocated two separate storage cells now!
let R₁ = C₁.i unit in
let R₂ = C₂.i unit in
R₂  // yields 1, not 2!
```

:::::full
::::exercise (rating := 1) (name := "store_draw") (manual := true)
Draw (on paper) the contents of the store at the point in
execution where the first two `let`s have finished and the third
one is about to begin.
::::

:::grade
`GRADE_MANUAL 1: store_draw`
:::
:::::

## References to Compound Types

A reference cell need not contain just a number: the primitives
we've defined above allow us to create references to values of any
type, including functions.  For example, we can use references to
functions to give a(n inefficient) implementation of arrays of
numbers as follows.

Write `NatArray` for the type `Ref (Nat→Nat)`.

::::full
Recall the `Equal` function from the {ref "MoreStlc"}[MoreStlc] chapter:
```display
Equal =
  fix
    (λEq:Nat→Nat→Bool.
        λM:Nat. λN:Nat.
          if M=0 then iszero n
          else if N=0 then false
          else Eq (pred m) (pred n))
```
::::

To build a new array, we allocate a reference cell and fill
it with a function that, when given an index, always returns `0`.

```display
Newarray = λ_:Unit. ref (λN:Nat.0)
```

To look up an element of an array, we apply the function
to the desired index.
```display
Lookup = λA:NatArray, λN:Nat. (!A) N
```

The interesting part of the encoding is the `Update` function.  It
takes an array, an index, and a new value to be stored at that index, and
it does its job by creating (and storing in the reference) a new function
that, when it is asked for the value at this very index, returns the new
value that was given to `Update`, while on all other indices it passes the
lookup to the function that was previously stored in the reference.
```
Update = \A:NatArray, \M:Nat, \V:Nat,
  let Oldf = !A in
  A := (λN:Nat. if Equal M N then V else Oldf N);
```

References to values containing other references can also be very
useful, allowing us to define data structures such as mutable
lists and trees.

:::::full
::::exercise (rating := 2) (name := "compact_update") (manual := true)

If we defined `Update` more compactly like this
```display
Update = \A:NatArray, \M:Nat, \V:Nat,
    A := (λN:Nat. if Equal M N then V else (!A) N);
```
would it behave the same?

:::solution
No: calls to `Lookup` with any index other than the one given to
`Update` will now diverge.  The point is that we need to make sure
we look up the value stored in `A` _before_ we overwrite it with
the new function.  Otherwise, when we get around to doing the
lookup, we will find the new function, not the original one.
:::

:::grade
`GRADE_MANUAL 2: compact_update`
:::
::::
:::::

## Null References

::::full
There is one final significant difference between our
references and C-style mutable variables: in C-like languages,
variables holding pointers into the heap may sometimes have the
value `NULL`.  Dereferencing such a "null pointer" is an error,
and results either in a clean exception (Java and C#) or in
arbitrary and possibly insecure behavior (C and relatives like
C++).  Null pointers cause significant trouble in C-like
languages: the fact that any pointer might be null means that any
dereference operation in the program can potentially fail.

Even in ML-like languages, there are sometimes situations where
we may or may not have a valid pointer in our hands.  Fortunately,
there is no need to extend the basic mechanisms of references to
represent such situations: the sum types introduced in the
{ref "MoreStlc"}[MoreStlc] chapter already give us what we need.

First, we can use sums to build an analog of the `option` types
introduced in the Lists chapter of _Logical Foundations_.
Define `Option τ` to be an abbreviation for `Unit + τ`.

Then a "nullable reference to a `τ`" is simply an element of the
type `Option (Ref τ)`.
::::

::::terse
One more difference between our references and C-style
mutable variables: _null pointers_.

- In C, a pointer variable can contain either a valid pointer
into the heap or the special value `NULL`.

- A source of many errors and much tricky reasoning:
  - (any pointer may potentially be "not there")
  - but occasionally useful

- Nullable pointers are easy to implement using references
plus options (which can be built out of disjoint sum types):

```display
Option τ       =  Unit + τ
NullableRef τ  =  Ref (Option τ)
```
::::

## Garbage Collection

A last issue that we should mention before we move on with formalizing
references is storage _de_-allocation.  We have not provided any
primitives for freeing reference cells when they are no longer needed.
Instead, like many modern languages (including OCaml, Haskell, Java,
etc.), we rely on the run-time system to perform _garbage collection_,
automatically identifying and reusing cells that can no longer be
reached by the program.

This is _not_ just a question of taste in language design: it is
extremely difficult to achieve type safety in the presence of an
explicit deallocation operation; only the Rust language has
made this practical, at the cost of significantly constraining the
creation and use of aliases.

One reason for this difficulty is the familiar _dangling reference_ problem:
we allocate a cell holding a number, save a reference to it in
some data structure, use it for a while, then deallocate it and
allocate a new cell holding a boolean, possibly reusing the same
storage.  Now we can have two names for the same storage cell —
one with type `Ref Nat` and the other with type `Ref Bool`.

:::::full
::::exercise (rating := 2) (name := "type_safety_violation") (manual := true)
Show how this can lead to a violation of type safety.

:::solution
Suppose the language provides a primitive `free` that takes a
reference cell as argument and releases its storage so that (say)
the very next allocation of a reference cell will obtain the same
piece of memory.  Then the program
```
    let R = ref 0 in
    let S = R in
    free R;
    let T = ref true in
    T := false;
    succ (!S)
```
will reduce to the stuck term `succ false`.  Note that aliasing
plays a crucial role here in setting up the problem, since it
prevents us from detecting invalid deallocations by simply making
`free r` illegal if the variable `R` appears free in the remainder
of the expression.

This sort of example is easy to mimic in a language like C with
manual memory management (our `ref` constructor corresponds to C's
`malloc`, our `free` to a simplified version of C's `free`).
:::

:::grade
`GRADE_MANUAL 2: type_safety_violation`
:::
::::
:::::

# Operational Semantics

## Locations

::::full
The most subtle aspect of the treatment of references
appears when we consider how to formalize their operational
behavior.  One way to see why is to ask, "What should be the
_values_ of type `Ref τ`?"  The crucial observation that we need
to take into account is that reducing a `ref` operator should
_do_ something — namely, allocate some storage — and the result
of the operation should be a reference to this storage.

What, then, is a reference?

The run-time store in most programming-language implementations is
essentially just a big array of bytes.  The run-time system keeps
track of which parts of this array are currently in use.  When we
need to allocate a new reference cell, we allocate a large enough
segment from the free region of the store (4 bytes for integer
cells, 8 bytes for cells storing `Float`s, etc.), record somewhere
that it is being used, and return the index (typically, a 32- or
64-bit integer) of the start of the newly allocated region.  These
indices are references.

For present purposes, there is no need to be quite so concrete.
We can think of the store as an array of _values_, rather than an
array of bytes, abstracting away from the different sizes of the
run-time representations of different values.  A reference, then,
is simply an index into the store.  (If we like, we can even
abstract away from the fact that these indices are numbers, but
for purposes of formalization in Lean it is convenient to use
numbers.)  We use the word _location_ instead of _reference_ or
_pointer_ to emphasize this abstract quality.

Treating locations abstractly in this way will prevent us from
modeling the _pointer arithmetic_ found in low-level languages
such as C.  This limitation is intentional.  While pointer
arithmetic is occasionally very useful, especially for
implementing low-level services such as garbage collectors, it
cannot be tracked by most type systems: knowing that location `n`
in the store contains a `Float` doesn't tell us anything useful
about the type of location `n+4`.  In C, pointer arithmetic is a
notorious source of type-safety violations.
::::

::::terse
A reference names a location in the _store_ (a.k.a. heap).

What is the store?

  - Concretely: An array of 8-bit bytes, indexed by 32-bit integers.

  - More abstractly: a list or array of values

  - Even more abstractly: a partial function from locations to values.

We'll choose the middle way here: A store is a list of values, and
a location is a natural-number index into this list.
::::

## Stores

::::full
Recall that, in the small-step operational semantics for
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
reference cell is with `ref t₁`, which puts the value of `t₁`
in a new reference cell and reduces to the location of the newly
created reference cell. When reducing such an expression, we can
just add a new reference cell to the end of the list representing
the store.)
::::

::::terse
A store is just a _list_ of values.  (This more concrete
representation will be more convenient for proofs than the
functional representation we used in Imp.) We will use the Greek letter ρ
to represent stores.
::::

```lean
abbrev Store := List Tm
```

We use `ρ[n]` to retrieve the value of the reference
cell at location `n` in the store `ρ`.  Note that we must give a
default value to `nth` in case we try looking up an index which is
too large. (In fact, we never actually do this, but _proving_
that we don't will require a bit of work.)

```lean
open scoped MyGetElem
instance : MyGetElem Store Nat Tm where
  getElem ρ n := ρ.getD n <{unit}>

@[simp]
theorem Store_get_succ_tl (hd : Tm) (tl : Store) (n : Nat) :
  (hd :: tl)[n + 1] = tl[n] := by rfl

@[simp]
theorem Store_get_zero_hd (hd : Tm) (tl : Store) :
  (hd :: tl)[0] = hd := by rfl
```

To update the store, we use the {lean}`List.set` function, which replaces
the contents of a cell at a particular index.

```display
def List.set : (l : List α) → (n : Nat) → (a : α) → List α
  | cons _ as, 0,          b => cons b as
  | cons a as, Nat.succ n, b => cons a (set as n b)
  | nil,       _,          _ => nil
```

As might be expected, we will also need some technical
lemmas; they are straightforward to prove.

```lean
theorem Store_get_set_eq (ρ : Store) (l : Nat) (x : Tm)
  (h : l < ρ.length) :
  (ρ.set l x)[l] = x := by
  induction ρ generalizing l with
  | nil => simp_all
  | cons hd tl ih => cases l <;> simp_all

theorem Store_get_set_neq (l₁ l₂ : Nat) (t : Tm) (ρ : Store) :
  l₁ ≠ l₂ ->
  (ρ.set l₂ t)[l₁] = ρ[l₁] := by
  induction ρ generalizing l₁ l₂ with
  | nil => simp
  | cons hd tl ih => cases l₁ <;> cases l₂ <;> simp_all
```
## Reduction

::::terse
First, we augment existing reduction rules with stores:
```display +centered
            v₂.IsValue
------------------------------------ (appAbs)
(λx:τ₂. t₁) v₂ / ρ ⟶ [x:=v₂] t₁ / ρ

            t₁ / ρ ⟶ t₁' / ρ'
---------------------------------    (app₁)
         t₁ t₂ / ρ ⟶ t₁' t₂ / ρ'

           v₁.IsValue
            t₂ / ρ ⟶ t₂' / ρ'
---------------------------------    (app₂)
         v₁ t₂ / ρ ⟶ v₁ t₂' / ρ'
```

Now we can give the rules for the new constructs:

```display +centered
------------------------------------    (refValue)
     ref v / ρ ⟶ loc ρ.length / ρ,v

        t₁ / ρ ⟶ t₁' / ρ'
------------------------------          (ref)
    ref t₁ / ρ ⟶ ref t₁' / ρ'

      l < ρ.length
--------------------------              (derefLoc)
  !(loc l) / ρ ⟶ ρ[l] / ρ

        t₁ / ρ ⟶ t₁' / ρ'
---------------------------             (deref)
       !t₁ / ρ ⟶ !t₁' / ρ'

             l < ρ.length
--------------------------------------- (assign)
loc l := v / ρ ⟶ unit / List.set ρ l v

        t₁ / ρ ⟶ t₁' / ρ'
--------------------------------        (assign₁)
  t₁ := t₂ / ρ ⟶ t₁' := t₂ / ρ'

        t₂ / ρ ⟶ t₂' / ρ'
--------------------------------        (assign₂)
  v₁ := t₂ / ρ ⟶ v₁ := t₂' / ρ'
```
::::

::::full
Next, we need to extend the operational semantics to take
stores into account.  Since the result of reducing an expression
will in general depend on the contents of the store in which it is
reduced, the evaluation rules should take not just a term but
also a store as argument.  Furthermore, since the reduction of a
term can cause side effects on the store, and these may affect the
reduction of other terms in the future, the reduction rules need
to return a new store.  Thus, the shape of the single-step
reduction relation needs to change from `t ⟶ t'` to `t / ρ ⟶ t' / ρ'`,
where `ρ` and `ρ'` are the starting and ending states of
the store.

To carry through this change, we first need to augment all of our
existing reduction rules with stores:

```display +centered
            value v₂
---------------------------------- (appAbs)
(λx:τ₂,t₁) v₂ / ρ ⟶ [x:=v₂]t₁ / ρ

           t₁ / ρ ⟶ t₁' / ρ'
--------------------------------   (app₁)
        t₁ t₂ / ρ ⟶ t₁' t₂ / ρ'

           value v₁
           t₂ / ρ ⟶ t₂' / ρ'
--------------------------------   (app₂)
        v₁ t₂ / ρ ⟶ v₁ t₂' / ρ'
```

Note that the first rule here returns the store unchanged, since
function application, in itself, has no side effects.  The other
two rules simply propagate side effects from premise to
conclusion.

Now, the result of reducing a `ref` expression will be a fresh
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
First, to reduce a dereferencing expression `!t₁`, we must first
reduce `t₁` until it becomes a value:

```display +centered
 t₁ / ρ ⟶ t₁' / ρ'
-------------------- (deref)
!t₁ / ρ ⟶ !t₁' / ρ'
```
Once `t₁` has finished reducing, we should have an expression of
the form `!l`, where `l` is some location.  (A term that attempts
to dereference any other sort of value, such as a function or
`unit`, is erroneous, as is a term that tries to dereference a
location that is larger than the size ρ.length of the currently
allocated store; the reduction rules simply get stuck in this
case.  The type-safety properties established below assure us
that well-typed terms will never misbehave in this way.)

```display +centered
     l < ρ.length
------------------------ (derefLoc)
!(loc l) / ρ ⟶ ρ[l] / ρ
```

Next, to reduce an assignment expression `t₁:=t₂`, we must first
reduce `t₁` until it becomes a value (a location), and then
reduce `t₂` until it becomes a value (of any sort):

```display +centered
      t₁ / ρ ⟶ t₁' / ρ'
------------------------------ (assign₁)
t₁ := t₂ / ρ ⟶ t₁' := t₂ / ρ'

      t₂ / ρ ⟶ t₂' / ρ'
------------------------------ (assign₂)
v₁ := t₂ / ρ ⟶ v₁ := t₂' / ρ'
```

Once we have finished with `t₁` and `t₂`, we have an expression of
the form `l:=v`, which we execute by updating the store to make
location `l` contain `v`:

```display +centered
         l < ρ.length
-------------------------------- (assign)
loc l := v / ρ ⟶ unit / [l:=v]ρ
```

The notation `[l:=v]ρ` means "the store that maps `l` to `v`
and maps all other locations to the same thing as `ρ`". Note
that the term resulting from this reduction step is just `unit`;
the interesting result is the updated store.

Finally, to reduce an expression of the form `ref t₁`, we first
reduce `t₁` until it becomes a value:

```display +centered
    t₁ / ρ ⟶ t₁' / ρ'
-------------------------- (ref)
ref t₁ / ρ ⟶ ref t₁' / ρ'
```

Then, to reduce the `ref` itself, we choose a fresh location at
the end of the current store — i.e., location `ρ.length` — and yield
a new store that extends `ρ` with the new value `v`.

```display +centered
-------------------------------- (refValue)
ref v / ρ ⟶ loc ρ.length / ρ, v
```

The value resulting from this step is the newly allocated location
itself.  (Formally, `ρ, v` means `ρ.concat v` — i.e., to add
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

Here are the rules again, formally:
::::

::::details "Notation"
```lean
section
set_option hygiene false in
local notation:40
  t:71 " / " ρ:41 " ⟶ " t':71 " / " ρ':41 =>
  Step (t, ρ) (t', ρ')
```
::::

```lean
inductive Step : Tm × Store → Tm × Store → Prop where
  -- pure STLC
  | appAbs {x : String} {τ₂ : Ty} {t₁ v₂ : Tm} {ρ : Store}
      (h : v₂.IsValue) :
      <{(λ x : τ₂ . t₁) v₂}> / ρ ⟶
      <{ [x := v₂] t₁ }> / ρ
  | app₁ {t₁ t₁' t₂ : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{t₁ t₂}> / ρ ⟶ <{t₁' t₂}> / ρ'
  | app₂ {v₁ t₂ t₂' : Tm} {ρ ρ' : Store}
      (h₁ : v₁.IsValue)
      (h₂ : t₂ / ρ ⟶ t₂' / ρ') :
      <{v₁ t₂}> / ρ ⟶ <{v₁ t₂'}> / ρ'
  -- numbers
  | succNat {n : Nat} {ρ : Store} :
      <{ succ ~(Tm.const n) }> / ρ ⟶ Tm.const (n + 1) / ρ
  | succ {t₁ t₁' : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ succ t₁ }> / ρ ⟶ <{ succ t₁' }> / ρ'
  | predConst {n : Nat} {ρ : Store} :
      <{ pred ~(Tm.const n) }> / ρ ⟶ Tm.const (n - 1) / ρ
  | pred {t₁ t₁' : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ pred t₁ }> / ρ ⟶ <{ pred t₁' }> / ρ'
  | multConst {n₁ n₂ : Nat} {ρ : Store} :
      <{ ~(Tm.const n₁) * ~(Tm.const n₂) }> / ρ ⟶
      Tm.const (n₁ * n₂) / ρ
  | mult₁ {t₁ t₁' t₂ : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ t₁ * t₂ }> / ρ ⟶ <{ t₁' * t₂ }> / ρ'
  | mult₂ {v₁ t₂ t₂' : Tm} {ρ ρ' : Store}
      (h₁ : v₁.IsValue)
      (h₂ : t₂ / ρ ⟶ t₂' / ρ') :
      <{ v₁ * t₂ }> / ρ ⟶ <{ v₁ * t₂' }> / ρ'
  | if0Step {t₁ t₁' t₂ t₃ : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ if0 t₁ then t₂ else t₃ }> / ρ ⟶
      <{ if0 t₁' then t₂ else t₃ }> / ρ'
  | if0Zero {t₂ t₃ : Tm} {ρ : Store} :
      <{ if0 0 then t₂ else t₃ }> / ρ ⟶ t₂ / ρ
  | if0Nonzero {n : Nat} {t₂ t₃ : Tm} {ρ : Store} :
      <{ if0 ~(Tm.const (n + 1)) then t₂ else t₃ }> / ρ ⟶
      t₃ / ρ
  -- references
  | refValue {v : Tm} {ρ : Store}
      (h : v.IsValue) :
      <{ ref v }> / ρ ⟶ Tm.loc ρ.length / ρ.concat v
  | ref_ {t₁ t₁' : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ ref t₁ }> / ρ ⟶ <{ ref t₁' }> / ρ'
  | derefLoc {l : Nat} {ρ : Store}
      (h : l < ρ.length) :
      <{ !~(Tm.loc l) }> / ρ ⟶ ρ[l] / ρ
  | deref {t₁ t₁' : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ !t₁ }> / ρ ⟶ <{ !t₁' }> / ρ'
  | assign {v : Tm} {l : Nat} {ρ : Store}
      (h₁ : v.IsValue)
      (h₂ : l < ρ.length) :
      <{ ~(Tm.loc l) := v }> / ρ ⟶ <{ unit }> / ρ.set l v
  | assign₁ {t₁ t₁' t₂ : Tm} {ρ ρ' : Store}
      (h : t₁ / ρ ⟶ t₁' / ρ') :
      <{ t₁ := t₂ }> / ρ ⟶ <{ t₁' := t₂ }> / ρ'
  | assign₂ {v₁ t₂ t₂' : Tm} {ρ ρ' : Store}
      (h₁ : v₁.IsValue)
      (h₂ : t₂ / ρ ⟶ t₂' / ρ') :
      <{ v₁ := t₂ }> / ρ ⟶ <{ v₁ := t₂' }> / ρ'
end

attribute [StlcRefEval] Step.appAbs Step.app₁ Step.app₂
    Step.succ Step.succNat Step.pred Step.predConst
    Step.multConst Step.mult₁ Step.mult₂
    Step.if0Step Step.if0Zero Step.if0Nonzero
    Step.refValue Step.ref_ Step.derefLoc Step.deref Step.assign
    Step.assign₁ Step.assign₂
```

::::details "Notation"
```lean
scoped notation:40
  t:71 " / " ρ:41 " ⟶ " t':71 " / " ρ':41 =>
  Step (t, ρ) (t', ρ')
scoped notation:40
  t:71 " / " ρ:41 " ⟶* " t':71 " / " ρ':41 =>
  Multi Step (t, ρ) (t', ρ')
```
::::

# Typing

The contexts assigning types to free variables are exactly the
same as for the STLC: partial maps from identifiers to types.

```lean
abbrev Context := PartialMap String Ty
```

## Store typings

::::full
Having extended our syntax and reduction rules to accommodate
references, our last job is to write down typing rules for the new
constructs (and, of course, to check that these rules are sound!).

Naturally, the key question is, "What is the type of a location?"
::::
::::terse
Naturally, the key question is, "What is the type of a location?"
::::

::::full
First of all, notice that this question doesn't arise when
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
term `!(loc 1)` in the store `unit, unit`, the result is `unit`;
if we reduce the same term in the store `unit, λX:Unit.X`, the
result is `λX:Unit.X`.  With respect to the former store, the
location `1` has type `Unit`, and with respect to the latter it
has type `Unit→Unit`. This observation leads us immediately to a
first attempt at a typing rule for locations:
::::

::::terse
As a first try, observe that the type of a location is connected to the contents of the store `ρ`.
::::

```display +centered
 Γ ⊢ ρ[l] : τ₁
------------------
Γ ⊢ loc l : Ref τ₁
```

But where does `ρ` come from?

::::full
That is, to find the type of a location `l`, we look up the
current contents of `l` in the store and calculate the type `τ₁`
of the contents.  The type of the location is then `Ref τ₁`.

Having begun in this way, we need to go a little further to reach a
consistent state.  In effect, by making the type of a term depend on
the store, we have changed the typing relation from a three-place
relation (between contexts, terms, and types) to a four-place relation
(between contexts, _stores_, terms, and types).  Since the store is,
intuitively, part of the context in which we calculate the type of a
term, let's write this four-place relation with the store to the left
of the turnstile: `Γ; ρ ⊢ t : τ`.  Our rule for typing
references now has the form
::::

::::terse
We could try adding `ρ` to the judgment: `Γ; ρ ⊢ t : τ`, which gives us this rule:
::::

```display +centered
 Γ; ρ ⊢ ρ[l] : τ₁
---------------------
Γ; ρ ⊢ loc l : Ref τ₁
```

::::terse
But that means the _whole_ store `ρ`, including all dynamically
created values, is needed _during typechecking_.  This does not seem
like something we want.

Worse yet, it doesn't work at all for _cyclic_ stores.
::::

::::full
and all the rest of the typing rules in the system are extended
similarly with stores.  (The other rules do not need to do anything
interesting with their stores — just pass them from premise to
conclusion.)

However, this rule will not quite do.  For one thing, typechecking
is rather inefficient, since calculating the type of a location `l`
involves calculating the type of the current contents `v` of `l`.  If
`l` appears many times in a term `τ`, we will re-calculate the type of
`v` many times in the course of constructing a typing derivation for
`τ`.  Worse, if `v` itself contains locations, then we will have to
recalculate _their_ types each time they appear.  Worse yet, the
proposed typing rule for locations may not allow us to derive
anything at all if the store contains a _cycle_.  For example,
there is no finite typing derivation for the location `0` with respect
to this store:
::::

::::terse
For example, what is the type of location `0` in the following store?
::::

```
λX:Nat. (!(loc 1)) X, λX:Nat. (!(loc 0)) X
```

:::::full
::::exercise (rating := 3) (name := "cyclic_store")
Can you find a term whose reduction will create this particular
cyclic store?

```lean
theorem cyclic_store:
  ∃ t,
    t / [] ⟶*
    <{ unit }> / (<{ λX:Nat. (!(loc 1)) X }> :: <{ λX:Nat. (!(loc 0)) X }> :: []) := by
  solution!
    -- `(λR:τ. t₂) t₁` acts as `let R : τ = t₁ in t₂`
    exists <{
      (λR₀ : Ref (Nat → Nat).
        (λR₁ : Ref (Nat → Nat).
          R₀ := (λX:Nat. (!R₁) X))
        (ref (λX:Nat. (!R₀) X)))
      (ref (λX:Nat. X)) }>
    repeat
      apply Multi.step
      solve_by_elim using StlcRefEval
    apply Multi.refl
```
::::

:::grade
`GRADE_MANUAL 3: cyclic_store`
:::
:::::

::::full
These problems arise from the fact that our proposed
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
can be collected together as a _store typing_ — a finite function
mapping locations to types.

As with the other type systems we've seen, this conservative typing
restriction on allowed updates means that we will rule out as
ill-typed some programs that could reduce perfectly well without
getting stuck.

Just as we did for stores, we will represent a store type simply
as a list of types: the type at index `i` records the type of the
values that we expect to be stored in cell `i`.
::::

::::terse
Instead, we establish an _invariant_ that the type of
value stored in a location never changes.

This _static_ representation of the store contents is called a
_store typing_:
::::

```lean
abbrev StoreTy := List Ty
```

:::terse
Here we represent locations as indices into a _list_ of
types so the type at index `i` is the type of the values stored in
cell `i`.
:::

```lean
open scoped MyGetElem
instance : MyGetElem StoreTy Nat Ty where
  getElem δ n := δ.getD n <{Unit}>

@[simp]
theorem StoreTy_get_succ_tl (hd : Ty) (tl : StoreTy) (n : Nat) :
  (hd :: tl)[n + 1] = tl[n] := by rfl

@[simp]
theorem StoreTy_get_zero_hd (hd : Ty) (tl : StoreTy) :
  (hd :: tl)[0] = hd := by rfl
```

::::full
Suppose we are given a store typing `δ` describing the store
`ρ` in which some term `τ` will be reduced.  Then we can use
`δ` to calculate the type of the result of `τ` without ever
looking directly at `ρ`.  For example, if `δ` is `Unit, Unit→Unit`,
then we can immediately infer that `!(loc 1)` has
type `Unit→Unit`.  More generally, the typing rule for locations
can be reformulated in terms of store typings like this:
::::

::::terse
We can use the store typing `δ` to give a type to
any location `l` like this:
::::

```display +centered
     l < δ.length
-----------------------
Γ; δ ⊢ loc l : Ref δ[l]
```

That is, as long as `l` is a valid location, we can compute the
type of `l` just by looking it up in `δ`.  Typing is again a
four-place relation, but it is parameterized on a store _typing_
rather than a concrete store.  The rest of the typing rules are
analogously augmented with store typings.

## The Typing Relation

::::full
We can now formalize the typing relation for the STLC with
references.  Here, again, are the rules we're adding to the base
STLC (with numbers and `Unit`):
::::

```display +centered
     l < δ.length
-----------------------  (loc)
Γ; δ ⊢ loc l : Ref δ[l]

    Γ; δ ⊢ t₁ : τ₁
----------------------   (ref)
Γ; δ ⊢ ref t₁ : Ref τ₁

  Γ; δ ⊢ t₁ : Ref τ₁
  ------------------     (deref)
  Γ; δ ⊢ !t₁ : τ₁

  Γ; δ ⊢ t₁ : Ref τ₂
    Γ; δ ⊢ t₂ : τ₂
----------------------   (assign)
Γ; δ ⊢ t₁ := t₂ : Unit
```

```lean
inductive HasType (δ : StoreTy) : Context → Tm → Ty → Prop where
  -- pure STLC
  | var {Γ : Context} {x : String} {τ₁ : Ty}
      (h : Γ[x] = some τ₁) :
      <{ Γ / δ ⊢ ~(Tm.var x) ⦂ τ₁ }>
  | abs {Γ : Context} {x : String} {τ₁ τ₂ : Ty} {t₁ : Tm}
      (h : <{ x ↦ τ₂ ; Γ / δ ⊢ t₁ ⦂ τ₁ }>) :
      <{ Γ / δ ⊢ λ x : τ₂ . t₁ ⦂ τ₂ → τ₁ }>
  | app {Γ : Context} {τ₁ τ₂ : Ty} {t₁ t₂ : Tm}
      (h₁ : <{ Γ / δ ⊢ t₁ ⦂ τ₂ → τ₁ }>)
      (h₂ : <{ Γ / δ ⊢ t₂ ⦂ τ₂ }>) :
      <{ Γ / δ ⊢ t₁ t₂ ⦂ τ₁ }>
  -- numbers
  | const {Γ : Context} {n : Nat} :
      <{ Γ / δ ⊢ ~(Tm.const n) ⦂ Nat }>
  | succ {Γ : Context} {t₁ : Tm}
      (h : <{ Γ / δ ⊢ t₁ ⦂ Nat }>) :
      <{ Γ / δ ⊢ succ t₁ ⦂ Nat }>
  | pred {Γ : Context} {t₁ : Tm}
      (h : <{ Γ / δ ⊢ t₁ ⦂ Nat }>) :
      <{ Γ / δ ⊢ pred t₁ ⦂ Nat }>
  | mult {Γ : Context} {t₁ t₂ : Tm}
      (h₁ : <{ Γ / δ ⊢ t₁ ⦂ Nat }>)
      (h₂ : <{ Γ / δ ⊢ t₂ ⦂ Nat }>) :
      <{ Γ / δ ⊢ t₁ * t₂ ⦂ Nat }>
  | ite0 {Γ : Context} {t₁ t₂ t₃ : Tm} {τ : Ty}
      (h₁ : <{ Γ / δ ⊢ t₁ ⦂ Nat }>)
      (h₂ : <{ Γ / δ ⊢ t₂ ⦂ τ }>)
      (h₃ : <{ Γ / δ ⊢ t₃ ⦂ τ }>) :
      <{ Γ / δ ⊢ if0 t₁ then t₂ else t₃ ⦂ τ }>
  -- unit
  | unit {Γ : Context} :
      <{ Γ / δ ⊢ unit ⦂ Unit }>
  -- references
  | loc_ {Γ : Context} {l : Nat}
      (h : l < δ.length) :
      <{ Γ / δ ⊢ ~(Tm.loc l) ⦂ Ref ~(δ[l]) }>
  | ref_ {Γ : Context} {t₁ : Tm} {τ₁ : Ty}
      (h : <{ Γ / δ ⊢ t₁ ⦂ τ₁ }>) :
      <{ Γ / δ ⊢ ref t₁ ⦂ Ref τ₁ }>
  | deref {Γ : Context} {t₁ : Tm} {τ₁ : Ty}
      (h : <{ Γ / δ ⊢ t₁ ⦂ Ref τ₁ }>) :
      <{ Γ / δ ⊢ !t₁ ⦂ τ₁ }>
  | assign {Γ : Context} {t₁ t₂ : Tm} {τ₂ : Ty}
      (h₁ : <{ Γ / δ ⊢ t₁ ⦂ Ref τ₂ }>)
      (h₂ : <{ Γ / δ ⊢ t₂ ⦂ τ₂ }>) :
      <{ Γ / δ ⊢ t₁ := t₂ ⦂ Unit }>

attribute [StlcRefTyping] HasType.var HasType.abs HasType.app
    HasType.const HasType.succ HasType.pred HasType.mult
    HasType.ite0 HasType.unit
    HasType.loc_ HasType.ref_ HasType.deref HasType.assign
```

:::details "Notation encoding"
```lean
open Lean PrettyPrinter StlcCommon.Delab in
@[app_unexpander HasType]
def HasType.unexpand : Unexpander
  | `($_ $δ $Γ $t $T) => do
      let Γ' ← unexpandCtx Γ
      `(<{ $Γ':stlcCtx / $δ ⊢ $(getTm t):stlcTm ⦂ $(getTy T):stlcTy }>)
  | _ => throw ()
```
:::

:::ignore
```lean -show
/-- info: <{ ∅ / [] ⊢ ref 3 ⦂ Ref Nat }> : Prop -/
#guard_msgs in
#check <{ ∅ / [] ⊢ ref 3 ⦂ Ref Nat }>

/-- info: <{ X ↦ Ref Nat ; ∅ / (List.concat δ (<{ Nat }>)) ⊢ !X ⦂ Nat }> : Prop -/
#guard_msgs in
variable (δ : StoreTy) in
#check <{ X ↦ Ref Nat ; ∅ / (δ.concat <{ Nat }>) ⊢ !X ⦂ Nat }>

/-- error: typing judgments need a store typing: write `Γ / δ ⊢ t ⦂ τ` -/
#guard_msgs in
#check <{ ∅ ⊢ unit ⦂ Unit }>

example : <{ ∅ / [<{ Nat }>] ⊢ !(loc 0) ⦂ Nat }> := by
  apply_rules using StlcRefTyping
  simp

example : <{ ∅ / [] ⊢ (λ X : Ref Nat . X := 2) (ref 1) ⦂ Unit }> := by
  apply_rules using StlcRefTyping
```
:::

::::full
Of course, these typing rules will accurately predict the results
of reduction only if the concrete store used during reduction
actually conforms to the store typing that we assume for purposes
of typechecking.  This proviso exactly parallels the situation
with free variables in the basic STLC: the substitution lemma
promises that, if `Γ / δ ⊢ t : T`, then we can replace the free
variables in `τ` with values of the types listed in `Γ` to
obtain a closed term of type `τ`, which, by the type preservation
theorem will reduce to a final result of type `τ` if it yields
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
the type preservation theorem below.
::::

# Properties

::::full
Our final task is to check that standard type safety
properties continue to hold for the STLC with references.  The
progress theorem ("well-typed terms are not stuck") can be stated
and proved almost as for the STLC; we just need to add a few
straightforward cases to the proof to deal with the new
constructs.  The preservation theorem is a bit more interesting,
so let's look at it first.
::::

::::terse
Standard theorems...
- Progress — pretty much same as always
- Preservation — needs to be stated more carefully!
::::

## Well-Typed Stores

::::full
Since we have extended both the reduction relation (with
initial and final stores) and the typing relation (with a store
typing), we need to change the statement of preservation to
include these parameters.  But clearly we cannot just add stores
and store typings without saying anything about how they are
related — i.e., this is wrong:
::::

::::terse
The evaluation and typing relations take more parameters
now, so at a minimum we have to add these to the statement of
preservation...
::::

```lean +error
theorem preservation_wrong (δ : StoreTy) (τ : Ty) (t t' : Tm) (ρ ρ' : Store) :
    <{ ∅ / δ ⊢ t ⦂ τ }> →
    t / ρ ⟶ t' / ρ' →
    <{ ∅ / δ ⊢ t' ⦂ τ }> := by
```

::::full
If we typecheck with respect to some set of assumptions
about the types of the values in the store and then reduce with
respect to a store that violates these assumptions, the result
will be disaster.  We say that a store `ρ` is _well typed_ with
respect to a store typing `δ` if the term at each location `l` in
`ρ` has the type at location `l` in `δ`.  Since only closed
terms ever get stored in locations (why?), it suffices to type
them in the empty context. The following definition of
`StoreWellTyped` formalizes this:
::::

::::terse
Obviously wrong: no relation between assumed store typing
and provided store!

We need a way of saying "this store satisfies the
assumptions of that store typing"...
::::

```lean
def StoreWellTyped (δ:StoreTy) (ρ:Store) :=
  δ.length = ρ.length ∧
  (∀ (l : Nat), l < ρ.length → <{ ∅ / δ ⊢ ~(ρ[l]) ⦂ ~(δ[l]) }>)
```

Informally, we will write `δ ⊢ ρ` for `StoreWellTyped δ ρ`.

```lean
scoped notation:40 δ:41 " ⊢ " ρ:41 => StoreWellTyped δ ρ
```

Intuitively, a store `ρ` is consistent with a store typing
`δ` if every value in the store has the type predicted by the
store typing.  The only subtle point is the fact that, when typing
the values in the store, we supply the very same store typing to
the typing relation.  This allows us to type circular stores like
the one we saw above.

:::::full
::::exercise (rating := 3) (name := "store_not_unique")
Can you find a store `ρ`, and two
different store typings `δ₁` and `δ₂` such that both
`δ₁ ⊢ ρ` and `δ₂ ⊢ ρ`?

:::solution
Let `ρ` be a store with a single location `0`, such that
  `ρ`  =  `λX:Unit. (!(loc 0))(X)`.
Then `ρ` is well typed with
respect to both of the following store typings:
  δ₁  =  `Unit → Unit`
  δ₂  =  `Unit → (Unit→Unit)`.
In fact, it is well typed with respect to any store typing of the form
  δ   =  `Unit → τ`
for any type `τ`.
:::

```lean
theorem store_not_unique:
  exists ρ, exists δ₁, exists δ₂,
    δ₁ ⊢ ρ ∧ δ₂ ⊢ ρ ∧ δ₁ ≠ δ₂ := by
  solution!
    exists (<{ λX:Unit. (!(loc 0)) X }> :: []);
    exists (<{ Unit → Unit }> :: []);
    exists (<{ Unit → Nat }> :: []);
    constructor
    · simp [StoreWellTyped]
      apply_rules using StlcRefTyping
      simp
    · constructor
      · simp [StoreWellTyped]
        apply_rules using StlcRefTyping
        simp
      · simp
```
::::

:::grade
`GRADE_MANUAL 3: store_not_unique`
:::
:::::

We can now state something closer to the desired preservation property:

```lean +error
theorem preservation_less_wrong (δ : StoreTy) (τ : Ty) (t t' : Tm) (ρ ρ' : Store) :
  <{ ∅ / δ ⊢ t ⦂ τ }> →
  t / ρ ⟶ t' / ρ' →
  δ ⊢ ρ →
  <{ ∅ / δ ⊢ t' ⦂ τ }> := by
```

::::full
This statement is fine for all of the reduction rules except
the allocation rule `refValue`.  The problem is that this rule
yields a store with a larger domain than the initial store, which
falsifies the conclusion of the above statement: if `ρ'` includes
a binding for a fresh location `l`, then `l` cannot be in the
domain of `δ`, and it will not be the case that `t'` (which
definitely mentions `l`) is typable under `δ`.
::::

::::terse
This works... for all but _one_ of the reduction rules! (Which?)
::::

::::terse
The `refValue` rule is the problem
```display +centered
-------------------------- (refValue)
ref v / ρ ⟶ loc |ρ| / ρ,v
```

It allocates a fresh location `l` and adds it to the store, but
the store typing `δ` doesn't know about `l`, so `t'` won't be
typeable under `δ`.

For example, the term `ref 5` is typeable in the ∅ context and
∅ store typing, but it steps to `loc 0`, which is not typeable
with an ∅ store typing.
::::

## Extending Store Typings

::::full
Evidently, since the store can increase in size during
reduction, we need to allow the store _typing_ to grow during
reduction as well. This motivates the following definition.  We
say that the store type `δ'` _extends_ `δ` if `δ'` is just `δ`
with some new types added to the end.
::::

::::terse
Intuition: Since the store can grow during reduction, we
need to let the store _typing_ grow too...
::::

```lean
inductive Extends : StoreTy → StoreTy → Prop where
  | nil (δ' : StoreTy) : Extends δ' []
  | cons (τ : Ty) {δ' δ : StoreTy} (h : Extends δ' δ) :
      Extends (τ::δ') (τ::δ)

attribute [StlcRefTyping] Extends.nil Extends.cons
```

For example, the store typing `[Nat]` with a single location of
type `Nat` extends the empty store typing.

We'll need a few technical lemmas about extended contexts.
First, looking up a type in an extended store typing yields the
same result as in the original:

```lean
theorem extends_lookup {l : Nat} {δ δ' : StoreTy}
  (h₁ : l < δ.length)
  (h₂ : Extends δ' δ) :
  δ'[l] = δ[l] := by

    induction δ generalizing l δ' with
    | nil => simp_all
    | cons hd tl ih =>
      cases δ' with
      | nil => inversion h₂
      | cons hd' tl' =>
        inversion h₂
        cases l with
        | zero => rfl
        | succ l =>
          simp only [StoreTy_get_succ_tl]; apply ih
          · simp_all
          · assumption
```

Next, if `δ'` extends `δ`, the length of `δ'` is at least that of `δ`.

```lean
theorem length_extends {l : Nat} {δ δ' : StoreTy}
  (h₁ : l < δ.length)
  (h₂ : Extends δ' δ) :
  l < δ'.length := by
    induction h₂ generalizing l with
    | nil => simp_all
    | cons τ h ih =>
        simp only [List.length_cons]
        cases l with
        | zero => lia
        | succ l' =>
          apply Nat.succ_lt_succ; apply ih
          simp_all
```

Finally, `δ ++ δ'` extends `δ`, and `Extends` is reflexive.

```lean
theorem extends_app (δ δ' : StoreTy) : Extends (δ ++ δ') δ := by
  induction δ generalizing δ' <;> apply_rules using StlcRefTyping

theorem extends_refl (δ : StoreTy) : Extends δ δ := by
  induction δ <;> apply_rules using StlcRefTyping
```

## Preservation, Finally

We can now give the final, correct statement of the type
preservation property:

```lean
def preservation_theorem {δ : StoreTy} {t t' : Tm} {τ : Ty} {ρ ρ' : Store} :=
  (hTy : <{ ∅ / δ ⊢ t ⦂ τ }>) →
  (hStoreTy : δ ⊢ ρ) →
  (hEval : t / ρ ⟶ t' / ρ') →
    ∃ δ', Extends δ' δ ∧ (<{ ∅ / δ' ⊢ t' ⦂ τ }>) ∧ (δ' ⊢ ρ')
```

::::full
Note that the preservation theorem merely asserts that there
is _some_ store typing `δ'` extending `δ` (i.e., agreeing with
`δ` on the values of all the old locations) such that the new
term `t'` is well typed with respect to `δ'`; it does not tell us
exactly what `δ'` is.  It is intuitively clear, of course, that
`δ'` is either `δ` or else exactly `δ ++ [τ₁]`, where `τ₁`
is the type of the value `v₁` in the extended store `ρ ++ [v₁]`,
but stating this explicitly would complicate the
statement of the theorem without making it any more useful: the
weaker version above is already in the right form (because its
conclusion implies its hypothesis) to "turn the crank" repeatedly
and conclude that every _sequence_ of reduction steps preserves
well-typedness.  Combining this with the progress property, we
obtain the usual guarantee that "well-typed programs never go
wrong."

In order to prove this, we'll need a few lemmas, as usual.
::::

::::terse
This gives us just what we need to "turn the
crank" when applying the theorem to multi-step reduction
sequences.
::::

### Substitution Lemma

::::terse
To prove preservation, we need to re-develop the rest of
the machinery that we saw for the pure STLC (plus a couple of new
things about store typings and extension)...
::::

::::full
First, we need an easy extension of the standard substitution
lemma, along with the same machinery about context invariance that
we used in the proof of the substitution lemma for the STLC.
::::

```lean
theorem weakening {Γ Γ' : Context} {δ : StoreTy} {t : Tm} {τ: Ty}
    (hi : Γ ⊆ Γ')
    (ht : <{ Γ / δ ⊢ t ⦂ τ }>) :
     <{ Γ' / δ ⊢ t ⦂ τ }> := by
  induction ht generalizing Γ' with (apply_rules [PartialMap.update_subset] using StlcRefTyping)
```

```lean
theorem weakening_empty {Γ : Context} {δ : StoreTy} {t : Tm} {τ: Ty}
    (ht :<{ ∅ / δ ⊢ t ⦂ τ }>) :
    <{ Γ / δ ⊢ t ⦂ τ }> := by
  apply weakening (Γ := ∅)
  · intros x b contra
    contradiction
  · assumption
```

```lean
theorem substitution_preserves_typing (Γ : Context) (δ : StoreTy) (x : String)
    (τ₁ : Ty) (t v : Tm) (τ : Ty)
    (ht : <{ x ↦ τ₁ ; Γ / δ⊢ t ⦂ τ }>)
    (hv : <{ ∅ / δ ⊢ v ⦂ τ₁ }>) :
    <{ Γ / δ ⊢ [x := v] t ⦂ τ }> := by
  induction t generalizing Γ τ with (
    rw [subst]; try (inversion ht; apply_rules using StlcRefTyping; done))
    | var y =>
        inversion ht with | _ h =>
        by_cases h₁ : x = y
        · subst h₁; simp at h; subst h;
          apply weakening_empty at hv
          simp; assumption
        · rw [PartialMap.update_neq] at h <;> simp_all
          apply_rules using StlcRefTyping
    | abs y _ _ ih =>
        inversion ht with | _ h =>
        by_cases h₁ : x = y
        · simp_all [PartialMap.update_shadow]; apply_rules using StlcRefTyping
        · rw [PartialMap.update_permute] at h
          · simp_all; apply_rules using StlcRefTyping
          · lia
```

### Assignment Preserves Store Typing

Next, we must show that replacing the contents of a cell in the
store with a new value of appropriate type does not change the
overall type of the store.  (This is needed for the `assign`
rule.)

```lean
theorem assign_pres_store_typing {δ : StoreTy} {ρ : Store} {l : Nat} {t : Tm}
  (hLen : l < ρ.length)
  (hStoreTy : δ ⊢ ρ)
  (hTy : <{ ∅ / δ ⊢ t ⦂ ~(δ[l]) }>) :
  δ ⊢ ρ.set l t := by
    have ⟨h₁, h₂⟩ := hStoreTy
    constructor
    · simp_all [List.length_set]
    · intro l' hLen'
      by_cases h₁ : l' = l
      · subst_vars
        rw [Store_get_set_eq] <;> assumption
      · rw [Store_get_set_neq] <;> try assumption
        apply h₂
        simp_all [List.length_set]
```

### Weakening for Stores

Finally, we need a lemma on store typings, stating that, if a
store typing is extended with a new location, the extended one
still allows us to assign the same types to the same terms as the
original.

```lean
theorem store_weakening {Γ : Context} {δ δ' : StoreTy} {t : Tm} {τ : Ty}
  (hExt : Extends δ' δ)
  (hTy : <{ Γ / δ ⊢ t ⦂ τ }>) :
  <{ Γ / δ' ⊢ t ⦂ τ }> := by
    induction hTy with (try (apply_rules using StlcRefTyping; done))
    | loc_ h =>
        rw [←extends_lookup] <;> try assumption
        apply HasType.loc_
        apply length_extends <;> assumption
```

We can use the `store_weakening` lemma to prove that if a store is
well typed with respect to a store typing, then the store extended
with a new term `τ` will still be well typed with respect to the
store typing extended with `τ`'s type.

```lean
theorem store_well_typed_app {δ : StoreTy} {ρ : Store} {t₁ : Tm} {τ₁ : Ty}
  (hStoreTy : δ ⊢ ρ)
  (hTy : <{ ∅ / δ ⊢ t₁ ⦂ τ₁ }>) :
  (δ.concat τ₁) ⊢ (ρ.concat t₁) := by
    have ⟨h₁, h₂⟩ := hStoreTy
    simp_all only [List.concat_eq_append]
    constructor
    · simp_all
    · simp_all only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      intro l hl
      inversion hl with
      | refl =>
          apply store_weakening <;> try assumption
          apply extends_app
          simp_all [MyGetElem.getElem]
      | step hl =>
          apply store_weakening <;> try assumption
          · apply extends_app
          · have hl' : l < ρ.length := by lia
            simp_all [MyGetElem.getElem, List.getElem?_append_left]
```

### Preservation!

Now that we've got everything set up right, the proof of
preservation is actually quite straightforward:

```lean
theorem preservation {δ : StoreTy} {t t' : Tm} {τ : Ty} {ρ ρ' : Store}
  (hTy : <{ ∅ / δ ⊢ t ⦂ τ }>)
  (hStoreTy : δ ⊢ ρ)
  (hEval : t / ρ ⟶ t' / ρ') :
    ∃ δ', Extends δ' δ ∧ (<{ ∅ / δ' ⊢ t' ⦂ τ }>) ∧ (δ' ⊢ ρ') := by

    generalize heq : (∅ : Context) = Γ at hTy
    -- discharge the goals where `t` doesn't step
    induction hTy generalizing t' with (subst_vars; try (inversion hEval; done))
    | app h₁ h₂ ih₁ ih₂ =>
      inversion hEval with
      | appAbs =>
        inversion h₁ with | abs h =>
        exists δ; constructor
        apply extends_refl; constructor
        apply_rules [substitution_preserves_typing, extends_refl] using StlcRefTyping
        assumption
      | app₁ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₁ hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
      | app₂ _ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₂ hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
    | succ _ ih =>
      inversion hEval with
      | succNat =>
        exists δ; constructor
        apply extends_refl; constructor
        constructor
        assumption
      | succ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
    | pred _ ih =>
      inversion hEval with
      | predConst =>
        exists δ; constructor
        apply extends_refl; constructor
        constructor
        assumption
      | pred hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
    | mult h₁ h₂ ih₁ ih₂ =>
      inversion hEval with
      | multConst =>
        exists δ; constructor
        apply extends_refl; constructor
        constructor
        assumption
      | mult₁ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₁ hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
      | mult₂ _ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₂ hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
    | ite0 _ h₂ h₃ ih₁ _ _ =>
      inversion hEval with
      | if0Step hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₁ hs rfl
        exists δ'; constructor
        assumption; constructor
        constructor <;> solve_by_elim [store_weakening] using StlcRefTyping
        assumption
      | if0Zero =>
        exists δ; constructor
        apply extends_refl; constructor <;> assumption
      | if0Nonzero =>
        exists δ; constructor
        apply extends_refl; constructor <;> assumption
    | @ref_ _ _ τ₁ h ih =>
      inversion hEval with
      | refValue =>
        exists δ.concat τ₁; constructor
        · rw [List.concat_eq_append]; apply extends_app
        · constructor
          · have h : <{Ref τ₁}> = <{Ref ~((δ.concat τ₁)[ρ.length])}> := by
              simp_all [StoreWellTyped, MyGetElem.getElem]
            rw [h]
            constructor
            simp [StoreWellTyped] at hStoreTy ⊢; lia
          · apply store_well_typed_app <;> assumption
      | ref_ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
    | deref h ih =>
      inversion hEval with
      | derefLoc hl =>
        inversion h
        exists δ; constructor
        apply extends_refl; constructor
        have ⟨h₁, h₂⟩ := hStoreTy
        apply h₂ <;> assumption
        assumption
      | deref hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
    | assign h₁ h₂ ih₁ ih₂ =>
      inversion hEval with
      | assign _ hl =>
        inversion h₁
        exists δ; constructor
        apply extends_refl; constructor
        constructor
        apply assign_pres_store_typing <;> assumption
      | assign₁ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₁ hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
      | assign₂ _ hs =>
        have ⟨δ', hExt, hTy', hStoreTy'⟩ := ih₂ hs rfl
        exists δ'; constructor
        assumption; constructor
        solve_by_elim [store_weakening] using StlcRefTyping
        assumption
```

::::full
This proof is pretty long, and many of the cases repeat themselves. With judicious
use of automation, we can make it much shorter:

```lean
theorem preservation_shorter {δ : StoreTy} {t t' : Tm} {τ : Ty} {ρ ρ' : Store}
  (hTy : <{ ∅ / δ ⊢ t ⦂ τ }>)
  (hStoreTy : δ ⊢ ρ)
  (hEval : t / ρ ⟶ t' / ρ') :
    ∃ δ', Extends δ' δ ∧ (<{ ∅ / δ' ⊢ t' ⦂ τ }>) ∧ (δ' ⊢ ρ') := by

      generalize heq : (∅ : Context) = Γ at hTy
      induction hTy generalizing t' with (
        subst_vars <;>
        -- discharge the goals where `t` doesn't step
        inversion hEval <;>
        -- handle the congruence cases where the store typing grows,
        -- but in an uninteresting way
        (try
          -- we want to apply our inductive hypotheses, but we can't name
          -- them in our automation. Instead, we restate the result that
          -- we want and use `solve_by_elim` to figure out how to prove
          -- this result using the unnamed `ih`
          obtain ⟨δ', hExt, hTy', hStoreTy'⟩ : ∃ δ', Extends δ' δ ∧ _ ∧ (δ' ⊢ ρ') := by
            solve_by_elim
          exists δ'; constructor
          assumption; constructor
          constructor <;> solve_by_elim [store_weakening] using StlcRefTyping
          assumption) <;>
        -- handle the cases where the store doesn't grow
        (try
          exists δ; constructor
          apply extends_refl; constructor
          solve_by_elim using StlcRefTyping
          assumption))
    | app h₁ h₂ ih₁ ih₂ =>
      inversion h₁
      exists δ; constructor
      apply extends_refl; constructor
      apply_rules [substitution_preserves_typing] using StlcRefTyping
      assumption
    | @ref_ _ _ τ₁ =>
      exists δ.concat τ₁; constructor
      · rw [List.concat_eq_append]; apply extends_app
      · constructor
        · have h : <{Ref τ₁}> = <{Ref ~((δ.concat τ₁)[ρ.length])}> := by
            simp_all [StoreWellTyped, MyGetElem.getElem]
          rw [h]
          constructor
          simp [StoreWellTyped] at hStoreTy ⊢; lia
        · apply store_well_typed_app <;> assumption
    | deref h =>
      inversion h
      exists δ; constructor
      apply extends_refl; constructor
      have ⟨_, h₂⟩ := hStoreTy; apply h₂; assumption
      assumption
    | assign h₁ =>
      inversion h₁
      exists δ; constructor
      apply extends_refl; constructor
      constructor
      apply assign_pres_store_typing <;> assumption
```

This shorter proof only handles the interesting cases (`app`, `deref`, `assign`, and `ref`)
manually, and solves all the mechanical ones automatically.
::::

:::::full
::::exercise (rating := 3) (name := "preservation_informal") (manual := true)
Write a careful informal proof of the preservation theorem,
concentrating on the `app`, `deref`, `assign`, and `ref`
cases.

:::solution
_Proof_: By induction on a derivation of `∅ / [] ⊢ t : τ`.

- If the last rule in the derivation is `app`, then `t = t₁ t₂`
  for some `t₁` and `t₂` and `τ = τ₁₂`, with `∅ / δ ⊢ t₁ : τ₁₁ → τ₁₂`
  and `∅ / δ ⊢ t₂ : τ₁₁`.  There are three cases to
  consider, one for each rule that could have been used to show
  that `t₁ t₂` takes a step to `t'`.

    - Suppose `t₁ t₂` takes a step by `app₁`, with `t₁`
      stepping to `t₁'` and new store `ρ'`.  Then by the IH there
      is some store typing `δ'` such that `δ'` extends `δ`,
      `ρ'` is well typed with respect to `δ'`, and `∅ / δ' ⊢ t₁' : τ₁₁ → τ₁₂`.
      We also know `∅ / δ' ⊢ t₂ : τ₁₁`
      by the `store_weakening` lemma.  Hence, `∅ / δ' ⊢ t₁' t₂` by `app`.

    - The `app₂` case is similar.

    - Suppose `t₁ t₂` takes a step by `appAbs`.  Then `t₁ = λx:τ₁₁. t₁₂`
      and `t₁ t₂` steps to `[x:=t₂] t₁₂`; the
      desired result now follows from the substitution lemma,
      taking `δ' = δ`.

- If the last rule in the derivation is `ref`, then `t = ref t₁`
  for some `t₁` and `∅ / δ ⊢ t₁ : τ₁` for some `τ₁`, with `τ = Ref τ₁`.
  There are two cases to consider, one for each rule
  that could have been used to show that `ref t₁` takes a step to
  `t'`.

    - Suppose `ref t₁` takes a step by `ref`, with `t₁`
      stepping to `t₁'` and new store `ρ'`.  Then by the IH there
      is some store typing `δ'` such that `δ'` extends `δ`,
      `ρ'` is well typed with respect to `δ'`, and `∅ / δ' ⊢ t₁' : τ₁`.
      Hence, `∅ / δ' ⊢ ref t₁' : Ref τ₁` by `ref`.

    - Suppose `ref t₁` takes a step by `refValue`.  Then `t₁`
      is a value, `ρ' = ρ.concat t₁`, and `t'` is the length of
      `ρ` - i.e., the location of `t₁` in `ρ'`.  If we choose
      `δ' = δ.concat τ₁`, we obtain
          - `δ'` extends `δ` by construction
          - `ρ'` is well typed with respect to `δ'` because `ρ`
            is well typed with respect to `δ` and the last
            element, `t₁`, has type `τ₁` under `δ`,
            hence also under `δ'` by the store
            weakening lemma
          - `∅ / δ' ⊢ l : Ref τ₁` by `loc` as required.

- If the last rule in the derivation is `deref`, then `t = !t₁`
  for some `t₁` and `∅ / δ ⊢ t₁ : Ref τ`.  There are two
  cases to consider, one for each rule that could have been used
  to show that `!t₁` takes a step to `t'`.

    - Suppose `!t₁` takes a step by `deref`, with `t₁` stepping
      to `t₁'` and new store `ρ'`.  Then by the IH there is some
      store typing `δ'` such that `δ'` extends `δ`, `ρ'` is
      well typed with respect to `δ'`, and `∅ / δ' ⊢ t₁' : Ref τ`.
      Hence, `∅ / δ' ⊢ !t₁' : τ` by `deref`.

    - Suppose `ref t₁` takes a step by `derefLoc`.  Then `t₁`
      is some location `l` and `t'` is the contents of `ρ` at
      location `l`.  Moreover, the typing rule used to derive
      `∅ / δ ⊢ l : Ref τ` must be `loc`, so the contents of
      `δ` at location `l` is `τ`.  Now, since `ρ` is well typed
      with respect to `δ`, we know that `∅ / δ ⊢ t' : τ`, as
      required.

- If the last rule in the derivation is `assign`, then `t = t₁ := t₂`
  for some `t₁` and `t₂`, with `∅ / δ ⊢ t₁ : Ref τ₂`
  and `∅ / δ ⊢ t₂ : τ₂` for some `τ₂`; moreover, `τ = Unit`.
  There are now three cases to consider, one for each rule that
  could have been used to show that `t₁ := t₂` takes a step to
  `t'`.

    - The cases where `t₁ := t₂` takes a step by either
      `assign₁` or `assign₂` are similar to the congruence
      rule cases above.

    - Suppose `t₁ := t₂` takes a step by `assign`.  Then `t₁`
      is some location `l`, `t₂` is some value, `t'` is `unit`,
      and `ρ'` is formed from `ρ` by updating the contents of
      location `l` with `t₂`.

      Moreover, the typing rule used to derive `∅ / δ ⊢ l : Ref τ₂`
      must be `loc`, so the contents of `δ` at location
      `l` is `τ₂`.  Now, `∅ / δ ⊢ unit : Unit` by `unit`.
      Moreover, since `ρ` is well typed with respect to `δ` and
      we know `∅ / δ ⊢ t₂ : τ₂`, we know that `ρ'` is well
      typed with respect to `δ` by lemma
      `assign_pres_store_typing`.  So we can take `δ' = δ` and
      finish this case.

    - (Other cases elided...)

_QED_.
:::

:::grade
`GRADE_MANUAL 3: preservation_informal`
:::

::::
:::::

## Progress

As we've said, progress for this system is pretty easy to prove;
the proof is very similar to the proof of progress for the STLC,
with a few new cases for the new syntactic constructs.

```lean
theorem progress (δ : StoreTy) (t : Tm) (τ : Ty) (ρ : Store)
  (hTy : <{ ∅ / δ ⊢ t ⦂ τ }>)
  (hStoreTy : δ ⊢ ρ) :
  (t.IsValue ∨ ∃ t' ρ', t / ρ ⟶ t' / ρ') := by
    have ⟨hLen, _⟩ := hStoreTy
    generalize heq : (∅ : Context) = Γ at hTy
    induction hTy with (subst_vars; first
      | contradiction
      -- discharge cases where `t` is obviously a value
      | try (left; constructor; done))
    | app h₁ _ ih₁ ih₂ =>
      right; cases ih₁ (by rfl) with
      -- t₁ is a value
      | inl hv₁ =>
        cases ih₂ (by rfl) with
        -- t₂ is a value
        | inl hv₂ =>
          cases hv₁ <;> try contradiction
          apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
        -- t₂ steps
        | inr hs₂ =>
          have ⟨t₂', ρ', hs₂⟩ := hs₂
          apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
      -- t₁ steps
      | inr hs₁ =>
        have ⟨t₁', ρ', hs₁⟩ := hs₁
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | succ h ih
    | pred h ih =>
      -- these two cases are the same
      right; cases ih (by rfl) with
      -- t₁ is a value
      | inl hv =>
        cases hv <;> try contradiction
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
      -- t₁ steps
      | inr hs =>
        have ⟨t₁', ρ', hs⟩ := hs
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | mult h₁ h₂ ih₁ ih₂ =>
      right; cases ih₁ (by rfl) with
      -- t₁ is a value
      | inl hv₁ =>
        cases ih₂ (by rfl) with
        -- t₂ is a value
        | inl hv₂ =>
          cases hv₁ <;> try contradiction
          cases hv₂ <;> try contradiction
          apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
        -- t₂ steps
        | inr hs₂ =>
          have ⟨t₂', ρ', hs₂⟩ := hs₂
          apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
      -- t₁ steps
      | inr hs₁ =>
        have ⟨t₁', ρ', hs₁⟩ := hs₁
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | ite0 h₁ _ _ ih₁ _ _ =>
      right; cases ih₁ (by rfl) with
      -- t₁ is a value
      | inl hv₁ =>
        cases hv₁ with (try contradiction)
        | nat n =>
          cases n <;> (apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval)
      -- t₁ steps
      | inr hs₁ =>
        have ⟨t₁', ρ', hs₁⟩ := hs₁
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | ref_ _ ih =>
      right; cases ih (by rfl) with
      -- t₁ is a value
      | inl hv =>
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
      -- t₁ steps
      | inr hs =>
        have ⟨t₁', ρ', hs⟩ := hs
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | deref h ih =>
      right; cases ih (by rfl) with
      -- t₁ is a value; its typing tells us `l < δ.length`
      | inl hv =>
        cases hv with (inversion h)
        | loc_ l => exists ρ[l], ρ; apply Step.derefLoc; lia
      -- t₁ steps
      | inr hs =>
        have ⟨t₁', ρ', hs⟩ := hs
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | @assign _ _ t₂ _ h₁ _ ih₁ ih₂ =>
      right; cases ih₁ (by rfl) with
      -- t₁ is a value
      | inl hv₁ =>
        cases ih₂ (by rfl) with
        -- t₂ is a value
        | inl hv₂ =>
          cases hv₁ with (inversion h₁)
          | loc_ l => exists <{ unit }>, ρ.set l t₂; apply Step.assign hv₂; lia
        -- t₂ steps
        | inr hs₂ =>
          have ⟨_, _, _⟩ := hs₂
          apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
      -- t₁ steps
      | inr hs₁ =>
        have ⟨t₁', ρ', hs₁⟩ := hs₁
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
```

::::full
Like the earlier preservation proof, many of these cases are repetitive.
Once again we can make the proof more concise using automation:

```lean
theorem progress_shorter (δ : StoreTy) (t : Tm) (τ : Ty) (ρ : Store)
  (hTy : <{ ∅ / δ ⊢ t ⦂ τ }>)
  (hStoreTy : δ ⊢ ρ) :
  (t.IsValue ∨ ∃ t' ρ', t / ρ ⟶ t' / ρ') := by
    have ⟨hLen, _⟩ := hStoreTy
    generalize heq : (∅ : Context) = Γ at hTy
    induction hTy with (
      subst_vars; first
      | contradiction
      -- discharge cases where `t` is obviously a value
      | (left; constructor; done)
      -- otherwise, `t` steps
      | (right
         -- we use the same trick as in the preservation proof
         -- to get around our unnamed `ih`
         (obtain hv | ⟨t', ρ', hs⟩ : Tm.IsValue _ ∨ ∃ t' ρ', _ / ρ ⟶ t' / ρ' := by
           solve_by_elim) <;>
         -- handle simple cases where `t`'s type gives us
         -- one possible value
         try
           (try (cases hv <;> try contradiction)) <;>
           (apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval)))
    | app h₁ _ _ ih₂ =>
      cases hv <;> inversion h₁
      obtain hv₂ | ⟨t₂', ρ', hs₂⟩ := ih₂ (by rfl) <;>
      (apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval)
    | mult h₁ h₂ _ ih₂ =>
      cases hv <;> try contradiction
      cases ih₂ (by rfl) with
      | inl hv₂ =>
        cases hv₂ <;> try contradiction
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
      | inr hs₂ =>
        have ⟨t₂', ρ', hs₂⟩ := hs₂
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
    | ite0 h₁ =>
      cases hv with (inversion h₁)
      | nat n =>
        cases n <;>
        (apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval)
    | deref h =>
      cases hv <;> inversion h
      apply Exists.intro; apply Exists.intro; apply Step.derefLoc; lia
    | assign h₁ _ _ ih₂ =>
      cases hv <;> inversion h₁
      cases ih₂ (by rfl) with
      | inl hv₂ =>
        apply Exists.intro; apply Exists.intro; apply Step.assign hv₂; lia
      | inr hs₂ =>
        have ⟨t₂', ρ', hs₂⟩ := hs₂
        apply Exists.intro; apply Exists.intro; solve_by_elim using StlcRefEval
```
::::

# References and Nontermination

An important fact about the STLC
is that it is _normalizing_ — that is, every well-typed term
can be reduced to a value in a finite number of steps.

What about STLC + references?  Surprisingly, adding references
causes us to lose the normalization property: there exist
well-typed terms in the STLC + references which can continue to
reduce forever, without ever reaching a normal form!

How can we construct such a term?  The main idea is to make a
function which calls itself.  We first make a function which calls
another function stored in a reference cell; the trick is that we
then smuggle in a reference to itself!

```display
(λR : Ref (Unit → Unit).
    R := (λX:Unit. (!R) unit); (!R) unit)
(ref (λX:Unit. unit))
```

::::full
First, `ref (λX:Unit.unit)` creates a reference to a cell of
type `Unit → Unit`.  We then pass this reference as the argument
to a function which binds it to the name `R`, and assigns to it
the function `λX:Unit.(!R) unit` — that is, the function which
ignores its argument and calls the function stored in `R` on the
argument `unit`; but of course, that function is itself!  To start
the divergent loop, we execute the function stored in the cell by
evaluating `(!r) unit`.

Here is the divergent term in Lean:
::::

```lean
namespace RefsAndNontermination

def loop_fun := <{ λX : Unit. (!R) unit }>

def loop :=
  <{ (λR : Ref (Unit → Unit). (( R := (λX : Unit. (!R) unit) );  ( (! R) unit ) ))
     (ref (λX : Unit. unit)) }>
```

This term is well typed:

```lean
theorem loop_typeable : ∃ τ, <{ ∅ / [] ⊢ loop ⦂ τ }> := by
  apply Exists.intro
  apply_rules using StlcRefTyping
```

To show formally that the term diverges, we first define the
`step_closure` of the single-step reduction relation, written
`⟶+`.  This is just like the reflexive step closure of
single-step reduction (which we're been writing `⟶*`), except
that it is not reflexive: `t ⟶+ t'` means that `τ` can reach
`t'` by _one or more_ steps of reduction.

```lean
inductive StepClosure {X:Type} (R: Relation X) : X → X → Prop :=
  | one {x y : X} (h₁ : R x y) : StepClosure R x y
  | step {x y z : X} (h₁ : R x y) (h₂ : StepClosure R y z) : StepClosure R x z

scoped notation:40
  t:71 " / " ρ:41 " ⟶+ " t':71 " / " ρ':41 =>
  StepClosure Step (t, ρ) (t', ρ')
```

Now, we can show that the expression {lean}`loop` reduces to the
expression `!(loc 0) unit` and the size-one store
`[R:=(loc 0)] loop_fun`.

As a convenience, we introduce a slight variant of the {tactic}`normalize`
tactic, called `reduce`, which tries solving the goal with
{lean}`Multi.refl` at each step, instead of waiting until the goal can't
be reduced any more. Of course, the whole point is that {lean}`loop`
doesn't normalize, so the old {tactic}`normalize` tactic would just go
into an infinite loop reducing it forever!

```lean
syntax "reduce" " using " ident,+ : tactic

macro_rules
  | `(tactic| reduce using $xs,*) =>
    `(tactic|
      repeat
        (apply Multi.step
         · solve_by_elim (maxDepth := 15) (constructor := false) [Nat.le.refl, Nat.le.step] using $xs,*
         try apply Multi.refl))
```

Next, we use {tactic}`reduce` to show that {lean}`loop` steps to
`!(loc 0) unit`, starting from the ∅ store.

```lean
theorem loop_steps_to_loop_fun :
  loop / [] ⟶*  <{ (! (loc 0)) unit }> / [<{ [R := loc 0] loop_fun }>] := by
    reduce using StlcRefEval
```

Finally, we show that the latter expression reduces in
two steps to itself!

```lean
theorem loop_fun_step_self :
  <{ (! (loc 0)) unit }> / [<{ [R := loc 0] loop_fun }>] ⟶+
  <{ (! (loc 0)) unit }> / [<{ [R := loc 0] loop_fun }>] := by
    apply StepClosure.step; solve_by_elim using StlcRefEval
    apply StepClosure.one; solve_by_elim using StlcRefEval
```

:::::full
::::exercise (rating := 4) (name := "factorial_ref")
Use the above ideas to implement a factorial function in STLC with
references.  (There is no need to prove formally that it really
behaves like the factorial.  Just uncomment the example below to make
sure it gives the correct result when applied to the argument
`4`.)

```lean
def factorial : Tm :=
  solution!(
    <{(λR : (Ref (Nat → Nat) ).
            (R := (λX : Nat. if0 X then 1 else (X * ( (!R) (pred X) ) ))); !R  )
      (ref (λX : Nat. X)) }>)

theorem factorial_type : <{ ∅ / [] ⊢ factorial ⦂ (Nat → Nat) }> := by
  solution!
    apply_rules using StlcRefTyping
```

:::autogradedHole factorial
:::

:::gradeTheorem "3" factorial_type
:::

If your definition is correct, you should be able to finish
the example below; the proof should be fully
automatic using the `reduce` tactic, once the witness is supplied.

```lean
theorem factorial_4 : ∃ (ρ : Store), <{ factorial 4 }> / [] ⟶* .const 24 / ρ := by
  solution!
    exists [<{ λX : Nat. if0 X then 1 else (X * ((!(loc 0)) (pred X))) }>]
    reduce using StlcRefEval
```
::::
:::::

```lean
end RefsAndNontermination
```

# Additional Exercises

:::suppressPreviousHeaderWhenTerse
:::

:::::full
::::exercise (rating := 5) (name := "garbage_collector") (optional := true)
Challenge problem: modify our formalization to include an account
of garbage collection, and prove that it satisfies whatever nice
properties you can think to prove about it.
::::
:::::

```lean
end STLCRef
```
