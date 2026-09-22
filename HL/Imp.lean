import SFLMeta

import LF.CustomTactics
import LF.Typeclasses

import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Imp: Simple Imperative Programs" =>
%%%
tag := "Imp"
htmlSplit := .never
file := some "Imp"
%%%

:::instructors
This chapter plus `Typeclasses` takes a little more than one
   80-minute lecture.  It could be streamlined a bit further without
   losing much, by removing (for example) the inference rules and BNF
   notations from the terse version.

   (BCP 21: ... Actually, I tried removing inference rules from the
   TERSE version; eventually decided that it makes some of the
   definitions harder to talk about.)
:::

:::dev BeforeNextRelease
Needs some WORKINCLASSes and some quizzes

LATER: Another nice challenge exercise at some point would be to add
   C-style arrays (i.e., indirect read/write).  This sets up some
   really nice challenge problems in Hoare (reasoning about arrays /
   aliasing / etc.).

SOONER: BCP 25: Maybe we should write /\ instead of && in assertions,
   to save a mismatch in the `dec_minimum` exercise in Hoare₂?

   At some point we could consider moving material from the old
   HoareLists to this chapter (and into later files, as
   appropriate).  We haven't done it yet because it's a shame to
   complicate the nice simple presentation here when it's used as the
   basis for applications like Xavier's static analysis lectures.
   Also, we now have a whole volume on real separation logic...
:::

::::full
In this chapter, we take a more serious look at how to use Lean as a
tool to study other things.  Our case study is a _simple imperative
programming language_ called Imp, embodying a tiny core fragment of
conventional mainstream languages such as C and Java.

Here is a familiar mathematical function written in Imp.

```display
Z := X;
Y := 1;
while (Z ≠ 0) {
  Y := Y * Z;
  Z := Z - 1
}
```
::::

We concentrate here on defining the _syntax_ and _semantics_ of Imp;
later in this volume we develop a theory of _program equivalence_ and introduce
_Hoare Logic_, a popular logic for reasoning about imperative programs.

::::full
We build Imp in three layers.  The first — a core language of _arithmetic and
boolean expressions_ — is developed in its own chapter, {ref "Slang"}[_Slang_];
read that one first.  There you meet the abstract syntax of arithmetic
expressions (`Aexp`) and boolean expressions (`Bexp`), their evaluation both as
a recursive _function_ and as an inductive _relation_ (proved equivalent), and a
small `optimize0plus` program transformation together with its correctness
proof.  Those expressions are _variable-free_.

This chapter picks up from there.  First we extend the expressions with
_variables_; then we add a language of _commands_ — assignment, conditionals,
sequencing, and loops.
::::

# Expressions With Variables

::::full
Let's return to defining Imp. The next thing we need to do is to
enrich our arithmetic and boolean expressions with variables. To keep
things simple, we'll assume that all variables are global and that they
only hold numbers.
::::

## States

:::dev PotentialImprovement
Maybe this section needs a little preface talking about "what is
   the meaning of an expression with variables?"...

LATER: (Note copied from Equiv right before the `assign_aequiv`
   exercise): Some or all of this discussion should really happen when
   states are introduced in Imp.v, and the whole idea of treating states as
   an ADT should be raised there.
:::

Since we'll want to look variables up to find out their current values,
we'll use total maps from the
{ref "Typeclasses" (remote := "lf")}`Typeclasses` chapter. A _machine state_ (or
just _state_) represents the current values of all variables at some
point in the execution of a program.

::::full
For simplicity, we assume that the state is defined for _all_ variables,
even though any given program is only able to mention a finite number of
them. Because each variable stores a natural number, we represent the
state as a total map from strings (variable names) to {name}`Nat`, and will use
`0` as the default value in the store.
::::

We give the type of variable identifiers a name, `Ident`. For now it is just
{name}`String`; naming it makes the intent clearer.

```lean
open scoped MyGetElem

abbrev Ident := String
abbrev State := TotalMap Ident Nat
```

## Syntax

We can add variables to the arithmetic expressions we had before simply
by including one more constructor.  (This is a fresh `Aexp`, replacing
the variable-free one from the {ref "Slang"}[Slang] chapter.)

```lean
inductive Aexp where
  | num (n : Nat)
  | id (x : Ident)                -- NEW
  | plus (a₁ a₂ : Aexp)
  | minus (a₁ a₂ : Aexp)
  | mult (a₁ a₂ : Aexp)
```

:::dev "Chris Henson (chenson2018)" PotentialImprovement
Rather than define identifiers as Ident, a more general approach is
to use a *type variable* with `DecidableEq` (as the
`Maps` chapter does), threaded through `Aexp`/`Bexp`/`Com`/`State`.  Stashed
for a future decision; the parameterized version would look like:

```
inductive Aexp (V : Type) where
  | num (n : Nat)
  | id (x : V)
  | plus (a₁ a₂ : Aexp V)
  | minus (a₁ a₂ : Aexp V)
  | mult (a₁ a₂ : Aexp V)
-- … then `Bexp V`, `Com V`, `abbrev State (V) [DecidableEq V] :=
-- TotalMap V Nat`, and `[DecidableEq V]` wherever a lookup/update is
-- performed.
```
:::

The `Bexp` definition is unchanged, except that it now refers to the new {name}`Aexp`.

```lean
inductive Bexp where
  | bool (b : Bool)
  | eq (a₁ a₂ : Aexp)
  | neq (a₁ a₂ : Aexp)
  | le (a₁ a₂ : Aexp)
  | gt (a₁ a₂ : Aexp)
  | not (b : Bexp)
  | and (b₁ b₂ : Bexp)
```

Defining a few variable names as shorthands will make examples easier to read.

```lean
def W : Ident := "W"
def X : Ident := "X"
def Y : Ident := "Y"
def Z : Ident := "Z"
```

:::instructors
Making `X Y Z W` `@[simp] def`s has the unwanted side effect that
sometimes `X` and `"X"` get mixed up in the proof state.
We opt to use {tactic}`simp +decide` instead (e.g. in `assertion_auto` in Hoare).
:::

:::ignore
```lean -show
example : X ≠ Y := by
  simp +decide

example : (Y →ₜ 1 ; X →ₜ 2)[X] = 2 := by
  simp +decide
```
:::

## Notations
%%%
tag := "imp-notations"
%%%

::::full
To make Imp programs easier to read and write, we introduce some notations.

You do not need to understand exactly what these declarations do. Briefly, though,
here is how the two blocks below fit together:

- The `declare_syntax_cat` directive adds a new non-terminal to Lean's grammar, called
  `imp_aexp`. We'll add additional non-terminals further below.
- Each `syntax` directive defines a grammar production, of which there are eight in
  total. The first two define literals, `num` and `ident`, as `imp_aexp`s. The next
  several directives define productions for building larger expressions, with
  some annotations to define precedence, etc.
- Finally, `macro_rules` is used to translate each production of the `imp_aexp` nonterminal
  into a Lean expression.

Boolean expressions and, later, commands follow this same pattern exactly, so
their declarations are collapsed where they appear: open one if you want to see
the pattern repeated, and skip them otherwise.
::::

::::details "Notation encoding: arithmetic expressions"
```lean
/-- Arithmetic expressions of Imp -/
declare_syntax_cat imp_aexp
/-- Numeric literal -/
syntax:max num : imp_aexp
/-- `Ident` or Lean identifier -/
syntax:max ident : imp_aexp
/-- Addition -/
syntax:65 imp_aexp:65 " + " imp_aexp:66 : imp_aexp
/-- Subtraction -/
syntax:65 imp_aexp:65 " - " imp_aexp:66 : imp_aexp
/-- Multiplication -/
syntax:70 imp_aexp:70 " * " imp_aexp:71 : imp_aexp
/-- Parentheses for grouping -/
syntax:max "(" imp_aexp ")" : imp_aexp
/-- Escape to Lean -/
syntax:max "~" term:max : imp_aexp

/-- Embed an Imp arithmetic expression into a Lean term -/
syntax:80 "aexp " "{" imp_aexp "}" : term
```
::::

:::instructors
A bare identifier is resolved by its type.
An {name}`Ident` such as {name}`X` becomes {name}`Aexp.id`,
while an {name}`Aexp` is inserted directly.
A consequence is that object-language variables must
be a declared {name}`Ident` constants — as {name}`W`/{name}`X`/{name}`Y`/{name}`Z` are,
but Lean variables of type {name}`Aexp` can be referred without antiquotation.
:::

```lean
namespace Imp.Elab

open Lean Elab Term Meta

def withSourceInfoOf {kind : Name} (ref : Syntax) (stx : TSyntax kind)
    (canonical := true) : TSyntax kind :=
  let info := SourceInfo.fromRef ref (canonical := canonical)
  ⟨stx.raw.setInfo info⟩

macro_rules
  | `(aexp { $exp:imp_aexp }) => do
    let stx ← match exp with
      | `(imp_aexp| $n:num) => ``(Aexp.num $n)
      | `(imp_aexp| ~$e:term) => ``(($e : Aexp))
      | `(imp_aexp| $a + $b) => ``(Aexp.plus (aexp {$a}) (aexp {$b}))
      | `(imp_aexp| $a - $b) => ``(Aexp.minus (aexp {$a}) (aexp {$b}))
      | `(imp_aexp| $a * $b) => ``(Aexp.mult (aexp {$a}) (aexp {$b}))
      | `(imp_aexp| ($a)) => ``(aexp {$a})
      | _ => Lean.Macro.throwUnsupported
    return withSourceInfoOf exp stx

elab_rules : term
  | `(aexp { $x:ident }) => do
    let some e ← resolveId? x (withInfo := true)
      | throwErrorAt x "unknown identifier `{x.getId.eraseMacroScopes}`"
    let type ← whnf (← inferType e)
    tryPostponeIfMVar type
    match_expr type with
    | Aexp => pure e
    | String => mkAppM ``Aexp.id #[e]
    | _ => throwErrorAt x "expected an Imp identifier or arithmetic expression"

end Imp.Elab
```

:::instructors
The literals `true`/`false` are accepted through the bare-identifier form
(`syntax:max ident : imp_bexp`) and turned into {name}`Bexp.bool` by the macro
below. Any other bare identifier is inserted as a Lean {name}`Bexp`.
We take this route rather than
declaring `true`/`false` as symbols: as reserved keywords they would break
ordinary Lean uses of `true`/`false`, and as non-reserved symbols they would
clash with the bare-identifier form of `imp_aexp`.
:::

::::details "Notation encoding: boolean expressions"
```lean
/-- Boolean expressions of Imp -/
declare_syntax_cat imp_bexp
/-- Boolean literal (`true` or `false`) and Lean identifier -/
syntax:max ident : imp_bexp
/-- Equality of arithmetic expressions -/
syntax:50 imp_aexp:51 " = " imp_aexp:51 : imp_bexp
/-- Disequality of arithmetic expressions -/
syntax:50 imp_aexp:51 " ≠ " imp_aexp:51 : imp_bexp
/-- Less than or equal -/
syntax:50 imp_aexp:51 " ≤ " imp_aexp:51 : imp_bexp
/-- Greater than -/
syntax:50 imp_aexp:51 " > " imp_aexp:51 : imp_bexp
/-- Boolean negation -/
syntax:70 "¬ " imp_bexp:70 : imp_bexp
/-- Boolean conjunction (right associative) -/
syntax:35 imp_bexp:36 " ∧ " imp_bexp:35 : imp_bexp
/-- Parentheses for grouping -/
syntax:max "(" imp_bexp ")" : imp_bexp
/-- Escape to Lean -/
syntax:max "~" term:max : imp_bexp

/-- Embed an Imp boolean expression into a Lean term -/
syntax:80 "bexp " "{" imp_bexp "}" : term
```
::::

::::details "Notation encoding: boolean expressions, macro rules"
```lean
namespace Imp.Elab

open Lean

macro_rules
  | `(bexp { $exp:imp_bexp }) => do
    let stx ← match exp with
      | `(imp_bexp| true) => ``(Bexp.bool true)
      | `(imp_bexp| false) => ``(Bexp.bool false)
      | `(imp_bexp| $x:ident) => ``(($x : Bexp))
      | `(imp_bexp| ~$e:term) => ``(($e : Bexp))
      | `(imp_bexp| $a:imp_aexp = $b:imp_aexp) => ``(Bexp.eq (aexp {$a}) (aexp {$b}))
      | `(imp_bexp| $a:imp_aexp ≠ $b:imp_aexp) => ``(Bexp.neq (aexp {$a}) (aexp {$b}))
      | `(imp_bexp| $a:imp_aexp ≤ $b:imp_aexp) => ``(Bexp.le (aexp {$a}) (aexp {$b}))
      | `(imp_bexp| $a:imp_aexp > $b:imp_aexp) => ``(Bexp.gt (aexp {$a}) (aexp {$b}))
      | `(imp_bexp| ¬ $b:imp_bexp) => ``(Bexp.not (bexp {$b}))
      | `(imp_bexp| $b₁:imp_bexp ∧ $b₂:imp_bexp) => ``(Bexp.and (bexp {$b₁}) (bexp {$b₂}))
      | `(imp_bexp| ($b:imp_bexp)) => ``(bexp {$b})
      | _ => Macro.throwUnsupported
    return withSourceInfoOf exp stx

end Imp.Elab
```
::::

```lean
#check aexp { 3 + (X * 2) }
#check bexp { true ∧ ¬(X ≤ 4) }
```

## Delaborators
%%%
tag := "imp-delaborators"
%%%

::::full
Next, we write a suite of _delaborators_ for {name}`Aexp` and {name}`Bexp`.
Delaborators are like the opposite of `macro_rules` -- they are used to pretty print _elaborated_ terms back to the user.
::::

::::details "Notation encoding: printing expressions back"
```lean
namespace Imp.Delab

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer Imp.Elab

@[category_parenthesizer imp_aexp]
def imp_aexp.parenthesizer : CategoryParenthesizer := fun prec => do
  maybeParenthesize `imp_aexp true wrapParens prec <|
    parenthesizeCategoryCore `imp_aexp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let stxInfo := SourceInfo.fromRef stx
    let stx := stx.setInfo .none
    let pstx ← `(imp_aexp| ($(⟨stx⟩)))
    return pstx.raw.setInfo stxInfo

@[category_parenthesizer imp_bexp]
def imp_bexp.parenthesizer : CategoryParenthesizer := fun prec => do
  Parenthesizer.maybeParenthesize `imp_bexp true wrapParens prec <|
    Parenthesizer.parenthesizeCategoryCore `imp_bexp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let stxInfo := SourceInfo.fromRef stx
    let stx := stx.setInfo .none
    let pstx ← `(imp_bexp| ($(⟨stx⟩)))
    return pstx.raw.setInfo stxInfo
```
::::

::::details "Notation encoding: registering the delaborators"
```lean

/--
Recognizes a term as being an `aexp { ... }` expression.
-/
def getAexp (stx : Term) : TSyntax `imp_aexp :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `(aexp { $e:imp_aexp }) => return e
    | _ => `(imp_aexp| ~$stx)

@[app_unexpander Aexp.num]
private def Aexp.unexpandNum : Unexpander
  | `($_ $n:num) => `(aexp { $n:num })
  | _ => throw ()

@[app_unexpander Aexp.id]
private def Aexp.unexpandId : Unexpander
  | `($_ $x:ident) => `(aexp { $x:ident })
  | _ => throw ()

@[app_unexpander Aexp.plus]
private def Aexp.unexpandPlus : Unexpander
  | `($_ $a $b) => `(aexp { $(getAexp a) + $(getAexp b) })
  | _ => throw ()

@[app_unexpander Aexp.minus]
private def Aexp.unexpandMinus : Unexpander
  | `($_ $a $b) => `(aexp { $(getAexp a) - $(getAexp b) })
  | _ => throw ()

@[app_unexpander Aexp.mult]
private def Aexp.unexpandMult : Unexpander
  | `($_ $a $b) => `(aexp { $(getAexp a) * $(getAexp b) })
  | _ => throw ()

/--
Recognizes a term as being an `bexp { ... }` expression.
-/
def getBexp (stx : Term) : TSyntax `imp_bexp :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `(bexp { $e:imp_bexp }) => return e
    | _ => `(imp_bexp| ~$stx)

/--
Delaborator for `Bexp.bool`. This is needed since we want to be sure we are
matching on the actual `true`/`false` expressions, rather than matching on the
delaborated identifiers `true`/`false` (which might not be accurate).
-/
@[app_delab Bexp.bool]
private def BExp.delabBool : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.isAppOfArity ``Bexp.bool 1
  match_expr e.appArg! with
  | true => `(bexp { $(mkIdent `true):ident })
  | false => `(bexp { $(mkIdent `false):ident })
  | _ => failure


@[app_unexpander Bexp.eq]
private def Bexp.unexpandEq : Unexpander
  | `($_ $a $b) => `(bexp { $(getAexp a):imp_aexp = $(getAexp b):imp_aexp })
  | _ => throw ()

@[app_unexpander Bexp.neq]
private def Bexp.unexpandNeq : Unexpander
  | `($_ $a $b) => `(bexp { $(getAexp a):imp_aexp ≠ $(getAexp b):imp_aexp })
  | _ => throw ()

@[app_unexpander Bexp.le]
private def Bexp.unexpandLe : Unexpander
  | `($_ $a $b) => `(bexp { $(getAexp a):imp_aexp ≤ $(getAexp b):imp_aexp })
  | _ => throw ()

@[app_unexpander Bexp.gt]
private def Bexp.unexpandGt : Unexpander
  | `($_ $a $b) => `(bexp { $(getAexp a):imp_aexp > $(getAexp b):imp_aexp })
  | _ => throw ()

@[app_unexpander Bexp.not]
private def Bexp.unexpandNot : Unexpander
  | `($_ $a) => `(bexp { ¬ $(getBexp a):imp_bexp })
  | _ => throw ()

@[app_unexpander Bexp.and]
private def Bexp.unexpandAnd : Unexpander
  | `($_ $a $b) => `(bexp { $(getBexp a):imp_bexp ∧ $(getBexp b):imp_bexp })
  | _ => throw ()

end Imp.Delab
```
::::

:::ignore
```lean -show -keep

def a₁ : Aexp := aexp { X + 1 }
def a₂ : Aexp := aexp { a₁ * 5 }

/-- info: aexp {1 * (2 + 3)} : Aexp -/
#guard_msgs in #check aexp { 1 * (2 + 3) }
/-- info: aexp {(1 + 2) * 3} : Aexp -/
#guard_msgs in #check aexp { (1 + 2) * 3 }
/-- info: aexp {X + ~a₁} : Aexp -/
#guard_msgs in #check aexp { X + a₁ }

def b₁ := bexp { true ∧ ¬(X ≤ 4) }
def b₂ := bexp { b₁ ∧ (¬ (X ≤ (4 + 2))) }

/-- info: bexp {1 = X} : Bexp -/
#guard_msgs in #check bexp { 1 = X }
/-- info: bexp {1 ≠ X} : Bexp -/
#guard_msgs in #check bexp { 1 ≠ X }
/-- info: bexp {1 ≤ X} : Bexp -/
#guard_msgs in #check bexp { 1 ≤ X }
/-- info: bexp {1 > X} : Bexp -/
#guard_msgs in #check bexp { 1 > X }
/-- info: bexp {¬ true} : Bexp -/
#guard_msgs in #check bexp { ¬ true }
/-- info: bexp {true ∧ false} : Bexp -/
#guard_msgs in #check bexp { true ∧ false }

/-- info: bexp {~b₁ ∧ ~b₂ ∧ ~a₁ + ~a₂ = ~a₂ + 1} : Bexp -/
#guard_msgs in #check bexp { b₁ ∧ b₂ ∧ (a₁ + a₂) = (a₂ + 1) }

```
:::

::::full
With these delaborators in place, Lean pretty-prints Imp expressions with the higher-level
notations rather than their raw constructors.

The pretty-printed version of an expression might not exactly
match its original form.
For example, the parentheses around `X * 2` in `aexp { 3 + (X * 2) }` are not printed because
they are redundant, which the parenthesizer knows.
::::

```lean
/-- info: aexp {3 + X * 2} : Aexp -/
#guard_msgs in
#check aexp { 3 + (X * 2) }

/-- info: bexp {true ∧ ¬ (X ≤ 4)} : Bexp -/
#guard_msgs in
#check bexp { true ∧ ¬(X ≤ 4) }
```

## Evaluation

::::full
The arithmetic and boolean evaluators must now be extended to handle
variables, taking a state `st` as an extra argument.  A variable is
looked up in the state with the map-indexing notation `st[x]` from the
{ref "Typeclasses" (remote := "lf")}`Typeclasses` chapter in the Logical Foundations book.
For the notation to work, we used `open scoped MyGetElem` earlier,
which opens only the scoped items like notation from the module.
::::

:::terse
Now we need to add an `st` parameter to both evaluation functions:
:::

```lean
def Aexp.eval (st : State) (a : Aexp) : Nat :=
  match a with
  | num   n     =>  n
  | id    x     =>  st[x]                    -- NEW
  | plus  a₁ a₂ =>  a₁.eval st + a₂.eval st
  | minus a₁ a₂ =>  a₁.eval st - a₂.eval st
  | mult  a₁ a₂ =>  a₁.eval st * a₂.eval st

def Bexp.eval (st : State) (b : Bexp) : Bool :=
  match b with
  | bool b      =>  b
  | eq   a₁ a₂  =>  a₁.eval st == a₂.eval st
  | neq  a₁ a₂  =>  a₁.eval st != a₂.eval st
  | le   a₁ a₂  =>  a₁.eval st ≤  a₂.eval st
  | gt   a₁ a₂  =>  a₁.eval st >  a₂.eval st
  | not  b₁     =>  !b₁.eval st
  | and  b₁ b₂  =>  b₁.eval st && b₂.eval st

@[simp] theorem Aexp.eval_num (st : State) (n : Nat) : (num n).eval st = n := rfl
@[simp] theorem Aexp.eval_id (st : State) (x : Ident) : (Aexp.id x).eval st = st[x] := rfl
@[simp] theorem Aexp.eval_plus (st : State) (a₁ a₂ : Aexp) :
    (plus a₁ a₂).eval st = a₁.eval st + a₂.eval st := rfl
@[simp] theorem Aexp.eval_minus (st : State) (a₁ a₂ : Aexp) :
    (minus a₁ a₂).eval st = a₁.eval st - a₂.eval st := rfl
@[simp] theorem Aexp.eval_mult (st : State) (a₁ a₂ : Aexp) :
    (mult a₁ a₂).eval st = a₁.eval st * a₂.eval st := rfl

@[simp] theorem Bexp.eval_bool (st : State) (b : Bool) : (bool b).eval st = b := rfl
@[simp] theorem Bexp.eval_eq (st : State) (a₁ a₂ : Aexp) :
    (eq a₁ a₂).eval st = (a₁.eval st == a₂.eval st) := rfl
@[simp] theorem Bexp.eval_neq (st : State) (a₁ a₂ : Aexp) :
    (neq a₁ a₂).eval st = (a₁.eval st != a₂.eval st) := rfl
@[simp] theorem Bexp.eval_le (st : State) (a₁ a₂ : Aexp) :
    (le a₁ a₂).eval st = (a₁.eval st ≤ a₂.eval st : Bool) := rfl
@[simp] theorem Bexp.eval_gt (st : State) (a₁ a₂ : Aexp) :
    (gt a₁ a₂).eval st = (a₁.eval st > a₂.eval st : Bool) := rfl
@[simp] theorem Bexp.eval_not (st : State) (b : Bexp) : (not b).eval st = !b.eval st := rfl
@[simp] theorem Bexp.eval_and (st : State) (b₁ b₂ : Bexp) :
    (and b₁ b₂).eval st = (b₁.eval st && b₂.eval st) := rfl
```

We reuse the total-map notation (`x →ₜ v` etc.) for states.

```lean
example : aexp { 3 + (X * 2) }.eval (X →ₜ 5) = 13 := by rfl

example : aexp { Z + (X * Y) }.eval (X →ₜ 5 ; Y →ₜ 4) = 20 := by rfl

example : bexp { true ∧ ¬(X ≤ 4) }.eval (X →ₜ 5) = true := by rfl
```

# Commands

::::full
Now we are ready to define the syntax and behavior of Imp _commands_
(or _statements_). Informally, commands `c` are described by the
following BNF grammar:

```bnf
c ::= "skip"
    | x ":=" a
    | c ";" c
    | "if" b "then" c "else" c "end"
    | "while" b "do" c "end" ;
```

Here is the formal definition of the abstract syntax of commands.
::::

```lean
inductive Com where
  | skip
  | asgn (x : Ident) (a : Aexp)
  | seq (c₁ c₂ : Com)
  | cond (b : Bexp) (c₁ c₂ : Com)
  | whileDo (b : Bexp) (c : Com)
```

:::instructors
We don't make `skip` a reserved keyword on purpose because otherwise `skip` couldn't be used as a name and {name}`Com.skip` would not work.
:::

::::details "Notation encoding: commands, macro rules"
```lean
/-- Imp commands -/
declare_syntax_cat imp_com
/-- The command that does nothing (`skip`) -/
syntax:max ident : imp_com
/-- Sequencing: one command after another (right associative. min + 1 = 11) -/
syntax:80 imp_com:11 Lean.Parser.semicolonOrLinebreak ppHardSpace imp_com:min : imp_com
/-- Assignment -/
syntax:max ident ppHardSpace ":=" ppHardSpace imp_aexp : imp_com
/-- Conditional -/
syntax:max "if " "(" imp_bexp ")" ppHardSpace "{" imp_com "}" ppHardSpace "else" ppHardSpace "{" imp_com "}" : imp_com
/-- Loop -/
syntax:max "while " "(" imp_bexp ")" ppHardSpace "{" imp_com "}" : imp_com
/-- Escape to Lean -/
syntax:max "~" term:max : imp_com

/-- Include an Imp command in Lean code -/
syntax:80 "imp" ppHardSpace "{" imp_com "}" : term

namespace Com

open Lean Imp.Elab

scoped macro_rules
  | `(imp { $s }) => do
    let stx ← match s with
      | `(imp_com| skip) => ``(Com.skip)
      | `(imp_com| $x:ident) => ``(($x : Com))
      | `(imp_com| $c₁ ; $c₂) =>
        ``(Com.seq (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| $x:ident := $a) =>
        ``(Com.asgn $x (aexp {$a}))
      | `(imp_com| if ($b) {$c₁} else {$c₂}) =>
        ``(Com.cond (bexp {$b}) (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| while ($b) {$c}) =>
        ``(Com.whileDo (bexp {$b}) (imp {$c}))
      | `(imp_com| ~$c) => `(($c : Com))
      | _ => Macro.throwUnsupported
    return withSourceInfoOf s stx

end Com

open scoped Com
```
::::

::::details "Notation encoding: printing commands back"
```lean
namespace Imp.Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Elab

/--
Recognizes a term as being an `imp { ... }` expression.
-/
def getImp (stx : Term) : TSyntax `imp_com :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `(imp { $e:imp_com }) => return e
    | _ => `(imp_com| ~$stx)

@[app_unexpander Com.skip]
def unexpandComSkip : Unexpander
  | _ => `(imp { $(mkIdent `skip):ident })

@[app_unexpander Com.asgn]
def unexpandComAsgn : Unexpander
  | `($_ $x:ident $a) => `(imp { $x:ident := $(getAexp a) })
  | _ => throw ()

@[app_unexpander Com.seq]
def unexpandComSeq : Unexpander
  | `($_ $a $b) =>
    match a with
    | `(imp { $_ ; $_ }) =>
      -- seq syntax is right associative, so need to quote `a`
      `(imp { ~$a ; $(getImp b):imp_com })
    | _ =>
      `(imp { $(getImp a):imp_com ; $(getImp b):imp_com })
  | _ => throw ()

@[app_unexpander Com.cond]
def unexpandComCond : Unexpander
  | `($_ $b $c₁ $c₂) => `(imp { if ($(getBexp b)) { $(getImp c₁) } else { $(getImp c₂) } })
  | _ => throw ()

@[app_unexpander Com.whileDo]
def unexpandComWhileDo : Unexpander
  | `($_ $b $c) => `(imp { while ($(getBexp b)) { $(getImp c) } })
  | _ => throw ()

end Imp.Delab
```
::::

:::ignore
```lean -show
section
/-- info: imp {skip} : Com -/
#guard_msgs in
#check imp { skip }

/-- info: imp {skip; if (true) {X := 1} else {X := 2}} : Com -/
#guard_msgs in
#check imp { skip; if (true) {X := 1} else {X:=2} }


variable (x : Ident) (a : Aexp)
/-- info: imp {x := ~a} : Com -/
#guard_msgs in
#check imp { x := a }

/-- info: imp {x := ~a} : Com -/
#guard_msgs in
#check imp { ~(Com.asgn x a) }

/-- info: Com.asgn (if true = true then x else x) a : Com -/
#guard_msgs in
#check imp { ~(Com.asgn (if true then x else x) a) }

/-- info: imp {if (true) {skip} else {~(Com.asgn (if true = true then x else x) a)}} : Com -/
#guard_msgs in
#check imp { if (true) { skip } else{ ~(Com.asgn (if true then x else x) a)}}

variable (b : Bexp) (c c₁ c₂ : Com)

/-- info: imp {x := ~a} : Com -/
#guard_msgs in
#check imp { x := a }

/-- info: imp {if (~b) {~c₁} else {~c₂}} : Com -/
#guard_msgs in
#check imp { if (b) {c₁} else {c₂} }

/-- info: c : Com -/
#guard_msgs in
#check imp { c }

/-- info: imp {~c₁; ~c₂} : Com -/
#guard_msgs in
#check imp {c₁;c₂}

example : (
  match imp { skip; c } with
    | imp { skip; c' } => c' -- no need to write `~c'`
    | _ => imp { skip }) = c := rfl


example : (
  match imp { X := X + 1 } with
    | imp { x := ~a } => (x, a) -- still need `~`, because `a` itself is a valid aexp.
                                -- here we want to bind the entire RHS.
    | _ => (X, aexp {0})) = (X, aexp {X + 1}) := rfl

variable (b : Bool) (y : Ident)

/--
info: imp {if
    (~(Bexp.bool
        b)) {if (true) {y := ~(Aexp.num (3 + 4))} else {~(Com.asgn (if b = true then x else y) a)}} else {skip}} : Com
-/
#guard_msgs in
#check
  Com.cond (Bexp.bool b)
    (.cond (Bexp.bool true)
      (.asgn y (.num <| 3 + 4))
      (.asgn (if b then x else y) a)
    ) (.skip)

end
```
:::

::::full
As an example, here is the factorial function again, written as a formal
definition. When this command terminates, the variable `Y` will
contain the factorial of the initial value of `X`.  (Compare this to
the concrete Imp program at the very start of the chapter.)
::::

```lean
def fact_in_lean : Com := imp {
  Z := X
  Y := 1
  while (Z ≠ 0) {
    Y := Y * Z
    Z := Z - 1
  }
}
```

::::full
Because we registered a delaborator, we can inspect a defined program with
`#print`, which pretty prints (i.e. delaborates) the stored definition using the same syntax:
::::

```lean (name := fact_in_lean)
#print fact_in_lean
```

```leanOutput fact_in_lean
def fact_in_lean : Com :=
imp {Z := X; Y := 1; while (Z ≠ 0) {Y := Y * Z; Z := Z - 1}}
```

## Desugaring Notations

Even though the notations are useful for getting the high-level picture,
it's sometimes helpful to turn off the notation to see the parsed structure as a plain term.
This can be done with `set_option pp.notation false`
(which we briefly mentioned in the {ref "Typeclasses" (remote := "lf")}`Typeclasses` chapter) as follows:

```lean (name := imp1)
#check imp { X := X + 1 }
```

```leanOutput imp1
imp {X := X + 1} : Com
```

```lean (name := imp2)
set_option pp.notation false in
#check imp { X := X + 1 }
```

```leanOutput imp2
Com.asgn X ((Aexp.id X).plus (Aexp.num 1)) : Com
```

## More Examples

A few more examples.

:::slidebreak
:::

Assignment:

```lean
def plus2 : Com := imp { X := X + 2 }
def XtimesYinZ : Com := imp { Z := X * Y }
```

:::slidebreak
:::

Loops:

```lean
def subtract_slowly_body : Com := imp {
  Z := Z - 1;
  X := X - 1
}

def subtract_slowly : Com := imp {
  while (X ≠ 0) {
    ~subtract_slowly_body
  }
}

def subtract_3_from_5_slowly : Com := imp {
  X := 3;
  Z := 5;
  ~subtract_slowly
}
```

:::slidebreak
:::

An infinite loop:

```lean
def loop : Com := imp { while (true) { skip } }
```

:::hide
```
/- Exponentiation: -/
def exp_body : Com := imp {
  Z := Z * X;
  Y := Y - 1
}
def pexp : Com := imp {
  while (Y ≠ 0) {
    ~exp_body
  }
}
/- (Note that `pexp` should be run in a state where `Z` is `1`.) -/
```
:::

# Evaluating Commands

::::full
Next we need to define what it means to evaluate an Imp command.  The
fact that `while` loops don't necessarily terminate makes defining an
evaluation function tricky.
::::

## Evaluation as a Function (Failed Attempt)

:::dev PotentialImprovement
In SmallStep we need to package the state and command into a pair,
   so that we can talk about normal forms and such. Probably we should do it
   here too, for consistency. (Won't change much except the type
   declarations, but we'll need to add a comment why we wrote them this
   way.)
:::

In a more conventional functional language like OCaml or Haskell we could define
the evaluation function as follows:

```lean -keep +error (name := eval_fail)
def Com.eval (st : State) (c : Com) : State :=
  match c with
  | imp {skip} => st
  | imp {x := ~a} => (x →ₜ a.eval st ; st)
  | imp {c₁; c₂} =>
      let st' := eval st c₁
      eval st' c₂
  | imp {if (b) {c₁} else {c₂}} =>
      if b.eval st then eval st c₁
      else eval st c₂
  | imp {while (b) {c}} =>
      if b.eval st then eval st (imp { c; while (b) {c}})
      --                ^-- recursive call without a decreasing argument
      else st
```

```leanOutput eval_fail
fail to show termination for
  Com.eval
with errors
failed to infer structural recursion:
Cannot use parameter st:
  the type TotalMap Ident Nat does not have a `.brecOn` recursor
Cannot use parameter c:
  failed to eliminate recursive application
    eval st (imp {~c; while (~b) {~c}})


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
st : State
b : Bexp
c : Com
h✝ : Bexp.eval st b = true
⊢ 1 + sizeOf c + (1 + sizeOf b + sizeOf c) < 1 + sizeOf b + sizeOf c
```

::::full
Lean doesn't accept such a definition
because the function we want to define is not guaranteed to terminate.
Indeed, it _doesn't_ always terminate: the full `Com.eval` applied to
the `loop` program above would run forever. Since Lean aims to be not
just a programming language but also a consistent logic, any
potentially non-terminating function must be rejected.

Here is what would go wrong if Lean allowed non-terminating recursive functions:

```lean +error -keep
theorem loop_false (n : Nat) : False := loop_false n
```

That is, propositions like {name}`False` would become provable (`loop_false 0`
would be a proof of {name}`False`), a disaster for logical consistency.

Thus, because it doesn't terminate on all inputs, the full `Com.eval`
cannot be written in Lean -- at least not without additional tricks and
workarounds.
::::

:::dev
   Perhaps that discussion should be moved to -- or previewed in --
   Logic.v?  MRC'20: It's already in ProofObjects (which not everyone
   sees).
:::

:::terse
A nonterminating `theorem loop_false (n : Nat) : False := loop_false n` would make `False`
provable, so Lean rejects it.
:::

## Evaluation as a Relation

Here's a better way: define `Com.eval` as a _relation_ rather than a
_function_ -- i.e., make its result a {lean}`Prop` rather than a {name}`State`,
similar to what we did for `Aexp.EvalR` in the {ref "Slang"}[Slang] chapter.

::::full
This is an important change. Besides freeing us from awkward workarounds,
it gives us more flexibility in the definition. For example, if we
add nondeterministic features like `any` to the language, we want the
definition of evaluation to be nondeterministic -- i.e., not only will it
not be total, it will not even be a function!
::::

:::dev "Michael Hicks (mwhicks1)"
I kind of hate this notation. Is there something more standard
in Lean? CSLib precedent maybe?
:::

We'll use the notation `st =[ c ]=> st'` for the `Com.EvalR` relation:
`st =[ c ]=> st'` means that executing program `c` in a starting state
`st` results in an ending state `st'`.  This can be pronounced "`c` takes
state `st` to `st'`".

:::slidebreak
:::

## Operational Semantics

:::dev PotentialImprovement
BCP 21: I wonder if `seq` would be easier to work with if st' and
   st'' were swapped...
:::

Here is an informal definition of evaluation, presented as inference rules
for readability:

```display
                      -----------------                  (skip)
                      st =[ skip ]=> st

                      a.eval st = n
              --------------------------------           (asgn)
              st =[ x := a ]=> (x →ₜ n ; st)

                      st  =[ c₁ ]=> st'
                      st' =[ c₂ ]=> st''
                    ---------------------                (seq)
                    st =[ c₁;c₂ ]=> st''

                     b.eval st = true
                      st =[ c₁ ]=> st'
           --------------------------------------        (ifTrue)
           st =[ if b then c₁ else c₂ end ]=> st'

                    b.eval st = false
                      st =[ c₂ ]=> st'
           --------------------------------------        (ifFalse)
           st =[ if b then c₁ else c₂ end ]=> st'

                    b.eval st = false
               -----------------------------             (whileFalse)
               st =[ while b do c end ]=> st

                     b.eval st = true
                      st =[ c ]=> st'
             st' =[ while b do c end ]=> st''
             --------------------------------            (whileTrue)
             st  =[ while b do c end ]=> st''
```

Here is the formal definition.  Make sure you understand how it
corresponds to the inference rules.

```lean
inductive Com.EvalR : Com → State → State → Prop where
  | skip {st : State} : EvalR (imp {skip}) st st
  | asgn {st : State} {a : Aexp} {n : Nat} {x : Ident} (h : a.eval st = n) :
      EvalR (imp {x := a}) st (x →ₜ n ; st)
  | seq {c₁ c₂ : Com} {st st' st'' : State} (h₁ : EvalR c₁ st st') (h₂ : EvalR c₂ st' st'') :
      EvalR (imp {c₁; c₂}) st st''
  | ifTrue {st st' : State} {b : Bexp} {c₁ c₂ : Com} (hb : b.eval st = true)
      (hc : EvalR c₁ st st') :
      EvalR (imp {if (b) {c₁} else {c₂}}) st st'
  | ifFalse {st st' : State} {b : Bexp} {c₁ c₂ : Com} (hb : b.eval st = false)
      (hc : EvalR c₂ st st') :
      EvalR (imp {if (b) {c₁} else {c₂}}) st st'
  | whileFalse {b : Bexp} {st : State} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {while (b) {c}}) st st
  | whileTrue {st st' st'' : State} {b : Bexp} {c : Com} (hb : b.eval st = true)
      (hc : EvalR c st st') (hloop : Com.EvalR (imp {while (b) {c}}) st' st'') :
      EvalR (imp {while (b) {c}}) st st''
```

:::instructors
We define evaluation notation using a typeclass to make extending it easier in the Hoare chapter.
:::

:::instructors
Setting `In` and `Out` as `outParam`s is a hack to resolve various typeclass synthesis
problems, or at least I can't explain why it works.
:::

::::details "Notation encoding: commands"
```lean
class HasEval (Com : Type) (In : outParam <| Type) (Out : outParam <| Type) where
  Eval : Com → In → Out → Prop

namespace HasEval
/-- Evaluation: `st =[ c ]=> st'` with `imp_com` command syntax -/
scoped syntax:lead term " =[ " imp_com:min " ]=> " term : term
scoped macro_rules
  | `($st =[ $c:imp_com ]=> $st') => ``(HasEval.Eval (imp { $c }) $st $st')

namespace Delab
open Lean PrettyPrinter Delaborator SubExpr Imp.Delab
@[delab app.HasEval.Eval]
def delabTriple : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``HasEval.Eval 7
  let c ← withNaryArg 4 delab
  let st ← withNaryArg 5 delab
  let st' ← withNaryArg 6 delab
  match c with
  | `(imp { $c:imp_com }) => ``($st =[ $c ]=> $st')
  | c => ``($st =[ ~$c ]=> $st')
end Delab
end HasEval

open scoped HasEval

instance : HasEval Com State State where
  Eval := Com.EvalR

@[simp]
theorem Com.evalR_eq {c : Com} {st st' : State} :
    EvalR c st st' ↔ st =[ c ]=> st' := by rfl
```
::::

:::ignore
```lean -keep
#check ∅ =[ skip ]=> ∅
```
:::

The cost of defining evaluation as a relation instead of a function is
that we now need to construct a _proof_ that some program evaluates to
some result state, rather than letting Lean's computation mechanism do
it for us.

```lean
open scoped KVPair
open Com

example :
    ∅ =[
      X := 2;
      if (X ≤ 1) {
        Y := 3
      } else {
        Z := 4
      }
    ]=> {Z ↦ 4, X ↦ 2} := by
  -- To supply the intermediate state to the `seq` rule, which is sometimes necessary,
  -- we can write `Com.EvalR.seq (st' := ...)`.
  apply EvalR.seq (st' := {X ↦ 2})
  · exact EvalR.asgn rfl
  · apply EvalR.ifFalse
    · rfl
    · exact EvalR.asgn rfl
```

:::dev "Niklas Halonen (xhalo32)"
After `apply EvalR.seq (st' := {X ↦ 2})`, the infoview shows `imp {X := 2}.EvalR ∅ {X ↦ 2}` instead of `∅ =[ X := 2 ]=> {X ↦ 2}`.
It would be silly to use `apply EvalR.seq (st' := {X ↦ 2}) <;> try simp only [evalR_eq] at *`.
:::

Since the total map update notation (`→ₜ`) is difficult to type, we prefer to use the `{}`-notation with `KVPair`s.

In the above proof, using `EvalR.asgn rfl` is convenient because it computes the value of the right hand side and can use it to determine `st'`.

```lean
example {x : Nat} : ∅ =[ X := ~(.num x) ]=> {X ↦ x} := by
  apply EvalR.asgn
  -- `⊢ Aexp.eval ∅ x = (X ↦ x).value`, which we can prove with `simp` or `rfl`
  simp

example {x : Nat} : ∅ =[ X := ~(.num x) ]=> {X ↦ x} := by
  exact EvalR.asgn rfl

example : ∅ =[ X := 2; Y := 3 ]=> {Y ↦ 3, X ↦ 2} := by
  apply EvalR.seq
  · -- `⊢ imp {X := 2}.EvalR ∅ ?st'`
    exact EvalR.asgn rfl -- assigns the metavariable `?st'` to `{X ↦ 2}` (or equivalent)
  · simp only [Aexp.eval_num, evalR_eq]
    exact EvalR.asgn rfl
```

This is a case where `rfl` is more powerful than `simp`, because it can assign the `?st'` metavariable.
To demonstrate, here's a version with `simp`

```lean +error -keep
example : ∅ =[ X := 2; Y := 3 ]=> {Y ↦ 3, X ↦ 2} := by
  apply EvalR.seq
  · apply EvalR.asgn
    simp -- doesn't work because `simp` doesn't assign the metavariable
  · sorry
```

However, it's possible to use `simp` as long as we have assigned `st'` ourselves:

```lean
example : ∅ =[ X := 2; Y := 3 ]=> {Y ↦ 3, X ↦ 2} := by
  apply EvalR.seq (st' := {X ↦ 2})
  · apply EvalR.asgn
    simp
  · apply EvalR.asgn
    simp
```

::::::full
:::::exercise (rating := 2) (name := "ceval_example₂")
```lean
theorem ceval_example₂ :
    ∅ =[
      X := 0;
      Y := 1;
      Z := 2
    ]=> {Z ↦ 2, Y ↦ 1, X ↦ 0} := by
  solution!
    apply EvalR.seq (st' := {X ↦ 0}) -- Note: specifying the intermediate state is not necessary
    · apply EvalR.asgn rfl
    · apply EvalR.seq (st' := {Y ↦ 1, X ↦ 0}) -- Note: st' is not necessary
      · exact EvalR.asgn rfl
      · exact EvalR.asgn rfl
```

:::gradeTheorem 2 ceval_example₂
:::
:::::
::::::

:::terse
What sorts of things might we want to prove using these definitions?  Here are
some simple examples...
:::

:::dev
  PR: I phrased these quizzes with the following alternatives:
   (A) Not true
   (B) True and easily provable
   (C) True and takes more work to prove
   (D) True and cannot be proved without additional axioms
:::

::::quiz
Is the following proposition provable?

```display
∀ (c : Com) (st st' : State),
  st =[ skip; c ]=> st' →
  st =[ c ]=> st'
```

(A) Yes    (B) No    (C) Not sure

:::quizSolution
```lean
theorem quiz1_answer (c : Com) (st st' : State)
    (h : st =[ skip; c ]=> st') : st =[ c ]=> st' := by
  inversion h with
  | seq smid h₁ h₂ =>
    inversion h₁
    exact h₂
```
:::
::::

::::quiz
Is the following proposition provable?

```display
∀ (c₁ c₂ : Com) (st st' : State),
  st =[ c₁; c₂ ]=> st' →
  st =[ c₁ ]=> st →
  st =[ c₂ ]=> st'
```

(A) Yes    (B) No    (C) Not sure

:::instructors
Yes, but answer is given later (`quiz2_answer`) as it depends on `ceval_deterministic`.
:::
::::

::::quiz
Is the following proposition provable?

```display
∀ (b : Bexp) (c : Com) (st st' : State),
  st =[ if (b) { c } else { c } ]=> st' →
  st =[ c ]=> st'
```

(A) Yes    (B) No    (C) Not sure

:::quizSolution
```lean
theorem quiz3_answer (b : Bexp) (c : Com) (st st' : State)
    (h : st =[ if (b) { c } else { c } ]=> st') : st =[ c ]=> st' := by
  inversion h with
  | ifTrue hb hc => exact hc
  | ifFalse hb hc => exact hc
```
:::
::::

::::quiz
Is the following proposition provable?

```display
∀ (b : Bexp),
  (∀ st, b.eval st = true) →
  ∀ (c : Com) (st : State),
  ¬ ∃ st', st =[ while (b) { c } ]=> st'
```

(A) Yes    (B) No    (C) Not sure

:::quizSolution
```lean
-- This one is tricky!
theorem quiz4_answer (b : Bexp) (hbtrue : ∀ st, b.eval st = true)
    (c : Com) (st : State) : ¬ ∃ st', st =[ while (b) { c } ]=> st' := by
  rintro ⟨st', hev⟩
  have key : ∀ (cmd : Com) (s s' : State),
      (s =[ cmd ]=> s') → cmd = (imp { while (b) { c } }) → False := by
    intro cmd s s' hce
    induction hce with
    | @whileFalse b₀ s₀ c₀ hbf =>
        intro heq; injection heq with e₁ _; subst e₁
        rw [hbtrue s₀] at hbf; simp at hbf
    | @whileTrue s₀ s0' s0'' b₀ c₀ hbt hc0 hloop ih₁ ih₂ =>
        intro heq; exact ih₂ heq
    | @skip s₀ => intro heq; simp at heq
    | @asgn s₀ a n x h => intro heq; simp at heq
    | @seq d1 d2 s₀ s0' s0'' hh₁ hh₂ ih₁ ih₂ => intro heq; simp at heq
    | @ifTrue s₀ s0' b₀ d1 d2 hb0 hc0 ih => intro heq; simp at heq
    | @ifFalse s₀ s0' b₀ d1 d2 hb0 hc0 ih => intro heq; simp at heq
  exact key _ st st' hev rfl
```
:::
::::

::::quiz
Is the following proposition provable?

```display
∀ (b : Bexp) (c : Com) (st : State),
  (¬ ∃ st', st =[ while (b) { c } ]=> st') →
  ∀ st'', b.eval st'' = true
```

(A) Yes    (B) No    (C) Not sure

:::quizSolution
This claim is *false*, so it cannot be proved -- the proof gets
stuck immediately:

```lean +error
theorem quiz5_answer (b : Bexp) (c : Com) (st : State)
    (H : ¬ ∃ st', st =[ while (b) { c } ]=> st') :
    ∀ st'', b.eval st'' = true := by
  intro st''
  -- Can't make any progress -- the claim is false!
```
:::
::::

## Determinism of Evaluation

:::dev PotentialImprovement
Maybe this should go at the end of the file in a section marked
   optional? Not everybody will want to spend time on it.
:::

::::full
Changing from a computational to a relational definition of evaluation
is a good move because it frees us from the artificial requirement that
evaluation be a total function. But it raises a question: is the
relational definition really a partial _function_? Could the same
command, from the same state, evaluate to two different final states?
In fact this cannot happen: `Com.EvalR` _is_ a partial function.
::::

:::terse
Finally, we should pause to check that our evaluation relation really is a (partial) function...
:::

:::dev PotentialImprovement
Informal proof needed! (And one can surely be found in some past
   CIS500 exam solutions!)
:::

```lean
theorem ceval_deterministic {c : Com} {st st1 st2 : State}
    (e₁ : st =[ c ]=> st1) (e₂ : st =[ c ]=> st2) : st1 = st2 := by
  induction e₁ generalizing st2 with
  | skip =>
      inversion e₂
      rfl
  | asgn =>
      inversion e₂ with
      | asgn h' => subst_vars; rfl
  | seq h₁ h₂ ih₁ ih₂ =>
      inversion e₂ with
      | seq st2' h₁' h₂' =>
          apply ih₁ at h₁'; subst h₁'
          exact ih₂ h₂'
  | ifTrue hb hc ih =>
      inversion e₂ with
      | ifTrue hb' hc' => exact ih hc'
      | ifFalse hb' hc' => simp_all
  | ifFalse hb hc ih =>
      inversion e₂ with
      | ifTrue hb' hc' => simp_all
      | ifFalse hb' hc' => exact ih hc'
  | whileFalse hb =>
      inversion e₂ with
      | whileFalse hb' => rfl
      | whileTrue hb' hc' hl' => simp_all
  | whileTrue hb hc hloop ih₁ ih₂ =>
      inversion e₂ with
      | whileFalse hb' => simp_all
      | whileTrue st2' _ hc' hl' =>
          apply ih₁ at hc'; subst hc'
          exact ih₂ hl'
```

::::hide
```lean
/- Answer to the second quiz above (deferred because it depends on
   `ceval_deterministic`). -/
theorem quiz2_answer (c₁ c₂ : Com) (st st' : State)
    (h₁ : st =[ c₁; c₂ ]=> st') (h₂ : st =[ c₁ ]=> st) : st =[ c₂ ]=> st' := by
  inversion h₁ with
  | seq smid hc₁ hc₂ =>
    have hmid : smid = st := ceval_deterministic hc₁ h₂
    subst hmid
    exact hc₂
```
::::

::::::full
:::::exercise (rating := 3) (name := "pupToN") (optional := true)
Write an Imp program that sums the numbers from {lean}`1` to {lean}`X` (inclusive)
in the variable {lean}`Y`.  Your program should update the state as shown in
`pup_to_2_ceval`, which you can reverse-engineer to discover the program
you should write.  The proof of that theorem will be somewhat lengthy.

```lean
def pupToN : Com := solution!(
  imp {
    Y := 0;
    while (1 ≤ X) {
      Y := Y + X;
      X := X - 1
    }
  })
```

:::hide
   Result is the same as `(X →ₜ 0 ; Y →ₜ 3)` if one admits
   functional extensionality.
:::

```lean
theorem pup_to_2_ceval :
    {X ↦ 2} =[ pupToN ]=> {X ↦ 0, Y ↦ 3, X ↦ 1, Y ↦ 2, Y ↦ 0, X ↦ 2} := by
  solution!
    rw [pupToN]
    apply Com.EvalR.seq (st' := (Y →ₜ 0 ; X →ₜ 2 ; ∅))
    · apply Com.EvalR.asgn; rfl
    · apply Com.EvalR.whileTrue (st' := (X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅))
      · rfl
      · apply Com.EvalR.seq (st' := (Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅)) <;>
          (apply Com.EvalR.asgn; rfl)
      · apply Com.EvalR.whileTrue
          (st' := (X →ₜ 0 ; Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅))
        · rfl
        · apply Com.EvalR.seq (st' := (Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅)) <;>
            (apply Com.EvalR.asgn; rfl)
        · apply Com.EvalR.whileFalse; rfl
```
:::::
::::::

:::dev PotentialImprovement
Comment from reader: Another good place to mention lack of
   functional extensionality.  The 6 `→ₜ`/`t_update`s in the above theorem
   are not redundant, nor would `pup_to_2_ceval` be provable if the
   algorithm were defined differently (e.g., if it used `Z` as a "buffer"
   variable instead of decrementing `X`).
:::

# Reasoning About Imp Programs

:::dev PotentialImprovement
This section doesn't seem very useful -- to anybody! It takes too
   much time to go through it in class, and even for advanced students it's
   too low-level and grubby to be a very convincing motivation for what
   follows -- i.e., to feel motivated by its grubbiness, you have to
   understand it, but this takes more time than it's worth. Better to cut
   the whole rest of the file (except the further exercises at the very end),
   or at least make it optional.
   (BCP 10/18: However, this removes quite a few exercises. Is the homework
   assignment still meaty enough? I'm going to leave it as-is for now, but
   we should reconsider this later.)
:::

::::full
We'll get into more systematic and powerful techniques for reasoning
about Imp programs in the next chapter, but we can
already do a few things (albeit in a somewhat low-level way) just by
working with the bare definitions. This section explores some examples.
::::

```lean
theorem plus2_spec {st : State} {n : Nat} {st' : State}
    (hx : st[X] = n) (heval : st =[ plus2 ]=> st') :
    st'[X] = n + 2 := by
  -- Inverting `heval` forces one step of the evaluation relation: since
  -- `plus2` is an assignment, `st'` must be `st` extended at `X`.
  rw [plus2] at heval
  inversion heval with
  | asgn m h =>
    simp [hx] at h ⊢
    lia
```

:::dev PotentialImprovement
This used to be recommended.  Should it be reinstated?
:::

::::::full
:::::exercise (rating := 3) (name := "XtimesYinZ_spec") (optional := true) (manual := true)
State and prove a specification of {name}`XtimesYinZ`.

```lean
-- SOLUTION
/- Here is a specification in the style of `plus2_spec`: -/
theorem XtimesYinZ_spec₁ {st : State} {nx ny : Nat} {st' : State}
    (hx : st[X] = nx) (hy : st[Y] = ny) (heval : st =[ XtimesYinZ ]=> st') :
    st'[Z] = nx * ny := by
  rw [XtimesYinZ] at heval
  inversion heval with
  | asgn n h =>
    simp_all

/- Though perhaps a cleaner specification would be: -/
theorem XtimesYinZ_spec {st : State} :
    st =[ XtimesYinZ ]=> (Z →ₜ st[X] * st[Y] ; st) := by
  rw [XtimesYinZ]
  apply EvalR.asgn
  rfl

/- A less informative specification would be ... -/
theorem XtimesYinZ_spec₂ {st : State} : ∃ st', st =[ XtimesYinZ ]=> st' := by
  exists (Z →ₜ st[X] * st[Y] ; st)
  exact XtimesYinZ_spec
-- END SOLUTION
```

:::grade
```
GRADE_MANUAL 3: XtimesYinZ_spec
```
:::
:::::
::::::

:::dev "Niklas Halonen (xhalo32)"
We need to explain the `generalize` tactic.
I've changed some Hoare proofs from `have key` to `generalize` but the tactic hasn't been explained yet.
:::

:::dev "One An (meluge)"
At least currently, it looks like `generalize` is introduced in `Automation.lean`.
Are we doing anything different here with `generalize` that is
unexplained there?
:::

::::::full
:::::exercise (rating := 3) (name := "loop_never_stops")
Hint: proceed by induction on the assumed derivation showing that {name}`loop`
terminates.  Most of the cases are immediately contradictory and so can be
solved in one step (by {tactic}`simp`/{tactic}`contradiction` on the impossible command
equation).

```lean
theorem loop_never_stops (st st' : State) : ¬ (st =[ loop ]=> st') := by
  solution!
    intro contra
    -- Generalize over the command so the induction remembers what `loop` is.
    have key : ∀ (c : Com) (s s' : State), (s =[ c ]=> s') → c = loop → False := by
      intro c s s' hce; simp only [loop] at *
      induction hce with (intro heq; try contradiction)
      | whileFalse hb =>
          injection heq with e₁ _
          subst e₁; simp at hb
    exact key loop st st' contra rfl
```

:::gradeTheorem 3 loop_never_stops
:::
:::::
::::::

:::dev PotentialImprovement
Marc Bezem 2022:
   There are trade-offs between using tactics and additional lemmas. Here is
   a case where a lemma would make things clearer. For `loop_never_stops`,
   the surprise is that it is proved by induction, and the Rocq tactic
   `remember` is hard to understand. The following formulation explains the
   induction better:

```
     Theorem loop_never_stops' : forall st st' c,
       st =[ c ]=> st' -> c = loop -> False.
```

   The equivalence of the two formulations is an easy lemma.  (Note: the Lean
   proof above already takes exactly this generalized-`key` shape.)
   BCP 23: Not sure I see a big difference between the two presentations: both
   statements are negations, and the `remember` in the proof is avoided in
   the new one by introducing an equality in the theorem statement that IMO
   is not very pretty...
:::

::::::full
:::::exercise (rating := 3) (name := "no_whiles_eqv")
The following function yields {name}`true` just on programs with no while
loops. Using `inductive`, write a property `Com.NoWhilesR` that holds
exactly when `c` is while-free, then prove it equivalent to `Com.no_whiles`.

```lean
def Com.no_whiles (c : Com) : Bool :=
  match c with
  | imp {skip} => true
  | imp {x := ~a} => true
  | imp {c₁; c₂} => no_whiles c₁ && no_whiles c₂
  | imp {if (b) {ct} else {cf}} => no_whiles ct && no_whiles cf
  | imp {while (b) {c}} => false

inductive Com.NoWhilesR : Com → Prop where
  -- SOLUTION
  | skip : Com.NoWhilesR (imp { skip })
  | asgn {x : Ident} {a : Aexp} : Com.NoWhilesR (imp { x := ~a })
  | seq {c₁ c₂ : Com} (h₁ : Com.NoWhilesR c₁) (h₂ : Com.NoWhilesR c₂) :
      Com.NoWhilesR (imp { c₁; c₂ })
  | cond {b : Bexp} {c₁ c₂ : Com} (h₁ : Com.NoWhilesR c₁) (h₂ : Com.NoWhilesR c₂) :
      Com.NoWhilesR (imp { if (b) { c₁ } else { c₂ } })
  -- END SOLUTION

theorem no_whiles_eqv (c : Com) : c.no_whiles = true ↔ Com.NoWhilesR c := by
  solution!
    constructor
    · induction c with (intro h <;> try constructor <;> simp_all [Com.no_whiles, Bool.and_eq_true])
      | whileDo b c ih => simp [Com.no_whiles] at h
    · intro h
      induction h with simp_all [Com.no_whiles]
```

:::autogradedHole Com.NoWhilesR
:::

:::gradeTheorem 3 no_whiles_eqv
:::
:::::
::::::

::::::full
:::::exercise (rating := 4) (name := "no_whiles_terminating")
Imp programs that don't involve while loops always terminate.  State and
prove a theorem `no_whiles_terminating` that says this.  Use either
{name}`Com.no_whiles` or {name}`Com.NoWhilesR`, as you prefer.

```lean
theorem no_whiles_terminating {c : Com} (st : State) (h : Com.NoWhilesR c) :
    ∃ st', st =[ ~c ]=> st' := by
  solution!
    induction h generalizing st with
    | skip => exists st; constructor
    | @asgn x a => exists (x →ₜ a.eval st ; st); constructor; rfl
    | seq h₁ h₂ ih₁ ih₂ =>
        obtain ⟨st', hc₁⟩ := ih₁ st
        obtain ⟨st'', hc₂⟩ := ih₂ st'
        exists st''; constructor <;> assumption
    | @cond b c₁ c₂ h₁ h₂ ih₁ ih₂ =>
        cases hb : b.eval st with
        | true =>
            obtain ⟨st', hc₁⟩ := ih₁ st
            exists st'; constructor <;> assumption
        | false =>
            obtain ⟨st', hc₂⟩ := ih₂ st
            exists st'; apply Com.EvalR.ifFalse <;> assumption
```

:::solution
And here is an alternative solution by induction on `c` (using
{name}`Com.no_whiles` instead of {name}`Com.NoWhilesR`):

```lean
theorem no_whiles_terminating' (c : Com) (st1 : State)
    (hb : c.no_whiles = true) : ∃ st2, st1 =[ c ]=> st2 := by
  induction c generalizing st1 with
  | skip => exists st1; constructor
  | asgn x a => exists (x →ₜ a.eval st1 ; st1); constructor; rfl
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Com.no_whiles, Bool.and_eq_true] at hb
      obtain ⟨st1', hc₁⟩ := ih₁ st1 hb.1
      obtain ⟨st1'', hc₂⟩ := ih₂ st1' hb.2
      exists st1''; constructor <;> assumption
  | cond b ct cf ih₁ ih₂ =>
      simp only [Com.no_whiles, Bool.and_eq_true] at hb
      cases hbev : b.eval st1 with
      | true =>
          obtain ⟨st2, h⟩ := ih₁ st1 hb.1
          exists st2; constructor <;> assumption
      | false =>
          obtain ⟨st2, h⟩ := ih₂ st1 hb.2
          exists st2; apply Com.EvalR.ifFalse <;> assumption
  | whileDo b c ih => simp [Com.no_whiles] at hb
```
:::

:::grade
```
GRADE_MANUAL 6: no_whiles_terminating
```
:::
:::::
::::::

# Case Study (Optional)

Recall the factorial program (broken up into smaller pieces this
time, for convenience of proving things about it).

```lean
def factBody : Com := imp {
  Y := Y * Z;
  Z := Z - 1
}

def factLoop : Com := imp {
  while (Z ≠ 0) {
    ~factBody
  }
}

def factCom : Com := imp {
  Z := X;
  Y := 1;
  ~factLoop
}
```

Here is an alternative "mathematical" definition of the factorial
function:

```lean
def realFact (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n' + 1 => (n' + 1) * realFact n'
```

We would like to show that they agree -- if we start `factCom` in
a state where variable `X` contains some number `n`, then it will
terminate in a state where variable `Y` contains the factorial of
`n`.

To show this, we rely on the critical idea of a _loop
invariant_.

```lean
def FactInvariant (n : Nat) (st : State) : Prop :=
  st[Y] * realFact st[Z] = realFact n
```

We show that the body of the factorial loop preserves the invariant:

:::dev PotentialImprovement
Needs an informal proof!
:::

```lean
theorem factBody_preserves_invariant {st st' : State} {n : Nat}
    (hinv : FactInvariant n st) (hz : st[Z] ≠ 0)
    (heval : st =[ ~factBody ]=> st') :
    FactInvariant n st' := by
  rw [FactInvariant] at hinv ⊢
  rw [factBody] at heval
  inversion heval with
  | seq _ h₁ h₂ =>
    inversion h₁ with
    | asgn hy =>
      inversion h₂ with
      | asgn hz' =>
        subst hy hz'
        have hyz : Y ≠ Z := by decide
        have hzy : Z ≠ Y := by decide
        simp [hyz, hzy]
        -- Show that `st[Z] = z + 1` for some `z`
        cases hzz : st[Z] with
        | zero => contradiction
        | succ z =>
          rw [hzz, realFact] at hinv
          rw [Nat.add_sub_cancel, Nat.mul_assoc]
          exact hinv
```

From this, we can show that the whole loop also preserves the
invariant:

```lean
theorem factLoop_preserves_invariant {st st' : State} {n : Nat}
    (hinv : FactInvariant n st) (heval : st =[ ~factLoop ]=> st') :
    FactInvariant n st' := by
  generalize heq : factLoop = c at heval
  induction heval with
  | whileFalse hb =>
    -- trivial when the loop doesn't run...
    exact hinv
  | @whileTrue st st' st'' b c hb hc hloop ih₁ ih₂ =>
    -- if the loop does run, we know that `factBody` preserves
    -- `FactInvariant` -- we just need to assemble the pieces
    rw [factLoop] at heq
    injection heq with hb' hc'
    subst hb' hc'
    have hz : st[Z] ≠ 0 := by
      intro hz
      simp [hz] at hb
    exact ih₂ (factBody_preserves_invariant hinv hz hc) rfl
  | skip | asgn | seq | ifTrue | ifFalse => simp [factLoop] at heq
```

Next, we show that, for any loop, if the loop terminates, then the
condition guarding the loop must be false at the end:

```lean
theorem guard_false_after_loop {b : Bexp} {c : Com} {st st' : State}
    (heval : st =[ while (~b) {~c} ]=> st') :
    b.eval st' = false := by
  generalize heq : (imp { while (~b) {~c} }) = cmd at heval
  induction heval with
  | whileFalse hb =>
    injection heq with hb' _
    subst hb'
    exact hb
  | whileTrue _ _ _ _ ih₂ => exact ih₂ heq
  | skip | asgn | seq | ifTrue | ifFalse => simp at heq
```

Finally, we can patch it all together...

```lean
theorem factCom_correct {st st' : State} {n : Nat}
    (hx : st[X] = n) (heval : st =[ ~factCom ]=> st') :
    st'[Y] = realFact n := by
  rw [factCom] at heval
  inversion heval with
  | seq _ h₁ h₂ =>
    inversion h₁ with
    | asgn hz =>
      inversion h₂ with
      | seq _ h₃ h₄ =>
        inversion h₃ with
        | asgn hy =>
          subst hz hy
          -- The invariant is true before the loop runs...
          have hinv : FactInvariant n (Y →ₜ 1 ; Z →ₜ st[X] ; st) := by
            have hyz : Y ≠ Z := by decide
            simp [FactInvariant, hyz, hx]
          -- ...so when the loop is done running, the invariant
          -- is maintained
          have hinv' := factLoop_preserves_invariant hinv h₄
          -- Finally, if the loop terminated, then `Z` is `0`; so `Y` must be
          -- factorial of `X`
          rw [factLoop] at h₄
          have hz := guard_false_after_loop h₄
          simp at hz
          rw [FactInvariant, hz, realFact, Nat.mul_one] at hinv'
          exact hinv'
```

One might wonder whether all this work with poking at states and
unfolding definitions could be ameliorated with some more powerful
lemmas and/or more uniform reasoning principles... Indeed, this is
exactly the point of the {ref "Hoare"}[Hoare] chapters!

:::::full
::::exercise (rating := 4) (name := "subtract_slowly_spec") (optional := true)
Prove a specification for `subtract_slowly`, using the above
specification of `factCom` and the invariant below as
guides.

```lean
def SsInvariant (n z : Nat) (st : State) : Prop :=
  st[Z] - st[X] = z - n

-- SOLUTION
theorem ss_body_preserves_invariant {st st' : State} {n z : Nat}
    (hinv : SsInvariant n z st) (hx : st[X] ≠ 0)
    (heval : st =[ ~subtract_slowly_body ]=> st') :
    SsInvariant n z st' := by
  rw [SsInvariant] at hinv ⊢
  rw [subtract_slowly_body] at heval
  inversion heval with
  | seq _ h₁ h₂ =>
    inversion h₁ with
    | asgn hz =>
      inversion h₂ with
      | asgn hx' =>
        subst hz hx'
        have hzx : Z ≠ X := by decide
        have hxz : X ≠ Z := by decide
        simp [hzx, hxz]
        lia -- Interestingly, this is all we need here!

theorem ss_preserves_invariant {st st' : State} {n z : Nat}
    (hinv : SsInvariant n z st) (heval : st =[ ~subtract_slowly ]=> st') :
    SsInvariant n z st' := by
  generalize heq : subtract_slowly = c at heval
  induction heval with
  | whileFalse hb => exact hinv
  | @whileTrue st st' st'' b c hb hc hloop ih₁ ih₂ =>
    rw [subtract_slowly] at heq
    injection heq with hb' hc'
    subst hb' hc'
    have hx : st[X] ≠ 0 := by
      intro hx
      simp [hx] at hb
    exact ih₂ (ss_body_preserves_invariant hinv hx hc) rfl
  | skip | asgn | seq | ifTrue | ifFalse => simp [subtract_slowly] at heq

theorem ss_correct {st st' : State} {n z : Nat}
    (hx : st[X] = n) (hz : st[Z] = z) (heval : st =[ ~subtract_slowly ]=> st') :
    st'[Z] = z - n := by
  have hinv : SsInvariant n z st := by
    simp [SsInvariant, hx, hz]
  have hinv' := ss_preserves_invariant hinv heval
  rw [subtract_slowly] at heval
  have hx' := guard_false_after_loop heval
  simp at hx'
  rw [SsInvariant] at hinv'
  simp [hx'] at hinv'
  exact hinv'
-- END SOLUTION
```
::::
:::::

## Additional Exercises

::::exercise (rating := 3) (name := "stack_compiler") (checkVisibility := false)
Old HP Calculators, programming languages like Forth and Postscript,
and abstract machines like the Java Virtual Machine all evaluate
arithmetic expressions using a _stack_. For instance, the expression

```display
(2*3)+(3*(4-2))
```

would be written as

```display
      2 3 * 3 4 2 - * +
```

and evaluated like this (where we show the program being evaluated
on the right and the contents of the stack on the left):

```
      [ ]           |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |
```

The goal of this exercise is to write a small compiler that
translates `aexp`s into stack machine instructions.

The instruction set for our stack language will consist of the
following instructions:
    - `sPush n`: Push the number `n` on the stack.
    - `sLoad x`: Load the identifier `x` from the store and push it
                on the stack
    - `sPlus`:   Pop the two top numbers from the stack, add them, and
                push the result onto the stack.
    - `sMinus`:  Similar, but subtract the first number from the second.
    - `sMult`:   Similar, but multiply.

```lean
namespace StackCompiler

inductive Sinstr : Type where
  | sPush (n : Nat)
  | sLoad (x : String)
  | sPlus
  | sMinus
  | sMult

open Sinstr
```

Write a function to evaluate programs in the stack language. It
should take as input a state, a stack represented as a list of
numbers (top stack item is the head of the list), and a program
represented as a list of instructions, and it should return the
stack after executing the program.  Test your function on the
examples below.

Note that it is unspecified what to do when encountering an
{name}`sPlus`, {name}`sMinus`, or {name}`sMult` instruction if the stack contains
fewer than two elements.  In a sense, it is immaterial what we do,
since a correct compiler will never emit such a malformed program.
But for sake of later exercises, it would be best to skip the
offending instruction and continue with the next one.

```lean
def sExecute (st : State) (stack : List Nat) (prog : List Sinstr) : List Nat :=
  solution!(match prog, stack with
    | [],               _                => stack
    | sPush n :: prog', _                => sExecute st (n :: stack) prog'
    | sLoad x :: prog', _                => sExecute st (st[x] :: stack) prog'
    | sPlus   :: prog', n :: m :: stack' => sExecute st ((m + n) :: stack') prog'
    | sMinus  :: prog', n :: m :: stack' => sExecute st ((m - n) :: stack') prog'
    | sMult   :: prog', n :: m :: stack' => sExecute st ((m * n) :: stack') prog'
    -- Bad state: skip the instruction
    | _       :: prog', _                => sExecute st stack prog')

-- SOLUTION
@[simp] theorem sExecute_nil (st : State) (stack : List Nat) :
    sExecute st stack [] = stack := rfl
@[simp] theorem sExecute_push (st : State) (stack : List Nat) (n : Nat) (prog' : List Sinstr) :
    sExecute st stack (sPush n :: prog') = sExecute st (n :: stack) prog' := rfl
@[simp] theorem sExecute_load (st : State) (stack : List Nat) (x : String) (prog' : List Sinstr) :
    sExecute st stack (sLoad x :: prog') = sExecute st (st[x] :: stack) prog' := rfl
@[simp] theorem sExecute_plus (st : State) (n m : Nat) (stack' : List Nat) (prog' : List Sinstr) :
    sExecute st (n :: m :: stack') (sPlus :: prog') = sExecute st ((m + n) :: stack') prog' := rfl
@[simp] theorem sExecute_minus (st : State) (n m : Nat) (stack' : List Nat) (prog' : List Sinstr) :
    sExecute st (n :: m :: stack') (sMinus :: prog') = sExecute st ((m - n) :: stack') prog' := rfl
@[simp] theorem sExecute_mult (st : State) (n m : Nat) (stack' : List Nat) (prog' : List Sinstr) :
    sExecute st (n :: m :: stack') (sMult :: prog') = sExecute st ((m * n) :: stack') prog' := rfl
@[simp] theorem sExecute_plus_bad (st : State) (stack : List Nat) (prog' : List Sinstr)
    (hs : stack.length < 2) :
    sExecute st stack (sPlus :: prog') = sExecute st stack prog' := by
  rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> trivial
@[simp] theorem sExecute_minus_bad (st : State) (stack : List Nat) (prog' : List Sinstr)
    (hs : stack.length < 2) :
    sExecute st stack (sMinus :: prog') = sExecute st stack prog' := by
  rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> trivial
@[simp] theorem sExecute_mult_bad (st : State) (stack : List Nat) (prog' : List Sinstr)
    (hs : stack.length < 2) :
    sExecute st stack (sMult :: prog') = sExecute st stack prog' := by
  rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> trivial
-- END SOLUTION

theorem sExecute1 : sExecute ∅ [] [sPush 5, sPush 3, sPush 1, sMinus] = [2, 5] := by
  solution!
    rfl

theorem sExecute2 : sExecute {X ↦ 3} [3, 4] [sPush 4, sLoad X, sMult, sPlus] = [15, 4] := by
  solution!
    rfl
```

:::autogradedHole sExecute
:::

:::gradeTheorem 1 sExecute1
:::

:::gradeTheorem "0.5" sExecute2
:::

Next, write a function that compiles an {name}`Aexp` into a stack
machine program. The effect of running the program should be the
same as pushing the value of the expression on the stack.

```lean
def sCompile (a : Aexp) : List Sinstr :=
  solution!(match a with
  | .num n        => [sPush n]
  | .id x         => [sLoad x]
  | .plus a₁ a₂   => sCompile a₁ ++ sCompile a₂ ++ [sPlus]
  | .minus a₁ a₂  => sCompile a₁ ++ sCompile a₂ ++ [sMinus]
  | .mult a₁ a₂   => sCompile a₁ ++ sCompile a₂ ++ [sMult])

-- SOLUTION
@[simp] theorem sCompile_num (n : Nat) : sCompile (.num n) = [sPush n] := rfl
@[simp] theorem sCompile_id (x : String) : sCompile (.id x) = [sLoad x] := rfl
@[simp] theorem sCompile_plus (a₁ a₂ : Aexp) :
    sCompile (.plus a₁ a₂) = sCompile a₁ ++ sCompile a₂ ++ [sPlus] := rfl
@[simp] theorem sCompile_minus (a₁ a₂ : Aexp) :
    sCompile (.minus a₁ a₂) = sCompile a₁ ++ sCompile a₂ ++ [sMinus] := rfl
@[simp] theorem sCompile_mult (a₁ a₂ : Aexp) :
    sCompile (.mult a₁ a₂) = sCompile a₁ ++ sCompile a₂ ++ [sMult] := rfl
-- END SOLUTION
```

After you've defined `sCompile`, prove the following to test that it works.

```lean
theorem sCompile1 : sCompile (aexp { X - (2 * Y) }) = [sLoad X, sPush 2, sLoad Y, sMult, sMinus] := by
  solution!
    rfl
```

:::autogradedHole sCompile
:::

:::gradeTheorem "1.5" sCompile1
:::
::::

::::exercise (rating := 3) (name := "execute_app") (checkVisibility := false)
Execution can be decomposed in the following sense: executing
stack program `p₁ ++ p₂` is the same as executing `p₁`, taking
the resulting stack, and executing `p₂` from that stack. Prove
that fact.

```lean
theorem execute_app (st : State) (p₁ p₂ : List Sinstr) (stack : List Nat) :
    sExecute st stack (p₁ ++ p₂) = sExecute st (sExecute st stack p₁) p₂ := by
  solution!
    induction p₁ generalizing p₂ stack with
    | nil => rfl
    | cons a p' ih =>
      cases a with
      | sPush | sLoad => simp_all
      | sPlus | sMinus | sMult =>
        if hs : stack.length < 2 then
          simp [hs, ih]
        else
          rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> simp_all
```

:::gradeTheorem 3 execute_app
:::
::::

::::exercise (rating := 3) (name := "compiler_correct") (checkVisibility := false)
Now we'll prove the correctness of the compiler implemented in the
previous exercise.  Begin by proving the following lemma. If it
becomes difficult, consider whether your implementation of
`sExecute` or `sCompile` could be simplified.

```lean
theorem sCompile_correct_aux (st : State) (a : Aexp) (stack : List Nat) :
    sExecute st stack (sCompile a) = Aexp.eval st a :: stack := by
  solution!
    induction a generalizing st stack with (simp_all [List.append_assoc, execute_app] <;> rfl)
```

The main theorem should be a very easy corollary of that lemma.

```lean
theorem sCompile_correct (st : State) (a : Aexp) :
    sExecute st [] (sCompile a) = [Aexp.eval st a] := by
  solution!
    exact sCompile_correct_aux st a []

end StackCompiler
```

:::gradeTheorem "2.5" StackCompiler.sCompile_correct_aux
:::

:::gradeTheorem "0.5" StackCompiler.sCompile_correct
:::
::::

:::::full
::::exercise (rating := 3) (name := "short_circuit") (optional := true)
Most modern programming languages use a "short-circuit" evaluation
rule for boolean `and`: to evaluate `Bexp.and b₁ b₂`, first evaluate
`b₁`.  If it evaluates to {name}`false`, then the entire `and`
expression evaluates to {name}`false` immediately, without evaluating
`b₂`.  Otherwise, `b₂` is evaluated to determine the result of the
`and` expression.

Write an alternate version of {name}`Bexp.eval` that performs short-circuit
evaluation of `Bexp.and` in this manner, and prove that it is
equivalent to {name}`Bexp.eval`.  (N.b. This is only true because expression
evaluation in Imp is rather simple.  In a bigger language where
evaluating an expression might diverge, the short-circuiting `and`
would _not_ be equivalent to the original, since it would make more
programs terminate.)

:::dev PotentialImprovement
This exercise turned out to be easier than we intended!
:::

```lean
def Bexp.evalSC (st : State) (b : Bexp) : Bool := solution!(
  match b with
  | .bool b      =>  b
  | .eq   a₁ a₂  =>  a₁.eval st == a₂.eval st
  | .neq  a₁ a₂  =>  a₁.eval st != a₂.eval st
  | .le   a₁ a₂  =>  decide (a₁.eval st ≤ a₂.eval st)
  | .gt   a₁ a₂  =>  decide (a₁.eval st > a₂.eval st)
  | .not  b₁     =>  !b₁.evalSC st
  | .and  b₁ b₂  =>  match (b₁.evalSC st) with
                    | false => false
                    | true => b₂.evalSC st)

-- SOLUTION
@[simp] theorem Bexp.evalSC_bool (st : State) (b : Bool) : (bool b).evalSC st = b := rfl
@[simp] theorem Bexp.evalSC_eq (st : State) (a₁ a₂ : Aexp) :
    (eq a₁ a₂).evalSC st = (a₁.eval st == a₂.eval st) := rfl
@[simp] theorem Bexp.evalSC_neq (st : State) (a₁ a₂ : Aexp) :
    (neq a₁ a₂).evalSC st = (a₁.eval st != a₂.eval st) := rfl
@[simp] theorem Bexp.evalSC_le (st : State) (a₁ a₂ : Aexp) :
    (le a₁ a₂).evalSC st = decide (a₁.eval st ≤ a₂.eval st) := rfl
@[simp] theorem Bexp.evalSC_gt (st : State) (a₁ a₂ : Aexp) :
    (gt a₁ a₂).evalSC st = decide (a₁.eval st > a₂.eval st) := rfl
@[simp] theorem Bexp.evalSC_not (st : State) (b : Bexp) :
    (not b).evalSC st = !b.evalSC st := rfl
@[simp] theorem Bexp.evalSC_and (st : State) (b₁ b₂ : Bexp) :
    (and b₁ b₂).evalSC st =
      match b₁.evalSC st with
      | false => false
      | true => b₂.evalSC st := rfl
-- END SOLUTION

theorem Bexp.eval_eq_evalSC (st : State) (b : Bexp) :
    b.eval st = b.evalSC st := by
  solution!
    induction b <;> simp_all <;> lia
```
::::
:::::

:::::full
::::exercise (rating := 3) (name := "break_imp") (optional := true)
Imperative languages like C and Java often include a `break` or
similar statement for interrupting the execution of loops. In this
exercise we consider how to add `break` to Imp.  First, we need to
enrich the language of commands with an additional case. Because `break`
is a reserved keyword in Lean, we will abbreviate it as `brk`.

```lean
namespace Imp.Break

inductive Com where
  | skip
  | brk                          -- <--- NEW
  | asgn (x : Ident) (a : Aexp)
  | seq (c₁ c₂ : Com)
  | cond (b : Bexp) (c₁ c₂ : Com)
  | whileDo (b : Bexp) (c : Com)
```

:::details "Notation encoding: commands, macro rules"
```lean
namespace Com

open Lean

scoped macro_rules
  | `(imp { $s }) => do
    let stx ← match s with
      | `(imp_com| skip) => ``(Com.skip)
      | `(imp_com| brk) => ``(Com.brk)
      | `(imp_com| $x:ident) => ``(($x : Com))
      | `(imp_com| $c₁ ; $c₂) =>
        ``(Com.seq (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| $x:ident := $a) =>
        ``(Com.asgn $x (aexp {$a}))
      | `(imp_com| if ($b) {$c₁} else {$c₂}) =>
        ``(Com.cond (bexp {$b}) (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| while ($b) {$c}) =>
        ``(Com.whileDo (bexp {$b}) (imp {$c}))
      | `(imp_com| ~$c) => `(($c : Com))
      | _ => Macro.throwUnsupported
    return Imp.Elab.withSourceInfoOf s stx

end Com

open scoped Com

namespace Delab
open Lean PrettyPrinter Imp.Delab

@[app_unexpander Com.brk]
private def unexpandComBrk : Unexpander
  | _ => `(imp { $(mkIdent `brk):ident })

attribute [app_unexpander Com.skip] unexpandComSkip
attribute [app_unexpander Com.asgn] unexpandComAsgn
attribute [app_unexpander Com.seq] unexpandComSeq
attribute [app_unexpander Com.cond] unexpandComCond
attribute [app_unexpander Com.whileDo] unexpandComWhileDo

end Delab
```

```lean
/-- info: imp {brk} : Com -/
#guard_msgs in
#check imp {brk}
```
:::

Next, we need to define the behavior of `brk`.  Informally,
whenever `brk` is executed in a sequence of commands, it stops
the execution of that sequence and signals that the innermost
enclosing loop should terminate.  (If there aren't any
enclosing loops, then the whole program simply terminates.)  The
final state should be the same as the one in which the `brk`
statement was executed.

One important point is what to do when there are multiple loops
enclosing a given `brk`. In those cases, `brk` should only
terminate the _innermost_ loop. Thus, after executing the
following...

```display
    X := 0;
    Y := 1;
    while (0 <> Y) {
      while (true) {
        break
      };
      X := 1;
      Y := Y - 1
    }
```

... the value of `X` should be {lean}`1`, and not {lean}`0`.

One way of expressing this behavior is to add another parameter to
the evaluation relation that specifies whether evaluation of a
command executes a `brk` statement:

```lean
inductive Result : Type where
  | sContinue
  | sBreak

open Result
```

We will use the syntax `st =[ c ]=> st' // s` to mean that, if `c` is started in
state `st`, then it terminates in state `st'` and either signals
that the innermost surrounding loop (or the whole program) should
exit immediately (`s = sBreak`) or that execution should continue
normally (`s = sContinue`).

The definition of the `st =[ c ]=> st' // s` relation is very
similar to the one we gave above for the regular evaluation
relation (`st =[ c ]=> st'`) -- we just need to handle the
termination signals appropriately:

- If the command is `skip`, then the state doesn't change and
  execution of any enclosing loop can continue normally.

- If the command is `brk`, the state stays unchanged but we
  signal a {name}`sBreak`.

- If the command is an assignment, then we update the binding for
  that variable in the state accordingly and signal that execution
  can continue normally.

- If the command is of the form `if (b) {c₁} else {c₂}`, then
  the state is updated as in the original semantics of Imp, except
  that we also propagate the signal from the execution of
  whichever branch was taken.

- If the command is a sequence `c₁ ; c₂`, we first execute
  `c₁`.  If this yields a  {name}`sBreak`, we skip the execution of `c₂`
  and propagate the  {name}`sBreak` signal to the surrounding context;
  the resulting state is the same as the one obtained by
  executing `c₁` alone. Otherwise, we execute `c₂` on the state
  obtained after executing `c₁`, and propagate the signal
  generated there.

- Finally, for a loop of the form `while (b) {c}`, the
  semantics is almost the same as before. The only difference is
  that, when `b` evaluates to {name}`true`, we execute `c` and check the
  signal that it raises.  If that signal is {name}`sContinue`, then the
  execution proceeds as in the original semantics. Otherwise, we
  stop the execution of the loop, and the resulting state is the
  same as the one resulting from the execution of the current
  iteration.  In either case, since `break` only terminates the
  innermost loop, `while` signals  {name}`sContinue`.

Based on the above description, complete the definition of the
`Com.EvalR` relation:

```lean
inductive Com.EvalR : Com → State → State → Result → Prop where
  | skip {st : State} : EvalR (imp {skip}) st st sContinue
  -- SOLUTION
  | brk {st : State}  : EvalR (imp {brk}) st st sBreak
  | asgn {st : State} {a : Aexp} {n : Nat} {x : Ident} (h : a.eval st = n) :
      EvalR (imp {x := a}) st (x →ₜ n ; st) sContinue
  | seqContinue {c₁ c₂ : Com} {st st' st'' : State} {s : Result}
      (h₁ : EvalR c₁ st st' sContinue)
      (h₂ : EvalR c₂ st' st'' s) :
      EvalR (imp {c₁; c₂}) st st'' s
  | seqBreak {c₁ c₂ : Com} {st st' : State} (h : EvalR c₁ st st' sBreak) :
      EvalR (imp {c₁; c₂}) st st' sBreak
  | ifTrue {st st' : State} {b : Bexp} {c₁ c₂ : Com} {s : Result} (hb : b.eval st = true)
      (hc : EvalR c₁ st st' s) :
      EvalR (imp {if (b) {c₁} else {c₂}}) st st' s
  | ifFalse {st st' : State} {b : Bexp} {c₁ c₂ : Com} {s : Result} (hb : b.eval st = false)
      (hc : EvalR c₂ st st' s) :
      EvalR (imp {if (b) {c₁} else {c₂}}) st st' s
  | whileFalse {b : Bexp} {st : State} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {while (b) {c}}) st st sContinue
  | whileContinue {st st' st'' : State} {b : Bexp} {c : Com} (hb : b.eval st = true)
      (hc : EvalR c st st' sContinue)
      (hloop : EvalR (imp {while (b) {c}}) st' st'' sContinue) :
      EvalR (imp {while (b) {c}}) st st'' sContinue
  | whileBreak {st st' : State} {b : Bexp} {c : Com} (hb : b.eval st = true)
      (hc : EvalR c st st' sBreak) :
      EvalR (imp {while (b) {c}}) st st' sContinue
  -- END SOLUTION

scoped notation:40 st0:41 " =[ " c " ]=> " st1:41 " // " s:41 => Com.EvalR c st0 st1 s
```

:::autogradedHole Com.EvalR
:::

:::instructors
We don't make the notation with `c:imp_com` since it would need the custom `macro_rules` and elaborators which for a one-off thing are not worth the noise.
:::

Now prove the following properties of your definition:

```lean
theorem break_ignore {c : Com} (st st' : State) {s : Result}
  (h : st =[ imp { brk ; c } ]=> st' // s) :
  st = st' := by
  solution!
    inversion h with
    | seqContinue st'' h₁ h₂ =>
      inversion h₁
    | seqBreak h =>
      inversion h
      rfl
```

```lean
theorem while_continue {b : Bexp} {c : Com} {st st' : State} {s : Result}
  (h : st =[ imp { while (b) {c} } ]=> st' // s) :
  s = sContinue := by
  solution!
    inversion h <;> rfl
```

```lean
theorem while_stops_on_break {b : Bexp} {c : Com} {st st' : State}
    (h₁ : b.eval st = true)
    (h₂ : st =[ imp { ~c } ]=> st' // sBreak) :
    st =[ imp { while (~b) {~c} } ]=> st' // sContinue := by
  solution!
    exact .whileBreak h₁ h₂
```

```lean
theorem seq_continue {c₁ c₂ : Com} {st st' st'' : State}
  (h₁ : st =[ imp { c₁ } ]=> st' // sContinue)
  (h₂ : st' =[ imp { c₂ } ]=> st'' // sContinue) :
  st =[ imp { c₁ ; c₂ } ]=> st'' // sContinue := by
  solution!
    exact .seqContinue h₁ h₂
```

```lean
theorem seq_stops_on_break {c₁ c₂ : Com} {st st' : State}
  (h : st =[ imp { c₁ } ]=> st' // sBreak) :
  st =[ imp { c₁ ; c₂ } ]=> st' // sBreak := by
  solution!
    exact .seqBreak h
```

:::gradeTheorem "1.5" break_ignore
:::

:::gradeTheorem "1.5" while_continue
:::

:::gradeTheorem 1 while_stops_on_break
:::

:::gradeTheorem 1 seq_continue
:::

:::gradeTheorem 1 seq_stops_on_break
:::
::::
:::::

:::::full
::::exercise (rating := 3) (name := "while_break_true") (optional := true)
```lean
theorem while_break_true {b : Bexp} {c : Com} {st st' : State}
  (h₁ : st =[ imp { while (b) {c} } ]=> st' // sContinue)
  (h₂ : b.eval st' = true) :
  ∃ st'', st'' =[ imp { c } ]=> st' // sBreak := by
  solution!
    generalize heq : (imp {while (b) {c}}) = c' at h₁
    generalize hr : sContinue = s at h₁ ⊢
    induction h₁ with (inversion heq; try lia)
    | whileContinue _ _ _ _ ih₂ =>
      apply ih₂ <;> try lia
    | @whileBreak st =>
      exists st
```
::::
:::::

:::::full
::::exercise (rating := 4) (name := "ceval_deterministic") (optional := true)
```lean
theorem ceval_deterministic {c : Com} {st st₁ st₂ : State} {s₁ s₂ : Result}
  (h₁ : st =[ imp { c } ]=> st₁ // s₁)
  (h₂ : st =[ imp { c } ]=> st₂ // s₂) :
  st₁ = st₂ ∧ s₁ = s₂ := by
  solution!
    induction h₁ generalizing st₂ s₂ with (try (inversion h₂ <;> lia))
    | seqContinue h₁' h₂' ih₁ ih₂ =>
      inversion h₂ with
      | seqContinue h₁ h₂ =>
        obtain ⟨eq₁, _⟩ := ih₁ h₁
        inversion eq₁
        apply ih₂
        assumption
      | seqBreak h =>
        specialize ih₁ h
        lia
    | seqBreak _ ih =>
      inversion h₂ with
      | seqContinue h₁ _ =>
        specialize ih h₁
        lia
      | seqBreak =>
        apply ih
        assumption
    | ifTrue _ _ ih =>
      inversion h₂ with
      | ifTrue _ hc' => exact ih hc'
      | ifFalse => lia
    | ifFalse _ _ ih =>
      inversion h₂ with
      | ifTrue => lia
      | ifFalse _ hc' => exact ih hc'
    | whileContinue hb hc hloop ihc ihloop =>
      inversion h₂ with
      | whileFalse => lia
      | whileBreak hb' hc' =>
        specialize ihc hc'
        lia
      | whileContinue hb' hc' hloop' =>
        obtain ⟨eq₁, _⟩ := ihc hc'
        inversion eq₁
        apply ihloop
        assumption
    | whileBreak hb hc ih =>
      inversion h₂ with
      | whileFalse => lia
      | whileBreak hb' hc' =>
        obtain ⟨eq₁, _⟩ := ih hc'
        inversion eq₁
        lia
      | whileContinue hb' hc' hloop' =>
        specialize ih hc'
        lia
```
::::
:::::

:::::full
```lean
end Imp.Break
```
:::::

:::dev PotentialImprovement
Should this exercise be un-hidden?  It needs a tiny bit more
material to be really interesting, though it also leads to a
very interesting exercise in Hoare2.
:::

:::ignore
```lean -show
/- Many programming languages include mechanisms for raising and
handling exceptions.  In this problem (a variant of the above
exercises on `brk`), we'll experiment with a very simple
version, with just a single exception called `throw`.  First, we
need to enrich the language of commands with an additional case
for raising the `throw` exception and a case for catching it. -/

namespace Imp.Throw

inductive Com where
  | skip
  | throw                        -- <--- NEW
  | tryCatch (c₁ c₂ : Com)       -- <--- NEW
  | asgn (x : Ident) (a : Aexp)
  | seq (c₁ c₂ : Com)
  | cond (b : Bexp) (c₁ c₂ : Com)
  | whileDo (b : Bexp) (c : Com)

/-- Exception handling: `try {c₁} catch {c₂}` -/
syntax:max "try " "{" imp_com "}" ppHardSpace "catch" ppHardSpace "{" imp_com "}" : imp_com

-- INSTRUCTORS: Copy of template com

namespace Com

open Lean

scoped macro_rules
  | `(imp { $s }) => do
    let stx ← match s with
      | `(imp_com| skip) => ``(Com.skip)
      | `(imp_com| throw) => ``(Com.throw)
      | `(imp_com| try {$c₁} catch {$c₂}) =>
        ``(Com.tryCatch (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| $x:ident) => ``(($x : Com))
      | `(imp_com| $c₁ ; $c₂) =>
        ``(Com.seq (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| $x:ident := $a) =>
        ``(Com.asgn $x (aexp {$a}))
      | `(imp_com| if ($b) {$c₁} else {$c₂}) =>
        ``(Com.cond (bexp {$b}) (imp {$c₁}) (imp {$c₂}))
      | `(imp_com| while ($b) {$c}) =>
        ``(Com.whileDo (bexp {$b}) (imp {$c}))
      | `(imp_com| ~$c) => `(($c : Com))
      | _ => Macro.throwUnsupported
    return Imp.Elab.withSourceInfoOf s stx

end Com

open scoped Com

namespace Delab
open Lean PrettyPrinter Imp.Delab

@[app_unexpander Com.throw]
private def unexpandComThrow : Unexpander
  | _ => `(imp { $(mkIdent `throw):ident })

@[app_unexpander Com.tryCatch]
private def unexpandComTryCatch : Unexpander
  | `($_ $c₁ $c₂) => `(imp { try { $(getImp c₁) } catch { $(getImp c₂) } })
  | _ => throw ()

attribute [app_unexpander Com.skip] unexpandComSkip
attribute [app_unexpander Com.asgn] unexpandComAsgn
attribute [app_unexpander Com.seq] unexpandComSeq
attribute [app_unexpander Com.cond] unexpandComCond
attribute [app_unexpander Com.whileDo] unexpandComWhileDo

end Delab

/-- info: imp {try {X := 1; throw} catch {Y := 2}} : Com -/
#guard_msgs in
#check imp {try {X := 1; throw} catch {Y := 2}}

/- Next, we need to define the behavior of `throw`.  Informally,
whenever `throw` is executed, we immediately stop executing this
command and start executing the `catch` clause of the closest
enclosing `try`.

A simple way of achieving this effect is to add another parameter
to the evaluation relation that specifies whether evaluation of a
command executes a `throw` statement: -/

inductive Status : Type where
  | sNormal
  | sThrow

open Status

/- Intuitively, `st =[ c ]=> st' // s` means that, if `c` is started in
state `st`, then it terminates in state `st'` and either signals
that an exception has been raised (`s = sThrow`) or that execution
can continue normally (`s = sNormal`).

- If the command is `skip`, then the state doesn't change and
  execution of any enclosing loop can continue normally.

- If the command is `throw`, the state stays unchanged but we
  signal a `sThrow`.

- If the command is `try`, we begin by executing the first
  subcommand; if it terminates normally, then the whole `try`
  terminates in the same state; if it terminates with an
  exception, we execute the second subcommand instead.

- If the command is an assignment, then we update the binding for
  that variable in the state accordingly and signal that execution
  can continue normally.

- If the command is of the form `if (b) {c₁} else {c₂}`, then
  the state is updated as in the original semantics of Imp, except
  that we also propagate the signal from the execution of
  whichever branch was taken.

- If the command is a sequence `c₁ ; c₂`, we first execute `c₁`.
  If this yields a `sThrow`, we skip the execution of `c₂` and
  propagate the `sThrow` signal to the surrounding context; the
  resulting state is the same as the one obtained by executing
  `c₁` alone. Otherwise, we execute `c₂` on the state obtained
  after executing `c₁`, and propagate the signal generated there.

- Finally, for a loop of the form `while (b) {c}`, when `b`
  evaluates to `true`, we execute `c` and check the signal that it
  raises.  If that signal is `sNormal`, the execution proceeds
  as in the original semantics. Otherwise, we stop the execution
  of the loop and signal `sThrow`.

Based on the above description, complete the definition of the
`Com.EvalR` relation: -/

-- INSTRUCTORS: Copy of template eval

inductive Com.EvalR : Com → State → State → Status → Prop where
  | skip {st : State} : EvalR (imp {skip}) st st sNormal
  -- SOLUTION
  | throw {st : State} : EvalR (imp {throw}) st st sThrow
  | tryNormal {c₁ c₂ : Com} {st st' : State} (h : EvalR c₁ st st' sNormal) :
      EvalR (imp {try {~c₁} catch {~c₂}}) st st' sNormal
  | tryThrow {c₁ c₂ : Com} {st st' st'' : State} {s : Status}
      (h₁ : EvalR c₁ st st' sThrow)
      (h₂ : EvalR c₂ st' st'' s) :
      EvalR (imp {try {~c₁} catch {~c₂}}) st st'' s
  | asgn {st : State} {a : Aexp} {n : Nat} {x : Ident} (h : a.eval st = n) :
      EvalR (imp {x := ~a}) st (x →ₜ n ; st) sNormal
  | seqNormal {c₁ c₂ : Com} {st st' st'' : State} {s : Status}
      (h₁ : EvalR c₁ st st' sNormal)
      (h₂ : EvalR c₂ st' st'' s) :
      EvalR (imp {~c₁; ~c₂}) st st'' s
  | seqThrow {c₁ c₂ : Com} {st st' : State} (h : EvalR c₁ st st' sThrow) :
      EvalR (imp {~c₁; ~c₂}) st st' sThrow
  | ifTrue {st st' : State} {b : Bexp} {c₁ c₂ : Com} {s : Status} (hb : b.eval st = true)
      (hc : EvalR c₁ st st' s) :
      EvalR (imp {if (~b) {~c₁} else {~c₂}}) st st' s
  | ifFalse {st st' : State} {b : Bexp} {c₁ c₂ : Com} {s : Status} (hb : b.eval st = false)
      (hc : EvalR c₂ st st' s) :
      EvalR (imp {if (~b) {~c₁} else {~c₂}}) st st' s
  | whileFalse {b : Bexp} {st : State} {c : Com} (hb : b.eval st = false) :
      EvalR (imp {while (~b) {~c}}) st st sNormal
  | whileNormal {st st' st'' : State} {b : Bexp} {c : Com} {s : Status} (hb : b.eval st = true)
      (hc : EvalR c st st' sNormal)
      (hloop : EvalR (imp {while (~b) {~c}}) st' st'' s) :
      EvalR (imp {while (~b) {~c}}) st st'' s
  | whileThrow {st st' : State} {b : Bexp} {c : Com} (hb : b.eval st = true)
      (hc : EvalR c st st' sThrow) :
      EvalR (imp {while (~b) {~c}}) st st' sThrow
  -- END SOLUTION

scoped notation:40 st0:41 " =[ " c " ]=> " st1:41 " // " s:41 => Com.EvalR c st0 st1 s

-- LATER: It would be good to have some examples that verify
-- that their implementation does the right thing on a few unit
-- tests!

/- Your definition should allow you to prove this example: -/

example :
    ∅ =[ imp { try {X := 1; throw; X := 2} catch {Y := X} } ]=>
      {Y ↦ 1, X ↦ 1} // sNormal := by
  solution!
    apply Com.EvalR.tryThrow
    · apply Com.EvalR.seqNormal (Com.EvalR.asgn rfl)
      exact Com.EvalR.seqThrow Com.EvalR.throw
    · exact Com.EvalR.asgn rfl

/- Now prove the following properties of your definition of `Com.EvalR`: -/

-- LATER: see comments in the break exercise

theorem ceval_deterministic_throw {c : Com} {st st₁ st₂ : State} {s₁ s₂ : Status}
    (h₁ : st =[ imp { ~c } ]=> st₁ // s₁)
    (h₂ : st =[ imp { ~c } ]=> st₂ // s₂) :
    st₁ = st₂ ∧ s₁ = s₂ := by
  solution!
    induction h₁ generalizing st₂ s₂ with (try (inversion h₂ <;> lia))
    | tryNormal _ ih =>
      inversion h₂ with
      | tryNormal h => exact ih h
      | tryThrow h _ =>
        specialize ih h
        lia
    | tryThrow _ _ ih₁ ih₂ =>
      inversion h₂ with
      | tryNormal h =>
        specialize ih₁ h
        lia
      | tryThrow h₁' h₂' =>
        obtain ⟨hst, _⟩ := ih₁ h₁'
        subst hst
        exact ih₂ h₂'
    | seqNormal _ _ ih₁ ih₂ =>
      inversion h₂ with
      | seqNormal h₁' h₂' =>
        obtain ⟨hst, _⟩ := ih₁ h₁'
        subst hst
        exact ih₂ h₂'
      | seqThrow h =>
        specialize ih₁ h
        lia
    | seqThrow _ ih =>
      inversion h₂ with
      | seqNormal h _ =>
        specialize ih h
        lia
      | seqThrow h => exact ih h
    | ifTrue _ _ ih =>
      inversion h₂ with
      | ifTrue _ hc' => exact ih hc'
      | ifFalse => lia
    | ifFalse _ _ ih =>
      inversion h₂ with
      | ifTrue => lia
      | ifFalse _ hc' => exact ih hc'
    | whileNormal hb hc hloop ihc ihloop =>
      inversion h₂ with
      | whileFalse => lia
      | whileNormal hb' hc' hloop' =>
        obtain ⟨hst, _⟩ := ihc hc'
        subst hst
        exact ihloop hloop'
      | whileThrow hb' hc' =>
        specialize ihc hc'
        lia
    | whileThrow hb hc ih =>
      inversion h₂ with
      | whileFalse => lia
      | whileNormal hb' hc' _ =>
        specialize ih hc'
        lia
      | whileThrow hb' hc' =>
        obtain ⟨hst, _⟩ := ih hc'
        subst hst
        exact ⟨rfl, rfl⟩

end Imp.Throw
```
:::

:::::full
::::exercise (rating := 4) (name := "add_for_loop") (optional := true)
Add C-style `for` loops to the language of commands, update the
`Com.EvalR` definition to define the semantics of `for` loops, and add
cases for `for` loops as needed so that all the proofs in this
file are accepted by Lean.

A `for` loop should be parameterized by (a) a statement executed
initially, (b) a test that is run on each iteration of the loop to
determine whether the loop should continue, (c) a statement
executed at the end of each loop iteration, and (d) a statement
that makes up the body of the loop.  (You don't need to worry
about making up a concrete Notation for `for` loops, but feel free
to play with this too if you like.)
::::
:::::

:::dev
```
HTML polish — deferred Verso-markup opportunities for a later pass (see
CONTRIBUTING.md, "Verso markup for nicer HTML"):
* {name} was applied to resolvable declaration references in visible prose.
  More could be added, but bare type names were linked only selectively (avoid
  over-linking; mind forward references and namespace scope — a name must
  already be defined and in scope at that point in the document, or {name} fails
  to build).
* {ref "tag"} cross-references link "see the X section" phrasings; add a
  `%%% tag := "…" %%%` block under a heading to make it a target. Done for the
  Notations and Delaborators sections; more internal "above/below" phrasings
  could get the same treatment.
* {deftech}/{tech} — a small glossary: define Imp's core terms once with
  {deftech} (abstract syntax, state, big-step, relation, partial function, …)
  and link later uses with {tech}.
* {lean}`expr` — inline elaborated expressions/types where a whole expression,
  not just a single name, reads better with hover types (e.g. the
  `Coe Ident Aexp` / `OfNat Aexp n` bullets in the Notations section).
```
:::
