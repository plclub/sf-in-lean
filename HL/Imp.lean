import VersoManual
import VersoManual.InlineLean
import Illuminate
import SFLMeta.Bnf
import SFLMeta.DisplayMath
import SFLMeta.Ignore
import SFLMeta.Save
import SFLMeta.Comment
import SFLMeta.Exercise
import SFLMeta.Grade
import SFLMeta.Hide
import SFLMeta.Instructors
import SFLMeta.Quiz
import SFLMeta.SlideBreak
import SFLMeta.Solution
import SFLMeta.Terse
import LF.Maps
import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer
open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "Imp: Simple Imperative Programs" =>
%%%
tag := "Imp"
htmlSplit := .never
file := some "Imp"
%%%

:::instructors
This chapter plus `Maps` takes a little more than one
   80-minute lecture.  It could be streamlined a bit further without
   losing much, by removing (for example) the inference rules and BNF
   notations from the terse version.

   (BCP 21: ... Actually, I tried removing inference rules from the
   TERSE version; eventually decided that it makes some of the
   definitions harder to talk about.)
:::

:::dev SOONER
Needs some WORKINCLASSes and some quizzes

LATER: Another nice challenge exercise at some point would be to add
   C-style arrays (i.e., indirect read/write).  This sets up some
   really nice challenge problems in Hoare (reasoning about arrays /
   aliasing / etc.).

SOONER: BCP 25: Maybe we should write /\ instead of && in assertions,
   to save a mismatch in the `dec_minimum` exercise in Hoare2?

   At some point we could consider moving material from the old
   HoareLists to this chapter (and into later files, as
   appropriate).  We haven't done it yet because it's a shame to
   complicate the nice simple presentation here when it's used as the
   basis for applications like Xavier's static analysis lectures.
   Also, we now have a whole volume on real separation logic...

MWH (port note): The Rocq chapter's "Rocq Automation" tour has been
retooled here for Lean.  The tactic combinators `try` and `repeat` (and the
custom-tactic `macro`) are introduced in this chapter; `<;>` and `simp` were
already introduced in Logical Foundations (`<;>` in `Induction`)
so we use them freely and the `<;>` section
below is a recap.  For linear arithmetic we use `lia`;
NOTE that LF currently
introduces `omega`, not `lia`, so this needs to be reconciled volume-wide
(either introduce `lia` in LF, or keep `omega`).
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
while Z <> 0 do
  Y := Y * Z;
  Z := Z - 1
end
```
::::

We concentrate here on defining the _syntax_ and _semantics_ of Imp;
later in this volume we develop a theory of _program equivalence_ and introduce
_Hoare Logic_, a popular logic for reasoning about imperative programs.

::::full
We build Imp in three layers.  The first — a core language of _arithmetic and
boolean expressions_ — is developed in its own chapter, _Slang_;
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

:::dev LATER
Maybe this section needs a little preface talking about "what is
   the meaning of an expression with variables?"...

LATER: (Note copied from Equiv right before the `assign_aequiv`
   exercise): Some or all of this discussion should really happen when
   states are introduced in Imp.v, and the whole idea of treating states as
   an ADT should be raised there.
:::

Since we'll want to look variables up to find out their current values,
we'll use total maps from the `Maps` chapter. A _machine state_ (or
just _state_) represents the current values of all variables at some
point in the execution of a program.

::::full
For simplicity, we assume that the state is defined for _all_ variables,
even though any given program is only able to mention a finite number of
them. Because each variable stores a natural number, we represent the
state as a total map from strings (variable names) to `Nat`, and will use
`0` as the default value in the store.
::::

We give the type of variable identifiers a name, `Ident`. For now it is just
   `String`; naming it makes the intent clearer.

```lean
abbrev Ident := String
abbrev State := TotalMap Ident Nat
```

## Syntax

We can add variables to the arithmetic expressions we had before simply
by including one more constructor.  (This is a fresh `Aexp`, replacing
the variable-free one from the _Slang_ chapter.)

```lean
inductive Aexp where
  | num (n : Nat)
  | id (x : Ident)                -- NEW
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)
```

:::dev "Chris Henson (chenson2018)"
Rather than define identifiers as Ident, a more general approach is
to use a *type variable* with `DecidableEq` (as the
`Maps` chapter does), threaded through `Aexp`/`Bexp`/`Com`/`State`.  Stashed
for a future decision; the parameterized version would look like:

```
inductive Aexp (V : Type) where
  | num (n : Nat)
  | id (x : V)
  | plus (a1 a2 : Aexp V)
  | minus (a1 a2 : Aexp V)
  | mult (a1 a2 : Aexp V)
-- … then `Bexp V`, `Com V`, `abbrev State (V) [DecidableEq V] :=
-- TotalMap V Nat`, and `[DecidableEq V]` wherever a lookup/update is
-- performed.
```
:::

The `Bexp` definition is unchanged, except that it now refers to the new `Aexp`.

```lean
inductive Bexp where
  | bool (b : Bool)
  | eq (a1 a2 : Aexp)
  | neq (a1 a2 : Aexp)
  | le (a1 a2 : Aexp)
  | gt (a1 a2 : Aexp)
  | not (b : Bexp)
  | and (b1 b2 : Bexp)
```

Defining a few variable names as shorthands will make examples easier to read.

```lean
def W : Ident := "W"
def X : Ident := "X"
def Y : Ident := "Y"
def Z : Ident := "Z"
```

::::full
(This convention for naming program variables (`X`, `Y`, `Z`) clashes a
bit with our earlier use of uppercase letters for types. Since we're not
using polymorphism heavily in the chapters developed to Imp, this
overloading should not cause confusion.)
::::

## Notations
%%%
tag := "imp-notations"
%%%

::::full
To make Imp programs easier to read and write, we introduce some notations and implicit
coercions.

You do not need to understand exactly what these declarations do. Briefly, though:

- The `declare_syntax_cat` directive adds a new non-terminal to Lean's grammar, called
  `imp_aexp`. We'll add additional non-terminals further below.
- Each `syntax` directive defines a grammar production, of which there are eight in
  total. The first two define literals, `num` and `ident`, as `imp_aexp`s. The next
  deveral directives define productions for building larger expressions, with
  some annotations to define precedence, etc.
- Finally, `macro_rules` is used to translate each production of the `imp_aexp` nonterminal
  into a Lean expression.
- The same basic pattern is followed for `bexp`s too.
::::

```lean
/-- Arithmetic expressions of Imp -/
declare_syntax_cat imp_aexp
/-- Numeric literal -/
syntax:max num : imp_aexp
/-- Variable reference -/
syntax:max ident : imp_aexp
/-- Addition -/
syntax:65 imp_aexp:65 " + " imp_aexp:66 : imp_aexp
/-- Subtraction -/
syntax:65 imp_aexp:65 " - " imp_aexp:66 : imp_aexp
/-- Multiplication -/
syntax:70 imp_aexp:70 " * " imp_aexp:71 : imp_aexp
/-- Parentheses for grouping -/
syntax "(" imp_aexp ")" : imp_aexp
/-- Escape to Lean -/
syntax:max "~" term:max : imp_aexp

/-- Embed an Imp arithmetic expression into a Lean term -/
syntax:min "aexp " "{" imp_aexp "}" : term
```

:::instructors
A variable reference elaborates to `Aexp.id $x` with the identifier spliced
as a *term*, not as a string literal. So `aexp { X }` is `Aexp.id X`, using
the declared constant `X : Ident`, exactly matching hand-written terms like
`.asgn X …` and the shape the state/`ceval` proofs expect. (Rocq's `<{ }>`
does the same via its `constr` fallback, yielding `AId X`.) A consequence is
that a variable name must be a declared `Ident` constant — as W/X/Y/Z are.
:::

```lean
open Lean in
macro_rules
  | `(aexp { $n:num }) => `(Aexp.num $(quote n.getNat))
  | `(aexp { $x:ident }) => `(Aexp.id $x)
  | `(aexp { ~$e }) => pure e
  | `(aexp { $a + $b }) => `(Aexp.plus (aexp {$a}) (aexp {$b}))
  | `(aexp { $a - $b }) => `(Aexp.minus (aexp {$a}) (aexp {$b}))
  | `(aexp { $a * $b }) => `(Aexp.mult (aexp {$a}) (aexp {$b}))
  | `(aexp { ($a) }) => `(aexp {$a})
```

:::instructors
The literals `true`/`false` are accepted through the bare-identifier form
(`syntax:max ident : imp_bexp`) and turned into {name}`Bexp.bool` by the macro
below, which rejects any other identifier. We take this route rather than
declaring `true`/`false` as symbols: as reserved keywords they would break
ordinary Lean uses of `true`/`false`, and as non-reserved symbols they would
clash with the bare-identifier form of `imp_aexp`.
:::

```lean
/-- Boolean expressions of Imp -/
declare_syntax_cat imp_bexp
/-- Boolean literal (`true` or `false`) -/
syntax:max ident : imp_bexp
/-- Equality of arithmetic expressions -/
syntax:50 imp_aexp:51 " = " imp_aexp:51 : imp_bexp
/-- Disequality of arithmetic expressions -/
syntax:50 imp_aexp:51 " <> " imp_aexp:51 : imp_bexp
/-- Less than or equal -/
syntax:50 imp_aexp:51 " <= " imp_aexp:51 : imp_bexp
/-- Greater than -/
syntax:50 imp_aexp:51 " > " imp_aexp:51 : imp_bexp
/-- Boolean negation -/
syntax:70 "! " imp_bexp:70 : imp_bexp
/-- Boolean conjunction -/
syntax:35 imp_bexp:36 " && " imp_bexp:35 : imp_bexp
/-- Parentheses for grouping -/
syntax "(" imp_bexp ")" : imp_bexp
/-- Escape to Lean -/
syntax:max "~" term:max : imp_bexp

/-- Embed an Imp boolean expression into a Lean term -/
syntax:min "bexp " "{" imp_bexp "}" : term
```

:::instructors
The antiquotations are annotated with their category (`$a:imp_aexp`,
`$b:imp_bexp`) because an `imp_bexp` can begin with an `imp_aexp` (a
comparison); without the annotation the parser would descend into `imp_aexp`
and then insist on a comparison operator.
:::

```lean
open Lean in
macro_rules
  | `(bexp { $x:ident }) =>
    match x.getId with
    | `true  => `(Bexp.bool true)
    | `false => `(Bexp.bool false)
    | _      => Macro.throwErrorAt x s!"expected 'true' or 'false', got '{x.getId}'"
  | `(bexp { ~$e }) => pure e
  | `(bexp { $a:imp_aexp = $b:imp_aexp }) => `(Bexp.eq (aexp {$a}) (aexp {$b}))
  | `(bexp { $a:imp_aexp <> $b:imp_aexp }) => `(Bexp.neq (aexp {$a}) (aexp {$b}))
  | `(bexp { $a:imp_aexp <= $b:imp_aexp }) => `(Bexp.le (aexp {$a}) (aexp {$b}))
  | `(bexp { $a:imp_aexp > $b:imp_aexp }) => `(Bexp.gt (aexp {$a}) (aexp {$b}))
  | `(bexp { ! $b:imp_bexp }) => `(Bexp.not (bexp {$b}))
  | `(bexp { $b1:imp_bexp && $b2:imp_bexp }) => `(Bexp.and (bexp {$b1}) (bexp {$b2}))
  | `(bexp { ($b:imp_bexp) }) => `(bexp {$b})
```

::::full
We make it a little easier to write Imp programs using normal constructors (i.e.,
without notation), by using _implicit coercions_.
In Lean, a `Coe` instance tells the elaborator how to turn a
value of one type into another automatically:
 - `Coe Ident Aexp` lets us write a bare variable (an `Ident`) where an
   `Aexp` is expected; the identifier is implicitly wrapped with `id`.
 - `OfNat Aexp n` lets us write a numeric literal where an `Aexp` is
   expected; it is implicitly wrapped with `num`.
 - `Coe Bool Bexp` lets us write a boolean literal (`true`/`false`) where a
   `Bexp` is expected; it is implicitly wrapped with `bool`.
::::

```lean
instance : Coe Ident Aexp where
  coe := .id

instance (n : Nat) : OfNat Aexp n where
  ofNat := .num n

instance : Coe Bool Bexp where
  coe := .bool
```

::::full
With these coercions we can write `.plus 3 (.mult X 2)` instead of the fully
   explicit `.plus (.num 3) (.mult (.id "X") (.num 2))`, and `.and true (.not …)`
   instead of `.and (.bool true) (.not …)`. More readably still, the concrete
   syntax from the {ref "imp-notations"}[Notations section] lets us write these examples directly:
::::

```lean
def example_aexp : Aexp := aexp { 3 + (X * 2) }
def example_bexp : Bexp := bexp { true && !(X <= 4) }
```

## Delaborators
%%%
tag := "imp-delaborators"
%%%

::::full
The notations above are _input_ only: they teach Lean how to *read* `aexp
{ … }` and `bexp { … }`, but Lean still *prints* an expression using its raw
constructors -- `example_aexp` shows up as `Aexp.plus (Aexp.num 3) …` rather
than `aexp { 3 + X * 2 }`. A _delaborator_ closes the loop. Where a `macro`
turns surface syntax into a term (_elaboration_), a delaborator does the
reverse: it turns an elaborated term back into surface syntax so that Lean's
own output uses our concrete Imp notation.

Each delaborator below walks a term of the given type and rebuilds the
matching piece of `imp_aexp`/`imp_bexp` syntax; a subterm Lean doesn't
recognize is printed with the `~` escape. The `@[delab …]` attribute
registers the top-level function to fire whenever Lean is about to display a
term headed by one of those constructors -- unless notation printing has been
switched off with `set_option pp.notation false`, which lets us fall back to
the raw constructors when debugging (see _Desugaring Notations_ below). The
companion _category parenthesizer_ re-inserts the parentheses the grammar's
precedences demand, so that, e.g., `(1 + 2) * 3` prints with its parentheses
intact.

You do not need to understand the details. The result is that a `#check`, an
`#eval`, or a proof goal mentioning an Imp expression is displayed in
readable Imp syntax rather than as a pile of constructors.
::::

```lean
namespace Imp.Delab
open Lean PrettyPrinter Delaborator SubExpr Parenthesizer

/-- Re-inserts parentheses in `imp_aexp` output according to the grammar's precedences. -/
@[category_parenthesizer imp_aexp]
def imp_aexp.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `imp_aexp true wrapParens prec <|
    parenthesizeCategoryCore `imp_aexp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

/-- Re-inserts parentheses in `imp_bexp` output according to the grammar's precedences. -/
@[category_parenthesizer imp_bexp]
def imp_bexp.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `imp_bexp true wrapParens prec <|
    parenthesizeCategoryCore `imp_bexp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

/-- Tag freshly built syntax with the term info that Lean's pretty printer expects. -/
def annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

/-- Rebuild `imp_aexp` concrete syntax from an `Aexp` term. -/
partial def delabAexpInner : DelabM (TSyntax `imp_aexp) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | Aexp.num _ =>
      match (← withAppArg getExpr).nat? with
      | some v => pure ⟨Syntax.mkNumLit (toString v) |>.raw⟩
      | none   => `(imp_aexp| ~$(← withAppArg delab))
    | Aexp.id _ =>
      -- A variable reference like aexp { X } elaborates to Aexp.id X where X is the
      -- declared Ident constant, so the delaborators print the constant's name as a
      -- bare identifier (and also handle the .id "X" string-literal form).
      match ← withAppArg getExpr with
      | .const nm _      => `(imp_aexp| $(mkIdent nm):ident)
      | .lit (.strVal s) => `(imp_aexp| $(mkIdent (.mkSimple s)):ident)
      | _                => `(imp_aexp| ~$(← withAppArg delab))
    | Aexp.plus _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_aexp| $s1 + $s2)
    | Aexp.minus _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_aexp| $s1 - $s2)
    | Aexp.mult _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_aexp| $s1 * $s2)
    | _ => `(imp_aexp| ~$(← delab))
  annAsTerm stx

/-- Rebuild `imp_bexp` concrete syntax from a `Bexp` term. -/
partial def delabBexpInner : DelabM (TSyntax `imp_bexp) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | Bexp.bool _ =>
      match ← withAppArg getExpr with
      | .const ``Bool.true _  => `(imp_bexp| $(mkIdent `true):ident)
      | .const ``Bool.false _ => `(imp_bexp| $(mkIdent `false):ident)
      | _                     => `(imp_bexp| ~$(← withAppArg delab))
    | Bexp.eq _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_bexp| $s1:imp_aexp = $s2:imp_aexp)
    | Bexp.neq _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_bexp| $s1:imp_aexp <> $s2:imp_aexp)
    | Bexp.le _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_bexp| $s1:imp_aexp <= $s2:imp_aexp)
    | Bexp.gt _ _ =>
      let s1 ← withAppFn <| withAppArg delabAexpInner
      let s2 ← withAppArg delabAexpInner
      `(imp_bexp| $s1:imp_aexp > $s2:imp_aexp)
    | Bexp.not _ =>
      let s ← withAppArg delabBexpInner
      `(imp_bexp| ! $s)
    | Bexp.and _ _ =>
      let s1 ← withAppFn <| withAppArg delabBexpInner
      let s2 ← withAppArg delabBexpInner
      `(imp_bexp| $s1 && $s2)
    | _ => `(imp_bexp| ~$(← delab))
  annAsTerm stx
```

The `whenPPOption getPPNotation` wrapper lets `set_option pp.notation false`
switch this delaborator off, revealing the raw constructors (see the
"Desugaring Notations" discussion, after the commands are introduced).

```lean
@[delab app.Aexp.num, delab app.Aexp.id, delab app.Aexp.plus,
  delab app.Aexp.minus, delab app.Aexp.mult]
partial def delabAexp : Delab := whenPPOption getPPNotation do
  -- This delaborator only understands `Aexp`'s constructors -- bail otherwise.
  guard <| match_expr ← getExpr with
    | Aexp.num _ => true
    | Aexp.id _ => true
    | Aexp.plus _ _ => true
    | Aexp.minus _ _ => true
    | Aexp.mult _ _ => true
    | _ => false
  match ← delabAexpInner with
  | `(imp_aexp| ~$e) => pure e
  | e => `(term| aexp { $e })

@[delab app.Bexp.bool, delab app.Bexp.eq, delab app.Bexp.neq, delab app.Bexp.le,
  delab app.Bexp.gt, delab app.Bexp.not, delab app.Bexp.and]
partial def delabBexp : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Bexp.bool _ => true
    | Bexp.eq _ _ => true
    | Bexp.neq _ _ => true
    | Bexp.le _ _ => true
    | Bexp.gt _ _ => true
    | Bexp.not _ => true
    | Bexp.and _ _ => true
    | _ => false
  match ← delabBexpInner with
  | `(imp_bexp| ~$e) => pure e
  | e => `(term| bexp { $e })

end Imp.Delab
```

::::full
With the delaborators in place, Lean now prints Imp expressions using the
concrete syntax rather than their raw constructors.
::::

```lean
/-- info: aexp {3 + X * 2} : Aexp -/
#guard_msgs in
#check aexp { 3 + (X * 2) }

/-- info: bexp {true && ! (X <= 4)} : Bexp -/
#guard_msgs in
#check bexp { true && !(X <= 4) }
```

## Evaluation

::::full
The arithmetic and boolean evaluators must now be extended to handle
variables, taking a state `st` as an extra argument.  A variable is
looked up in the state with the map-indexing notation `st[x]` from the
`Maps` chapter.
::::

:::terse
Now we need to add an `st` parameter to both evaluation functions:
:::

```lean
def Aexp.eval (st : State) (a : Aexp) : Nat :=
  match a with
  | num   n     =>  n
  | id    x     =>  st[x]                    -- NEW
  | plus  a1 a2 =>  eval st a1 + eval st a2
  | minus a1 a2 =>  eval st a1 - eval st a2
  | mult  a1 a2 =>  eval st a1 * eval st a2

def Bexp.eval (st : State) (b : Bexp) : Bool :=
  match b with
  | bool b      =>  b
  | eq   a1 a2  =>  a1.eval st == a2.eval st
  | neq  a1 a2  =>  a1.eval st != a2.eval st
  | le   a1 a2  =>  a1.eval st ≤  a2.eval st
  | gt   a1 a2  =>  a1.eval st >  a2.eval st
  | not  b1     =>  !b1.eval st
  | and  b1 b2  =>  b1.eval st && b2.eval st

@[simp] theorem Aexp.eval_num (st : State) (n : Nat) : (num n).eval st = n := rfl
@[simp] theorem Aexp.eval_id (st : State) (x : Ident) : (Aexp.id x).eval st = st[x] := rfl
@[simp] theorem Aexp.eval_plus (st : State) (a1 a2 : Aexp) :
    (plus a1 a2).eval st = a1.eval st + a2.eval st := rfl
@[simp] theorem Aexp.eval_minus (st : State) (a1 a2 : Aexp) :
    (minus a1 a2).eval st = a1.eval st - a2.eval st := rfl
@[simp] theorem Aexp.eval_mult (st : State) (a1 a2 : Aexp) :
    (mult a1 a2).eval st = a1.eval st * a2.eval st := rfl

@[simp] theorem Bexp.eval_bool (st : State) (b : Bool) : (bool b).eval st = b := rfl
@[simp] theorem Bexp.eval_eq (st : State) (a1 a2 : Aexp) :
    (eq a1 a2).eval st = (a1.eval st == a2.eval st) := rfl
@[simp] theorem Bexp.eval_neq (st : State) (a1 a2 : Aexp) :
    (neq a1 a2).eval st = (a1.eval st != a2.eval st) := rfl
@[simp] theorem Bexp.eval_le (st : State) (a1 a2 : Aexp) :
    (le a1 a2).eval st = (a1.eval st ≤ a2.eval st : Bool) := rfl
@[simp] theorem Bexp.eval_gt (st : State) (a1 a2 : Aexp) :
    (gt a1 a2).eval st = (a1.eval st > a2.eval st : Bool) := rfl
@[simp] theorem Bexp.eval_not (st : State) (b : Bexp) : (not b).eval st = !b.eval st := rfl
@[simp] theorem Bexp.eval_and (st : State) (b1 b2 : Bexp) :
    (and b1 b2).eval st = (b1.eval st && b2.eval st) := rfl
```

We reuse the total-map notation (`x →ₜ v ; ∅` etc.) for states.

```lean
example : aexp { 3 + (X * 2) }.eval (X →ₜ 5 ; ∅) = 13 := by rfl

example : aexp { Z + (X * Y) }.eval (X →ₜ 5 ; Y →ₜ 4 ; ∅) = 20 := by rfl

example : bexp { true && !(X <= 4) }.eval (X →ₜ 5 ; ∅) = true := by rfl
```

:::dev
dsainati: Bikeshedding: I'm not sure how I feel about this arrow subscript for maps.
Easy to change later but just flagging to discuss. mwhicks1: This comes from the Maps
chapter, which chenson2018 is working on.
There is a keyboard shortcut for ↦ we could use (\mapsto).
:::

# Commands

::::full
Now we are ready to define the syntax and behavior of Imp _commands_
(or _statements_). Informally, commands `c` are described by the
following BNF grammar:

```display
c := skip
   | x := a
   | c ; c
   | if b then c else c end
   | while b do c end
```

Here is the formal definition of the abstract syntax of commands.
::::

```lean
inductive Com where
  | skip
  | asgn (x : Ident) (a : Aexp)
  | seq (c1 c2 : Com)
  | cond (b : Bexp) (c1 c2 : Com)
  | whileDo (b : Bexp) (c : Com)
```

:::instructors
Concrete syntax for commands, in the style of the `ssft24` Imp `Stmt`
   grammar: an `imp_com` category with an `imp { … }` hook. Assignments and
   `skip` end in `;`, and sequencing is written by juxtaposition. Conditions use
   the `imp_bexp` grammar; the branch/loop bodies use the `imp_com` grammar. As
   with expressions, `~c` escapes back to an ordinary Lean term of type `Com`.
:::

```lean
/-- Imp commands -/
declare_syntax_cat imp_com
```

:::instructors
`skip` is *not* a reserved keyword: it is accepted through a bare
   identifier-terminated command (`syntax ident ";" : imp_com`) and recognised
   in the macro below, which rejects any other identifier. This keeps `skip`
   usable as the bare constructor name {name}`Com.skip` in `match`/`induction`
   elsewhere in the file, and avoids reserving `skip` globally.
:::

```lean
/-- The command that does nothing (`skip;`) -/
syntax ident ";" : imp_com
/-- Sequencing: one command after another -/
syntax imp_com ppDedent(ppLine imp_com) : imp_com
/-- Assignment -/
syntax ident " := " imp_aexp ";" : imp_com
/-- Conditional -/
syntax "if " "(" imp_bexp ")" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}" ppHardSpace "else" ppHardSpace "{") ppLine imp_com ppDedent(ppLine "}") : imp_com
/-- Loop -/
syntax "while " "(" imp_bexp ")" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}") : imp_com
/-- Escape to Lean -/
syntax:max "~" term:max : imp_com

/-- Include an Imp command in Lean code -/
syntax:min "imp" ppHardSpace "{" ppLine imp_com ppDedent(ppLine "}") : term

open Lean in
macro_rules
  | `(imp { $x:ident ; }) =>
    if x.getId == `skip then `(Com.skip)
    else Macro.throwErrorAt x s!"expected 'skip', got '{x.getId}'"
  | `(imp { $c1 $c2 }) =>
    `(Com.seq (imp {$c1}) (imp {$c2}))
  | `(imp { $x:ident := $a; }) =>
    `(Com.asgn $x (aexp {$a}))
  | `(imp { if ($b) {$c1} else {$c2} }) =>
    `(Com.cond (bexp {$b}) (imp {$c1}) (imp {$c2}))
  | `(imp { while ($b) {$c} }) =>
    `(Com.whileDo (bexp {$b}) (imp {$c}))
  | `(imp { ~$c }) =>
    pure c
```

::::full
Just as we did for expressions, we add a delaborator so that Lean prints
commands back in the `imp { … }` concrete syntax (see the
{ref "imp-delaborators"}[Delaborators section] above). It reuses the expression
delaborators for the condition of an
`if`/`while` and for the right-hand side of an assignment, and prints an
unrecognized subcommand with the `~` escape.
::::

```lean
namespace Imp.Delab
open Lean PrettyPrinter Delaborator SubExpr

/-- Rebuild `imp_com` concrete syntax from a `Com` term. -/
partial def delabComInner : DelabM (TSyntax `imp_com) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | Com.skip => `(imp_com| skip;)
    | Com.asgn _ _ =>
      match ← withAppFn <| withAppArg getExpr with
      | .const nm _ =>
        let a ← withAppArg delabAexpInner
        `(imp_com| $(mkIdent nm):ident := $a;)
      | .lit (.strVal s) =>
        let a ← withAppArg delabAexpInner
        `(imp_com| $(mkIdent (.mkSimple s)):ident := $a;)
      | _ => `(imp_com| ~$(← delab))
    | Com.seq _ _ =>
      let s1 ← withAppFn <| withAppArg delabComInner
      let s2 ← withAppArg delabComInner
      `(imp_com| $s1 $s2)
    | Com.cond _ _ _ =>
      let b  ← withAppFn <| withAppFn <| withAppArg delabBexpInner
      let c1 ← withAppFn <| withAppArg delabComInner
      let c2 ← withAppArg delabComInner
      `(imp_com| if ($b) {$c1} else {$c2})
    | Com.whileDo _ _ =>
      let b ← withAppFn <| withAppArg delabBexpInner
      let c ← withAppArg delabComInner
      `(imp_com| while ($b) {$c})
    | _ => `(imp_com| ~$(← delab))
  annAsTerm stx

@[delab app.Com.skip, delab app.Com.asgn, delab app.Com.seq,
  delab app.Com.cond, delab app.Com.whileDo]
partial def delabCom : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Com.skip => true
    | Com.asgn _ _ => true
    | Com.seq _ _ => true
    | Com.cond _ _ _ => true
    | Com.whileDo _ _ => true
    | _ => false
  match ← delabComInner with
  | `(imp_com| ~$e) => pure e
  | e => `(term| imp { $e })

end Imp.Delab
```

::::full
As an example, here is the factorial function again, written as a formal
definition. When this command terminates, the variable `Y` will
contain the factorial of the initial value of `X`.  (Compare this to
the concrete Imp program at the very start of the chapter.)
::::

```lean
def fact_in_lean : Com := imp {
  Z := X;
  Y := 1;
  while (Z <> 0) {
    Y := Y * Z;
    Z := Z - 1;
  }
}
```

::::full
Because we registered a delaborator, we can inspect a defined program with
`#print`, which shows the stored definition using the same concrete syntax:
::::

```lean
/--
info: def fact_in_lean : Com :=
imp {
  Z := X;
  Y := 1;
  while (Z <> 0) {
    Y := Y * Z;
    Z := Z - 1;
  }
}
-/
#guard_msgs in
#print fact_in_lean
```

## Desugaring Notations

::::full
The `imp { … }` notation, together with the delaborators, is purely a
convenience for reading and writing programs. Occasionally, such as when debugging
a definition or a stuck proof, the concrete syntax `hide`s the underlying structure
we want to see. For those moments we can switch the Imp notation off in Lean's
output with `set_option pp.notation false`, which our delaborators honor.

Note that unlike a `def`, `imp { … }` is a `macro` which is expanded during elaboration,
*before* the resulting term is type-checked. So `fact_in_lean` is not a
program hidden behind a layer of notation that a proof must first peel back;
it simply *is* the underlying tree of {name}`Com`, {name}`Aexp`, and {name}`Bexp` constructors.
Consequently, when a proof goal mentions an Imp program, tactics such as
`cases`, `injection`, and `simp` already act on those constructors directly
-- there is nothing to "unfold". The delaborators affect only how that tree
is *displayed*. Nevertheless, seeing the raw constructors is sometimes very helpful!
::::

```lean
/-- info: imp {
  X := X + 1;
} : Com -/
#guard_msgs in
#check imp { X := X + 1; }

/-- info: Com.asgn X ((Aexp.id X).plus (Aexp.num 1)) : Com -/
#guard_msgs in
set_option pp.notation false in
#check imp { X := X + 1; }
```

## More Examples

A few more examples.

:::slidebreak
:::

Assignment:

```lean
def plus2 : Com := imp { X := X + 2; }
def XtimesYinZ : Com := imp { Z := X * Y; }
```

:::slidebreak
:::

Loops:

```lean
def subtract_slowly_body : Com := imp {
  Z := Z - 1;
  X := X - 1;
}

def subtract_slowly : Com := imp {
  while (X <> 0) {
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
def loop : Com := imp { while (true) { skip; } }
```

::::hide
```
/- Exponentiation: -/
def exp_body : Com := imp {
  Z := Z * X;
  Y := Y - 1;
}
def pexp : Com := imp {
  while (Y <> 0) {
    ~exp_body
  }
}
/- (Note that `pexp` should be run in a state where `Z` is `1`.) -/
```
::::

# Evaluating Commands

::::full
Next we need to define what it means to evaluate an Imp command.  The
fact that `while` loops don't necessarily terminate makes defining an
evaluation function tricky.
::::

## Evaluation as a Function (Failed Attempt)

Here's an attempt at defining an evaluation function for commands (with
a bogus `while` case).

:::dev LATER
In SmallStep we need to package the state and command into a pair,
   so that we can talk about normal forms and such. Probably we should do it
   here too, for consistency. (Won't change much except the type
   declarations, but we'll need to add a comment why we wrote them this
   way.)
:::

```lean
def Com.ceval_fun_no_while (st : State) (c : Com) : State :=
  match c with
  | imp {skip;} => st
  | imp {x := ~a;} => (x →ₜ a.eval st ; st)
  | imp {~c1 ~c2} =>
      let st' := ceval_fun_no_while st c1
      ceval_fun_no_while st' c2
  | imp {if (~b) {~c1} else {~c2}} =>
      if b.eval st then ceval_fun_no_while st c1
      else ceval_fun_no_while st c2
  | imp {while (~_) {~_}} => st     -- bogus
```

::::full
In a more conventional functional language like OCaml or Haskell we
could add the `while` case as follows:

```
| .whileDo b c =>
    if b.eval st then ceval_fun st (.seq c (.whileDo b c))
    else st
```

Lean doesn't accept such a definition ("fail to show termination")
because the function we want to define is not guaranteed to terminate.
Indeed, it _doesn't_ always terminate: the full `ceval_fun` applied to
the `loop` program above would run forever. Since Lean aims to be not
just a programming language but also a consistent logic, any
potentially non-terminating function must be rejected. Here is what
would go wrong if Lean allowed non-terminating recursive functions:

```
def loop_false (n : Nat) : False := loop_false n
```

That is, propositions like `False` would become provable (`loop_false 0`
would be a proof of `False`), a disaster for logical consistency.

Thus, because it doesn't terminate on all inputs, the full `ceval_fun`
cannot be written in Lean -- at least not without additional tricks and
workarounds.
::::

:::dev
   Perhaps that discussion should be moved to -- or previewed in --
   Logic.v?  MRC'20: It's already in ProofObjects (which not everyone
   sees).
:::

:::terse
A nonterminating `def loop_false (n) : False := loop_false n` would make `False`
provable, so Lean rejects it.
:::

## Evaluation as a Relation

Here's a better way: define `ceval` as a _relation_ rather than a
_function_ -- i.e., make its result a `Prop` rather than a `State`,
similar to what we did for `Aexp.EvalR` above.

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

Operational Semantics

:::dev SOONER
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

                      st  =[ c1 ]=> st'
                      st' =[ c2 ]=> st''
                    ---------------------                (seq)
                    st =[ c1;c2 ]=> st''

                     b.eval st = true
                      st =[ c1 ]=> st'
           --------------------------------------        (ifTrue)
           st =[ if b then c1 else c2 end ]=> st'

                    b.eval st = false
                      st =[ c2 ]=> st'
           --------------------------------------        (ifFalse)
           st =[ if b then c1 else c2 end ]=> st'

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

:::dev "Chris Henson (chenson2018)"
TODO Propose you use inline notation such as `Com.EvalR (imp {skip;}) st st`
:::

```lean
inductive Com.EvalR : Com → State → State → Prop where
  | skip (st : State) : EvalR (imp {skip;}) st st
  | asgn (st : State) (a : Aexp) (n : Nat) (x : Ident) (h : a.eval st = n) :
      EvalR (imp {x := ~a;}) st (x →ₜ n ; st)
  | seq (c1 c2 : Com) (st st' st'' : State) (h1 : EvalR c1 st st') (h2 : EvalR c2 st' st'') :
      EvalR (imp {~c1 ~c2}) st st''
  | ifTrue (st st' : State) (b : Bexp) (c1 c2 : Com) (hb : b.eval st = true)
      (hc : EvalR c1 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2}}) st st'
  | ifFalse (st st' : State) (b : Bexp) (c1 c2 : Com) (hb : b.eval st = false)
      (hc : EvalR c2 st st') :
      EvalR (imp {if (~b) {~c1} else {~c2}}) st st'
  | whileFalse (b : Bexp) (st : State) (c : Com) (hb : b.eval st = false) :
      EvalR (imp {while (~b) {~c}}) st st
  | whileTrue (st st' st'' : State) (b : Bexp) (c : Com) (hb : b.eval st = true)
      (hc : EvalR c st st') (hloop : Com.EvalR (imp {while (~b) {~c}}) st' st'') :
      EvalR (imp {while (~b) {~c}}) st st''

notation:40 st0:41 " =[ " c " ]=> " st1:41 => Com.EvalR c st0 st1
-- Also accept a bare Imp command between the brackets, so concrete programs can
-- be written without the `imp { … }` wrapper. Bare `Com` terms still work via the
-- notation above; splice a Lean term into the command with `~`.
syntax:40 term:41 " =[ " imp_com " ]=> " term:41 : term
macro_rules
  | `($st0 =[ $c:imp_com ]=> $st1) => `($st0 =[ imp { $c } ]=> $st1)
```

The cost of defining evaluation as a relation instead of a function is
that we now need to construct a _proof_ that some program evaluates to
some result state, rather than letting Lean's computation mechanism do
it for us.

```lean
example :
    ∅ =[
      X := 2;
      if (X <= 1) {
        Y := 3;
      } else {
        Z := 4;
      }
    ]=> (Z →ₜ 4 ; X →ₜ 2 ; ∅) := by
  -- We must supply the intermediate state.
  apply Com.EvalR.seq (st' := (X →ₜ 2 ; ∅))
  · apply Com.EvalR.asgn; rfl
  · apply Com.EvalR.ifFalse
    · rfl
    · apply Com.EvalR.asgn; rfl
```

:::::exercise (rating := 2) (name := "ceval_example2")
```lean
example :
    ∅ =[
      X := 0;
      Y := 1;
      Z := 2;
    ]=> (Z →ₜ 2 ; Y →ₜ 1 ; X →ₜ 0 ; ∅) := by
  solution!
    apply Com.EvalR.seq (st' := (X →ₜ 0 ; ∅))
    · apply Com.EvalR.asgn; rfl
    · apply Com.EvalR.seq (st' := (Y →ₜ 1 ; X →ₜ 0 ; ∅))
      · apply Com.EvalR.asgn; rfl
      · apply Com.EvalR.asgn; rfl
```
:::::

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
  st =[ skip; ~c ]=> st' →
  st =[ c ]=> st'
```

(A) Yes    (B) No    (C) Not sure

:::answer
```
theorem quiz1_answer (c : Com) (st st' : State)
    (h : st =[ skip; ~c ]=> st') : st =[ c ]=> st' := by
  cases h with
  | seq _ _ _ smid _ h1 h2 =>
      cases h1 with
      | skip _ => exact h2
```
:::
::::

::::quiz
Is the following proposition provable?

```display
∀ (c1 c2 : Com) (st st' : State),
  st =[ ~c1 ~c2 ]=> st' →
  st =[ c1 ]=> st →
  st =[ c2 ]=> st'
```

(A) Yes    (B) No    (C) Not sure

:::instructors
Answer is given later (`quiz2_answer`) as it depends on `ceval_deterministic`.
:::
::::

::::quiz
Is the following proposition provable?

```display
∀ (b : Bexp) (c : Com) (st st' : State),
  st =[ if (~b) { ~c } else { ~c } ]=> st' →
  st =[ c ]=> st'
```

(A) Yes    (B) No    (C) Not sure

:::answer
```
theorem quiz3_answer (b : Bexp) (c : Com) (st st' : State)
    (h : st =[ if (~b) { ~c } else { ~c } ]=> st') : st =[ c ]=> st' := by
  cases h with
  | ifTrue _ _ _ _ _ hb hc => exact hc
  | ifFalse _ _ _ _ _ hb hc => exact hc
```
:::
::::

::::quiz
Is the following proposition provable?

```display
∀ (b : Bexp),
  (∀ st, b.eval st = true) →
  ∀ (c : Com) (st : State),
  ¬ ∃ st', st =[ while (~b) { ~c } ]=> st'
```

(A) Yes    (B) No    (C) Not sure

:::answer
```
-- This one is tricky!
theorem quiz4_answer (b : Bexp) (hbtrue : ∀ st, b.eval st = true)
    (c : Com) (st : State) : ¬ ∃ st', st =[ while (~b) { ~c } ]=> st' := by
  rintro ⟨st', hev⟩
  have key : ∀ (cmd : Com) (s s' : State),
      (s =[ cmd ]=> s') → cmd = (imp { while (~b) { ~c } }) → False := by
    intro cmd s s' hce
    induction hce with
    | whileFalse b0 s0 c0 hbf =>
        intro heq; injection heq with e1 _; subst e1
        rw [hbtrue s0] at hbf; simp at hbf
    | whileTrue s0 s0' s0'' b0 c0 hbt hc0 hloop ih1 ih2 =>
        intro heq; exact ih2 heq
    | skip s0 => intro heq; simp at heq
    | asgn s0 a n x h => intro heq; simp at heq
    | seq d1 d2 s0 s0' s0'' hh1 hh2 ih1 ih2 => intro heq; simp at heq
    | ifTrue s0 s0' b0 d1 d2 hb0 hc0 ih => intro heq; simp at heq
    | ifFalse s0 s0' b0 d1 d2 hb0 hc0 ih => intro heq; simp at heq
  exact key _ st st' hev rfl
```
:::
::::

::::quiz
Is the following proposition provable?

```display
∀ (b : Bexp) (c : Com) (st : State),
  (¬ ∃ st', st =[ while (~b) { ~c } ]=> st') →
  ∀ st'', b.eval st'' = true
```

(A) Yes    (B) No    (C) Not sure

:::answer
This claim is *false*, so it cannot be proved -- the proof gets
stuck immediately:

```
theorem quiz5_answer (b : Bexp) (c : Com) (st : State)
    (H : ¬ ∃ st', st =[ while (~b) { ~c } ]=> st') :
    ∀ st'', b.eval st'' = true := by
  intro st''
  -- Can't make any progress -- the claim is false!
```
:::
::::

## Determinism of Evaluation

:::dev LATER
Maybe this should go at the end of the file in a section marked
   optional? Not everybody will want to spend time on it.
:::

::::full
Changing from a computational to a relational definition of evaluation
is a good move because it frees us from the artificial requirement that
evaluation be a total function. But it raises a question: is the
relational definition really a partial _function_? Could the same
command, from the same state, evaluate to two different final states?
In fact this cannot happen: `ceval` _is_ a partial function.
::::

:::terse
Finally, we should pause to check that our evaluation relation really is a (partial) function...
:::

:::dev LATER
Informal proof needed! (And one can surely be found in some past
   CIS500 exam solutions!)
:::

```lean
theorem ceval_deterministic (c : Com) (st st1 st2 : State)
    (e1 : st =[ c ]=> st1) (e2 : st =[ c ]=> st2) : st1 = st2 := by
  induction e1 generalizing st2 with
  | skip st =>
      cases e2 with
      | skip => rfl
  | asgn st a n x h =>
      cases e2 with
      | asgn _ _ n' _ h' => subst h; subst h'; rfl
  | seq c1 c2 st st' st'' h1 h2 ih1 ih2 =>
      cases e2 with
      | seq _ _ _ st2' _ h1' h2' =>
          have hst : st' = st2' := ih1 _ h1'
          subst hst
          exact ih2 _ h2'
  | ifTrue st st' b c1 c2 hb hc ih =>
      cases e2 with
      | ifTrue _ _ _ _ _ hb' hc' => exact ih _ hc'
      | ifFalse _ _ _ _ _ hb' hc' => simp_all
  | ifFalse st st' b c1 c2 hb hc ih =>
      cases e2 with
      | ifTrue _ _ _ _ _ hb' hc' => simp_all
      | ifFalse _ _ _ _ _ hb' hc' => exact ih _ hc'
  | whileFalse b st c hb =>
      cases e2 with
      | whileFalse _ _ _ hb' => rfl
      | whileTrue _ _ _ _ _ hb' hc' hl' => simp_all
  | whileTrue st st' st'' b c hb hc hloop ih1 ih2 =>
      cases e2 with
      | whileFalse _ _ _ hb' => simp_all
      | whileTrue _ st2' _ _ _ hb' hc' hl' =>
          have hst : st' = st2' := ih1 _ hc'
          subst hst
          exact ih2 _ hl'
```

::::hide
```
/- Answer to the second quiz above (deferred because it depends on
   `ceval_deterministic`). -/
theorem quiz2_answer (c1 c2 : Com) (st st' : State)
    (h1 : st =[ .seq c1 c2 ]=> st') (h2 : st =[ c1 ]=> st) : st =[ c2 ]=> st' := by
  cases h1 with
  | seq _ _ _ smid _ hc1 hc2 =>
      have hmid : smid = st := ceval_deterministic c1 st smid st hc1 h2
      subst hmid
      exact hc2
```
::::

:::::exercise (rating := 3) (name := "pup_to_n")
Write an Imp program that sums the numbers from `1` to `X` (inclusive)
in the variable `Y`.  Your program should update the state as shown in
`pup_to_2_ceval`, which you can reverse-engineer to discover the program
you should write.  The proof of that theorem will be somewhat lengthy.

```lean
def pup_to_n : Com := solution!(
  imp {
    Y := 0;
    while (1 <= X) {
      Y := Y + X;
      X := X - 1;
    }
  })
```

:::hide
   Result is the same as `(X →ₜ 0 ; Y →ₜ 3 ; ∅)` if one admits
   functional extensionality.
:::

```lean
theorem pup_to_2_ceval :
    (X →ₜ 2 ; ∅) =[ pup_to_n ]=>
      (X →ₜ 0 ; Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; ∅) := by
  solution!
    unfold pup_to_n
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

:::dev LATER
Comment from reader: Another good place to mention lack of
   functional extensionality.  The 6 `→ₜ`/`t_update`s in the above theorem
   are not redundant, nor would `pup_to_2_ceval` be provable if the
   algorithm were defined differently (e.g., if it used `Z` as a "buffer"
   variable instead of decrementing `X`).
:::

# Reasoning About Imp Programs

:::dev LATER
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
theorem plus2_spec (st : State) (n : Nat) (st' : State)
    (hx : st[X] = n) (heval : st =[ plus2 ]=> st') :
    st'[X] = n + 2 := by
  -- Inverting `heval` forces one step of the `ceval` computation: since
  -- `plus2` is an assignment, `st'` must be `st` extended at `X`.
  unfold plus2 at heval
  cases heval with
  | asgn _ _ m _ h =>
      simp only [Aexp.eval_plus, Aexp.eval_id, Aexp.eval_num] at h
      rw [TotalMap.update_eq]
      lia
```

:::dev LATER
This used to be recommended.  Should it be reinstated?
:::

:::::exercise (rating := 3) (name := "XtimesYinZ_spec")
State and prove a specification of `XtimesYinZ`.

```lean
-- SOLUTION
/- Here is a specification in the style of `plus2_spec`: -/
theorem XtimesYinZ_spec1 (st : State) (nx ny : Nat) (st' : State)
    (hx : st[X] = nx) (hy : st[Y] = ny) (heval : st =[ XtimesYinZ ]=> st') :
    st'[Z] = nx * ny := by
  unfold XtimesYinZ at heval
  cases heval with
  | asgn _ _ n _ h =>
      simp only [Aexp.eval_mult, Aexp.eval_id] at h
      subst hx hy
      rw [TotalMap.update_eq]
      exact h.symm

/- Though perhaps a cleaner specification would be: -/
theorem XtimesYinZ_spec (st : State) :
    st =[ XtimesYinZ ]=> (Z →ₜ st[X] * st[Y] ; st) := by
  unfold XtimesYinZ
  apply Com.EvalR.asgn
  rfl

/- A less informative specification would be ... -/
theorem XtimesYinZ_spec2 (st : State) : ∃ st', st =[ XtimesYinZ ]=> st' := by
  exact ⟨(Z →ₜ st[X] * st[Y] ; st), by unfold XtimesYinZ; apply Com.EvalR.asgn; rfl⟩
-- END SOLUTION
```

:::grade
```
GRADE_MANUAL 3: XtimesYinZ_spec
```
:::
:::::

:::::exercise (rating := 3) (name := "loop_never_stops")
Hint: proceed by induction on the assumed derivation showing that `loop`
terminates.  Most of the cases are immediately contradictory and so can be
solved in one step (by `simp`/`discriminate` on the impossible command
equation).

```lean
theorem loop_never_stops (st st' : State) : ¬ (st =[ loop ]=> st') := by
  solution!
    intro contra
    -- Generalize over the command so the induction remembers what `loop` is.
    have key : ∀ (c : Com) (s s' : State), (s =[ c ]=> s') → c = loop → False := by
      intro c s s' hce
      induction hce with
      | whileFalse b s0 c0 hb =>
          intro heq; unfold loop at heq; injection heq with e1 _
          subst e1; simp at hb
      | whileTrue s0 s0' s0'' b c0 hb hc hloop ih1 ih2 =>
          intro heq; exact ih2 heq
      | skip s0 => intro heq; simp [loop] at heq
      | asgn s0 a n x h => intro heq; simp [loop] at heq
      | seq c1 c2 s0 s0' s0'' h1 h2 ih1 ih2 => intro heq; simp [loop] at heq
      | ifTrue s0 s0' b c1 c2 hb hc ih => intro heq; simp [loop] at heq
      | ifFalse s0 s0' b c1 c2 hb hc ih => intro heq; simp [loop] at heq
    exact key loop st st' contra rfl
```
:::::

:::dev LATER
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

:::::exercise (rating := 3) (name := "no_whiles_eqv")
The following function yields `true` just on programs with no while
loops. Using `inductive`, write a property `Com.NoWhilesR` that holds
exactly when `c` is while-free, then prove it equivalent to `Com.no_whiles`.

```lean
def Com.no_whiles (c : Com) : Bool :=
  match c with
  | imp {skip;} => true
  | imp {_x := ~_a;} => true
  | imp {~c1 ~c2} => no_whiles c1 && no_whiles c2
  | imp {if (~_) {~ct} else {~cf}} => no_whiles ct && no_whiles cf
  | imp {while (~_) {~_}} => false

inductive Com.NoWhilesR : Com → Prop where
  -- SOLUTION
  | skip : Com.NoWhilesR (imp { skip; })
  | asgn (x : Ident) (a : Aexp) : Com.NoWhilesR (imp { x := ~a; })
  | seq (c1 c2 : Com) (h1 : Com.NoWhilesR c1) (h2 : Com.NoWhilesR c2) :
      Com.NoWhilesR (imp { ~c1 ~c2 })
  | cond (b : Bexp) (c1 c2 : Com) (h1 : Com.NoWhilesR c1) (h2 : Com.NoWhilesR c2) :
      Com.NoWhilesR (imp { if (~b) { ~c1 } else { ~c2 } })
  -- END SOLUTION

theorem no_whiles_eqv (c : Com) : c.no_whiles = true ↔ Com.NoWhilesR c := by
  solution!
    constructor
    · induction c with
      | skip => intro _; exact .skip
      | asgn x a => intro _; exact .asgn x a
      | seq c1 c2 ih1 ih2 =>
          intro h; simp only [Com.no_whiles, Bool.and_eq_true] at h
          exact .seq _ _ (ih1 h.1) (ih2 h.2)
      | cond b c1 c2 ih1 ih2 =>
          intro h; simp only [Com.no_whiles, Bool.and_eq_true] at h
          exact .cond _ _ _ (ih1 h.1) (ih2 h.2)
      | whileDo b c ih => intro h; simp [Com.no_whiles] at h
    · intro h
      induction h with
      | skip => rfl
      | asgn x a => rfl
      | seq c1 c2 h1 h2 ih1 ih2 => simp [Com.no_whiles, ih1, ih2]
      | cond b c1 c2 h1 h2 ih1 ih2 => simp [Com.no_whiles, ih1, ih2]
```
:::::

:::::exercise (rating := 4) (name := "no_whiles_terminating")
Imp programs that don't involve while loops always terminate.  State and
prove a theorem `no_whiles_terminating` that says this.  Use either
{name}`Com.no_whiles` or {name}`Com.NoWhilesR`, as you prefer.

```lean
theorem no_whiles_terminating (c : Com) (st : State) (h : Com.NoWhilesR c) :
    ∃ st', st =[ c ]=> st' := by
  solution!
    induction h generalizing st with
    | skip => exact ⟨st, .skip st⟩
    | asgn x a => exact ⟨(x →ₜ a.eval st ; st), .asgn st a (a.eval st) x rfl⟩
    | seq c1 c2 h1 h2 ih1 ih2 =>
        obtain ⟨st', hc1⟩ := ih1 st
        obtain ⟨st'', hc2⟩ := ih2 st'
        exact ⟨st'', .seq c1 c2 st st' st'' hc1 hc2⟩
    | cond b c1 c2 h1 h2 ih1 ih2 =>
        cases hb : b.eval st with
        | true =>
            obtain ⟨st', hc1⟩ := ih1 st
            exact ⟨st', .ifTrue st st' b c1 c2 hb hc1⟩
        | false =>
            obtain ⟨st', hc2⟩ := ih2 st
            exact ⟨st', .ifFalse st st' b c1 c2 hb hc2⟩
```

And here is an alternative solution by induction on `c` (using
   {name}`Com.no_whiles` instead of {name}`Com.NoWhilesR`):

```lean
-- SOLUTION
theorem no_whiles_terminating' (c : Com) (st1 : State)
    (hb : c.no_whiles = true) : ∃ st2, st1 =[ c ]=> st2 := by
  induction c generalizing st1 with
  | skip => exact ⟨st1, .skip st1⟩
  | asgn x a => exact ⟨(x →ₜ a.eval st1 ; st1), .asgn st1 a (a.eval st1) x rfl⟩
  | seq c1 c2 ih1 ih2 =>
      simp only [Com.no_whiles, Bool.and_eq_true] at hb
      obtain ⟨st1', hc1⟩ := ih1 st1 hb.1
      obtain ⟨st1'', hc2⟩ := ih2 st1' hb.2
      exact ⟨st1'', .seq c1 c2 st1 st1' st1'' hc1 hc2⟩
  | cond b ct cf ih1 ih2 =>
      simp only [Com.no_whiles, Bool.and_eq_true] at hb
      cases hbev : b.eval st1 with
      | true =>
          obtain ⟨st2, h⟩ := ih1 st1 hb.1
          exact ⟨st2, .ifTrue st1 st2 b ct cf hbev h⟩
      | false =>
          obtain ⟨st2, h⟩ := ih2 st1 hb.2
          exact ⟨st2, .ifFalse st1 st2 b ct cf hbev h⟩
  | whileDo b c ih => simp [Com.no_whiles] at hb
-- END SOLUTION
```
:::::

:::dev "Michael Hicks (mwhicks1)"
```
NOT PORTED YET — remaining sections of sfdev/lf/Imp.v to port:
  - Case Study (Optional), Imp.v:2774
      * subtract_slowly_spec (EX4?, Imp.v:2919): loop-invariant style proof
        about `subtract_slowly`.
  - Additional Exercises, Imp.v:2986
      * stack_compiler (EX3, Imp.v:2988): define `s_execute` (stack machine)
        and `s_compile : aexp -> list sinstr`; needs a `SInstr` inductive
        (SPush/SLoad/SPlus/SMinus/SMult) and a list-based stack.
      * execute_app (EX3, Imp.v:3114)
      * stack_compiler_correct (EX3, Imp.v:3134): the correctness theorem;
        the standard proof needs a strengthened lemma over an arbitrary
        initial stack (generalize the stack before inducting).
      * short_circuit (EX3?, Imp.v:3184): short-circuiting `Bexp.eval`.
      * break_imp (EX4?, Imp.v:3227): extends Com with `CBreak`; new
        relational semantics `ceval` carrying a `result` (SContinue/SBreak).
        Large. See verso-book branch (lf/Imp.lean ~line 1141, CEvalBreak) for
        a prior take on the signal type.
      * while_break_true (EX3A?, Imp.v:3454)
      * ceval_deterministic for break (EX4A?, Imp.v:3477)
      * exn_imp (EX4A?, Imp.v:3524): exceptions variant. Large.
      * add_for_loop (EX4?, Imp.v:3728): add a C-style `for` loop to Com,
        its notation, and extend ceval.
```
:::

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
* {tactic}`simp` — link tactic names in the automation/tactics prose (`try`,
  `repeat`, `<;>`, `simp`, `lia`, `cases`, `induction`).
* {deftech}/{tech} — a small glossary: define Imp's core terms once with
  {deftech} (abstract syntax, state, big-step, relation, partial function, …)
  and link later uses with {tech}.
* {lean}`expr` — inline elaborated expressions/types where a whole expression,
  not just a single name, reads better with hover types (e.g. the
  `Coe Ident Aexp` / `OfNat Aexp n` bullets in the Notations section).
```
:::
