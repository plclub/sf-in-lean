import SFLMeta

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Appendix: Notations" =>
%%%
tag := "Appendix: Notations"
htmlSplit := .never
file := some "Notations"
%%%

# Notations in Logical Foundations (plus HL and TS)

This file provides an overview of the custom notations introduced across the volumes.

## Basics

:::table +header
*
  * Notation
  * Chapter
  * Comment
*
  * ```
    local prefix:40 (priority := high) "!" => not
    local infixl:35 (priority := high) " && " => and
    local infixl:30 (priority := high) " || " => or
    ```
  * Basics (`MyBool`)
  * The notation is `local` so it's dropped at `end MyBool`. This is on purpose as we start using Lean's booleans right after.
*
  * ```
    scoped infixl:65 " + " => add
    scoped infixl:70 " * " => mul
    scoped infixl:30 " == " => beq
    ```
  * Basics (`NatPlayground.Nat`)
  * The notation is `scoped` inside `NatPlayground.Nat`.
*
  * ```
    scoped infixr:65 " :: " => cons
    scoped macro (priority := high) "[" elems:term,* "]"
    @[scoped app_unexpander nil]
    @[scoped app_unexpander cons]
    ```
  * Lists
  * The `::` notation might be causing some performance issues with verso.
*
  * ```
    infix:52 " ≤? " => Nat.ble
    ```
  * Tactics
  * --
*
  * ```
    scoped infix:50 (priority := high) " ≤ " => Le
    ```
  * IndProp
  * This for some reason doesn't work without `(priority := high)`
*
  * ```
    infix:40 " =~ " => ExpMatch
    ```
  * Automation
  * --
*
  * ```
    notation a " →ₜ " b " ; " m => TotalMap.update m a b
    notation a " →ₜ " b => TotalMap.update ∅ a b
    scoped notation k " ↦ " v => KVPair.mk k v
    notation a " →ₚ " b " ; " m => PartialMap.update m a b
    notation a " →ₚ " b => PartialMap.update ∅ a b
    ```
  * Typeclasses
  * --
*
  * ```
    syntax " | " caseArg " => " tacticSeq : invAlt
    syntax (" | " caseArg)+ " => " tacticSeq : invAlts
    syntax (name := inversion) "inversion "
      optConfig ident (" with " (colGe invAlts)+)? : tactic
    macro "lemma " thm:declId sig:declSig val:declVal :
      command => `(theorem $thm $sig $val)
    elab "apply " t:term " at " i:ident : tactic =>
      withSynthesize <| withMainContext do
    ```
  * CustomTactics (not a chapter itself, imported in most chapters)
  * Introduces tactics like `inversion` and `apply at` plus the `lemma` command.
:::

:::dev "Niklas Halonen (xhalo32)"
- Comments about notations in Basics:
  - We have a mixture of `local` and `scoped` notations. Neither `local` or `scoped` is mentioned in `More on Notation (Optional)`.
    - The scoped notations are inside `NatPlayground.Nat`.
  - The boolean notations have `(priority := high)` which seem to be unnecessary. The file builds without the priority setting.

- The `≤?` notation in Tactics, `=~` in Automation, and `→ₜ, →ₚ` in Typeclasses should be `scoped`.

- Should `CustomTactics` be imported by default in every chapter?
:::

:::dev "Niklas Halonen (xhalo32)"
The `(priority := high)` in IndProp is in fact necessary which is surprising since increasing the priority isn't necessary in Basics.
This is caused by the fact that `≤` has the same type signature in IndProp so it's ambiguous whereas in Basics `+` is defined for a custom `Nat` type so Lean selects the notation that is expected by the types.
Lean also seems to favor the scoped `+` notation over the one from the prelude:
```
scoped infixl:65 " + " => add

end NatPlayground.Nat
open scoped NatPlayground.Nat

example {a b} : a + b = b + a := by
  guard_hyp a : NatPlayground.Nat
  sorry
```
But the same does not work with `≤`:
```
scoped infix:50 " ≤ " => Le

end LePlayground
open scoped LePlayground

#check 3 ≤ 5 -- ambiguous term
```

:::

## Hoare logic

:::table +header
*
  * Notation
  * Chapter
  * Comment
*
  * ```
    declare_syntax_cat imp_aexp
    declare_syntax_cat imp_bexp
    syntax:min "aexp " "{" imp_aexp "}" : term
    syntax:min "bexp " "{" imp_bexp "}" : term
    @[delab app.Aexp.num, delab app.Aexp.id, delab app.Aexp.plus,
      delab app.Aexp.minus, delab app.Aexp.mult]
    partial def delabAexp : Delab := whenPPOption getPPNotation do
    @[delab app.Bexp.bool, delab app.Bexp.eq, delab app.Bexp.neq,
      delab app.Bexp.le, delab app.Bexp.gt,
      delab app.Bexp.not, delab app.Bexp.and]
    partial def delabBexp : Delab := whenPPOption getPPNotation do
    ```
  * Imp
  * Comes with 130 lines of delaboration code
*
  * ```
    declare_syntax_cat imp_com
    syntax:min "imp" ppHardSpace
      "{" ppLine imp_com ppDedent(ppLine "}") : term

    @[delab app.Com.skip, delab app.Com.asgn, delab app.Com.seq,
      delab app.Com.cond, delab app.Com.whileDo]
    partial def delabCom : Delab := whenPPOption getPPNotation do
    ```
  * Imp
  * The delaborator formats the code over multiple lines
:::

## Type Systems

:::table +header
*
  * Notation
  * Chapter
  * Comment
*
  * ```
    scoped notation:55 e:56 " ⇓ " n:56 => Aexp.EvalR e n
    ```
  * Slang
  * --
*
  * ```
    scoped notation:55 e:56 " ⇓b " b:56 => Bexp.EvalR e b
    ```
  * Slang
  * --
*
  * ```
    notation:50 t " ⇓ " n => Eval t n
    ```
  * Smallstep
  * --
*
  * ```
    scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
    ```
  * Smallstep
  * --
*
  * ```
    notation:40 t:41 " ⟶ " t':41 => Step t t'
    ```
  * Smallstep
  * --
*
  * ```
    notation:40 t:41 " ⟶* " t':41 => Multi Step t t'
    ```
  * Smallstep
  * --
*
  * ```
    scoped notation:40 a:41 " ⟶a " a':41 => AStep a a'
    ```
  * Smallstep
  * --
*
  * ```
    scoped notation:40 b:41 " ⟶b " b':41 => BStep b b'
    ```
  * Smallstep
  * --
*
  * ```
    scoped notation:40 a:41 " ⟶n " a':41 => ANStep a a'
    ```
  * Smallstep
  * --
*
  * ```
    declare_syntax_cat tm
    macro_rules -- tm
    @[delab app.TM.Tm.tru, delab app.TM.Tm.fls,
      delab app.TM.Tm.zero, delab app.TM.Tm.succ,
      delab app.TM.Tm.pred, delab app.TM.Tm.isZero,
      delab app.TM.Tm.ite]
    partial def delabTm : Delab := whenPPOption getPPNotation do
    ```
  * Types
  * --
*
  * ```
    local notation:40 t:41 " ⟶ " t':41 => Tm.Step t t'
    scoped notation:40 t:41 " ⟶ " t':41 => Tm.Step t t'
    ```
  * Types
  * The local notation is used only inside the inductive declaration
*
  * ```
    local notation:40 t:41 " ⇢ " t':41 => Tm.AltStep t t'
    scoped notation:40 t:41 " ⇢ " t':41 => Tm.AltStep t t'
    ```
  * Types
  * The local notation is used only inside the inductive declaration
*
  * ```
    syntax:max "<{ " "⊢ " tm " ⦂ " ident " }>" : term
    syntax:max "<{ " "⊢ " tm " ⦂ " "~" term:max " }>" : term
    local macro_rules
    macro_rules
    ```
  * Types
  * The local macro rules is used only inside the inductive declaration
*
  * ```
    scoped notation:40 t1:41 " ⟶* " t2:41 => Tm.MultiStep t1 t2
    ```
  * Types
  * --
*
  * ```
    declare_syntax_cat stlcTy
    macro_rules (kind := tyBracket)
    declare_syntax_cat stlcVar
    declare_syntax_cat stlcTm
    macro_rules (kind := tmBracket)
    @[delab app.Stlc.Ty.bool, delab app.Stlc.Ty.arrow]
    def delabTy : Delab := whenPPOption getPPNotation do
    @[delab app.Stlc.Tm.var, delab app.Stlc.Tm.app,
      delab app.Stlc.Tm.abs, delab app.Stlc.Tm.tru,
      delab app.Stlc.Tm.fls, delab app.Stlc.Tm.ite]
    def delabTm : Delab := whenPPOption getPPNotation do
    ```
  * Stlc
  * Delaborators take up 120 lines
*
  * ```
    local macro_rules (kind := tmBracket)
    macro_rules (kind := tmBracket)
    ```
  * Stlc
  * Used in the definition of `subst`
*
  * ```
    local notation:40 t:41 " ⟶ " t':41 => Step t t'
    scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
    scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'
    ```
  * Stlc
  * The local notation is used only inside the inductive declaration
*
  * ```
    declare_syntax_cat stlcCtx
    ```
  * Stlc
  * --
*
  * ```
    local macro_rules (kind := judgeBracket)
    macro_rules (kind := judgeBracket)
    @[app_unexpander Stlc.HasType]
    ```
  * Stlc
  * The local notation is used only inside the inductive declaration
:::


:::dev "Niklas Halonen (xhalo32)"
It might make sense to introduce a notation type class for big step evaluation, or to use scoped notation to change `⇓b` to `⇓`. The notation type class could be reused in Smallstep.

Notation type class for `⟶`?

I think we can simplify typing judgments to just `"<{ " "⊢ " tm " ⦂ " term:max " }>"` and remove the ``| `(<{ ⊢ $t ⦂ ~$T }>) => `(Tm.HasType <{ $t }> $T)`` branch.
The `Tm.HasType` in my opinion gets drowned between all of the syntax boilerplate.

I find it a bit strange that substitution is `stlcTm` rather than a term. At least I don't think of substitution as a "term" in the internal language.
:::
