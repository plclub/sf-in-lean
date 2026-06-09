module

public meta import Lean.Elab.ConfigEval
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Tactic.RenameInaccessibles
public meta import Lean.Elab.Tactic.Induction
public meta import Lean.Elab.Tactic.BuiltinTactic
meta import all Lean.Elab.Tactic.BuiltinTactic

public meta import Lean.Meta.Tactic.Generalize
public meta import Lean.Meta.Tactic.Cases
public meta import Lean.Meta.Tactic.Injection
public meta import Lean.Meta.Tactic.Contradiction

meta section

namespace Lean.Parser
open Tactic

declare_syntax_cat invAlt
syntax " | " caseArg " => " tacticSeq : invAlt

/--
  `inversion t` generalizes nonvariable indices of the type of `t` before invoking `cases t`,
  then solves away contradictory generated goals.
  * If `inversion +clear t` is set, `t` is `clear`ed from the context.
  * The form `inversion t with | tag₁ x ... => tac ... | ... | tagₙ z ... => tac ...` is supported,
    similar to that of `cases` and `inversion`.
    However, `tag`s must be explicitly given.
-/
syntax (name := inversion)
  "inversion " optConfig ident (" with " (colGe invAlt)+)? : tactic

end Lean.Parser

namespace Lean.Meta

/--
  This function is similar to `forallMetaTelescopeReducing`: Given `e` of the
  form `forall ..xs, A`, this combinator will create a new metavariable for
  each `x` in `xs` until it reaches an `x` whose type is defeq to `t`,
  and instantiate `A` with these, while also reducing `A` if needed.
  It uses `forallMetaTelescopeReducing`.

  This function returns a triple `(mvs, bis, out)` where
  - `mvs` is an array containing the new metavariables.
  - `bis` is an array containing the binder infos for the `mvs`.
  - `out` is `e` but instantiated with the `mvs`.

  Lifted from [https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Lean/Meta/Basic.lean#L41].
-/
def forallMetaTelescopeReducingUntilDefEq
    (e t : Expr) (kind : MetavarKind := MetavarKind.natural) :
    MetaM (Array Expr × Array BinderInfo × Expr) := do
  let (ms, bs, tp) ← forallMetaTelescopeReducing e (some 1) kind
  unless ms.size == 1 do
    if ms.size == 0 then throwError m!"Failed: {← ppExpr e} is not the type of a function."
    else throwError m!"Failed"
  let mut mvs := ms
  let mut bis := bs
  let mut out : Expr := tp
  while !(← isDefEq (← inferType mvs.toList.getLast!) t) do
    let (ms, bs, tp) ← forallMetaTelescopeReducing out (some 1) kind
    unless ms.size == 1 do
      throwError m!"Failed to find {← ppExpr t} as the type of a parameter of {← ppExpr e}."
    mvs := mvs ++ ms
    bis := bis ++ bs
    out := tp
  return (mvs, bis, out)

/-- Get the user-facing name for the given metavariable. -/
def _root_.Lean.MVarId.getUserName (mvarId : MVarId) : MetaM Name := do
  let decl ← mvarId.getDecl
  return decl.userName

def mkGeneralizeArgs (mvarId : MVarId) (hypType : Expr) (hypName : Name) : MetaM (Array GeneralizeArg) := do
  let hypType ← whnf hypType
  let (ind, args) := hypType.getAppFnArgs
  match ← isInductive? ind with
  | some val =>
    let indices := args.drop val.numParams
    let mut genArgs : Array GeneralizeArg := #[]
    for idx in indices do
      unless idx.isFVar || genArgs.any (·.expr == idx) do
        genArgs := genArgs.push
          { expr := idx
            hName? := some (← mkFreshUserName $ hypName.append `eq) }
    return genArgs
  | none =>
    throwTacticEx `inversion mvarId
      m!"target is not an inductive type{indentExpr hypType}"

partial def substGenEqs (mvarId : MVarId) (eqs : List FVarId) : MetaM (Option MVarId) := do
  match eqs with
  | [] => return some mvarId
  | e :: rest =>
    mvarId.withContext do
      match (← getLCtx).find? e with
      | none => substGenEqs mvarId rest
      | some decl =>
        let ty ← instantiateMVars decl.type
        if !ty.isEq && !ty.isHEq then
          substGenEqs mvarId rest
        else
          match ← observing? (mvarId.cases e) with
          | none => substGenEqs mvarId rest
          | some #[] => return none
          | some #[s] =>
              let rest := rest.filterMap fun f => (s.subst.apply (mkFVar f)).fvarId?
              let newEqs := s.fields.toList.filterMap (·.fvarId?)
              substGenEqs s.mvarId (newEqs ++ rest)
          | some sgs =>
              throwTacticEx `inversion mvarId
                m!"error: `cases` on the equation{indentExpr ty}produced \
                   {sgs.size} subgoals, but an equality admits at most one"

end Lean.Meta

namespace Lean.Elab.Tactic
open Meta Term

/--
  `apply t at i` uses forward reasoning with `t` at the hypothesis `i`.
  Explicitly, if `t : α₁ → ⋯ → αᵢ → ⋯ → αₙ` and `i` has type `αᵢ`, then this tactic adds
  metavariables/goals for any terms of `αⱼ` for `j = 1, …, i-1`,
  then replaces the type of `i` with `αᵢ₊₁ → ⋯ → αₙ` by applying those metavariables and the
  original `i`.

  Lifted from [https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/ApplyAt.lean].
-/
elab "apply " t:term " at " i:ident : tactic => withSynthesize <| withMainContext do
  let f ← elabTermForApply t
  let some ldecl := (← getLCtx).findFromUserName? i.getId
    | throwErrorAt i m!"Identifier {i} not found"
  let (mvs, bis, _) ← forallMetaTelescopeReducingUntilDefEq (← inferType f) ldecl.type
  for (m, b) in mvs.zip bis do
    if b.isInstImplicit && !(← m.mvarId!.isAssigned) then
      try m.mvarId!.inferInstance
      catch _ => continue
  let (_, mainGoal) ← (← getMainGoal).note ldecl.userName
    (← mkAppOptM' f (mvs.pop.push ldecl.toExpr |>.map some))
  let mainGoal ← mainGoal.tryClear ldecl.fvarId
  replaceMainGoal <| [mainGoal] ++ mvs.pop.toList.map (·.mvarId!)

structure InversionConfig where
  clear : Bool := false

declare_config_elab elabInversionConfig InversionConfig

private def inversionCore (h : FVarId) (config : InversionConfig) : TacticM (List MVarId) := withMainContext do
  let goal ← getMainGoal
  let hypType ← h.getType
  let hypName ← h.getUserName
  let (target, goal) ←
    if config.clear then pure (h, goal)
    else (← goal.assert hypName hypType (.fvar h)).intro1P
  let genArgs ← goal.withContext do
    mkGeneralizeArgs goal hypType hypName
  let (subst, newVars, goal) ← goal.withContext do
    goal.generalizeHyp genArgs #[target]
  let targetExpr := subst.apply (mkFVar target)
  let target ← match targetExpr with
    | .fvar f => pure f
    | _ =>
      throwTacticEx `inversion goal
        m!"generalization mapped the inverted hypothesis to a non-variable term{indentExpr targetExpr}"
  let genEqs := newVars.toList.drop genArgs.size
  let subgoals ← goal.cases target
  let newGoals ← subgoals.toList.filterMapM fun s => do
    let eqs := genEqs.filterMap fun f => (s.subst.apply (mkFVar f)).fvarId?
    substGenEqs s.mvarId eqs
  return newGoals

private def evalInvAlt (goals : List MVarId) (alt : TSyntax `invAlt) : TacticM MVarId :=
  match alt with
  | `(invAlt| | $tag:ident $vars:binderIdent* => $tactics:tacticSeq) => do
    match ← findTag? goals tag.getId with
    | some goal =>
      let goals ← renameInaccessibles goal vars >>= evalTacticAt tactics
      unless goals.isEmpty do
        reportUnsolvedGoals goals
      return goal
    | none =>
      let goalMsgs ← goals.mapM (.ofName <$> ·.getUserName)
      let msg ← if goals.isEmpty
        then pure m!"There are no unhandled alternatives"
        else pure m!"Expected {.orList goalMsgs}"
      throwError m!"Invalid alternative name `{tag.getId}`: {msg}"
  | stx@`(invAlt| | _ $_vars:binderIdent* => $_tactics:tacticSeq) =>
    -- TODO: allow the last alternative to be a wildcard
    throwErrorAt stx "inversion alternatives must be explicitly named"
  | stx => throwErrorAt stx "could not parse inversion alternative"

@[tactic Lean.Parser.inversion]
public meta def evalInversion : Tactic
  | `(tactic| inversion $config $h:ident $[with $[$alts?:invAlt]*]?) => do
    let config ← elabInversionConfig config
    let mut goals ← inversionCore (← getFVarId h) config
    if let some alts := alts? then
      for alt in alts do
        let goal ← evalInvAlt goals alt
        goals := goals.erase goal
      unless goals.isEmpty do
        reportUnsolvedGoals goals
    replaceMainGoal goals
  | stx => throwErrorAt stx "could not parse inversion tactic"

end Lean.Elab.Tactic

end -- meta section

-- [https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Lemma.lean]
-- [https://github.com/leanprover-community/batteries/blob/main/Batteries/Tactic/Lemma.lean]
/-- Synonym for `theorem`. -/
macro "lemma " thm:declId sig:declSig val:declVal : command => `(theorem $thm $sig $val)

set_option trace.debug true

example (f : Nat → Nat) (n : Nat) (le : f n ≤ 0) : f n = 0 := by
  -- cases le /- Dependent elimination failed: Failed to solve equation 0 = f n -/
  inversion le with | refl e => rw [← e]

example (f : Nat → Nat) (n : Nat) (le : f n ≤ 0) : f n = 0 := by
  inversion +clear le; rfl

/-- warning: declaration uses `sorry` -/
#guard_msgs(warning) in
example (f : Nat → Nat) (n m : Nat) (le : f n ≤ f m) : f n = 0 := by
  inversion +clear le with
  | refl e =>
    rw [← e]
    sorry
  | step k _ e =>
    sorry

example (H : Bool → Nat → False) (n : Nat) : False := by
  apply H at n; apply n; exact true

lemma doubleNegation : ∀ P, P → ¬ ¬ P := by
  intro P p np; exact (np p)
