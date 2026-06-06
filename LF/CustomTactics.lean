module

public meta import Lean.Parser.Term
public meta import Lean.Elab.ConfigEval
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.Tactic.Generalize
public meta import Lean.Meta.Tactic.Cases
public meta import Lean.Meta.Tactic.Injection
public meta import Lean.Meta.Tactic.Contradiction

meta section

namespace Lean.Parser
open Term in
/--
  `inversion t` generalizes nonvariable indices of the type of `t` before invoking `cases t`,
  then solves away contradictory generated goals.
  * If `inversion +clear t` is set, `t` is `clear`ed from the context.
  * If `inversion t with h₁ ... hₙ` are provided, the last n hypotheses generated are given these names.
-/
syntax (name := inversion)
  "inversion " (configItem)? ident (" with " (ppSpace colGt binderIdent)+)? : tactic
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

private def mkGeneralizeArgs (hypType : Expr) : MetaM (Array GeneralizeArg) := do
  let hypType ← whnf hypType
  hypType.withApp fun fn args =>
    matchConstInduct fn (fun _ => pure #[]) fun val _ => do
      let indices := args.extract val.numParams args.size
      let mut seen : Array Expr := #[]
      let mut genArgs : Array GeneralizeArg := #[]
      for idx in indices do
        if idx.isFVar || seen.any (· == idx) then continue
        seen := seen.push idx
        genArgs := genArgs.push
          { expr := idx
            xName? := some (← mkFreshUserName `x)
            hName? := some (← mkFreshUserName `heq) }
      pure genArgs

private partial def substGenEqs (mvarId : MVarId) (eqs : List FVarId) :
    MetaM (Option MVarId) := do
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

structure InversionConfig where
  clear : Bool := false

declare_config_elab elabInversionConfig InversionConfig

def inversionCore (h : FVarId) (config : InversionConfig) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let hypType ← h.getType
  let (target, goal) ←
    if config.clear then pure (h, goal)
    else do
      let goal ← goal.assert (← mkFreshUserName `hInv) hypType (mkFVar h)
      goal.intro1P
  let genArgs ← mkGeneralizeArgs hypType
  let (subst, newVars, goal) ← goal.withContext do
    if genArgs.isEmpty then pure (({} : FVarSubst), (#[] : Array FVarId), goal)
    else goal.generalizeHyp genArgs #[target]
  let targetExpr := subst.apply (mkFVar target)
  let target ← match targetExpr with
    | .fvar f => pure f
    | _ => goal.withContext do
        throwTacticEx `inversion goal
          m!"error: generalization mapped the inverted hypothesis to a non-variable term{indentExpr targetExpr}"
  let genEqs := (newVars.extract genArgs.size newVars.size).toList
  let subgoals ← goal.cases target
  let newGoals ← subgoals.toList.filterMapM fun s => do
    let eqs := genEqs.filterMap fun f => (s.subst.apply (mkFVar f)).fvarId?
    substGenEqs s.mvarId eqs
  replaceMainGoal newGoals

@[tactic Lean.Parser.inversion]
public def evalInversion : Tactic
  | `(tactic| inversion $(config?)? $h $[with $hs?*]?) => do
    let config ← elabInversionConfig $ config?.getD default
    inversionCore (← getFVarId h) config
    if let some hs := hs? then
      evalTactic (← `(tactic| rename_i $hs*))
  | _ => throwError m!"could not parse inversion tactic"

end Lean.Elab.Tactic

end -- meta section

-- [https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Lemma.lean]
-- [https://github.com/leanprover-community/batteries/blob/main/Batteries/Tactic/Lemma.lean]
/-- Synonym for `theorem`. -/
macro "lemma " thm:declId sig:declSig val:declVal : command => `(theorem $thm $sig $val)

example (f : Nat → Nat) (n : Nat) (le : f n ≤ 0) : f n = 0 := by
  -- cases le /- Dependent elimination failed: Failed to solve equation 0 = f n -/
  inversion +clear le with e; rfl

example (H : Bool → Nat → False) (n : Nat) : False := by
  apply H at n; apply n; exact true

lemma doubleNegation : ∀ P, P → ¬ ¬ P := by
  intro P p np; exact (np p)
