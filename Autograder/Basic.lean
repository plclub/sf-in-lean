module

public import Lean
public import Autograder.Attributes
public import Autograder.Util

public section

open Lean DebugT VisitedT

def getGradedAttribute? (name : Name) : CoreM (Option Graded) := do
  return gradedAttr.getParam? (← getEnv) name

def getGradedAttribute! (name : Name) : CoreM Graded := do
  return (← getGradedAttribute? name).get!

def getGradedPoints? (name : Name) : CoreM (Option PointAmount) := return match ← getGradedAttribute? name with
  | some (.assignment points) => some points
  | _ => none

def isGradedIgnore? (name : Name) : CoreM Bool := return match ← getGradedAttribute? name with
  | some .ignore => true
  | _ => false

def PointAmount.format (points : Option PointAmount) : String := match points with
  | none => "none"
  | some points => toString <| (Float.ofInt points.num) / (Float.ofInt points.den) -- TODO don't use floats

/--
Collect all declarations from the environment that are "assignments" i.e. have the `@[graded n]` attribute.
-/
def collectAssignments : CoreM (Array (Name × ConstantInfo)) := do
  let mut results := #[]
  for (name, constInfo) in (← getEnv).constants.toList do
    if let some (.assignment _) ← getGradedAttribute? name then
      results := results.push ⟨name, constInfo⟩
  return results

/--
Compare binder names.

For example in the `forallE` branch with `bnl=m._@.Assignment.2314059840._hygCtx._hyg.8 bnr=m._@.Submission.2314059840._hygCtx._hyg.8`, we need to erase the macro scopes to compare the names, otherwise they are considered ≠.

NH: Is this correct?
-/
def compareBinderNames (l r : Name) := Id.run do
  let l' := l.eraseMacroScopes
  let r' := r.eraseMacroScopes
  -- if l != r then
    -- dbg_trace s!"erased macro scopes {l} => {l'}, {r} => {r'}"
  l' == r'

-- NH: is it correct to compare these?
deriving instance BEq for QuotKind
deriving instance BEq for QuotVal

mutual

/--
Compare `expr_a` from the CoreM (assignment) with `expr_s` from the environment `env_s` (submission).
-/
partial def deepSynEq (env_s : Environment) (expr_a expr_s : Expr) : DebugT (VisitedT CoreM) Bool := call (m := VisitedT CoreM) do
  dbg s!"deepSynEq: comparing {expr_a} with {expr_s}"
  match expr_a, expr_s with
  | .bvar i, .bvar j => return i == j
  | .fvar _, .fvar _ => panic! "BUG: expressions should not contain free variables by the assumption that the module is well typed"
  | .mvar _, .mvar _ => panic! "BUG: expressions should not contain metavariables by the assumption that the module is well sorted"
  | .sort ua, .sort us => return ua == us
  | .const na ua, .const ns us => return na == ns && (← deepSynEqName env_s na) && ua == us
  | .app fa aa, .app fs as => return (← deepSynEq env_s fa fs) && (← deepSynEq env_s aa as)
  | .lam bna bta ba bia, .lam bns bts bs bis => return compareBinderNames bna bns && (← deepSynEq env_s bta bts) && (← deepSynEq env_s ba bs) && bia == bis
  | .forallE bna bta ba bia, .forallE bns bts bs bis => return compareBinderNames bna bns && (← deepSynEq env_s bta bts) && (← deepSynEq env_s ba bs) && bia == bis
  | .letE na ta va ba nondepa, .letE ns ts vs bs nondeps => return compareBinderNames na ns && (← deepSynEq env_s ta ts) && (← deepSynEq env_s va vs) && (← deepSynEq env_s ba bs) && nondepa == nondeps
  | .mdata _ a, .mdata _ s =>
    dbg "deepSynEq: ignoring metadata" -- ignore metadata for now
    deepSynEq env_s a s
  | .proj na i a, .proj ns j s => return na == ns && (← deepSynEqName env_s na) && i == j && (← deepSynEq env_s a s)
  | .lit a, .lit s => return a == s
  | _, _ => return false

/--
Compare `name` from the CoreM (assignment) with the environment `env_s` (submission).
The type of `name`, various metadata like reducibility attributes and its value are compared between the environments.

NH: I see no reason to compare opaques like proof terms based on the assumption that even if they have changed, it should not have an observable effect
-/
partial def deepSynEqName (env_s : Environment) (name : Name) (compareOpaques := false) : DebugT (VisitedT CoreM) Bool := call (m := VisitedT CoreM) <|
  defer (m := DebugT (VisitedT CoreM)) (fun b => do
    if !b then
      -- Marks the name false if the prediction was wrong
      markFalse name (m := CoreM)
  ) do
  if let some eq := ← visited? name (m := CoreM) then
    dbg s!"deepSynEqName: already visited {name} => {eq}"
    return eq

  -- We mark the name to avoid infinite recursion, and adjust if the function returns false
  -- NH: There's probably a more elegant way to do this
  markTrue name (m := CoreM)

  dbg s!"deepSynEqName: comparing {name}"

  let env_a ← getEnv
  let some a_info := env_a.find? name | return false
  let some s_info := env_s.find? name | return false

  if let some Graded.ignore ← getGradedAttribute? name then
    dbg s!"deepSynEqName: ignoring {name} (comparing only their types)"
    return ← deepSynEq env_s a_info.type s_info.type

  -- Check that the types of the constants are syntactically equal
  if ! (← deepSynEq env_s a_info.type s_info.type) then return false
  if a_info.type != s_info.type then
    panic! "Types don't match"

  -- Check that level params are equal
  if ! a_info.levelParams == s_info.levelParams then return false

  -- Check that reducibility attributes haven't been changed
  if ! getReducibilityStatusCore env_a name == getReducibilityStatusCore env_s name then return false

  match a_info, s_info with
  | .axiomInfo a, .axiomInfo s => return a.isUnsafe == s.isUnsafe
  | .defnInfo a, .defnInfo s => return a.safety == s.safety && (← deepSynEq env_s a.value s.value)
  | .thmInfo a, .thmInfo s => return !compareOpaques || (← deepSynEq env_s a.value s.value)
  | .opaqueInfo a, .opaqueInfo s => return a.isUnsafe == s.isUnsafe && (!compareOpaques || (← deepSynEq env_s a.value s.value))
  | .quotInfo a, .quotInfo s => return a == s
  | .inductInfo a, .inductInfo s => (a.ctors.zip s.ctors).allM fun ⟨ctor_a, ctor_s⟩ => return ctor_a == ctor_s && (← deepSynEqName env_s ctor_a)
  | .ctorInfo a, .ctorInfo s => return a == s -- also compares their names which is unnecessary
  | .recInfo a, .recInfo s => return a.isUnsafe == s.isUnsafe
    && a.numParams == s.numParams
    && a.numIndices == s.numIndices
    && a.numMotives == s.numMotives
    && a.numMinors == s.numMinors
    && (← (a.rules.zip s.rules).allM fun ⟨rule_a, rule_s⟩ => do
      return rule_a.nfields == rule_s.nfields && (← deepSynEq env_s rule_a.rhs rule_s.rhs))
  | _, _ => return false

end

def allowedAxioms := #[`propext, `Quot.sound, `Classical.choice]

def Lean.ConstantInfo.eqKind (c1 c2 : ConstantInfo) : Bool := (c1.isDefinition && c2.isDefinition) || (c1.isTheorem && c2.isTheorem)

local instance : Inhabited Core.Context where
  default := { fileName := "", fileMap := default }

def Graded.points (self : Graded) : Option Rat := match self with
  | assignment n => some n
  | .ignore => none

structure Report where
  name : Name
  points_awarded : Option Rat
  points_maximum : Option Rat
  errors : Array String
  deriving Inhabited, Repr

/--
Check a single constant. Runs in the assignment's CoreM.
-/
def checkName (env_s : Environment) (name : Name) : DebugT (VisitedT CoreM) Report := do
  let points_maximum := (← getGradedAttribute! name).points
  let const_a := ((← getEnv).find? name).get!

  let some const_s := env_s.find? name
  | return {
      name,
      errors := #[s!"Could not find {name} in submission"]
      points_maximum
      points_awarded := none
    }

  if ! const_a.eqKind const_s then
    let kindName := if const_a.isDefinition then "definition" else if const_a.isTheorem then "theorem" else panic! "BUG: assignment declaration is not a definition or a theorem"
    return {
      name,
      errors := #[s!"Expected {name} to be a {kindName}"]
      points_maximum
      points_awarded := none
    }

  let mut errors := #[]
  if const_a.isTheorem then
    let typesEqual? ← deepSynEq env_s const_a.type const_s.type
    if ! typesEqual? then
      errors := errors.push s!"The type of {name} does not match the original type"

    if let .error e := Lean.Kernel.check env_s {} (const_s.value! (allowOpaque := true)) then
      panic! s!"BUG: submission failed kernel check even though it was built with lake!\n{← (e.toMessageData {}).format}"

    let axioms ← Core.CoreM.toIO' (collectAxioms name) default { env := env_s }
    if axioms.any (· ∉ allowedAxioms) then
      errors := errors.push s!"{name} relies on an axiom which is not allowed: {axioms}"

  if const_a.isDefinition then
    if ! (← isGradedIgnore? const_a.name) then
      panic! "Grading definitions is not supported, mark with @[graded ignore] instead"

  let some points_maximum := points_maximum
  | return { name, errors, points_maximum, points_awarded := none }

  let points_awarded := some (if errors.isEmpty then points_maximum else 0)
  return { name, errors, points_maximum, points_awarded }

/--
Check every declaration marked for grading in `env_assignment` against what is submitted in `env_submission`.
-/
def check (env_assignment env_submission : Environment) : DebugT (VisitedT IO) Unit := do
  let assignments ← Core.CoreM.toIO' collectAssignments default { env := env_assignment }

  let mut reports := #[]
  for ⟨name, _const_a⟩ in assignments do
    let new_reports ← (checkName env_submission name).toIO default { env := env_assignment }
    reports := reports.push new_reports

  let size ← VisitedT.size (m := IO)
  dbg s!"Total number of names visited: {size}"

  for report in reports do
    IO.println s!"{report.name}: {PointAmount.format report.points_awarded} out of {PointAmount.format report.points_maximum}"
    for error in report.errors do
      IO.println s!"\t{error}"

end
