module

-- For testing cases in this file
meta import all Init.Prelude
public meta import SFLCompat.Recall.Common

/-!
# Recall, checked by elaboration

`sf_recall` lets a chapter restate a definition from earlier in the
development while the build checks that the restatement means the same
thing. The restated declaration is elaborated for real, inside a hidden
namespace, and compared with the original up to definitional equality; the
temporary declaration is then rolled back.

Two forms:

```
sf_recall
  def twice (f : Nat → Nat) (n : Nat) : Nat := f <| f n

sf_recall statement twice_id : twice id 3 = 3
```

What is compared:

* types, always;
* a `def`'s value, safety, and abbreviation status;
* an inductive's constructors, one by one (names, parameter and index
  counts, and each constructor's type);
* a structure's fields, field defaults, and type-class registration;
* a theorem's statement, never its proof.

So a recalled definition may be reformatted or rephrased into something
definitionally equal, and a theorem may be reproved differently or, with
the `statement` form, restated without any proof. The command is global and
available wherever this module is imported.
-/


namespace SFLCompat.Recall.Check

open Lean Elab Command Meta

meta section

structure DeclId where
  /-- This could be a private name. -/
  actual : Name
  display : Name

def DeclId.ofActual (actual : Name) : DeclId :=
  { actual, display := privateToUserName actual }

/-- Look up the actual name in temp elaboration namespace -/
def tempDeclId (userName : Name) : CommandElabM DeclId := do
  let env ← getEnv
  let privateName := mkPrivateName env userName
  let actual ←
    if env.contains privateName then pure privateName
    else if env.contains userName then pure userName
    else throwError "the re-elaborated declaration '{userName}' was not found"
  return .ofActual actual

def renameBackName (chk orig n : Name) : Name :=
  if chk.isPrefixOf n then n.replacePrefix chk orig
  else
    let chk := privateToUserName chk
    if chk.isPrefixOf n then n.replacePrefix chk orig else n

/--
Replaces the name prefix `chk` with `orig` in every constant that `e`
mentions: `chk` itself becomes `orig`, and a longer name such as a hidden
constructor `chk.mk` becomes `orig.mk`. Constructor types mention the
hidden inductive type's name in argument and resulting positions, so this
rewrite is what makes a re-elaborated declaration comparable with the
original.
-/
def renameBack (chk orig : DeclId) (e : Expr) : Expr :=
  e.replace fun
    | .const n us =>
      let n' := renameBackName chk.actual orig.actual n
      if n == n' then none else some (.const n' us)
    | _ => none

/--
Applies `renameBack` to the expressions recorded in an info tree. The info
recorded while elaborating the hidden copy mentions the hidden constants,
so hovers over a recalled declaration would otherwise display the hidden
names; rewriting before the trees are stored makes them display the
originals, which also exist after the hidden copy is rolled back.
-/
partial def renameBackInfoTree (chk orig : DeclId) (t : InfoTree) : InfoTree :=
  match t with
  | .context (.parentDeclCtx n) t' =>
    .context (.parentDeclCtx (renameBackName chk.actual orig.actual n))
      (renameBackInfoTree chk orig t')
  | .context ctx t' => .context ctx (renameBackInfoTree chk orig t')
  | .node i children =>
    let i := match i with
      | .ofTermInfo ti => .ofTermInfo (reTerm ti)
      | .ofDelabTermInfo dti => .ofDelabTermInfo { dti with toTermInfo := reTerm dti.toTermInfo }
      | other => other
    .node i (children.map (renameBackInfoTree chk orig))
  | .hole m => .hole m
where
  reTerm (ti : TermInfo) : TermInfo :=
    { ti with
      expr := renameBack chk orig ti.expr
      expectedType? := ti.expectedType?.map (renameBack chk orig) }

/--
Checks that the types of the original constant `x` and its re-elaborated
counterpart `chk` agree, definitionally. The restated type is first
rewritten by `renameBack renChk renOrig`; the defaults compare a
declaration against its own hidden copy, and the constructor check
overrides them with the enclosing inductive types, whose names the
constructor types mention. The restatement's universe parameters are
instantiated with the original's.
-/
def checkTypesMatch (x chk : DeclId) (ref : Syntax)
    (renChk : DeclId := chk) (renOrig : DeclId := x) (hint : MessageData := .nil) :
    TermElabM Unit := do
  let origInfo ← getConstInfo x.actual
  let chkInfo ← getConstInfo chk.actual
  unless origInfo.levelParams.length == chkInfo.levelParams.length do
    throwErrorAt ref (m!"universe parameters of '{x.display}' do not match" ++ hint)
  let chkType := (renameBack renChk renOrig chkInfo.type).instantiateLevelParams
    chkInfo.levelParams (origInfo.levelParams.map .param)
  unless ← isDefEq chkType origInfo.type do
    throwErrorAt ref
      (m!"the statement of '{x.display}' does not match.\n\
          Original:{indentD origInfo.type}\nRestated:{indentD chkType}" ++ hint)

/--
All constructor syntax nodes of a command, in source order: an inductive
type's `| name : ...` alternatives and a structure's `name ::` header.
-/
partial def ctorStxs (stx : Syntax) : Array Syntax :=
  let inner := stx.getArgs.flatMap ctorStxs
  if stx.isOfKind ``Lean.Parser.Command.ctor
      || stx.isOfKind ``Lean.Parser.Command.structCtor then
    #[stx] ++ inner
  else inner

/-- Does the syntax contain a doc comment? -/
def hasDocComment (stx : Syntax) : Bool :=
  (stx.find? (·.isOfKind ``Lean.Parser.Command.docComment)).isSome

/--
Suggestions localized to a mismatched constructor, returned as a pair of
hints for name errors and for type errors. An inductive type's `| name : ...` alternative is replaced
with the original constructor's own source. A structure's `name ::` header
can carry a name fix but not a field fix, so its type errors keep `outer`,
the suggestion that replaces the whole restatement. A constructor without
syntax also falls back to `outer`.
-/
def ctorHints (ctorRef : Syntax) (origCtor origShort : Name) (outer : MessageData) :
    TermElabM (MessageData × MessageData) := do
  try
    if ctorRef.isOfKind ``Lean.Parser.Command.ctor then
      let origSrc := dedent (← sourceOf origCtor)
      -- A restatement without a doc comment gets a suggestion without one;
      -- the meaning check does not compare documentation.
      let origSrc := if hasDocComment ctorRef then origSrc
        else stripLeadingComments origSrc
      let restatedSrc ← sourceOfSyntax ctorRef
      let h ← replaceWithOriginalHint ctorRef origSrc restatedSrc
      return (h, h)
    if ctorRef.isOfKind ``Lean.Parser.Command.structCtor then
      let restatedSrc ← sourceOfSyntax ctorRef
      let h ← replaceWithOriginalHint ctorRef s!"{origShort} ::" restatedSrc
      return (h, outer)
    return (outer, outer)
  catch _ => return (outer, outer)

/--
Checks a re-elaborated declaration against the original, definitionally.
Errors point at `ref`, the restated command, except for constructor
mismatches, which point at the offending constructor within it.
-/
def checkMatch (x chk : DeclId) (ref : Syntax) (hint : MessageData := .nil) :
    TermElabM Unit := do
  checkTypesMatch x chk ref (hint := hint)
  let origInfo ← getConstInfo x.actual
  let chkInfo ← getConstInfo chk.actual
  match origInfo, chkInfo with
  | .defnInfo orig, .defnInfo restated =>
    let chkVal := (renameBack chk x restated.value).instantiateLevelParams
      restated.levelParams (orig.levelParams.map .param)
    unless ← isDefEq chkVal orig.value do
      throwErrorAt ref
        (m!"the value of '{x.display}' does not match.\n\
            Original:{indentD orig.value}\nRestated:{indentD chkVal}" ++ hint)
  | .inductInfo orig, .inductInfo restated =>
    unless orig.numParams == restated.numParams && orig.numIndices == restated.numIndices do
      throwErrorAt ref (m!"parameters or indices of '{x.display}' do not match" ++ hint)
    unless orig.ctors.length == restated.ctors.length do
      throwErrorAt ref
        (m!"'{x.display}' has {orig.ctors.length} constructors, \
            the restatement has {restated.ctors.length}" ++ hint)
    -- A `structure` that writes no `name ::` header has a constructor
    -- without syntax; the whole command remains the fallback position.
    let ctorRefs := ctorStxs ref
    let mut i := 0
    for origCtorActual in orig.ctors, chkCtorActual in restated.ctors do
      let origCtor := DeclId.ofActual origCtorActual
      let chkCtor := DeclId.ofActual chkCtorActual
      let ctorRef := ctorRefs[i]?.getD ref
      let origShort := origCtor.actual.replacePrefix x.actual .anonymous
      let (nameHint, typeHint) ← ctorHints ctorRef origCtor.actual origShort hint
      let renamedChkCtor := DeclId.ofActual <|
        chkCtor.actual.replacePrefix chk.actual x.actual
      unless origCtor.actual == renamedChkCtor.actual do
        throwErrorAt ctorRef
          (m!"constructor '{renamedChkCtor.display}' does not match \
              '{origCtor.display}'" ++ nameHint)
      checkTypesMatch origCtor chkCtor ctorRef (renChk := chk) (renOrig := x) (hint := typeHint)
      i := i + 1
    -- A structure's field names are part of its interface, and the
    -- constructor's type does not record them, so they are compared
    -- through the environment's structure information.
    let env ← getEnv
    match getStructureInfo? env x.actual, getStructureInfo? env chk.actual with
    | some origSi, some chkSi =>
      let origFields := origSi.fieldNames.map DeclId.ofActual
      let chkFields := chkSi.fieldNames.map DeclId.ofActual
      unless origFields.map (·.actual) == chkFields.map (·.actual) do
        throwErrorAt ref
          (m!"the fields of '{x.display}' do not match.\n\
              Original:{indentD (toMessageData (origFields.map (·.display)).toList)}\n\
              Restated:{indentD (toMessageData (chkFields.map (·.display)).toList)}" ++ hint)
      unless getOutParamPositions? env x.actual == getOutParamPositions? env chk.actual
          && getOutLevelParamPositions? env x.actual == getOutLevelParamPositions? env chk.actual do
        throwErrorAt ref (m!"the type-class metadata of '{x.display}' does not match" ++ hint)
    | some _, none =>
      throwErrorAt ref (m!"'{x.display}' is a structure, but the restatement is not" ++ hint)
    | none, some _ =>
      throwErrorAt ref (m!"'{x.display}' is not a structure, but the restatement is one" ++ hint)
    | none, none => pure ()
  -- A theorem's proof is not compared; restating it as a `def` is also
  -- accepted, since only the statement matters.
  | .thmInfo _, .thmInfo _ => pure ()
  | .thmInfo _, .defnInfo _ => pure ()
  | .axiomInfo _, .axiomInfo _ => pure ()
  | .opaqueInfo _, .opaqueInfo _ => pure ()
  | _, _ =>
    throwErrorAt ref
      (m!"'{x.display}' and its restatement are different kinds of declaration" ++ hint)

/--
`sf_recall` restates a definition from earlier in the development and checks
that the restatement means the same thing. `sf_recall statement x : T` checks
that `T` matches the statement of the theorem `x`.
-/
syntax (name := recallChk) "sf_recall " command : command

@[inherit_doc recallChk]
syntax (name := recallChkStmt) "sf_recall " &"statement " ident " : " term : command

elab_rules : command
  | `(sf_recall $cmd:command) => do
    let decl ← declaredName cmd
    let xActual ← liftCoreM <| withoutExporting <|
      realizeGlobalConstNoOverloadWithInfo decl.ident
    let x := DeclId.ofActual xActual
    -- The restatement elaborates unchanged inside a fresh hidden namespace:
    -- self-references (an inductive's own name in its constructor types, in
    -- resulting-type position included) resolve to the hidden copy, and
    -- every other name resolves as it would at the recall site. The
    -- namespace comes from the name generator: `_uniq` names cannot be
    -- written in source, so it is collision-free, and unlike a macro-scoped
    -- name it is an ordinary component, so declarations under it keep the
    -- prefix structure that `renameBack` and the constructor comparison
    -- rely on.
    let ns ← liftCoreM (mkFreshId : CoreM Name)
    -- Any mismatch gets a clickable fix: replace the restatement with the
    -- original's source text, indented like the restatement. The helpers
    -- for recovering and re-indenting source are shared with the
    -- byte-for-byte variant.
    -- A failed hint must not fail the check: not every constant has a
    -- declaration range or sources on the search path.
    let hint ←
      try
        let original := dedent (← sourceOf x.actual)
        let original := if hasDocComment cmd then original
          else stripLeadingComments original
        let restated ← sourceOfSyntax cmd
        liftCoreM <| replaceWithOriginalHint cmd original restated
      catch _ => pure .nil
    let envBefore ← getEnv
    try
      let chk ← withScope (fun sc => { sc with currNamespace := sc.currNamespace ++ ns }) do
        let saved ← getResetInfoTrees
        try
          elabCommand cmd
          -- this could be a private name
          let userName := (← getScope).currNamespace ++ decl.written
          let chk ← tempDeclId userName
          let inner ← getResetInfoTrees
          modifyInfoState fun s => { s with trees := saved ++ inner.map (renameBackInfoTree chk x) }
          return chk
        catch e =>
          let inner ← getResetInfoTrees
          modifyInfoState fun s => { s with trees := saved ++ inner }
          throw e
      runTermElabM fun _ => checkMatch x chk cmd (hint := hint)
    finally
      setEnv envBefore
  | `(sf_recall statement $ident:ident : $stmt:term) => do
    let xActual ← liftCoreM <| withoutExporting <|
      realizeGlobalConstNoOverloadWithInfo ident
    let x := DeclId.ofActual xActual
    addConstInfo ident x.actual
    let region := mkNullNode #[ident.raw, stmt.raw]
    let restated ← sourceOfSyntax region
    runTermElabM fun _ => do
      -- The suggestion restates the original's type as the pretty-printer
      -- renders it. The statement cannot be carved out of the original's
      -- source, since finding its boundary would require parsing the
      -- source in the elaboration context of its declaration site.
      let hint ←
        try
          let origInfo ← getConstInfo x.actual
          let printed ← ppExpr origInfo.type
          replaceWithOriginalHint region
            s!"{ident.getId} : {printed}" restated
        catch _ => pure .nil
      let t ← Term.elabType stmt
      Term.synthesizeSyntheticMVarsNoPostponing
      -- Remaining level metavariables become parameters, so the restatement
      -- must carry as many universe parameters as the original; comparing
      -- against fresh level metavariables instead would let a fixed
      -- universe pass for a polymorphic original.
      let t ← instantiateMVars (← Term.levelMVarToParam t)
      let origInfo ← getConstInfo x.actual
      let stParams := (collectLevelParams {} t).params
      unless stParams.size == origInfo.levelParams.length do
        throwErrorAt stmt
          (m!"universe parameters of '{x.display}' do not match" ++ hint)
      let t := t.instantiateLevelParams stParams.toList
        (origInfo.levelParams.map .param)
      unless ← isDefEq t origInfo.type do
        throwErrorAt stmt
          (m!"the restated statement of '{x.display}' does not match.\n\
              Original:{indentD origInfo.type}\nRestated:{indentD t}" ++ hint)

end
namespace Tests

sf_recall
  inductive Nat where
  | zero
  | succ (n : Nat) : Nat

-- A constructor mismatch is reported at the offending constructor, not at
-- the whole restatement.
/--
@ +4:2...26
error: the statement of 'Nat.succ' does not match.
Original:
  Nat → Nat
Restated:
  Nat → Nat → Nat

Hint: Replace the restatement with the original:
  | succ (̲n̲ ̲: N̲a̲t̲)̲ ̲:̲ ̲Nat ̵→̵ ̵N̵a̵t̵ ̵→̵ ̵N̵a̵t̵
-/
#guard_msgs (positions := true) in
sf_recall
  inductive Nat where
  | zero
  | succ : Nat → Nat → Nat

inductive Palette where
  | red | green | blue

def twice (f : Nat → Nat) (n : Nat) : Nat := f (f n)

theorem twice_id : twice id 3 = 3 := rfl

sf_recall
  inductive Palette where
    | red | green | blue

-- A misnamed constructor's suggestion replaces just that constructor.
/--
@ +3:18...24
error: constructor 'SFLCompat.Recall.Check.Tests.Palette.blau' does not match 'SFLCompat.Recall.Check.Tests.Palette.blue'

Hint: Replace the restatement with the original:
  | b̵l̵a̵u̵b̲l̲u̲e̲
-/
#guard_msgs (positions := true) in
sf_recall
  inductive Palette where
    | red | green | blau

-- Definitionally equal reformulations are accepted.
sf_recall
  def twice (f : Nat → Nat) (n : Nat) : Nat := f <| f n

sf_recall statement twice_id : twice id 3 = 3

-- Imported names can be recalled too.
sf_recall statement Nat.add_comm : ∀ (n m : Nat), n + m = m + n

-- The statement form counts universe parameters: a placeholder universe
-- becomes a parameter and matches, and a fixed universe is rejected.
theorem poly_refl.{u} : ∀ {α : Sort u} (a : α), a = a := fun _ => rfl

sf_recall statement poly_refl : ∀ {α : Sort _} (a : α), a = a

/--
error: universe parameters of 'SFLCompat.Recall.Check.Tests.poly_refl' do not match

Hint: Replace the restatement with the original:
  poly_refl : ∀ {α : T̵y̵p̵e̵}̵S̲o̲r̲t̲ ̲u̲}̲ (a : α), a = a
-/
#guard_msgs in
sf_recall statement poly_refl : ∀ {α : Type} (a : α), a = a

-- A standard library structure with the default constructor name.
sf_recall
  structure Prod (α : Type u) (β : Type v) where
    fst : α
    snd : β

-- A standard library structure with a custom constructor name.
sf_recall
  structure ULift.{r, s} (α : Type s) : Type (max s r) where
    up ::
    down : α

-- A wrong constructor name written as a `name ::` header is reported at
-- that header.
/--
@ +3:4...13
error: constructor 'ULift.uuuppp' does not match 'ULift.up'

Hint: Replace the restatement with the original:
  u̵u̵u̵p̵p̵p̵u̲p̲ ::
-/
#guard_msgs (positions := true) in
sf_recall
  structure ULift.{r, s} (α : Type s) : Type (max s r) where
    uuuppp ::
    down : α

-- A renamed field is rejected: the constructor's type does not change,
-- but the projections readers use would.
/--
error: the fields of 'Prod' do not match.
Original:
  [fst, snd]
Restated:
  [fst, other]

Hint: Replace the restatement with the original:
  s̵t̵r̵u̵c̵t̵u̵r̵e̵ ̵P̵r̵o̵d̵ ̵(̵α̵ ̵:̵ ̵T̵y̵p̵e̵ ̵u̵)̵ ̵(̵β̵ ̵:̵ ̵T̵y̵p̵e̵ ̵v̵)̵ ̵w̵h̵e̵r̵e̵
  ̵ ̵ ̵ ̵ ̵f̵s̵t̵ ̵:̵ ̵α̵
  ̵ ̵ ̵ ̵ ̵o̵t̵h̵e̵r̵ ̵:̵ ̵β̵s̲t̲r̲u̲c̲t̲u̲r̲e̲ ̲P̲r̲o̲d̲ ̲(̲α̲ ̲:̲ ̲T̲y̲p̲e̲ ̲u̲)̲ ̲(̲β̲ ̲:̲ ̲T̲y̲p̲e̲ ̲v̲)̲ ̲w̲h̲e̲r̲e̲
  ̲ ̲ ̲ ̲ ̲ ̲ ̲/̲-̲-̲
  ̲ ̲ ̲ ̲ ̲ ̲ ̲C̲o̲n̲s̲t̲r̲u̲c̲t̲s̲ ̲a̲ ̲p̲a̲i̲r̲.̲ ̲T̲h̲i̲s̲ ̲i̲s̲ ̲u̲s̲u̲a̲l̲l̲y̲ ̲w̲r̲i̲t̲t̲e̲n̲ ̲`̲(̲x̲,̲ ̲y̲)̲`̲ ̲i̲n̲s̲t̲e̲a̲d̲ ̲o̲f̲ ̲`̲P̲r̲o̲d̲.̲m̲k̲ ̲x̲ ̲y̲`̲.̲
  ̲ ̲ ̲ ̲ ̲ ̲ ̲-̲/̲
  ̲ ̲ ̲ ̲ ̲ ̲ ̲m̲k̲ ̲:̲:̲
  ̲ ̲ ̲ ̲ ̲ ̲ ̲/̲-̲-̲ ̲T̲h̲e̲ ̲f̲i̲r̲s̲t̲ ̲e̲l̲e̲m̲e̲n̲t̲ ̲o̲f̲ ̲a̲ ̲p̲a̲i̲r̲.̲ ̲-̲/̲
  ̲ ̲ ̲ ̲ ̲ ̲ ̲f̲s̲t̲ ̲:̲ ̲α̲
  ̲ ̲ ̲ ̲ ̲ ̲ ̲/̲-̲-̲ ̲T̲h̲e̲ ̲s̲e̲c̲o̲n̲d̲ ̲e̲l̲e̲m̲e̲n̲t̲ ̲o̲f̲ ̲a̲ ̲p̲a̲i̲r̲.̲ ̲-̲/̲
  ̲ ̲ ̲ ̲ ̲ ̲ ̲s̲n̲d̲ ̲:̲ ̲β̲
-/
#guard_msgs in
sf_recall
  structure Prod (α : Type u) (β : Type v) where
    fst : α
    other : β

-- Restating it with the default constructor name is rejected. A structure
-- has no constructor syntax node, so the error is on the whole command.
/--
error: constructor 'ULift.mk' does not match 'ULift.up'

Hint: Replace the restatement with the original:
  s̵t̵r̵u̵c̵t̵u̵r̵e̵ ̵U̵L̵i̵f̵t̵.̵{̵r̵,̵ ̵s̵}̵ ̵(̵α̵ ̵:̵ ̵T̵y̵p̵e̵ ̵s̵)̵ ̵:̵ ̵T̵y̵p̵e̵ ̵(̵m̵a̵x̵ ̵s̵ ̵r̵)̵ ̵w̵h̵e̵r̵e̵
  ̵ ̵ ̵ ̵ ̵d̵o̵w̵n̵ ̵:̵ ̵α̵s̲t̲r̲u̲c̲t̲u̲r̲e̲ ̲U̲L̲i̲f̲t̲.̲{̲r̲,̲ ̲s̲}̲ ̲(̲α̲ ̲:̲ ̲T̲y̲p̲e̲ ̲s̲)̲ ̲:̲ ̲T̲y̲p̲e̲ ̲(̲m̲a̲x̲ ̲s̲ ̲r̲)̲ ̲w̲h̲e̲r̲e̲
  ̲ ̲ ̲ ̲ ̲ ̲ ̲/̲-̲-̲ ̲W̲r̲a̲p̲s̲ ̲a̲ ̲v̲a̲l̲u̲e̲ ̲t̲o̲ ̲i̲n̲c̲r̲e̲a̲s̲e̲ ̲i̲t̲s̲ ̲t̲y̲p̲e̲'̲s̲ ̲u̲n̲i̲v̲e̲r̲s̲e̲ ̲l̲e̲v̲e̲l̲.̲ ̲-̲/̲
  ̲ ̲ ̲ ̲ ̲ ̲ ̲u̲p̲ ̲:̲:̲
  ̲ ̲ ̲ ̲ ̲ ̲ ̲/̲-̲-̲ ̲E̲x̲t̲r̲a̲c̲t̲s̲ ̲a̲ ̲w̲r̲a̲p̲p̲e̲d̲ ̲v̲a̲l̲u̲e̲ ̲f̲r̲o̲m̲ ̲a̲ ̲u̲n̲i̲v̲e̲r̲s̲e̲-̲l̲i̲f̲t̲e̲d̲ ̲t̲y̲p̲e̲.̲ ̲-̲/̲
  ̲ ̲ ̲ ̲ ̲ ̲ ̲d̲o̲w̲n̲ ̲:̲ ̲α̲
-/
#guard_msgs in
sf_recall
  structure ULift.{r, s} (α : Type s) : Type (max s r) where
    down : α

/--
error: the value of 'SFLCompat.Recall.Check.Tests.twice' does not match.
Original:
  fun f n => f (f n)
Restated:
  fun f n => f n

Hint: Replace the restatement with the original:
  def twice (f : Nat → Nat) (n : Nat) : Nat := f (̲f̲ ̲n)̲
-/
#guard_msgs in
sf_recall
  def twice (f : Nat → Nat) (n : Nat) : Nat := f n

/--
error: the restated command declares several names; recall one declaration at a time
---
error: the restated command declares several names; recall one declaration at a time
-/
#guard_msgs in
sf_recall
  mutual
    def one : Nat := 1
    def two : Nat := 2
  end

open List in
sf_recall
  def List.map (f : α → β) : (l : List α) → List β
    | [] => []
    | x :: xs => f x :: map f xs


-- `sorry` doesn't work

/-- warning: declaration uses `sorry` -/
#guard_msgs in
noncomputable def Foo : Nat := by sorry
/--
error: the value of 'SFLCompat.Recall.Check.Tests.Foo' does not match.
Original:
  sorry
Restated:
  sorry

Hint: Replace the restatement with the original:
  noncomputable def Foo : Nat := by sorry
---
warning: declaration uses `sorry`
-/
#guard_msgs in
sf_recall
  noncomputable def Foo : Nat := by sorry

-- field visibility is not checked

structure Bar where
  private x : Nat
  y : Bool

sf_recall
  structure Bar where
    x : Nat
    y : Bool

end Tests

end  SFLCompat.Recall.Check
