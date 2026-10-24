import Lean
import LF.Typeclasses

namespace StlcCommon

declare_syntax_cat stlcQuoted

declare_syntax_cat stlcTy

syntax:max "~" term:max : stlcTy
syntax:max "(" stlcTy ")" : stlcTy
syntax:max ident : stlcTy
syntax:50 stlcTy:51 " → " stlcTy:50 : stlcTy
syntax:50 stlcTy:51 " -> " stlcTy:50 : stlcTy

syntax (name := quotedTy) stlcTy : stlcQuoted

declare_syntax_cat stlcVar

syntax:max (name := objectVar) ident : stlcVar
syntax:max "~" term:max : stlcVar

declare_syntax_cat stlcTm

syntax:max "~" term:max : stlcTm
syntax:max "(" stlcTm ")" : stlcTm
syntax:max ident : stlcTm
syntax:75 stlcTm:75 ppSpace stlcTm:76 : stlcTm
syntax:50 "λ " stlcVar " : " stlcTy " . " stlcTm:50 : stlcTm
syntax:max "[" stlcVar " := " stlcTm "] " stlcTm:max : stlcTm

syntax (name := quotedTm) stlcTm : stlcQuoted

declare_syntax_cat stlcCtx

syntax:max "∅" : stlcCtx
syntax:max "~" term:max : stlcCtx
syntax:max ident : stlcCtx
syntax:max stlcVar " ↦ " stlcTy " ; " stlcCtx : stlcCtx

syntax (name := quotedCtx) stlcCtx : stlcQuoted

syntax (name := quotedJudge) stlcCtx " ⊢ " stlcTm " ⦂ " stlcTy : stlcQuoted

syntax:max (name := bracket) "<{ " stlcQuoted " }>" : term

namespace Elab

open Lean Elab Term Meta Tactic.TryThis

def withSourceInfoOf {kind : Name} (ref : Syntax) (stx : TSyntax kind)
    (canonical := true) : TSyntax kind :=
  let info := SourceInfo.fromRef ref (canonical := canonical)
  ⟨stx.raw.setInfo info⟩

def mkObjectIdentFrom (ref : Syntax) (name : String) : Ident :=
  mkIdentFrom ref (Name.mkSimple name)

/--
Disable the unused-variable linter for our synthetic binder fvars.
A bound object language variable may occur through antiquotation,
so Lean's syntactic check is not accurate; and it would also suggest
invalid binder names like `_X`.
-/
@[unused_variables_ignore_fn]
def ignoreUnusedObjectVars : Linter.IgnoreFunction :=
  fun _ stack _ => stack.matches [``StlcCommon.objectVar]

structure Language where
  tyType : Name
  tmType : Name

  arrowCtor : Name
  varCtor   : Name
  appCtor   : Name
  absCtor   : Name

  subst : Name
  hasType  : Name

def Language.mkArrow (lang : Language) (A B : Expr) : Expr :=
  mkApp2 (mkConst lang.arrowCtor) A B

def Language.mkVar (lang : Language) (x : String) : Expr :=
  mkApp (mkConst lang.varCtor) (mkStrLit x)

def Language.mkApp (lang : Language) (f a : Expr) : Expr :=
  mkApp2 (mkConst lang.appCtor) f a

def Language.mkAbs (lang : Language) (x T body : Expr) : Expr :=
  mkApp3 (mkConst lang.absCtor) x T body

/-! See the note on `Language.mkHasType`. -/
def Language.mkSubst (lang : Language) (x s t : Expr) : TermElabM Expr := do
  let some subst ← resolveId? (mkIdent lang.subst)
    | throwError "unknown declaration `{lang.subst}`"
  return mkApp3 subst x s t

-- Fixed to `PartialMap String Ty`
def Language.ctxType (lang : Language) : Expr :=
  mkApp2 (mkConst ``PartialMap) (mkConst ``String) (mkConst lang.tyType)

def Language.mkEmptyCtx (lang : Language) : TermElabM Expr := do
  let stx ← `(∅)
  elabTermEnsuringType stx lang.ctxType

def Language.mkExtendCtx (_lang : Language) (Γ x T : Expr) : TermElabM Expr :=
  mkAppM ``PartialMap.update #[Γ, x, T]

/-!
Trick: resolve the forward-referenced `hasType` here
so that `HasType` notation is aviable when defining `HasType`.
This relies on Lean's `inductive` elabrator implementation detail:
an auxiliary fvar of the inductive type being defined is created
before the consturctors are elaborated to represent this inductive type,
because the constructors need to refer the inductive type.
So once we resolve `HasType`, that auxiliary fvar is correctly used.
I (berberman) think this is better than macro-based notation with `set_option hygiene false`.
-/
def Language.mkHasType (lang : Language) (Γ t T : Expr) : TermElabM Expr := do
  let some hasType ← resolveId? (mkIdent lang.hasType)
    | throwError "unknown declaration `{lang.hasType}`"
  return mkApp3 hasType Γ t T

structure Binding where
  name : String
  fvar : Expr
  lctx : LocalContext

abbrev Scope := List Binding
abbrev FVars := List Binding

def identString (id : Ident) : String :=
  id.getId.eraseMacroScopes.toString

def lookupBinding
    (Γ : List Binding)
    (name : String) : Option Binding :=
  Γ.find? fun b =>
    b.name == name


def addBindingInfo
    (id : Ident)
    (binding : Binding)
    (isBinder := false) : TermElabM Unit :=
  addTermInfo' id binding.fvar (lctx? := some binding.lctx) (isBinder := isBinder)


def mkSyntheticBinding
    (lang : Language)
    (id : Ident) : TermElabM Binding :=
  withLocalDeclD id.getId (mkConst lang.tmType) fun fvar => do
    let lctx ← getLCtx
    return {
      name := identString id
      fvar
      lctx
    }

def mkBinder
    (lang : Language)
    (id : Ident) : TermElabM Binding := do
  let binding ← mkSyntheticBinding lang id
  addBindingInfo id binding (isBinder := true)
  return binding

inductive IdentRole where
  | term
  | type
  | name
  | context
  deriving Repr, BEq

def IdentRole.desc : IdentRole → String
  | term => "term"
  | type => "type"
  | name => "name"
  | context => "context"

inductive IndentKind where
  | object
  | metavar
  deriving Repr, BEq

def isGreek (c : Char) : Bool :=
  let n := c.val.toNat
  decide (
    -- Greek and Coptic
    (0x0370 ≤ n ∧ n ≤ 0x03ff) ∨
    -- Greek Extended
    (0x1f00 ≤ n ∧ n ≤ 0x1fff)
  )

def classifyIdent? (id : Ident) :
    Option (IndentKind × String) := do
  let Name.str .anonymous s ← id.getId.eraseMacroScopes
    | failure
  -- reject «a.b»
  if s.isEmpty || s.contains '.' then
    failure
  let c := s.front
  if c.isUpper then
    return (.object, s)
  else if c.isLower || isGreek c then
    return (.metavar, s)
  else failure

def resolveMetaIdent (lang : Language) (role : IdentRole)
    (expectedType : Expr) (id : Ident) : TermElabM Expr := do

  let some (.metavar, name) := classifyIdent? id
    | throwErrorAt id "expected a metalanguage identifier"

  -- Used only by error branches
  let getCandidates := do
    let mut result := #[]
    for decl in (← getLCtx) do
      unless decl.isImplementationDetail do
        if ← withNewMCtxDepth <|
            isDefEq decl.type expectedType then
          result := result.push decl
    return result

  -- Give one obvious local-variable replacement
  let suggestCandidate (decl : LocalDecl) : TermElabM Unit := do
    let candidate := mkIdentFrom id decl.userName.eraseMacroScopes
    let term : Term := ⟨candidate.raw⟩

    -- quote the Lean variable if its name is in the form of object language variable name
    let bare :=
      match classifyIdent? candidate with
      | some (.metavar, _) => true
      | _ => false

    let suggestion ←
      match role with
      | .term =>
          if bare then
            `(stlcTm| $candidate:ident)
          else
            `(stlcTm| ~$term)
      | .type =>
          if bare then
            `(stlcTy| $candidate:ident)
          else
            `(stlcTy| ~$term)
      | .name =>
          if bare then
            `(stlcVar| $candidate:ident)
          else
            `(stlcVar| ~$term)
      | .context =>
          if bare then
            `(stlcCtx| $candidate:ident)
          else
            `(stlcCtx| ~$term)

    addSuggestion id { suggestion }

  -- Main logic starts here
  let some e ← resolveId? id (withInfo := false)
    | -- we failed to find `id`
      do
        let candidates ← getCandidates

        if let some candidate := candidates[0]? then
          suggestCandidate candidate

        match role with
        | .name =>
            let s : Term := ⟨Syntax.mkStrLit name⟩
            let suggestion ← `(stlcVar| ~$s)
            addSuggestion id { suggestion }
        | .term =>
            let var : Term := mkIdent lang.varCtor
            let s : Term := ⟨Syntax.mkStrLit name⟩
            let app ← `($var $s)
            let suggestion ← `(stlcTm| ~$app)
            addSuggestion id { suggestion }
        | .type | .context => pure ()

        throwErrorAt id m!"unknown metalanguage {role.desc} identifier `{name}`"

  -- we found `id`
  let actualType ← inferType e

  -- add back if we want to only accept local variable but not global constant
  -- unless e.isFVar do
  --   let term : Term := ⟨id.raw⟩
  --   let suggestion : SuggestionText ←
  --     match role with
  --     | .term => `(stlcTm| ~$term)
  --     | .type => `(stlcTy| ~$term)
  --     | .name => `(stlcVar| ~$term)
  --     | .context => `(stlcCtx| ~$term)

  --   addSuggestion id { suggestion }

  --   throwErrorAt id m!"\
  --   `{name}` resolves to a Lean declaration, not a local {role.desc} variable; \
  --   use `~{name}`"

  -- Actual elaboration
  if ← commitWhen <| isDefEq actualType expectedType then
    addTermInfo' id e
    return e

  -- Diagnostics only from here on
  let actualType ← instantiateMVars actualType
  let expectedType ← instantiateMVars expectedType

  let candidates ← getCandidates

  if let some candidate := candidates[0]? then
    suggestCandidate candidate

  -- special check for cases like `fun (x : String) => <{ λ x : τ . x }>`:
  -- the occurrence of `x` is syntactically meta, but Lean variable `x` is a `String` instead of `Tm`
  if role == .term &&  (← withNewMCtxDepth <| isDefEq actualType (mkConst ``String)) then
    let var : Term := mkIdent lang.varCtor
    let x : Term := ⟨id.raw⟩
    let app ← `($var $x)
    let suggestion ← `(stlcTm| ~$app)
    addSuggestion id { suggestion }

  if role == .name then
    let s : Term := ⟨Syntax.mkStrLit name⟩
    let suggestion ← `(stlcVar| ~$s)
    addSuggestion id { suggestion }

  throwErrorAt id m!"\
  metalanguage {role.desc} identifier `{name}` has type
    {actualType}
  but this position expects
    {expectedType}"

def elabStlcVarName (lang : Language) (x : TSyntax `stlcVar) : TermElabM Expr := do
  match x with
  | `(stlcVar| ~$e:term) =>
      elabTermEnsuringType e (mkConst ``String)
  | `(stlcVar| $id:ident) =>
      match classifyIdent? id with
      | some (.object, name) => return mkStrLit name
      | some (.metavar, _) =>
          resolveMetaIdent lang .name (mkConst ``String) id
      | none => throwErrorAt id "\
invalid bare name

Use an uppercase Latin identifier for an object-language name, \
a lowercase/Greek identifier for a Lean String variable, or \
explicit `~...` for a Lean expression."
  | _ => throwUnsupportedSyntax

def elabStlcBinder
    (lang : Language)
    (Γ : Scope)
    (x : TSyntax `stlcVar) :
    TermElabM (Expr × Scope) := do
  match x with
  | `(stlcVar| ~$e:term) => do
      let name ← elabTermEnsuringType e (mkConst ``String)
      return (name, Γ)
  | `(stlcVar| $id:ident) =>
      match classifyIdent? id with
      | some (.object, name) => do
          -- Static object binder.
          let binding ← mkBinder lang id
          return (mkStrLit name, binding :: Γ)
      | some (.metavar, _) => do
          -- Lean String variable: dynamic binder name.
          let name ← resolveMetaIdent lang .name (mkConst ``String) id
          return (name, Γ)
      | none => throwErrorAt id "\
invalid bare binder name

Use an uppercase Latin identifier for a static object-language binder, \
a lowercase/Greek identifier for a Lean String variable, or \
explicit `~...` for an arbitrary Lean name expression."

  | _ => throwUnsupportedSyntax

/-!
Two different continuations:
* `recur` elaborates a child using the complete language.
* `k` continues with the next handler when this handler does not recognize
  the current syntax node.
-/

abbrev TyElab := TSyntax `stlcTy → TermElabM Expr

abbrev TyElabHandler := (recur : TyElab) → (k : TyElab) → TyElab

abbrev TmElab :=
  Scope →
  FVars →
  TSyntax `stlcTm →
  TermElabM (Expr × FVars)

abbrev TmElabHandler := (recur : TmElab) → (k : TmElab) → TmElab

def TyElabHandler.orElse
    (first second : TyElabHandler) :
    TyElabHandler :=
  fun recur k => first recur (second recur k)

def TmElabHandler.orElse
    (first second : TmElabHandler) :
    TmElabHandler :=
  fun recur k => first recur (second recur k)

def unsupportedTy (lang : Language) : TyElab :=
  fun T => do
    match T with
    | `(stlcTy| $id:ident) =>
        match classifyIdent? id with
        | some (.object, name) => do
            -- All handlers declined this uppercase identifier.
            -- Before throwing unknown object type error, check whether there
            -- happens to be a same-named Lean local of the target `Ty` type
            -- to give a useful diagnostic for `T : Ty`.
            let e? ← resolveId? id (withInfo := false)
            if let some e := e? then
              if e.isFVar then
                let actualType ← inferType e
                if ← withNewMCtxDepth <| isDefEq actualType (mkConst lang.tyType) then
                  let term : Term := ⟨id.raw⟩
                  let suggestion ← `(stlcTy| ~$term)
                  addSuggestion id { suggestion }
                  throwErrorAt id m!"\
`{name}` starts with an uppercase Latin letter, so it denotes an \
object-language type here, not the Lean variable `{name}`.

This language has no object-language type named `{name}`.
Use `~{name}`, or rename the Lean variable to a lowercase/Greek name \
such as `τ`."
            throwErrorAt id m!"unknown object-language type `{name}`"
        | _ => throwUnsupportedSyntax
    | _ => throwUnsupportedSyntax

def unsupportedTm : TmElab :=
  fun _ _ _ => throwUnsupportedSyntax

/-- Handles:
* `~` antiquotation
* parentheses
* arrows
* implicit Lean `Ty` antiquotation
-/
def commonTyHandler (lang : Language) : TyElabHandler :=
  fun recur k T => do
    match T with
    | `(stlcTy| ~$e:term) =>
        elabTermEnsuringType e (mkConst lang.tyType)
    | `(stlcTy| ($T:stlcTy)) =>
        recur T
    | `(stlcTy| $A:stlcTy → $B:stlcTy) => do
        let A ← recur A
        let B ← recur B
        return lang.mkArrow A B
    | `(stlcTy| $A:stlcTy -> $B:stlcTy) => do
        let A ← recur A
        let B ← recur B
        return lang.mkArrow A B
    | `(stlcTy| $id:ident) =>
        match classifyIdent? id with
        | some (.metavar, _) =>
            resolveMetaIdent lang .type (mkConst lang.tyType) id
        | some (.object, _) => k T -- handled by downstream
        | none => throwErrorAt id "\
invalid bare type identifier

Use an uppercase Latin identifier for object-language type syntax, \
a lowercase/Greek identifier for a Lean type variable, or \
explicit `~...` for a Lean expression."
    | _ => k T

/--
Handles:
* `~` antiquotation
* variables
* application
* parentheses
* lambda
* substitution
-/
def commonTmHandler
    (lang : Language)
    (elabTy : TyElab) :
    TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    -- Explicit ~ antiquotation
    | `(stlcTm| ~$e:term) =>
        return ( ← elabTermEnsuringType e (mkConst lang.tmType), free)
    -- Identifier
    | `(stlcTm| $id:ident) =>
        match classifyIdent? id with
        | some (.metavar, _) => do
            let e ← resolveMetaIdent lang .term (mkConst lang.tmType) id
            return (e, free)
        | some (.object, name) => do
            -- 1. Lexically bound object variable.
            if let some binding := lookupBinding Γ name then
              addBindingInfo id binding
              return (lang.mkVar name, free)
            -- 2. Existing free object variable.
            if let some binding := lookupBinding free name then
              addBindingInfo id binding
              return (lang.mkVar name, free)
            -- 3. First free occurrence.
            let binding ← mkSyntheticBinding lang id
            addBindingInfo id binding
            return (lang.mkVar name, binding :: free)
        | none => throwErrorAt id "\
invalid bare term identifier

Use an uppercase Latin identifier for an object-language variable, \
a lowercase/Greek identifier for a Lean term variable, or \
explicit `~...` for a Lean expression."

    -- Substitution
    | `(stlcTm| [$x:stlcVar := $s:stlcTm] $t:stlcTm) => do
        let x ← elabStlcVarName lang x
        let (s, free) ← recur Γ free s
        let (t, free) ← recur Γ free t
        return (← lang.mkSubst x s t, free)

    -- Application
    | `(stlcTm| $f:stlcTm $a:stlcTm) => do
        let (f, free) ← recur Γ free f
        let (a, free) ← recur Γ free a
        return (lang.mkApp f a, free)

    -- Parentheses
    | `(stlcTm| ($t:stlcTm)) =>
        recur Γ free t

    -- Lambda
    | `(stlcTm| λ $x:stlcVar : $T:stlcTy . $body:stlcTm) => do
        let T ← elabTy T
        let (x, Γ) ← elabStlcBinder lang Γ x
        let (body, free) ← recur Γ free body
        return (lang.mkAbs x T body, free)

    | _ => k Γ free t


abbrev CtxElab := TSyntax `stlcCtx → TermElabM (Expr × Scope)

partial def elabCtxCommon
    (lang : Language)
    (elabTy : TyElab)
    (Γ : TSyntax `stlcCtx) :
    TermElabM (Expr × Scope) := do
  match Γ with
  -- Empty object context.
  | `(stlcCtx| ∅) => do
      return (← lang.mkEmptyCtx, [])
  | `(stlcCtx| $id:ident) =>
      match classifyIdent? id with
      | some (.metavar, _) =>
          return (← resolveMetaIdent lang .context lang.ctxType id, [])
      | some (.object, name) => do
          let ΓTerm : Term := ⟨id.raw⟩
          let suggestion ← `(stlcCtx| ~$ΓTerm)
          addSuggestion id { suggestion }
          throwErrorAt id m!"\
`{name}` starts with an uppercase Latin letter, so it denotes an \
object-language identifier.

Object-language context variables do not exist.
Use a lowercase/Greek Lean context variable such as `Γ`, or explicitly \
antiquote a Lean context expression using `~...`."
      | none => throwErrorAt id "invalid bare context identifier"
  -- Dynamic Lean context
  | `(stlcCtx| ~$Γ:term) => do
      let Γ ← elabTermEnsuringType Γ lang.ctxType
      return (Γ, [])
  -- Static context extension
  | `(stlcCtx| $x:stlcVar ↦ $T:stlcTy ; $Γ:stlcCtx) => do
      let (Γ, scope) ← elabCtxCommon lang elabTy Γ
      let T ← elabTy T
      let (x, scope) ← elabStlcBinder lang scope x
      return (← lang.mkExtendCtx Γ x T, scope)
  | _ => throwUnsupportedSyntax


def elabQuoted
    (lang : Language)
    (elabTy : TyElab)
    (elabTm : TmElab)
    (elabCtx : CtxElab)
    (q : TSyntax `stlcQuoted)
    (expectedType? : Option Expr) :
    TermElabM Expr := do

  let elabOne (q : TSyntax `stlcQuoted) : TermElabM Expr := do
    match q with
    | `(stlcQuoted| $T:stlcTy) => elabTy T
    | `(stlcQuoted| $t:stlcTm) => do
        return (← elabTm [] [] t).1
    | `(stlcQuoted| $Γ:stlcCtx) => do
        return (← elabCtx Γ).1
    | `(stlcQuoted| $Γ:stlcCtx ⊢ $t:stlcTm ⦂ $T:stlcTy) => do
        let (Γ, scope) ← elabCtx Γ
        let (t, _) ← elabTm scope [] t
        let T ← elabTy T
        lang.mkHasType Γ t T
    | _ => throwUnsupportedSyntax

  let resultType? (q : Syntax) : Option Expr :=
    if q.isOfKind ``StlcCommon.quotedTy then
      some (mkConst lang.tyType)
    else if q.isOfKind ``StlcCommon.quotedTm then
      some (mkConst lang.tmType)
    else if q.isOfKind ``StlcCommon.quotedCtx then
      some lang.ctxType
    else if q.isOfKind ``StlcCommon.quotedJudge then
      some (mkSort .zero)
    else
      none

  let kindName (stx : Syntax) : String :=
    if stx.isOfKind ``StlcCommon.quotedTy then
      "type"
    else if stx.isOfKind ``StlcCommon.quotedTm then
      "term"
    else if stx.isOfKind ``StlcCommon.quotedCtx then
      "context"
    else if stx.isOfKind ``StlcCommon.quotedJudge then
      "typing judgment"
    else
      "unknown"

  let alternatives :=
    if q.raw.isOfKind choiceKind then
      q.raw.getArgs
    else
      #[q.raw]

  let candidates ←
    match expectedType? with
    | none => pure alternatives
    | some expectedType => do
      let expectedType ← instantiateMVars expectedType
      if expectedType.hasExprMVar then
        pure alternatives
      else
        let mut res := #[]
        for alt in alternatives do
          if let some resultType := resultType? alt then
            if ← isDefEq expectedType resultType then
              res := res.push alt
        if res.isEmpty then
          throwErrorAt q m!"this STLC quotation cannot have the expected Lean type {expectedType}"
        pure res

  let test (alt : Syntax) : TermElabM Bool := do
    let s ← saveState
    try
      let result? ← commitIfNoErrors? <| elabOne ⟨alt⟩
      return result?.isSome
    finally
      s.restore (restoreInfo := true)

  let mut successes := #[]

  for alt in candidates do
    if ← test alt then
      successes := successes.push alt

  match successes with
  | #[alt] =>
      -- Unique interpretation: re-elab it.
      elabOne ⟨alt⟩

  | #[] =>
      -- The expected type selected exactly one category.
      -- rerun to get its language-specific error.
      if let #[alt] := candidates then
        discard <| elabOne ⟨alt⟩

      let kinds := candidates.toList
        |>.map kindName
        |> String.intercalate ", "

      throwErrorAt q m!"\
this STLC quotation has no valid interpretation

Tried: {kinds}

Add a Lean type annotation to select an interpretation and obtain a more specific error."

  | _ =>
      let kinds := successes.toList
        |>.map kindName
        |> String.intercalate ", "

      throwErrorAt q m!"\
ambiguous STLC quotation

This syntax has multiple valid interpretations:
  {kinds}

Add a Lean type annotation to select the intended interpretation."

end Elab

namespace Delab

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer Elab

@[category_parenthesizer stlcTy]
def stlcTy.parenthesizer : CategoryParenthesizer
  | prec => do
      maybeParenthesize `stlcTy true wrapParens prec <|
        parenthesizeCategoryCore `stlcTy prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(stlcTy| ($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

@[category_parenthesizer stlcTm]
def stlcTm.parenthesizer : CategoryParenthesizer
  | prec => do
      maybeParenthesize `stlcTm true wrapParens prec <|
        parenthesizeCategoryCore `stlcTm prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(stlcTm| ($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

def getTy (stx : Term) : TSyntax `stlcTy :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `(<{ $T:stlcTy }>) => return T
    | `((<{ $T:stlcTy }>)) => return T
    | `($id:ident) =>
        match classifyIdent? id with
        | some (.metavar, _) => `(stlcTy| $id:ident)
        | _ => `(stlcTy| ~$stx)
    | _ => `(stlcTy| ~$stx)

def getTm (stx : Term) : TSyntax `stlcTm :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `(<{ $t:stlcTm }>) => return t
    | `((<{ $t:stlcTm }>)) => return t
    | `($id:ident) =>
      match classifyIdent? id with
      | some (.metavar, _) => `(stlcTm| $id:ident)
      | _ => `(stlcTm| ~$stx)
    | _ => `(stlcTm| ~$stx)

def getVar (stx : Term) : TSyntax `stlcVar :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `($s:str) =>
        let id := mkObjectIdentFrom stx s.getString
        match classifyIdent? id with
        | some (.object, _) => `(stlcVar| $id:ident)
        | _ => `(stlcVar| ~$s)
    | _ => `(stlcVar| ~$stx)

/-- Each language provides its `reserved` identifiers (to not be printed as ordinary variables) -/
def unexpandVar (reserved : String → Bool) (varCtor : Name) : Unexpander
  | stx@`($_ $s:str) => do
      let name := s.getString
      let id := mkObjectIdentFrom stx name
      match classifyIdent? id, !reserved name with
      | some (.object, _), true =>
          let t ← `(stlcTm| $id:ident)
          `(<{ $t:stlcTm }>)
      | _, _ => pure <| Unhygienic.run do
          let var : Term := mkIdentFrom stx varCtor
          return (← `($var $s)).raw
  | _ => throw ()

def delabVar (varCtor : Name) : Delab :=
  whenPPOption getPPNotation do
    let e ← getExpr
    guard <| e.isAppOfArity varCtor 1
    match e.appArg! with
    | .lit (.strVal _) => failure
    | _ => do
        let var : Term := mkIdent varCtor
        `($var $(← withAppArg delab))

def unexpandArrow : Unexpander
  | `($_ $A $B) => do
      let T ← `(stlcTy| $(getTy A) → $(getTy B))
      let q ← `(stlcQuoted| $T:stlcTy)
      `(<{ $q:stlcQuoted }>)
  | _ => throw ()

def unexpandApp : Unexpander
  | `($_ $f $a) => do
      let t ← `(stlcTm| $(getTm f) $(getTm a))
      let q ← `(stlcQuoted| $t:stlcTm)
      `(<{ $q:stlcQuoted }>)
  | _ => throw ()

def unexpandAbs : Unexpander
  | `($_ $x $T $t) => `(<{ λ $(getVar x) : $(getTy T) . $(getTm t) }>)
  | _ => throw ()

def unexpandSubst : Unexpander
  | `($_ $x $s $t) => `(<{ [$(getVar x) := $(getTm s)] $(getTm t) }>)
  | _ => throw ()

partial def unexpandCtx :
    Term → UnexpandM (TSyntax `stlcCtx)
  | `(∅) => `(stlcCtx| ∅)
  | `($x:str →ₚ $T) => do unexpandCtx (← `($x →ₚ $T ; ∅))
  | `($x:str →ₚ $T ; $Γ) => do
      let Γ' ← unexpandCtx Γ
      let x' := getVar x
      let T' := getTy T
      `(stlcCtx| $x':stlcVar ↦ $T':stlcTy ; $Γ':stlcCtx)
  | `($Γ:ident) => `(stlcCtx| $Γ:ident)
  | Γ => `(stlcCtx| ~$Γ)

def unexpandHasType : Unexpander
  | `($_ $Γ $t $T) => do
      let Γ' ← unexpandCtx Γ
      let t' := getTm t
      let T' := getTy T
      `(<{ $Γ':stlcCtx ⊢ $t':stlcTm ⦂ $T':stlcTy }>)
  | _ => throw ()

end Delab

end StlcCommon
