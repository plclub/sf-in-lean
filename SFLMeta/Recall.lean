import VersoManual

import SFLCompat.Recall.Check
import SFLCompat.Recall.Source

import SubVerso.Highlighting

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean (reportMessages saveOutputs)
open Verso.Genre.Manual.InlineLean.Scopes (getScopes)
open Verso.SyntaxUtils (parseStrLitAsCategory)
open SubVerso.Highlighting

namespace SFLMeta

namespace Recall

inductive Kind where
  | semantic
  | source
  deriving BEq, ToJson, FromJson, Quote

structure Data where
  kind : Kind
  statement : Bool
  expectedError : Bool
  strictUniverse : Bool
  source : String
  outputName : Option Name
  deriving ToJson, FromJson, Quote

def decode? (data : Json) : Option Data :=
  match fromJson? data with
  | .ok recall => some recall
  | .error _ => none

end Recall

block_extension Block.recall (saved : Recall.Data) where
  data := toJson saved
  traverse _ _ _ := pure none
  toHtml := some fun _ goB _ _ contents => contents.mapM goB
  toTeX := some fun _ goB _ _ contents => contents.mapM goB

/--
Configuration shared by `recall` and `recallSource`: `+error` expects the
check to fail, `+statement` restates only a theorem statement,
`+strictUniverse` requires exact universe parameters for recall,
and `name` saves the block's messages for `leanOutput`.
-/
structure RecallBlockConfig where
  error : Bool := false
  statement : Bool := false
  strictUniverse : Bool := false
  name : Option Name := none

def RecallBlockConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
    [MonadError m] : ArgParse m RecallBlockConfig :=
  RecallBlockConfig.mk <$> .flag `error false <*> .flag `statement false <*>
    .flag `strictUniverse false <*> .named `name .name true

instance [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] :
    FromArgs RecallBlockConfig m := ⟨RecallBlockConfig.parse⟩

/-- The contents of a statement-mode recall block. -/
declare_syntax_cat recallStmtSpec

syntax ident " : " term : recallStmtSpec

/--
Sets `linter.unusedVariables` to `false` in the recorded info trees, so the
document's own linter pass does not re-report warnings the inner
elaboration already handled.
-/
private partial def disableUnusedVarLinter : InfoTree → InfoTree
  | .context (.commandCtx ci) child =>
    .context (.commandCtx { ci with options := Linter.linter.unusedVariables.set ci.options false })
      (disableUnusedVarLinter child)
  | .context pci child => .context pci (disableUnusedVarLinter child)
  | .node info children => .node info (children.map disableUnusedVarLinter)
  | .hole id => .hole id

/--
Elaborate a recall block synchronously in the document environment, render its
plain contents, and preserve explicit recall metadata for later extraction.
-/
def recallBlock (config : RecallBlockConfig) (str : StrLit) (kind : Recall.Kind)
    (cmdKind : SyntaxNodeKind) (highlighted : Bool := true) :
    DocElabM Term := withoutAsync do
  if config.strictUniverse then
    if kind != .semantic then
      throwError "`+strictUniverse` is supported only by `recall`"
    if config.statement then
      throwError "`+strictUniverse` cannot be combined with `+statement`"
  if config.statement && kind == .source then
    throwError "`+statement` is supported only by semantic `recall`"
  let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)
  let (cmdStx, wrapped) ←
    if config.«statement» then
      let spec ← parseStrLitAsCategory `recallStmtSpec str
      pure (spec,
        (mkNode ``SFLCompat.Recall.Check.recallChkStmt
          #[mkAtom "sf_recall", mkAtom "statement", spec[0], mkAtom ":", spec[2]]).raw)
    else
      let cmdStx ← parseStrLitAsCategory `command str
      let cmdKind :=
        if config.strictUniverse then ``SFLCompat.Recall.Check.recallChkStrict else cmdKind
      let strictArgs :=
        if config.strictUniverse then #[mkAtom "+", mkAtom "strictUniverse"] else #[]
      pure (cmdStx, (mkNode cmdKind
        (#[mkAtom (if kind == .semantic then "sf_recall" else "sf_recall_source")] ++ strictArgs ++ #[cmdStx])).raw)
  let scopes := (← getScopes).modifyHead fun sc =>
    { sc with opts := pp.tagAppFns.set (Elab.async.set sc.opts false) true, isPublic := true }
  let cctx : Command.Context :=
    { fileName := ← getFileName, fileMap := ← getFileMap, snap? := none, cancelTk? := none }
  let st : Command.State :=
    { env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes }
  let st ←
    match ← liftM <| EIO.toIO' <| ((Command.elabCommandTopLevel wrapped).run cctx).run st with
    | .error e => logError e.toMessageData; pure st
    | .ok ((), st) => pure st
  for t in st.infoState.trees do
    pushInfoTree (disableUnusedVarLinter t)
  if let some name := config.name then
    let outMsgs ← st.messages.toList.filter (!·.isSilent) |>.mapM fun msg => do
      let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
      let msg ← highlightMessage msg
      pure { msg with contents := .append #[.text head, msg.contents] }
    saveOutputs name outMsgs
  reportMessages (if config.error then some true else none) str st.messages
  let saved : Recall.Data := {
      kind
      statement := config.statement
      expectedError := config.error
      strictUniverse := config.strictUniverse
      source := str.getString
      outputName := config.name
    }
  if !highlighted then
    return ← ``(Verso.Doc.Block.other (SFLMeta.Block.recall $(quote saved))
      #[Verso.Doc.Block.code $(quote str.getString)])
  let hls ← highlight cmdStx (st.messages.toArray.filter (!·.isSilent)) st.infoState.trees
  let hls := match col? with
    | none => hls
    | some col => hls.deIndent col
  let range := (Syntax.getRange? str).map (← getFileMap).utf8RangeToLspRange
  let child ← ``(Verso.Doc.Block.other
    (Verso.Genre.Manual.InlineLean.Block.lean $(quote hls)
      (some $(quote (← getFileName))) $(quote range))
    #[Verso.Doc.Block.code $(quote str.getString)])
  ``(Verso.Doc.Block.other (SFLMeta.Block.recall $(quote saved)) #[$child])

/--
A `recall` code block checks a declaration up to definitional equality. With
`+statement`, it checks only a theorem statement.
-/
@[code_block]
def recall : CodeBlockExpanderOf RecallBlockConfig
  | config, str =>
    recallBlock config str .semantic ``SFLCompat.Recall.Check.recallChk

/--
A `recallSource` code block checks a whole declaration byte for byte. Its
contents are not elaborated, so it renders without per-token highlighting.
-/
@[code_block]
def recallSource : CodeBlockExpanderOf RecallBlockConfig
  | config, str =>
    recallBlock config str .source ``SFLCompat.Recall.Source.recallSrc (highlighted := false)

end SFLMeta
