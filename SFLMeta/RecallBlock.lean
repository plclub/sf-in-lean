import VersoManual
import SFLMeta.RecallSource
import SFLMeta.RecallCheck

/-!
# Recall as a code block

In a rendered book, a recalled definition should look like any other code
block. The `recall` and `recallSource` code blocks parse their contents as
a plain declaration, wrap it in the corresponding checking command, and
elaborate that in the document's Lean environment. The rendered block shows
only the declaration, so the checking is invisible in the output, and the
source needs no marker beyond the code block's own name. The wrapped node
is built directly, so the commands' scoped syntax never needs to be in
scope in a document.
-/

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean (reportMessages saveOutputs)
open Verso.Genre.Manual.InlineLean.Scopes (getScopes)
open Verso.SyntaxUtils (parseStrLitAsCategory)
open SubVerso.Highlighting

/--
Configuration for the recall code blocks: `+error` expects the check to
fail, `+statement` restates only a theorem statement, and `name` saves the
block's messages for a `leanOutput` block.
-/
structure RecallBlockConfig where
  /-- Whether the check is expected to fail. -/
  error : Bool := false
  /-- Whether the contents restate only a theorem statement. -/
  statement : Bool := false
  /-- A name under which the block's messages are saved for `leanOutput`. -/
  name : Option Name := none

def RecallBlockConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
    [MonadError m] : ArgParse m RecallBlockConfig :=
  RecallBlockConfig.mk <$> .flag `error false <*> .flag `statement false <*>
    .named `name .name true

instance [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] :
    FromArgs RecallBlockConfig m := ⟨RecallBlockConfig.parse⟩

/-- The contents of a statement-mode recall block: a theorem name and its
restated statement. -/
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
Elaborates a code block's contents wrapped in a recall command, in the
document's Lean environment, then renders the block as the plain contents.
The contents are a declaration wrapped by the command of kind `cmdKind`,
or, in statement mode, a theorem name and statement wrapped by the command
of kind `stmtKind`; a block without a statement form passes `none` and
rejects `+statement`. When `highlighted` is `true`, the rendered block
carries the elaboration's highlighting; the byte-for-byte block passes
`false`, since its contents are never elaborated and the only recorded
information is the block-wide reference to the recalled constant, which
would give every token the same hover.
-/
def recallBlock (config : RecallBlockConfig) (str : StrLit)
    (cmdKind : SyntaxNodeKind) (stmtKind : Option SyntaxNodeKind)
    (highlighted : Bool := true) : DocElabM Term := withoutAsync do
  let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)
  let (cmdStx, wrapped) ←
    if config.statement then
      let some stmtKind := stmtKind
        | throwError "this block has no statement form"
      let spec ← parseStrLitAsCategory `recallStmtSpec str
      pure (spec,
        (mkNode stmtKind #[mkAtom "recall", mkAtom "statement", spec[0], mkAtom ":", spec[2]]).raw)
    else
      let cmdStx ← parseStrLitAsCategory `command str
      pure (cmdStx, (mkNode cmdKind #[mkAtom "recall", cmdStx]).raw)
  -- The same adjustments the `lean` code block makes: synchronous
  -- elaboration so info trees are available for highlighting, and public
  -- names so the document sees what it declares.
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
  unless highlighted do
    return ← ``(Verso.Doc.Block.code $(quote str.getString))
  let hls ← highlight cmdStx (st.messages.toArray.filter (!·.isSilent)) st.infoState.trees
  let hls := match col? with
    | none => hls
    | some col => hls.deIndent col
  let range := (Syntax.getRange? str).map (← getFileMap).utf8RangeToLspRange
  ``(Verso.Doc.Block.other
      (Verso.Genre.Manual.InlineLean.Block.lean $(quote hls)
        (some $(quote (← getFileName))) $(quote range))
      #[Verso.Doc.Block.code $(quote str.getString)])

/--
A code block whose contents restate an earlier definition, checked up to
definitional equality by the `recall` command. With `+statement`, the
contents restate only a theorem statement.
-/
@[code_block]
def recall : CodeBlockExpanderOf RecallBlockConfig
  | config, str =>
    recallBlock config str ``RecallCheck.recallChk (some ``RecallCheck.recallChkStmt)

/--
A code block whose contents restate an earlier definition, checked byte for
byte by the `recall_source` command, which compares whole declarations
only. The block renders as plain code: the contents are never elaborated,
so there is no per-token information to show.
-/
@[code_block]
def recallSource : CodeBlockExpanderOf RecallBlockConfig
  | config, str =>
    recallBlock config str ``RecallSource.recallSrc none (highlighted := false)
