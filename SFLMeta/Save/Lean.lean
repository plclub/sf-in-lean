import VersoManual

import SubVerso.Highlighting

import SFLMeta.Variant

import SFLMeta.Save.SourceRewrite

open Verso Doc Elab Genre Manual InlineLean ArgParse
open SubVerso.Highlighting
open Lean Elab
open Verso.Genre.Manual.InlineLean.Scopes (getScopes setScopes)

namespace SFLMeta

namespace Save

/-! ## Student elaboration & highlighting

`elabAndHighlightStudent` runs the student variant of a `lean` block through a
standalone command-parser + elaborator + highlighter pipeline, using a private
`Command.State` so the surrounding environment is *not* mutated. It is the
analogue of the upstream `lean` expander but operating on a raw source string
rather than a string literal at a position in the chapter file.

The starting environment and scopes should be a snapshot taken *before* the
upstream teacher elaboration of the same block, so the student elaboration sees
all prior chapter definitions (e.g. types referenced from the student code)
but does *not* see the teacher-side defs of this same block (which would
collide when the student variant redefines them). -/

namespace LeanElab

/--
  Go through the lines of `hls` and drop the line that is not appear in lines of `src`.

  This is for reusing highlighting results from elbaoration for solution (teacher) variant: removing `-- SOLUTION`/`-- END SOLUTION` and `#guard_msgs` should not
  cause elaboration again.
-/
defmethod Highlighted.filterBySource (hls : Highlighted) (src : String) : Highlighted := Id.run do
  let expected := (src.splitOn "\n").toArray
  let mut nextExpected := 0
  let mut out : Highlighted := .empty
  for line in hls.lines do
    if nextExpected < expected.size then
      let rendered := line.toString
      let rendered := if rendered.endsWith "\n" then rendered.dropEnd 1 |>.toString else rendered
      if rendered == expected[nextExpected]! then
        out := out ++ line
        nextExpected := nextExpected + 1
  return if nextExpected == expected.size then out else .unparsed src


def elabAndHighlightStudent
    (initEnv : Environment) (initScopes : List Command.Scope) (src : String) :
    DocElabM Highlighted := do
  let fileName ← getFileName
  let fileMap := FileMap.ofString src
  let ictx := Parser.mkInputContext src fileName
  let scopes := initScopes.modifyHead fun (sc : Command.Scope) =>
    let opts := Elab.async.set sc.opts false
    let opts := pp.tagAppFns.set opts true
    { sc with opts }
  let cctx : Command.Context :=
    { fileName, fileMap, snap? := none, cancelTk? := none }
  let mut cmdState : Command.State :=
    { env := initEnv
      maxRecDepth := ← MonadRecDepth.getMaxRecDepth
      scopes }
  let mut pstate : Parser.ModuleParserState := {}
  let mut cmds : Array Syntax := #[]
  repeat
    let scope := cmdState.scopes.head!
    let pmctx : Parser.ParserModuleContext :=
      { env := cmdState.env
        options := scope.opts
        currNamespace := scope.currNamespace
        openDecls := scope.openDecls }
    let (cmd, ps', messages) :=
      Parser.parseCommand ictx pmctx pstate cmdState.messages
    cmds := cmds.push cmd
    pstate := ps'
    cmdState := { cmdState with messages }
    -- `elabCommandTopLevel` resets `messages` and `infoState` per command;
    -- snapshot and re-prepend so the highlighter sees the cumulative trees.
    let savedMsgs := cmdState.messages
    let savedTrees := cmdState.infoState.trees
    let runRes ← liftM (m := IO) <| IO.FS.withIsolatedStreams <| EIO.toIO' <|
      ((Command.elabCommandTopLevel cmd).run cctx).run cmdState
    match runRes with
    | (_, .error _) => break
    | (_, .ok ((), cs)) => cmdState := cs
    cmdState := { cmdState with
      messages := savedMsgs ++ cmdState.messages
      infoState :=
        { cmdState.infoState with
          trees := savedTrees ++ cmdState.infoState.trees } }
    if Parser.isTerminalCommand cmd then break
  DocElabM.withFileMap fileMap do
    let nonSilent := cmdState.messages.toArray.filter (!·.isSilent)
    let mut hls : Highlighted := .empty
    let mut lastPos : String.Pos.Raw := 0
    for cmd in cmds do
      hls := hls ++ (← highlightIncludingUnparsed
        cmd nonSilent cmdState.infoState.trees (startPos? := lastPos))
      lastPos := (cmd.getTrailingTailPos?).getD lastPos
    return hls

end LeanElab



/-! ## Block extension that carries pre-computed source variants -/

namespace LeanSaved
/--
  `ExtractionMode` defines three ways that a Lean code block can be emitted.
-/
inductive ExtractionMode where
  | code
  | experiment
  | expectFailure
  deriving ToJson, FromJson, Quote

/--
  A subset of `InlineLean.LeanBlockConfig` flags:
  - `keep` -> `persistent`
  - `error` -> `expectedError`
  - `show` -> `render`

  Only `keep` and `error` are used to derive the extraction policy (`Data.extractionMode`).
-/
structure Config where
  persistent : Bool
  expectedError : Bool
  render : Bool
  name : Option Name
  deriving ToJson, FromJson, Quote

namespace Config

variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

def parse : ArgParse m Config :=
  Config.mk <$>
    .flag `keep true <*>
    .flag `error false <*>
    .flag `show true <*>
    .named `name .name true

instance : FromArgs Config m := ⟨Config.parse⟩

def toInlineLean (config : Config) : InlineLean.LeanBlockConfig :=
  {
    «show» := config.render,
    keep := config.persistent,
    name := config.name,
    error := config.expectedError,
    fresh := false
  }

end Config

/--
  The saved-payload format for `Block.leanSaved`.
-/
structure Data where
  variants : Variants String
  config : Config
  deriving ToJson, FromJson, Quote

/-- Decode a `Block.leanSaved` payload. -/
def decode? (data : Json) : Option Data :=
  match fromJson? data with
  | .ok saved => some saved
  | .error _ => none

/--
  * persistent, non-error blocks become executable Lean;
  * non-persistent blocks (`-keep`) become indented `sf_experiment` blocks;
  * expected-error blocks (`+error`) become indented `sf_expect_failure` blocks
-/
def Data.extractionMode (saved : Data) : ExtractionMode :=
  let {persistent, expectedError, ..} := saved.config
  if expectedError then
    .expectFailure
  else if persistent then
    .code
  else
    .experiment

end LeanSaved


end Save


/-!
`Block.leanSaved` wraps an elaborated `lean` block and records the student,
solutions, and terse source variants computed at elaboration time, together with
the original block's extraction-relevant flags. Its three children are the
solutions-, student-, and terse-rendered forms of the block; traversal keeps the
one selected by the build's typed `Variant`, so the same compiled document serves
all three builds. HTML/TeX rendering passes through to the surviving child; the
saver checks the stored metadata to decide whether to emit the saved source into
extracted `.lean` files as raw code, `sf_experiment`, or `sf_expect_failure`.
-/
open Save in
block_extension Block.leanSaved (saved : Save.LeanSaved.Data) where
  data := toJson saved
  traverse _ data contents := do
    -- Three children = still unselected: keep the solutions, student, or terse
    -- variant selected by the current typed `Variant`.
    -- One child (or anything else) = already selected; nothing to do.
    if h : contents.size = 4 then
      let some saved := LeanSaved.decode? data | return none
      let variant ← getCurrVariant
      let chosen ←
        if variant.isSolution ∨ variant.isGrading then pure contents[0]
        else if variant.isTerse then pure contents[2]
        else pure contents[1]
      return some (.other (Block.leanSaved saved) #[chosen])
    else
      return none -- xhalo32: shouldn't this be `unreachable!`?
  toHtml := some fun _ goB _ data contents => do
    let some saved := Save.LeanSaved.decode? data
      | return .empty
    unless saved.config.render do
      return .empty
    contents.mapM goB
  toTeX := some fun _ goB _ data contents => do
    let some saved := Save.LeanSaved.decode? data
      | return .empty
    unless saved.config.render do
      return .empty
    contents.mapM goB


/-! ## `lean` code-block override

Wraps each ` ```lean … ``` ` code block. The pipeline is:

1. Snapshot the current environment and scopes (the "pre-teacher" state).
2. Delegate to the upstream Lean code-block expander to elaborate the teacher
   form of the source. This typechecks the author's solutions (giving live
   error feedback during the book build) and populates `studentEditRef` /
   `teacherEditRef` with the source ranges of every `solution!(…)` invocation.
3. Convert those absolute source ranges to offsets relative to the block's
   own source string and compute the teacher, student, and terse variants.
4. Run `elabAndHighlightStudent` on the student source (starting from the
   pre-teacher environment, so prior chapter definitions are available but
   this block's teacher-side defs are not), and likewise on the terse source
   when it differs (i.e. when the block contains `workinclass!`).
5. Emit a `Block.leanSaved` with three children: the upstream
   (teacher-rendered) block and `Block.lean`s wrapping the student and terse
   `Highlighted`s. Traversal later keeps one of the three according to the
   build's typed `Variant`, while the saver uses the recorded block config to
   decide whether to wrap extracted output Lean code in `sf_expect_failure` or
   `sf_experiment`.
-/

open Save SourceRewrite LeanElab LeanSaved in
@[code_block]
def lean : CodeBlockExpanderOf LeanSaved.Config
  | config, str => do
    studentEditRef.set #[]
    teacherEditRef.set #[]
    terseEditRef.set #[]
    let preEnv ← getEnv
    let preScopes ← getScopes
    -- Run InlineLean.elabCommands so that we can reuse some highlightings
    -- after edits for different variants
    elabCommands config.toInlineLean str fun _ originalHls str => do
      let studentEdits ← studentEditRef.get
      let teacherEdits ← teacherEditRef.get
      let terseEdits ← terseEditRef.get
      let src := str.getString

      -- `strLitInputContext` parses starting at `str.getPos?`, so the byte
      -- indices recorded by the elaborator are absolute file offsets. The
      -- string-literal contents begin one byte past the opening quote.
      let relativize (edits : Array SolutionEditRaw) : Array Replacement :=
        edits.flatMap (·.edits) |>.map fun r =>
          { r with
            range.start.byteIdx := r.range.start.byteIdx - str.raw.getPos!.byteIdx
            range.stop.byteIdx := r.range.stop.byteIdx - str.raw.getPos!.byteIdx
            }
      let teacherEdited := applyEdits src <| relativize teacherEdits
      let studentEdited := applyEdits src <| relativize studentEdits
      let terseEdited := applyEdits src <| relativize terseEdits

      let teacher := stripGuardMsgs ∘ stripFillInMarkers <| teacherEdited
      let student := stripGuardMsgs ∘ applyFillInForStudent <| studentEdited
      let terse := stripGuardMsgs <| applyFillInForStudent <| terseEdited

      -- Note: this is different from `teacher`.
      -- `teacher` is for extracted projects which includes `teacherEdits`,
      -- while `teacherDisplay` is the string that will be shown in HTML.
      let teacherDisplay := stripGuardMsgs ∘ stripFillInMarkers <| src

      -- Always reuse orignal elaboration for teacher
      let teacherHls :=
        if teacherDisplay == src then originalHls
        else originalHls.filterBySource teacherDisplay

      -- Reuse original elaboration for student if the edits didn't change the source
      let studentHls ←
        if student == src then pure originalHls
        else elabAndHighlightStudent preEnv preScopes student

      -- Reuse student/original elaboration if they still apply
      let terseHls ←
        if terse == student
          then pure studentHls
        else if terse == src
          then pure originalHls
        else
          elabAndHighlightStudent preEnv preScopes terse

      let range := Syntax.getRange? str
      let lspRange := range.map (← getFileMap).utf8RangeToLspRange
      let fileName ← getFileName

      let mkChild (source : String) (hls : Highlighted) : DocElabM Term := do
        -- Serialize highlighted tree with `hlToExport`/`hlFromExport!` to reduce the term size
        let encoded := hlToExport hls
        `(Verso.Doc.Block.other
            (Verso.Genre.Manual.InlineLean.Block.lean
              (hlFromExport! $(quote encoded))
              (some $(quote fileName))
              $(quote lspRange))
            #[Verso.Doc.Block.code $(quote source)])

      let teacherChild ← mkChild teacherDisplay teacherHls
      let studentChild ← mkChild student studentHls
      let terseChild ← mkChild terse terseHls
      let variants := {student, solutions := teacher, terse, grading := teacher : Variants String}
      let saved := { variants, config : Data }
      ``(Verso.Doc.Block.other
          (SFLMeta.Block.leanSaved $(quote saved))
          #[$teacherChild, $studentChild, $terseChild])


open Verso.Genre.Manual.InlineLean in

@[role SFLMeta.lean]
meta def leanInline : RoleExpanderOf LeanInlineConfig :=
  Verso.Genre.Manual.InlineLean.leanInline


end SFLMeta
