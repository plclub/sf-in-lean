import VersoManual
import SFLMeta.Bnf
import SFLMeta.Ignore
import SFLMeta.Exercise
import SFLMeta.Terse
import SFLMeta.SlideBreak
import SFLMeta.Details
import Std.Data.HashMap
import SubVerso.Highlighting

open Lean Elab
open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Std (HashMap)
open SubVerso.Highlighting
open Verso.Genre.Manual.InlineLean.Scopes (getScopes setScopes)
open Verso (BuildLogT reportError)

namespace SFLMeta

/--
When `true`, `lean` code blocks render with the teacher (solution-filled)
source in the HTML and TeX output. When `false` (the default), the rendered
output shows the student form: each `solution!(…)` is replaced by `sorry` and
each `-- SOLUTION … -- END SOLUTION` region is collapsed to `-- FILL IN HERE`.

Both variants are elaborated and highlighted when the chapter is compiled (so
author errors in solutions are always reported); this flag merely selects
which variant survives traversal.  Each `Main*.lean` executable sets it before
calling `manualMain`, which is what makes the student and solutions builds two
runs of the same compiled document rather than two compilations. -/
initialize Save.showSolutions : IO.Ref Bool ← IO.mkRef false

/-! ## Block extensions used by the saver -/

/-!
`Block.diagramWithAlt` wraps a diagram and an ASCII-text fallback. The HTML
and TeX renderings emit only the diagram child; the saver emits only the
text-fallback child wrapped in a `/-! … -/` module-doc comment. -/

block_extension Block.diagramWithAlt where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ _ contents => do
      contents.foldlM (init := (.empty : Verso.Output.Html)) fun acc b => do
        match b with
        | .code _ => pure acc
        | _ => return acc ++ (← goB b)
  toTeX :=
    open Verso.Output.TeX in
    some fun _ goB _ _ contents => do
      contents.foldlM (init := (.empty : Verso.Output.TeX)) fun acc b => do
        match b with
        | .code _ => pure acc
        | _ => return acc ++ (← goB b)

/-! ## `:::diagramWithAlt` directive -/

/--
A `:::diagramWithAlt` directive wraps a diagram code block and an ASCII text
fallback. The HTML book renders only the diagram; the saver emits only the
text fallback. Use it to attach an ASCII alt that ends up in the generated
`.lean` files in place of the SVG. -/
@[directive]
def diagramWithAlt : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other SFLMeta.Block.diagramWithAlt #[$blocks,*])

/-! ## Inline-to-text pretty printer -/

namespace Save

namespace Text

/--
Render a piece of Verso inline content to a plain-text fragment suitable for
inclusion in a `/-! … -/` Lean module-doc comment. Markdown-like delimiters
(`*…*` for emphasis, `**…**` for bold, backticks for code, `[text](url)` for
links) are preserved so the resulting comment still reads naturally. -/
partial def inlineToText : Verso.Doc.Inline Manual → String
  | .text s => s
  | .linebreak _ => "\n"
  | .emph content => "*" ++ String.join (content.toList.map inlineToText) ++ "*"
  | .bold content => "**" ++ String.join (content.toList.map inlineToText) ++ "**"
  | .code s => "`" ++ s ++ "`"
  | .math _ s => "$" ++ s ++ "$"
  | .link content url =>
    "[" ++ String.join (content.toList.map inlineToText) ++ "](" ++ url ++ ")"
  | .footnote name _ => s!"[^{name}]"
  | .image alt url => s!"![{alt}]({url})"
  | .concat content => String.join (content.toList.map inlineToText)
  | .other _ content => String.join (content.toList.map inlineToText)

/-- Pretty-print an array of inlines to plain text. -/
def inlinesToText (inls : Array (Verso.Doc.Inline Manual)) : String :=
  String.join (inls.toList.map inlineToText)

/-- Right margin used when filling prose paragraphs in the terse build's
generated `.lean` files. -/
def terseFillWidth : Nat := 60

/-- Right margin used when filling prose paragraphs in the student and
solutions builds' generated `.lean` files. -/
def proseFillWidth : Nat := 75

/-- The prose fill width for a build variant (`"terse"`, `"student"`, or
`"solutions"`). -/
def fillWidthFor (variant : String) : Nat :=
  if variant == "terse" then terseFillWidth else proseFillWidth

/--
Split `s` into whitespace-separated words, keeping each `` `code span` `` intact
as a single token even when it contains spaces (so wrapping never splits one
across a line break). -/
private def tokenizeKeepingCodeSpans (s : String) : Array String := Id.run do
  let mut words : Array String := #[]
  let mut cur : String := ""
  let mut inCode := false
  for c in s.toList do
    if inCode then
      cur := cur.push c
      if c == '`' then inCode := false
    else if c == '`' then
      cur := cur.push c
      inCode := true
    else if c == ' ' || c == '\n' || c == '\t' then
      if !cur.isEmpty then
        words := words.push cur
        cur := ""
    else
      cur := cur.push c
  if !cur.isEmpty then words := words.push cur
  return words

/--
Fill (word-wrap) `text` to at most `width` columns. The source's soft-wrap
newlines and continuation-line indentation are discarded and the words are
reflowed; a `` `code span` `` is never split across lines, and a single word
longer than `width` is left to overflow rather than being broken. -/
def fillText (width : Nat) (text : String) : String := Id.run do
  let mut lines : Array String := #[]
  let mut cur : String := ""
  for w in tokenizeKeepingCodeSpans text do
    if cur.isEmpty then
      cur := w
    else if cur.length + 1 + w.length ≤ width then
      cur := cur ++ " " ++ w
    else
      lines := lines.push cur
      cur := w
  if !cur.isEmpty then lines := lines.push cur
  return String.intercalate "\n" lines.toList

/-- Pretty-print a paragraph's inlines, reflowing them to `width` columns. -/
def paraToText (width : Nat) (inls : Array (Verso.Doc.Inline Manual)) : String :=
  fillText width (inlinesToText inls)

/--
Render a Verso block to a Markdown-like string for inclusion in a `/-! … -/`
comment, filling prose to `width` columns.  List items are prefixed with `- ` /
`N. `; continuation lines are indented to align under the item text. -/
private partial def blockToText (width : Nat) : Verso.Doc.Block Manual → String
  | .para inlines => paraToText width inlines
  | .code s => "`" ++ s.trimAscii.toString ++ "`"
  | .concat bs | .blockquote bs =>
    String.intercalate "\n\n" (bs.toList.map (blockToText width))
  | .ul lis =>
    let items := lis.toList.map fun li =>
      let body := String.intercalate "\n\n" (li.contents.toList.map (blockToText width))
      "- " ++ body.replace "\n" "\n  "
    -- Blank lines between items only when some item is itself multi-line.
    let sep := if items.any (·.contains '\n') then "\n\n" else "\n"
    String.intercalate sep items
  | .ol start lis =>
    let items := lis.toList.mapIdx fun i li =>
      let pfx := s!"{start + i}. "
      let indent := String.ofList (List.replicate pfx.length ' ')
      let body := String.intercalate "\n\n" (li.contents.toList.map (blockToText width))
      pfx ++ body.replace "\n" s!"\n{indent}"
    let sep := if items.any (·.contains '\n') then "\n\n" else "\n"
    String.intercalate sep items
  | .dl dis =>
    String.intercalate "\n" (dis.toList.map fun di =>
      inlinesToText di.term ++ "\n:   " ++
      String.intercalate "\n    " (di.desc.toList.map (blockToText width)))
  | .other _ bs => String.intercalate "\n\n" (bs.toList.map (blockToText width))

end Text

/-! ## Lake project scaffold templates -/

/-- Contents of the generated project's `lakefile.toml`. -/
private def lakefileTemplate (vol : String) : String :=
  "name = \"" ++ vol.toLower ++ "-extracted\"\n" ++
  "version = \"0.1.0\"\n" ++
  "defaultTargets = [\"" ++ vol ++ "\"]\n\n" ++
  "[[lean_lib]]\n" ++
  "name = \"" ++ vol ++ "\"\n"

/-! ## Support module template
  Create `SFLCompat.lean` with custom commands used in generated projects.
-/

private def supportModuleName (vol : String) : String :=
  vol ++ ".SFLCompat"

private def supportModulePath (vol : String) : String :=
  vol ++ "/SFLCompat.lean"

private def readSFLCompat : IO String := IO.FS.readFile "SFLMeta/SFLCompat.lean"

/-! ## ExtraStep walker -/

/-- Per-file buffers accumulated by the saver:
`(teacher source, student source, terse source)`. -/
private abbrev SaveBuffers := HashMap String (String × String × String)

private def appendBoth (buf : SaveBuffers) (file : String) (s : String) : SaveBuffers :=
  let (t, st, tr) := buf.getD file ("", "", "")
  buf.insert file (t ++ s, st ++ s, tr ++ s)

private def appendVariants
    (buf : SaveBuffers) (file : String) (teacher student terse : String) : SaveBuffers :=
  let (t, st, tr) := buf.getD file ("", "", "")
  buf.insert file (t ++ teacher, st ++ student, tr ++ terse)

/-- Render a string as a block of `--` line comments, one per line (blank lines
stay completely blank), normalising trailing whitespace. -/
private def asModuleDoc (s : String) : String :=
  let t := s.trimAscii.toString
  let commented := String.intercalate "\n"
    ((t.splitOn "\n").map fun line =>
      if line.all (·.isWhitespace) then "" else "-- " ++ line)
  commented ++ "\n\n"

/-- Merge adjacent `/-! … -/` blocks into one, separating their contents with a blank line. -/
private def mergeAdjacentModuleDocs (s : String) : String :=
  s.replace "\n-/\n\n/-!\n" "\n\n"

/-- Decode a `Block.bnf` payload and return its original source string. -/
private def decodeBnfSource? (data : Json) : Option String :=
  match data with
  | .arr #[_, .str src] => some src
  | _ => none

/-- Decode a `Block.exercise` payload `(rating, name)`. -/
private def decodeExercise? (data : Json) : Option (Nat × String) :=
  match data with
  | .arr #[.num r, .str n] => some (r.toFloat.toUInt32.toNat, n)
  | _ => none

private def wrap (startText endText body : String) : String :=
  let body := body.trimAscii.toString.splitOn "\n" |>.map ("  " ++ ·) |> String.intercalate "\n"
  startText ++ "\n\n" ++ body ++ "\n\n" ++ endText ++ "\n\n"

/-! ## Block extension that carries pre-computed teacher and student source -/

namespace LeanSaved
/--
  `ExtractionMode` defines three ways that a Lean code block can be emitted.
-/
private inductive ExtractionMode where
  | code
  | experiment
  | expectFailure
  deriving ToJson, FromJson, Quote

/--
  A subset of `InlineLean.LeanBlockConfig` flags:
  - `keep` -> `persistent`
  - `error` -> `expectedError`

  Note: `show` is dropped, because it's for rendered book visibility
  and shouldn't affect generated projects.

  They are used to derive the extraction policy (`Data.extractionMode`).
-/
structure Config where
  persistent : Bool
  expectedError : Bool
  deriving ToJson, FromJson, Quote

def Config.fromInlineLean (config : InlineLean.LeanBlockConfig) :=
  Config.mk config.keep config.error

/--
  The saved-payload format for `Block.leanSaved`.
-/
structure Data where
  teacher : String
  student : String
  terse : String
  config : Config
  deriving ToJson, FromJson, Quote

/-- Decode a `Block.leanSaved` payload. -/
def decode? (data : Json) : Option Data :=
  match fromJson? data with
  | .ok saved => some saved
  | .error _ => none

/--
  * persistent, non-error blocks become executable Lean;
  * non-persistent blocks (`-keep`) become `sf_experiment ... end`;
  * expected-error blocks (`+error`) become `sf_expect_failure ... end`
-/
private def Data.extractionMode (saved : Data) : ExtractionMode :=
  let {persistent, expectedError} := saved.config
  if expectedError then
    .expectFailure
  else if persistent then
    .code
  else
    .experiment

end LeanSaved

end Save

/-!
`Block.leanSaved` wraps an elaborated `lean` block and records the teacher,
student, and terse source variants computed at elaboration time, together with
the original block's extraction-relevant flags. Its three children are the
teacher-, student-, and terse-rendered forms of the block; traversal keeps the
one selected by the `Save.showSolutions` flag / draft (terse) mode, so the same
compiled document serves all three builds. HTML/TeX rendering passes through to
the surviving child; the saver checks the stored metadata to decide whether to
emit the saved source into extracted `.lean` files as raw code, `sf_experiment`,
or `sf_expect_failure`.
-/
open Save in
block_extension Block.leanSaved (saved : Save.LeanSaved.Data) where
  data := toJson saved
  traverse _ data contents := do
    -- Three children = still unselected: keep the teacher, student, or terse
    -- variant (the terse build is the draft build, cf. `Block.terse`).
    -- One child (or anything else) = already selected; nothing to do.
    if h : contents.size = 3 then
      let some saved := LeanSaved.decode? data | return none
      let chosen ←
        if ← showSolutions.get then pure contents[0]
        else if ← isDraft then pure contents[2]
        else pure contents[1]
      return some (.other (Block.leanSaved saved) #[chosen])
    else
      return none
  toHtml := some fun _ goB _ _ contents => contents.mapM goB
  toTeX  := some fun _ goB _ _ contents => contents.mapM goB

namespace Save

/-! ## Syntactic rewriting of `solution!` markers

The `solution!` term and tactic elaborators (declared in `SFLMeta.Exercise`)
register the source range of each invocation into `solutionEditsRef` as they
run. The project-local `lean` code-block expander (below) snapshots that ref
around its call to the upstream Lean elaborator, then uses the freshly added
ranges to compute three variants of the block's source: a teacher form (just
the `solution!` keyword removed, parenthesised body kept), a student form (the
whole `solution!(…)` invocation replaced by `sorry`), and a terse form (also
stubbing `workinclass!`). The variants, together with the block's
extraction-relevant flags, are stored in a `Block.leanSaved` wrapper.
Extraction does not re-parse Lean source; it reads this saved payload and emits
raw code, `sf_experiment`, or `sf_expect_failure` according to the saved flags.
-/

namespace SourceRewrite

/-- Apply a set of byte-range replacements right-to-left so earlier edits
don't shift later positions. Works at the byte level via `ByteArray`. -/
private def applyEdits (src : String) (edits : Array Replacement) : String := Id.run do
  let sorted := edits.qsort fun a b => a.range.start.byteIdx > b.range.start.byteIdx
  let mut src := src
  for ⟨{ start, stop }, replacement⟩ in sorted do
    if h : start.IsValid src ∧ stop.IsValid src then
      -- Splice positionally: replace the byte range [start, stop) in place.
      -- (`String.replace` would substitute the first *matching substring*, which
      -- corrupts a block holding several identical edits, e.g. repeated
      -- `solution!(by rfl)`.)  Right-to-left order keeps earlier positions valid.
      let pre := src.slice! ⟨0, String.Pos.Raw.isValid_zero⟩ ⟨start, h.1⟩
      let post := src.slice! ⟨stop, h.2⟩ ⟨src.rawEndPos, String.Pos.Raw.isValid_rawEndPos⟩
      src := pre.toString ++ replacement ++ post.toString
  return src

/-! ## Textual `-- SOLUTION … -- END SOLUTION` rewriting

A complementary mechanism to `solution!(…)` for places where the missing piece
isn't a term or tactic but, for example, the constructors of an inductive
declaration. The source uses `-- SOLUTION` and `-- END SOLUTION` line comments
to delimit the region; in the student build the whole region (including the
marker lines) is replaced with a single `-- FILL IN HERE` comment at the
indentation of the opening marker. In the teacher build the marker lines are
simply removed and the body is kept verbatim. If `-- END SOLUTION` is missing,
the rewrite extends to the end of the block. -/

/-- Trimmed equality test: `line` is the start marker (`-- SOLUTION`). -/
private def isSolutionStart (line : String) : Bool :=
  line.trimAscii.toString == "-- SOLUTION"

/-- Trimmed equality test: `line` is the end marker (`-- END SOLUTION`). -/
private def isSolutionEnd (line : String) : Bool :=
  line.trimAscii.toString == "-- END SOLUTION"

/-- The leading-whitespace prefix of `line` (its indentation). -/
private def lineIndent (line : String) : String :=
  (line.takeWhile (·.isWhitespace)).toString

/-- Replace each `-- SOLUTION … -- END SOLUTION` block in `src` with a single
`-- FILL IN HERE` line at the indentation of the opening marker. -/
partial def applyFillInForStudent (src : String) : String := Id.run do
  let lines := src.splitOn "\n"
  let mut out : Array String := #[]
  let mut i := 0
  let n := lines.length
  while i < n do
    let line := lines[i]!
    if isSolutionStart line then
      out := out.push (lineIndent line ++ "-- FILL IN HERE")
      i := i + 1
      while i < n && !isSolutionEnd lines[i]! do
        i := i + 1
      if i < n then i := i + 1  -- skip the matching `-- END SOLUTION` line
    else
      out := out.push line
      i := i + 1
  return String.intercalate "\n" out.toList

/-- Drop lines that are just `-- SOLUTION` or `-- END SOLUTION` markers, keeping
the body in place. Used to clean up the teacher variant. -/
def stripFillInMarkers (src : String) : String :=
  let lines := src.splitOn "\n"
  let kept := lines.filter fun line => !isSolutionStart line && !isSolutionEnd line
  String.intercalate "\n" kept

/-! ## `#guard_msgs` stripping

`#guard_msgs(…) in <cmd>` modifiers (with their preceding `/-- … -/` expected-
message docstring) verify Lean's output to catch bitrot. They run during the
Verso build — this only removes them from the *rendered* (`.html`) and
*extracted* (`.lean`) forms, leaving the wrapped command in place. -/

/-- Remove `#guard_msgs … in` command-modifier lines and the `/-- … -/`
expected-message docstring immediately preceding them. -/
partial def stripGuardMsgs (src : String) : String := Id.run do
  let lines := (src.splitOn "\n").toArray
  let n := lines.size
  let mut out : Array String := #[]
  let mut i := 0
  while i < n do
    let line := lines[i]!
    let t := line.trimAscii.toString
    if t.startsWith "/--" then
      -- A docstring: scan to the line that closes it (`… -/`).
      let mut j := i
      while j < n && !(lines[j]!.trimAscii.toString.endsWith "-/") do
        j := j + 1
      if j + 1 < n && (lines[j + 1]!.trimAscii.toString.startsWith "#guard_msgs") then
        -- Expected-message docstring for a `#guard_msgs`: drop it and the modifier.
        i := j + 2
      else
        for k in [i:j+1] do out := out.push lines[k]!
        i := j + 1
    else if t.startsWith "#guard_msgs" then
      i := i + 1   -- a `#guard_msgs … in` with no docstring: drop the modifier line
    else
      out := out.push line
      i := i + 1
  return String.intercalate "\n" out.toList

end SourceRewrite

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

end Save

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
   `showSolutions` flag and draft (terse) mode, while the saver uses the
   recorded block config to decide whether to wrap extracted output Lean code
   in `sf_expect_failure` or `sf_experiment`.
-/

open Save SourceRewrite LeanElab LeanSaved in
@[code_block]
def lean : CodeBlockExpanderOf Verso.Genre.Manual.InlineLean.LeanBlockConfig
  | config, str => do
    SFLMeta.studentEditRef.set #[]
    SFLMeta.teacherEditRef.set #[]
    SFLMeta.terseEditRef.set #[]
    let preEnv ← getEnv
    let preScopes ← getScopes
    let underlying ← Verso.Genre.Manual.InlineLean.lean config str
    let student ← studentEditRef.get
    let teacher ← teacherEditRef.get
    let terse ← terseEditRef.get
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
    let teacherRanges := relativize teacher
    let studentRanges := relativize student
    let terseRanges := relativize terse
    let teacherRaw := stripFillInMarkers (applyEdits src teacherRanges)
    let studentRaw := applyFillInForStudent (applyEdits src studentRanges)
    let terseRaw := applyFillInForStudent (applyEdits src terseRanges)
    -- Strip `#guard_msgs` wrappers from the rendered/extracted forms.  They
    -- still ran during the upstream elaboration above (verification intact).
    let teacher := stripGuardMsgs teacherRaw
    let student := stripGuardMsgs studentRaw
    let terse := stripGuardMsgs terseRaw
    let studentHls ← elabAndHighlightStudent preEnv preScopes student
    let range := Syntax.getRange? str
    let lspRange := range.map (← getFileMap).utf8RangeToLspRange
    let saved := {
      teacher, student, terse, config := Config.fromInlineLean config : Data
    }
    -- The upstream `underlying` block highlights the original source, which
    -- still shows the `#guard_msgs` wrapper.  When stripping changed the teacher
    -- form, re-highlight the stripped form for the teacher-side HTML instead.
    let teacherChild ← do
      if teacher != teacherRaw then
        let teacherHls ← elabAndHighlightStudent preEnv preScopes teacher
        `(Verso.Doc.Block.other
            (Verso.Genre.Manual.InlineLean.Block.lean
              $(quote teacherHls)
              (some $(quote (← getFileName)))
              $(quote lspRange))
            #[Verso.Doc.Block.code $(quote teacher)])
      else
        pure underlying
    -- The terse variant usually coincides with the student one (no
    -- `workinclass!` in the block); reuse the student highlighting then.
    let terseHls ←
      if terse == student then pure studentHls
      else elabAndHighlightStudent preEnv preScopes terse
    ``(Verso.Doc.Block.other
        (SFLMeta.Block.leanSaved $(quote saved))
        #[$teacherChild,
          Verso.Doc.Block.other
            (Verso.Genre.Manual.InlineLean.Block.lean
              $(quote studentHls)
              (some $(quote (← getFileName)))
              $(quote lspRange))
            #[Verso.Doc.Block.code $(quote student)],
          Verso.Doc.Block.other
            (Verso.Genre.Manual.InlineLean.Block.lean
              $(quote terseHls)
              (some $(quote (← getFileName)))
              $(quote lspRange))
            #[Verso.Doc.Block.code $(quote terse)]])

namespace Save

/-- Find the ASCII alt text inside a `diagramWithAlt`: the first plain code block. -/
private def findAlt? (contents : Array (Verso.Doc.Block Manual)) : Option String :=
  contents.findSome? fun
    | .code s => some s
    | _ => none

open Text in
mutual

/--
Walk a list of blocks, batching consecutive `.para`, `.ul`, and `.ol` blocks
into a single `/-! … -/` comment instead of emitting one per block, so a list
stays in the same comment as its lead-in paragraph. -/
partial def walkBlocks (width : Nat) (file : String) (bs : Array (Verso.Doc.Block Manual))
    (buf : SaveBuffers) : SaveBuffers := Id.run do
  let mut buf := buf
  let mut pending : Array String := #[]
  for b in bs do
    match b with
    | .para inls => pending := pending.push (paraToText width inls)
    | .ul _ | .ol _ _ => pending := pending.push (blockToText width b)
    | _ =>
      if !pending.isEmpty then
        buf := appendBoth buf file (asModuleDoc (String.intercalate "\n\n" pending.toList))
        pending := #[]
      buf := walkBlock width file b buf
  if !pending.isEmpty then
    buf := appendBoth buf file (asModuleDoc (String.intercalate "\n\n" pending.toList))
  return buf

/--
Walk a single block, accumulating teacher and student content into `buf` for
`file`. The bulk of the saver's logic lives here. -/
partial def walkBlock (width : Nat) (file : String) (b : Verso.Doc.Block Manual)
    (buf : SaveBuffers) : SaveBuffers := Id.run do
  match b with
  | .other which contents =>
    let name := which.name
    if name == ``Block.ignore then
      return buf
    if name == ``Verso.Genre.Manual.Block.diagram then
      return buf
    if name == ``SFLMeta.Block.leanSaved then
      -- The wrapper carries pre-computed teacher/student/terse source plus the
      -- extraction-relevant `lean` block flags. Verso still checks and renders
      -- the block normally; the generated project gets code, `sf_experiment`,
      -- or `sf_expect_failure` according to `LeanSaved.Data.extractionMode`.
      if let some saved := LeanSaved.decode? which.data then
        match saved.extractionMode with
        | .code =>
          return appendVariants buf file
            (saved.teacher.trimAscii.toString ++ "\n\n")
            (saved.student.trimAscii.toString ++ "\n\n")
            (saved.terse.trimAscii.toString ++ "\n\n")
        | .experiment =>
          return appendVariants buf file
            (wrap "sf_experiment" "end" saved.teacher)
            (wrap "sf_experiment" "end" saved.student)
            (wrap "sf_experiment" "end" saved.terse)
        | .expectFailure =>
          return appendVariants buf file
            (wrap "sf_expect_failure" "end" saved.teacher)
            (wrap "sf_expect_failure" "end" saved.student)
            (wrap "sf_expect_failure" "end" saved.terse)
      return buf
    if name == ``Block.exercise then
      -- Emit a `### Exercise (N⭐): name` heading; the contained `lean`
      -- blocks render normally via recursion below.
      if let some (rating, exName) := decodeExercise? which.data then
        let stars := String.ofList (List.replicate rating '⭐')
        let header := s!"### Exercise ({rating} star{if rating == 1 then "" else "s"}): {exName} {stars}"
        let mut buf := appendBoth buf file (asModuleDoc header)
        buf := walkBlocks width file contents buf
        return buf
      return buf
    if name == ``Block.bnf then
      if let some src := decodeBnfSource? which.data then
        return appendBoth buf file (asModuleDoc src.trimAscii.toString)
    if name == ``Block.diagramWithAlt then
      match findAlt? contents with
      | some alt => return appendBoth buf file (asModuleDoc alt.trimAscii.toString)
      | none => return buf
    if name == ``Block.details then
      -- Saved file gets the contents inlined verbatim; the summary becomes a
      -- short comment so the reader of the `.lean` knows it was originally
      -- collapsed in the book.
      let summary :=
        match which.data with
        | .str s => s
        | _ => ""
      let mut buf := appendBoth buf file (asModuleDoc s!"_Details:_ {summary}")
      buf := walkBlocks width file contents buf
      return buf
    if name == ``Block.terse then
      -- Terse content kept in the tree only in terse builds (full builds replace
      -- with concat #[] during traverse). Recurse into children.
      return walkBlocks width file contents buf
    if name == ``Block.full then
      -- Full content kept in the tree only in full builds. Recurse into children.
      return walkBlocks width file contents buf
    if name == ``Block.slidebreak then
      -- Slide-break marker: emit nothing in all generated .lean files.
      return buf
    -- Unknown extension block: recurse into children as a best-effort.
    -- NB: :::dev / :::instructor blocks carry no children (their bodies are
    -- dropped at elaboration), so this recursion is a no-op for them.
    walkBlocks width file contents buf
  | .para inls => return appendBoth buf file (asModuleDoc (paraToText width inls))
  | .code s => return appendBoth buf file (asModuleDoc s.trimAscii.toString)
  | .concat bs | .blockquote bs => walkBlocks width file bs buf
  | .ul _ | .ol _ _ =>
    -- Normally batched with adjacent paragraphs in `walkBlocks`; this case is
    -- only reached for a list arriving outside that batching.
    return appendBoth buf file (asModuleDoc (blockToText width b))
  | .dl dis =>
    let mut buf := buf
    for di in dis do
      buf := walkBlocks width file di.desc buf
    return buf

end

/--
Determine the file-name base for a chapter Part. Uses the `file := …` HTML
metadata if the chapter author set it; otherwise falls back to the sluggified
title (matching what Verso uses for the HTML output filename). -/
private def chapterFileBase (p : Part Manual) : String :=
  let .mk _ titleStr meta? _ _ := p
  (meta?.bind (·.file)).getD titleStr.sluggify.toString

/-- Generated Lean file path for a chapter Part. -/
private def chapterPath (vol : String) (p : Part Manual) : String :=
  vol ++ "/" ++ chapterFileBase p ++ ".lean"

/-- Generated Lean module name for a chapter Part. Uses the raw `file :=`
identifier when it is a plain alphanumeric/underscore name; falls back to
French-quote brackets for slugs that contain hyphens or other punctuation. -/
private def chapterModule (vol : String) (p : Part Manual) : String :=
  let base := chapterFileBase p
  if base.all (fun c => c.isAlphanum || c == '_') then vol ++ "." ++ base
  else vol ++ ".«" ++ base ++ "»"

/--
Walk a section (a Part at depth ≥ 1, inside a chapter). The section's title is
emitted as a `#`-prefixed module-doc heading whose level equals `depth`; all
content goes into the chapter's `file`. -/
partial def walkSection (width : Nat) (depth : Nat) (file : String) (part : Part Manual)
    (buf : SaveBuffers) : SaveBuffers := Id.run do
  let .mk titleInlines _ _ intro subParts := part
  let mut buf := buf
  let hashes := String.ofList (List.replicate depth '#')
  let titleText := Text.inlinesToText titleInlines
  buf := appendBoth buf file (asModuleDoc s!"{hashes} {titleText}")
  buf := walkBlocks width file intro buf
  for p in subParts do
    buf := walkSection width (depth + 1) file p buf
  return buf

/--
The root of the walker. Each top-level sub-Part of the root document is
treated as a chapter and written to its own file (using the `file :=` metadata
key each chapter sets in its `%%%` block). The root file (`{vol}.lean`) gets one
`import` line per chapter. -/
def walkOuter (width : Nat) (vol : String) (text : Part Manual) (buf : SaveBuffers) :
    SaveBuffers := Id.run do
  let rootFile := vol ++ ".lean"
  let .mk _ _ _ _ subParts := text
  let mut buf := buf
  for p in subParts do
    buf := appendBoth buf rootFile s!"import {chapterModule vol p}\n"
  for p in subParts do
    let chapterFile := chapterPath vol p
    buf := appendBoth buf chapterFile s!"import {supportModuleName vol}\n\n"
    buf := walkSection width 1 chapterFile p buf
  return buf

/--
Write a complete generated Lake project at `dest`: the per-file buffer contents
under `dest/`, plus `lakefile.toml`, `lean-toolchain`, and a README. The root
module file is one of the saved buffers produced by `walkOuter`. -/
private def writeProject (dest : System.FilePath) (toolchain : String)
    (vol kind : String) (files : Array (String × String)) : IO Unit := do
  IO.FS.createDirAll dest
  -- Clear the volume source tree so chapter files that have since been renamed
  -- or removed don't linger as stale orphans. Other artifacts (`.lake`,
  -- `lakefile.toml`, `lean-toolchain`, `README.md`) are left alone.
  let chapterRoot := dest / vol
  if ← chapterRoot.pathExists then
    IO.FS.removeDirAll chapterRoot
  IO.FS.writeFile (dest / "lakefile.toml") (lakefileTemplate vol)
  IO.FS.writeFile (dest / "lean-toolchain") toolchain
  IO.FS.writeFile (dest / "README.md")
    s!"# {vol} — {kind} version\n\nGenerated from the Verso source.\n"
  for (relPath, body) in files do
    let target := dest / relPath
    target.parent.forM IO.FS.createDirAll
    IO.FS.writeFile target body

/--
Run `lake build` inside `dest` and report any failure via `logError`. Used to
verify each generated project compiles. Student builds are expected to succeed
with `sorry` warnings only; expected-error doc examples have already been
wrapped in `expect_failure` during extraction. -/
private def buildProject (dest : System.FilePath) (kind : String) :
    BuildLogT IO Unit := do
  IO.println s!"Building generated {kind} project at {dest}…"
  let res ← IO.Process.output {
    cmd := "lake", args := #["build"], cwd := dest
  }
  if res.exitCode != 0 then
    reportError <|
      s!"Generated {kind} project at {dest} failed to build " ++
      s!"(exit {res.exitCode}):\n--- stdout ---\n{res.stdout}\n" ++
      s!"--- stderr ---\n{res.stderr}"
  else
    IO.println s!"Generated {kind} project built successfully."

/--
Shared implementation. Writes the extracted Lean project to
`_out/<destSlug>/<variant>/lean/`, next to that variant's `html-multi/`
(which `manualMain` writes via `cfg.destination := "_out/<destSlug>/<variant>"`).
`modPrefix` is the uppercase module prefix used for the generated chapters'
module names and paths (e.g. `"LF"`, `"HL"`, `"TS"`); it is normally the same
as `destSlug` uppercased, but the draft executable passes `modPrefix := "LF"`
with `destSlug := "lf-draft"` so its output lands under `LF/…` in a separate
tree that never clobbers the real `lf` build.
`variant` selects which form of the code is written: `"solutions"` the
solution-filled form, `"terse"` the lecture form (`workinclass!` proofs and
solutions stubbed), anything else the student form.
`verify` runs `lake build` on the extracted project to confirm it compiles;
the draft emitter passes `verify := false`, since its not-yet-graduated
chapters are not expected to build standalone. -/
private def emitSavedImpl (destSlug modPrefix variant : String)
    (verify : Bool := true) :
    Mode → Config → TraverseState → Part Manual → BuildLogT IO Unit :=
  fun _mode _cfg _state text => do
    let buf : SaveBuffers := walkOuter (Text.fillWidthFor variant) modPrefix text ({} : SaveBuffers)
    let toolchain ← (IO.FS.readFile "lean-toolchain").toBaseIO >>= fun
      | .ok s => pure s
      | .error _ => pure "leanprover/lean4:v4.30.0-rc2\n"
    let supportModuleTemplate ← readSFLCompat
    let files : Array (String × String) :=
      buf.fold (init := #[(supportModulePath modPrefix, supportModuleTemplate)]) fun acc file (teacher, student, terse) =>
        let chosen :=
          if variant == "solutions" then teacher
          else if variant == "terse" then terse
          else student
        acc.push (file, mergeAdjacentModuleDocs chosen)
    let dest := System.FilePath.mk "_out" / destSlug / variant / "lean"
    writeProject dest toolchain modPrefix variant files
    if verify then buildProject dest variant

/-- `ExtraStep` for the student build: solutions elided. -/
def emitSavedStudent (vol : String) := emitSavedImpl vol.toLower vol "student"

/-- `ExtraStep` for the solutions build: solutions shown. -/
def emitSavedSolutions (vol : String) := emitSavedImpl vol.toLower vol "solutions"

/-- `ExtraStep` for the terse build: solutions elided and `workinclass!`
proofs stubbed to `sorry`. -/
def emitSavedTerse (vol : String) := emitSavedImpl vol.toLower vol "terse"

/-- Like `emitSavedSolutions`/`emitSavedStudent` but writes to
`_out/<destSlug>/…` while using `modPrefix` as the chapter module/path prefix.
Used by the draft executable to emit output for generated chapters that are not
yet in the real book, without clobbering the real volume's output. -/
def emitSavedSolutionsTo (destSlug modPrefix : String) :=
  emitSavedImpl destSlug modPrefix "solutions" (verify := false)

def emitSavedStudentTo (destSlug modPrefix : String) :=
  emitSavedImpl destSlug modPrefix "student" (verify := false)

def emitSavedTerseTo (destSlug modPrefix : String) :=
  emitSavedImpl destSlug modPrefix "terse" (verify := false)

end Save

end SFLMeta
