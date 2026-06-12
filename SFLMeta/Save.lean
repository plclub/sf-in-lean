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

/--
When `true`, `lean` code blocks render with the teacher (solution-filled)
source in the HTML and TeX output. When `false` (the default), the rendered
output shows the student form: each `solution!(…)` is replaced by `sorry` and
each `-- SOLUTION … -- END SOLUTION` region is collapsed to `-- FILL IN HERE`.
The teacher source is always also elaborated, so author errors in solutions
are reported during the book build regardless of this setting. -/
register_option sf.showSolutions : Bool := {
  defValue := false
  descr := "When true, show the teacher (solution-filled) version of `lean` code blocks in the rendered HTML output."
}

namespace SFLMeta

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

/--
Render a Verso block to a Markdown-like string for inclusion in a `/-! … -/`
comment.  List items are prefixed with `- ` / `N. `; continuation lines are
indented to align under the item text. -/
private partial def blockToText : Verso.Doc.Block Manual → String
  | .para inlines => inlinesToText inlines
  | .code s => "`" ++ s.trimAscii.toString ++ "`"
  | .concat bs | .blockquote bs =>
    String.intercalate "\n\n" (bs.toList.map blockToText)
  | .ul lis =>
    String.intercalate "\n\n" (lis.toList.map fun li =>
      let body := String.intercalate "\n\n" (li.contents.toList.map blockToText)
      "- " ++ body.replace "\n" "\n  ")
  | .ol start lis =>
    String.intercalate "\n\n" (lis.toList.mapIdx fun i li =>
      let pfx := s!"{start + i}. "
      let indent := String.ofList (List.replicate pfx.length ' ')
      let body := String.intercalate "\n\n" (li.contents.toList.map blockToText)
      pfx ++ body.replace "\n" s!"\n{indent}")
  | .dl dis =>
    String.intercalate "\n" (dis.toList.map fun di =>
      inlinesToText di.term ++ "\n:   " ++
      String.intercalate "\n    " (di.desc.toList.map blockToText))
  | .other _ bs => String.intercalate "\n\n" (bs.toList.map blockToText)

/-! ## Lake project scaffold templates -/

/-- Contents of the generated project's `lakefile.toml`. -/
private def lakefileTemplate : String :=
  "name = \"plf-extracted\"\n" ++
  "version = \"0.1.0\"\n" ++
  "defaultTargets = [\"LF\"]\n\n" ++
  "[[lean_lib]]\n" ++
  "name = \"LF\"\n"

/-! ## ExtraStep walker -/

/-- Per-file buffers accumulated by the saver: `(teacher source, student source)`. -/
private abbrev SaveBuffers := HashMap String (String × String)

private def appendBoth (buf : SaveBuffers) (file : String) (s : String) : SaveBuffers :=
  let (t, st) := buf.getD file ("", "")
  buf.insert file (t ++ s, st ++ s)

private def appendTeacherStudent
    (buf : SaveBuffers) (file : String) (teacher student : String) : SaveBuffers :=
  let (t, st) := buf.getD file ("", "")
  buf.insert file (t ++ teacher, st ++ student)

/-- Wrap a string in `/-! … -/` module-doc comment form, normalising trailing whitespace. -/
-- To extend the inline treatment to multi-line blocks, replace the branch with
-- just `"/-! " ++ t ++ " -/\n\n"` (the else branch below) for all cases.
-- That puts the first content line on the `/-!` line and the last on the `-/` line.
private def asModuleDoc (s : String) : String :=
  let t := s.trimAscii.toString
  -- if t.contains '\n' then "/-!\n" ++ t ++ "\n-/\n\n"
  -- else
  "/-! " ++ t ++ " -/\n\n"

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

/-! ## Block extension that carries pre-computed teacher and student source -/

/-!
`Block.leanSaved` wraps an elaborated `lean` block and records both the teacher
and student source variants computed at elaboration time. HTML/TeX rendering
passes through to the inner block; the saver consumes the recorded strings
directly without re-parsing anything. -/

block_extension Block.leanSaved (teacher : String) (student : String) where
  data := Json.arr #[.str teacher, .str student]
  traverse _ _ _ := pure none
  toHtml := some fun _ goB _ _ contents => contents.mapM goB
  toTeX  := some fun _ goB _ _ contents => contents.mapM goB

/-- Decode a `Block.leanSaved` payload `(teacher, student)`. -/
private def decodeLeanSaved? (data : Json) : Option (String × String) :=
  match data with
  | .arr #[.str t, .str s] => some (t, s)
  | _ => none

/-! ## Syntactic rewriting of `solution!` markers

The `solution!` term and tactic elaborators (declared in `SFLMeta.Exercise`)
register the source range of each invocation into `solutionEditsRef` as they
run. The project-local `lean` code-block expander (below) snapshots that ref
around its call to the upstream Lean elaborator, then uses the freshly added
ranges to compute two variants of the block's source: a teacher form (just the
`solution!` keyword removed, parenthesised body kept) and a student form (the
whole `solution!(…)` invocation replaced by `sorry`). Both variants are stored
in a `Block.leanSaved` wrapper that the saver consumes verbatim — no parsing
happens at extraction time. -/

/-- Apply a set of byte-range replacements right-to-left so earlier edits
don't shift later positions. Works at the byte level via `ByteArray`. -/
private def applyEdits (src : String) (edits : Array Replacement) : String := Id.run do
  let sorted := edits.qsort fun a b => a.range.start.byteIdx > b.range.start.byteIdx
  let mut src := src
  for ⟨{ start, stop }, replacement⟩ in sorted do
    if h : start.IsValid src ∧ stop.IsValid src then
      let slice := src.slice! ⟨start, h.1⟩ ⟨stop, h.2⟩
      src := src.replace slice replacement
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

/-! ## `lean` code-block override

Wraps each ` ```lean … ``` ` code block. The pipeline is:

1. Snapshot the current environment and scopes (the "pre-teacher" state).
2. Delegate to the upstream Lean code-block expander to elaborate the teacher
   form of the source. This typechecks the author's solutions (giving live
   error feedback during the book build) and populates `studentEditRef` /
   `teacherEditRef` with the source ranges of every `solution!(…)` invocation.
3. Convert those absolute source ranges to offsets relative to the block's
   own source string and compute the teacher and student variants.
4. If the `sf.showSolutions` option is `true`, return the upstream block
   unchanged so the rendered HTML shows the teacher form.
5. Otherwise, run `elabAndHighlightStudent` on the student source (starting
   from the pre-teacher environment, so prior chapter definitions are
   available but this block's teacher-side defs are not) and emit a
   `Block.lean` wrapping the resulting `Highlighted` so the rendered HTML
   shows the student form. -/

@[code_block]
def lean : CodeBlockExpanderOf Verso.Genre.Manual.InlineLean.LeanBlockConfig
  | config, str => do
    SFLMeta.studentEditRef.set #[]
    SFLMeta.teacherEditRef.set #[]
    let preEnv ← getEnv
    let preScopes ← getScopes
    let underlying ← Verso.Genre.Manual.InlineLean.lean config str
    let student ← studentEditRef.get
    let teacher ← teacherEditRef.get
    let src := str.getString

    -- `strLitInputContext` parses starting at `str.getPos?`, so the byte
    -- indices recorded by the elaborator are absolute file offsets. The
    -- string-literal contents begin one byte past the opening quote.
    let teacherRanges :=
      teacher.flatMap (·.edits) |>.map fun r =>
        { r with
          range.start.byteIdx := r.range.start.byteIdx - str.raw.getPos!.byteIdx
          range.stop.byteIdx := r.range.stop.byteIdx - str.raw.getPos!.byteIdx
          }
    let studentRanges := student.flatMap (·.edits) |>.map fun r =>
        { r with
          range.start.byteIdx := r.range.start.byteIdx - str.raw.getPos!.byteIdx
          range.stop.byteIdx := r.range.stop.byteIdx - str.raw.getPos!.byteIdx
          }
    let teacher := stripFillInMarkers (applyEdits src teacherRanges)
    let student := applyFillInForStudent (applyEdits src studentRanges)
    if sf.showSolutions.get (← getOptions) then
      ``(Verso.Doc.Block.other
          (SFLMeta.Block.leanSaved $(quote teacher) $(quote student))
          #[$underlying])
    else
      let studentHls ← elabAndHighlightStudent preEnv preScopes student
      let range := Syntax.getRange? str
      let lspRange := range.map (← getFileMap).utf8RangeToLspRange
      ``(Verso.Doc.Block.other
          (SFLMeta.Block.leanSaved $(quote teacher) $(quote student))
          #[Verso.Doc.Block.other
              (Verso.Genre.Manual.InlineLean.Block.lean
                $(quote studentHls)
                (some $(quote (← getFileName)))
                $(quote lspRange))
              #[Verso.Doc.Block.code $(quote student)]])

/-- Find the first `Block.code` source string in `contents`. -/
private def findCodeSource? (contents : Array (Block Manual)) : Option String :=
  contents.findSome? fun
    | .code s => some s
    | _ => none

/-- Find the ASCII alt text inside a `diagramWithAlt`: the first plain code block. -/
private def findAlt? (contents : Array (Verso.Doc.Block Manual)) : Option String :=
  contents.findSome? fun
    | .code s => some s
    | _ => none

mutual

/--
Walk a list of blocks, batching consecutive `.para` blocks into a single
`/-! … -/` comment instead of emitting one per paragraph. -/
partial def walkBlocks (file : String) (bs : Array (Verso.Doc.Block Manual))
    (buf : SaveBuffers) : SaveBuffers := Id.run do
  let mut buf := buf
  let mut pending : Array String := #[]
  for b in bs do
    match b with
    | .para inls => pending := pending.push (inlinesToText inls)
    | _ =>
      if !pending.isEmpty then
        buf := appendBoth buf file (asModuleDoc (String.intercalate "\n\n" pending.toList))
        pending := #[]
      buf := walkBlock file b buf
  if !pending.isEmpty then
    buf := appendBoth buf file (asModuleDoc (String.intercalate "\n\n" pending.toList))
  return buf

/--
Walk a single block, accumulating teacher and student content into `buf` for
`file`. The bulk of the saver's logic lives here. -/
partial def walkBlock (file : String) (b : Verso.Doc.Block Manual)
    (buf : SaveBuffers) : SaveBuffers := Id.run do
  match b with
  | .other which contents =>
    let name := which.name
    if name == ``Block.ignore then
      return buf
    if name == ``Verso.Genre.Manual.Block.diagram then
      return buf
    if name == ``Verso.Genre.Manual.Block.diagram then
      return buf
    if name == ``Block.leanSaved then
      -- The wrapper carries pre-computed teacher and student variants.
      if let some (teacher, student) := decodeLeanSaved? which.data then
        return appendTeacherStudent buf file
          (teacher.trimAscii.toString ++ "\n\n")
          (student.trimAscii.toString ++ "\n\n")
      return buf
    if name == ``Block.exercise then
      -- Emit a `### Exercise (N⭐): name` heading; the contained `lean`
      -- blocks render normally via recursion below.
      if let some (rating, exName) := decodeExercise? which.data then
        let stars := String.ofList (List.replicate rating '⭐')
        let header := s!"### Exercise ({rating} star{if rating == 1 then "" else "s"}): {exName} {stars}"
        let mut buf := appendBoth buf file (asModuleDoc header)
        buf := walkBlocks file contents buf
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
      buf := walkBlocks file contents buf
      return buf
    if name == ``Block.terse then
      -- Terse content kept in the tree only in terse builds (full builds replace
      -- with concat #[] during traverse). Recurse into children.
      return walkBlocks file contents buf
    if name == ``Block.full then
      -- Full content kept in the tree only in full builds. Recurse into children.
      return walkBlocks file contents buf
    if name == ``Block.slidebreak then
      -- Slide-break marker: emit nothing in all generated .lean files.
      return buf
    -- Unknown extension block: recurse into children as a best-effort.
    walkBlocks file contents buf
  | .para inls => return appendBoth buf file (asModuleDoc (inlinesToText inls))
  | .code s => return appendBoth buf file (asModuleDoc s.trimAscii.toString)
  | .concat bs | .blockquote bs => walkBlocks file bs buf
  | .ul lis =>
    let items := lis.toList.map fun li =>
      let body := String.intercalate "\n\n" (li.contents.toList.map blockToText)
      "- " ++ body.replace "\n" "\n  "
    return appendBoth buf file (asModuleDoc (String.intercalate "\n" items))
  | .ol start lis =>
    let items := lis.toList.mapIdx fun i li =>
      let pfx := s!"{start + i}. "
      let indent := String.ofList (List.replicate pfx.length ' ')
      let body := String.intercalate "\n\n" (li.contents.toList.map blockToText)
      pfx ++ body.replace "\n" s!"\n{indent}"
    return appendBoth buf file (asModuleDoc (String.intercalate "\n" items))
  | .dl dis =>
    let mut buf := buf
    for di in dis do
      buf := walkBlocks file di.desc buf
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
private def chapterPath (p : Part Manual) : String :=
  "LF/" ++ chapterFileBase p ++ ".lean"

/-- Generated Lean module name for a chapter Part. Uses the raw `file :=`
identifier when it is a plain alphanumeric/underscore name; falls back to
French-quote brackets for slugs that contain hyphens or other punctuation. -/
private def chapterModule (p : Part Manual) : String :=
  let base := chapterFileBase p
  if base.all (fun c => c.isAlphanum || c == '_') then "LF." ++ base
  else "LF.«" ++ base ++ "»"

/--
Walk a section (a Part at depth ≥ 1, inside a chapter). The section's title is
emitted as a `#`-prefixed module-doc heading whose level equals `depth`; all
content goes into the chapter's `file`. -/
partial def walkSection (depth : Nat) (file : String) (part : Part Manual)
    (buf : SaveBuffers) : SaveBuffers := Id.run do
  let .mk titleInlines _ _ intro subParts := part
  let mut buf := buf
  let hashes := String.ofList (List.replicate depth '#')
  let titleText := inlinesToText titleInlines
  buf := appendBoth buf file (asModuleDoc s!"{hashes} {titleText}")
  buf := walkBlocks file intro buf
  for p in subParts do
    buf := walkSection (depth + 1) file p buf
  return buf

/--
The root of the walker. Each top-level sub-Part of the root document is
treated as a chapter and written to its own file (using the `file :=` metadata
key each chapter sets in its `%%%` block). The root file (`LF.lean`) gets one
`import` line per chapter. -/
def walkOuter (rootFile : String) (text : Part Manual) (buf : SaveBuffers) :
    SaveBuffers := Id.run do
  let .mk _ _ _ _ subParts := text
  let mut buf := buf
  for p in subParts do
    buf := appendBoth buf rootFile s!"import {chapterModule p}\n"
  for p in subParts do
    let chapterFile := chapterPath p
    -- BCP: Maybe this is not needed?
    -- buf := appendBoth buf chapterFile "import Lean\n\nopen Lean\n\n"
    buf := walkSection 1 chapterFile p buf
  return buf

/--
Write a complete generated Lake project at `dest`: the per-file buffer
contents under `dest/`, plus `lakefile.toml`, `lean-toolchain`, and a `LF.lean`
that imports `LF.STLC`. -/
private def writeProject (dest : System.FilePath) (toolchain : String)
    (kind : String) (files : Array (String × String)) : IO Unit := do
  IO.FS.createDirAll dest
  -- Clear the LF/ source tree so chapter files that have since been renamed
  -- or removed don't linger as stale orphans. Other artifacts (`.lake`,
  -- `lakefile.toml`, `lean-toolchain`, `README.md`) are left alone.
  let chapterRoot := dest / "LF"
  if ← chapterRoot.pathExists then
    IO.FS.removeDirAll chapterRoot
  IO.FS.writeFile (dest / "lakefile.toml") lakefileTemplate
  IO.FS.writeFile (dest / "lean-toolchain") toolchain
  IO.FS.writeFile (dest / "README.md")
    s!"# LF — {kind} version\n\nGenerated from the Verso source.\n"
  for (relPath, body) in files do
    let target := dest / relPath
    target.parent.forM IO.FS.createDirAll
    IO.FS.writeFile target body

/--
Run `lake build` inside `dest` and report any failure via `logError`. Used to
verify each generated project compiles. Student builds are expected to succeed
with `sorry` warnings only. -/
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
Shared implementation. `root` is the parent directory; each entry in `variants`
is `(dirName, useTeacherContent)`.  All three generation targets write under
`_out/generated/` regardless of `cfg.destination`. -/
private def emitSavedImpl
    (root : System.FilePath)
    (variants : List (String × Bool)) :
    Mode → Config → TraverseState → Part Manual → BuildLogT IO Unit :=
  fun _mode _cfg _state text => do
    let buf : SaveBuffers := walkOuter "LF.lean" text ({} : SaveBuffers)
    let toolchain ← (IO.FS.readFile "lean-toolchain").toBaseIO >>= fun
      | .ok s => pure s
      | .error _ => pure "leanprover/lean4:v4.30.0-rc2\n"
    for (name, isTeacher) in variants do
      let files : Array (String × String) :=
        buf.fold (init := #[]) fun acc file (teacher, student) =>
          acc.push (file, mergeAdjacentModuleDocs (if isTeacher then teacher else student))
      let dest := root / name
      writeProject dest toolchain name files
      buildProject dest name

/--
The Verso `ExtraStep` for full builds. Produces `_out/generated/solutions/`
(with solutions) and `_out/generated/student/` (without). -/
def emitSaved : Mode → Config → TraverseState → Part Manual → BuildLogT IO Unit :=
  emitSavedImpl "_out/generated" [("solutions", true), ("student", false)]

/--
The Verso `ExtraStep` for terse builds. Produces `_out/generated/terse/`
(terse, no solutions). -/
def emitSavedTerse : Mode → Config → TraverseState → Part Manual → BuildLogT IO Unit :=
  emitSavedImpl "_out/generated" [("terse", false)]

end SFLMeta
