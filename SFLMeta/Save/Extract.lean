import VersoManual

import SFLMeta.Ignore
import SFLMeta.Bnf
import SFLMeta.Exercise
import SFLMeta.DisplayMath
import SFLMeta.Quiz
import SFLMeta.Terse
import SFLMeta.SlideBreak
import SFLMeta.Grade

import SFLMeta.Save.SourceRewrite
import SFLMeta.Save.Lean
import SFLMeta.Save.CodeBlock

import Std.Data.HashMap

open Lean
open Std (HashMap)
open Verso Doc Genre Manual

namespace SFLMeta.Save


/-- Per-file buffers accumulated by the saver -/
abbrev SaveBuffers := HashMap String (Variants String)

namespace SaveBuffers

def appendAll (buf : SaveBuffers) (file : String) (s : String) : SaveBuffers :=
  let vs := buf.getD file default
  buf.insert file <| vs.map (· ++ s)

def appendOnly (buf : SaveBuffers) (file : String) (variant : Variant) (s : String) : SaveBuffers :=
  let vs := buf.getD file default |>.mapV fun v x => if v == variant then x ++ s else x
  buf.insert file vs

def append
    (buf : SaveBuffers) (file : String) (vs' : Variants String) : SaveBuffers :=
  let vs := buf.getD file default
  buf.insert file <| vs ++ vs'

end SaveBuffers

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

/-- The prose fill width for a build variant. -/
def fillWidthFor : Variant → Nat
  | .terse => terseFillWidth
  | .student | .solutions | .grading => proseFillWidth
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

/-- Drop leading and trailing all-whitespace lines from `s`, preserving each
remaining line's own leading whitespace (so ASCII diagrams and hand-aligned
displays keep their column alignment).

Defined as a `String.` method (not a plain `SFLMeta` function) on purpose: its one
caller applies it to a `let`-bound `match` whose result type is not yet pinned,
and a plain application there leaves the elaborator stuck on a universe
constraint.  Dot-notation (`src.stripBlankEdgeLines`, like `src.trimAscii`) pins
`src : String` first and elaborates cleanly — so keep the dot-notation call. -/
defmethod String.stripBlankEdgeLines (s : String) : String :=
  let blank : String → Bool := fun l => l.all (·.isWhitespace)
  let ls := s.splitOn "\n"
  let ls := (((ls.dropWhile blank).reverse).dropWhile blank).reverse
  String.intercalate "\n" ls

/--
Render a Verso block to a Markdown-like string for inclusion in a `/-! … -/`
comment, filling prose to `width` columns.  List items are prefixed with `- ` /
`N. `; continuation lines are indented to align under the item text. -/
partial def blockToText (width : Nat) : Verso.Doc.Block Manual → String
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


/-! ## ExtraStep walker -/

/-- Render a string as a block of `--` line comments, one per line (blank lines
stay completely blank), normalising trailing whitespace. -/
private def asModuleDoc (s : String) : String :=
  let t := s.trimAscii.toString
  let commented := String.intercalate "\n"
    ((t.splitOn "\n").map fun line =>
      if line.all (·.isWhitespace) then "" else "-- " ++ line)
  commented ++ "\n\n"

section

/-- Render a shown dev note as one contiguous `--` comment block, visually set
off from surrounding prose: the label line first, body lines indented 4 spaces
under it, and interior blank lines kept as bare `--` (not truly blank) so the
note reads as a single unit. -/
def devNoteComment (label body : String) : String :=
  let indented := String.intercalate "\n"
    ((body.trimAscii.toString.splitOn "\n").map fun l =>
      if l.all (·.isWhitespace) then "--" else "--     " ++ l)
  "-- " ++ label ++ ":\n" ++ indented ++ "\n\n"

/-- Decode a `Block.bnf` payload and render the grammar as an aligned plain-text
display (`Bnf.toTextImpl`), which is what an extracted `.lean` file wants: the
authoring source spells terminals as string literals and metavariables with a
leading underscore, and neither is meant to be read.  Falls back to the original
source if the payload cannot be decoded. -/
def decodeBnfSource? (data : Json) : Option String :=
  match data with
  | .arr #[.str jsonStr, .str src] =>
    match Json.parse jsonStr >>= fromJson? with
    | .ok (b : BNF) => some (Bnf.toTextImpl b)
    | .error _      => some src
  | _ => none

/-- Decode a `Block.exercise` payload `(rating, name, level, manual)`, tolerating
the older 2-element `(rating, name)` form.  (See `SFLMeta.decodeExerciseData`.) -/
def decodeExercise? (data : Json) : Option (Nat × String × Option String × Bool) :=
  match data with
  | .arr #[.num _, .str _, _, _] | .arr #[.num _, .str _] => some (decodeExerciseData data)
  | _ => none

/-- Does one of `blocks` contain a `Block.suppressPreviousHeaderWhenTerse`
marker?  The marker is emitted at a section's top level, but elaboration wraps
each source block in `.concat` layers, so look through those (only — the marker
never sits inside another extension block in the terse tree). -/
partial def hasSuppressHeaderMarker (blocks : Array (Verso.Doc.Block Manual)) : Bool :=
  blocks.any fun b =>
    match b with
    | .other which _ => which.name == ``Block.suppressPreviousHeaderWhenTerse
    | .concat bs => hasSuppressHeaderMarker bs
    | _ => false

/-- Find the ASCII alt text inside a `diagramWithAlt`: the first plain code block. -/
def findAlt? (contents : Array (Verso.Doc.Block Manual)) : Option String :=
  contents.findSome? fun
    | .code s => some s
    | _ => none

/-- For wrapping code in `sf_experiment` and `sf_expect_failure` -/
def wrapIndented (startText body : String) : String :=
  let body := body.trimAscii.toString.splitOn "\n" |>.map ("  " ++ ·) |> String.intercalate "\n"
  startText ++ "\n" ++ body ++ "\n\n"

end

section

/--
Determine the file-name base for a chapter Part. Uses the `file := …` HTML
metadata if the chapter author set it; otherwise falls back to the sluggified
title (matching what Verso uses for the HTML output filename). -/
def chapterFileBase (p : Part Manual) : String :=
  let .mk _ titleStr meta? _ _ := p
  (meta?.bind (·.file)).getD titleStr.sluggify.toString


/-- Generated Lean file path for a chapter Part. -/
def chapterPath (vol : String) (p : Part Manual) : String :=
  vol ++ "/" ++ chapterFileBase p ++ ".lean"

/-- Generated Lean module name for a chapter Part. Uses the raw `file :=`
identifier when it is a plain alphanumeric/underscore name; falls back to
French-quote brackets for slugs that contain hyphens or other punctuation. -/
def chapterModule (vol : String) (p : Part Manual) : String :=
  let base := chapterFileBase p
  if base.all (fun c => c.isAlphanum || c == '_') then vol ++ "." ++ base
  else vol ++ ".«" ++ base ++ "»"

end

/-! ## Support module template
  Create `SFLCompat.lean` with custom commands used in generated projects.
-/

section

def supportModuleName (vol : String) : String :=
  vol ++ ".SFLCompat"

def supportModulePath (vol : String) : String :=
  vol ++ "/SFLCompat.lean"

def readSFLCompat : IO String := IO.FS.readFile "SFLMeta/SFLCompat.lean"

end

mutual

open Text

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
    | .para inls => pending := pending.push (Text.paraToText width inls)
    | .ul _ | .ol _ _ => pending := pending.push (Text.blockToText width b)
    | _ =>
      if !pending.isEmpty then
        buf := buf.appendAll file (asModuleDoc (String.intercalate "\n\n" pending.toList))
        pending := #[]
      buf := walkBlock width file b buf
  if !pending.isEmpty then
    buf := buf.appendAll file (asModuleDoc (String.intercalate "\n\n" pending.toList))
  return buf

/--
Walk a single block, accumulating content for the student, solutions, and terse
variants in `buf` for `file`. The bulk of the extraction walker's block-specific
logic lives here. -/
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
      -- The wrapper carries pre-computed student, solutions, and terse source
      -- variants plus the extraction-relevant `lean` block flags. Verso still
      -- checks and renders the selected child normally; the generated project
      -- gets code, `sf_experiment`, or `sf_expect_failure` according to
      -- `LeanSaved.Data.extractionMode`.
      if let some saved := LeanSaved.decode? which.data then
        match saved.extractionMode with
        | .code =>
          return buf.append file <| saved.variants.map fun src =>
            -- `src` doesn't have ending newline
           src.trimAscii.toString ++ "\n\n"
        | .experiment =>
          return buf.append file <| saved.variants.map (wrapIndented "sf_experiment")
        | .expectFailure =>
          return buf.append file <| saved.variants.map (wrapIndented "sf_expect_failure")
      return buf
    if name == ``Block.importBlock then
      -- Cross-chapter `import` lines shown to the reader.  The extracted
      -- files get their import lines from the chapter source's header
      -- preamble in `emitSavedImpl` (which also bundles non-chapter
      -- prerequisites), so nothing is emitted here.
      return buf
    if name == ``Block.exercise then
      -- Emit a `### Exercise (N⭐): name` heading; the contained `lean`
      -- blocks render normally via recursion below.
      if let some (rating, exName, level, manual) := decodeExercise? which.data then
        let stars := String.ofList (List.replicate rating '⭐')
        let desig := exerciseDesignation level manual
        let header := s!"### Exercise ({rating} star{if rating == 1 then "" else "s"}): {exName}{desig} {stars}"
        let mut buf := buf.appendAll file (asModuleDoc header)
        buf := walkBlocks width file contents buf
        return buf
      return buf
    if name == ``Block.bnf then
      if let some src := decodeBnfSource? which.data then
        return buf.appendAll file (asModuleDoc src.trimAscii.toString)
    if name == ``Block.display || name == ``Block.displaymath then
      -- A ` ```display ` / ` ```displaymath ` block is a *display*: its line
      -- structure is significant, so it is emitted verbatim as a comment — each
      -- source line kept on its own line and indented a couple of spaces to set
      -- it off — and is NEVER reflowed/filled into a paragraph the way ordinary
      -- prose is.  `display` stores its source string directly; `displaymath`
      -- carries no data, so recover the text from its `Block.para`/math children.
      let src :=
        match which.data with
        | .str s => s
        | _ =>
          -- `displaymath`: one `Block.para` per equation, each holding a single
          -- math inline; take the raw inline text (unfilled), one line each.
          String.intercalate "\n" (contents.toList.filterMap fun (b : Verso.Doc.Block Manual) =>
            match b with
            | .para inls => some (inlinesToText inls)
            | _ => none)
      -- Emit as its own comment, built by hand rather than via `asModuleDoc`:
      -- each source line kept on its own line and indented under `-- ` to set the
      -- display off, and NEVER reflowed/filled the way prose is.  Only leading and
      -- trailing *blank lines* are dropped — a line's own leading whitespace is
      -- preserved verbatim, so ASCII diagrams and hand-aligned displays keep their
      -- column alignment.  (`asModuleDoc`/`trimAscii` would trim the whole block
      -- and so drop the first line's indentation.)
      let commented := String.intercalate "\n"
        ((src.stripBlankEdgeLines.splitOn "\n").map fun l =>
          if l.all (·.isWhitespace) then "" else "--   " ++ l)
      return buf.appendAll file (commented ++ "\n\n")
    if name == ``Block.diagramWithAlt then
      match findAlt? contents with
      | .some alt => return buf.appendAll file (asModuleDoc alt.trimAscii.toString)
      | .none => return buf
    if name == ``Block.details then
      -- The contents are inlined verbatim, bracketed by skip markers so the
      -- reader of the `.lean` can tell this was a collapsed, skippable aside in
      -- the book. The summary (if any) rides along on the opening marker.
      let summary :=
        match which.data with
        | .str s => s
        | _ => ""
      let opener := if summary.isEmpty
        then "THESE DETAILS CAN BE SKIPPED:"
        else s!"THESE DETAILS CAN BE SKIPPED: {summary}"
      let mut buf := buf.appendAll file (asModuleDoc opener)
      buf := walkBlocks width file contents buf
      buf := buf.appendAll file (asModuleDoc "END DETAILS")
      return buf
    if name == ``Block.quiz then
      -- A quiz is shown in every build product; label it so the reader of the
      -- generated `.lean` can tell the question apart from surrounding prose.
      let mut buf := buf.appendAll file (asModuleDoc "_Quiz:_")
      buf := walkBlocks width file contents buf
      return buf
    if name == ``Block.quizSolution then
      -- A quiz answer is elided from every generated `.lean` build product — it
      -- surfaces only in the HTML book, as a click-to-reveal button.  (The block
      -- is still kept through traversal for that HTML rendering; the saver just
      -- emits nothing.)
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
    if name == ``Block.suppressPreviousHeaderWhenTerse then
      -- Full-only-heading marker: consumed by `walkSection` (which suppresses
      -- the heading it follows); emits nothing itself.
      return buf
    if name == ``Block.devcomment then
      -- A dev note passes through as a labelled comment when its urgency makes
      -- it shown (`devNoteShown`: `NOW`, `BeforeNextRelease`, or none);
      -- otherwise nothing is emitted. `devNoteComment` sets the note off from
      -- surrounding prose (indented body, contiguous comment block); the body is
      -- filled 4 columns narrower to compensate for that indentation.
      if let some (author, urgency, year) := decodeDevData? which.data then
        if devNoteShown urgency then
          let body := String.intercalate "\n\n"
            (contents.toList.map (blockToText (width - 4)))
          return buf.appendAll file
            (devNoteComment (devNoteLabel author urgency year) body)
      return buf
    if name == ``Block.gradeTheorem then
      let ⟨points, names⟩ := decodeGradeTheoremData which.data
      let names := " ".intercalate (names.map Name.toString).toList
      return buf.appendOnly file .grading s!"attribute [autogradedProof {points}] {names}\n\n"
    if name == ``Block.autogradedHole then
      let names := decodeAutogradedHoleData which.data
      let names := " ".intercalate (names.map Name.toString).toList
      return buf.appendOnly file .grading s!"attribute [autogradedHole] {names}\n\n"
    -- Unknown extension block: recurse into children as a best-effort.
    -- NB: :::instructors blocks carry no children (their bodies are dropped at
    -- elaboration), so this recursion is a no-op for them.
    walkBlocks width file contents buf
  | .para inls => return buf.appendAll file (asModuleDoc (paraToText width inls))
  | .code s => return buf.appendAll file (asModuleDoc s.trimAscii.toString)
  | .concat bs | .blockquote bs => walkBlocks width file bs buf
  | .ul _ | .ol _ _ =>
    -- Normally batched with adjacent paragraphs in `walkBlocks`; this case is
    -- only reached for a list arriving outside that batching.
    return buf.appendAll file (asModuleDoc (blockToText width b))
  | .dl dis =>
    -- A description list: the term of each item is content too, so emit it
    -- before walking that item's description blocks.
    let mut buf := buf
    for di in dis do
      buf := buf.appendAll file (asModuleDoc (inlinesToText di.term))
      buf := walkBlocks width file di.desc buf
    return buf


end

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
  -- A `Block.suppressPreviousHeaderWhenTerse` marker among the section's own
  -- blocks means the heading is full-only. The marker survives traversal only
  -- in terse builds (full builds replace it with an empty block), so its
  -- presence here says: this is the terse tree, suppress the heading (the
  -- content still flows).
  if !hasSuppressHeaderMarker intro then
    buf := buf.appendAll file (asModuleDoc s!"{hashes} {titleText}")
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
    buf := buf.appendAll rootFile s!"import {chapterModule vol p}\n"
  for p in subParts do
    let chapterFile := chapterPath vol p
    buf := buf.appendOnly chapterFile .grading s!"import ComparatorAutograderLib\n"
    buf := buf.appendAll chapterFile s!"import {supportModuleName vol}\n\n"
    buf := walkSection width 1 chapterFile p buf
  return buf
