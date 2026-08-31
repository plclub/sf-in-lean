
import SFLMeta.Exercise

namespace SFLMeta.Save

namespace SourceRewrite

/-- Apply a set of byte-range replacements right-to-left so earlier edits
don't shift later positions. Works at the byte level via `ByteArray`. -/
def applyEdits (src : String) (edits : Array Replacement) : String := Id.run do
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
marker lines) is replaced with a single `--  FILL IN HERE` comment at the
indentation of the opening marker. In the teacher build the marker lines are
simply removed and the body is kept verbatim. If `-- END SOLUTION` is missing,
the rewrite extends to the end of the block. -/

/-- Trimmed equality test: `line` is the start marker (`-- SOLUTION`). -/
def isSolutionStart (line : String) : Bool :=
  line.trimAscii.toString == "-- SOLUTION"

/-- Trimmed equality test: `line` is the end marker (`-- END SOLUTION`). -/
def isSolutionEnd (line : String) : Bool :=
  line.trimAscii.toString == "-- END SOLUTION"

/-- The leading-whitespace prefix of `line` (its indentation). -/
def lineIndent (line : String) : String :=
  (line.takeWhile (·.isWhitespace)).toString

/-- Replace each `-- SOLUTION … -- END SOLUTION` block in `src` with a single
`--  FILL IN HERE` line at the indentation of the opening marker.  The two
spaces after `--` match the `commentPrefix` of the prose comments the line sits
among in the generated `.lean` files. -/
partial def applyFillInForStudent (src : String) : String := Id.run do
  let lines := src.splitOn "\n"
  let mut out : Array String := #[]
  let mut i := 0
  let n := lines.length
  while i < n do
    let line := lines[i]!
    if isSolutionStart line then
      out := out.push (lineIndent line ++ "--  FILL IN HERE")
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

end SourceRewrite
