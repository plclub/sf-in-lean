#!/usr/bin/env python3
"""
to_verso.py  —  Convert a code-forward LF chapter to docs-forward Verso.

Each /- ... -/ block comment becomes Verso prose.  Code is wrapped in
```lean``` fences.  Structural markers are converted to Verso directives:

  /- ## Title -/      → section heading
  -- FULL / -- /FULL  → :::full blocks
  -- TERSE: /- *** -/ → :::slidebreak
  -- TERSE: /- txt -/ → :::terse blocks
  -- INSTRUCTORS:     → stripped
  -- EX1 (name)       → :::exercise (rating := N) (name := "name")
  -- []               → closes :::exercise
  -- GRADE_THEOREM    → stripped
  -- BCP:/JC:/etc.    → :::dev blocks
  code                → ```lean blocks

Note: -- ADMITDEF / -- /ADMITDEF and -- ADMITTED markers are left as Lean
comments inside code blocks.  A future pass will convert them to solution!().

Usage (from the repo root):
    python3 scripts/to_verso.py LF/Basics.lean LF/BasicsVerso.lean
"""

import argparse
import pathlib
import re
import sys

# ---------------------------------------------------------------------------
# Verso header / footer
# ---------------------------------------------------------------------------

HEADER_TEMPLATE = """\
import VersoManual
import VersoManual.InlineLean
import Illuminate
import SFLMeta.Bnf
import SFLMeta.Ignore
import SFLMeta.Save
import SFLMeta.Comment
import SFLMeta.Exercise
import SFLMeta.SlideBreak
import SFLMeta.Terse

open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

set_option maxRecDepth 100000

noncomputable section

#doc (Manual) "{title}" =>
%%%
htmlSplit := .never
file := "{file}"
%%%

"""

FOOTER = "end\n"

# ---------------------------------------------------------------------------
# Title extraction
# ---------------------------------------------------------------------------

def extract_title(src: str) -> str:
    """Pull the chapter title from the opening /- ... -/ block comment."""
    m = re.match(r"\s*/\-(.*?)-/", src, re.DOTALL)
    if m:
        body = m.group(1)
        lines = [l.strip() for l in body.splitlines() if l.strip()]
        if lines:
            title = lines[0].lstrip("#").strip()
            if title:
                return title
    return "Chapter"

# ---------------------------------------------------------------------------
# Tokenizer helpers
# ---------------------------------------------------------------------------

def _strip_title_comment(src: str) -> str:
    """Remove the opening /- title -/ block comment (already used for #doc title)."""
    return re.sub(r'^\s*/\-.*?-/\s*', '', src, count=1, flags=re.DOTALL)

def _is_label_comment(text: str) -> bool:
    """True when text (stripped comment body) should be stripped in Verso output.

    This covers:
      - Single identifiers like "test_nandb1" or "test_leb3'" (test-case labels)
      - Pure separator lines like "############################" (visual dividers)
      - Lean output annotations like "==> true : Bool" or "===> ..." (#check/#eval)
      - Author/editor notes that appear as block comments (BCP: ..., MWH: ..., etc.)
    These act as code-block separators but produce no visible Verso output.
    """
    t = text.strip()
    return (bool(re.match(r"^[\w.']+$", t)) or
            bool(re.match(r'^#{3,}\s*$', t)) or
            bool(re.match(r'^=+>', t)) or
            bool(re.match(r'^(BCP|JC|MWH|CGH|RAB)[: ]', t)))

def _parse_section_header(text: str):
    """If text is a section-header comment, return (level, title); else None.

    Recognised forms:
      ########...# Title   → level 1  (the ######...# line is ignored;
                                        the next non-blank line has # Title)
      # Title              → level 1
      ## Title             → level 2
      ### Title            → level 3
    """
    lines = [l.strip() for l in text.splitlines() if l.strip()]
    if not lines:
        return None
    # Strip a separator line made of # repeated
    if re.match(r'^#{4,}\s*$', lines[0]):
        lines = lines[1:]
    if not lines:
        return None
    m = re.match(r'^(#{1,6})\s+(.+)$', lines[0])
    if m:
        return len(m.group(1)), m.group(2).strip()
    return None

def _extract_comment_text(raw_lines):
    """Strip /- and -/ delimiters from a list of raw source lines and dedent."""
    if not raw_lines:
        return ''
    lines = list(raw_lines)
    # Remove opening /-
    lines[0] = re.sub(r'^\s*/-\s?', '', lines[0])
    # Remove closing -/
    lines[-1] = re.sub(r'\s*-/\s*$', '', lines[-1])

    # Dedent: remove common leading whitespace from non-blank lines
    non_blank = [l for l in lines if l.strip()]
    if non_blank:
        min_indent = min(len(l) - len(l.lstrip()) for l in non_blank)
        lines = [l[min_indent:] if len(l) >= min_indent else l.lstrip()
                 for l in lines]

    # Trim leading/trailing blank lines
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()

    return '\n'.join(lines)

# ---------------------------------------------------------------------------
# Tokenizer
# ---------------------------------------------------------------------------

# Marker patterns checked against the stripped line
_INSTRUCTOR_RE = re.compile(r'^-- INSTRUCTORS:')
_INSTRUCTOR_CONT_RE = re.compile(r'^--(\s{3,}|\t|\s*$)')  # continuation
_FULL_OPEN_RE = re.compile(r'^-- FULL$')
_FULL_CLOSE_RE = re.compile(r'^-- /FULL$')
_SLIDEBREAK_RE = re.compile(r'^-- TERSE:\s*/- \*\*\* -/$')
_TERSE_DELIM_RE = re.compile(r'^-- TERSE:\s*/-(.*?)-/$')
_TERSE_PLAIN_RE = re.compile(r'^-- TERSE:\s+(.+)$')
_EX_RE = re.compile(r'^-- EX(\d+)\??\s+\((\w+)\)$')
_EX_CLOSE_RE = re.compile(r'^-- \[\]$')
_GRADE_RE = re.compile(r'^--\s+GRADE_')
_SOLUTION_OPEN_RE = re.compile(r'^--\s+SOLUTION$')
_SOLUTION_CLOSE_RE = re.compile(r'^--\s+/SOLUTION$')
_AUTHOR_RE = re.compile(r'^-- (BCP|JC|MWH|CGH|RAB)[: ](.*)$')


def tokenize(text: str):
    """Convert source text to a flat list of (kind, content) tokens.

    Token kinds:
      block_comment_label  – /- identifier -/ (stripped; acts as separator)
      block_comment_prose  – /- prose text -/
      block_comment_header – /- ## Section Title -/
      code_line            – one line of Lean code
      blank                – empty or whitespace-only line
      full_open / full_close
      terse_inline(text) / slidebreak
      exercise_open(rating, name) / exercise_close
      grade_theorem / instructor / solution_open / solution_close
      author_comment(author, text)
    """
    lines = text.splitlines()
    tokens = []
    i = 0
    n = len(lines)

    while i < n:
        line = lines[i]
        stripped = line.strip()

        # --- Blank line ---
        if stripped == '':
            tokens.append(('blank', None))
            i += 1
            continue

        # --- Block comment /- ... -/ ---
        # Only treat as prose when /- starts at column 0.  Indented /- (inside
        # theorem proofs) is left as a code line so proofs stay intact.
        # Must not be /-- (docstring) or /-! (module docstring)
        m_start = re.match(r'^/-(?![-!])', line)
        if m_start:
            # Single-line? /- ... -/  (already know line starts with /-)
            m_single = re.match(r'^/-(.*?)-/\s*$', line)
            if m_single:
                body = m_single.group(1).strip()
                hdr = _parse_section_header(body)
                if hdr:
                    tokens.append(('block_comment_header', hdr))
                elif _is_label_comment(body):
                    tokens.append(('block_comment_label', body))
                else:
                    tokens.append(('block_comment_prose', body))
                i += 1
                continue

            # Multi-line: collect until -/
            raw = [line]
            i += 1
            while i < n and '-/' not in lines[i]:
                raw.append(lines[i])
                i += 1
            if i < n:
                raw.append(lines[i])
                i += 1
            body = _extract_comment_text(raw)
            hdr = _parse_section_header(body)
            if hdr:
                tokens.append(('block_comment_header', hdr))
            elif _is_label_comment(body):
                tokens.append(('block_comment_label', body))
            elif not body.strip():
                tokens.append(('blank', None))
            else:
                tokens.append(('block_comment_prose', body))
            continue

        # --- Structural markers (check stripped) ---

        if _INSTRUCTOR_RE.match(stripped):
            i += 1
            while i < n and _INSTRUCTOR_CONT_RE.match(lines[i]):
                i += 1
            tokens.append(('instructor', None))
            continue

        if _FULL_OPEN_RE.match(stripped):
            tokens.append(('full_open', None))
            i += 1
            continue

        if _FULL_CLOSE_RE.match(stripped):
            tokens.append(('full_close', None))
            i += 1
            continue

        if _SLIDEBREAK_RE.match(stripped):
            tokens.append(('slidebreak', None))
            i += 1
            continue

        m = _TERSE_DELIM_RE.match(stripped)
        if m:
            tokens.append(('terse_inline', m.group(1).strip()))
            i += 1
            continue

        m = _TERSE_PLAIN_RE.match(stripped)
        if m:
            tokens.append(('terse_inline', m.group(1).strip()))
            i += 1
            continue

        m = _EX_RE.match(stripped)
        if m:
            tokens.append(('exercise_open', (int(m.group(1)), m.group(2))))
            i += 1
            continue

        if _EX_CLOSE_RE.match(stripped):
            tokens.append(('exercise_close', None))
            i += 1
            continue

        if _GRADE_RE.match(stripped):
            tokens.append(('grade_theorem', None))
            i += 1
            continue

        if _SOLUTION_OPEN_RE.match(stripped):
            tokens.append(('solution_open', None))
            i += 1
            continue

        if _SOLUTION_CLOSE_RE.match(stripped):
            tokens.append(('solution_close', None))
            i += 1
            continue

        m = _AUTHOR_RE.match(stripped)
        if m:
            author = m.group(1)
            text_lines = [m.group(2).lstrip(': ').strip()]
            i += 1
            # Consume continuation lines (standalone -- ... not matching any marker)
            while i < n:
                cont = lines[i].strip()
                if (cont.startswith('--') and
                        not any(p.match(cont) for p in [
                            _FULL_OPEN_RE, _FULL_CLOSE_RE, _SLIDEBREAK_RE,
                            _TERSE_DELIM_RE, _TERSE_PLAIN_RE,
                            _INSTRUCTOR_RE, _EX_RE, _EX_CLOSE_RE,
                            _GRADE_RE, _SOLUTION_OPEN_RE, _SOLUTION_CLOSE_RE,
                            _AUTHOR_RE]) and
                        cont != '--'):
                    text_lines.append(cont[2:].lstrip())
                    i += 1
                else:
                    break
            tokens.append(('author_comment', (author, '\n'.join(text_lines))))
            continue

        # --- Default: code line ---
        tokens.append(('code_line', line))
        i += 1

    return tokens

# ---------------------------------------------------------------------------
# Renderer
# ---------------------------------------------------------------------------

class Renderer:
    """Convert a token stream to a Verso document body."""

    def __init__(self):
        self.parts = []       # completed output pieces
        self.code_buf = []    # lines awaiting code block flush
        self.full_depth = 0
        self.pending_full = False   # :::full has NOT been opened yet for current FULL block
        self.in_exercise = False
        self.in_solution = False    # inside -- SOLUTION / -- /SOLUTION (suppress output)

    # --- Output helpers ---

    def _append(self, s: str):
        if s:
            self.parts.append(s)

    def _flush_code(self):
        if not self.code_buf:
            return
        # Drop trailing blank lines from code buffer
        buf = list(self.code_buf)
        while buf and not buf[-1].strip():
            buf.pop()
        if buf:
            # Verso's InlineLean can't elaborate comment-only blocks — skip them.
            has_command = any(
                l.strip() and not l.strip().startswith('--')
                for l in buf
            )
            if has_command:
                self._append('```lean\n' + '\n'.join(buf) + '\n```\n\n')
        self.code_buf = []

    def _open_full_if_pending(self):
        """Emit :::full if pending and we are not inside an exercise."""
        if self.pending_full and not self.in_exercise:
            self._append(':::full\n\n')
            self.pending_full = False

    # --- Token handlers ---

    def _on_blank(self):
        # A blank line ends the current code accumulation
        self._flush_code()

    def _on_block_comment_label(self):
        # Label comment acts as code-block separator; emit nothing
        self._flush_code()

    def _on_block_comment_prose(self, text):
        self._flush_code()
        self._open_full_if_pending()
        self._append(text + '\n\n')

    def _on_block_comment_header(self, hdr):
        level, title = hdr
        self._flush_code()
        # Headers always go at document level — Verso doesn't support
        # headings nested inside block directives like :::full.
        if self.pending_full:
            # Keep pending_full=True so the NEXT prose/code opens :::full.
            # The header itself goes at document level (no :::full wrapper).
            pass
        elif self.full_depth > 0 and not self.in_exercise:
            # We're inside an open :::full; close it, emit the header at
            # document level, and re-arm pending_full for subsequent content.
            self._append(':::\n\n')
            self.pending_full = True
        self._append('#' * level + ' ' + title + '\n\n')

    def _on_code_line(self, line):
        self._open_full_if_pending()
        self.code_buf.append(line)

    def _on_full_open(self):
        self._flush_code()
        self.full_depth += 1
        # Don't open a :::full directive if we're already inside an exercise
        if not self.in_exercise:
            self.pending_full = True

    def _on_full_close(self):
        self._flush_code()
        # A :::full is currently open iff full_depth > 0 AND NOT pending_full
        # AND NOT in_exercise.  Suppress the closing ::: in all other cases.
        suppress = self.pending_full or self.in_exercise
        self.pending_full = False
        self.full_depth = max(0, self.full_depth - 1)
        if not suppress:
            self._append(':::\n\n')

    def _on_exercise_open(self, rating, name):
        self._flush_code()
        # Exercises cannot be nested inside :::full.  If a :::full is currently
        # open (full_depth > 0, pending_full=False), close it first and re-arm
        # pending_full so that any content after the exercise (before -- /FULL)
        # opens a new :::full.  If pending_full is still True (no :::full was
        # opened yet), leave it True — _open_full_if_pending won't fire inside
        # an exercise, so the :::full is still deferred.
        if self.full_depth > 0 and not self.pending_full and not self.in_exercise:
            self._append(':::\n\n')
            self.pending_full = True
        self.in_exercise = True
        self._append(f':::exercise (rating := {rating}) (name := "{name}")\n\n')

    def _on_exercise_close(self):
        self._flush_code()
        self.in_exercise = False
        self._append(':::\n\n')

    def _on_slidebreak(self):
        self._flush_code()
        self._append(':::slidebreak\n:::\n\n')

    def _on_terse_inline(self, text):
        self._flush_code()
        self._append(f':::terse\n{text}\n:::\n\n')

    def _on_author_comment(self):
        # Author/editor notes (BCP, JC, etc.) are stripped from the Verso output;
        # they live in the source Basics.lean.
        self._flush_code()  # still acts as a code-block separator

    def _on_solution_open(self):
        self._flush_code()
        self.in_solution = True

    def _on_solution_close(self):
        self._flush_code()
        self.in_solution = False

    # --- Main dispatch ---

    def process(self, tokens):
        for kind, content in tokens:
            if kind == 'solution_open':
                self._on_solution_open()
                continue
            elif kind == 'solution_close':
                self._on_solution_close()
                continue
            if self.in_solution:
                continue  # suppress everything between SOLUTION markers
            if kind == 'blank':
                self._on_blank()
            elif kind == 'block_comment_label':
                self._on_block_comment_label()
            elif kind == 'block_comment_prose':
                self._on_block_comment_prose(content)
            elif kind == 'block_comment_header':
                self._on_block_comment_header(content)
            elif kind == 'code_line':
                self._on_code_line(content)
            elif kind == 'full_open':
                self._on_full_open()
            elif kind == 'full_close':
                self._on_full_close()
            elif kind == 'exercise_open':
                rating, name = content
                self._on_exercise_open(rating, name)
            elif kind == 'exercise_close':
                self._on_exercise_close()
            elif kind == 'slidebreak':
                self._on_slidebreak()
            elif kind == 'terse_inline':
                self._on_terse_inline(content)
            elif kind == 'author_comment':
                self._on_author_comment()
            elif kind in ('instructor', 'grade_theorem'):
                pass  # strip
            # else: unknown token — ignore

        # Flush any trailing code
        self._flush_code()

        # Close any unclosed blocks (shouldn't happen in well-formed source)
        if self.in_exercise:
            self._append(':::\n\n')  # close unclosed exercise
        if self.full_depth > 0 and not self.pending_full and not self.in_exercise:
            self._append(':::\n\n')  # close unclosed full block

    def result(self) -> str:
        return ''.join(self.parts)

# ---------------------------------------------------------------------------
# Top-level converter
# ---------------------------------------------------------------------------

def convert(src_text: str, title: str, file_key: str) -> str:
    """Return a Verso document converted from the code-forward *src_text*."""
    header = HEADER_TEMPLATE.format(title=title, file=file_key)
    # The opening /- title -/ comment is already used for the #doc declaration;
    # strip it so it doesn't appear again as prose.
    body_src = _strip_title_comment(src_text)
    tokens = tokenize(body_src)
    renderer = Renderer()
    renderer.process(tokens)
    body = renderer.result()
    return header + body + FOOTER

# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('src', metavar='SOURCE.lean',
                        help='code-forward chapter source (e.g. LF/Basics.lean)')
    parser.add_argument('dst', metavar='DEST.lean', nargs='?',
                        help="output Verso file (default: same dir, stem + 'Verso')")
    parser.add_argument('--title', default=None,
                        help='override the #doc title (auto-detected by default)')
    args = parser.parse_args()

    src_path = pathlib.Path(args.src)
    if not src_path.exists():
        sys.exit(f'Error: source file not found: {src_path}')

    dst_path = (pathlib.Path(args.dst) if args.dst
                else src_path.with_stem(src_path.stem + 'Verso'))

    src_text = src_path.read_text()
    title = args.title or extract_title(src_text)
    file_key = src_path.stem   # e.g. "Basics"

    result = convert(src_text, title, file_key)
    dst_path.write_text(result)
    print(f'Written {dst_path}  (title: {title!r}, file key: {file_key!r})')


if __name__ == '__main__':
    main()
