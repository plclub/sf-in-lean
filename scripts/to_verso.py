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
import SFLMeta.Hide
import SFLMeta.Instructors
import SFLMeta.SlideBreak
import SFLMeta.Solution
import SFLMeta.Terse

open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "{title}" =>
%%%
htmlSplit := .never
file := "{file}"
%%%

"""

FOOTER = ""

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
            bool(re.match(r'^(BCP|JC|MWH|CGH|RAB|TODO)[: ]', t)))

_SEPARATOR_LINE_RE = re.compile(r'^\s*#{4,}\s*$')   # ######... divider lines
_HEADING_LINE_RE = re.compile(r'^\s{0,3}(#{1,6})\s+(.+)$')
_DEV_NOTE_RE = re.compile(r'^\s*-- (BCP|JC|MWH|CGH|RAB|TODO)\b')
_DEV_NOTE_CONT_RE = re.compile(r'^\s*--')


def _strip_dev_note_lines(text: str) -> str:
    """Remove author/editor note lines (`-- BCP: ...`, `-- TODO ...`) embedded
    inside block-comment prose, along with their `--` continuation lines."""
    out = []
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        if _DEV_NOTE_RE.match(lines[i]):
            i += 1
            while i < len(lines) and _DEV_NOTE_CONT_RE.match(lines[i]):
                i += 1
        else:
            out.append(lines[i])
            i += 1
    return '\n'.join(out)


def _md_bold_to_verso(text: str) -> str:
    """Translate Markdown `**bold**` to Verso `*bold*` (Verso uses a single
    `*` for bold and `_` for emphasis; doubled stars trip its markup linter)."""
    return re.sub(r'\*\*([^*\n]+)\*\*', r'*\1*', text)


def _comment_tokens(body: str):
    """Split a block-comment body into header and prose tokens.

    A comment may contain several `## Title` heading lines with prose between
    them; each heading becomes a block_comment_header token and each prose run
    becomes a block_comment_prose token (the old code kept only the first
    heading and silently dropped everything after it).  `####...` divider
    lines and embedded dev notes are stripped.
    """
    body = _strip_dev_note_lines(body)
    lines = [l for l in body.splitlines() if not _SEPARATOR_LINE_RE.match(l)]
    tokens = []
    prose = []

    def flush_prose():
        seg = list(prose)
        while seg and not seg[0].strip():
            seg.pop(0)
        while seg and not seg[-1].strip():
            seg.pop()
        if seg:
            tokens.append(('block_comment_prose',
                           _md_bold_to_verso('\n'.join(seg))))
        prose.clear()

    for l in lines:
        m = _HEADING_LINE_RE.match(l)
        if m:
            flush_prose()
            tokens.append(('block_comment_header',
                           (len(m.group(1)), m.group(2).strip())))
        else:
            prose.append(l)
    flush_prose()
    return tokens if tokens else [('blank', None)]

def _scan_block_comment(lines, i):
    """Collect a block comment starting at lines[i] (whose first `/-` opens it),
    tracking `/- ... -/` nesting.  Returns (raw_lines, next_index)."""
    raw = []
    depth = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        j = 0
        while j < len(line) - 1:
            if line.startswith('/-', j):
                depth += 1
                j += 2
            elif line.startswith('-/', j):
                depth -= 1
                j += 2
                if depth == 0:
                    break
            else:
                j += 1
        raw.append(line)
        i += 1
        if depth <= 0:
            break
    return raw, i


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
_HIDE_OPEN_RE = re.compile(r'^-- HIDE$')
_HIDE_CLOSE_RE = re.compile(r'^-- /HIDE$')
_SOL_OPEN_RE = re.compile(r'^--\s+SOLUTION$')
_SOL_CLOSE_RE = re.compile(r'^--\s+/SOLUTION$')
# Author-only / developer comment markers.  These are swept into :::dev blocks
# (discarded from generated outputs, preserved verbatim in the Verso source).
# Add new author initials or task keywords here.  NB: INSTRUCTORS is handled
# separately (-> :::instructor); TERSE/FULL have their own dedicated markers.
_AUTHOR_RE = re.compile(
    r'^-- (BCP|JC|MWH|CGH|RAB|CH|NB|TODO|TOFIX|LATER|SOONER)[: (](.*)$')


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
      grade_theorem / instructor
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
        # Must not be /-- (docstring) or /-! (module docstring).
        # A comment that directly continues a code run (an indented /- with a
        # code line right before it, e.g. commentary between tactics inside a
        # proof) is kept as code so the proof stays intact.  Any other comment
        # -- including indented but standalone ones -- becomes prose.
        m_start = re.match(r'^\s*/-(?![-!])', line)
        if m_start:
            raw, i = _scan_block_comment(lines, i)
            indented = bool(re.match(r'^\s', line))
            prev_kind = tokens[-1][0] if tokens else None
            if indented and prev_kind == 'code_line':
                # Part of a code run: emit verbatim (blank lines inside the
                # comment stay code lines, so the run is not split).
                for l in raw:
                    tokens.append(('code_line', l))
                continue
            body = _extract_comment_text(raw)
            if _is_label_comment(body):
                tokens.append(('block_comment_label', body))
            elif not body.strip():
                tokens.append(('blank', None))
            else:
                tokens.extend(_comment_tokens(body))
            continue

        # --- Structural markers (check stripped) ---

        if _INSTRUCTOR_RE.match(stripped):
            # Drop the '-- INSTRUCTORS:' marker; the :::instructors directive
            # already conveys what the block is.  Keep the trailing text.
            first = re.sub(r'^INSTRUCTORS:\s*', '', stripped[2:].strip())
            body_lines = [first] if first else []
            i += 1
            while i < n and _INSTRUCTOR_CONT_RE.match(lines[i]):
                body_lines.append(lines[i].strip()[2:].strip())
                i += 1
            tokens.append(('instructor', '\n'.join(body_lines)))
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

        if _HIDE_OPEN_RE.match(stripped):
            # Capture the whole -- HIDE ... -- /HIDE region verbatim.  Hidden
            # content is often deliberately broken/admitted, so it must never be
            # elaborated; it is emitted as an opaque :::hide block (discarded at
            # elaboration, preserved textually in the source).
            i += 1
            raw = []
            while i < n and not _HIDE_CLOSE_RE.match(lines[i].strip()):
                raw.append(lines[i])
                i += 1
            if i < n:
                i += 1   # skip the closing -- /HIDE
            while raw and not raw[0].strip():
                raw.pop(0)
            while raw and not raw[-1].strip():
                raw.pop()
            tokens.append(('hide', '\n'.join(raw)))
            continue

        if _SOL_OPEN_RE.match(stripped):
            # -- SOLUTION ... -- /SOLUTION.  Two flavours:
            #  * compilable code  -> keep as a code block wrapped in the textual
            #    `-- SOLUTION`/`-- END SOLUTION` markers SFLMeta understands
            #    (student -> `-- FILL IN HERE`, teacher -> body kept & typechecked).
            #  * prose / non-compiling illustration -> a :::solution block (shown
            #    only in the solutions build; can't be a code block since a
            #    comment-only `lean` block fails to elaborate).
            i += 1
            body = []
            while i < n and not _SOL_CLOSE_RE.match(lines[i].strip()):
                body.append(lines[i]); i += 1
            if i < n:
                i += 1   # skip the closing -- /SOLUTION
            if _strip_lean_comments('\n'.join(body)).strip():
                tokens.append(('code_line', '-- SOLUTION'))
                for bl in body:
                    tokens.append(('code_line', bl))
                tokens.append(('code_line', '-- END SOLUTION'))
            else:
                while body and not body[0].strip():
                    body.pop(0)
                while body and not body[-1].strip():
                    body.pop()
                if body and body[0].lstrip().startswith('/-'):
                    prose = _extract_comment_text(body)
                else:
                    prose = '\n'.join(body)
                tokens.append(('solution_prose', prose))
            continue

        m = _AUTHOR_RE.match(stripped)
        if m:
            # Preserve the original marker + text verbatim (e.g. 'BCP: ...',
            # 'TODO Claude: ...') so the :::dev block keeps the authorship cue.
            body_lines = [stripped[2:].strip()]   # drop '--', keep 'BCP: ...'
            i += 1
            # Consume continuation lines (standalone -- ... not matching any marker)
            while i < n:
                cont = lines[i].strip()
                if (cont.startswith('--') and
                        not any(p.match(cont) for p in [
                            _FULL_OPEN_RE, _FULL_CLOSE_RE, _SLIDEBREAK_RE,
                            _TERSE_DELIM_RE, _TERSE_PLAIN_RE,
                            _INSTRUCTOR_RE, _EX_RE, _EX_CLOSE_RE,
                            _GRADE_RE, _AUTHOR_RE]) and
                        cont != '--'):
                    body_lines.append(cont[2:].lstrip())
                    i += 1
                else:
                    break
            tokens.append(('author_comment', '\n'.join(body_lines)))
            continue

        # --- Default: code line ---
        tokens.append(('code_line', line))
        i += 1

    return tokens

def _strip_lean_comments(text: str) -> str:
    """Return *text* with `--` line comments and (nested) `/- ... -/` block
    comments removed; used to detect code blocks that contain no real code."""
    out = []
    depth = 0
    j = 0
    while j < len(text):
        if text.startswith('/-', j):
            depth += 1
            j += 2
        elif text.startswith('-/', j) and depth > 0:
            depth -= 1
            j += 2
        elif depth == 0 and text.startswith('--', j):
            nl = text.find('\n', j)
            j = len(text) if nl == -1 else nl
        else:
            if depth == 0:
                out.append(text[j])
            j += 1
    return ''.join(out)


# ---------------------------------------------------------------------------
# Renderer
# ---------------------------------------------------------------------------

# Container directives (:::exercise, :::full) may hold leaf directives such as
# :::dev / :::instructor / :::terse.  Verso requires an outer directive's fence
# to be strictly longer than any directive nested inside it, so containers use a
# 4-colon fence while leaves use the usual 3.
_CONTAINER_FENCE = '::::'


def _verbatim_block(text: str) -> str:
    """Wrap *text* in a fenced code block so arbitrary author prose (which may
    contain `*`, `_`, `:::`, backticks, ...) can never derail Verso's directive
    parser.  The fence is grown to outrun any backtick run inside *text*."""
    longest = max((len(m) for m in re.findall(r'`+', text)), default=0)
    fence = '`' * max(3, longest + 1)
    return fence + '\n' + text + '\n' + fence


class Renderer:
    """Convert a token stream to a Verso document body."""

    def __init__(self):
        self.parts = []       # completed output pieces
        self.code_buf = []    # lines awaiting code block flush
        self.full_depth = 0         # source-level FULL marker nesting
        self.pending_full = False   # :::full requested but not yet emitted
        self.full_open = False      # an emitted :::full is currently unclosed
        self.in_exercise = False

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
        # Verso's InlineLean can't elaborate comment-only blocks — skip any
        # buffer that contains no actual code once `--` line comments and
        # (possibly nested) /- ... -/ block comments are removed.
        if buf and _strip_lean_comments('\n'.join(buf)).strip():
            self._append('```lean\n' + '\n'.join(buf) + '\n```\n\n')
        self.code_buf = []

    def _open_full_if_pending(self):
        """Emit :::full if pending and we are not inside an exercise."""
        if self.pending_full and not self.in_exercise:
            self._append(_CONTAINER_FENCE + 'full\n\n')
            self.pending_full = False
            self.full_open = True

    def _close_full_if_open(self):
        """Emit ::: if an emitted :::full is currently unclosed.

        Tracking the emitted-but-unclosed state explicitly (rather than
        deriving it from marker depth) keeps the output's :::full / :::
        balanced even when the source's -- FULL / -- /FULL markers are not."""
        if self.full_open:
            self._append(_CONTAINER_FENCE + '\n\n')
            self.full_open = False

    # --- Token handlers ---

    def _on_blank(self):
        # A blank line no longer flushes the code buffer.  If we are
        # accumulating code, the blank is kept *inside* the buffer so that
        # consecutive code runs separated only by blank lines merge into a
        # single ```lean block (consecutive runs of blanks collapse to one).
        # Non-code tokens still end the block: their handlers call _flush_code,
        # so blocks break at prose, directives, headers, and label comments.
        # Trailing blanks are dropped when the buffer is flushed.
        if self.code_buf and self.code_buf[-1].strip():
            self.code_buf.append('')

    def _on_block_comment_label(self):
        # Label comments (/- ident -/) render as nothing and no longer break the
        # code block, so code groups separated only by labels (or blanks) merge
        # into a single ```lean block.  Prose, headers, and directives still
        # flush, so blocks break at every meaningful boundary.
        pass

    def _on_block_comment_prose(self, text):
        self._flush_code()
        self._open_full_if_pending()
        self._append(text + '\n\n')

    def _on_block_comment_header(self, hdr):
        level, title = hdr
        self._flush_code()
        # Headers always go at document level — Verso doesn't support
        # headings nested inside block directives like :::full.  If a
        # :::full is currently open, close it and re-arm pending_full so
        # subsequent content opens a fresh one.
        if self.full_open and not self.in_exercise:
            self._close_full_if_open()
            self.pending_full = True
        self._append('#' * level + ' ' + title + '\n\n')

    def _on_code_line(self, line):
        # Code is treated like prose with respect to :::full — it stays inside
        # the directive.  NB: the terse build drops :::full content wholesale,
        # so definitions that later (terse-visible) code depends on must sit
        # outside -- FULL regions in the source.
        self._open_full_if_pending()
        self.code_buf.append(line)

    def _on_full_open(self):
        self._flush_code()
        self.full_depth += 1
        # Don't open a :::full directive if we're already inside an exercise
        # or one is already open (stray double -- FULL in the source).
        if not self.in_exercise and not self.full_open:
            self.pending_full = True

    def _on_full_close(self):
        self._flush_code()
        self.full_depth = max(0, self.full_depth - 1)
        if self.full_depth == 0:
            # Outermost close: drop any deferred open and close the emitted
            # :::full if there is one (a stray -- /FULL emits nothing).
            self.pending_full = False
            if not self.in_exercise:
                self._close_full_if_open()

    def _on_exercise_open(self, rating, name):
        self._flush_code()
        # Exercises cannot be nested inside :::full.  If a :::full is
        # currently open, close it first and re-arm pending_full so that any
        # content after the exercise (before -- /FULL) opens a new :::full.
        # If pending_full is still True (no :::full was opened yet), leave it
        # True — _open_full_if_pending won't fire inside an exercise, so the
        # :::full is still deferred.
        if self.full_open and not self.in_exercise:
            self._close_full_if_open()
            self.pending_full = True
        self.in_exercise = True
        self._append(
            f'{_CONTAINER_FENCE}exercise (rating := {rating}) (name := "{name}")\n\n')

    def _on_exercise_close(self):
        self._flush_code()
        self.in_exercise = False
        self._append(_CONTAINER_FENCE + '\n\n')

    def _on_slidebreak(self):
        self._flush_code()
        self._append(':::slidebreak\n:::\n\n')

    def _on_terse_inline(self, text):
        self._flush_code()
        self._append(f':::terse\n{text}\n:::\n\n')

    def _on_hide(self, text):
        # -- HIDE / -- /HIDE regions become :::hide blocks, processed identically
        # to :::dev / :::instructor (body dropped at elaboration, preserved
        # verbatim in the source).  Emitted as a 4-colon container wrapping a
        # verbatim code fence, so its arbitrary content is never elaborated and
        # can't perturb the parser.
        self._flush_code()
        if not text.strip():
            return  # empty hide region: emit nothing
        # A :::hide cannot nest inside an emitted :::full (same fence width):
        # close the full first and re-arm it so content after the hide reopens.
        if self.full_open and not self.in_exercise:
            self._close_full_if_open()
            self.pending_full = True
        self._append(_CONTAINER_FENCE + 'hide\n' + _verbatim_block(text)
                     + '\n' + _CONTAINER_FENCE + '\n\n')

    def _on_solution_prose(self, text):
        # Prose / non-compiling solution -> :::solution block, shown only in the
        # solutions build (SFLMeta.Block.solution).  Body is verbatim-fenced so
        # arbitrary illustrative code can't perturb the parser.
        self._flush_code()
        if not text.strip():
            return
        self._append(':::solution\n' + _verbatim_block(text) + '\n:::\n\n')

    def _emit_noop_directive(self, directive, text):
        # Author notes become noop annotation directives (:::dev / :::instructors).
        # The text is preserved in the Verso source, but the directive discards
        # its body so it never reaches the generated outputs.  :::dev and
        # :::instructors are processed identically (see SFLMeta); they differ only
        # in name so instructor notes can be treated differently later.
        #
        # NB: the body is emitted *unfenced*, so it is parsed as Verso markup.
        # Author comments must therefore avoid raw Verso specials (unbalanced
        # `*`, `[...]`, stray backticks, a leading `#`); offending text breaks the
        # build at parse time.  (:::hide keeps a verbatim fence -- see _on_hide --
        # because it wraps raw code, not prose.)
        self._flush_code()  # still acts as a code-block separator
        self._append(f':::{directive}\n' + text + '\n:::\n\n')

    # --- Main dispatch ---

    def process(self, tokens):
        for kind, content in tokens:
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
                self._emit_noop_directive('dev', content)
            elif kind == 'instructor':
                self._emit_noop_directive('instructors', content)
            elif kind == 'hide':
                self._on_hide(content)
            elif kind == 'solution_prose':
                self._on_solution_prose(content)
            elif kind == 'grade_theorem':
                pass  # strip
            # else: unknown token — ignore

        # Flush any trailing code
        self._flush_code()

        # Close any unclosed blocks (shouldn't happen in well-formed source)
        if self.in_exercise:
            self._append(_CONTAINER_FENCE + '\n\n')  # close unclosed exercise
            self.in_exercise = False
        self._close_full_if_open()

    def result(self) -> str:
        return ''.join(self.parts)

# ---------------------------------------------------------------------------
# Post-processing
# ---------------------------------------------------------------------------

def _strip_directive_blanks(text: str) -> str:
    """Remove blank lines immediately after :::foo opening lines and
    immediately before standalone ::: closing lines."""
    # Blank line(s) after an *opening* :::name line (3 or more colons).  The
    # char after the colons must be a directive-name char (non-colon,
    # non-space) so this does not match a bare closing line like `::::`, whose
    # extra colons would otherwise satisfy a looser pattern and get its trailing
    # blank lines (wrongly) stripped.
    text = re.sub(r'(:::+[^\s:][^\n]*)\n\n+', r'\1\n', text)
    # Blank line(s) before a standalone ::: closing line (3 or more colons)
    text = re.sub(r'\n\n+(:::+[ \t]*\n)', r'\n\1', text)
    return text

# ---------------------------------------------------------------------------
# Solution-marker conversion (code-forward source -> Verso code-block forms)
# ---------------------------------------------------------------------------

def _indent_of(line: str) -> str:
    return line[:len(line) - len(line.lstrip())]


def _convert_solution_markers(src: str) -> str:
    """Translate the code-forward solution markers into the in-code-block forms
    that SFLMeta understands, so the student and solutions builds diverge.  In
    every case the teacher build keeps the author's solution (and typechecks it
    during the book build); the student build replaces it with `sorry` /
    `-- FILL IN HERE`.

      def f … : T            ->   def f … : T
        -- ADMITDEF                 := solution!(<body>)
        := <body>
        -- /ADMITDEF

      <inside `by`>           ->   solution!
        -- ADMITTED                   <tactics, reindented one level deeper>
        <tactics>
        -- /ADMITTED

      expr := <proof>  -- ADMITTED   ->   expr := solution!(<proof>)

    (`-- SOLUTION … -- /SOLUTION` blocks are handled in the tokenizer, which
    splits compilable answers from prose ones.)
    """
    lines = src.split('\n')
    out = []
    i, n = 0, len(lines)
    while i < n:
        line = lines[i]
        s = line.strip()

        # --- ADMITDEF: wrap the definition body (`:= …`) in solution!(…) ---
        if s == '-- ADMITDEF':
            j = i + 1
            body = []
            while j < n and lines[j].strip() != '-- /ADMITDEF':
                body.append(lines[j]); j += 1
            if body:
                m = re.match(r'^(\s*:=\s*)(.*)$', body[0])
                if m:
                    body[0] = m.group(1) + 'solution!(' + m.group(2)
                    body[-1] = body[-1] + ')'
                out.extend(body)
            i = j + 1
            continue

        # --- ADMITTED block: a tactic sequence inside a `by` ---
        if s == '-- ADMITTED':
            indent = _indent_of(line)
            j = i + 1
            body = []
            while j < n and lines[j].strip() != '-- /ADMITTED':
                body.append(lines[j]); j += 1
            out.append(indent + 'solution!')
            for bl in body:
                # tacticSeqIndentGt: body must sit deeper than `solution!`.
                out.append(('  ' + bl) if bl.strip() else bl)
            i = j + 1
            continue

        # --- trailing ADMITTED: a one-line proof term ---
        if s.endswith('-- ADMITTED') and s != '-- ADMITTED':
            out.append(re.sub(r':=\s*(.*?)\s*--\s*ADMITTED\s*$',
                              lambda m: ':= solution!(' + m.group(1) + ')', line))
            i += 1
            continue

        out.append(line)
        i += 1
    return '\n'.join(out)


# ---------------------------------------------------------------------------
# Top-level converter
# ---------------------------------------------------------------------------

def convert(src_text: str, title: str, file_key: str) -> str:
    """Return a Verso document converted from the code-forward *src_text*."""
    header = HEADER_TEMPLATE.format(title=title, file=file_key)
    # The opening /- title -/ comment is already used for the #doc declaration;
    # strip it so it doesn't appear again as prose.
    body_src = _strip_title_comment(src_text)
    # Rewrite solution markers (ADMITDEF/ADMITTED/SOLUTION) into the in-code
    # forms SFLMeta understands before tokenizing.
    body_src = _convert_solution_markers(body_src)
    tokens = tokenize(body_src)
    renderer = Renderer()
    renderer.process(tokens)
    body = _strip_directive_blanks(renderer.result())
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
