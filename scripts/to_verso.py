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
import textwrap

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
import SFLMeta.Grade
import SFLMeta.Hide
import SFLMeta.Instructors
import SFLMeta.Quiz
import SFLMeta.SlideBreak
import SFLMeta.Solution
import SFLMeta.Terse
{extra_imports}
open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "{title}" =>
%%%
tag := "{file}"
htmlSplit := .never
file := some "{file}"
%%%

"""

FOOTER = ""

# ---------------------------------------------------------------------------
# Title extraction
# ---------------------------------------------------------------------------

def _find_title_comment(src: str, stem: str = None):
    """Locate the chapter-title comment and return (title, match) or None.

    Chapter titles follow the convention `<Stem>: <description>` (e.g.
    `Tactics: More Basic Tactics`) and are written either as a line comment
    (`-- Tactics: …`, Tactics) or a block comment (`/- Lists: … -/`, most
    chapters).  When *stem* is known, prefer the first comment of either form
    whose text starts with `<stem>:` — this skips leading non-title comments
    (Lists opens with a stray `-- Note that …`; Tactics opens with a multi-line
    `/- TODO: … -/` note that used to be mistaken for the title).  Without a
    stem (or when nothing matches), fall back to the first block comment."""
    if stem:
        m_line = re.search(rf'(?m)^--[ \t]*({re.escape(stem)}:[^\n]*)$', src)
        m_block = re.search(rf'/\-\s*({re.escape(stem)}:.*?)-/', src, re.DOTALL)
        # Prefer whichever title-form appears first in the file.
        cands = [m for m in (m_line, m_block) if m]
        if cands:
            m = min(cands, key=lambda m: m.start())
            title = ' '.join(m.group(1).split())
            return title, m
    m = re.search(r"/\-(.*?)-/", src, re.DOTALL)
    if m:
        lines = [l.strip() for l in m.group(1).splitlines() if l.strip()]
        if lines:
            title = lines[0].lstrip("#").strip()
            if title:
                return title, m
    return None


def extract_title(src: str, stem: str = None) -> str:
    """Pull the chapter title from its title comment (see _find_title_comment)."""
    found = _find_title_comment(src, stem)
    return found[0] if found else "Chapter"

# ---------------------------------------------------------------------------
# Tokenizer helpers
# ---------------------------------------------------------------------------

def _strip_title_comment(src: str, stem: str = None) -> str:
    """Remove the title comment (already used for the #doc title) so it doesn't
    render again as prose.  Uses the same lookup as `extract_title`, so exactly
    the comment that supplied the title is removed — whether the `-- <Stem>: …`
    line form or the `/- <Stem>: … -/` block form."""
    found = _find_title_comment(src, stem)
    if not found:
        return src
    m = found[1]
    return src[:m.start()] + src[m.end():]


# LF modules that are authored directly in Verso (Basics) or are plain Lean
# support modules (CustomTactics): an `import LF.X` of one of these passes
# through unchanged.  Every *other* `import LF.X` refers to a generated chapter,
# so it is rewritten to `import LF.XVerso`.
DIRECT_LF_MODULES = {"Basics", "CustomTactics"}

_IMPORT_RE = re.compile(r'^import\s+(\S+)\s*$')

# Some chapters write structural markers in block-comment form (`/- EX2 (foo) -/`,
# `/- /TERSE -/`, `/- [] -/`) rather than line form (`-- EX2 (foo)`).  Only the
# line form is recognized downstream, so normalize a single-line `/- MARKER -/`
# to `-- MARKER`.  Plain `/- label -/` / `/- prose -/` comments are left alone.
_BLOCK_MARKER_RE = re.compile(
    r'/-[ \t]*('
    r'EX\d+[A-Za-z!?]*[ \t]+\(\w+\)'          # exercise open: EX2M? (name)
    r'|\[\]'                                   # exercise close
    r'|GRADE_\S[^\n]*?'                        # grading spec
    r'|/?(?:HIDEFROMADVANCED|HIDEFROMHTML|FULL|TERSE|HIDE|QUIZ|SOLUTION|INSTRUCTORS)'
    r')[ \t]*-/')


def _normalize_block_markers(src: str) -> str:
    return _BLOCK_MARKER_RE.sub(lambda m: '-- ' + m.group(1).rstrip(), src)


# Marker lines that can appear *inside* a multi-line comment body and should be
# dropped (their underscores/brackets/stars would otherwise break Verso markup).
# Region semantics (HIDEFROM*) are not honored yet — dropping the marker just
# lets the surrounding prose render.  FULL/TERSE are handled separately as modes.
# FOLD/-- /FOLD marks a proof region to render collapsed; folding is not
# honored yet, so like HIDEFROM* the markers are dropped and the content
# renders normally.
_DROP_MARKER_RE = re.compile(
    r'/?(?:HIDEFROMADVANCED|HIDEFROMHTML|HIDE|FOLD|ADMITTED|ADMITDEF)'
    r'|\[\]'
    r'|GRADE_\S.*')

# A `--` line comment whose whole content is a HIDEFROM* region marker.  Used
# to drop such markers on paths that bypass `_comment_tokens` (indented
# comments kept as code lines).  Deliberately narrower than _DROP_MARKER_RE:
# HIDE/FOLD/ADMITTED/ADMITDEF in code position carry meaning for other branches.
_HIDEFROM_COMMENT_RE = re.compile(r'--\s*/?(?:HIDEFROMHTML|HIDEFROMADVANCED)')


def _extract_imports(body: str):
    """Pull top-level `import …` lines and `prelude` out of *body* and return
    (has_prelude, import_lines, body_without_imports).

    These belong in the Verso header (real Lean file-level directives), not in
    a ```lean``` code block.  `prelude` must go *before* all imports in the
    generated file, just as in the source.  Because a chapter's InlineLean
    definitions are exported, importing a dependency makes its definitions
    visible to this chapter's code blocks."""
    has_prelude = False
    kept, imports = [], []
    for line in body.splitlines():
        if line.strip() == 'prelude':
            has_prelude = True
            continue  # lifted to the file header; not a body code line
        m = _IMPORT_RE.match(line)
        if m:
            mod = m.group(1)
            lf = re.match(r'LF\.(\w+)$', mod)
            if lf and lf.group(1) not in DIRECT_LF_MODULES:
                mod = f'LF.{lf.group(1)}Verso'
            imports.append(f'import {mod}')
        else:
            kept.append(line)
    return has_prelude, imports, '\n'.join(kept)

# Author/dev markers (matches the line-comment set in `_AUTHOR_RE`).  A block
# comment whose body opens with one of these is an author note routed to :::dev.
# `HIDE:` (colon required, to stay clear of the bare `-- HIDE` region marker)
# prefixes reviewer remarks like `/- HIDE: Robert Rand: … -/`; they are author-
# only content, kept in ```dev like the initialed notes.
_BLOCK_DEV_RE = re.compile(
    r'^(BCP|JC|MWH|CGH|RAB|CH|HG|NB|TODO|TOFIX|LATER|SOONER|HIDE(?=:))\b')


def _is_block_dev_comment(text: str) -> bool:
    """True when a `/- … -/` block comment is an author/dev note (e.g. `MWH: …`).
    These are routed to :::dev blocks (preserving every word), not dropped."""
    return bool(_BLOCK_DEV_RE.match(text.strip()))


def _is_label_comment(text: str) -> bool:
    """True when text (stripped comment body) should be stripped in Verso output.

    This covers:
      - Single identifiers like "test_nandb1" or "test_leb3'" (test-case labels)
      - Pure separator lines like "############################" (visual dividers)
      - Lean output annotations like "==> true : Bool" or "===> ..." (#check/#eval)
    These act as code-block separators but produce no visible Verso output.
    (Author/dev block notes are *not* labels — see `_is_block_dev_comment`.)
    """
    t = text.strip()
    return (bool(re.match(r"^[\w.']+$", t)) or
            bool(re.match(r'^#{3,}[ \t#-]*$', t)) or
            bool(re.match(r'^=+>', t)))

# ######... divider lines; tolerate trailing decoration (`###### --`, spaces)
_SEPARATOR_LINE_RE = re.compile(r'^\s*#{4,}[ \t#-]*$')
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


def _strip_coq_comment_markers(text: str) -> str:
    """Remove leftover Coq/coqdoc comment delimiters (`(**`, `(*`, `*)`) embedded
    in migrated prose.  Some chapters keep informal-proof prose in a Lean `/- … -/`
    block whose body still carries the original coqdoc `(** … *)` markers; the
    `/- -/` already delimits the comment, so the inner Coq markers are stray text
    that would otherwise leak (and the `*)` trips Verso's `*` bold parser)."""
    text = re.sub(r'\(\*+', '', text)   # (*  /  (**  comment openers
    text = re.sub(r'\*+\)', '', text)   # *)  /  **) comment closers
    return text


def _bullets_to_verso(text: str) -> str:
    """Convert `* item` bullet-list markers to `- item`.  Verso reads a
    line-initial `*` as the start of bold text (single-`*` bold), so a `*`
    bullet errors with "unexpected '*'"; `-` is an unambiguous list bullet.  A
    `***` slide break or `**bold**` (star not followed by a space) is untouched."""
    return re.sub(r'(?m)^([ \t]*)\*([ \t])', r'\1-\2', text)


def _md_bold_to_verso(text: str) -> str:
    """Translate Markdown `**bold**` to Verso `*bold*` (Verso uses a single
    `*` for bold and `_` for emphasis; doubled stars trip its markup linter)."""
    return re.sub(r'\*\*([^*\n]+)\*\*', r'*\1*', text)


# SF/Coq prose marks inline code with square brackets (`[add_comm]`); Verso reads
# `[…]` as a link reference, so convert it to a backtick code span.  A real
# Markdown link/reference (`[text](url)` or `[text][ref]`) is left alone.
_SF_INLINE_CODE_RE = re.compile(r'\[([^\]\n]+)\](?![(\[])')


def _sf_inline_code(text: str) -> str:
    # Convert `[…]` only *outside* existing backtick code spans, so brackets
    # already inside a span (e.g. `rw [add_succ]`) aren't turned into nested
    # backticks.
    out = []
    for p in re.split(r'(`[^`\n]*`)', text):
        if len(p) >= 2 and p.startswith('`') and p.endswith('`'):
            out.append(p)
            continue
        p = _SF_INLINE_CODE_RE.sub(lambda m: '`' + m.group(1) + '`', p)
        # Escape any brackets that survive conversion — empty `[]`, stray `[`/`]`
        # — which Verso would otherwise read as link syntax.  (This corpus has
        # no real `[text](url)` markdown links.)
        p = p.replace('[', '\\[').replace(']', '\\]')
        out.append(p)
    return ''.join(out)


def _latex_macros_to_verso(text: str) -> str:
    """Translate LaTeX macros to Verso markup.  `\\CHAP{Basics}` becomes a
    cross-chapter reference `{ref "Basics"}[Basics]` — the `ref` role resolves,
    at book-traverse time, to a link to the part tagged `"Basics"` (every chapter
    header now emits `tag := "<name>"`).  Any other `\\macro{arg}` is reduced to
    its argument text (Verso has no `\\macro` syntax).

    This runs *after* `_sf_inline_code` so the `[Basics]` link text it emits is
    not seen (and escaped/converted) by the `[…]`-inline-code pass."""
    text = re.sub(r'\\CHAP\{([^}]*)\}', r'{ref "\1"}[\1]', text)
    text = re.sub(r'\\[A-Za-z]+\{([^}]*)\}', r'\1', text)
    return text


def _prose_markup(text: str) -> str:
    """Apply the prose-level rewrites Verso needs (bold, SF inline code, and
    LaTeX-macro / cross-reference translation)."""
    return _latex_macros_to_verso(
        _sf_inline_code(_md_bold_to_verso(
            _bullets_to_verso(_strip_coq_comment_markers(text)))))


def _comment_tokens(body: str):
    """Split a block-comment body into header and prose tokens.

    A comment may contain several `## Title` heading lines with prose between
    them; each heading becomes a block_comment_header token and each prose run
    becomes a block_comment_prose token (the old code kept only the first
    heading and silently dropped everything after it).  `####...` divider
    lines and embedded dev notes are stripped.

    A line beginning `FULL:` or `TERSE:` switches the build mode for the lines
    that follow it (within the comment), wrapping that run in a ::::full /
    ::::terse region; the mode persists until the next prefix or the end of the
    comment.  This handles both whole-comment forms (`/- FULL: … -/`) and mixed
    comments that alternate full and terse prose line by line.
    """
    body = _strip_dev_note_lines(body)
    lines = [l for l in body.splitlines() if not _SEPARATOR_LINE_RE.match(l)]
    tokens = []
    prose = []
    mode = [None]   # None | 'FULL' | 'TERSE'

    def flush_prose():
        seg = list(prose)
        while seg and not seg[0].strip():
            seg.pop(0)
        while seg and not seg[-1].strip():
            seg.pop()
        if seg:
            tokens.append(('block_comment_prose',
                           _prose_markup('\n'.join(seg))))
        prose.clear()

    def set_mode(new):
        if new == mode[0]:
            return
        flush_prose()
        if mode[0] == 'FULL':
            tokens.append(('full_close', None))
        elif mode[0] == 'TERSE':
            tokens.append(('terse_close', None))
        mode[0] = new
        if new == 'FULL':
            tokens.append(('full_open', None))
        elif new == 'TERSE':
            tokens.append(('terse_open', None))

    def add_content(l):
        m = _HEADING_LINE_RE.match(l)
        if l.strip() == '***':
            # A `***` line is a slide break (embedded form of the /- *** -/ marker).
            flush_prose()
            tokens.append(('slidebreak', None))
        elif l.lstrip().startswith('*** '):
            # `*** text` : a slide break immediately followed by prose.
            flush_prose()
            tokens.append(('slidebreak', None))
            prose.append(l.lstrip()[4:])
        elif m:
            flush_prose()
            tokens.append(('block_comment_header',
                           (len(m.group(1)), m.group(2).strip())))
        else:
            prose.append(l)

    idx = 0
    while idx < len(lines):
        l = lines[idx]
        s = l.strip()
        # coqdoc display-code: a lone `[[` (or `[[[`) opens a verbatim code
        # display inside comment prose, closed by a matching `]]` / `]]]`.  The
        # enclosed lines are Lean code (sometimes deliberately ill-formed, e.g.
        # "the following definitions are ill-formed"), so they become a plain,
        # NON-elaborated code block — never a ```lean block Verso would run.
        if s in ('[[', '[[['):
            closer = ']]' if s == '[[' else ']]]'
            flush_prose()
            body = []
            idx += 1
            while idx < len(lines) and lines[idx].strip() != closer:
                body.append(lines[idx]); idx += 1
            idx += 1                       # skip the closing ]] / ]]]
            code = textwrap.dedent('\n'.join(body)).strip('\n')
            if code.strip():
                tokens.append(('code_display', code))
            continue
        # Block-embedded structural markers: some chapters (notably Poly) write
        # EX / [] / GRADE / QUIZ / INSTRUCTORS *inside* /- … -/ comments rather
        # than as `-- ` line markers, so recognize the same set the main
        # tokenizer does — otherwise they flatten to prose (or are dropped) and
        # the quiz/exercise/grade structure is lost.
        m_ex = re.match(r'^EX(\d+)[A-Za-z!?]*\s+\((\w+)\)$', s)
        if s == '/QUIZ':
            flush_prose()
            tokens.append(('quiz_close', None))
            idx += 1; continue
        if s == 'QUIZ':
            flush_prose()
            set_mode(None)            # a ::::quiz can't nest in a same-width
                                      # ::::full/::::terse — close the mode first
                                      # (quiz shown-but-preserved beats quiz lost)
            tokens.append(('quiz_open', None))
            idx += 1; continue
        if m_ex:
            flush_prose()
            tokens.append(('exercise_open', (int(m_ex.group(1)), m_ex.group(2))))
            idx += 1; continue
        if s == '[]':
            flush_prose()
            tokens.append(('exercise_close', None))
            idx += 1; continue
        if re.match(r'^GRADE_\S', s):
            flush_prose()
            tokens.append(('grade_theorem', s))
            idx += 1; continue
        if s.startswith('INSTRUCTORS:'):
            flush_prose()
            tokens.append(('instructor', re.sub(r'^INSTRUCTORS:\s*', '', s)))
            idx += 1; continue
        # Whole-comment FULL/TERSE wrappers: a bare `FULL` / `TERSE` line opens a
        # mode and `/FULL` / `/TERSE` closes it (the `/- FULL … /FULL -/` comment
        # form, distinct from the inline `FULL:` prefix handled just below).
        m_close = re.match(r'^/(FULL|TERSE)$', s)
        m_open_bare = re.match(r'^(FULL|TERSE)$', s)
        m_mode = re.match(r'^\s*(FULL|TERSE):\s?(.*)$', l)
        if m_close:
            set_mode(None)
        elif m_open_bare:
            set_mode(m_open_bare.group(1))
        elif m_mode:
            set_mode(m_mode.group(1))
            # A payload that is itself a dropped region marker (`TERSE:
            # HIDEFROMHTML`, `TERSE: /HIDEFROMHTML`, …) must not become prose.
            rest = m_mode.group(2).strip()
            if rest and not _DROP_MARKER_RE.fullmatch(rest):
                add_content(m_mode.group(2))
        elif _DROP_MARKER_RE.fullmatch(s):
            pass                      # stray region/grade/admitted marker — skip
        else:
            add_content(l)
        idx += 1
    set_mode(None)   # closes any open FULL/TERSE region (flushes prose if one was open)
    flush_prose()    # flush any remaining prose: set_mode(None) early-returns when the
                     # mode is already None (the common no-FULL:/TERSE: case), so the
                     # trailing prose run would otherwise be silently dropped.
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
# Paired `-- TERSE` … `-- /TERSE` region (the complement of FULL: content shown
# only in the terse/lecture build).  Distinct from the inline `-- TERSE:` forms.
_TERSE_OPEN_RE = re.compile(r'^-- TERSE$')
_TERSE_CLOSE_RE = re.compile(r'^-- /TERSE$')
_SLIDEBREAK_RE = re.compile(r'^-- TERSE:\s*/- \*\*\* -/$')
_TERSE_DELIM_RE = re.compile(r'^-- TERSE:\s*/-(.*?)-/$')
_TERSE_PLAIN_RE = re.compile(r'^-- TERSE:\s+(.+)$')
# `-- EX<rating><flags> (name)` — the rating is the leading digit(s); the flags
# are SF difficulty/grading marks: `!` (recommended), `?` (optional), `A`
# (advanced), `M` (manual), and combinations like `2AM?`.
_EX_RE = re.compile(r'^-- EX(\d+)[A-Za-z!?]*\s+\((\w+)\)$')
_EX_CLOSE_RE = re.compile(r'^-- \[\]$')
_GRADE_RE = re.compile(r'^--\s+GRADE_')
# Coq-SF-style section headers written as line comments: `-- # Title` …
# `-- ###### Title`, and `-- * Title` / `-- ** Title` / `-- *** Title`.  These
# are section headings (not code commentary), so they convert to Verso headings.
# A `#`-run longer than 6 (a `-- #####…` divider line) can't match `#{1,6}\s`
# because the char after the 6th `#` is another `#`, not whitespace — so divider
# lines still fall through and are dropped, as before.
_LINE_HEADER_HASH_RE = re.compile(r'^--\s+(#{1,6})\s+(\S.*)$')
_LINE_HEADER_STAR_RE = re.compile(r'^--\s+(\*{1,3})\s+(\S.*)$')
_HIDE_OPEN_RE = re.compile(r'^-- HIDE$')
_HIDE_CLOSE_RE = re.compile(r'^-- /HIDE$')
# Paired `-- QUIZ` … `-- /QUIZ` review question.  Unlike HIDE, the region is
# shown (-> ::::quiz); a `-- HIDE` nested inside becomes the quiz's :::answer.
_QUIZ_OPEN_RE = re.compile(r'^-- QUIZ$')
_QUIZ_CLOSE_RE = re.compile(r'^-- /QUIZ$')
# `-- QUIETSOLUTION` is a solution shown without the solutions-build banner; for
# translation it is handled identically to `-- SOLUTION` (the answer typechecks
# in the teacher build, becomes `sorry` in the student build).
_SOL_OPEN_RE = re.compile(r'^--\s+(?:QUIET)?SOLUTION$')
# Tolerate a stray space after the slash (`-- / SOLUTION`): that typo would
# otherwise leave the capture unclosed, silently swallowing everything up to
# the next close marker (or EOF) into the solution block.
_SOL_CLOSE_RE = re.compile(r'^--\s+/\s?(?:QUIET)?SOLUTION$')
# Author-only / developer comment markers.  These are swept into :::dev blocks
# (discarded from generated outputs, preserved verbatim in the Verso source).
# Add new author initials or task keywords here.  NB: INSTRUCTORS is handled
# separately (-> :::instructor); TERSE/FULL have their own dedicated markers.
_AUTHOR_RE = re.compile(
    r'^-- (BCP|JC|MWH|CGH|RAB|CH|HG|NB|TODO|TOFIX|LATER|SOONER)[: (](.*)$')

# `-- ==> …` / `-- ===> …` hand-written eval-output annotations: intentionally
# dropped (Verso renders the real output live), so they must not be swept into
# a prose run.
_EVAL_ANNOT_RE = re.compile(r'^--\s*=+>')

# Markers that need handling by their own branch in `tokenize` (region capture,
# mode switches, exercise/heading/author tokens).  A run of narrative `--` line
# comments stops at any of these so the dedicated branch processes them; bare
# region markers not listed here (HIDEFROMHTML, QUIZ, ADMITTED, GRADE_…) are
# cleaned up by `_comment_tokens`' own `_DROP_MARKER_RE` instead.
_DEDICATED_LINE_MARKERS = [
    _INSTRUCTOR_RE, _FULL_OPEN_RE, _FULL_CLOSE_RE, _TERSE_OPEN_RE,
    _TERSE_CLOSE_RE, _SLIDEBREAK_RE, _TERSE_DELIM_RE, _TERSE_PLAIN_RE,
    _EX_RE, _EX_CLOSE_RE, _GRADE_RE, _HIDE_OPEN_RE, _HIDE_CLOSE_RE,
    _QUIZ_OPEN_RE, _QUIZ_CLOSE_RE,
    _SOL_OPEN_RE, _SOL_CLOSE_RE, _LINE_HEADER_HASH_RE, _LINE_HEADER_STAR_RE,
    _AUTHOR_RE,
]

def _is_dedicated_line_marker(stripped: str) -> bool:
    return any(p.match(stripped) for p in _DEDICATED_LINE_MARKERS)


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
    quiz_depth = 0   # >0 while inside a -- QUIZ region (so nested HIDE -> answer)

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
            if re.fullmatch(r'(FULL:\s*|TERSE:\s*)?\*\*\*', body.strip()):
                # /- *** -/, /- TERSE: *** -/, /- FULL: *** -/ : a slide break
                # (block-comment form of the -- TERSE: /- *** -/ line marker).
                tokens.append(('slidebreak', None))
            elif body.strip().startswith('INSTRUCTORS:'):
                # /- INSTRUCTORS: … -/ block-form instructor note -> ```instructors
                # (the block-comment analogue of the line-form -- INSTRUCTORS:).
                tokens.append(('instructor',
                               re.sub(r'^INSTRUCTORS:\s*', '', body.strip())))
            elif body.strip().startswith('QUIZ:'):
                # /- QUIZ: question … -/ colon-form whole-comment quiz (Logic):
                # the entire comment is one quiz, closed at the comment's end
                # (distinct from Poly's bare-`QUIZ`-line form handled inside
                # `_comment_tokens`).  Body tokens render inside ::::quiz.
                tokens.append(('quiz_open', None))
                tokens.extend(_comment_tokens(
                    re.sub(r'^\s*QUIZ:\s*', '', body, count=1)))
                tokens.append(('quiz_close', None))
            elif _is_block_dev_comment(body):
                # /- MWH: … -/ author note -> :::dev (keeps every word).
                tokens.append(('author_comment', body))
            elif _is_label_comment(body):
                tokens.append(('block_comment_label', body))
            elif not body.strip():
                tokens.append(('blank', None))
            else:
                tokens.extend(_comment_tokens(body))
            continue

        # An indented `-- …` line comment that directly follows a code line is
        # commentary between tactics inside a proof; keep it as code so the proof
        # stays intact, rather than letting a marker (e.g. `-- BCP:`) pull it out
        # into a directive and split the proof.  (Source markers like -- FULL,
        # -- EX, -- [] sit at column 0, so this never swallows them.)  An
        # indented HIDEFROM* region marker is the exception: it is intentionally
        # dropped everywhere (region semantics not honored), so drop it here too
        # rather than leaking it into the ```lean block.
        if (line[:1].isspace() and stripped.startswith('--')
                and tokens and tokens[-1][0] == 'code_line'):
            if _HIDEFROM_COMMENT_RE.fullmatch(stripped):
                i += 1
                continue
            tokens.append(('code_line', line))
            i += 1
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

        if _TERSE_OPEN_RE.match(stripped):
            tokens.append(('terse_open', None))
            i += 1
            continue

        if _TERSE_CLOSE_RE.match(stripped):
            tokens.append(('terse_close', None))
            i += 1
            continue

        if _SLIDEBREAK_RE.match(stripped):
            tokens.append(('slidebreak', None))
            i += 1
            continue

        m = _TERSE_DELIM_RE.match(stripped)
        if m:
            # `-- TERSE: /- HIDEFROMHTML -/` etc.: the payload is itself a
            # dropped region marker — emit nothing rather than a :::terse block
            # containing the literal marker word.
            if not _DROP_MARKER_RE.fullmatch(m.group(1).strip()):
                tokens.append(('terse_inline', m.group(1).strip()))
            i += 1
            continue

        m = _TERSE_PLAIN_RE.match(stripped)
        if m:
            # A bare `-- TERSE: ***` is a slide break, not the first line of a
            # terse paragraph (cf. the `-- TERSE: /- *** -/` form handled by
            # _SLIDEBREAK_RE above).  Emit the break and let any following comment
            # lines be tokenized on their own, rather than swallowing them into a
            # :::terse block whose stray `***` would then derail Verso.
            if m.group(1).strip() == '***':
                tokens.append(('slidebreak', None))
                i += 1
                continue
            # A `-- TERSE:` paragraph often spans several line comments; collect
            # the continuation `-- …` lines so the whole paragraph lands inside
            # one :::terse block (stopping at a blank line, a non-comment line, or
            # any dedicated marker — including another -- TERSE:/-- FULL:).
            body_lines = [m.group(1).strip()]
            i += 1
            while i < n:
                cont = lines[i].strip()
                if (not cont.startswith('--') or cont == '--'
                        or _is_dedicated_line_marker(cont)
                        or _EVAL_ANNOT_RE.match(cont)):
                    break
                body_lines.append(re.sub(r'^--\s?', '', cont))
                i += 1
            # Drop lines that are bare region markers (`-- TERSE: HIDEFROMHTML`
            # etc.); if nothing else remains, the whole paragraph was a marker —
            # emit no :::terse block at all.
            body_lines = [bl for bl in body_lines
                          if not _DROP_MARKER_RE.fullmatch(bl.strip())]
            if body_lines:
                tokens.append(('terse_inline', '\n'.join(body_lines)))
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
            # Preserve the grading spec (e.g. 'GRADE_THEOREM 1: nandb_test4').
            tokens.append(('grade_theorem', stripped[2:].strip()))
            i += 1
            continue

        if _QUIZ_OPEN_RE.match(stripped):
            tokens.append(('quiz_open', None))
            quiz_depth += 1
            i += 1
            continue

        if _QUIZ_CLOSE_RE.match(stripped):
            tokens.append(('quiz_close', None))
            quiz_depth = max(0, quiz_depth - 1)
            i += 1
            continue

        if _HIDE_OPEN_RE.match(stripped):
            # Capture the whole -- HIDE ... -- /HIDE region verbatim.  Hidden
            # content is often deliberately broken/admitted, so it must never be
            # elaborated; it is emitted as an opaque :::hide block (discarded at
            # elaboration, preserved textually in the source).  Inside a -- QUIZ,
            # the same region is the quiz's answer -> emit an 'answer' token (same
            # verbatim capture, rendered as :::answer).
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
            tokens.append(('answer' if quiz_depth > 0 else 'hide', '\n'.join(raw)))
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

        # Coq-SF section headers in line-comment form -> Verso headings.  The
        # `#`/`*` count maps directly to the heading level (`-- * Foo` and
        # `-- # Foo` -> `# Foo`; `-- ** Foo` / `-- ## Foo` -> `## Foo`).
        m = _LINE_HEADER_HASH_RE.match(stripped) or _LINE_HEADER_STAR_RE.match(stripped)
        if m:
            tokens.append(('block_comment_header',
                           (len(m.group(1)), m.group(2).strip())))
            i += 1
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
                            _GRADE_RE, _AUTHOR_RE,
                            _LINE_HEADER_HASH_RE, _LINE_HEADER_STAR_RE]) and
                        cont != '--'):
                    body_lines.append(cont[2:].lstrip())
                    i += 1
                else:
                    break
            tokens.append(('author_comment', '\n'.join(body_lines)))
            continue

        # --- Narrative prose written as a run of `--` line comments ---
        # The code-forward sources sometimes write prose (and `-- FULL: …`
        # inline-mode paragraphs) as line comments rather than `/- … -/` blocks.
        # Such a run reaches this point only after every dedicated-marker check
        # above has failed and after the indented-comment-inside-a-proof case, so
        # collect the maximal run of plain comment lines and feed it through the
        # same processor used for block-comment bodies (`_comment_tokens`, which
        # also handles FULL:/TERSE: prefixes, `##` headings, dividers, dev notes,
        # and drops bare region markers).  Without this the run would fall through
        # to `code_line` and be silently dropped as a comment-only code block.
        # The extra `_is_dedicated_line_marker` guard ensures the triggering line
        # is itself collectable, so the loop below always advances `i` by at least
        # one (a stray dedicated marker like an unmatched `-- /HIDE` that reaches
        # here would otherwise break immediately, leaving `i` unmoved → infinite
        # loop); such a line instead falls through to the `code_line` default.
        if (stripped.startswith('--') and not _EVAL_ANNOT_RE.match(stripped)
                and not _is_dedicated_line_marker(stripped)):
            run = []
            while i < n:
                s2 = lines[i].strip()
                if (not s2.startswith('--') or _EVAL_ANNOT_RE.match(s2)
                        or _is_dedicated_line_marker(s2)):
                    break
                run.append(re.sub(r'^--\s?', '', lines[i].strip()))
                i += 1
            # A run that is a single identifier is a name/test label (`-- foo_bar`
            # before a definition), the line-comment twin of the `/- foo -/` label
            # dropped via `_is_label_comment`; drop it so it doesn't render as
            # prose (its underscores would also break Verso markup).
            if len(run) == 1 and _is_label_comment(run[0]):
                continue
            tokens.extend(_comment_tokens('\n'.join(run)))
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

# Verso requires an outer directive's fence to be strictly longer than any
# directive nested directly inside it.  The correct width of a *container* fence
# therefore depends on how deeply it ends up nested — which is not known when the
# container opens (its inner content is emitted later, streaming).  So container
# open/close fences are emitted as *sentinels* (`_c_open` / `_c_close`) and their
# real colon widths are computed in a single post-pass over the nesting tree by
# `_resolve_fences`, which grows each container just enough to outrun whatever it
# contains.  This is what lets a `::::full` legally nest inside a `:::::quiz`
# (and an exercise around either), rather than colliding at a shared width.
#
# Leaf directives (`:::answer`, `:::grade`, `:::solution`, `:::slidebreak`, the
# inline `:::terse`) are NOT sentinels: their bodies never hold a colon directive,
# so a plain 3-colon fence is always strictly shorter than any (≥4-colon)
# container around them.
#
# Per-type minimum widths preserve the historical output in the common,
# non-nested cases: full/terse/quiz/hide default to 4 colons and exercise to 5;
# `_resolve_fences` only grows a fence beyond its minimum when nesting demands it.
_CONTAINER_MIN = 4
_EXERCISE_MIN = 5

# Sentinel bytes that cannot occur in source text; replaced by `_resolve_fences`.
_FENCE_OPEN = '\x00['     # followed by the directive header, then '\x00'
_FENCE_CLOSE = '\x00]'


def _c_open(header: str) -> str:
    """Container-open fence sentinel carrying its directive *header* (the text
    after the colons, e.g. `full` or `exercise (rating := 3) (name := "x")`)."""
    return _FENCE_OPEN + header + '\x00'


def _c_close() -> str:
    """Container-close fence sentinel (paired with the matching open by nesting
    order in `_resolve_fences`)."""
    return _FENCE_CLOSE


def _fence_min(header: str) -> int:
    """Minimum colon width for a container by directive type."""
    if header.startswith('exercise'):
        return _EXERCISE_MIN
    return _CONTAINER_MIN


def _resolve_fences(text: str) -> str:
    """Replace container-fence sentinels with colon fences of correct width.

    Walks the sentinels as a tree: each container's width is the larger of its
    per-type minimum and one more than the widest container nested directly
    inside it, so every fence is strictly longer than its children (Verso's
    rule) and no wider than necessary.  Leaf directives already use a literal
    3-colon fence, which is always shorter than the ≥4-colon container around
    them, so they need not participate here."""
    tok = re.compile(r'\x00\[([^\x00]*)\x00|\x00\]')
    stack = []
    events = []  # (is_open, node) in document order; nodes gain 'width' below
    for m in tok.finditer(text):
        if m.group(0) == _FENCE_CLOSE:
            if not stack:  # unbalanced close (shouldn't happen); render minimally
                events.append((False, {'header': '', 'width': 3}))
                continue
            node = stack.pop()
            node['width'] = max(node['min'], node['childmax'] + 1)
            if stack:
                stack[-1]['childmax'] = max(stack[-1]['childmax'], node['width'])
            events.append((False, node))
        else:
            header = m.group(1)
            node = {'header': header, 'min': _fence_min(header), 'childmax': 0}
            stack.append(node)
            events.append((True, node))
    it = iter(events)

    def repl(_m):
        is_open, node = next(it)
        colons = ':' * node['width']
        return colons + node['header'] if is_open else colons

    return tok.sub(repl, text)


def _verbatim_block(text: str) -> str:
    """Wrap *text* in a fenced code block so arbitrary author prose (which may
    contain `*`, `_`, `:::`, backticks, ...) can never derail Verso's directive
    parser.  The fence is grown to outrun any backtick run inside *text*."""
    longest = max((len(m) for m in re.findall(r'`+', text)), default=0)
    fence = '`' * max(3, longest + 1)
    return fence + '\n' + text + '\n' + fence


def _code_block(tag: str, text: str) -> str:
    """Wrap *text* in a fenced code block tagged *tag* (e.g. ` ```dev `).  A
    Verso code block delivers its body to the expander as a raw string that is
    never parsed as markdown, so arbitrary author prose can't derail the parser
    — no inner verbatim fence is needed.  The fence is grown to outrun any
    backtick run inside *text*."""
    longest = max((len(m) for m in re.findall(r'`+', text)), default=0)
    fence = '`' * max(3, longest + 1)
    return fence + tag + '\n' + text + '\n' + fence


class Renderer:
    """Convert a token stream to a Verso document body."""

    def __init__(self):
        self.parts = []       # completed output pieces
        self.code_buf = []    # lines awaiting code block flush
        self.full_depth = 0         # source-level FULL marker nesting
        self.pending_full = False   # :::full requested but not yet emitted
        self.full_open = False      # an emitted :::full is currently unclosed
        self.terse_open = False     # an emitted :::terse is currently unclosed
        self.in_exercise = False
        self.quiz_depth = 0         # emitted-but-unclosed ::::quiz nesting

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
            self._append(_c_open('full') + '\n\n')
            self.pending_full = False
            self.full_open = True

    def _close_full_if_open(self):
        """Emit ::: if an emitted :::full is currently unclosed.

        Tracking the emitted-but-unclosed state explicitly (rather than
        deriving it from marker depth) keeps the output's :::full / :::
        balanced even when the source's -- FULL / -- /FULL markers are not."""
        if self.full_open:
            self._append(_c_close() + '\n\n')
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

    def _on_code_display(self, text):
        # coqdoc `[[ … ]]` display code (see _comment_tokens): a NON-elaborated
        # verbatim code block.  The snippet is often deliberately ill-formed
        # ("the following definitions are ill-formed"), so it must never become a
        # ```lean block that Verso would try to compile.  The fence is grown to
        # outrun any backticks inside the snippet, like other verbatim blocks.
        self._flush_code()
        self._open_full_if_pending()
        self._append(_verbatim_block(text) + '\n\n')

    def _on_block_comment_header(self, hdr):
        level, title = hdr
        self._flush_code()
        # Headers always go at document level — Verso doesn't support headings
        # nested inside block directives like :::full / ::::terse / ::::exercise.
        # A section heading ends any open exercise or terse region (the source
        # closes exercises implicitly at the next section rather than always with
        # `-- []`), and closes/re-arms :::full so later content reopens a fresh one.
        if self.in_exercise:
            self._append(_c_close() + '\n\n')
            self.in_exercise = False
        if self.terse_open:
            self._append(_c_close() + '\n\n')
            self.terse_open = False
        if self.full_open and not self.in_exercise:
            self._close_full_if_open()
            self.pending_full = True
        # Drop trailing coqdoc decoration from the title (`# The apply Tactic *`
        # — the `*` is a leftover coqdoc section marker; a bare line-initial `*`
        # would also trip Verso's bold parser in the rendered heading).
        title = re.sub(r'[ \t*]+$', '', title)
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

    def _on_terse_open(self):
        self._flush_code()
        # Mirror :::full: only emit the region at top level.  Inside an exercise
        # or a :::full (both 4-colon containers) the content just renders inline,
        # which also keeps a same-width directive from nesting illegally.  Also
        # guard against re-opening an already-open :::terse (a source with two
        # `-- TERSE` and no intervening `-- /TERSE`), which would otherwise emit a
        # second `::::terse` with no matching close and unbalance the document
        # (matching `_on_full_open`'s `not self.full_open` guard).
        if (not self.in_exercise and not self.full_open and not self.pending_full
                and not self.terse_open):
            self._append(_c_open('terse') + '\n\n')
            self.terse_open = True

    def _on_terse_close(self):
        self._flush_code()
        if self.terse_open:
            self._append(_c_close() + '\n\n')
            self.terse_open = False

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
        # A new exercise ends the previous one (the source sometimes omits the
        # `-- []` close before the next `-- EX`).
        if self.in_exercise:
            self._append(_c_close() + '\n\n')
        self.in_exercise = True
        self._append(
            _c_open(f'exercise (rating := {rating}) (name := "{name}")') + '\n\n')

    def _on_exercise_close(self):
        self._flush_code()
        # Only emit a close for an exercise we actually opened; a stray `-- []`
        # would otherwise produce an orphan `::::` that unbalances the document.
        if self.in_exercise:
            self.in_exercise = False
            self._append(_c_close() + '\n\n')

    def _on_slidebreak(self):
        self._flush_code()
        self._append(':::slidebreak\n:::\n\n')

    def _on_terse_inline(self, text):
        self._flush_code()
        if text.strip() == '***':
            # `-- TERSE: ***` is a slide break, not terse prose.
            self._append(':::slidebreak\n:::\n\n')
            return
        self._append(':::terse\n' + _prose_markup(text) + '\n:::\n\n')

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
        self._append(_c_open('hide') + '\n' + _verbatim_block(text)
                     + '\n' + _c_close() + '\n\n')

    def _on_quiz_open(self):
        # -- QUIZ ... -- /QUIZ becomes a shown ::::quiz container: its question
        # prose and any illustrative code render normally, and a nested -- HIDE
        # renders as :::answer.  Uses a 4-colon fence (like :::full) so the
        # 3-colon :::answer nests legally; a quiz can't nest inside a
        # same-width :::full, so close a :::full first and re-arm it (mirrors
        # _on_exercise_open) so content after the quiz reopens one.
        self._flush_code()
        if self.full_open and not self.in_exercise:
            self._close_full_if_open()
            self.pending_full = True
        self._append(_c_open('quiz') + '\n\n')
        self.quiz_depth += 1

    def _on_quiz_close(self):
        self._flush_code()
        if self.quiz_depth > 0:
            self._append(_c_close() + '\n\n')
            self.quiz_depth = max(0, self.quiz_depth - 1)

    def _on_answer(self, text):
        # The -- HIDE region inside a -- QUIZ.  Like :::hide it is preserved
        # verbatim and dropped at elaboration for now (rendering it sensibly is a
        # later step); a 3-colon :::answer nests inside the 4-colon ::::quiz.
        self._flush_code()
        if not text.strip():
            return
        self._append(':::answer\n' + _verbatim_block(text) + '\n:::\n\n')

    def _on_grade(self, text):
        # -- GRADE_THEOREM / GRADE_MANUAL -> :::grade.  A noop for now, but the
        # grading spec is preserved (verbatim-fenced, since names contain `_`)
        # for the future grading infrastructure to consume.
        self._flush_code()
        if not text.strip():
            return
        self._append(':::grade\n' + _verbatim_block(text) + '\n:::\n\n')

    def _on_solution_prose(self, text):
        # Prose / non-compiling solution -> :::solution block, shown only in the
        # solutions build (SFLMeta.Block.solution).  Body is verbatim-fenced so
        # arbitrary illustrative code can't perturb the parser.
        self._flush_code()
        if not text.strip():
            return
        self._append(':::solution\n' + _verbatim_block(text) + '\n:::\n\n')

    def _emit_noop_directive(self, directive, text):
        # Author notes become noop annotation *code blocks* (```dev / ```instructors).
        # The text is preserved in the Verso source, but the block discards its
        # body so it never reaches the generated outputs.  ```dev and
        # ```instructors are processed identically (see SFLMeta); they differ only
        # in name so instructor notes can be treated differently later.
        #
        # A code block delivers its body to the expander as a raw string that
        # Verso never parses as markdown, so arbitrary author text (underscores,
        # `*`, `[...]`, a leading `#`, `:::`, ...) can't break the parser — unlike
        # a `:::` directive, whose body IS parsed and so used to need an inner
        # verbatim fence.  The single tagged fence replaces that nesting.
        self._flush_code()  # still acts as a code-block separator
        self._append(_code_block(directive, text) + '\n\n')

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
            elif kind == 'terse_open':
                self._on_terse_open()
            elif kind == 'terse_close':
                self._on_terse_close()
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
            elif kind == 'quiz_open':
                self._on_quiz_open()
            elif kind == 'quiz_close':
                self._on_quiz_close()
            elif kind == 'answer':
                self._on_answer(content)
            elif kind == 'code_display':
                self._on_code_display(content)
            elif kind == 'solution_prose':
                self._on_solution_prose(content)
            elif kind == 'grade_theorem':
                self._on_grade(content)
            # else: unknown token — ignore

        # Flush any trailing code
        self._flush_code()

        # Close any unclosed blocks (shouldn't happen in well-formed source)
        if self.in_exercise:
            self._append(_c_close() + '\n\n')  # close unclosed exercise
            self.in_exercise = False
        if self.terse_open:
            self._append(_c_close() + '\n\n')  # close unclosed terse
            self.terse_open = False
        while self.quiz_depth > 0:
            self._append(_c_close() + '\n\n')  # close unclosed quiz
            self.quiz_depth -= 1
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


def _drop_empty_directives(text: str) -> str:
    """Remove directives with an empty body, e.g. an `::::terse` immediately
    followed by its `::::` close.  These arise when a region's only content is
    pulled out to document level — a `-- TERSE` whose body is just a `#` heading
    (headings can't nest in a directive, so the heading forces the terse closed
    and leaves an empty shell).  Iterated so a nested empty directive that leaves
    its parent empty is removed too."""
    def once(t):
        lines = t.split('\n')
        out, i, n = [], 0, len(lines)
        while i < n:
            # An opening directive with a name — but NOT `:::slidebreak`, which is
            # an intentionally empty self-closing marker (`:::slidebreak` / `:::`),
            # not an empty container to drop.
            m = re.match(r'^(:::+)(?!slidebreak\b)\w', lines[i])
            if m:
                fence = m.group(1)
                j = i + 1
                while j < n and lines[j].strip() == '':
                    j += 1
                if j < n and lines[j].rstrip() == fence:   # immediate matching close
                    i = j + 1                              # drop both open and close
                    continue
            out.append(lines[i]); i += 1
        return '\n'.join(out)
    prev = None
    while prev != text:
        prev, text = text, once(text)
    return text


def _normalize_heading_levels(text: str) -> str:
    """Remap heading levels so they never skip a level.  Verso rejects a jump
    from `#` straight to `###` (every heading must be at most one level deeper
    than its parent), but the sources mix `#`/`##` markers with coqdoc
    `*`/`**`/`***` section markers, which can leave gaps.  Walk the document-level
    headings in order and compress each source level to the shallowest legal
    output level via a stack.  Lines inside fenced code blocks (```lean, ```dev,
    verbatim, display) are skipped so a `#` inside a note or snippet is left
    alone."""
    out = []
    stack = []          # (source_level, output_level), outermost first
    fence = None        # opening backtick/tilde run while inside a code block
    for line in text.split('\n'):
        if fence is not None:
            if line.rstrip() == fence:
                fence = None
            out.append(line)
            continue
        mf = re.match(r'^(`{3,}|~{3,})', line)
        if mf:
            fence = mf.group(1)
            out.append(line)
            continue
        m = re.match(r'^(#{1,6})\s+(.*)$', line)
        if m:
            src = len(m.group(1))
            while stack and stack[-1][0] >= src:
                stack.pop()
            lvl = (stack[-1][1] + 1) if stack else 1
            stack.append((src, lvl))
            out.append('#' * lvl + ' ' + m.group(2))
            continue
        out.append(line)
    return '\n'.join(out)


def _fuse_noop_blocks(text: str) -> str:
    """Fuse runs of consecutive ```dev / ```instructors code blocks (separated
    only by blank lines) into a single same-tag block, so a run of adjacent
    author notes renders as one box rather than a stack of tiny ones.  The fused
    body is re-fenced via `_code_block`, so a fence that had to grow to outrun
    backticks in one note still outruns backticks in the combined body.  Only
    same-tag blocks fuse (a `dev` never merges into an `instructors`)."""
    lines = text.split('\n')
    out, i, n = [], 0, len(lines)
    while i < n:
        m = re.match(r'^(`{3,})(dev|instructors)$', lines[i])
        if not m:
            out.append(lines[i]); i += 1; continue
        tag = m.group(2)
        bodies = []
        while i < n:
            mm = re.match(r'^(`{3,})' + re.escape(tag) + r'$', lines[i])
            if not mm:
                break
            fence = mm.group(1)
            j = i + 1
            body = []
            while j < n and lines[j] != fence:
                body.append(lines[j]); j += 1
            bodies.append('\n'.join(body))
            k = j + 1
            while k < n and lines[k].strip() == '':  # skip blanks between blocks
                k += 1
            i = k
        out.append(_code_block(tag, '\n\n'.join(bodies)))
        out.append('')
    return '\n'.join(out)


def _fuse_full_blocks(text: str) -> str:
    """Fuse adjacent ::::full … :::: blocks (separated only by blank lines) into
    a single block, so consecutive -- FULL / -- /FULL / -- FULL runs in the
    source don't render as a stack of separate full boxes.  Safe because a full
    body never contains a bare 4-colon `::::` line except its own closer: a
    nested hide/quiz/exercise closes the open full before opening (so they land
    after the full), and grade/solution/dev use narrower (3-colon / backtick)
    fences."""
    lines = text.split('\n')
    out, i, n = [], 0, len(lines)
    while i < n:
        if lines[i] != '::::full':
            out.append(lines[i]); i += 1; continue
        bodies = []
        while i < n and lines[i] == '::::full':
            j = i + 1
            body = []
            while j < n and lines[j] != '::::':
                body.append(lines[j]); j += 1
            bodies.append('\n'.join(body).strip('\n'))
            k = j + 1
            while k < n and lines[k].strip() == '':  # skip blanks between blocks
                k += 1
            i = k
        out.append('::::full')
        out.append('')
        out.append('\n\n'.join(bodies))
        out.append('')
        out.append('::::')
        out.append('')
    return '\n'.join(out)

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
            j = i + 1
            body = []
            while j < n and lines[j].strip() != '-- /ADMITTED':
                body.append(lines[j]); j += 1
            # `solution!` must align with the proof body (which sits inside the
            # `by`), not with the `-- ADMITTED` marker — the marker is often at
            # column 0 while the tactics are indented, and a column-0 `solution!`
            # would be read as a new command after an empty `by` block.
            first_body = next((b for b in body if b.strip()), '')
            indent = _indent_of(first_body) if first_body else _indent_of(line)
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
    # The opening title comment is already used for the #doc declaration;
    # strip it so it doesn't appear again as prose.
    body_src = _strip_title_comment(src_text, file_key)
    # Lift top-level `import …` lines (and `prelude`) into the Verso header;
    # they can't live in a ```lean``` code block.
    has_prelude, extra_imports, body_src = _extract_imports(body_src)
    header = HEADER_TEMPLATE.format(
        title=title, file=file_key, extra_imports='\n'.join(extra_imports))
    if has_prelude:
        header = 'prelude\n' + header
    # Normalize block-comment markers (/- EX … -/, /- /TERSE -/, …) to line form.
    body_src = _normalize_block_markers(body_src)
    # Rewrite solution markers (ADMITDEF/ADMITTED/SOLUTION) into the in-code
    # forms SFLMeta understands before tokenizing.
    body_src = _convert_solution_markers(body_src)
    tokens = tokenize(body_src)
    renderer = Renderer()
    renderer.process(tokens)
    body = renderer.result()
    # Resolve container-fence sentinels to correctly-widened colon fences before
    # any pass that inspects `:::` fences (fusing, blank-stripping, empty-drop).
    body = _resolve_fences(body)
    # Fuse adjacent same-type author-note / full blocks before normalizing blanks.
    body = _fuse_noop_blocks(body)
    body = _fuse_full_blocks(body)
    body = _normalize_heading_levels(body)
    body = _drop_empty_directives(body)
    body = _strip_directive_blanks(body)
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
    file_key = src_path.stem   # e.g. "Basics"
    title = args.title or extract_title(src_text, file_key)

    result = convert(src_text, title, file_key)
    dst_path.write_text(result)
    print(f'Written {dst_path}  (title: {title!r}, file key: {file_key!r})')


if __name__ == '__main__':
    main()
