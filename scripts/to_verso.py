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

Note: -- ADMITDEF / -- /ADMITDEF and -- ADMITTED markers are converted to
solution!() wrappers (see `_convert_solution_markers`), so the student build
stubs the elided definition/proof to `sorry` and the teacher build keeps it.

A Rocq source (SOURCE.v) is also accepted: its comment/marker layer is first
converted to the code-forward Lean-comment dialect above (the code lines stay
Coq) and then run through the same pipeline.  The result is a ROUGH DRAFT Verso
file — full structure, prose, and (untranslated) code, with nothing dropped —
meant to be translated to Lean by hand from then on; it will not build until
that is done.  --emit-lean writes the intermediate Lean-dialect skeleton too,
which is only needed as the reference input for scripts/check_verso_prose.py
and scripts/check_verso_markers.py (both compare a skeleton against the Verso
output); it is not meant to be edited.

Usage (from the repo root):
    python3 scripts/to_verso.py LF/Basics.lean LF/BasicsVerso.lean
    python3 scripts/to_verso.py old/orig-lf-files/Poly.v /tmp/PolyVerso.lean
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
import SFLMeta.DisplayMath
import SFLMeta.Ignore
import SFLMeta.Save
import SFLMeta.Comment
import SFLMeta.Epigraph
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

{doc_options}#doc (Manual) "{title}" =>
%%%
tag := "{file}"
htmlSplit := .never
file := some "{file}"
%%%

"""

# Per-chapter document-level `set_option`s emitted just before `#doc`.  Unlike a
# `set_option … in` inside a ```lean block, options here cover the whole
# command — including InlineLean's syntax highlighting (which re-drives
# elaboration) and the code generator's pass over the generated `Verso.Doc.Block`
# document term.  IndPropRegexp needs both: its pumping proofs elaborate under
# the highlighting overhead well past the default 200000 heartbeats, and the
# chapter's deep directive nesting overflows the code generator's recursion
# limit compiling the document `block` term (which then reports as noncomputable).
# Other chapters compile within the defaults, so they are left untouched.  Keyed
# by file_key; a graduated (direct-Verso) chapter carries the same options inline.
DOC_LEVEL_OPTIONS = {
    "IndPropRegexp": "set_option maxHeartbeats 2000000\n"
                     "set_option maxRecDepth 100000\n\n",
}

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


# LF modules that are authored directly in Verso (Basics, Induction, UsingLean,
# Lists) or are plain Lean support modules (CustomTactics, Maps): an
# `import LF.X` of one of these passes through unchanged.  Every *other*
# `import LF.X` refers to a generated chapter, so it is rewritten to
# `import LF.XVerso`.
# (Maps added by Claude: HL/TS chapters import LF.Maps for its definitions.)
DIRECT_LF_MODULES = {"Basics", "Induction", "UsingLean", "Lists", "Poly",
                     "CustomTactics", "Maps"}

_IMPORT_RE = re.compile(r'^import\s+(\S+)\s*$')

# Some chapters write structural markers in block-comment form (`/- EX2 (foo) -/`,
# `/- /TERSE -/`, `/- [] -/`) rather than line form (`-- EX2 (foo)`).  Only the
# line form is recognized downstream, so normalize a single-line `/- MARKER -/`
# to `-- MARKER`.  Plain `/- label -/` / `/- prose -/` comments are left alone.
_BLOCK_MARKER_RE = re.compile(
    r'/-[ \t]*('
    r"EX\d+[A-Za-z!?]*[ \t]+\(\w[\w' \-]*\)"   # exercise open: EX2M? (name)
    r'|\[\]'                                   # exercise close
    r'|GRADE_\S[^\n]*?'                        # grading spec
    r'|/?(?:HIDEFROMADVANCED|HIDEFROMHTML|FULL|TERSE|HIDE|QUIZ|QUIETSOLUTION|SOLUTION'
    r'|INSTRUCTORS|WORKINCLASS|ADMITTED|ADMITDEF)'
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
            # A volume-module import also stays in the body, as a sentinel that
            # the renderer turns into a ```importBlock code block: the header
            # import above names the Verso module, but the generated student/
            # solutions/terse chapter files need the original import line (and
            # the reader should see it where the prose introduces it).
            if re.match(r'(?:LF|HL|TS)\.\w+$', m.group(1)):
                kept.append('--IMPORTBLOCK ' + line.strip())
        else:
            kept.append(line)
    return has_prelude, imports, '\n'.join(kept)

# Author initials / task keywords that mark an author-or-dev note.  Both block
# `/- … -/` comments and `-- ` line comments (see `_AUTHOR_RE`) that open with
# one of these route to :::dev — preserved in the Verso source, dropped from the
# generated outputs.  Add new tags here so they route cleanly instead of leaking
# into the rendered chapter as prose.  INSTRUCTORS is deliberately NOT in this
# set: it routes to :::instructor (handled separately, both line and block).
_DEV_TAGS = (r'BCP|JC|MWH|CGH|RAB|CH|HG|NB|Claude|TODO|TOFIX|LATER|SOONER|NOW'
             r'|NDS|NOTATION|APT|BAY|SAZ|ET|AAA|MRC|PR|ORI|Ori|mwhicks1|chenson2018'
             r'|COMMENT')  # COMMENT: untagged (* .. *) comments from a .v source
# The block set additionally recognizes `HIDE:` (a `/- HIDE: … -/` dev note).
# The colon is required so a bare `/- HIDE -/` region/label marker keeps its old
# behavior (dropped as a label) rather than becoming a noise :::dev block; and
# as a `-- HIDE` / `-- /HIDE` line marker `HIDE` is handled elsewhere, so it must
# stay out of the line-comment `_AUTHOR_RE`.
_BLOCK_DEV_RE = re.compile(r'^(HIDE(?=:)|(?:' + _DEV_TAGS + r')\b)')
# `/- INSTRUCTORS: … -/` -> :::instructor (colon required, mirroring the line
# form `_INSTRUCTOR_RE`).
_BLOCK_INSTRUCTOR_RE = re.compile(r'^INSTRUCTORS:')

# Urgency keywords: when one of these opens a dev note it becomes the :::dev
# directive's `(urgency := …)` argument rather than an author.
_URGENCY_TAGS = ('NOW', 'SOONER', 'LATER', 'TODO', 'TOFIX')

# Authors behind the initials appearing in dev notes, as "Full Name
# (github-handle)".  When a note opens with one of these tags (or, after an
# urgency keyword, with a clean `TAG:` / `(TAG)` attribution), the tag is
# promoted to the :::dev directive's `(author := "…")` argument.  Initials
# with no entry here are left in the note body untouched — add entries as the
# people behind the initials are identified.
_AUTHOR_NAMES = {
    'BCP': 'Benjamin Pierce (bcpierce00)',
    'MWH': 'Michael Hicks (mwhicks1)',
    'mwhicks1': 'Michael Hicks (mwhicks1)',
    'JC': 'Jonathan Chan (ionathanch)',
    'RAB': 'Roger Burtonpatel (rogerburtonpatel)',
    # CH is Chris Henson in sf-in-lean notes; in old sfdev notes CH was
    # Catalin Hritcu — none of those are ported yet.
    'CH': 'Chris Henson (chenson2018)',
    'chenson2018': 'Chris Henson (chenson2018)',
    'HG': 'Harrison Goldstein (hgoldstein95)',
    'DHS': 'Daniel Sainati (dsainati1)',
    'AAA': 'Arthur Azevedo de Amorim (arthuraa)',
    'BAY': 'Brent Yorgey (byorgey)',
    'MRC': 'Michael Clarkson (clarksmr)',
    'ORI': 'Ori Lahav (orilahav)',
    'Ori': 'Ori Lahav (orilahav)',
    'APT': 'Andrew Tolmach (AndrewTolmach)',
    'SAZ': 'Steve Zdancewic (Zdancewic)',
    'NDS': 'Noé De Santo (Ef55)',
    'OA': 'One An (meluge)',
    'KH': 'Kihong Heo (KihongHeo)',
    'KK': 'Konstantinos Kallas (angelhof)',
    'Claude': 'Claude',   # AI-generated notes keep the plain name
    # Unresolved initials (left verbatim in note bodies until identified):
    # CGH, NB, ET, PR, FSR, MMG.
}


# GitHub handles (as written in `@handle:` attributions in hand-versified
# chapters) -> the full author string from `_AUTHOR_NAMES`.
_HANDLE_NAMES = {}
for _v in set(_AUTHOR_NAMES.values()):
    _m = re.search(r'\(([^)]+)\)$', _v)
    if _m:
        _HANDLE_NAMES[_m.group(1)] = _v
del _v


def _tag_year(digits):
    """Expand a `'NN` tag-year suffix to a full year (SF development spans
    2007–now, so two-digit years below 90 are 20NN)."""
    n = int(digits)
    return 2000 + n if n < 90 else 1900 + n


def _split_dev_tags(text):
    """Promote the leading tag(s) of a dev-note body into :::dev arguments.

    Returns ``(author, year, urgency, body)``.  The note's first token is the
    tag that routed it to :::dev: an urgency keyword (-> the `(urgency := …)`
    argument) or an author tag (-> the positional author argument, as
    `"Full Name (handle)"` via `_AUTHOR_NAMES`; a `@handle:` attribution is
    looked up via `_HANDLE_NAMES`).  After an urgency keyword, a clean author
    attribution — `BCP:`, `(DHS)`, `(BCP'20)`, a bare year `BCP 25:`, or an
    `MM/YY` date `BCP 9/16:` (month dropped, year kept) — is promoted too;
    anything murkier (unmapped initials, plain prose) stays in the body.
    Topic keywords (NOTATION:, HIDE:, COMMENT:) and unmapped tags leave the
    note untouched.  A year suffix on a promoted tag (`NDS'25`, `BCP'20`)
    becomes the `(year := 20NN)` argument."""
    body = text.lstrip()
    author = year = urgency = None
    m = re.match(r"@([A-Za-z][A-Za-z0-9-]*)\s*:?\s*", body)
    if m and m.group(1) in _HANDLE_NAMES:
        author = _HANDLE_NAMES[m.group(1)]
        body = body[m.end():]
    else:
        m = re.match(r"([A-Za-z][A-Za-z0-9]*)(?:'(\d+))?\s*:?\s*", body)
        if not m:
            return None, None, None, text
        tok = m.group(1)
        if tok in _URGENCY_TAGS:
            urgency = tok
        elif tok in _AUTHOR_NAMES:
            author = _AUTHOR_NAMES[tok]
            if m.group(2):
                year = _tag_year(m.group(2))
        else:
            return None, None, None, text
        body = body[m.end():]
    if urgency:
        # `TODO: (DHS) …` / `SOONER: (BCP'20) …` / `LATER: KK: …`; a bare tag
        # WITH a year suffix (`LATER: NDS'25 This list…`) is also unambiguously
        # an attribution, colon or not.
        m2 = re.match(r"\(([A-Za-z][A-Za-z0-9]*)(?:'(\d+))?\)\s*:?\s*", body)
        if not m2:
            m2 = re.match(r"([A-Za-z][A-Za-z0-9]*)(?:'(\d+))?\s*:\s*", body)
        if not m2:
            m2 = re.match(r"([A-Za-z][A-Za-z0-9]*)'(\d+)\s+", body)
        if not m2:
            # `SOONER: BCP 25: …` — initials, a space, a bare two-digit year,
            # then a colon.  The space-then-year spelling of `BCP'25:`.
            m2 = re.match(r"([A-Za-z][A-Za-z0-9]*)\s+(\d{2})\s*:\s*", body)
        if not m2:
            # `LATER: BCP 9/16: …` / `SOONER: MRC 3/22: …` — an `MM/YY` date;
            # we keep only the year (after the slash) and drop the month.
            m2 = re.match(r"([A-Za-z][A-Za-z0-9]*)\s+\d{1,2}/(\d{2})\s*:\s*", body)
        if m2 and m2.group(1) in _AUTHOR_NAMES:
            author = _AUTHOR_NAMES[m2.group(1)]
            if m2.group(2):
                year = _tag_year(m2.group(2))
            body = body[m2.end():]
    else:
        # `BCP: SOONER: …`
        m2 = re.match(r"(%s)\s*:\s*" % '|'.join(_URGENCY_TAGS), body)
        if m2:
            urgency = m2.group(1)
            body = body[m2.end():]
    if not body.strip():
        body = text  # tag-only note: keep the original text as the body
    return author, year, urgency, body


def _is_block_dev_comment(text: str) -> bool:
    """True when a `/- … -/` block comment is an author/dev note (e.g. `MWH: …`).
    These are routed to :::dev blocks (preserving every word), not dropped."""
    return bool(_BLOCK_DEV_RE.match(text.strip()))


def _is_label_comment(text: str) -> bool:
    """True when text (stripped comment body) should be stripped in Verso output.

    This covers:
      - Single identifiers like "test_nandb1" or "test_leb3'" (test-case labels)
      - The same with a one-word parenthetical, like "star_app (helper)"
      - Pure separator lines like "############################" (visual dividers)
      - Lean output annotations like "==> true : Bool" or "===> ..." (#check/#eval)
    These act as code-block separators but produce no visible Verso output.
    (Author/dev block notes are *not* labels — see `_is_block_dev_comment`.)
    """
    t = text.strip()
    return (bool(re.match(r"^[\w.']+(?:\s+\(\w[\w.']*\))?$", t)) or
            bool(re.match(r'^#{3,}[ \t#-]*$', t)) or
            bool(re.match(r'^=+>', t)))

def _is_epigraph_comment(text: str) -> bool:
    """True when a standalone comment body is a section epigraph — a quotation
    whose first character is a double quote (straight or curly).  In the Rocq
    sources these were wrapped in `#<div class="quote">#…#</div>#`; the block
    markup was lost in the port, so the leading quote is the only surviving
    signal.  (Heuristic first pass: no ported chapter has a non-epigraph
    comment that opens with a quote.)"""
    return bool(re.match(r'^\s*["“]', text))

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


def _lean_comment_balance(line: str, depth: int = 0) -> int:
    """Net count of block comments opened minus closed on *line*, honoring
    `--` line comments: a `--` ends the scan only when no block comment is
    open at that point — *depth* is the block-comment depth carried in from
    previous lines, so a `--` inside a still-open `/-- … -/` (e.g. the
    `  -- no goals -/` tail of a #guard_msgs docstring) does not hide the
    closing `-/`."""
    bal = 0
    i = 0
    n = len(line)
    while i < n - 1:
        two = line[i:i + 2]
        if two == '/-':
            bal += 1
            i += 2
        elif two == '-/':
            bal -= 1
            i += 2
        elif two == '--' and depth + bal == 0:
            break
        else:
            i += 1
    return bal


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
            # Dedent the run by its common indent (uniform, so relative
            # indentation — bullets, display material — is preserved).
            # Catches alignment indents that survive `_extract_comment_text`,
            # e.g. when a column-0 fence line drags the comment-wide minimum
            # to zero.
            cut = min(len(l) - len(l.lstrip()) for l in seg if l.strip())
            if cut:
                seg = [l[cut:] if l.strip() else l for l in seg]
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
        # (Claude) A fenced code block written directly in prose (``` … ``` or
        # ~~~ … ~~~) is passed through verbatim.  This lets an author include
        # literal display material -- pseudocode, BNF grammars, inference rules --
        # whose characters (`*`, `|`, `_`, `<>`, …) would otherwise be mangled by
        # Verso's inline markup or would break the enclosing `::::` directive.
        fm = re.match(r'^\s*([`~]{3,})(.*)$', l)
        if fm:
            flush_prose()
            info = fm.group(2).strip()
            block = ['```' + info]
            idx += 1
            while idx < len(lines):
                if re.match(r'^\s*[`~]{3,}\s*$', lines[idx]):
                    idx += 1
                    break
                block.append(lines[idx])
                idx += 1
            block.append('```')
            tokens.append(('block_comment_prose', '\n'.join(block)))
            continue
        # Block-embedded structural markers: some chapters (notably Poly) write
        # EX / [] / GRADE / QUIZ / INSTRUCTORS *inside* /- … -/ comments rather
        # than as `-- ` line markers, so recognize the same set the main
        # tokenizer does — otherwise they flatten to prose (or are dropped) and
        # the quiz/exercise/grade structure is lost.
        m_ex = re.match(r"^EX(\d+)[A-Za-z!?]*\s+\((\w[\w']*)\)$", s)
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
        # FULL/TERSE markers in comment position come in two distinct forms:
        #
        # * A bare `FULL` / `TERSE` line is a *region* marker — the in-comment
        #   analogue of a `-- FULL` line.  Its `/FULL` close often lives in a
        #   *later* comment (Poly writes whole sections this way), so it must
        #   NOT be comment-local: emit the open/close token directly and let
        #   the renderer's region state span comments.  (Before 2026-07-14
        #   these were auto-closed at the end of the comment, silently
        #   widening every cross-comment region to both builds.)
        # * A `FULL:` / `TERSE:` *prefix* switches the mode for the lines that
        #   follow it within this comment only (handled via set_mode below and
        #   auto-closed at the end of the comment).
        m_close = re.match(r'^/(FULL|TERSE)$', s)
        m_open_bare = re.match(r'^(FULL|TERSE)$', s)
        m_mode = re.match(r'^\s*(FULL|TERSE):\s?(.*)$', l)
        if m_close:
            if mode[0] is not None:
                set_mode(None)
            else:
                flush_prose()
                tokens.append(('full_close' if m_close.group(1) == 'FULL'
                               else 'terse_close', None))
        elif m_open_bare:
            set_mode(None)
            flush_prose()
            tokens.append(('full_open' if m_open_bare.group(1) == 'FULL'
                           else 'terse_open', None))
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

    rest_non_blank = [l for l in lines[1:] if l.strip()]
    if lines[0].strip() and rest_non_blank:
        # Text starts on the opener line, which now sits at column 0 (its
        # indent went with the `/- `), while continuation lines keep the
        # source's alignment indent (2-4 spaces depending on the comment).
        # Take the first continuation line's indent as the alignment column
        # and strip up to that much whitespace from every continuation:
        # lines indented deeper (bullet bodies, display material) keep their
        # offset, and lines shallower than the alignment column (a `[[` or
        # fence marker at column 0, a raggedly-indented prose line) lose
        # only the whitespace they actually have.
        align = len(rest_non_blank[0]) - len(rest_non_blank[0].lstrip())
        lines = [lines[0]] + [l[min(align, len(l) - len(l.lstrip())):]
                              for l in lines[1:]]
    else:
        # Opener on a line of its own: plain common dedent over all lines.
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
# (advanced), `M` (manual), and combinations like `2AM?`.  A name is usually an
# identifier but occasionally a phrase (`EX2 (logical connectives)`), so allow
# internal spaces/hyphens.
_EX_RE = re.compile(r"^-- EX(\d+)[A-Za-z!?]*\s+\((\w[\w' \-]*)\)$")
# The close marker may carry a redundant `(end name)` label (IndPropRegexp
# style); it is consumed with the marker — the :::::exercise block records the
# name already.
_EX_CLOSE_RE = re.compile(r"^-- \[\](?:\s*\(end \w[\w']*\))?$")
_GRADE_RE = re.compile(r'^--\s+GRADE_')
# Coq-SF-style section headers written as line comments: `-- # Title` …
# `-- ###### Title`, and `-- * Title` / `-- ** Title` / `-- *** Title`.  These
# are section headings (not code commentary), so they convert to Verso headings.
# A `#`-run longer than 6 (a `-- #####…` divider line) can't match `#{1,6}\s`
# because the char after the 6th `#` is another `#`, not whitespace — so divider
# lines still fall through and are dropped, as before.
_LINE_HEADER_HASH_RE = re.compile(r'^--\s+(#{1,6})\s+(\S.*)$')
_LINE_HEADER_STAR_RE = re.compile(r'^--\s+(\*{1,3})\s+(\S.*)$')
# Hidden regions: `-- HIDE … -- /HIDE` and the region form
# `-- INSTRUCTORS … -- /INSTRUCTORS` (bare, no colon — distinct from the
# `-- INSTRUCTORS:` author note handled by `_INSTRUCTOR_RE`).  Both are captured
# verbatim and emitted as :::hide (or :::answer when nested inside a quiz); the
# content is often deliberately admitted, so it must never be elaborated.
_HIDE_OPEN_RE = re.compile(r'^-- (?:HIDE|INSTRUCTORS)$')
_HIDE_CLOSE_RE = re.compile(r'^-- /(?:HIDE|INSTRUCTORS)$')
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
# The recognized tag set is `_DEV_TAGS` (defined above — add new tags there).
# NB: the `-- INSTRUCTORS:` author note is handled separately (-> :::instructor),
# and the bare `-- INSTRUCTORS` region form is a hidden region (see
# `_HIDE_OPEN_RE`); TERSE/FULL have their own dedicated markers.
_AUTHOR_RE = re.compile(r'^-- (' + _DEV_TAGS + r')[: (](.*)$')

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
    code_comment_depth = 0  # open /-- … -/ (docstring) balance carried by code lines

    while i < n:
        line = lines[i]
        stripped = line.strip()

        # --- Inside a docstring (`/-- … -/` spanning code lines) ---
        # Everything is consumed verbatim as code — including blank lines,
        # which must NOT collapse: `#guard_msgs` docstrings quote expected
        # messages exactly, consecutive blanks and all.
        if code_comment_depth > 0:
            tokens.append(('code_line', line))
            code_comment_depth += _lean_comment_balance(line, code_comment_depth)
            i += 1
            continue

        # --- Blank line ---
        if stripped == '':
            tokens.append(('blank', None))
            i += 1
            continue

        # --- importBlock sentinel (planted by _extract_imports) ---
        if stripped.startswith('--IMPORTBLOCK '):
            body = [stripped[len('--IMPORTBLOCK '):]]
            i += 1
            while i < n and lines[i].strip().startswith('--IMPORTBLOCK '):
                body.append(lines[i].strip()[len('--IMPORTBLOCK '):])
                i += 1
            tokens.append(('import_block', '\n'.join(body)))
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
            elif _BLOCK_INSTRUCTOR_RE.match(body.strip()):
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
            elif _is_epigraph_comment(body):
                # A standalone comment that is entirely a quotation (its first
                # character is a double quote) is a section epigraph: in the
                # Rocq sources these were wrapped `#<div class="quote">#…#</div>#`,
                # markup that was lost in the port and survives only as the bare
                # quoted comment.  Restore it as a :::epigraph directive (rendered
                # italic for now).
                tokens.append(('epigraph', _prose_markup(body.strip())))
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

        # `-- DEV` … `-- /DEV` region: an author/developer note without a tag
        # prefix.  The whole body routes to a :::dev block (markers consumed).
        if stripped == '-- DEV':
            body_lines = []
            i += 1
            while i < n and lines[i].strip() != '-- /DEV':
                body_lines.append(re.sub(r'^--\s?', '', lines[i].strip()))
                i += 1
            i += 1  # skip the closing -- /DEV (or run off EOF)
            if body_lines:
                tokens.append(('author_comment', '\n'.join(body_lines)))
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
        code_comment_depth += _lean_comment_balance(line, code_comment_depth)
        i += 1

    return tokens

def _hoist_from_terse(tokens):
    """Lift slide breaks and quizzes out of any enclosing `::::terse` region.

    A slide break only matters in the terse HTML build (it renders an empty
    `<div class="slide-break">` there) and is stripped from every other product
    — full HTML and all three generated `.lean` files.  So it never needs to
    sit *inside* a `::::terse` container; doing so is just noise (and, when the
    break is a region's sole content, leaves a pointless one-item terse block).

    The same goes for a whole `-- QUIZ … -- /QUIZ` region: quizzes are shown
    only in the terse build product anyway, so nesting them in `::::terse`
    adds nothing — and keeping them at top level leaves the door open to
    including quizzes in the student/solutions products later.  The sources
    routinely wrap quiz runs in a TERSE region (Poly, Logic), so this pattern
    is the norm, not an error.

    A source like `/- TERSE: *** text -/` tokenizes to
    `terse_open, slidebreak, prose, terse_close`.  Rewrite each `slidebreak`
    that falls within an open terse region to `terse_close, slidebreak,
    terse_open` — hoisting the break to top level and reopening the region for
    whatever terse content follows — and likewise wrap each top-level
    `quiz_open … quiz_close` span in `terse_close … terse_open`; then drop any
    `terse_open … terse_close` pair left empty (the hoisted item was the
    region's first or last, or sat between two quizzes), so no bare
    `::::terse` survives.  Terse markers arriving *inside* a hoisted quiz span
    only adjust the source-depth bookkeeping and emit nothing: the enclosing
    region's fence is already suspended, and whether it resumes after the quiz
    is decided by the source depth at the `quiz_close`."""
    lifted = []
    terse_depth = 0   # source-level terse nesting (markers seen, hoisted or not)
    quiz_depth = 0
    for kind, content in tokens:
        if kind == 'terse_open':
            terse_depth += 1
            if quiz_depth == 0:
                lifted.append((kind, content))
        elif kind == 'terse_close':
            terse_depth = max(0, terse_depth - 1)
            if quiz_depth == 0:
                lifted.append((kind, content))
        elif kind == 'slidebreak' and terse_depth > 0 and quiz_depth == 0:
            lifted.append(('terse_close', None))
            lifted.append(('slidebreak', None))
            lifted.append(('terse_open', None))
        elif kind == 'quiz_open':
            if quiz_depth == 0 and terse_depth > 0:
                lifted.append(('terse_close', None))
            quiz_depth += 1
            lifted.append((kind, content))
        elif kind == 'quiz_close':
            quiz_depth = max(0, quiz_depth - 1)
            lifted.append((kind, content))
            if quiz_depth == 0 and terse_depth > 0:
                lifted.append(('terse_open', None))
        else:
            lifted.append((kind, content))
    # Drop terse regions left holding nothing but blanks and noop annotation
    # notes (:::dev / :::instructors, e.g. the `INSTRUCTORS: (A)` answer lines
    # between consecutive hoisted quizzes).  The notes are kept, promoted to
    # top level — they are noops in every build, so the terse wrapper around
    # them was pure noise (and would strand quiz answers in terse-only should
    # quizzes later join the student/solutions products).
    out = []
    i, n = 0, len(lifted)
    while i < n:
        if lifted[i][0] == 'terse_open':
            j = i + 1
            while j < n and lifted[j][0] in ('blank', 'instructor',
                                             'author_comment'):
                j += 1
            if j < n and lifted[j][0] == 'terse_close':
                out.extend(t for t in lifted[i + 1:j] if t[0] != 'blank')
                i = j + 1
                continue
        out.append(lifted[i])
        i += 1
    return out

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


# A backtick code span in note prose; its content is opaque to Verso's markdown
# parser, so hazard scanning skips it.
_NOTE_SPAN_RE = re.compile(r'`[^`\n]+`')
# Characters that can derail Verso's markdown when they appear in plain prose:
# backticks (an unpaired one, or a ≥3 run opening a fence), `*`/`_` (Verso
# bold/emphasis — an unpaired one is a parse error), `{`/`}` (role syntax),
# `|` (tables), and any backslash.  A backslash also flags `_sf_inline_code`'s
# own `\[`/`\]` escapes: an escape means the note had stray or nested brackets
# (`[sub_nil : subseq [] []]`), which the `[…]`→span conversion garbles rather
# than translates, so such a note must stay verbatim.
_NOTE_CHAR_HAZARD_RE = re.compile(r'[`*_{}|\\]')
# Line-initial constructs that a directive body must not contain: a heading
# (Verso forbids headings inside directives), a `:::…` line (would close or
# nest directives), a `%%%` metadata block, a `>` blockquote.
_NOTE_LINE_HAZARD_RE = re.compile(r'^[ \t]*[#:%>]')


def _inline_note_body(text: str):
    """Render an author-note body as a plain markdown directive body, or return
    None when that isn't provably safe.  The only rewrite applied is
    `_sf_inline_code` (SF's `[ident]` code markup → a backtick span, stray
    brackets escaped — the same treatment ::::full prose gets); the result is
    then scanned, outside backtick code spans, for anything that could derail
    Verso's markdown parser.  Callers fall back to `_verbatim_block` on the
    *original* text, so a hazardous note is preserved verbatim rather than
    half-rewritten."""
    body = _sf_inline_code(text.strip('\n'))
    plain = _NOTE_SPAN_RE.sub(' ', body)
    if _NOTE_CHAR_HAZARD_RE.search(plain):
        return None
    if any(_NOTE_LINE_HAZARD_RE.match(l) for l in plain.split('\n')):
        return None
    return body


def _unwrap_prose_note(text: str) -> str:
    """If *text* is a single `/- … -/` block comment (a pure prose note with no
    code), return its inner content with the comment delimiters stripped;
    otherwise return *text* unchanged.  A `-- HIDE` region wrapping only a note
    would otherwise stack `/- … -/` inside the verbatim fence inside `:::hide` —
    three redundant layers, since the fence already guards the body and the
    directive already discards it.  Anything with a further `/-`/`-/` inside
    (nested comments, or a comment mixed with code) is preserved verbatim."""
    stripped = text.strip()
    if not (stripped.startswith('/-') and stripped.endswith('-/')):
        return text
    inner = stripped[2:-2]
    if '/-' in inner or '-/' in inner:
        return text
    return inner.strip('\n')


def _code_block(tag: str, text: str) -> str:
    """Wrap *text* in a fenced code block tagged *tag* (e.g. ` ```display `).  A
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
        # display, rendered by the `SFLMeta` ```display code block (see
        # SFLMeta/DisplayMath.lean).  The snippet is often deliberately ill-formed
        # ("the following definitions are ill-formed"), or an informal-proof
        # equation, or a shell transcript, so it must never become a ```lean block
        # that Verso would try to compile — ```display shows it verbatim as Lean
        # code with no elaboration.  Emitting a *named* display (rather than an
        # anonymous ``` fence) marks it so a later pass can promote the
        # genuinely-mathematical ones to ```displaymath.  The fence is grown to
        # outrun any backticks inside the snippet, like other verbatim blocks.
        self._flush_code()
        self._open_full_if_pending()
        self._append(_code_block('display', text) + '\n\n')

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
        # A header inside a source FULL region is a *full-only* heading: the
        # heading itself must go at document level (above), but a
        # :::suppressPreviousHeaderWhenTerse marker directly after it records
        # the FULL scoping so terse builds can suppress the heading (see
        # SFLMeta.Block.suppressPreviousHeaderWhenTerse).  A leaf directive
        # like :::slidebreak — empty body, always at top level (the header just
        # closed any open containers), so a literal 3-colon fence is safe.
        if self.full_depth > 0:
            self._append(':::suppressPreviousHeaderWhenTerse\n:::\n\n')

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
            # A region cannot outlive an exercise it contains: a `-- /FULL`
            # while the (nested) exercise is still open force-closes the
            # exercise first (matching the source idiom `-- FULL` /
            # `-- EX… (name)` / `-- /FULL`, which scopes just the exercise
            # banner to the full build and leaves the following theorem
            # common).  Without this, the ::::full would silently extend past
            # the exercise and swallow everything up to the next close.
            if self.in_exercise and self.full_open:
                self._append(_c_close() + '\n\n')
                self.in_exercise = False
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
        # An exercise nests inside an open (or pending) :::full — fence widths
        # are computed by _resolve_fences, so the containers never collide.
        # BCP decision 2026-07-15: the terse build should elide (almost) all
        # exercises, so a FULL-scoped "Exercises" section drops out of terse
        # *wholesale* — exercises, their supporting definitions and namespaces
        # together.  When later terse-visible material depends on a definition
        # made inside a FULL region, that definition must be made
        # terse-visible in the source, case by case (the terse generated
        # project, `lake exe sfl lf terse`, is the detector).
        # A new exercise still ends the previous one (the source sometimes
        # omits the `-- []` close before the next `-- EX`).
        if self.in_exercise:
            self._append(_c_close() + '\n\n')
            self.in_exercise = False
        self._open_full_if_pending()
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

    def _on_epigraph(self, text):
        # A section-opening quotation -> :::epigraph (rendered italic for now;
        # SFLMeta.Block.epigraph).  The body is a single line of quoted prose,
        # holds no nested directive, so a plain 3-colon fence is safe.
        self._flush_code()
        self._append(':::epigraph\n' + text + '\n:::\n\n')

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
        self._append(_c_open('hide') + '\n' + _verbatim_block(_unwrap_prose_note(text))
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
        self._append(':::answer\n' + _verbatim_block(_unwrap_prose_note(text)) + '\n:::\n\n')

    def _on_grade(self, text):
        # -- GRADE_THEOREM / GRADE_MANUAL -> :::grade.  A noop for now, but the
        # grading spec is preserved for the future grading infrastructure to
        # consume — as a backtick code span, since the spec is a single line
        # whose underscored names would trip Verso's emphasis parser as bare
        # prose.  A spec a span can't hold (a backtick, an embedded newline —
        # neither occurs in practice) falls back to the verbatim fence.
        self._flush_code()
        text = text.strip()
        if not text:
            return
        body = ('`' + text + '`' if '`' not in text and '\n' not in text
                else _verbatim_block(text))
        self._append(':::grade\n' + body + '\n:::\n\n')

    def _on_import_block(self, text):
        # Cross-chapter `import` lines (sentinels from _extract_imports) -> a
        # ```importBlock code block: rendered to the reader as a plain code
        # block, and copied verbatim into the generated student/solutions/terse
        # chapter files by the saver (SFLMeta.Block.importBlock).  Emitted at
        # the top level, never inside a deferred :::full — the terse build
        # drops :::full content wholesale, and the import must survive in all
        # three generated variants.
        self._flush_code()
        self._append(_code_block('importBlock', text) + '\n\n')

    def _on_solution_prose(self, text):
        # Prose / non-compiling solution -> :::solution block, shown only in the
        # solutions build (SFLMeta.Block.solution).  The body is inlined as plain
        # markdown when `_inline_note_body` can prove that safe (so backtick
        # identifiers render as inline code rather than a monospace block), and
        # verbatim-fenced otherwise so arbitrary illustrative code — Lean
        # snippets, `:::`, stray emphasis chars — can't perturb the parser.
        self._flush_code()
        if not text.strip():
            return
        body = _inline_note_body(text)
        if body is None:
            body = _verbatim_block(text)
        self._append(':::solution\n' + body + '\n:::\n\n')

    def _emit_noop_directive(self, directive, text):
        # Author notes become noop annotation *directives* (:::dev / :::instructors),
        # consistent with :::hide / :::answer / :::grade / :::solution.  The body is
        # inlined as plain markdown when `_inline_note_body` can prove that safe
        # (the usual case — most notes are short prose), matching the hand-authoring
        # convention (see CONTRIBUTING.md); a body containing markdown hazards
        # (unbalanced backticks/`*`/`_`, a leading `#` or `:::`, ...) that could
        # derail Verso's directive parser is instead wrapped verbatim in a fence.
        # Either way the directive discards its body at elaboration, so nothing
        # reaches the generated outputs.  :::dev and :::instructors are processed
        # identically (see SFLMeta); they differ only in name so instructor notes
        # can be treated differently later.
        # For :::dev, a leading author/urgency tag is promoted to directive
        # arguments — `:::dev "Benjamin Pierce (bcpierce00)" SOONER
        # (year := 2020)` — via `_split_dev_tags`; :::instructors deliberately
        # takes no arguments.
        self._flush_code()  # still acts as a block separator
        header = ':::' + directive
        if directive == 'dev':
            author, year, urgency, text = _split_dev_tags(text)
            if author:
                header += ' "%s"' % author
            if urgency:
                header += ' %s' % urgency
            if year:
                header += ' (year := %d)' % year
        body = _inline_note_body(text)
        if body is None:
            body = _verbatim_block(text)
        self._append(header + '\n' + body + '\n:::\n\n')

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
            elif kind == 'epigraph':
                self._on_epigraph(content)
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
            elif kind == 'import_block':
                self._on_import_block(content)
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
            # An opening directive with a name — but NOT `:::slidebreak` or
            # `:::suppressPreviousHeaderWhenTerse`, which are intentionally
            # empty self-closing markers (`:::slidebreak` / `:::`), not empty
            # containers to drop.
            m = re.match(
                r'^(:::+)(?!slidebreak\b|suppressPreviousHeaderWhenTerse\b)\w',
                lines[i])
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
    output level via a stack.  Lines inside fenced code blocks (```lean,
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


def _parse_noop_block(lines, i):
    """Parse the :::dev / :::instructors directive opening at ``lines[i]``.
    Returns ``(header, body_lines, j)`` with *j* just past the closing `:::`
    line, or None when ``lines[i]`` opens no such directive or the close is
    missing.  A backtick fence in the body is honored, so a `:::` inside a
    verbatim-fenced body is body text, not the close (an *inline* body can
    never contain a line-initial `:` — `_inline_note_body` fences those)."""
    if not re.match(r'^:::(dev|instructors)\b', lines[i]):
        return None
    n = len(lines)
    j, fence, body = i + 1, None, []
    while j < n:
        line = lines[j]
        if fence is not None:
            if line.rstrip() == fence:
                fence = None
        elif line.rstrip() == ':::':
            return lines[i], body, j + 1
        else:
            m = re.match(r'^(`{3,})[ \t]*$', line)
            if m:
                fence = m.group(1)
        body.append(line)
        j += 1
    return None


def _fuse_noop_blocks(text: str) -> str:
    """Fuse runs of consecutive :::dev / :::instructors directives (separated
    only by blank lines) into a single same-tag directive, so a run of adjacent
    author notes renders as one box rather than a stack of tiny ones.  Each
    note's body — inline markdown or a verbatim fence (see
    `_emit_noop_directive`) — is kept in its own form; the fused bodies are
    joined by a blank line, so a fenced body stays its own code block next to
    an inline neighbor.  Only directives with an identical header line fuse —
    same tag AND same author/urgency arguments (a `:::dev bcpierce00` never
    merges into a bare `:::dev` or a `:::dev SOONER`, and `dev` never merges
    into `instructors`)."""
    lines = text.split('\n')
    out, i, n = [], 0, len(lines)
    while i < n:
        parsed = _parse_noop_block(lines, i) if lines[i].startswith(':::') else None
        if not parsed:
            out.append(lines[i]); i += 1; continue
        header, body, j = parsed
        bodies = ['\n'.join(body)]
        while True:
            while j < n and lines[j].strip() == '':  # skip blanks between blocks
                j += 1
            nxt = _parse_noop_block(lines, j) if j < n and lines[j] == header else None
            if not nxt:
                break
            bodies.append('\n'.join(nxt[1]))
            j = nxt[2]
        out.append(header)
        out.append('\n\n'.join(b.strip('\n') for b in bodies))
        out.append(':::')
        out.append('')
        i = j
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


_WIC_MARKER_RE = re.compile(r'^--\s*(/?)WORKINCLASS\s*$')
_ADM_MARKER_RE = re.compile(r'^--\s*/?ADMITTED\s*$')
# The block-comment wrapper around a suggested proof that student builds show
# commented out (an empty ADMITTED region precedes it; see _convert_solution_markers).
_OPEN_COMMENT_RE = re.compile(r'^/-\s*OPEN COMMENT WHEN HIDING SOLUTIONS\s*-/$')
_CLOSE_COMMENT_RE = re.compile(r'^/-\s*CLOSE COMMENT WHEN HIDING SOLUTIONS\s*-/$')
_FT_PREFIXED_RE = re.compile(r'^(\s*)--\s*(?:FULL|TERSE):\s*(/?)(ADMITTED|WORKINCLASS)\s*$')
_DECL_START_RE = re.compile(r'^(theorem|lemma|example|def|instance|abbrev)\b')


def _normalize_workinclass_markers(src: str) -> str:
    """Reduce the marker combinations around WORKINCLASS/ADMITTED to plain
    `-- WORKINCLASS` / `-- ADMITTED` regions.

    The sources spell "exercise in the reading build, worked live in lecture"
    in two ways:

      -- FULL: ADMITTED          -- FULL          -- TERSE
      -- TERSE: WORKINCLASS      -- ADMITTED      -- WORKINCLASS
      …                          -- /FULL         -- /TERSE

    Under SFLMeta's build model `solution!` alone already produces exactly
    that matrix (student: sorry, solutions: shown, terse: sorry), so both
    spellings normalize to a bare ADMITTED region:

    1. `-- FULL: ADMITTED` -> `-- ADMITTED` (and the closing form likewise);
       `-- TERSE: WORKINCLASS` -> `-- WORKINCLASS` (ditto).
    2. A `-- FULL … -- /FULL` (or TERSE) pair enclosing *only* an
       ADMITTED/WORKINCLASS marker line is unwrapped, keeping just the marker.
    3. A WORKINCLASS marker line immediately adjacent to an ADMITTED marker
       line is dropped (`solution!` subsumes it).
    """
    lines = src.split('\n')
    # 1. Unprefix `-- FULL:`/`-- TERSE:` marker forms.
    out = []
    for line in lines:
        m = _FT_PREFIXED_RE.match(line)
        out.append(f'{m.group(1)}-- {m.group(2)}{m.group(3)}' if m else line)
    lines = out

    _wic_or_adm = re.compile(r'^--\s*/?(?:WORKINCLASS|ADMITTED)\s*$')
    # 2. Unwrap a FULL/TERSE pair that encloses *only* a marker line
    #    (`-- FULL` / `-- ADMITTED` / `-- /FULL`), keeping just the marker.
    #    Matching the exact triple (not mere adjacency) is essential: a real
    #    `-- FULL` region can legitimately begin right after `-- /WORKINCLASS`
    #    (e.g. Induction.lean) and must not be touched.
    out = []
    i, n = 0, len(lines)
    while i < n:
        mo = re.match(r'^--\s*(FULL|TERSE)\s*$', lines[i].strip())
        if mo:
            j = i + 1
            while j < n and not lines[j].strip():
                j += 1
            if j < n and _wic_or_adm.match(lines[j].strip()):
                k = j + 1
                while k < n and not lines[k].strip():
                    k += 1
                if k < n and lines[k].strip() == f'-- /{mo.group(1)}':
                    out.append(lines[j])
                    i = k + 1
                    continue
        out.append(lines[i])
        i += 1
    lines = out

    def _adjacent(idx, pattern):
        """The nearest non-blank line before or after lines[idx] matches."""
        prev = next((l for l in reversed(lines[:idx]) if l.strip()), '')
        nxt = next((l for l in lines[idx + 1:] if l.strip()), '')
        return bool(pattern.match(prev.strip()) or pattern.match(nxt.strip()))

    # 3. Drop WORKINCLASS markers subsumed by an adjacent ADMITTED region.
    lines = [l for i, l in enumerate(lines)
             if not (_WIC_MARKER_RE.match(l.strip()) and _adjacent(i, _ADM_MARKER_RE))]
    return '\n'.join(lines)


def _convert_workinclass_markers(src: str) -> str:
    """Translate `-- WORKINCLASS … -- /WORKINCLASS` proof regions into the
    `workinclass!` tactic form SFLMeta understands (shown in the student and
    solutions builds, replaced by `sorry` in the terse build):

      <inside `by`>              ->   workinclass!
        -- WORKINCLASS                  <tactics, reindented one level deeper>
        <tactics>
      -- /WORKINCLASS

      -- WORKINCLASS             ->   theorem foo … := by
      theorem foo … := by               workinclass!
        <tactics>                         <tactics, reindented>
      -- /WORKINCLASS

    A *narrative* region — one whose body contains column-0 `/- … -/` prose
    that the tokenizer renders as book text — cannot become a single code
    block; its markers are simply dropped and the body is left for normal
    tokenization (so the terse build shows the discussion; the only such
    region, IndProp's "stuck proof" demo, ends in `sorry` anyway).
    """
    lines = src.split('\n')
    out = []
    i, n = 0, len(lines)
    while i < n:
        line = lines[i]
        m = _WIC_MARKER_RE.match(line.strip())
        if not m or m.group(1) == '/':
            # An orphaned `-- /WORKINCLASS` (its opener was dropped by
            # normalization) is dropped here too.
            if m:
                i += 1
                continue
            out.append(line)
            i += 1
            continue
        j = i + 1
        body = []
        while j < n and not _WIC_MARKER_RE.match(lines[j].strip()):
            body.append(lines[j]); j += 1
        if j < n:
            j += 1   # skip the closing -- /WORKINCLASS
        if any(b.startswith('/-') for b in body):
            # Narrative region: keep the body, drop the markers.
            out.extend(body)
            i = j
            continue
        # Whole-declaration region: keep the signature (through the line
        # ending in `by`) outside the wrap.
        first_body = next((b for b in body if b.strip()), '')
        wrap_from = 0
        if _DECL_START_RE.match(first_body.strip()):
            for k, b in enumerate(body):
                if re.search(r'\bby\s*$', b):
                    wrap_from = k + 1
                    break
        out.extend(body[:wrap_from])
        wrapped = body[wrap_from:]
        while wrapped and not wrapped[-1].strip():
            wrapped.pop()
        first_wrapped = next((b for b in wrapped if b.strip()), '')
        indent = _indent_of(first_wrapped) if first_wrapped else _indent_of(line)
        out.append(indent + 'workinclass!')
        for bl in wrapped:
            # tacticSeqIndentGt: body must sit deeper than `workinclass!`.
            out.append(('  ' + bl) if bl.strip() else bl)
        i = j
    return '\n'.join(out)


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

      def f … : T :=         ->   def f … : T := solution!(
        -- ADMITDEF                 <body>)
        <body>
        -- /ADMITDEF

      <inside `by`>           ->   solution!
        -- ADMITTED                   <tactics, reindented one level deeper>
        <tactics>
        -- /ADMITTED

      <inside `by`>           ->   solution!
        -- ADMITTED                   <suggested proof, reindented>
        -- /ADMITTED
        /- OPEN COMMENT WHEN HIDING SOLUTIONS -/
        <suggested proof>
        /- CLOSE COMMENT WHEN HIDING SOLUTIONS -/

      expr := <proof>  -- ADMITTED   ->   expr := solution!(<proof>)

      <decl ending in `:=`>   ->   solution!(<term>)
        -- ADMITTED
        <term>
        -- /ADMITTED

    (`-- SOLUTION … -- /SOLUTION` blocks are handled in the tokenizer, which
    splits compilable answers from prose ones.)
    """
    lines = src.split('\n')
    out = []
    i, n = 0, len(lines)
    while i < n:
        line = lines[i]
        s = line.strip()

        # --- ADMITDEF: wrap the definition body in solution!(…) so the student
        # build stubs the definition to `:= sorry` (keeping the name defined, so
        # later references still elaborate) while the teacher build keeps the
        # body.  The `:=` may sit either on the first body line (after the
        # marker) or already on the definition's signature line above it. ---
        if s in ('-- ADMITDEF', '/- ADMITDEF -/'):
            j = i + 1
            body = []
            while j < n and lines[j].strip() not in ('-- /ADMITDEF', '/- /ADMITDEF -/'):
                body.append(lines[j]); j += 1
            # index of the last non-blank body line (where the closing `)` goes)
            last = len(body) - 1
            while last > 0 and not body[last].strip():
                last -= 1
            if body:
                m = re.match(r'^(\s*:=)\s*(.*)$', body[0])
                if m:
                    # `:=` leads the body: `:= <expr>` -> `:= solution!(<expr>)`.
                    body[0] = m.group(1) + ' solution!(' + m.group(2)
                    body[last] = body[last] + ')'
                    out.extend(body)
                else:
                    # `:=` is on the signature line already emitted above; find it
                    # (skipping blank lines) and open `solution!(` there.
                    p = len(out) - 1
                    while p >= 0 and not out[p].strip():
                        p -= 1
                    if p >= 0 and out[p].rstrip().endswith(':='):
                        out[p] = out[p].rstrip() + ' solution!('
                        body[last] = body[last] + ')'
                    out.extend(body)
            i = j + 1
            continue

        # --- ADMITTED block: a tactic sequence inside a `by` ---
        if s == '-- ADMITTED':
            j = i + 1
            body = []
            while j < n and lines[j].strip() != '-- /ADMITTED':
                body.append(lines[j]); j += 1
            resume = j + 1
            # An interleaved bare `-- FULL`/`-- TERSE` marker (the source's
            # "back to full mode for the GRADE/[] lines" idiom, cf. beq_eq in
            # Tactics) must stay a structural marker, not become a comment
            # inside the code block: hoist it out and re-emit it after.
            trailing = [b for b in body
                        if re.fullmatch(r'--\s*/?(?:FULL|TERSE)', b.strip())]
            body = [b for b in body
                    if not re.fullmatch(r'--\s*/?(?:FULL|TERSE)', b.strip())]
            # A region whose declaration ends in a bare `:=` holds a *term*
            # proof, not tactics (cf. mstar'' in IndPropRegexp): wrap it in
            # the parenthesized form `solution!(<term>)` instead of emitting
            # the tactic form after a nonexistent `by`.
            p = len(out) - 1
            while p >= 0 and not out[p].strip():
                p -= 1
            if (p >= 0 and out[p].rstrip().endswith(':=')
                    and any(b.strip() for b in body)):
                first = next(k for k, b in enumerate(body) if b.strip())
                last = len(body) - 1
                while last > first and not body[last].strip():
                    last -= 1
                ind = _indent_of(body[first])
                body[first] = ind + 'solution!(' + body[first].strip()
                body[last] = body[last] + ')'
                out.extend(body[:last + 1])
                out.extend(trailing)
                i = resume
                continue
            # An *empty* region followed by an `OPEN COMMENT WHEN HIDING
            # SOLUTIONS` … `CLOSE COMMENT …` wrapper (the source idiom for
            # "students see the suggested proof as a comment", cf. the
            # NoStutter examples in IndProp) takes the wrapped suggested
            # proof as its `solution!` body.
            if not any(b.strip() for b in body):
                k = resume
                while k < n and not lines[k].strip():
                    k += 1
                if k < n and _OPEN_COMMENT_RE.match(lines[k].strip()):
                    k += 1
                    wrapped = []
                    while k < n and not _CLOSE_COMMENT_RE.match(lines[k].strip()):
                        wrapped.append(lines[k]); k += 1
                    if k < n:
                        body = wrapped
                        resume = k + 1
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
            out.extend(trailing)
            i = resume
            continue

        # --- trailing ADMITTED: a one-line proof term ---
        if s.endswith('-- ADMITTED') and s != '-- ADMITTED':
            if ':=' in line:
                out.append(re.sub(r':=\s*(.*?)\s*--\s*ADMITTED\s*$',
                                  lambda m: ':= solution!(' + m.group(1) + ')', line))
            else:
                # The `:=` sits on an earlier line (`theorem foo ... :=\n
                #   by rfl -- ADMITTED`): wrap just this line's proof term,
                # provided the previous non-blank line really ends with `:=`.
                p = len(out) - 1
                while p >= 0 and not out[p].strip():
                    p -= 1
                m = re.match(r'^(\s*)(.*?)\s*--\s*ADMITTED\s*$', line)
                if p >= 0 and out[p].rstrip().endswith(':=') and m:
                    out.append(m.group(1) + 'solution!(' + m.group(2) + ')')
                else:
                    out.append(line)
            i += 1
            continue

        out.append(line)
        i += 1
    return '\n'.join(out)


# ---------------------------------------------------------------------------
# Rocq front-end (.v source -> code-forward Lean-comment dialect)
# ---------------------------------------------------------------------------
# Converts ONLY the comment/marker layer of an SF Rocq chapter into the Lean
# dialect that `tokenize` (and the marker pre-passes) already consume; the code
# lines pass through as Coq, to be translated by hand in the generated Verso
# file.  The contract is LOSSLESSNESS: every comment routes somewhere (prose,
# dev note, marker, or code position) — the only silent drops are `####…`
# separator lines, which are pure decoration (see "Intentionally dropped" in
# CLAUDE.md).  The .v marker vocabulary is the same as the Lean dialect's
# (FULL/TERSE/EX/HIDE/QUIZ/SOLUTION/ADMITTED/…), so most markers just change
# delimiters.  Departures, all deliberate:
#
#   * `(** … *)` coqdoc prose -> `/- … -/`; `(** * Title *)` star headings ->
#     `/- # Title -/` (hash count = star count); the first heading, when it
#     matches `<Stem>: …`, becomes the chapter-title comment.
#   * `<< … >>` coqdoc verbatim -> `[[ … ]]` (the display-code form the
#     tokenizer already knows).  Content inside `[[ ]]`/`<< >>` is never
#     rescanned, so Coq comments in display snippets survive untouched.
#   * a `(* … *)` comment nested inside coqdoc prose is hoisted out of the
#     prose into its own block (the .lean pipeline would otherwise *strip*
#     embedded dev-note lines — see _strip_dev_note_lines).
#   * single-star `(* … *)` comments are author-internal by coqdoc convention:
#     tagged ones (`BCP:`, `LATER:`, `HIDE:`, `INSTRUCTORS:`, …) route as-is
#     (-> :::dev / :::instructor); untagged ones at prose position are
#     *probable errors* and get a `COMMENT:` banner naming their origin so the
#     manual pass can triage them; untagged ones inside a code run stay in
#     code position (ordinary code commentary).
#   * the bare `(* INSTRUCTORS *)` … `(* /INSTRUCTORS *)` *region* (quiz
#     answers in Imp; no line-form analogue) is mapped to `-- HIDE` … `-- /HIDE`
#     (same verbatim-capture treatment; renders as the quiz's :::answer).
#   * HIDEFROMHTML / HIDEFROMADVANCED markers (bare or `TERSE:`/`ADVANCED:`
#     prefixed) are dropped outright at conversion — the region semantics are
#     not honored anywhere downstream, and dropping here also keeps the marker
#     word out of verbatim-captured bodies.  The enclosed content is kept.
#   * `-/` / `/-` occurring inside comment text would break the emitted Lean
#     comment; a space is inserted (`- /`, `/ -`) — visible, harmless.

_RQ_STRUCT_MARKERS = (
    r"EX\d+[A-Za-z!?]*[ \t]+\(\w[\w' \-]*\)"    # exercise open: EX2M? (name)
    r'|\[\]'                                    # exercise close
    r'|GRADE_\S.*'                              # grading spec (rest of comment)
    r'|\*\*\*'                                  # slide break
    r'|/?(?:HIDEFROMADVANCED|HIDEFROMHTML|FULL|TERSE|HIDE|QUIZ|FOLD'
    r'|QUIETSOLUTION|SOLUTION|WORKINCLASS|ADMITTED|ADMITDEF|INSTRUCTORS)')

# A whole-comment structural marker, optionally mode-prefixed (`TERSE:
# HIDEFROMHTML`, `FULL: ADMITTED`, `ADVANCED: HIDEFROMHTML`, `TERSE: ***`).
# Matched against the comment body flattened to single-space (so `(* FULL *)`
# spacing/newlines don't matter).  NB `HIDE`/`FULL`/… alternatives are bare
# (end-anchored): `HIDE: prose` and `FULL: prose` do NOT match — those are
# dev-note / mode-prefixed-prose forms handled elsewhere.
_RQ_MARKER_BODY_RE = re.compile(
    r'^(?:(FULL|TERSE|ADVANCED):[ \t]*)?(' + _RQ_STRUCT_MARKERS + r')$')

# Marker comment embedded in a code line (`Proof. (* ADMITTED *) auto. Qed.`,
# `  (* ADMITDEF *) :=`): hoisted onto its own `-- MARKER` line so the region
# machinery sees it.  EX opens and INSTRUCTORS regions never occur inline.
_RQ_INLINE_MARKER_RE = re.compile(
    r'\(\*[ \t]*((?:(?:FULL|TERSE|ADVANCED):[ \t]*)?'
    r'(?:GRADE_[^*]*|\[\]'
    r'|/?(?:HIDEFROMADVANCED|HIDEFROMHTML|FULL|TERSE|HIDE|QUIZ|FOLD'
    r'|QUIETSOLUTION|SOLUTION|WORKINCLASS|ADMITTED|ADMITDEF)))[ \t]*\*\)')

_RQ_UNTAGGED_BANNER = (
    'COMMENT: [untagged (* .. *) comment at prose position in the Rocq '
    'source -- probably an error there; decide whether it is book prose '
    'or an author note]')


def _rq_read_comment(lines, i, j):
    """Read the (possibly nested, multi-line) Rocq comment whose `(*` opens at
    lines[i][j:].  Returns (body, end_line, end_col): *body* is the text between
    the outer delimiters (inner `(* … *)` delimiters kept verbatim), end_col is
    the index just past the closing `*)` on lines[end_line]."""
    depth = 0
    buf = []
    li, ci = i, j
    n = len(lines)
    while li < n:
        line = lines[li]
        while ci < len(line):
            if line.startswith('(*', ci):
                depth += 1
                if depth > 1:
                    buf.append('(*')
                ci += 2
            elif line.startswith('*)', ci) and depth > 0:
                depth -= 1
                if depth == 0:
                    return ''.join(buf), li, ci + 2
                buf.append('*)')
                ci += 2
            else:
                buf.append(line[ci])
                ci += 1
        buf.append('\n')
        li += 1
        ci = 0
    # Unterminated comment (malformed source): treat rest of file as the body.
    return ''.join(buf), n - 1, len(lines[-1]) if lines else 0


def _rq_balance(line):
    """Net `(*`-minus-`*)` count of *line* (for detecting a comment opened
    mid-line that spills onto later lines)."""
    depth, j = 0, 0
    while j < len(line) - 1:
        if line.startswith('(*', j):
            depth += 1
            j += 2
        elif line.startswith('*)', j):
            depth -= 1
            j += 2
        else:
            j += 1
    return depth


def _rq_body_text(body):
    """Normalize a comment body: strip the delimiter-adjacent padding and
    dedent continuation lines (coqdoc bodies are aligned under the `(** `)."""
    first, _, rest = body.partition('\n')
    first = first.strip()
    rest = textwrap.dedent(rest).rstrip() if rest.strip() else ''
    if first and rest:
        return first + '\n' + rest
    return first or rest


def _rq_escape_lean_delims(text):
    """Break `-/` / `/-` sequences that would derail the emitted `/- … -/`."""
    return text.replace('-/', '- /').replace('/-', '/ -')


def _rq_block_lines(text, indent=''):
    """Emit *text* as a Lean `/- … -/` block comment (list of lines)."""
    text = _rq_escape_lean_delims(text)
    ls = text.split('\n')
    if len(ls) == 1:
        return [f'{indent}/- {ls[0]} -/']
    out = [f'{indent}/- {ls[0]}']
    out.extend(indent + l if l.strip() else '' for l in ls[1:])
    out[-1] = (out[-1] + ' -/') if out[-1].strip() else (indent + '-/')
    return out


def _rq_marker_line(m):
    """Render a _RQ_MARKER_BODY_RE match as its `-- MARKER` line form, or
    None for a marker that is dropped outright at conversion."""
    prefix, marker = m.group(1), m.group(2)
    if marker.lstrip('/') in ('HIDEFROMHTML', 'HIDEFROMADVANCED'):
        # Region semantics are not honored anywhere downstream: dropping the
        # marker and keeping the enclosed content is the intended behavior
        # (see CLAUDE.md).  Dropping *here*, rather than relying on the
        # downstream prose-level drops, also keeps the marker word out of
        # verbatim-captured bodies (hide / answer / solution regions) and
        # covers the `ADVANCED:`/`TERSE:`-prefixed spellings uniformly.
        return None
    if marker.lstrip('/') == 'INSTRUCTORS':
        # Bare region form (quiz answers): no line-form analogue; HIDE gives
        # the same verbatim-capture treatment (-> :::answer inside a quiz).
        marker = marker.replace('INSTRUCTORS', 'HIDE')
    marker = ' '.join(marker.split())
    return f'-- {prefix}: {marker}' if prefix else f'-- {marker}'


def _rq_flat(body):
    """Comment body flattened for marker matching (coqdoc star stripped,
    whitespace collapsed)."""
    core = body[1:] if body.startswith('*') else body
    return ' '.join(core.split())


def _rq_track_hide(marker_line, state):
    """Maintain state['hide_depth'] across emitted -- HIDE / -- /HIDE markers
    (used to suppress the untagged-comment triage banner inside hide regions).
    Tolerates a dropped (None) marker."""
    s = marker_line.strip() if marker_line else ''
    if s == '-- HIDE':
        state['hide_depth'] = state.get('hide_depth', 0) + 1
    elif s == '-- /HIDE':
        state['hide_depth'] = max(0, state.get('hide_depth', 0) - 1)
    return marker_line


def _rq_hoist_inline_markers(line):
    """Split marker comments embedded in a code line onto their own lines."""
    ms = list(_RQ_INLINE_MARKER_RE.finditer(line))
    if not ms:
        return [line]
    indent = _indent_of(line)
    out, pos = [], 0
    for m in ms:
        before = line[pos:m.start()]
        if before.strip():
            out.append(before.rstrip())
        mb = _RQ_MARKER_BODY_RE.match(' '.join(m.group(1).split()))
        ml = _rq_marker_line(mb)
        if ml is not None:
            out.append(ml)
        pos = m.end()
    rest = line[pos:]
    if rest.strip():
        out.append(indent + rest.strip())
    return out


def _rq_classify_standalone(body, stem, state):
    """Emit a standalone (own-line) Rocq comment in the Lean dialect.

    Markers are handled by the caller; this routes prose / notes:
    coqdoc `(** … *)` -> book prose (headings, displays, nested-note hoisting);
    single-star `(* … *)` -> author-internal (dev-tagged as-is, mode-prefixed
    prose as-is, untagged banner-flagged)."""
    is_coqdoc = body.startswith('*')
    text = _rq_body_text(body[1:] if is_coqdoc else body)
    if not text.strip():
        return []
    if _SEPARATOR_LINE_RE.match(text.strip()):
        return []                      # ####… divider: pure decoration
    if is_coqdoc:
        return _rq_emit_coqdoc(text, stem, state)
    if re.match(r'^=+>', text):
        # `(* ==> monday : day *)` output annotation after a Compute/Check.
        # Emit as `--` comment lines so it stays inside the adjacent code
        # block: the expected output matters to whoever rewrites the code
        # (once the block elaborates live, the annotation can be deleted).
        return ['-- ' + l if l.strip() else '--' for l in text.split('\n')]
    if re.match(r'^(FULL|TERSE):\s', text):
        # Mode-prefixed prose in single-star form: shown in that build mode.
        return _rq_block_lines(text)
    if _BLOCK_DEV_RE.match(text) or _BLOCK_INSTRUCTOR_RE.match(text):
        return _rq_block_lines(text)
    if state.get('hide_depth', 0) > 0:
        # Inside a -- HIDE region everything is captured verbatim downstream;
        # an untagged comment there is unremarkable, so no triage banner.
        return _rq_block_lines(text)
    return _rq_block_lines(_RQ_UNTAGGED_BANNER + '\n' + text)


def _rq_emit_coqdoc(text, stem, state):
    """Emit a coqdoc `(** … *)` body as Lean-dialect prose lines."""
    lines = text.split('\n')
    out = []
    start = 0
    hm = re.match(r'^(\*{1,6})[ \t]+(\S.*)$', lines[0])
    if hm:
        title = hm.group(2).strip()
        if state.get('title_pending') and stem and title.startswith(stem + ':'):
            out.extend(_rq_block_lines(title))   # chapter-title comment form
        else:
            out.extend(_rq_block_lines('#' * len(hm.group(1)) + ' ' + title))
        state['title_pending'] = False
        start = 1
    prose = []

    def flush():
        seg = list(prose)
        prose.clear()
        while seg and not seg[0].strip():
            seg.pop(0)
        while seg and not seg[-1].strip():
            seg.pop()
        if seg:
            out.extend(_rq_block_lines('\n'.join(seg)))

    close_map = {'[[': ']]', '[[[': ']]]', '<<': '>>'}
    i = start
    n = len(lines)
    while i < n:
        l = lines[i]
        s = l.strip()
        if s in close_map:
            # Display code (`[[ … ]]` or coqdoc `<< … >>` -> `[[ … ]]`): the
            # content is Coq text, passed through with no comment rescanning.
            closer = close_map[s]
            prose.append('[[' if s == '<<' else s)
            i += 1
            while i < n and lines[i].strip() != closer:
                prose.append(lines[i])
                i += 1
            if i < n:
                prose.append(']]' if closer == '>>' else lines[i].strip())
                i += 1
            continue
        nm = re.match(r'^(\s*)\(\*', l)
        if nm:
            # A note nested inside book prose: hoist it out to its own block
            # (the .lean pipeline strips embedded dev-note lines, so leaving
            # it inline would LOSE it downstream).
            body2, li2, ci2 = _rq_read_comment(lines, i, len(nm.group(1)))
            trailing2 = lines[li2][ci2:]
            flush()
            mm2 = _RQ_MARKER_BODY_RE.match(_rq_flat(body2)) if body2.strip() else None
            if mm2:
                ml2 = _rq_marker_line(mm2)
                if ml2 is not None:
                    out.append(ml2)
            else:
                out.extend(_rq_classify_standalone(body2, stem, state))
            if trailing2.strip():
                prose.append(trailing2)
            i = li2 + 1
            continue
        prose.append(l)
        i += 1
    flush()
    return out


def rocq_to_lean_dialect(src, stem=None):
    """Convert the comment/marker layer of Rocq chapter source *src* to the
    code-forward Lean-comment dialect; code lines pass through unchanged."""
    lines = src.split('\n')
    out = []
    state = {'title_pending': bool(stem), 'hide_depth': 0}
    prev_code = False   # last emitted line was code (for in-proof commentary)
    i, n = 0, len(lines)
    while i < n:
        line = lines[i]
        if not line.strip():
            out.append('')
            prev_code = False
            i += 1
            continue
        m = re.match(r'^(\s*)\(\*', line)
        if m:
            indent = m.group(1)
            body, li, ci = _rq_read_comment(lines, i, len(indent))
            trailing = lines[li][ci:]
            mm = _RQ_MARKER_BODY_RE.match(_rq_flat(body)) if body.strip() else None
            if trailing.strip():
                # Comment glued to code on its closing line.
                if mm:
                    # `(* ADMITTED *) Proof. …`: marker on its own line, then
                    # reprocess the remainder (it may hold more comments).
                    ml = _rq_track_hide(_rq_marker_line(mm), state)
                    if ml is not None:
                        out.append(ml)
                    lines[li] = indent + trailing.lstrip()
                    i = li
                else:
                    # Non-marker comment leading a code line: code territory.
                    out.extend(lines[i:li])
                    out.extend(_rq_hoist_inline_markers(lines[li]))
                    prev_code = True
                    i = li + 1
                continue
            if mm:
                ml = _rq_track_hide(_rq_marker_line(mm), state)
                if ml is not None:
                    out.append(ml)
            elif indent and prev_code:
                # Indented commentary directly continuing a code run (between
                # tactics): keep it in code position, as the tokenizer expects.
                out.extend(_rq_block_lines(
                    _rq_body_text(body[1:] if body.startswith('*') else body),
                    indent))
                prev_code = True
            else:
                out.extend(_rq_classify_standalone(body, stem, state))
                prev_code = False
            i = li + 1
            continue
        # Code line.  A comment opened mid-line that spills onto later lines is
        # consumed verbatim with them (it is Coq-code commentary).
        bal = _rq_balance(line)
        if bal > 0:
            j = i
            while j + 1 < n and bal > 0:
                j += 1
                bal += _rq_balance(lines[j])
            out.extend(lines[i:j + 1])
            prev_code = True
            i = j + 1
            continue
        out.extend(_rq_hoist_inline_markers(line))
        prev_code = True
        i += 1
    text = '\n'.join(out)
    text = re.sub(r'\n{3,}', '\n\n', text)          # at most one blank line
    return text.strip('\n') + '\n'


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
        title=title, file=file_key, extra_imports='\n'.join(extra_imports),
        doc_options=DOC_LEVEL_OPTIONS.get(file_key, ''))
    if has_prelude:
        header = 'prelude\n' + header
    # Normalize block-comment markers (/- EX … -/, /- /TERSE -/, …) to line form.
    body_src = _normalize_block_markers(body_src)
    # Reduce FULL/TERSE-wrapped and FULL:/TERSE:-prefixed ADMITTED/WORKINCLASS
    # combinations to bare regions, then rewrite WORKINCLASS regions into
    # `workinclass!` and solution markers (ADMITDEF/ADMITTED/SOLUTION) into the
    # in-code forms SFLMeta understands before tokenizing.
    body_src = _normalize_workinclass_markers(body_src)
    body_src = _convert_workinclass_markers(body_src)
    body_src = _convert_solution_markers(body_src)
    tokens = tokenize(body_src)
    tokens = _hoist_from_terse(tokens)
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
    parser.add_argument('src', metavar='SOURCE.{lean,v}',
                        help='code-forward chapter source (e.g. LF/Basics.lean),'
                             ' or a Rocq chapter (.v) for a rough-draft conversion')
    parser.add_argument('dst', metavar='DEST.lean', nargs='?',
                        help="output Verso file (default: same dir, stem + 'Verso')")
    parser.add_argument('--title', default=None,
                        help='override the #doc title (auto-detected by default)')
    parser.add_argument('--emit-lean', metavar='PATH', default=None,
                        help='(.v input only) also write the intermediate'
                             ' Lean-dialect skeleton, for use with the'
                             ' check_verso_*.py scripts')
    args = parser.parse_args()

    src_path = pathlib.Path(args.src)
    if not src_path.exists():
        sys.exit(f'Error: source file not found: {src_path}')

    dst_path = (pathlib.Path(args.dst) if args.dst
                else src_path.with_stem(src_path.stem + 'Verso').with_suffix('.lean'))

    src_text = src_path.read_text()
    file_key = src_path.stem   # e.g. "Basics"
    if src_path.suffix == '.v':
        src_text = rocq_to_lean_dialect(src_text, file_key)
        if args.emit_lean:
            pathlib.Path(args.emit_lean).write_text(src_text)
            print(f'Written {args.emit_lean}  (Lean-dialect skeleton)')
    elif args.emit_lean:
        sys.exit('Error: --emit-lean only applies to a .v source')
    title = args.title or extract_title(src_text, file_key)

    result = convert(src_text, title, file_key)
    # Write-if-different: only touch the output (and thus bump its mtime, which
    # forces `lake` to re-elaborate every chapter that imports it) when the
    # generated content actually changed.  A comment-only edit whose tokens are
    # dropped by to_verso, or a change to this script that doesn't affect a
    # given chapter, then costs zero downstream Lean rebuilds.
    if dst_path.exists() and dst_path.read_text() == result:
        print(f'Unchanged {dst_path}  (skipped write)')
    else:
        dst_path.write_text(result)
        print(f'Written {dst_path}  (title: {title!r}, file key: {file_key!r})')


if __name__ == '__main__':
    main()
