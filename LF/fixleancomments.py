#!/usr/bin/env python3
"""
Normalize comment styles in a .lean course source file.

Rules (see conversation for the authoritative spec):

  1. `-- FULL` / `-- /FULL` markers stay as-is.
  2. Inside a FULL block, contiguous runs of *prose* line-comments
     (`-- text`, including blank `--` lines) are collapsed into a
     multi-line `/- ... -/` block comment. Marker lines inside FULL
     (TERSE, EX, ADMIT*, HIDEFROMHTML, RAB, GRADE_THEOREM, section
     dividers `######`) are left alone and act as separators between
     prose runs.
  3. `-- TERSE: foo` (plus continuation lines of the form `--  <spaces>text`)
     is collapsed to one line:  `-- TERSE: /- foo ... -/`
     If a TERSE continuation contains the keyword `FULL` (as on line 67
     of Basics.lean), that token ends TERSE and begins a new FULL block.
  4. `/- JC: ... -/` block comments (possibly multi-line) are rewritten
     as `-- JC: ...` line comments.
  5. Other markers and code lines are untouched.
"""

from __future__ import annotations

import re
import sys
from typing import List, Tuple

# --- Regexes -----------------------------------------------------------------

FULL_START_RE  = re.compile(r"^\s*--\s*FULL\s*$")
FULL_END_RE    = re.compile(r"^\s*--\s*/FULL\s*$")

TERSE_RE       = re.compile(r"^(\s*)--\s*TERSE:\s*(.*)$")
# A TERSE continuation: `--` followed by >=3 spaces of indent, then text.
TERSE_CONT_RE  = re.compile(r"^\s*--\s{3,}(\S.*)$")

# Any plain line comment: captures indent and body (stripped of leading
# single space, if present).
LINE_COMMENT_RE = re.compile(r"^(\s*)--( ?)(.*)$")

# Markers that must NOT be wrapped in /- -/ when encountered inside a FULL block.
FULL_PROTECTED_PATTERNS = [
    re.compile(r"^\s*--\s*/?TERSE\b"),
    re.compile(r"^\s*--\s*/?HIDEFROMHTML\s*$"),
    re.compile(r"^\s*--\s*/?HIDEFROMADVANCED\s*$"),
    re.compile(r"^\s*--\s*/?HIDE\s*$"),
    re.compile(r"^\s*--\s*/?QUIZ\s*$"),
    re.compile(r"^\s*--\s*/?SOLUTION\s*$"),
    re.compile(r"^\s*--\s*/?QUIETSOLUTION\s*$"),
    re.compile(r"^\s*--\s*/?WORKINCLASS\s*$"),
    re.compile(r"^\s*--\s*EX\d+[!?]*[A-Z]*\??\b"),
    re.compile(r"^\s*--\s*/?ADMIT(DEF|TED)?\b"),
    re.compile(r"^\s*--\s*GRADE_THEOREM\b"),
    re.compile(r"^\s*--\s*GRADE_MANUAL\b"),
    re.compile(r"^\s*--\s*RAB\b"),
    re.compile(r"^\s*--\s*RADDITION\b"),
    re.compile(r"^\s*--\s*JC\b"),
    re.compile(r"^\s*--\s*BCP\b"),
    re.compile(r"^\s*--\s*MMG\b"),
    re.compile(r"^\s*--\s*APT\b"),
    re.compile(r"^\s*--\s*DHS\b"),
    re.compile(r"^\s*--\s*TODO\b"),
    re.compile(r"^\s*--\s*SOONER\b"),
    re.compile(r"^\s*--\s*LATER\b"),
    # Grader terminators: `-- []`, `-- [word, word]`. Stay as `--`.
    re.compile(r"^\s*--\s*\[[^\]]*\]\s*$"),
    re.compile(r"^\s*--\s*INSTRUCTORS\b"),
    re.compile(r"^\s*--\s*/?FULL\s*$"),
]

# Block comments we convert to `--`.
JC_BLOCK_START_RE = re.compile(r"^(\s*)/-\s*(JC:.*)$")
JC_BLOCK_INLINE_RE = re.compile(r"^(\s*)/-\s*(JC:.*?)\s*-/\s*$")
BLOCK_END_RE = re.compile(r"^(.*?)\s*-/\s*$")


# --- Helpers -----------------------------------------------------------------

def is_protected_in_full(line: str) -> bool:
    return any(p.match(line) for p in FULL_PROTECTED_PATTERNS)


def _is_structural_non_author_marker(line: str) -> bool:
    """True if `line` is a protected marker that is NOT an author note.
    Used by the author-note absorption loop to know when to stop."""
    if AUTHOR_NOTE_RE.match(line):
        return False
    return is_protected_in_full(line)


def is_comment_line(line: str) -> bool:
    stripped = line.lstrip()
    return stripped.startswith("--")


def strip_comment_prefix(line: str) -> str:
    """`  -- foo` -> `foo`; blank `--` -> `` ."""
    m = LINE_COMMENT_RE.match(line)
    return m.group(3) if m else line


def flush_prose(prose: List[str], indent: str, out: List[str]) -> None:
    """Emit a prose run as a /- -/ block. Single-line bodies stay on one
    line (`<indent>/- body -/`); multi-line bodies use the 3-line form.
    Trims leading/trailing blanks."""
    while prose and prose[0] == "":
        prose.pop(0)
    while prose and prose[-1] == "":
        prose.pop()
    if not prose:
        return
    if len(prose) == 1:
        out.append(f"{indent}/- {prose[0]} -/")
        return
    out.append(f"{indent}/-")
    for p in prose:
        out.append(f"{indent}  {p}" if p else "")
    out.append(f"{indent}-/")


# --- TERSE handling ----------------------------------------------------------

def handle_terse(
    lines: List[str], i: int, out: List[str]
) -> Tuple[int, bool]:
    """
    Collapse a TERSE block starting at lines[i] into a single
    `-- TERSE: /- ... -/` line.

    Returns (new_index, injected_full_start). `injected_full_start` is True
    if a continuation contained the keyword `FULL`, in which case the
    remainder of that continuation should be treated as the first prose
    line of a new FULL block (the caller handles the block).
    """
    m = TERSE_RE.match(lines[i])
    assert m is not None
    indent = m.group(1)
    parts: List[str] = []
    first = m.group(2).strip()
    if first:
        parts.append(first)
    i += 1

    injected_full_rest: str = ""
    while i < len(lines):
        cm = TERSE_CONT_RE.match(lines[i])
        if not cm:
            break
        text = cm.group(1).rstrip()
        # Detect inline FULL keyword inside continuation.
        fm = re.match(r"^FULL\b\s*(.*)$", text)
        if fm:
            injected_full_rest = fm.group(1).strip()
            i += 1
            break
        parts.append(text)
        i += 1

    body = " ".join(parts).strip()
    # If the body is already wrapped in `/- ... -/`, strip the wrapper so
    # we don't produce `-- TERSE: /- /- body -/ -/` when re-running the
    # formatter on an already-formatted file.
    bm = re.match(r"^/-\s*(.*?)\s*-/$", body)
    if bm:
        body = bm.group(1).strip()
    if body:
        out.append(f"{indent}-- TERSE: /- {body} -/")
    else:
        out.append(f"{indent}-- TERSE:")

    if injected_full_rest != "":
        # Emit the FULL start marker; the caller will pick up FULL-block
        # processing on return. We also need to stash the leftover text
        # as a synthetic prose line — simplest is to splice it back into
        # `lines` at position `i`. But we can't mutate the caller's list
        # safely from here; instead, return the rest via a sentinel.
        out.append(f"{indent}-- FULL")
        return i, injected_full_rest  # type: ignore[return-value]
    return i, ""  # type: ignore[return-value]


# --- FULL block body ---------------------------------------------------------

AUTHOR_NOTE_RE = re.compile(r"^\s*--\s*(JC|RAB|RADDITION|BCP|INSTRUCTORS|SOONER|LATER|MMG|APT|DHS|TODO)\b")


def process_full_body(body_lines: List[str], out: List[str]) -> None:
    """Process lines between `-- FULL` and `-- /FULL`."""
    prose: List[str] = []
    prose_indent: str = ""
    i = 0
    n = len(body_lines)
    while i < n:
        line = body_lines[i]

        # TERSE inside FULL -> collapse, then keep going.
        if TERSE_RE.match(line):
            if prose:
                flush_prose(prose, prose_indent, out)
                prose = []
            new_i, leftover = handle_terse(body_lines, i, out)
            i = new_i
            if leftover:
                prose_indent = _leading_ws(line)
                prose.append(leftover)
            continue

        # Author note (JC/RAB/BCP/INSTRUCTORS): emit the header, then greedily
        # absorb following `--` comment lines as continuation of the note
        # (unless they're a different structural marker or another author note).
        if AUTHOR_NOTE_RE.match(line):
            if prose:
                flush_prose(prose, prose_indent, out)
                prose = []
            out.append(line)
            i += 1
            while i < n:
                nxt = body_lines[i]
                if (nxt.strip() == ""
                        or not is_comment_line(nxt)
                        or AUTHOR_NOTE_RE.match(nxt)
                        or FULL_START_RE.match(nxt)
                        or FULL_END_RE.match(nxt)
                        or TERSE_RE.match(nxt)
                        or _is_structural_non_author_marker(nxt)):
                    break
                out.append(nxt)
                i += 1
            continue

        # Protected marker -> flush prose and pass through.
        if is_protected_in_full(line):
            if prose:
                flush_prose(prose, prose_indent, out)
                prose = []
            out.append(line)
            i += 1
            continue

        # Non-comment line: flush and pass through verbatim.
        if not is_comment_line(line) and line.strip() != "":
            if prose:
                flush_prose(prose, prose_indent, out)
                prose = []
            out.append(line)
            i += 1
            continue

        # Blank source line: flush and pass through.
        if line.strip() == "":
            if prose:
                flush_prose(prose, prose_indent, out)
                prose = []
            out.append(line)
            i += 1
            continue

        # Plain line comment = prose. Accumulate.
        if not prose:
            prose_indent = _leading_ws(line)
        prose.append(strip_comment_prefix(line))
        i += 1

    if prose:
        flush_prose(prose, prose_indent, out)


def _leading_ws(line: str) -> str:
    m = re.match(r"^(\s*)", line)
    return m.group(1) if m else ""


# --- Top-level pass ----------------------------------------------------------

def convert_jc_blocks(lines: List[str]) -> List[str]:
    """Pre-pass: convert every `/- JC: ... -/` block comment to `-- JC:` lines.
    Runs before FULL-block processing so JC blocks anywhere in the file
    (including inside FULL regions) are handled uniformly."""
    out: List[str] = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        m = JC_BLOCK_INLINE_RE.match(line)
        if m:
            out.append(f"{m.group(1)}-- {m.group(2)}")
            i += 1
            continue
        m = JC_BLOCK_START_RE.match(line)
        if m:
            indent = m.group(1)
            out.append(f"{indent}-- {m.group(2).rstrip()}")
            i += 1
            while i < n:
                em = BLOCK_END_RE.match(lines[i])
                if em:
                    tail = em.group(1).strip()
                    if tail:
                        out.append(f"{indent}-- {tail}")
                    i += 1
                    break
                out.append(f"{indent}-- {lines[i].strip()}")
                i += 1
            continue
        out.append(line)
        i += 1
    return out


def format_lean_comments(lines: List[str]) -> List[str]:
    lines = convert_jc_blocks(lines)
    out: List[str] = []
    i = 0
    n = len(lines)

    # We collect runs of lines between FULL markers (i.e. "outside FULL")
    # and run them through process_full_body, which does prose wrapping,
    # TERSE handling, author-note absorption, and marker passthrough
    # uniformly. When we hit `-- FULL`, we flush the outside run, emit
    # the marker, collect the inside run, run it through the same
    # processor, then emit `-- /FULL`. This unifies outside- and
    # inside-FULL treatment — the only difference is the surrounding
    # markers — which is exactly what the user wants: all prose becomes
    # `/- -/`, all `--` lines are removable.
    outside_buf: List[str] = []

    def flush_outside() -> None:
        if outside_buf:
            process_full_body(outside_buf, out)
            outside_buf.clear()

    while i < n:
        line = lines[i]

        if FULL_START_RE.match(line):
            flush_outside()
            out.append(line)
            i += 1
            body: List[str] = []
            while i < n and not FULL_END_RE.match(lines[i]):
                body.append(lines[i])
                i += 1
            process_full_body(body, out)
            if i < n and FULL_END_RE.match(lines[i]):
                out.append(lines[i])
                i += 1
            continue

        # TERSE at top level might inject a FULL via its continuation.
        # Since process_full_body already handles TERSE, we can let it do
        # the work by just buffering the line. But the FULL-injection
        # case needs the outer loop to catch the resulting `-- FULL` and
        # find its matching `-- /FULL`. To keep that behavior correct,
        # detect it here rather than deferring.
        if TERSE_RE.match(line):
            flush_outside()
            new_i, leftover = handle_terse(lines, i, out)
            i = new_i
            if leftover:
                body = [f"-- {leftover}"]
                while i < n and not FULL_END_RE.match(lines[i]):
                    body.append(lines[i])
                    i += 1
                process_full_body(body, out)
                if i < n and FULL_END_RE.match(lines[i]):
                    out.append(lines[i])
                    i += 1
            continue

        # Anything else: accumulate for the outside-FULL processor.
        outside_buf.append(line)
        i += 1

    flush_outside()
    return out


# --- CLI ---------------------------------------------------------------------

def main() -> int:
    import argparse
    from lean_cli import process_files

    parser = argparse.ArgumentParser(
        prog="format_lean_comments.py",
        description="Normalize comment styles in .lean course source files. "
                    "Output is written to <out-dir>/<stem>.formatted.lean for "
                    "each input file. If a file is in a directory argument, "
                    "all .lean files in that directory (non-recursive) are "
                    "processed.",
    )
    parser.add_argument(
        "paths", nargs="*", metavar="FILE_OR_DIR",
        help="one or more .lean files and/or directories containing .lean files",
    )
    parser.add_argument(
        "--out-dir", "-o", required=True,
        help="directory to write formatted output into (created if missing)",
    )
    parser.add_argument(
        "--force", "-f", action="store_true",
        help="overwrite existing output files instead of skipping them",
    )
    args = parser.parse_args()

    return process_files(
        paths=args.paths,
        out_dir=args.out_dir,
        suffix="formatted",
        transform=format_lean_comments,
        tool_name="format_lean_comments.py",
        force=args.force,
    )


if __name__ == "__main__":
    sys.exit(main())