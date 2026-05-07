#!/usr/bin/env python3
"""
Build a presentation variant from a formatted Lean source file
(the output of format_lean_comments.py).

Variants:
  full       Keep FULL prose (unwrapped from /- -/), drop TERSE lines,
             replace `-- ADMITDEF ... -- /ADMITDEF` body with `sorry`,
             rewrite `example ... := by <proof>  -- ADMITTED` as
             `example ... := by sorry  -- ADMITTED`.
  terse      Drop FULL prose entirely, keep TERSE prose (unwrapped),
             same `sorry` substitutions as `full`.
  solutions  Keep FULL prose, drop TERSE lines, keep ADMITDEF body and
             ADMITTED lines verbatim (solutions show the answer).

All variants:
  * Drop HIDEFROMHTML regions entirely.
  * Drop FULL / /FULL / TERSE / HIDEFROMHTML region markers.
  * Drop instructor/author notes (-- INSTRUCTORS, -- RAB, -- JC, -- BCP),
    section dividers (-- ####), and -- EXn / -- EX2 markers.
  * Keep test-name markers (-- test_foo), grader terminators (-- []),
    GRADE_THEOREM lines, and -- ==> / -- ===> eval annotations.
  * Keep code.

Usage:
  extract.py --variant full --out-dir OUT FILE_OR_DIR [FILE_OR_DIR ...]
"""

from __future__ import annotations

import argparse
import re
import sys
from typing import List

from lean_cli import process_files

# --- Regexes -----------------------------------------------------------------

FULL_START_RE   = re.compile(r"^\s*--\s*FULL\s*$")
FULL_END_RE     = re.compile(r"^\s*--\s*/FULL\s*$")
HIDEFROMHTML_START_RE     = re.compile(r"^\s*--\s*HIDEFROMHTML\s*$")
HIDEFROMHTML_END_RE       = re.compile(r"^\s*--\s*/HIDEFROMHTML\s*$")
HIDEFROMADVANCED_START_RE = re.compile(r"^\s*--\s*HIDEFROMADVANCED\s*$")
HIDEFROMADVANCED_END_RE   = re.compile(r"^\s*--\s*/HIDEFROMADVANCED\s*$")
HIDE_PLAIN_START_RE       = re.compile(r"^\s*--\s*HIDE\s*$")
HIDE_PLAIN_END_RE         = re.compile(r"^\s*--\s*/HIDE\s*$")
SOLUTION_START_RE         = re.compile(r"^\s*--\s*SOLUTION\s*$")
SOLUTION_END_RE           = re.compile(r"^\s*--\s*/SOLUTION\s*$")
QUIETSOLUTION_START_RE    = re.compile(r"^\s*--\s*QUIETSOLUTION\s*$")
QUIETSOLUTION_END_RE      = re.compile(r"^\s*--\s*/QUIETSOLUTION\s*$")

# TERSE line: the formatter emits `<indent>-- TERSE: /- body -/` (single line).
# Keep a looser fallback for any leftover `-- TERSE:` lines.
TERSE_INLINE_RE = re.compile(r"^(\s*)--\s*TERSE:\s*/-\s*(.*?)\s*-/\s*$")
TERSE_BARE_RE   = re.compile(r"^\s*--\s*TERSE:")

# Block comment forms.
BLOCK_INLINE_RE            = re.compile(r"^(\s*)/-\s*(.*?)\s*-/\s*$")
BLOCK_OPEN_BARE_RE         = re.compile(r"^(\s*)/-\s*$")
BLOCK_OPEN_WITH_CONTENT_RE = re.compile(r"^(\s*)/-\s+(.+?)\s*$")
BLOCK_CLOSE_RE             = re.compile(r"^(.*?)\s*-/\s*$")

# ADMITDEF block: the definition body between the markers is the solution.
ADMITDEF_START_RE = re.compile(r"^(\s*)--\s*ADMITDEF\s*$")
ADMITDEF_END_RE   = re.compile(r"^\s*--\s*/ADMITDEF\s*$")

# Multi-line ADMITTED proof block: `  -- ADMITTED` / `  -- /ADMITTED`
# with a proof body between them. Same shape as ADMITDEF but for proofs.
ADMITTED_BLOCK_START_RE = re.compile(r"^(\s*)--\s*ADMITTED\s*$")
ADMITTED_BLOCK_END_RE   = re.compile(r"^\s*--\s*/ADMITTED\s*$")

# `example ... := by <proof>  -- ADMITTED` form.
# Capture: (prefix up to and including `by `), (proof body), (`  -- ADMITTED` tail).
ADMITTED_LINE_RE = re.compile(
    r"^(?P<prefix>.*?:=\s*by\s+)(?P<proof>.+?)(?P<tail>\s*--\s*ADMITTED\s*)$"
)

# Dropped instructor/author notes and structural markers.
DROP_LINE_PATTERNS = [
    re.compile(r"^\s*--\s*INSTRUCTORS\b"),
    re.compile(r"^\s*--\s*RAB\b"),
    re.compile(r"^\s*--\s*RADDITION\b"),
    re.compile(r"^\s*--\s*SOONER\b"),
    re.compile(r"^\s*--\s*LATER\b"),
    re.compile(r"^\s*--\s*MMG\b"),
    re.compile(r"^\s*--\s*APT\b"),
    re.compile(r"^\s*--\s*DHS\b"),
    re.compile(r"^\s*--\s*TODO\b"),
    re.compile(r"^\s*--\s*JC\b"),
    re.compile(r"^\s*--\s*BCP\b"),
    re.compile(r"^\s*--\s*EX\d+\b"),
    re.compile(r"^\s*-- ?#{3,}\s*$"),          # pure `#` divider
    re.compile(r"^\s*-- ?#{1,3}\s+\S[^#]*$"),  # `-- ## Title` header
]

# Kept-as-is markers (still `--` comments in the output).
KEEP_COMMENT_PATTERNS = [
    # re.compile(r"^\s*--\s*\[[^\]]*\]\s*$"),
    # re.compile(r"^\s*--\s*GRADE_THEOREM\b"),
]

LINE_COMMENT_RE = re.compile(r"^\s*--")


# --- Helpers -----------------------------------------------------------------

def is_drop_line(line: str) -> bool:
    return any(p.match(line) for p in DROP_LINE_PATTERNS)


def is_keep_comment(line: str) -> bool:
    return any(p.match(line) for p in KEEP_COMMENT_PATTERNS)


def rewrite_admitted_line(line: str, *, to_sorry: bool) -> str:
    """If `line` matches the ADMITTED pattern and `to_sorry`, rewrite the
    proof body to `sorry`. Otherwise return `line` unchanged."""
    if not to_sorry:
        return line
    m = ADMITTED_LINE_RE.match(line)
    if not m:
        return line
    return f"{m.group('prefix')}sorry{m.group('tail')}"


def emit_block_comment(
    lines: List[str], i: int, out: List[str]
) -> int:
    """Pass through a `/- ... -/` block starting at lines[i] verbatim.
    Returns new index."""
    line = lines[i]
    n = len(lines)

    if BLOCK_INLINE_RE.match(line):
        out.append(line)
        return i + 1

    if BLOCK_OPEN_BARE_RE.match(line) or BLOCK_OPEN_WITH_CONTENT_RE.match(line):
        out.append(line)
        i += 1
        while i < n:
            out.append(lines[i])
            if BLOCK_CLOSE_RE.match(lines[i]):
                return i + 1
            i += 1
        return i

    # Not actually a block opener — emit and move on.
    out.append(line)
    return i + 1


def skip_block_comment(lines: List[str], i: int) -> int:
    """Skip over a `/- ... -/` block. Returns new index."""
    line = lines[i]
    n = len(lines)
    if BLOCK_INLINE_RE.match(line):
        return i + 1
    if BLOCK_OPEN_BARE_RE.match(line) or BLOCK_OPEN_WITH_CONTENT_RE.match(line):
        i += 1
        while i < n and not BLOCK_CLOSE_RE.match(lines[i]):
            i += 1
        if i < n:
            i += 1
        return i
    return i + 1


def is_block_opener(line: str) -> bool:
    return (
        BLOCK_INLINE_RE.match(line) is not None
        or BLOCK_OPEN_BARE_RE.match(line) is not None
        or BLOCK_OPEN_WITH_CONTENT_RE.match(line) is not None
    )


# --- Main transform ----------------------------------------------------------

def extract(lines: List[str], variant: str) -> List[str]:
    """Apply the extraction rules for `variant` to `lines`."""
    keep_full   = variant in ("full", "solutions")
    keep_terse  = variant == "terse"
    body_to_sorry = variant in ("full", "terse")

    out: List[str] = []
    i = 0
    n = len(lines)
    hide_depth = 0

    while i < n:
        line = lines[i]

        # HIDE regions: drop content entirely in all variants (plain HIDE
        # means "author-only notes / scratch").
        if HIDE_PLAIN_START_RE.match(line):
            hide_depth += 1
            i += 1
            continue
        if HIDE_PLAIN_END_RE.match(line):
            hide_depth = max(0, hide_depth - 1)
            i += 1
            continue
        if hide_depth > 0:
            i += 1
            continue

        # HIDEFROMHTML: drop the region entirely in all variants (contains
        # notes intended only for the HTML export, not student Lean sources).
        if HIDEFROMHTML_START_RE.match(line):
            depth_html = 1
            i += 1
            while i < n and depth_html > 0:
                if HIDEFROMHTML_START_RE.match(lines[i]):
                    depth_html += 1
                elif HIDEFROMHTML_END_RE.match(lines[i]):
                    depth_html -= 1
                i += 1
            continue
        if HIDEFROMHTML_END_RE.match(line):
            # Stray close — defensive skip.
            i += 1
            continue

        # SOLUTION regions: drop the region entirely in full/terse (students
        # should not see sample solutions); strip markers only in solutions.
        if SOLUTION_START_RE.match(line) or QUIETSOLUTION_START_RE.match(line):
            start_re = (SOLUTION_START_RE if SOLUTION_START_RE.match(line)
                        else QUIETSOLUTION_START_RE)
            end_re = (SOLUTION_END_RE if start_re is SOLUTION_START_RE
                      else QUIETSOLUTION_END_RE)
            if variant != "solutions":
                depth_sol = 1
                i += 1
                while i < n and depth_sol > 0:
                    if start_re.match(lines[i]):
                        depth_sol += 1
                    elif end_re.match(lines[i]):
                        depth_sol -= 1
                    i += 1
            else:
                i += 1
            continue
        if SOLUTION_END_RE.match(line) or QUIETSOLUTION_END_RE.match(line):
            i += 1
            continue

        # HIDEFROMADVANCED: "hide from the advanced/terse version."
        # Drop the region entirely in terse; strip markers only in full/solutions.
        if HIDEFROMADVANCED_START_RE.match(line):
            if not keep_full:
                # terse: skip to matching close.
                depth_adv = 1
                i += 1
                while i < n and depth_adv > 0:
                    if HIDEFROMADVANCED_START_RE.match(lines[i]):
                        depth_adv += 1
                    elif HIDEFROMADVANCED_END_RE.match(lines[i]):
                        depth_adv -= 1
                    i += 1
            else:
                i += 1  # full/solutions: just strip the marker
            continue
        if HIDEFROMADVANCED_END_RE.match(line):
            # Stray close (shouldn't happen in full/solutions since we paired
            # it above; in terse it's consumed by the loop). Defensive skip.
            i += 1
            continue

        # FULL region: behavior depends on variant.
        if FULL_START_RE.match(line):
            i += 1
            if keep_full:
                # `full` / `solutions`: keep FULL region content (unwrap
                # prose blocks, pass markers through).
                while i < n and not FULL_END_RE.match(lines[i]):
                    i = process_line(lines, i, out,
                                     keep_full=True, keep_terse=False,
                                     body_to_sorry=body_to_sorry,
                                     inside_full=True)
            else:
                # `terse`: drop the entire FULL region — prose, code,
                # every marker between `-- FULL` and `-- /FULL`.
                while i < n and not FULL_END_RE.match(lines[i]):
                    i += 1
            if i < n and FULL_END_RE.match(lines[i]):
                i += 1
            continue

        # Outside FULL: usual processing.
        i = process_line(lines, i, out,
                         keep_full=keep_full,
                         keep_terse=keep_terse,
                         body_to_sorry=body_to_sorry,
                         inside_full=False)

    return collapse_blank_runs(out)


def process_line(
    lines: List[str],
    i: int,
    out: List[str],
    *,
    keep_full: bool,
    keep_terse: bool,
    body_to_sorry: bool,
    inside_full: bool,
) -> int:
    """Process a single non-HIDE, non-FULL-boundary line. Returns new index."""
    n = len(lines)
    line = lines[i]

    # SOLUTION / QUIETSOLUTION: drop region in full/terse, keep in solutions.
    for start_re, end_re in (
        (SOLUTION_START_RE, SOLUTION_END_RE),
        (QUIETSOLUTION_START_RE, QUIETSOLUTION_END_RE),
    ):
        if start_re.match(line):
            if body_to_sorry:
                depth = 1
                i += 1
                while i < n and depth > 0:
                    if start_re.match(lines[i]):
                        depth += 1
                    elif end_re.match(lines[i]):
                        depth -= 1
                    i += 1
            else:
                i += 1
            return i
    if SOLUTION_END_RE.match(line) or QUIETSOLUTION_END_RE.match(line):
        return i + 1

    # HIDEFROMHTML: drop region entirely in all variants.
    if HIDEFROMHTML_START_RE.match(line):
        depth = 1
        i += 1
        while i < n and depth > 0:
            if HIDEFROMHTML_START_RE.match(lines[i]):
                depth += 1
            elif HIDEFROMHTML_END_RE.match(lines[i]):
                depth -= 1
            i += 1
        return i
    if HIDEFROMHTML_END_RE.match(line):
        return i + 1

    # TERSE single-line form: `-- TERSE: /- body -/`
    m = TERSE_INLINE_RE.match(line)
    if m:
        if keep_terse:
            body = m.group(2).strip()
            if body:
                out.append(f"{m.group(1)}/- {body} -/")
        return i + 1

    # Defensive: any bare leftover `-- TERSE:` line gets dropped unless keep.
    if TERSE_BARE_RE.match(line):
        if keep_terse:
            text = line.split(":", 1)[1].strip() if ":" in line else ""
            if text:
                out.append(f"/- {text} -/")
        return i + 1

    # ADMITDEF block: `-- ADMITDEF` ... `-- /ADMITDEF`.
    m = ADMITDEF_START_RE.match(line)
    if m:
        indent = m.group(1)
        i += 1
        body: List[str] = []
        while i < n and not ADMITDEF_END_RE.match(lines[i]):
            body.append(lines[i])
            i += 1
        if i < n:
            i += 1  # skip -- /ADMITDEF
        if body_to_sorry:
            # If the `:=` is already present on the previous non-blank emitted
            # line (e.g. `def foo (n : Nat) : T :=`), emit just `sorry`;
            # otherwise emit `:= sorry` so the definition is syntactically complete.
            prev = next((o for o in reversed(out) if o.strip()), "")
            if prev.rstrip().endswith(":="):
                out.append(f"{indent}sorry")
            else:
                out.append(f"{indent}:= sorry")
        else:
            out.extend(body)
        return i

    # ADMITTED multi-line proof block: `-- ADMITTED` ... `-- /ADMITTED`.
    # The body is a proof term; replace with `sorry` or keep verbatim.
    m = ADMITTED_BLOCK_START_RE.match(line)
    if m:
        indent = m.group(1)
        i += 1
        body = []
        while i < n and not ADMITTED_BLOCK_END_RE.match(lines[i]):
            body.append(lines[i])
            i += 1
        if i < n:
            i += 1  # skip -- /ADMITTED
        if body_to_sorry:
            out.append(f"{indent}sorry")
        else:
            out.extend(body)
        return i

    # ADMITTED single-line form: proof -> sorry unless solutions.
    if ADMITTED_LINE_RE.match(line):
        out.append(rewrite_admitted_line(line, to_sorry=body_to_sorry))
        return i + 1

    # Block comments: passed through verbatim (prose stays as Lean comments).
    if is_block_opener(line):
        # If we're inside FULL and NOT keeping FULL, skip the block.
        if inside_full and not keep_full:
            return skip_block_comment(lines, i)
        return emit_block_comment(lines, i, out)

    # Line comments.
    if LINE_COMMENT_RE.match(line):
        if is_drop_line(line):
            return i + 1
        if is_keep_comment(line):
            out.append(line)
            return i + 1
        # Any other `--` line is treated as an instructor/author note: drop.
        return i + 1

    # Code / blank lines: keep.
    out.append(line)
    return i + 1


def collapse_blank_runs(lines: List[str]) -> List[str]:
    """Collapse 3+ consecutive blank lines to 2."""
    result: List[str] = []
    blanks = 0
    for ln in lines:
        if ln.strip() == "":
            blanks += 1
            if blanks <= 2:
                result.append(ln)
        else:
            blanks = 0
            result.append(ln)
    return result


# --- CLI ---------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        prog="extract.py",
        description="Build a presentation variant from formatted Lean files. "
                    "Output is written to <out-dir>/<stem>.<variant>.lean.",
    )
    parser.add_argument(
        "paths", nargs="*", metavar="FILE_OR_DIR",
        help="one or more formatted .lean files and/or directories",
    )
    parser.add_argument(
        "--variant", "-v", required=True,
        choices=("full", "terse", "solutions"),
        help="which variant to build",
    )
    parser.add_argument(
        "--out-dir", "-o", required=True,
        help="directory to write extracted output into (created if missing)",
    )
    parser.add_argument(
        "--force", "-f", action="store_true",
        help="overwrite existing output files instead of skipping them",
    )
    args = parser.parse_args()

    variant = args.variant

    def transform(data: List[str]) -> List[str]:
        return extract(data, variant)

    return process_files(
        paths=args.paths,
        out_dir=args.out_dir,
        suffix=variant,
        transform=transform,
        tool_name="extract.py",
        strip_infix="formatted",
        force=args.force,
    )


if __name__ == "__main__":
    sys.exit(main())