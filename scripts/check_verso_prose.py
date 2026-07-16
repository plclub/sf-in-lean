#!/usr/bin/env python3
"""
Check that a Verso translation didn't drop or garble prose from its
code-forward `.lean` source.

Motivation
----------
The original completeness check compared the *set* of words in the source
against the set of words in the translation.  That is too weak: a set check
only catches a word that is missing *everywhere*.  It silently passes on

  * a whole paragraph dropped, if its words happen to recur elsewhere
    (e.g. "repeating the definition here for ease of reference …");
  * reordered or garbled text (same bag of words, wrong order);
  * duplicated content.

This check instead compares *contiguous runs of words*.  For every prose
segment of the source it asks: does each N-word window appear, in order, in
the translation?  Source spans that don't are reported verbatim, so a human
can tell a genuine loss from an intentional drop (FULL/TERSE alternatives,
marker keywords, test labels, etc.).

Method
------
1. Extract prose *segments* from the source: the body of each `/- … -/`
   block comment (not `/--` / `/-!`), and each run of plain `-- …` line
   comments.  Marker/divider/author-note line comments are skipped (they are
   intentionally dropped by to_verso, so they would only add noise).
2. Tokenise the whole translation into a lowercased word stream and index all
   of its N-grams.
3. For each source segment, mark every word that participates in at least one
   N-gram present in the translation.  Maximal runs of *unmarked* words of
   length >= MIN_RUN are reported as missing spans.

Usage
-----
  check_verso_prose.py SOURCE.lean VERSO.lean [--n N] [--min-run M]

Exit status is 1 if any missing span is reported, else 0.
"""
from __future__ import annotations

import argparse
import re
import sys
from typing import List

WORD_RE = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_']*")

# Line comments that to_verso intentionally drops (markers, dividers, author
# notes).  Skipped so they don't show up as spurious "missing" spans.
_MARKER_LINE_RE = re.compile(
    r"^\s*--\s*(/?FULL|/?TERSE|/?HIDE\w*|/?QUIZ|/?SOLUTION|/?QUIETSOLUTION"
    r"|/?WORKINCLASS|/?ADMIT\w*|EX\d*\w*|GRADE_\w+|INSTRUCTORS|RAB|RADDITION"
    r"|BCP|JC|MWH|CGH|CH|HG|NB|MMG|APT|DHS|TODO|TOFIX|LATER|SOONER|\[\])\b",
    re.IGNORECASE,
)
_DIVIDER_LINE_RE = re.compile(r"^\s*--\s*[#*=-]{3,}")
# Lone `[[` / `]]` (or `[[[` / `]]]`) display-fence lines: to_verso turns the
# enclosed material into a ```display code block, so the fence interrupts the
# translation's word stream (the fence info string sits between prose and
# body).  Treat them as segment boundaries here too, or an n-gram spanning
# prose -> display body is (falsely) reported missing.
_DISPLAY_FENCE_RE = re.compile(r"^\s*(\[\[\[?|\]\]\]?)\s*$")
_TERSE_INLINE_RE = re.compile(r"^\s*--\s*TERSE:", re.IGNORECASE)

# Unambiguous marker lines *inside* a block comment (no `--` prefix there), e.g.
# `/- /ADMITTED \n GRADE_THEOREM 0.5: foo \n … -/`.  Only high-confidence forms
# are listed so a prose line beginning "Full …" is never mistaken for a marker.
_BLOCK_MARKER_RE = re.compile(
    r"^\s*(/(FULL|TERSE|HIDE\w*|QUIZ|SOLUTION|QUIETSOLUTION|WORKINCLASS|ADMIT\w*)"
    r"|ADMIT(TED|DEF)|GRADE_\w+|EX\d+\w*\s*\(|INSTRUCTORS:|\*\*\*\s*$"
    r"|[#=*-]{3,})\b")


# A dev/author note block (`/- BCP: … -/`, `/- TODO: … -/`) is routed to :::dev
# and is not pedagogical prose; skip it so it isn't reported as a loss.
_DEV_BLOCK_RE = re.compile(
    r"^\s*(BCP|JC|MWH|CGH|RAB|CH|HG|NB|TODO|TOFIX|LATER|SOONER)\b", re.IGNORECASE)
# `FULL:` / `TERSE:` inline-mode prefixes are consumed by to_verso; drop them so
# they don't appear (unmatched) in the source word stream.
_MODE_PREFIX_RE = re.compile(r"^\s*(FULL|TERSE):\s?", re.IGNORECASE)


def words(s: str) -> List[str]:
    return [w.lower() for w in WORD_RE.findall(s)]


def source_segments(text: str) -> List[str]:
    """Return the prose segments of a code-forward .lean source."""
    lines = text.splitlines()
    segments: List[str] = []
    i, n = 0, len(lines)
    line_run: List[str] = []

    def flush_run():
        nonlocal line_run
        if line_run:
            segments.append(" ".join(line_run))
            line_run = []

    while i < n:
        line = lines[i]
        # Block comment /- … -/  (but not /-- docstring or /-! module doc).
        m = re.match(r"^(\s*)/-(?![-!])(.*)$", line)
        if m:
            flush_run()
            body = [m.group(2)]
            # Single-line /- … -/ ?
            if "-/" in m.group(2):
                body = [m.group(2).split("-/")[0]]
                segments.append(" ".join(body))
                i += 1
                continue
            i += 1
            while i < n and "-/" not in lines[i]:
                body.append(lines[i])
                i += 1
            if i < n:  # closing line, text before -/
                body.append(lines[i].split("-/")[0])
                i += 1
            # Split the block body at any unambiguous marker line so that
            # marker-only blocks (e.g. a trailing `/- /ADMITTED GRADE_THEOREM … -/`)
            # don't masquerade as prose.
            # Dev/author-note block -> routed to :::dev, not prose; skip it.
            first = next((b for b in body if b.strip()), "")
            if _DEV_BLOCK_RE.match(first):
                continue
            run: List[str] = []
            for bl in body:
                if _BLOCK_MARKER_RE.match(bl) or _DISPLAY_FENCE_RE.match(bl):
                    if run:
                        segments.append(" ".join(run))
                        run = []
                elif _MODE_PREFIX_RE.match(bl):
                    # A FULL:/TERSE: prefix starts a new directive in the output,
                    # so it begins a new segment here too (n-grams must not span
                    # the boundary).
                    if run:
                        segments.append(" ".join(run))
                        run = []
                    run.append(_MODE_PREFIX_RE.sub("", bl))
                else:
                    run.append(bl)
            if run:
                segments.append(" ".join(run))
            continue
        # Plain line comment.
        if re.match(r"^\s*--", line):
            if (_MARKER_LINE_RE.match(line) or _DIVIDER_LINE_RE.match(line)
                    or _TERSE_INLINE_RE.match(line)
                    or _DISPLAY_FENCE_RE.match(re.sub(r"^\s*--\s?", "", line))):
                flush_run()  # marker ends the current prose run
            else:
                line_run.append(_MODE_PREFIX_RE.sub(
                    "", re.sub(r"^\s*--\s?", "", line)))
            i += 1
            continue
        # Any code / blank line ends a line-comment run.
        flush_run()
        i += 1
    flush_run()
    return segments


def missing_spans(src_words: List[str], dst_ngrams: set, n: int,
                  min_run: int) -> List[range]:
    covered = [False] * len(src_words)
    for i in range(len(src_words) - n + 1):
        if tuple(src_words[i:i + n]) in dst_ngrams:
            for j in range(i, i + n):
                covered[j] = True
    spans: List[range] = []
    i = 0
    while i < len(src_words):
        if covered[i]:
            i += 1
            continue
        j = i
        while j < len(src_words) and not covered[j]:
            j += 1
        if j - i >= min_run:
            spans.append(range(i, j))
        i = j
    return spans


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("source")
    ap.add_argument("verso")
    ap.add_argument("--n", type=int, default=6,
                    help="window size in words (default 6)")
    ap.add_argument("--min-run", type=int, default=5,
                    help="report unmatched runs at least this many words long "
                         "(default 5)")
    args = ap.parse_args()

    src_text = open(args.source).read()
    dst_words = words(open(args.verso).read())
    dst_ngrams = {tuple(dst_words[i:i + args.n])
                  for i in range(len(dst_words) - args.n + 1)}

    total = 0
    for seg in source_segments(src_text):
        sw = words(seg)
        if len(sw) < args.n:
            continue
        for span in missing_spans(sw, dst_ngrams, args.n, args.min_run):
            total += 1
            phrase = " ".join(sw[span.start:span.stop])
            print(f"MISSING ({span.stop - span.start} words): {phrase}")
    print(f"\n{total} missing span(s) "
          f"(n={args.n}, min-run={args.min_run}) in {args.source}")
    return 1 if total else 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except BrokenPipeError:
        # Output was truncated by a downstream pipe (e.g. `| head`); exit quietly.
        sys.exit(0)
