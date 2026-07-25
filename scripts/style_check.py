#!/usr/bin/env python3
# This file is maintained by Claude (AI-generated).
"""
style_check.py  —  Semi-automatic conformance checks for STYLE.md.

STYLE.md is the single source of truth: every normative convention there has a
stable ID (LEAN-*, PED-*, WRITE-*). This script keeps the material honest to it
in two ways.

  1. `--checklist`  — regenerate the audit checklist straight from STYLE.md
     (all IDs + their one-line titles, grouped by section). This is the
     checklist a periodic human/LLM audit works through for the *manual*
     conventions, so it can never drift from the doc.

  2. (default)      — run the mechanical checks over tracked files and print
     any violations, grouped by convention ID. Checks are one of two classes:

       * auto     — mechanically decidable; a violation FAILS the run
                    (exit 1), so CI/`make style-check` can gate on it.
       * assisted — a heuristic that surfaces *candidates*; printed as advice,
                    never fails the run (too noisy to gate).

Add a check by appending a Check(...) to CHECKS below; tag it with the STYLE.md
ID it enforces so its output threads back to the doc. Nothing here understands
Lean or English deeply — these are cheap guards, with the judgement-heavy
conventions left to the audit checklist.

USAGE
  python3 scripts/style_check.py            # run checks, exit 1 on auto failures
  python3 scripts/style_check.py --checklist  # print the STYLE.md audit checklist
  python3 scripts/style_check.py --strict   # also fail on assisted candidates
"""

import argparse
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STYLE = os.path.join(ROOT, "STYLE.md")

# Files worth scanning: tracked chapter/prose sources, not build output or deps.
_SCAN_EXT = (".lean", ".md")
_SCAN_SKIP = ("_out/", ".lake/", "old/")
# The style rulebook/plan quote the phrases and markers the checks look for.
_META_DOCS = {"STYLE.md", "STYLE-CHECKING.md"}


# --------------------------------------------------------------------------
# STYLE.md parsing
# --------------------------------------------------------------------------
# A convention bullet looks like:  - **LEAN-1 — Mathlib alignment.** Follow …
_ID_RE = re.compile(r"\*\*([A-Z]{2,6}-\d+)\s*—\s*(.+?)\*\*")
_ID_TOKEN_RE = re.compile(r"\b([A-Z]{2,6}-\d+)\b")


def parse_style():
    """Return (ids, sections): the set of defined IDs, and an ordered list of
    (section-title, [(id, title), …]) for every `##` section that defines any."""
    ids = {}
    sections = []
    current = None
    with open(STYLE, encoding="utf-8") as f:
        for line in f:
            if line.startswith("## "):
                current = (line[3:].strip(), [])
                sections.append(current)
                continue
            m = _ID_RE.search(line)
            if m and current is not None:
                cid, title = m.group(1), m.group(2).strip().rstrip(".")
                ids[cid] = title
                current[1].append((cid, title))
    sections = [s for s in sections if s[1]]
    return ids, sections


# --------------------------------------------------------------------------
# file iteration
# --------------------------------------------------------------------------
def tracked_files():
    """Relevant tracked files, via git so build artifacts never appear."""
    out = subprocess.run(
        ["git", "-C", ROOT, "ls-files", "-z"],
        capture_output=True, text=True,
    ).stdout
    for path in out.split("\0"):
        if not path or not path.endswith(_SCAN_EXT):
            continue
        # The style meta-docs are the rulebook, not material under review — they
        # quote the very phrases/markers the checks look for, so never scan them.
        if path in _META_DOCS:
            continue
        if any(path.startswith(s) or f"/{s}" in path for s in _SCAN_SKIP):
            continue
        yield path


def prose_lines(path):
    """Yield (lineno, text) for prose only: all of a .md file, or the comment
    text of a .lean file (`--` line comments and `/- … -/` blocks). Keeps the
    heuristic checks off actual code."""
    full = os.path.join(ROOT, path)
    try:
        with open(full, encoding="utf-8") as f:
            lines = f.readlines()
    except (OSError, UnicodeDecodeError):
        return
    is_lean = path.endswith(".lean")
    in_block = False
    for i, raw in enumerate(lines, 1):
        text = raw.rstrip("\n")
        if not is_lean:
            yield i, text
            continue
        if in_block:
            end = text.find("-/")
            yield i, (text[:end] if end != -1 else text)
            if end != -1:
                in_block = False
            continue
        start = text.find("/-")
        if start != -1:
            yield i, text[start + 2:]
            if "-/" not in text[start + 2:]:
                in_block = True
            continue
        c = text.find("--")
        if c != -1:
            yield i, text[c + 2:]


# --------------------------------------------------------------------------
# checks — each yields (path, lineno, message)
# --------------------------------------------------------------------------
class Check:
    def __init__(self, cid, klass, desc, fn):
        self.cid = cid          # STYLE.md convention id this enforces
        self.klass = klass      # "auto" | "assisted"
        self.desc = desc
        self.fn = fn


_MARKER_RE = re.compile(r"\bstyle:\s*([A-Z]{2,6}-\d+)")


def check_markers(valid_ids):
    """auto — a deviation marker `style: <ID>` must name a real STYLE.md ID."""
    def run():
        for path in tracked_files():
            for ln, text in prose_lines(path):
                for m in _MARKER_RE.finditer(text):
                    cid = m.group(1)
                    if cid not in valid_ids:
                        yield path, ln, f"deviation marker names unknown id {cid}"
    return run


# WRITE-7 (concision): filler that almost always reads better cut/rewritten.
_FILLER = [
    r"it is worth noting that",
    r"it should be noted that",
    r"needless to say",
    r"due to the fact that",
    r"at this point in time",
    r"in order to\b",
    r"\bbasically\b",
]
_FILLER_RE = re.compile("|".join(_FILLER), re.IGNORECASE)


def check_filler():
    """assisted — throat-clearing / wordy phrases (WRITE-7)."""
    def run():
        for path in tracked_files():
            for ln, text in prose_lines(path):
                m = _FILLER_RE.search(text)
                if m:
                    yield path, ln, f'wordy: "{m.group(0)}"'
    return run


def build_checks(valid_ids):
    return [
        Check("STYLE-markers", "auto",
              "deviation markers reference a real STYLE.md id",
              check_markers(valid_ids)),
        Check("WRITE-7", "assisted",
              "throat-clearing / wordy phrases",
              check_filler()),
    ]


# --------------------------------------------------------------------------
# checklist generation
# --------------------------------------------------------------------------
def print_checklist(sections):
    print("# STYLE.md audit checklist")
    print()
    print("_Generated from STYLE.md — work through each item for the material "
          "under review and note conforms / deviates (with reason) / N/A._")
    print()
    for title, items in sections:
        print(f"## {title}")
        print()
        for cid, desc in items:
            print(f"- [ ] **{cid}** — {desc}")
        print()


# --------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--checklist", action="store_true",
                    help="print the STYLE.md audit checklist and exit")
    ap.add_argument("--strict", action="store_true",
                    help="also fail (exit 1) on assisted candidates")
    args = ap.parse_args()

    if not os.path.exists(STYLE):
        sys.stderr.write(f"STYLE.md not found at {STYLE}\n")
        raise SystemExit(2)

    valid_ids, sections = parse_style()

    if args.checklist:
        print_checklist(sections)
        return

    checks = build_checks(valid_ids)
    auto_hits = assisted_hits = 0
    for chk in checks:
        findings = list(chk.fn())
        if not findings:
            continue
        tag = "FAIL" if chk.klass == "auto" else "note"
        print(f"[{tag}] {chk.cid} — {chk.desc}")
        for path, ln, msg in findings:
            print(f"    {path}:{ln}: {msg}")
        print()
        if chk.klass == "auto":
            auto_hits += len(findings)
        else:
            assisted_hits += len(findings)

    print(f"Checked against {len(valid_ids)} STYLE.md conventions: "
          f"{auto_hits} auto failure(s), {assisted_hits} assisted note(s).")
    if auto_hits or (args.strict and assisted_hits):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
