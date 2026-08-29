#!/usr/bin/env python3
# This file is maintained by Claude (AI-generated).
"""
proofread.py  —  Drives a low-level proofreading pass over a chapter.

Claude writes a *round* — a JSON file of anchored edits under proofread/rounds/
— and points this script at it. From then on the whole pass is two runs of one
bare command; the round file is never something you have to open.

    python3 scripts/proofread.py     # 1st run: check anchors, make every edit,
                                     #          write an isolated diff to read
    <review the diff; revert what you don't want, in your editor>
    python3 scripts/proofread.py     # 2nd run: record the rejections, report
                                     #          any pattern ripe for a house rule

Which round is in flight, and which of the two runs comes next, is kept in
proofread/state.json. See PROOFREADING.md.

Rejections land in proofread/ledger.jsonl, keyed by a whitespace-normalized
hash of the (old, new) pair. A later round that proposes the same edit again —
in this chapter or any other — is silently dropped before you ever see it.

OTHER COMMANDS
  start <round.json>   register a round (Claude does this; sets up the state)
  undo                 reverse the applied round and forget it
  status               what is in flight
  ledger [--cat C]     list recorded rejections
  patterns [--min N]   rejection categories that have earned a house rule
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(ROOT, "proofread", "ledger.jsonl")
STATE = os.path.join(ROOT, "proofread", "state.json")

# Two accepted edits closer than this many lines apart usually land in the same
# git hunk, so the editor cannot revert one without the other.
HUNK_GAP = 4

C_RED, C_GRN, C_YEL, C_DIM, C_BLD, C_OFF = (
    "\033[31m", "\033[32m", "\033[33m", "\033[2m", "\033[1m", "\033[0m")
if not sys.stdout.isatty():
    C_RED = C_GRN = C_YEL = C_DIM = C_BLD = C_OFF = ""


# --------------------------------------------------------------------------
# rounds, state, ledger
# --------------------------------------------------------------------------
def load_round(path):
    with open(path) as f:
        round_ = json.load(f)
    for key in ("file", "proposals"):
        if key not in round_:
            sys.exit(f"{path}: missing required key {key!r}")
    seen = set()
    for p in round_["proposals"]:
        for key in ("id", "old", "new"):
            if key not in p:
                sys.exit(f"{path}: proposal {p.get('id', '?')} missing key {key!r}")
        if p["id"] in seen:
            sys.exit(f"{path}: duplicate proposal id {p['id']!r}")
        seen.add(p["id"])
    return round_


def round_label(round_):
    return f"{round_.get('chapter', round_['file'])} round {round_.get('round', '?')}"


def load_state():
    if not os.path.exists(STATE):
        return None
    with open(STATE) as f:
        return json.load(f)


def save_state(state):
    os.makedirs(os.path.dirname(STATE), exist_ok=True)
    with open(STATE, "w") as f:
        json.dump(state, f, indent=1)
        f.write("\n")


def clear_state():
    if os.path.exists(STATE):
        os.remove(STATE)


def norm(text):
    """Whitespace-insensitive form: line breaks must not change an edit's identity."""
    return re.sub(r"\s+", " ", text).strip()


def key_of(p):
    """Stable identity of an edit, independent of file, line, and line wrapping."""
    h = hashlib.sha1()
    h.update(norm(p["old"]).encode())
    h.update(b"\x00")
    h.update(norm(p["new"]).encode())
    return h.hexdigest()[:16]


def load_ledger():
    if not os.path.exists(LEDGER):
        return {}
    entries = {}
    with open(LEDGER) as f:
        for line in f:
            line = line.strip()
            if line:
                e = json.loads(line)
                entries[e["key"]] = e
    return entries


def record_rejections(proposals, round_):
    os.makedirs(os.path.dirname(LEDGER), exist_ok=True)
    with open(LEDGER, "a") as f:
        for p in proposals:
            f.write(json.dumps({
                "key": key_of(p),
                "id": p["id"],
                "file": round_["file"],
                "cat": p.get("cat", ""),
                "old": p["old"],
                "new": p["new"],
                "why": p.get("why", ""),
            }, sort_keys=True) + "\n")


def line_of(text, index):
    return text.count("\n", 0, index) + 1


def rel(path):
    return os.path.relpath(path, ROOT)


# --------------------------------------------------------------------------
# anchors
# --------------------------------------------------------------------------
def anchor_report(text, proposals):
    """Locate every proposal; return (rows, errors). rows are (p, start, end)."""
    rows, errors = [], []
    for p in proposals:
        old, new = p["old"], p["new"]
        if old == new:
            errors.append(f"{p['id']}: old and new are identical")
            continue
        # The second run decides accepted-vs-rejected by asking which of the
        # two strings is in the file, so neither may contain the other.
        if norm(old) in norm(new) or norm(new) in norm(old):
            errors.append(
                f"{p['id']}: one of old/new contains the other — widen the "
                f"anchor with surrounding words so they are distinguishable")
            continue
        n = text.count(old)
        if n == 0:
            errors.append(f"{p['id']}: 'old' text not found in file")
            continue
        if n > 1:
            errors.append(f"{p['id']}: 'old' text occurs {n} times — widen the anchor")
            continue
        if text.count(new) != 0:
            errors.append(f"{p['id']}: 'new' text already present in file")
            continue
        start = text.index(old)
        rows.append((p, start, start + len(old)))
    rows.sort(key=lambda r: r[1])
    for (pa, _, enda), (pb, startb, _) in zip(rows, rows[1:]):
        if startb < enda:
            errors.append(f"{pa['id']} and {pb['id']}: anchors overlap in the file")
    return rows, errors


# --------------------------------------------------------------------------
# run 1 — check and apply
# --------------------------------------------------------------------------
def diff_path(round_path):
    return re.sub(r"\.json$", "", round_path) + ".diff"


def write_isolated_diff(round_path, round_, applied, after):
    """A diff of just this round's edits, free of any other pending changes."""
    before = after
    for p in applied:
        before = before.replace(p["new"], p["old"], 1)
    dest = diff_path(round_path)
    with tempfile.NamedTemporaryFile("w", suffix=".before", delete=False) as tmp:
        tmp.write(before)
        tmp_name = tmp.name
    try:
        out = subprocess.run(
            ["diff", "-u", "-U", "2",
             "--label", round_["file"] + " (before this round)",
             "--label", round_["file"],
             tmp_name, os.path.join(ROOT, round_["file"])],
            capture_output=True, text=True).stdout
    finally:
        os.remove(tmp_name)
    with open(dest, "w") as f:
        f.write(out)
    return dest


def run_apply(round_path, round_):
    path = os.path.join(ROOT, round_["file"])
    with open(path) as f:
        text = f.read()

    ledger = load_ledger()
    live = [p for p in round_["proposals"] if key_of(p) not in ledger]
    dropped = len(round_["proposals"]) - len(live)

    rows, errors = anchor_report(text, live)
    if errors:
        for e in errors:
            print(f"{C_RED}error {e}{C_OFF}")
        sys.exit("\nanchor errors — nothing was applied; the round needs fixing")

    shared = []
    for (pa, _, enda), (pb, startb, _) in zip(rows, rows[1:]):
        gap = line_of(text, startb) - line_of(text, enda)
        if 0 <= gap < HUNK_GAP:
            shared.append((pa, pb, gap))

    applied = []
    for p, _, _ in rows:
        text = text.replace(p["old"], p["new"], 1)
        applied.append(p)
    with open(path, "w") as f:
        f.write(text)

    dest = write_isolated_diff(round_path, round_, applied, text)
    save_state({"round": rel(round_path), "phase": "applied"})

    print(f"{C_BLD}{round_label(round_)}{C_OFF} — "
          f"{C_GRN}{len(applied)} edits applied{C_OFF} to {round_['file']}")
    if dropped:
        print(f"{C_DIM}{dropped} skipped: already declined in a previous round{C_OFF}")
    print()
    counts = {}
    for p in applied:
        counts[p.get("cat", "?")] = counts.get(p.get("cat", "?"), 0) + 1
    for cat, n in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"  {n:3d}  {cat}")
    if shared:
        print(f"\n{C_YEL}These pairs sit in one git hunk — reverting one reverts "
              f"both, so edit those spots by hand if you want only one:{C_OFF}")
        for pa, pb, gap in shared:
            print(f"  {pa['id']} + {pb['id']} ({gap} line{'' if gap == 1 else 's'} apart)"
                  f"  {C_DIM}{pa.get('cat', '')} / {pb.get('cat', '')}{C_OFF}")
    print(f"""
{C_BLD}Next{C_OFF}
  1. Read {rel(dest)} — just this round's edits, nothing else pending.
  2. Revert the ones you don't want, in {round_['file']}.
  3. Run {C_BLD}python3 scripts/proofread.py{C_OFF} again to save your choices.

  {C_DIM}To drop the whole round instead: python3 scripts/proofread.py undo{C_OFF}""")
    return 0


# --------------------------------------------------------------------------
# run 2 — reconcile
# --------------------------------------------------------------------------
def run_reconcile(round_path, round_):
    path = os.path.join(ROOT, round_["file"])
    with open(path) as f:
        text = f.read()
    ledger = load_ledger()

    kept, rejected, unclear = [], [], []
    for p in round_["proposals"]:
        if key_of(p) in ledger:
            continue
        has_new, has_old = text.count(p["new"]), text.count(p["old"])
        if has_new and not has_old:
            kept.append(p)
        elif has_old and not has_new:
            rejected.append(p)
        else:
            unclear.append(p)

    if rejected:
        record_rejections(rejected, round_)
    clear_state()

    print(f"{C_BLD}{round_label(round_)}{C_OFF} — "
          f"{C_GRN}{len(kept)} kept{C_OFF}, {C_RED}{len(rejected)} declined{C_OFF}"
          + (f", {C_YEL}{len(unclear)} unclear{C_OFF}" if unclear else ""))
    if rejected:
        print(f"\n{C_BLD}Declined and recorded — these will never be proposed "
              f"again:{C_OFF}")
        for p in rejected:
            print(f"  {C_DIM}{p.get('cat', '')}{C_OFF}")
            print(f"    - {norm(p['old'])[:96]}")
            print(f"    + {norm(p['new'])[:96]}")
    if unclear:
        print(f"\n{C_YEL}Unclear — you rewrote the surrounding text yourself, so "
              f"nothing was recorded:{C_OFF}")
        for p in unclear:
            print(f"  {p.get('cat', '')}: {norm(p['old'])[:80]}")

    print()
    flagged = report_patterns(2)
    print(f"\n{C_BLD}Next{C_OFF}")
    if flagged:
        print(f"  1. Add a line to the house-rules table in PROOFREADING.md for "
              f"the flagged categor{'y' if len(flagged) == 1 else 'ies'} above.")
        print(f"  2. lake build, then commit the chapter, {rel(LEDGER)}, and "
              f"PROOFREADING.md together.")
    else:
        print(f"  lake build, then commit the chapter and {rel(LEDGER)} together.")
    return 0


# --------------------------------------------------------------------------
# the bare command
# --------------------------------------------------------------------------
def cmd_run(args):
    state = load_state()
    if state is None:
        print("Nothing in flight. Ask Claude to proofread a chapter; it will "
              "write a round and register it here.")
        return 1
    round_path = os.path.join(ROOT, state["round"])
    round_ = load_round(round_path)
    if state.get("phase") == "applied":
        return run_reconcile(round_path, round_)
    return run_apply(round_path, round_)


def cmd_start(args):
    state = load_state()
    if state is not None and not args.force:
        sys.exit(f"{state['round']} is still in flight (phase "
                 f"{state.get('phase', 'pending')}); finish it or run `undo`")
    round_path = os.path.abspath(args.round)
    round_ = load_round(round_path)
    save_state({"round": rel(round_path), "phase": "pending"})
    print(f"registered {round_label(round_)} — "
          f"{len(round_['proposals'])} proposals")
    print("run `python3 scripts/proofread.py` to check and apply them")
    return 0


def cmd_undo(args):
    state = load_state()
    if state is None:
        sys.exit("nothing in flight")
    round_path = os.path.join(ROOT, state["round"])
    round_ = load_round(round_path)
    if state.get("phase") != "applied":
        clear_state()
        print(f"forgot {round_label(round_)} (nothing had been applied)")
        return 0
    path = os.path.join(ROOT, round_["file"])
    with open(path) as f:
        text = f.read()
    n = 0
    for p in round_["proposals"]:
        if text.count(p["new"]) == 1 and text.count(p["old"]) == 0:
            text = text.replace(p["new"], p["old"], 1)
            n += 1
    with open(path, "w") as f:
        f.write(text)
    clear_state()
    print(f"reverted {n} edit{'' if n == 1 else 's'} in {round_['file']}; "
          f"{round_label(round_)} forgotten")
    print(f"{C_DIM}nothing was written to the ledger{C_OFF}")
    return 0


def cmd_status(args):
    state = load_state()
    if state is None:
        print("nothing in flight")
    else:
        round_ = load_round(os.path.join(ROOT, state["round"]))
        phase = state.get("phase", "pending")
        nxt = ("run `python3 scripts/proofread.py` to save your choices"
               if phase == "applied" else
               "run `python3 scripts/proofread.py` to apply the edits")
        print(f"{round_label(round_)}: {len(round_['proposals'])} proposals, "
              f"phase {phase}")
        if phase == "applied":
            print(f"  edits are in {round_['file']}; "
                  f"diff at {rel(diff_path(os.path.join(ROOT, state['round'])))}")
        print(f"  {nxt}")
    print(f"\n{len(load_ledger())} declined edits on record")
    return 0


def cmd_ledger(args):
    ledger = load_ledger()
    shown = 0
    for e in sorted(ledger.values(), key=lambda e: (e.get("cat", ""), e["id"])):
        if args.cat and args.cat not in e.get("cat", ""):
            continue
        shown += 1
        print(f"{e.get('cat', '?')}  {C_DIM}{e['file']}{C_OFF}")
        print(f"  - {norm(e['old'])[:100]}")
        print(f"  + {norm(e['new'])[:100]}")
    print(f"\n{shown} shown, {len(ledger)} declined edits on record")
    return 0


def report_patterns(minimum):
    """Print the rejection histogram; return the categories at or over minimum."""
    counts = {}
    for e in load_ledger().values():
        counts.setdefault(e.get("cat", "?"), []).append(e)
    if not counts:
        print(f"{C_DIM}no rejections on record yet{C_OFF}")
        return []
    flagged = []
    print(f"{C_BLD}Rejections by category{C_OFF}")
    for cat, es in sorted(counts.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        hit = len(es) >= minimum
        flagged += [cat] if hit else []
        print(f"  {len(es):3d}  {cat}"
              + (f"{C_YEL}  <- worth a house rule{C_OFF}" if hit else ""))
    return flagged


def cmd_patterns(args):
    report_patterns(args.min)
    return 0


def main():
    ap = argparse.ArgumentParser(
        description="Drive a proofreading round. With no arguments: apply the "
                    "pending round, or (after you have reviewed) save your choices.")
    sub = ap.add_subparsers(dest="cmd")

    p = sub.add_parser("start", help="register a round file (Claude does this)")
    p.add_argument("round")
    p.add_argument("--force", action="store_true",
                   help="replace a round that is still in flight")
    p.set_defaults(func=cmd_start)

    p = sub.add_parser("undo", help="revert the applied round and forget it")
    p.set_defaults(func=cmd_undo)

    p = sub.add_parser("status", help="what is in flight")
    p.set_defaults(func=cmd_status)

    p = sub.add_parser("ledger", help="list recorded rejections")
    p.add_argument("--cat", help="filter by category substring")
    p.set_defaults(func=cmd_ledger)

    p = sub.add_parser("patterns", help="rejection categories worth a house rule")
    p.add_argument("--min", type=int, default=2)
    p.set_defaults(func=cmd_patterns)

    args = ap.parse_args()
    sys.exit(args.func(args) if args.cmd else cmd_run(args))


if __name__ == "__main__":
    main()
