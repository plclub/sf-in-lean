#!/usr/bin/env python3
# This file is maintained by Claude (AI-generated).
"""
proofread.py  —  Drives a low-level proofreading pass over a chapter.

Claude writes a *round* — a JSON file of anchored edits under proofread/rounds/
— and leaves it there. Doing the pass is one command with no arguments:

    python3 scripts/proofread.py

Run it with nothing waiting and it starts Claude on a chapter for you, then
picks up the round Claude writes; leave Claude and the pass carries on.

It asks which chapter to proofread (skipping the question when only one round
is waiting), makes every proposed edit, opens a diff of just those edits in VS
Code, and waits. You revert the ones you don't want, press return, and it
records your rejections and reports any pattern worth a house rule.

Stop at any point with Ctrl-C; run it again and it picks up where it left off.
The round file is never something you have to open. See PROOFREADING.md.

Rejections land in proofread/ledger.jsonl, keyed by a whitespace-normalized
hash of the (old, new) pair. A later round that proposes the same edit again —
in this chapter or any other — is silently dropped before you ever see it.

OTHER COMMANDS
  propose [CHAPTER]    have Claude write a round now, then run it
  undo                 reverse the applied round and forget it
  status               what is in flight
  ledger [--cat C]     list recorded rejections
  patterns [--min N]   rejection categories that have earned a house rule

Run non-interactively (a pipe, CI) and it falls back to two invocations: the
first applies and writes the diff, the second reconciles.
"""

import argparse
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROUNDS = os.path.join(ROOT, "proofread", "rounds")
LEDGER = os.path.join(ROOT, "proofread", "ledger.jsonl")
STATE = os.path.join(ROOT, "proofread", "state.json")

# Two accepted edits closer than this many lines apart usually land in the same
# git hunk, so the editor cannot revert one without the other.
HUNK_GAP = 4

C_RED, C_GRN, C_YEL, C_DIM, C_BLD, C_OFF = (
    "\033[31m", "\033[32m", "\033[33m", "\033[2m", "\033[1m", "\033[0m")
if not sys.stdout.isatty():
    C_RED = C_GRN = C_YEL = C_DIM = C_BLD = C_OFF = ""


def interactive():
    return sys.stdin.isatty() and sys.stdout.isatty()


def rel(path):
    return os.path.relpath(path, ROOT)


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


def mark_completed(path):
    """A finished round stays on disk as a record, but is no longer offered."""
    with open(path) as f:
        round_ = json.load(f)
    round_["completed"] = True
    with open(path, "w") as f:
        json.dump(round_, f, indent=1, ensure_ascii=False)
        f.write("\n")


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


# --------------------------------------------------------------------------
# choosing a round
# --------------------------------------------------------------------------
def available_rounds():
    """Unfinished rounds with at least one edit not already declined."""
    ledger = load_ledger()
    out = []
    for path in sorted(glob.glob(os.path.join(ROUNDS, "*.json"))):
        with open(path) as f:
            round_ = json.load(f)
        if round_.get("completed") or "proposals" not in round_:
            continue
        live = [p for p in round_["proposals"] if key_of(p) not in ledger]
        if live:
            out.append((path, round_, len(live)))
    return out


def choose_round():
    rounds = available_rounds()
    if not rounds:
        return None
    if len(rounds) == 1:
        path, round_, live = rounds[0]
        print(f"{C_BLD}{round_label(round_)}{C_OFF} — {live} proposed "
              f"edit{'' if live == 1 else 's'} to {round_['file']}")
        return path
    if not interactive():
        sys.exit("several rounds are waiting; run this from a terminal to choose")
    print(f"{C_BLD}Which chapter?{C_OFF}")
    for i, (_, round_, live) in enumerate(rounds, 1):
        print(f"  {i}. {round_['file']}  {C_DIM}({round_label(round_)}, "
              f"{live} edit{'' if live == 1 else 's'}){C_OFF}")
    while True:
        try:
            answer = input("number (or return to cancel): ").strip()
        except EOFError:
            return None
        if not answer:
            return None
        if answer.isdigit() and 1 <= int(answer) <= len(rounds):
            return rounds[int(answer) - 1][0]
        print("not one of the numbers above")


# --------------------------------------------------------------------------
# asking Claude for a round
# --------------------------------------------------------------------------
def volumes():
    """Directories holding chapter sources — one per Targets<Vol>.lean."""
    out = []
    for path in sorted(glob.glob(os.path.join(ROOT, "Targets*.lean"))):
        vol = os.path.basename(path)[len("Targets"):-len(".lean")]
        if os.path.isdir(os.path.join(ROOT, vol)):
            out.append(vol)
    return out


def chapter_sources():
    """Hand-maintained chapter sources, most recently edited first. A generated
    <Ch>Verso.lean is never proofread."""
    out = []
    for vol in volumes():
        for path in glob.glob(os.path.join(ROOT, vol, "*.lean")):
            if not path.endswith("Verso.lean"):
                out.append(path)
    out.sort(key=lambda path: -os.path.getmtime(path))
    return [rel(path) for path in out]


def find_chapter(name):
    """A chapter source named by path or by bare chapter name."""
    hits = [s for s in chapter_sources()
            if s == name or os.path.basename(s)[:-len(".lean")] == name]
    return hits[0] if len(hits) == 1 else None


def ask_chapter():
    sources = chapter_sources()
    if not sources:
        return None
    default = sources[0]
    print(f"{C_BLD}Which chapter should Claude proofread?{C_OFF} "
          f"{C_DIM}(return for {default}, Ctrl-C to stop){C_OFF}")
    while True:
        try:
            answer = input("chapter: ").strip()
        except (KeyboardInterrupt, EOFError):
            print()
            return None
        if not answer:
            return default
        found = find_chapter(answer)
        if found:
            return found
        print("no such chapter — give a path or a chapter name, e.g. "
              f"{os.path.basename(default)[:-len('.lean')]}")


def next_round_path(source):
    chapter = os.path.basename(source)[:-len(".lean")]
    used = [int(m.group(1))
            for m in (re.search(r"-r(\d+)\.json$", path)
                      for path in glob.glob(os.path.join(ROUNDS, f"{chapter}-r*.json")))
            if m]
    return os.path.join(ROUNDS, f"{chapter}-r{max(used, default=0) + 1:02d}.json")


def proofread_prompt(source, dest):
    return (
        f"Proofread {source}.\n\n"
        f"Read PROOFREADING.md in full first — its 'Writing a round' section, "
        f"the house rules, and the known non-issues — and read the recorded "
        f"rejections with `python3 scripts/proofread.py ledger`. Nothing already "
        f"declined or covered by a house rule may be proposed again.\n\n"
        f"Then write the round to {rel(dest)}: "
        f'{{"file", "chapter", "round", "proposals": [{{"id", "cat", "old", '
        f'"new", "why"}}]}}, anchored exactly as that section requires.\n\n'
        f"Do not edit {source} yourself and do not run scripts/proofread.py "
        f"other than its ledger and patterns commands — the author applies the "
        f"round. Write the round file, say briefly what is in it, and stop.")


def solicit_round(chapter=None):
    """Nothing is waiting: start Claude on a chapter, then pick up what it writes."""
    claude = shutil.which("claude")
    if claude is None or not interactive():
        print("No rounds are waiting. Ask Claude to proofread a chapter — it "
              "writes one into proofread/rounds/ and this command picks it up.")
        return None
    source = chapter or ask_chapter()
    if source is None:
        return None
    dest = next_round_path(source)
    before = {path for path, _, _ in available_rounds()}
    print(f"\nStarting Claude on {C_BLD}{source}{C_OFF} — it writes "
          f"{rel(dest)}.\n{C_DIM}Leave Claude (/exit, or Ctrl-D) when the round "
          f"is written and this command carries on with it.{C_OFF}\n")
    try:
        subprocess.run([claude, proofread_prompt(source, dest)], cwd=ROOT)
    except (OSError, subprocess.SubprocessError) as e:
        print(f"{C_RED}could not run claude: {e}{C_OFF}")
        return None
    fresh = [r for r in available_rounds() if r[0] not in before]
    if not fresh:
        print(f"\n{C_YEL}No new round in {rel(ROUNDS)} — nothing to apply.{C_OFF}")
        return None
    if len(fresh) == 1:
        path, round_, live = fresh[0]
        print(f"\n{C_BLD}{round_label(round_)}{C_OFF} — {live} proposed "
              f"edit{'' if live == 1 else 's'} to {round_['file']}")
        return path
    return choose_round()


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
        # Reconciling decides accepted-vs-rejected by asking which of the two
        # strings is in the file, so neither may contain the other. The test is
        # whitespace-insensitive — a rewrap is not a distinguishable edit —
        # except when the edit is *only* whitespace (collapsing a run of blank
        # lines), where the raw strings are exactly what reconciling compares.
        a, b = (old, new) if norm(old) == norm(new) else (norm(old), norm(new))
        if a in b or b in a:
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
# applying
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


def open_in_editor(*paths):
    """Open files in the surrounding VS Code window; report whether it worked."""
    try:
        r = subprocess.run(["code", "--reuse-window", *paths],
                           capture_output=True, text=True, timeout=20)
        return r.returncode == 0
    except (FileNotFoundError, subprocess.SubprocessError):
        return False


def do_apply(round_path, round_):
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

    print(f"\n{C_GRN}{len(applied)} edit{'' if len(applied) == 1 else 's'} "
          f"applied{C_OFF} to {round_['file']}")
    if dropped:
        print(f"{C_DIM}{dropped} skipped: already declined in a previous round{C_OFF}")
    counts = {}
    for p in applied:
        counts[p.get("cat", "?")] = counts.get(p.get("cat", "?"), 0) + 1
    for cat, n in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"  {n:3d}  {cat}")
    if shared:
        print(f"\n{C_YEL}These pairs sit in one git hunk — reverting one reverts "
              f"both, so edit those spots by hand if you want only one:{C_OFF}")
        for pa, pb, gap in shared:
            print(f"  {pa['id']} + {pb['id']} ({gap} line{'' if gap == 1 else 's'} "
                  f"apart)  {C_DIM}{pa.get('cat', '')} / {pb.get('cat', '')}{C_OFF}")
    return dest


# --------------------------------------------------------------------------
# reviewing and reconciling
# --------------------------------------------------------------------------
def wait_for_review(round_, dest):
    """Open the diff and the chapter, then block until the author is done."""
    opened = open_in_editor(os.path.join(ROOT, round_["file"]), dest)
    print()
    if opened:
        print(f"Opened {C_BLD}{rel(dest)}{C_OFF} and {round_['file']} in VS Code.")
    else:
        print(f"Read {C_BLD}{rel(dest)}{C_OFF} — just this round's edits, "
              f"nothing else pending.\n"
              f"  {C_DIM}code {rel(dest)} {round_['file']}{C_OFF}")
    print(f"Revert the edits you don't want, in {round_['file']} — one click per "
          f"hunk\nin the Source Control gutter.")
    try:
        input(f"\n{C_BLD}Press return when you're done{C_OFF} "
              f"{C_DIM}(Ctrl-C to stop and resume later){C_OFF} ")
    except (KeyboardInterrupt, EOFError):
        print(f"\n\nStopped. Your edits are still in place; run "
              f"{C_BLD}python3 scripts/proofread.py{C_OFF} again to finish,\n"
              f"or {C_BLD}python3 scripts/proofread.py undo{C_OFF} to drop the "
              f"whole round.")
        return False
    return True


def do_reconcile(round_path, round_):
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
    mark_completed(round_path)

    print(f"\n{C_BLD}{round_label(round_)}{C_OFF} — "
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

    if state is not None and state.get("phase") == "applied":
        # A pass was interrupted mid-review, or this is the second of two
        # non-interactive invocations.
        round_path = os.path.join(ROOT, state["round"])
        round_ = load_round(round_path)
        print(f"{C_BLD}{round_label(round_)}{C_OFF} — edits are already applied "
              f"to {round_['file']}")
        if interactive() and not wait_for_review(round_, diff_path(round_path)):
            return 1
        return do_reconcile(round_path, round_)

    round_path = state and os.path.join(ROOT, state["round"]) or choose_round()
    if round_path is None:
        round_path = solicit_round()
    if round_path is None:
        return 1
    return run_round(round_path)


def run_round(round_path):
    """Apply a chosen round, hand it to the author, record what they kept."""
    round_ = load_round(round_path)
    dest = do_apply(round_path, round_)

    if not interactive():
        print(f"\n{C_BLD}Next{C_OFF}\n"
              f"  1. Read {rel(dest)}.\n"
              f"  2. Revert the edits you don't want, in {round_['file']}.\n"
              f"  3. Run this command again to save your choices.")
        return 0
    if not wait_for_review(round_, dest):
        return 1
    return do_reconcile(round_path, round_)


def cmd_propose(args):
    if load_state() is not None:
        sys.exit("a round is already in flight; finish it or `proofread.py undo`")
    source = None
    if args.chapter:
        source = find_chapter(args.chapter)
        if source is None:
            sys.exit(f"no such chapter: {args.chapter}")
    round_path = solicit_round(source)
    if round_path is None:
        return 1
    return run_round(round_path)


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
          f"{round_label(round_)} left for another day")
    print(f"{C_DIM}nothing was written to the ledger{C_OFF}")
    return 0


def cmd_status(args):
    state = load_state()
    if state is None:
        waiting = available_rounds()
        if waiting:
            print("nothing in flight; waiting rounds:")
            for _, round_, live in waiting:
                print(f"  {round_['file']}  {C_DIM}({round_label(round_)}, "
                      f"{live} edit{'' if live == 1 else 's'}){C_OFF}")
        else:
            print("nothing in flight, no rounds waiting")
    else:
        round_path = os.path.join(ROOT, state["round"])
        round_ = load_round(round_path)
        phase = state.get("phase", "pending")
        print(f"{round_label(round_)}: {len(round_['proposals'])} proposals, "
              f"phase {phase}")
        if phase == "applied":
            print(f"  edits are in {round_['file']}; "
                  f"diff at {rel(diff_path(round_path))}")
        print("  run `python3 scripts/proofread.py` to carry on")
    n = len(load_ledger())
    print(f"\n{n} declined edit{'' if n == 1 else 's'} on record")
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
        description="Proofread a chapter. With no arguments, runs the whole "
                    "pass: pick a chapter, apply the proposed edits, review "
                    "them, save your choices.")
    sub = ap.add_subparsers(dest="cmd")

    p = sub.add_parser("propose", help="have Claude write a round now, then run it")
    p.add_argument("chapter", nargs="?", help="chapter source path or name")
    p.set_defaults(func=cmd_propose)

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
