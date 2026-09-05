#!/usr/bin/env python3
# This file is maintained by Claude (AI-generated).
"""
proofread.py  —  Mechanism for a low-level proofreading pass over a chapter.

The pass is driven from a Claude session — `/proofread <Chapter>` — and Claude
issues these three commands in turn:

  start [CHAPTER]      name the chapter source and the round file to write
  apply [ROUND]        apply a written round and open its diff for review
  record [ROUND]       record what the author kept, after the review

Between `apply` and `record` the author reverts the edits they don't want, in
the chapter itself — one click per hunk in the Source Control gutter. That
review is a human gesture nothing can observe, which is why the phases are
separate commands. proofread/state.json remembers which round is in flight, so
`record` can come minutes or days later, from a different session.

You can also do a pass by hand: run with no arguments in a terminal and it
applies the waiting round, waits at a prompt while you review, and records when
you press return. Ctrl-C stops without recording; run it again to resume.

OTHER COMMANDS
  undo                 reverse the applied round and forget it
  status               what is in flight
  check                exit non-zero while a round is applied but unrecorded
  ledger [--cat C]     list recorded rejections
  patterns [--min N]   rejection categories that have earned a house rule

Rejections land in proofread/ledger.jsonl, keyed by a whitespace-normalized
hash of the (old, new) pair. A later round that proposes the same edit again —
in this chapter or any other — is silently dropped before you ever see it.

The round file is never something the author has to open. See PROOFREADING.md.
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
        print("Several rounds are waiting — name the one to apply:")
        for path, round_, live in rounds:
            print(f"  proofread.py apply {os.path.basename(path)}"
                  f"   {C_DIM}({round_['file']}, {live} edit"
                  f"{'' if live == 1 else 's'}){C_OFF}")
        sys.exit(1)
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
# a clean tree
# --------------------------------------------------------------------------
def dirty_paths():
    """Uncommitted changes, ignoring the proofreading machinery's own files —
    a round is written into proofread/rounds/ before anything can be applied."""
    r = subprocess.run(["git", "status", "--porcelain"], cwd=ROOT,
                       capture_output=True, text=True)
    if r.returncode != 0:
        return []
    paths = set()
    for line in r.stdout.splitlines():
        path = line[3:]
        if " -> " in path:                      # a rename: the new name matters
            path = path.split(" -> ", 1)[1]
        path = path.strip().strip('"')
        if path and not path.startswith("proofread/"):
            paths.add(path)
    return sorted(paths)


def require_clean_tree(allow_dirty=False):
    """A pass starts from a clean tree: the round's edits are then the only
    thing in the chapter, so reverting a hunk is unambiguous and `undo` is
    exact. Nothing else in the pass can tell the author's work from ours."""
    paths = dirty_paths()
    if not paths:
        return
    if allow_dirty:
        print(f"{C_YEL}working tree is dirty ({len(paths)} path"
              f"{'' if len(paths) == 1 else 's'}) — proceeding anyway{C_OFF}")
        return
    print(f"{C_RED}The working tree has uncommitted changes.{C_OFF} A "
          f"proofreading pass starts from a\nclean branch, so that the round's "
          f"edits are the only thing in the chapter:")
    for path in paths[:10]:
        print(f"  {path}")
    if len(paths) > 10:
        print(f"  {C_DIM}… and {len(paths) - 10} more{C_OFF}")
    sys.exit(f"\nCommit or stash them and start again "
             f"{C_DIM}(--allow-dirty overrides){C_OFF}")


# --------------------------------------------------------------------------
# chapters and round files
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


def next_round_path(source):
    chapter = os.path.basename(source)[:-len(".lean")]
    used = [int(m.group(1))
            for m in (re.search(r"-r(\d+)\.json$", path)
                      for path in glob.glob(os.path.join(ROUNDS, f"{chapter}-r*.json")))
            if m]
    return os.path.join(ROUNDS, f"{chapter}-r{max(used, default=0) + 1:02d}.json")


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


def before_path(round_path, round_):
    """The chapter as it was before the round — the left pane of the review.
    It keeps the chapter's extension so the diff is syntax-highlighted."""
    ext = os.path.splitext(round_["file"])[1]
    return re.sub(r"\.json$", "", round_path) + ".before" + ext


def write_before(round_path, round_, applied, after):
    """Reconstruct and keep the pre-round text; the review diffs against it."""
    before = after
    for p in applied:
        before = before.replace(p["new"], p["old"], 1)
    dest = before_path(round_path, round_)
    if os.path.exists(dest):
        os.remove(dest)
    with open(dest, "w") as f:
        f.write(before)
    os.chmod(dest, 0o444)        # read-only: only the right pane is the chapter
    return dest


def write_isolated_diff(round_path, round_, before):
    """A unified diff of just this round's edits, as a record of what was
    proposed — it stays readable after the author starts reverting hunks."""
    dest = diff_path(round_path)
    out = subprocess.run(
        ["diff", "-u", "-U", "2",
         "--label", round_["file"] + " (before this round)",
         "--label", round_["file"],
         before, os.path.join(ROOT, round_["file"])],
        capture_output=True, text=True).stdout
    with open(dest, "w") as f:
        f.write(out)
    return dest


def discard_before(round_path, round_):
    """Drop the snapshot once the round is recorded or undone."""
    path = before_path(round_path, round_)
    if os.path.exists(path):
        os.chmod(path, 0o644)
        os.remove(path)


def open_in_editor(*args):
    """Run `code` in the surrounding window; report whether it worked."""
    try:
        r = subprocess.run(["code", "--reuse-window", *args],
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

    before = write_before(round_path, round_, applied, text)
    dest = write_isolated_diff(round_path, round_, before)
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
def announce_review(round_path, round_, mode="diff"):
    """Put the review in front of the author and say what to do with it.

    Default is a real side-by-side diff editor — `code --diff` against the
    snapshot — because that lands on the two versions in one step, with no
    dependence on which source-control extension the author uses. `files`
    opens the chapter and the unified diff as plain tabs instead."""
    chapter = os.path.join(ROOT, round_["file"])
    before, dest = before_path(round_path, round_), diff_path(round_path)
    opened = False
    if mode == "diff":
        opened = open_in_editor("--diff", before, chapter)
    elif mode == "files":
        opened = open_in_editor(chapter, dest)

    print()
    if opened and mode == "diff":
        print(f"Opened a side-by-side diff in VS Code: "
              f"{C_BLD}{os.path.basename(before)}{C_OFF} on the left — the "
              f"chapter as it\nwas before the round — and the live "
              f"{C_BLD}{round_['file']}{C_OFF} on the right.")
    elif opened:
        print(f"Opened {C_BLD}{round_['file']}{C_OFF} and {rel(dest)} in VS Code.")
    else:
        print(f"Open the review with:\n"
              f"  {C_DIM}code --diff {rel(before)} {round_['file']}{C_OFF}")
    print(f"\nRevert what you don't want in the {C_BLD}right-hand pane{C_OFF} — "
          f"hover a change and click\nthe arrow in the gutter between the panes, "
          f"or just edit the text. The left pane\nis a read-only snapshot; "
          f"whatever you leave standing on the right is accepted.")
    print(f"{C_DIM}Other ways in: the Source Control view — the tree was clean "
          f"before the round, so\neverything it lists is this round — or "
          f"{rel(dest)} for the proposals as a list.{C_OFF}")


def wait_for_review(round_path, round_, mode="diff"):
    """Show the review, then block until the author is done."""
    announce_review(round_path, round_, mode)
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
    discard_before(round_path, round_)
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
# the commands Claude drives
# --------------------------------------------------------------------------
def resolve_round(name=None):
    """The round to act on: one named explicitly, the one in flight, or the
    single one waiting."""
    if name:
        for cand in (name, os.path.join(ROOT, name), os.path.join(ROUNDS, name),
                     os.path.join(ROUNDS, name + ".json")):
            if os.path.isfile(cand):
                return cand
        sys.exit(f"no such round: {name}")
    state = load_state()
    if state is not None:
        return os.path.join(ROOT, state["round"])
    return choose_round()


def no_rounds():
    print("No rounds are waiting. Ask Claude for one — `/proofread <Chapter>` "
          "in a Claude\nsession writes a round into proofread/rounds/ and "
          "carries the pass through.")
    return 1


def cmd_start(args):
    """Say which chapter to proofread and where its round file goes. Nothing
    here reads or touches the chapter — the proofreading itself is Claude's."""
    state = load_state()
    if state is not None:
        round_ = load_round(os.path.join(ROOT, state["round"]))
        sys.exit(f"{round_label(round_)} is already in flight — finish it with "
                 f"`proofread.py record`, or drop it with `proofread.py undo`")
    require_clean_tree(getattr(args, "allow_dirty", False))
    sources = chapter_sources()
    if not sources:
        sys.exit("no chapter sources found")
    if args.chapter:
        source = find_chapter(args.chapter)
        if source is None:
            sys.exit(f"no such chapter: {args.chapter}")
    else:
        source = sources[0]          # the one edited most recently
    dest = next_round_path(source)
    print(f"source: {source}")
    print(f"round:  {rel(dest)}")
    waiting = [round_ for _, round_, _ in available_rounds()]
    if waiting:
        print(f"{C_YEL}note{C_OFF}: unfinished round"
              f"{'' if len(waiting) == 1 else 's'} already waiting — "
              + ", ".join(round_label(r) for r in waiting))
    return 0


def cmd_apply(args):
    """Phase one: make the proposed edits and put the diff in front of the author."""
    state = load_state()
    if state is not None and state.get("phase") == "applied":
        round_path = os.path.join(ROOT, state["round"])
        round_ = load_round(round_path)
        print(f"{C_BLD}{round_label(round_)}{C_OFF} is already applied to "
              f"{round_['file']} — nothing re-applied.")
        announce_review(round_path, round_, getattr(args, "open", "diff"))
        return 0
    require_clean_tree(getattr(args, "allow_dirty", False))
    round_path = resolve_round(args.round)
    if round_path is None:
        return no_rounds()
    round_ = load_round(round_path)
    do_apply(round_path, round_)
    announce_review(round_path, round_, getattr(args, "open", "diff"))
    print(f"\nWhen the author is done reviewing: "
          f"{C_BLD}python3 scripts/proofread.py record{C_OFF}")
    return 0


def cmd_record(args):
    """Phase two: read the chapter back and record what survived."""
    state = load_state()
    if state is None or state.get("phase") != "applied":
        sys.exit("no round is applied — run `proofread.py apply` first")
    round_path = os.path.join(ROOT, state["round"])
    if args.round:
        named = resolve_round(args.round)
        if os.path.abspath(named) != os.path.abspath(round_path):
            sys.exit(f"{rel(round_path)} is the round in flight, not {rel(named)}")
    return do_reconcile(round_path, load_round(round_path))


def cmd_check(args):
    """Guard for a pre-commit hook: a round must not be committed unrecorded."""
    state = load_state()
    if state is None or state.get("phase") != "applied":
        return 0
    round_ = load_round(os.path.join(ROOT, state["round"]))
    print(f"{C_RED}{round_label(round_)} is applied to {round_['file']} but not "
          f"recorded.{C_OFF}\n"
          f"  Committing now would lose the rejections from this round.\n"
          f"  Finish the review, then: python3 scripts/proofread.py record\n"
          f"  Or drop the round:       python3 scripts/proofread.py undo\n"
          f"  {C_DIM}(git commit --no-verify commits anyway){C_OFF}")
    return 1


def cmd_run(args):
    """The whole pass by hand, in a terminal, with no Claude session."""
    state = load_state()

    if state is not None and state.get("phase") == "applied":
        # A pass was interrupted mid-review, or Claude applied the round.
        round_path = os.path.join(ROOT, state["round"])
        round_ = load_round(round_path)
        print(f"{C_BLD}{round_label(round_)}{C_OFF} — edits are already applied "
              f"to {round_['file']}")
        if interactive() and not wait_for_review(round_path, round_,
                                                 getattr(args, "open", "diff")):
            return 1
        return do_reconcile(round_path, round_)

    require_clean_tree(getattr(args, "allow_dirty", False))
    round_path = resolve_round()
    if round_path is None:
        return no_rounds()
    return run_round(round_path, getattr(args, "open", "diff"))


def run_round(round_path, mode="diff"):
    """Apply a chosen round, hand it to the author, record what they kept."""
    round_ = load_round(round_path)
    dest = do_apply(round_path, round_)

    if not interactive():
        print(f"\n{C_BLD}Next{C_OFF}\n"
              f"  1. Read {rel(dest)}.\n"
              f"  2. Revert the edits you don't want, in {round_['file']}.\n"
              f"  3. Run `proofread.py record` to save your choices.")
        return 0
    if not wait_for_review(round_path, round_, mode):
        return 1
    return do_reconcile(round_path, round_)


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
    discard_before(round_path, round_)
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
        print("  the author reviews it; then `proofread.py record` saves their "
              "choices")
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
        description="Mechanism for a proofreading pass over a chapter, driven "
                    "from a Claude session (`/proofread <Chapter>`). With no "
                    "arguments, runs the whole pass by hand in a terminal: "
                    "apply the proposed edits, review them, save your choices.")
    # SUPPRESS so that a subcommand's copy of the flag does not overwrite the
    # top-level one with its own default.
    dirty = argparse.ArgumentParser(add_help=False)
    dirty.add_argument("--allow-dirty", action="store_true",
                       default=argparse.SUPPRESS,
                       help="run even with uncommitted changes in the tree")
    ap.add_argument("--allow-dirty", action="store_true",
                    default=argparse.SUPPRESS,
                    help="run even with uncommitted changes in the tree")
    opener = argparse.ArgumentParser(add_help=False)
    opener.add_argument("--open", choices=("diff", "files", "none"),
                        default=argparse.SUPPRESS,
                        help="how to show the review: a side-by-side diff "
                             "editor (default), the chapter and the unified "
                             "diff as plain tabs, or nothing")
    ap.add_argument("--open", choices=("diff", "files", "none"),
                    default=argparse.SUPPRESS, help=argparse.SUPPRESS)
    sub = ap.add_subparsers(dest="cmd")

    p = sub.add_parser("start", parents=[dirty],
                       help="name the chapter and the round file to write")
    p.add_argument("chapter", nargs="?", help="chapter source path or name")
    p.set_defaults(func=cmd_start)

    p = sub.add_parser("apply", parents=[dirty, opener],
                       help="apply a written round and open its diff")
    p.add_argument("round", nargs="?", help="round file (default: the one waiting)")
    p.set_defaults(func=cmd_apply)

    p = sub.add_parser("record", help="record what the author kept, after review")
    p.add_argument("round", nargs="?", help="round file (default: the one in flight)")
    p.set_defaults(func=cmd_record)

    p = sub.add_parser("check", help="fail while a round is applied but unrecorded")
    p.set_defaults(func=cmd_check)

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
