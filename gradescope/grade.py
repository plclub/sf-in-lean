#!/usr/bin/env python3
# Claude-generated (see CLAUDE.md, "Marking AI-generated material").
"""Grade one uploaded chapter and write Gradescope's results.json.

The submission becomes the Solution side of a comparator-autograder run; the
Challenge side is the chapter's grading build, which carries the grading
attributes. Points come from those attributes, not from anything here.
"""
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

WORKSPACE  = Path(os.environ.get("SFL_WORKSPACE",  "/opt/grader/workspace"))
BIN        = Path(os.environ.get("SFL_BIN",        "/opt/grader/bin"))
SUBMISSION = Path(os.environ.get("SFL_SUBMISSION", "/autograder/submission"))
RESULTS    = Path(os.environ.get("SFL_RESULTS",    "/autograder/results/results.json"))
VOLUME     = os.environ.get("SFL_VOLUME",  "LF")
# The chapters this assignment grades: the only ones scored, and the only ones a
# submission may replace. package.py resolves "*" before writing config.env, so
# this is always a concrete list.
CHAPTERS   = [c.strip() for c in os.environ.get("SFL_CHAPTER", "Basics").split(",")
              if c.strip()]
MANUAL = [e.strip() for e in os.environ.get("SFL_MANUAL", "").split(",") if e.strip()]
IMPORT = re.compile(r"(?m)^import (LF|HL|TS)\b")
# Under Gradescope's 600s, so an overrun is our message, not a platform kill.
TIMEOUT    = int(os.environ.get("SFL_TIMEOUT", "480"))
_T0 = time.monotonic()
SANDBOXED = False        # set in main() from sandbox_kind()


def log(msg):
    """Progress on stdout, which Gradescope shows to instructors only. Flushed,
    because when the platform kills a run this is all there is to go on."""
    print(f"[sfl] +{time.monotonic() - _T0:6.1f}s  {msg}", flush=True)


def time_left(cmd):
    """Seconds left for `cmd`, keeping the whole run below `TIMEOUT`."""
    remaining = TIMEOUT - (time.monotonic() - _T0)
    if remaining <= 0:
        raise subprocess.TimeoutExpired(cmd, TIMEOUT)
    return remaining


def clean_build():
    """Discard cached root-package outputs before a build or comparison.

    Lean's cache uses filesystem timestamps. Replacing a submission in the
    same timestamp tick can otherwise reuse the previous student's `.olean`.
    Clearing the root package also prevents a submitted elaborator from
    carrying modified Challenge artifacts into the comparison.
    """
    subprocess.run(["lake", "clean", "sfl-grader"], cwd=WORKSPACE, check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                   timeout=time_left("clearing build artifacts"))


def rewrite(text, side):
    """`import LF.Basics` -> `import Challenge.LF.Basics`, so both libraries can
    coexist in one workspace. setup.sh applies this when staging and main()
    applies it to the submission."""
    return IMPORT.sub(rf"import {side}.\1", text)


def human(names):
    """Chapter names as a student sees them: `Basics.lean`, `Induction.lean`."""
    return ", ".join(f"`{n}.lean`" for n in names)


def listing(names):
    """`a`, `b` and `c` -- prose, so the last item gets an "and"."""
    q = [f"`{n}`" for n in names]
    return q[0] if len(q) == 1 else ", ".join(q[:-1]) + " and " + q[-1]


def emit(output, tests=None):
    """Write results.json and stop. Gradescope reads nothing else."""
    payload = {"output": output, "output_format": "md", "test_output_format": "md"}
    if tests is None:
        payload["score"] = 0.0
    else:
        payload["tests"] = tests
    RESULTS.parent.mkdir(parents=True, exist_ok=True)
    RESULTS.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    sys.exit(0)


def find_submissions():
    """What the student uploaded, split into what this assignment grades and
    what it does not.

    We allow the submission to be `.lean` files, a folder, or a zip. Gradescope
    unpacks archives on arrival, so all three arrive as files and a recursive
    search covers them. Anything under a dot-directory or `__MACOSX` is skipped:
    a student who zips their project folder brings `.lake` along, and its
    packages contain plenty of `.lean` files that are not their work.

    Extra chapters are ignored rather than rejected, but they are reported, so
    a student who did the work in the wrong file finds out instead of silently
    scoring zero. If the same chapter appears twice we emit an error message."""
    wanted = set(CHAPTERS)
    graded, ignored, dupes = {}, [], {}
    for p in sorted(SUBMISSION.rglob("*.lean")):
        rel = p.relative_to(SUBMISSION)
        if not p.is_file() or any(part.startswith(".") or part == "__MACOSX"
                                  for part in rel.parts):
            continue
        if p.stem not in wanted:
            ignored.append(str(rel))
        elif p.stem in graded:
            dupes.setdefault(p.stem, [str(graded[p.stem].relative_to(SUBMISSION))]).append(str(rel))
        else:
            graded[p.stem] = p
    if dupes:
        emit("**Your submission has more than one copy of the same chapter.**\n\n"
             + "\n".join(f"- `{k}.lean`: " + ", ".join(f"`{v}`" for v in vs)
                         for k, vs in dupes.items())
             + "\n\nRemove the duplicates and resubmit, so it is unambiguous which "
               "one should be graded.")
    if not graded:
        emit(f"**Nothing this assignment grades was found in your submission.**\n\n"
             f"It grades {human(sorted(wanted))}."
             + (f"\n\nIgnored: {', '.join(f'`{n}`' for n in ignored[:8])}."
                if ignored else ""))
    return graded, ignored


MAX_ERRORS = 5

def clean_log(raw):
    """Reduce `lake build` output to the diagnostics a student can act on. lake
    interleaves progress bars, the full `lean` command line (`trace:`) and every
    `#check` in the chapter (`info:`) with the real errors, and one bad
    definition cascades into a dozen more."""
    kept, keeping, errors = [], False, 0
    for line in raw.splitlines():
        m = re.match(r"^(error|warning|info|trace):", line)
        if m:
            keeping = m.group(1) in ("error", "warning")
            errors += 1 if line.startswith("error:") else 0
        elif re.match(r"^[✔✖⚠ℹ]", line):       # a lake progress line
            keeping = False
        if keeping and errors <= MAX_ERRORS:
            kept.append(line)
    text = "\n".join(kept).replace(f"Solution/{VOLUME}/", "")
    if errors > MAX_ERRORS:
        text += f"\n\n... and {errors - MAX_ERRORS} further error(s)."
    if errors > 1:
        text += ("\n\nLater errors are often knock-on effects of the first, so "
                 "start at the top.")
    return text or raw[-2000:]


def chapter_points(ch):
    """What a chapter is worth, read off the Challenge side. Needed to score a
    chapter that failed to compile: its theorems cannot be reported, but they
    still have to count against the total."""
    f = WORKSPACE / "Challenge" / VOLUME / f"{ch}.lean"
    return sum((Fraction(p) * len(n.split()) for p, n in
                re.findall(r"(?m)^attribute \[autogradedProof ([0-9./]+)\] (.*)$",
                           f.read_text(encoding="utf-8"))), Fraction(0))


def explain(error, name=None):
    """A comparator FailureReason, as something a student can act on."""
    reason = next(iter(error))
    body = error[reason] if isinstance(error[reason], dict) else {}
    target = body.get("target")
    if reason == "illegalAxiom":
        axiom = body.get("axiomName", "")
        if "sorryAx" in str(axiom):
            return "Incomplete: this proof still contains `sorry`."
        return f"Uses the axiom `{axiom}`, which is not allowed here."
    if reason == "constDoesNotMatch":
        if target == name:
            return ("This theorem's statement is not the one you were given. Prove "
                    "the statement as written and do not change it.")
        return (f"`{target}` differs from the version you were given. Fill in the "
                f"parts marked `sorry`, but leave what you were handed unchanged.")
    if reason == "constNotFoundInSolution":
        return (f"`{target}` is missing from your submission. Do not rename or "
                f"delete the declarations you were given; just fill them in.")
    if reason == "wrongKind":
        return (f"`{target}` is declared as a different kind of declaration than "
                f"expected (for example `def` where a `theorem` was asked for). "
                f"Please do not modify the declarations you were given.")
    if reason == "holeDoesNotMatch":
        return (f"`{target}` must keep the name and type you were given; please "
                f"write the definition only.")
    return f"`{target}` does not match what was expected ({reason})."


def autograde(challenge, solution):
    """Run comparator-autograder over the workspace, returning its JSON report."""
    # A file, not a pipe: reading the report before draining stderr can deadlock
    # once the comparator fills the stderr buffer. Kept outside the workspace,
    # which the sandbox does not make writable.
    with tempfile.TemporaryDirectory(prefix="sfl-autograder-") as tmp:
        report = Path(tmp) / "report.json"
        env = {**os.environ,
               "AUTOGRADER_CHALLENGE": challenge,
               "AUTOGRADER_SOLUTION": solution,
               "AUTOGRADER_SKIP_IMPORTS": "true",  # this chapter only
               "AUTOGRADER_EXPORT_PATH": str(report),
               "AUTOGRADER_EXPORT_FORMAT": "json",
               "COMPARATOR_LEAN4EXPORT": str(BIN / "lean4export"),
               # setup.sh puts either real landrun or the unsandboxed shim here.
               "COMPARATOR_LANDRUN": os.environ.get("SFL_LANDRUN", str(BIN / "landrun"))}
        log(f"comparing {challenge}")
        p = subprocess.Popen(["lake", "env", str(BIN / "comparatorautograder")],
                             cwd=WORKSPACE, env=env, stdout=subprocess.DEVNULL,
                             stderr=subprocess.PIPE)
        try:
            _, err = p.communicate(timeout=time_left("comparison"))
        except subprocess.TimeoutExpired:
            p.kill()
            p.communicate()
            raise
        log(f"comparison done rc={p.returncode}")
        raw = report.read_text(encoding="utf-8") if report.is_file() else ""
    if p.returncode != 0 or not raw.strip():
        emit("**The grader could not evaluate your submission.** Your file compiled, "
             "but the comparison step failed. This is usually a problem with the "
             "grader rather than your work, so please tell the course staff.\n\n```\n"
             + err.decode(errors="replace")[-2000:] + "\n```")
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        emit("**The grader produced an invalid report.** Please tell the course staff.\n\n"
             "```\n" + raw[-2000:] + "\n```")


def sandbox_kind():
    """Which landrun is in play. setup.sh installs the real one and the shim at
    the same path, so the path alone says nothing: look at the file. The real
    binary is an ELF; the vendored fake-landrun.sh is a shell script."""
    p = Path(os.environ.get("SFL_LANDRUN", BIN / "landrun"))
    try:
        magic = p.read_bytes()[:4]
    except OSError:
        return f"MISSING ({p})"
    if magic == b"\x7fELF":
        return f"landrun binary ({p})"
    return f"NONE -- unsandboxed shim ({p})"


def cgroup_memory():
    """The container's memory cap, cgroup v2 then v1. Worth logging: Lean is
    memory-hungry, and a starved container looks like a hang, not an error."""
    for f in ("/sys/fs/cgroup/memory.max",
              "/sys/fs/cgroup/memory/memory.limit_in_bytes"):
        try:
            return Path(f).read_text().strip()
        except OSError:
            pass
    return "?"


def main():
    global SANDBOXED
    kind = sandbox_kind()
    SANDBOXED = kind.startswith("landrun")
    log("sandbox=" + kind)
    log(f"cpus={os.cpu_count()} mem={cgroup_memory()}")
    graded, ignored = find_submissions()
    for stem, src in graded.items():
        (WORKSPACE / "Solution" / VOLUME / f"{stem}.lean").write_text(
            rewrite(src.read_text(encoding="utf-8", errors="replace"), "Solution"),
            encoding="utf-8")

    # Every chapter the assignment covers; any chapter that needs to be graded but not 
    # submitted keeps the skeleton of `sorry`s (from the student variant), which scores zero.
    runs = [(f"Challenge.{VOLUME}.{c}", f"Solution.{VOLUME}.{c}") for c in CHAPTERS]
    what = human(CHAPTERS)

    # Build and grade each chapter on its own, so one that does not compile
    # costs only its own score instead of the whole submission.
    tests, broken = [], []
    for challenge, solution in runs:
        log(f"building {solution}")
        built = subprocess.run(["lake", "build", solution], cwd=WORKSPACE,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               timeout=time_left(f"building {solution}"))
        log(f"built {solution} rc={built.returncode}")
        name = solution.split(".")[-1]
        if built.returncode != 0:
            errlog = clean_log(built.stdout.decode(errors="replace"))
            # A break in an earlier chapter stops the later ones too, so blame
            # whichever file the errors are actually in -- otherwise a student
            # hunts for a bug that is not in the file we named.
            culprits = sorted({m for m in re.findall(r"(?m)^error: (\w+)\.lean:", errlog)})
            own = name in culprits
            if own:
                broken.append(name)
                why = ("This file does not compile, so none of its exercises could be graded.")
            else:
                why = ("This file could not be graded because "
                       + (human(culprits) if culprits else "a chapter it imports")
                       + " does not compile.")
            tests.append({"name": f"{name} (not graded)", "score": 0.0,
                          "max_score": float(chapter_points(name)),
                          "status": "failed",
                          "output": why + "\n\n```\n" + errlog + "\n```"})
            continue
        # Building the submission just ran the student's code, which may have
        # written into .lake. Clearing it makes the comparator rebuild
        # Challenge from source instead of trusting those files. That costs a
        # full recompile, so only do it under landrun: unsandboxed, the code
        # can write anywhere in the container (?!), so protecting .lake alone 
        # would not help.
        if SANDBOXED:
            log("clearing cached build artifacts before comparison")
            clean_build()
        for t in autograde(challenge, solution)["theoremReports"]:
            pts = Fraction(t["points"]["num"], t["points"]["den"])
            ok = t["error"] is None
            tests.append({"name": t["name"]["const"],
                          "score": float(pts) if ok else 0.0, "max_score": float(pts),
                          "status": "passed" if ok else "failed",
                          "output": "Correct." if ok
                                    else explain(t["error"], t["name"]["const"])})

    got = sum(Fraction(str(t["score"])) for t in tests)
    total = sum(Fraction(str(t["max_score"])) for t in tests)
    failed = sum(1 for t in tests if t["status"] == "failed")
    note = ""
    if broken:
        note += (f"\n\n**{human(broken)} did not compile**, so none of "
                 f"{'its' if len(broken) == 1 else 'their'} exercises could be "
                 f"graded. See the failing check below for the errors.")
    if MANUAL:
        note += (f"\n\n{listing(MANUAL)} {'is' if len(MANUAL) == 1 else 'are'} "
                 f"graded manually after the due date.")
    if ignored:
        note += (f"\n\n*This assignment grades {what}. Ignored "
                f"{len(ignored)} other file(s): {', '.join(f'`{n}`' for n in ignored[:6])}"
                + ("…" if len(ignored) > 6 else "") + ".*")
    emit(f"Graded {what} — **{float(got):g} / {float(total):g}** points"
         + (f"; {failed} of {len(tests)} checks still need work." if failed
            else ". All checks passed.") + note, tests=tests)


if __name__ == "__main__":
    try:
        main()
    except subprocess.TimeoutExpired as e:
        log(f"TIMED OUT running {e.cmd}")
        emit("**Grading timed out.** If your file compiles quickly in your editor "
             "this is a problem with the autograder, not your work — please tell "
             "the course staff.")
