#!/usr/bin/env python3
# Claude-generated (see CLAUDE.md, "Marking AI-generated material").
"""Build the Gradescope autograder, and run it locally without Docker.

    package.py                 -> autograder.zip, grading every released chapter
    package.py --chapter X,Y   ...grading only those
    package.py --dev           stage the same workspace locally
    package.py --dev FILE      ...and grade FILE through it

Run `make` first: both are assembled from the extracted chapters in _out/.
"""
import argparse, json, os, re, shutil, subprocess, sys, tempfile, zipfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import grade

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
LIB = "comparator-autograder-lib"


def pin(name):
    """(url, rev) from the book's lake-manifest.json, so the grader builds
    against exactly the revision the book does."""
    for p in json.loads((REPO / "lake-manifest.json").read_text())["packages"]:
        if p["name"].strip("«»") == name:
            return p["url"], p["rev"]
    sys.exit(f"{name} not found in lake-manifest.json")


def lakefile():
    """The two libraries, plus what the chapters need: the attribute library the
    grading build imports, and batteries, which SFLCompat pulls in."""
    req = "".join(f'\n[[require]]\nname = "{n}"\ngit = "{u}"\nrev = "{r}"\n'
                  for n, (u, r) in ((n, pin(n)) for n in ("batteries", LIB)))
    return ('name = "sfl-grader"\nversion = "0.1.0"\n' + req +
            '\n[[lean_lib]]\nname = "Challenge"\n\n[[lean_lib]]\nname = "Solution"\n'
            '\n[[lean_lib]]\nname = "SFLCompat"\n')


def released(vol):
    """Chapters this volume currently releases to students, from
    scripts/release_chapters.json -- the same allow-list package_release.py
    uses, so the autograder cannot cover more of the book than the students
    have been given. A volume absent from that file releases everything."""
    try:
        cfg = json.loads((REPO / "scripts" / "release_chapters.json")
                         .read_text(encoding="utf-8"))
    except OSError:
        return None
    return cfg.get(vol.lower())


def expand(vol, chapters):
    """Resolve "*" to the chapters students actually have, so staging, build
    targets and config.env all work from one concrete list."""
    if not chapters:
        sys.exit("at least one chapter is required")
    if len(chapters) != len(set(chapters)):
        sys.exit("each chapter may be named only once")
    rel_list = released(vol)
    if chapters == ["*"]:
        if rel_list is not None:
            if not rel_list:
                sys.exit(f"{vol} releases no chapters yet "
                         f"(scripts/release_chapters.json), so there is nothing "
                         f"to grade.")
            print(f"  '*' -> released chapters: {', '.join(rel_list)}")
            return list(rel_list)
        allc = sorted(p.stem for p in (REPO / "_out" / vol.lower() / "solutions"
                                       / "lean" / vol).glob("*.lean"))
        print(f"  '*' -> every chapter ({len(allc)}); no release allow-list found")
        return allc
    if rel_list is not None:
        extra = [c for c in chapters if c not in rel_list]
        if extra:
            sys.exit(f"{', '.join(extra)}: not released, so there is nothing to "
                     f"assign.\nAdd it to scripts/release_chapters.json "
                     f"(currently {', '.join(rel_list) or 'empty'}) once students "
                     f"have it.")
    return chapters


def manual_exercises(vol, chapters):
    """Exercises that need to be manually graded (without `optional`).

    Keyed on the `GRADE_MANUAL` spec, which is the grading instruction and
    carries the points; `(manual := true)` only labels the heading. An exercise
    with `GRADE_MANUAL` but not `(manual := true)` is a bug in the chapter. 
    A `:::grade` body is written either fenced or in backticks, so match both."""
    found = []
    for c in chapters:
        src = REPO / vol / f"{c}.lean"
        if not src.is_file():
            continue
        text = src.read_text(encoding="utf-8")
        optional = set()
        for args in re.findall(r"(?m)^:{3,}exercise(.*)$", text):
            name = re.search(r'name := "([^"]+)"', args)
            if name and "optional := true" in args:
                optional.add(name.group(1))
        for names in re.findall(r"(?m)^`?GRADE_MANUAL\s+[0-9./]+\s*:\s*([^`\n]+)", text):
            found += [n for n in names.split() if n not in optional]
    return found


def stage(vol, chapters, dest):
    """Copy the volume into both trees, imports namespaced.

    Graded chapters come from the `grading` extract on the Challenge side (it
    carries the autogradedProof/autogradedHole attributes -- nothing else does)
    and the `student` skeleton on the Solution side, so an exercise left undone
    scores zero.

    Every chapter the assignment does *not* grade comes from `solutions`, on
    both sides. Chapters import each other, and a skeleton dependency is full of
    `sorry`: a student's Induction proofs would inherit sorryAx from an ungraded
    Basics. The two sides must use the same variant, or the comparison hits a
    definition that differs and reports constDoesNotMatch.

    What ships is the released book -- see below. Earlier-volume dependencies
    bundled with the extract are staged from `solutions` on both sides. What
    gets *compiled* is narrower still: setup.sh names only the graded chapters
    as build targets and lake works out the rest."""
    base = REPO / "_out" / vol.lower()
    solutions = base / "solutions" / "lean" / vol
    if not solutions.is_dir():
        sys.exit(f"missing {solutions} -- run 'make' first")
    graded = set(chapters)
    names = sorted(p.name for p in solutions.glob("*.lean"))

    # The released book, not the whole repo: the chapters students have, plus
    # the support modules (SFLCompat, CustomTactics) that chapters import but
    # that no release list names. Safe because chapters never import a later
    # one, so a release list already holds everything its chapters need.
    rel = released(vol)
    if rel is not None:
        in_book = set(re.findall(r"(?m)^import %s\.(\w+)" % vol,
                                 (base / "solutions" / "lean" / f"{vol}.lean")
                                 .read_text(encoding="utf-8")))
        names = [n for n in names if Path(n).stem in set(rel) or Path(n).stem not in in_book]

    dependencies = [
        src
        for dep_vol in ("LF", "HL", "TS")
        if dep_vol != vol
        for src in sorted((solutions.parent / dep_vol).rglob("*.lean"))
    ]

    for side, variant in (("Challenge", "grading"), ("Solution", "student")):
        for name in names:
            src = base / (variant if Path(name).stem in graded else "solutions") \
                  / "lean" / vol / name
            if not src.is_file():
                sys.exit(f"missing {src} -- run 'make' first")
            out = dest / side / vol / name
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(grade.rewrite(src.read_text(encoding="utf-8"), side),
                           encoding="utf-8")

        # HL and TS extracts bundle the earlier-volume modules they import.
        # They are trusted dependencies, so both sides use the solved versions.
        for src in dependencies:
            out = dest / side / src.relative_to(solutions.parent)
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(grade.rewrite(src.read_text(encoding="utf-8"), side),
                           encoding="utf-8")
    # SFLCompat is a library beside the volume, not a chapter, and is identical
    # in every variant: one shared copy, and `import SFLCompat` needs no
    # namespacing.
    for src in [solutions.parent / "SFLCompat.lean",
                *sorted((solutions.parent / "SFLCompat").rglob("*.lean"))]:
        out = dest / src.relative_to(solutions.parent)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_bytes(src.read_bytes())

    print(f"  staged {len(names) + len(dependencies)} module(s) x2 + SFLCompat -- graded: "
          f"{', '.join(sorted(graded))}; the rest from solutions")


def assemble(vol, chapters, dest, sandbox=True):
    """Everything the archive holds except its own version stamp."""
    toolchain = (REPO / "lean-toolchain").read_text().strip()
    url, rev = pin("comparator-autograder")
    stage(vol, chapters, dest / "context")
    (dest / "context" / "lakefile.toml").write_text(lakefile())
    (dest / "context" / "lean-toolchain").write_text(toolchain)
    (dest / "config.env").write_text(
        f"VOLUME={vol}\nCHAPTER={','.join(chapters)}\nLEAN_TOOLCHAIN={toolchain}\n"
        f"COMPARATOR_AUTOGRADER_URL={url}\nCOMPARATOR_AUTOGRADER_REV={rev}\n"
        f"MANUAL={','.join(manual_exercises(vol, chapters))}\n"
        + ("" if sandbox else "SFL_LANDRUN=/opt/grader/bin/fake-landrun.sh\n"))
    for f in ("setup.sh", "run_autograder", "grade.py"):
        shutil.copyfile(HERE / f, dest / f)


def write_zip(src, out):
    """Gradescope wants the files at the archive root, not a folder containing
    them, and needs setup.sh and run_autograder executable."""
    out.unlink(missing_ok=True)
    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as z:
        for f in sorted(p for p in src.rglob("*") if p.is_file()):
            info = zipfile.ZipInfo(str(f.relative_to(src)))
            info.create_system = 3        # Unix, else the mode bits are ignored
            mode = 0o755 if f.name in ("setup.sh", "run_autograder") else 0o644
            info.external_attr = (0o100000 | mode) << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info, f.read_bytes())


def dev(vol, chapters, submission):
    """The workspace setup.sh builds, staged directly instead of through a
    Docker image -- seconds, rather than a full image build."""
    ws = Path(os.environ.get("SFL_WORKSPACE",
                             Path(tempfile.gettempdir()) / "sfl-grader-ws"))
    # Restage unless the workspace is both complete (`pristine` is written last)
    # and built for this same assignment (`.chapters`) -- otherwise a Basics
    # workspace silently grades an Induction run against the wrong Challenge.
    want = f"{vol}:{','.join(chapters)}"
    stamp = ws / ".chapters"
    staged_for = stamp.read_text(encoding="utf-8").strip() if stamp.exists() else None
    if not (ws / "pristine").exists() or staged_for != want:
        print(f"staging {ws} for {want}…")
        shutil.rmtree(ws, ignore_errors=True)
        (ws / "bin").mkdir(parents=True)
        stage(vol, chapters, ws)
        (ws / "lakefile.toml").write_text(lakefile())
        (ws / "lean-toolchain").write_text((REPO / "lean-toolchain").read_text().strip())
        for b in (".lake/packages/comparator-autograder/.lake/build/bin/comparatorautograder",
                  ".lake/packages/lean4export/.lake/build/bin/lean4export",
                  ".lake/packages/comparator/scripts/fake-landrun.sh"):
            if not (REPO / b).is_file():
                sys.exit(f"missing {b}\nrun: lake build lean4export comparatorautograder")
            # Landlock is Linux-only, so the dev loop always uses the shim.
            name = "landrun" if b.endswith("fake-landrun.sh") else Path(b).name
            (ws / "bin" / name).symlink_to(REPO / b)
        targets = [f"{side}.{vol}.{c}" for c in chapters
                   for side in ("Challenge", "Solution")]
        subprocess.run(["lake", "build", *targets], cwd=ws, check=True,
                       stdout=subprocess.DEVNULL)
        shutil.copytree(ws / "Solution", ws / "pristine", dirs_exist_ok=True)
        stamp.write_text(want, encoding="utf-8")
    if not submission:
        return print(f"ready: {ws}\ngrade with: package.py --dev path/to/a.lean")
    # Undo the previous submission, exactly as run_autograder does.
    shutil.copytree(ws / "pristine", ws / "Solution", dirs_exist_ok=True)
    sub, res = Path(tempfile.mkdtemp()), Path(tempfile.mkdtemp())
    try:
        if Path(submission).is_dir():      # a folder, as a student would zip it
            shutil.copytree(submission, sub, dirs_exist_ok=True)
        else:
            shutil.copyfile(submission, sub / Path(submission).name)
        subprocess.run([sys.executable, str(HERE / "grade.py")], check=True, stdout=subprocess.DEVNULL,
                       env={**os.environ, "SFL_WORKSPACE": str(ws),
                            "SFL_BIN": str(ws / "bin"), "SFL_SUBMISSION": str(sub),
                            "SFL_RESULTS": str(res / "results.json"),
                            "SFL_VOLUME": vol, "SFL_CHAPTER": ",".join(chapters),
                            "SFL_MANUAL": ",".join(manual_exercises(vol, chapters))})
        print(json.dumps(json.loads((res / "results.json").read_text()), indent=2))
    finally:
        shutil.rmtree(sub, ignore_errors=True)
        shutil.rmtree(res, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--volume", default="LF")
    ap.add_argument("--chapter", default="*",
                    help='chapter(s) this assignment grades: "*" (the default) '
                         'for every released chapter, or a concrete list such as '
                         '"Basics" or "Basics,Postscript"')
    ap.add_argument("--out", type=Path, default=HERE / "autograder.zip")
    ap.add_argument("--no-sandbox", action="store_true",
                    help="grade without landrun, to rule it in or out")
    ap.add_argument("--dev", nargs="?", const="", metavar="PATH",
                    help="stage a local workspace; with a .lean file or a volume "
                         "folder, grade it")
    a = ap.parse_args()
    chapters = expand(a.volume, [c.strip() for c in a.chapter.split(",") if c.strip()])
    if a.dev is not None:
        return dev(a.volume, chapters, a.dev or None)
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        assemble(a.volume, chapters, tmp, sandbox=not a.no_sandbox)
        write_zip(tmp, a.out)
        print(f"wrote {a.out} ({a.out.stat().st_size // 1024} KB)")
        manual = manual_exercises(a.volume, chapters)
        if manual:
            print("  reminder: " + ", ".join(manual) + " needs to be manually graded. Please create questions on Gradescope.")


if __name__ == "__main__":
    main()
