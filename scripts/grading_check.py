#!/usr/bin/env python3
# Authors: Niklas Halonen (xhalo32)
# NOTE: This is fully human-written code (unlike many other scripts in this directory)
#
# This script tests the autograder for a subset of volumes and variants.
# Normally, it tests autograding of the entire volume at once, but the `--module` argument can be used to pick a specific module to grade, e.g. `LF.Logic`.

# The script exiting successfully is determined by variant-specific assertions:
# - student variant: all exercises fail with `illegalAxiom`
# - solutions variant: all exercises pass

# There are two output formats:
# - stats: prints a tableau with statistics about passing and failing tests
# - json: prints an aggregated structure with detailed information about each autograded theorem

# Examples:
# - `python scripts/grading_check.py --no-make --volumes LF --variants solutions --stats --json`
#   checks all solutions in LF, doesn't run 'make', prints out statistics and the detailed json
# - `python scripts/grading_check.py --no-make --volumes LF --module LF.Lists --variants student --stats --json`
#   only checks `LF.Lists`, doesn't run 'make', prints out statistics and the detailed json
# - `python scripts/grading_check.py --no-make --volumes LF HL TS --variants student solutions --stats --json`
#   checks all solutions in LF, doesn't run 'make', prints out statistics and the detailed json

from subprocess import Popen, run, STDOUT
from pathlib import Path
from fractions import Fraction
import os, sys, tempfile, shutil, json, argparse

def runshell(cmd):
    run(cmd, shell=True, check=True)

ingore_pattern = shutil.ignore_patterns(".lake", "lakefile.toml", "lake-manifest.json", "lean-toolchain", "SFLCompat.lean", "SFLCompat")

def replace_everywhere(directory, find, replace):
    # https://stackoverflow.com/questions/4205854/recursively-find-and-replace-string-in-text-files
    for root, dirs, files in directory.walk():
        for file in files:
            filepath = root / file
            with open(filepath) as f:
                s = f.read()
            s = s.replace(find, replace)
            with open(filepath, "w") as f:
                f.write(s)

# See `manifestRequire` in SFLMeta/Save/Project.lean
# NOTE: Unlike the Lean version, here we must pass `«»` "quotes" explicitly
def manifest_require(manifest, name):
    for pkg in manifest["packages"]:
        if pkg["name"] == name:
            assert pkg["type"] == "git"
            git = pkg["url"]
            rev = pkg["rev"]
            return f"""[[require]]
name = "{name}"
git = "{git}"
rev = "{rev}"
"""

def create_lakefile(manifest):
    requires = [
        manifest_require(manifest, "batteries"),
        manifest_require(manifest, "«comparator-autograder-lib»"),
    ]
    return f"""name = "grading-check"
version = "0.1.0"
defaultTargets = ["Challenge", "Solution"]

{"\n".join(requires)}
[[lean_lib]]
name = "Challenge"
globs = ["Challenge.+"]

[[lean_lib]]
name = "Solution"
globs = ["Solution.+"]

[[lean_lib]]
name = "SFLCompat"
"""

all_volumes = ["LF", "HL", "TS"]

def runtest(toolchain, comparator_autograder, lean4export, landrun, root_path, variant, volume, module):
    with tempfile.TemporaryDirectory(delete=True) as tmpdir:
        print(f"[grading_check.py]: using temporary directory '{tmpdir}'")
        with open("lake-manifest.json") as f:
            lakefile = create_lakefile(json.loads(f.read()))
        with (Path(tmpdir) / "lakefile.toml").open("w+") as f:
            f.write(lakefile)
        with (Path(tmpdir) / "lean-toolchain").open("w+") as f:
            f.write(toolchain)
        shutil.copy(root_path / "_out" / volume.lower() / "grading" / "lean" / "SFLCompat.lean", Path(tmpdir))
        shutil.copytree(root_path / "_out" / volume.lower() / "grading" / "lean" / "SFLCompat", Path(tmpdir) / "SFLCompat")
        
        shutil.copytree(root_path / "_out" / volume.lower() / "grading" / "lean", Path(tmpdir) / "Challenge", ignore=ingore_pattern)
        shutil.copytree(root_path / "_out" / volume.lower() / variant / "lean", Path(tmpdir) / "Solution", ignore=ingore_pattern)
        for vol in all_volumes:
            replace_everywhere(Path(tmpdir) / "Challenge", f"import {vol}", f"import Challenge.{vol}")
            replace_everywhere(Path(tmpdir) / "Solution", f"import {vol}", f"import Solution.{vol}")
        format_pipe_r, format_pipe_w = os.pipe()
        env = {
            # We grade the top-level volume file that imports each chapter
            "AUTOGRADER_CHALLENGE": f"Challenge.{volume}",
            "AUTOGRADER_SOLUTION": f"Solution.{volume}",
            "AUTOGRADER_SKIP_IMPORTS": "false" if module is None else "true", # skip imports only when testing a specific module
            "AUTOGRADER_EXPORT_PATH": f"/proc/self/fd/{format_pipe_w}",
            "AUTOGRADER_EXPORT_FORMAT": "json",
            "COMPARATOR_LEAN4EXPORT": lean4export,
            "COMPARATOR_LANDRUN": landrun,
            "PATH": os.environ.get("PATH"),
        }
        if module:
            env["AUTOGRADER_CHALLENGE"] = f"Challenge.{module}"
            env["AUTOGRADER_SOLUTION"] = f"Solution.{module}"
        cmd = f"lake env '{comparator_autograder}'"
        print(f"[grading_check.py]: running '{cmd}'")
        with Popen(cmd, shell=True, cwd=tmpdir, pass_fds=[format_pipe_w], env=env) as p:
            os.close(format_pipe_w)
        with os.fdopen(format_pipe_r) as f:
            return json.loads(f.read())

def collect_stats(results):
    stats = {
        "pass": 0,
        # Below are from FailureReason in ComparatorAutograder/Basic.lean
        "constNotFoundInChallenge": 0,
        "constNotFoundInSolution": 0,
        "wrongKind": 0,
        "constDoesNotMatch": 0,
        "holeDoesNotMatch": 0,
        "illegalAxiom": 0,
        "bug": 0,
    }
    illegal_axioms = 0
    failures = 0
    for r in results["theoremReports"]:
        if r["error"] != None:
            stats[next(iter(r["error"]))] += 1
        else:
            stats["pass"] += 1
    return stats

def count_points(results):
    total = Fraction(0)
    for r in results["theoremReports"]:
        total += Fraction(r["points"]["num"], r["points"]["den"])
    return total

def assert_results(aggregate_results):
    for vol in aggregate_results:
        if "student" in aggregate_results[vol]:
            for r in aggregate_results[vol]["student"]["theoremReports"]:
                assert r["error"] is not None and next(iter(r["error"])) == "illegalAxiom"
        if "solutions" in aggregate_results[vol]:
            for r in aggregate_results[vol]["solutions"]["theoremReports"]:
                assert r["error"] is None

def main():
    parser = argparse.ArgumentParser(description='Test automated grading in SF-in-lean.')

    parser.add_argument('--module', help="Specify the module to test (skips imports). Select only one volume.")
    parser.add_argument('--volumes', nargs="+", default=[all_volumes[0]], choices=all_volumes)
    parser.add_argument('--variants', nargs="+", default=["student"], choices=["student", "solutions"])
    parser.add_argument('--stats', action='store_true', help="Print out failure reason statistics for each volume and variant.")
    parser.add_argument('--json', action='store_true', help="Print out an aggregated JSON of the results")
    parser.add_argument('--no-make', action='store_true', help="Don't run 'make'")
    parser.add_argument('--no-build', action='store_true', help="Don't build lean4export and comparatorautograder")

    args = parser.parse_args()
    if not (len(args.volumes) == 1) ** (args.module is not None):
        print("only one volume can be selected when using --module")
        return

    if not args.no_make:
        runshell("make")

    if not args.no_build:
        runshell("lake build lean4export comparatorautograder")

    cwd = Path.cwd()
    comparator_autograder = cwd / ".lake/packages/comparator-autograder/.lake/build/bin/comparatorautograder"
    lean4export = cwd / ".lake/packages/lean4export/.lake/build/bin/lean4export"
    landrun = cwd / ".lake/packages/comparator/scripts/fake-landrun.sh"

    with open("lean-toolchain") as f:
        toolchain = f.read()

    aggregate_results = {}
    for vol in args.volumes:
        vol_dir = cwd / "_out" / vol.lower()
        for variant in args.variants:
            print(f"[grading_check.py]: checking volume {vol} variant {variant}")
            results = runtest(toolchain, comparator_autograder, lean4export, landrun, cwd, variant, vol, args.module)

            aggregate_results[vol] = aggregate_results.get(vol) or {}
            aggregate_results[vol][variant] = results

    if args.stats:
        for vol in aggregate_results:
            print(f"Volume {vol}:")
            for variant in aggregate_results[vol]:
                total_points = count_points(aggregate_results[vol][variant])
                print(f"  Variant {variant} (max points: {total_points} = {float(total_points)}):")
                stats = collect_stats(aggregate_results[vol][variant])
                for reason in stats:
                    print(f"    {reason}: {stats[reason]}")

    if args.json:
        print(json.dumps(aggregate_results))

    assert_results(aggregate_results)

if __name__ == "__main__":
    main()
