#!/usr/bin/env python3
# Authors: Niklas Halonen (xhalo32)
# NOTE: This is fully human-written code (unlike many other scripts in this directory)

from subprocess import check_output, Popen, STDOUT
from pathlib import Path
import os, sys

def runshell(cmd):
    p = Popen(cmd, shell=True)
    os.waitpid(p.pid, 0)

def is_autograded_file(path):
    with path.open() as f:
        src = f.read()
        return "import AutograderLib" in src and "attribute [autogradedProof" in src

def find_autograded_files(grading_lean_dir, volume):
    for root, dirs, files in (grading_lean_dir / volume).walk():
        root_path = Path(root)
        for file in files:
            path = root_path / file
            if is_autograded_file(root_path / file):
                yield file

USAGE = """USAGE: grading_check.py [OPTIONS]

OPTIONS:
    --no-make               Don't run 'make' before the check
    --lf                    Check _out/lf/grading/lean
    --ts                    Check _out/ts/grading/lean
    --hl                    Check _out/hl/grading/lean
"""

VOLUME_ARGS = {"--lf": "LF", "--ts": "TS", "--hl": "HL"}

def main():
    if "--help" in sys.argv:
        print(USAGE)
        return
    if not "--no-make" in sys.argv:
        runshell("make")
    vols = [VOLUME_ARGS[k] for k in sys.argv if k in VOLUME_ARGS]
    for vol in vols:
        grading_lean_dir = Path("_out") / vol.lower() / "grading" / "lean"
        print(f"[grading_check.py]: checking volume {vol}")
        for file in find_autograded_files(grading_lean_dir, vol):
            # TODO make this a function that abstracts over "student"
            cmd = f"lake exe autograder --local ../../student/lean/{vol}/{file} {vol}/{file}"
            print(f"[grading_check.py]: running {cmd}")
            output = check_output(cmd, shell=True, cwd=grading_lean_dir)
            sorrys = output.count(b"Proof contains sorry")
            passes = output.count(b"Passed all tests")
            # print(output)
            print(f"[grading_check.py]: {file}: sorrys: {sorrys}, passes: {passes}")

if __name__ == "__main__":
    main()