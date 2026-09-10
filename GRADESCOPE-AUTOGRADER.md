# Gradescope autograder

This tool grades a student submission on Gradescope using [comparator-autograder](https://github.com/plclub/comparator-autograder); the `:::gradeTheorem` directive it reads is described in AUTOMATED-GRADING.md. Students may upload chapter `.lean` file(s) directly, or a folder or a zip containing the `.lean` file(s) as Gradescope will unpack them automatically.


## Build

Run `make` first (and watch for warnings), then one of:

```bash
python3 gradescope/package.py --chapter Basics              # grade chapter Basics
python3 gradescope/package.py --chapter Basics,Induction    # grade several chapters
python3 gradescope/package.py                               # grade all released chapters
```

This gives you `gradescope/autograder.zip`:

    autograder.zip
    |-- setup.sh          runs when Gradescope builds the image
    |-- run_autograder    runs once per submission; Gradescope's entrypoint
    |-- grade.py          runs once per submission to grade and report
    |-- config.env        this assignment's settings
    `-- context/          the Lean workspace, will be copied to /opt/grader/workspace
        |-- lakefile.toml
        |-- lean-toolchain
        |-- Challenge/     graded chapters from `grading`, the rest solved
        |-- Solution/      graded chapters as skeletons, the rest solved
        |-- SFLCompat.lean
        `-- SFLCompat/

Upload `autograder.zip` to Gradescope "Configure Autograder" and select Ubuntu 22.04 (the most recent version) as the base image to build.

The context is the released part of the textbook: the chapters in
`scripts/release_chapters.json` plus the support modules (`SFLCompat`, `CustomTactics`) that chapters import.

For both the **Challenge** and the **Solution** side, the chapters that are not part of the assignment (not passed as an argument to `package.py`) are copied from the `solutions` variant. For the **Challenge** side, the chapters we'd like to grade are taken from the `grading` variant of the released chapters that contain `autogradedProof` and `autogradedHole` attributes. For the **Solution** side, the chapters we'd like to grade are the student submission (or the empty `student` variant if the file is not found in the submission). Chapters that are not part of the assignment but are included in the submission are ignored but listed in
the output, so students will know that they uploaded the wrong files.

Exercises with a `GRADE_MANUAL` spec (without `(optional := true)`) should not carry the `autogradedProof` attribute. `package.py` reads them from the
chapter sources into `config.env` and outputs a reminder to create the manually graded components on Gradescope.


## Test locally

Example usage:

```bash
python3 gradescope/package.py --dev _out/lf/solutions/lean/LF/Basics.lean   # one file
python3 gradescope/package.py --dev path/to/dir  # a folder containing multiple chapters
```

## Notes

Sandbox is not currently supported on Gradescope. The comparator runs `lake` and `lean4export` through `$COMPARATOR_LANDRUN`. Real [landrun](https://github.com/zouuup/landrun) would confine them with Linux
Landlock: It needs kernel 5.13+, but Gradescope's runners are Amazon Linux 2 on 4.14. `setup.sh` therefore checks `uname -r` and skips building landrun when the kernel is too old, so grading runs through the `fake-landrun.sh` and logs `sandbox=NONE`.

