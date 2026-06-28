# Autograder

[A library](./Basic.lean) and [CLI tooling](./grade.sh) for validating lean-based homework submissions.

The student-facing part of this library is [Attributes.lean](./Attributes.lean).
It's distributed as part of the generated lean handouts.

## Attributes

Attributes, such as `@[graded 1.0]` tell the autograder how declarations should be graded.
Grading happens in the context of an ASSIGNMENT module (e.g. `_out/lf/student/lean/LF/Basics.lean`).
The student submits their solutions as SUBMISSION, and this is compared against ASSIGNMENT by .

Supported attributes:
- `@[graded <points>]` where `<points>` is a rational number in scientific notation.
  Used to mark a declaration to be graded with the specified amount of points.
- `@[graded ignore]`.
  Used to mark a definition as "ignored" by the comparison algorithm.
  Useful for "sorry" definitions that the student fills in -- otherwise the grader will error if the definition has been modified (which is counter-productive if the exercise is about coming up with a definition).
  > These could be easily detected automatically by looking for declarations which are defined as sorry.

Note: If it's more convenient, we can put grading attributes away from the declarations like this: `attribute [graded 2.0] Nat.add_zero`. This makes it easier to e.g. copy the code to the lean playground.

## Grading script

[`grade.sh`](./grade.sh) can be used to run the grading pipeline for a single file submission:

```sh
./grade.sh --assignment _out/lf/student/lean/ --submission _out/grading-test/LF/Basics.lean
```

- `--assignment` should point to the (unmodified) assignment project. The script uses the lake environment from this directory as the base for a temporary copy.
- `--submission` should point to an individual submission from the student.

> Note: `LF.Basics` is currently the only supported chapter.

The script starts by copying the assignment project to a temporary directory, let's call it `$TMPDIR`.
It also copies [`Main.lean`](./Main.lean) as `$TMPDIR/Main.lean`.
It then copies the submission to `$TMPDIR/Submission.lean` and adds
```toml
[[lean_lib]]
name = "Submission"
```
to `$TMPDIR/lakefile.toml`.

The actual grading happens by running `lake build` and `lake build Submission` followed by `lake env $AUTOGRADER_EXE LF.Basics Submission` in `$TMPDIR`.

> You can manually specify the path to `autograder` with the `AUTOGRADER_EXE` environment variable.
> If unset, it defaults to this project's `.lake/build/bin/autograder` which can be built with `make autograder`.

### Cleanup

The temporary directory `$TMPDIR` is not removed automatically.
The following command can be used to remove all temporary files used by the tool.

```
rm -vrf /tmp/autograder-**
```

## Debugging

To get debug logs, set the `AUTOGRADER_DEBUG=1` environment variable, e.g. by prefixing running the script with it:
```
AUTOGRADER_DEBUG=1 ./Autograder/grade.sh ...
```

## Design

The main problem the library solves is "when are two declarations from different environments considered equal" taking into account grading related details like when to ignore a definition (`@[graded ignore]`).

The obvious question is "why is comparing the expressions not sufficient?" and the rough answer is that expressions can refer to other constants by `Name`s, which are not compared when comparing the expressions syntax-to-syntax.

The approach taken is to traverse the "left" (assignment, unmodified) and "right" (submission) expression while recursively comparing any constants found in them.

The high-level algorithm is as follows, given a name and the constant with that name from both environments:

1. check if the constants are of the same kind (theorem/definition)
2. if they are theorems:
  1. check that their types are `deepSynEq`
  2. check the axioms used by the submission
3. if they are definitions:
  1. check that the types of the definitions match (even though definitions don't award points, this is helpful to point out the root cause of a mismatch)
  2. check the axioms used by the submission

> In addition we mark visited names to efficiently walk the closure of names in the constants.

The comparison `deepSynEq` is similar to syntactic equality, i.e. it will consider `n + 0 = id n` to be different from `n + 0 = n`.

For example, consider the following definition
```lean
@[irreducible]
def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | succ m' => succ (add n m')
  | zero => n
```
Making any of the following changes to the definition will be considered a change:
- Changing any name even in an α-compatible way
- Removing `@[irreducible]`
- Reordering the match arms

The following are for example not considered syntactic changes:
- Combining the arguments into `(n m : Nat)`
- Leaving out the explicit return type `: Nat`

## Known issues/limitations

- The `autograder` binary should check if it was built using the same toolchain as what is used by `PATH_TO_ASSIGNMENT_PROJECT`
- The points only support scientific numbers, e.g. `0.25`, but not rationals like `1/3` are represented.
- Autograder is not aware of our custom verso annotations like `GRADE_THEOREM`, `GRADE_MANUAL`
- `LF.Basics` is hard-coded in `grade.sh`
- The attributes are not supported on examples.
- `deepSynEqName` does not check some modifiers like `noncomputable`.

## Methodology & acknowledgements

This library was developed with ideas borrowed from the following projects:
- [lean4-autograder-main](https://github.com/robertylewis/lean4-autograder-main) is a more complete grading solution designed to integrate with [Gradeoscope](https://gradescope-autograders.readthedocs.io/en/latest/) and a heavy inspiration for this project.
  For example, using `@[...]` attributes for marking declarations is inspired by lean4-autograder-main.
  > NH: I did not manage to actually use the tool because I ran into an issue where the tool couldn't find something in `.lake/packages/autograder/`.
- [comparator](https://github.com/leanprover/comparator) and [lean4-export](https://github.com/leanprover/lean4export/) provided useful reading into how to work with the Lean [Environment](https://leanprover-community.github.io/mathlib4_docs/Lean/Environment.html) and how to recursively traverse expressions.
