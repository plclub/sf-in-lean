# Automated Grading

TODO this is outdated!

SF-in-Lean comes with automated grading infrastructure that's built on top of [robertylewis/lean4-autograder-main](https://github.com/robertylewis/lean4-autograder-main) (which we have a fork of in [plclub/lean4-autograder-main](https://github.com/plclub/lean4-autograder-main) containing updates and fixes).
We refer to "lean4-autograder-main" with just "the autograder".

The autograder has the following features:
- It can grade a submission against a solution file which contains grading attributes that look like `attribute [autogradedProof points] name1 name2 ...`, see [running locally](#running-locally)

## Autograding Directive

To add automated grading to an exercise, use the `:::gradeTheorem <POINTS> <NAME1> ...` directive to instruct the autograder to grade any number of theorems.
Use double quotes around `<POINTS>` if you use a decimal separator.
Integer points can be written without double quotes.

For example, in the following exercise, each `nand_test1/2/3/4` gives `0.25` points (for a total of 1 point) if proven correctly in the submission:

````
::::exercise (rating := 1) (name := "nand")
```lean
def nand (b1 : MyBool) (b2 : MyBool) : MyBool
  := solution!(match b1 with
  | MyBool.true => not b2
  | MyBool.false => MyBool.true)

theorem nand_test1 : nand MyBool.true  MyBool.false = MyBool.true  := solution!(by rfl)
theorem nand_test2 : nand MyBool.false MyBool.false = MyBool.true  := solution!(by rfl)
theorem nand_test3 : nand MyBool.false MyBool.true  = MyBool.true  := solution!(by rfl)
theorem nand_test4 : nand MyBool.true  MyBool.true  = MyBool.false := solution!(by rfl)
```

:::gradeTheorem "0.25" nand_test1 nand_test2 nand_test3 nand_test4
:::
::::
````

Instead of using the autograder's `autogradedDef` attributes, we use `autogradedTheorem`s on some of the examples (or characterizing lemmas) that follow the definition.
These need to be named so they are `theorem`s rather than `example`s.

## Running Locally (example)

After building all the variants (including `grading`) for LF (with `make lf`), change directory to `_out/lf/grading/lean`.
To test the generated student lean file for Basics, run

```
lake exe autograder --local ../../student/lean/LF/Basics.lean LF/Basics.lean
```

Likewise, to test the generated solutions, from the same directory run

```
lake exe autograder --local ../../solutions/lean/LF/Basics.lean LF/Basics.lean
```

## Implementation Details

Our integration with the autograder happens in multiple places

- [SFLMeta/Grade.lean](SFLMeta/Grade.lean) contains the definition for the `:::gradeTheorem` directive.
- `walkBlock` in [SFLMeta/Save/Extract.lean](SFLMeta/Save/Extract.lean) saves the grading attributes to the extracted Lean files.

## Match Deduplication

Due to Lean's elaborate match deduplication system, we need to avoid using structural recursion in solution blocks that are followed by non-solution definition that uses a match with the same data type.

For example (adapted from `Logic.lean`):

```lean
-- SOLUTION
def List.IsNil {α : Type} (l : List α) : Prop :=
  match l with
  | [] => True
  | _ :: _ => False
-- END SOLUTION

def List.In {α : Type} (x : α) (xs : List α) : Prop :=
  match xs with
  | [] => False
  | x' :: xs' => x = x' ∨ In x xs'
```

Here `List.In` has a hidden dependency on `List.IsNil` because of the similar `match` expressions.

The issue that this causes is that once the solution is removed in the grading variant, `List.In` generates its own matcher `List.In.match_1`, which is not the same name as `List.IsNil.match_1` and therefore comparator gives a "constant does not match" failure.