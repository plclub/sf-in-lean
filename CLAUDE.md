# Instructions for Claude

This file contains instructions to help Claude assist in creating and 
maintaining SF-in-Lean materials.

The file `CONTRIBUTING.md` details the rules and conventions to be 
followed by (human and AI) contributions to this project. 

## Checking to_verso outputs

To check a chapter survived translation by the to_verso script: 
Regenerate `<Ch>Verso.lean`, then confirm every identifier/number
token and comment word in `<Ch>.lean` appears in the Verso output,
excluding the intentionally-dropped tokens described below.

**Intentionally dropped by `to_verso` — do not treat as content loss:**

* `/- test_* -/` single-identifier test-case labels (decided 2026-06-15).
* Hand-written Lean output annotations `/- ==> … -/` and `/- ===> … -/`: Verso's
  InlineLean renders the *real, verified* output live, so these drift-prone
  copies are redundant.
* `####…` separator/divider lines in comments.
* The marker keywords themselves once consumed: `ADMITDEF`, `ADMITTED`,
  `SOLUTION`, `FULL`, `TERSE`, `HIDE`, `EX`/`EX1`/…, `GRADE_THEOREM`,
  `GRADE_MANUAL`, `INSTRUCTORS`.

**Must be preserved** (these were bugs, now fixed): block-style author notes
(`/- MWH: … -/`, `/- BCP: … -/`) → `:::dev`; `-- GRADE_THEOREM …` → `:::grade`.

