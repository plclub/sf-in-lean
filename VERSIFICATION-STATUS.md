<!-- AI-generated (Claude), 2026-07-14.  Status dump + instructions for
     finishing the LF Verso conversion.  Delete when the conversion is done. -->

# LF → Verso conversion: status and remaining work

Branch: `bcp-versification3` (all work **uncommitted** in the working tree as
of this writing; BCP wants to review before committing).

## Done: chapters graduated into the real book (`LF.lean`)

**Basics** (previously), plus this pass: **Induction, UsingLean, Lists, Poly,
Tactics, Logic** — each `{include LF.<Ch>Verso}`d in `LF.lean`.
`make lf` passes end-to-end: all three variants (student/solutions/terse)
build, and the three *generated* Lake projects under `_out/lf/*/lean/`
compile. `LFDraft.lean` is now empty (everything graduated).

Per-chapter verification that nothing is lost from the bare `.lean`:

1. `lake build LF.<Ch>` (bare chapter compiles);
2. regenerate with `python3 scripts/to_verso.py LF/<Ch>.lean LF/<Ch>Verso.lean`;
3. `scripts/check_verso_prose.py` — **0 missing spans on every chapter**;
4. `scripts/check_verso_markers.py` — every count mismatch hand-traced to a
   benign mechanism (see "reading the marker warnings" below);
5. a scoping spot-check (session tool) verifying each FULL/TERSE region's text
   lands inside the matching `::::full`/`::::terse` directive in the output;
6. `lake build LF.<Ch>Verso`, then `make lf` after adding it to `LF.lean`.

### Reading the marker-check warnings (all verified benign this pass)

- Adjacent same-type regions fuse into one directive (`_fuse_full_blocks`).
- FULL/TERSE regions inside an exercise are flattened by design (directives
  can't nest there); content stays visible in all builds.
- Markers inside `-- HIDE` regions are captured verbatim into the `::::hide`
  body — an EX/QUIZ/GRADE "missing" from the directive count but present in
  the hide body is correct behavior (e.g. IndProp's two quizzes).
- `/- HIDE: … -/`-style notes are dev notes (→ ```dev), not hide regions.
- Marker-only lines (`-- TERSE: HIDEFROMHTML`, `-- TERSE: /FOLD`, …) emit
  nothing on purpose.

## Infrastructure changes this pass (review these!)

`scripts/to_verso.py`:
- **` ```savedImport ` blocks**: `_extract_imports` plants `--SAVEDIMPORT`
  sentinels for volume-module imports; the renderer emits a `savedImport`
  code block at that spot. The saver copies its body as *live code* into all
  three generated chapter files (this fixed the extracted-project build:
  extracted Induction had no `import LF.Basics`). The Verso module *header*
  still gets the `…Verso`-rewritten import for the book build.
- **Bare in-comment `FULL`/`TERSE` are region markers spanning comments**
  (Poly writes whole sections this way, closed by `/FULL` in a later
  comment). Only the `FULL:`/`TERSE:` *prefix* form is comment-local.
  Consequence: an unbalanced bare marker no longer self-heals at the end of
  the comment — chapter sources must be balanced (several missing closes were
  restored, see below).
- **Docstring interiors pass through verbatim** (`_lean_comment_balance` +
  `code_comment_depth` in `tokenize`): consecutive blank lines inside
  `/-- … -/` no longer collapse, which `#guard_msgs` docstrings require.
- Exercise names may contain `'` (`EX4A? (ev'_ev)`); block-form
  `/- QUIETSOLUTION -/` is recognized (routes like SOLUTION).

`SFLMeta/Save.lean`:
- `Block.savedImport` extension + `@[code_block] savedImport` expander +
  `walkBlock` case (emits body verbatim into teacher/student/terse buffers).
- `supportModules`: `LF/CustomTactics.lean` is copied into the generated
  projects (graduated chapters import it; it is self-contained, core-only
  imports).

Chapter sources — marker/structure repairs (found by the checks):
- Induction: `zero.5` → `0.5` grade ratings; `EX2 (mul_one)` → `(mul_two)`;
  indented `-- GRADE_THEOREM` dedented + `-- []` closes added; nested
  "Tip: Rewriting by definitions" comment flattened to prose (BCP may prefer
  moving it outside the exercise as a real `##` heading instead).
- UsingLean: chapter-goals note → `/- TODO: … -/`; INSTRUCTORS note → block
  form (its continuation lines were leaking into book prose); missing
  `-- /FULL` after the imports; two GRADE lines dedented.
- Lists: `-- QUIZ --` / `-- FULL --` trailing-dash typos; stray `/FULL`
  *inside* the Micro-Sermon comment → real `-- /FULL`; missing `-- /TERSE`
  after the two length quizzes.
- Poly: "One small problem…" restored to `FULL:` prefix form (port had
  dropped the colon, leaving an unclosed bare FULL); lost `/- FULL -/` open
  before mumble_grumble restored (per Poly.v).
- Logic: `-- /FULl` typo; two missing `-- /FULL` (placed per Logic.v); one
  Rocq-style TERSE-inside-FULL alternation (~L295) restructured because the
  directive model can't express it (the WORKINCLASS example after it is now
  terse-visible, matching its marking).
- Five dropped `TERSE: ***` slide breaks (`-- TERSE:` with lost payload):
  Lists 64, Poly 939, Tactics 134 & 1324, IndProp 574.
- Tactics: `theorem zero_leb` added next to `succ_leb_succ` (deleted from
  UsingLean 2026-06-29 but still used by IndProp).

## Remaining work

### IndProp (deferred — needs more work)

Bare `LF.IndProp` **builds again** (was broken): `zero_leb` restored;
`exists 0; rw [double_zero]` → `exists 0` (×2, `exists` closes the goal);
`inversion contra` → `cases contra` on the empty relation (`inversion` can't
handle a no-constructor indexed inductive).

`LF/IndPropVerso.lean` conversion is mostly fixed but **not done**:
- Fixed already: 7 coqdoc `*`/`**` headings → `#`/`##`; 3 raw inference-rule
  displays wrapped in `[[ … ]]`; `]]]` closer typo; dangling `/--` docstring →
  prose; mid-proof unindented comment in `ev_Even` firsttry indented into the
  code run; dead Rocq proof joined to its code run.
- **Remaining #1 — `OPEN COMMENT WHEN HIDING SOLUTIONS` needs a real
  mechanism.** The four NoStutter examples use the idiom
  `example … := by` + empty `/- ADMITTED -/ /- /ADMITTED -/` pair +
  `/- OPEN COMMENT WHEN HIDING SOLUTIONS -/ …proof… /- CLOSE COMMENT … -/`.
  Intended semantics (from the Rocq build): solutions build shows the proof
  live; the **student build shows the proof too, but wrapped in a comment**
  (students are told to "just uncomment" the suggested proofs, since their
  own `nostutter` definition may differ), with the empty ADMITTED pair
  supplying the admit. Neither to_verso nor SFLMeta handles the tag today —
  it leaks into the Verso output as literal prose and splits the code block.
  (An earlier attempt this session to move the proofs into ADMITTED regions
  was WRONG — it hides the suggested proofs from students — and has been
  reverted; the source is back to the original form.) Design needed: e.g. a
  marker that the `lean` block expander turns into a comment in the
  student/terse variants and live code in the solutions variant (a cousin of
  the `-- SOLUTION`/`-- END SOLUTION` textual rewriting, but emitting the
  body commented-out instead of `-- FILL IN HERE`). Also used once in
  `old/orig-lf-files/ImpCEvalFun.v` for a future volume.
- **Remaining #2**: one `(deterministic) timeout at isDefEq` in the
  pigeonhole_principle block (~Verso L4054). The bare chapter compiles the
  same proof, so it's the extra student/terse-variant elaboration; likely
  needs `set_option maxHeartbeats` in the source or a slimmer proof.
- Marker check on IndProp reports `QUIZ 2 → 0 FLATTENED`: verified benign
  (both quizzes are inside `-- HIDE` regions, captured verbatim into
  `::::hide` bodies).

### IndPropRegexp (not started)

Bare `LF.IndPropRegexp` builds (warnings only). Run the same per-chapter
pipeline once IndProp's Verso builds (it imports IndProp).

### Maps (not started; known blocker)

`LF.MapsVerso` builds standalone but **cannot join the book yet**: it
redefines `PartialMap.update` (etc.) already defined by ListsVerso's
partial-maps preview section, and Verso imports share one environment (see
the old note in LFDraft.lean's history). Resolve by renaming/namespacing one
side or dropping the Lists preview definitions, then run the pipeline.

### Typeclasses

Skipped per BCP (no `LF/Typeclasses.lean` exists yet).

### Merging `origin/main` (required before finishing; 8 commits ahead)

Known merge hotspots (`git diff HEAD...origin/main --stat`):
- `LF.lean`: main imports the *bare* chapters (CI build); ours includes the
  Verso chapters. Bare and Verso chapters declare the same names, so both
  chains cannot be imported together — drop bare imports for graduated
  chapters and build `LF.IndProp` / `LF.IndPropRegexp` via
  `check-bare-lean-chapters` in the Makefile instead (main currently has that
  target as a no-op echo).
- `SFLMeta/Save.lean`: main's #78 (Imp conversion) added `headerImports` /
  `keepImport` / `lakefileTemplate extraLibs` — an alternative mechanism for
  getting imports into generated projects. Reconcile with our
  `Block.savedImport` + `supportModules` (they may compose: theirs derives
  header imports, ours renders the import to the reader and pins the original
  module name; pick one source of truth for the emitted import lines).
- `scripts/to_verso.py`: main widened `_HIDE_OPEN_RE` to cover
  `-- INSTRUCTORS` regions and touched heading normalization and solution
  markers — mostly disjoint from our changes but adjacent; merge by hand.
- Chapter sources: main has "Fixes to Induction and UsingLean (#85)",
  "Polish and build fixes for IndProp (#84)", and two Lists-edit PRs — these
  overlap our marker repairs; re-run the full check suite on every chapter
  after the merge (`make verso` + the three checks + `make lf`).
- `HL/Imp.lean` is now Verso-authored on main (#78) and `HL.lean` includes
  it; our HL is untouched, should merge cleanly.

### After the merge

1. `make verso` (regenerate all `LF/*Verso.lean`).
2. Re-run `check_verso_prose.py` + `check_verso_markers.py` on all chapters;
   re-trace any *new* warnings.
3. `make all` (lf + hl + ts + check targets) — this also rebuilds and
   compiles the generated projects.
4. Finish IndProp (timeout), then IndPropRegexp, then Maps (conflict above),
   graduating each into `LF.lean` the same way.

### Eventually: permanent versification

When a chapter is made *permanently* Verso — the generated `<Ch>Verso.lean`
promoted to the hand-maintained source of truth and the code-forward
`LF/<Ch>.lean` retired, as already happened for Basics and HL/Imp — **keep
the plain .lean version in the repo as `LF/Old<Ch>.lean`** for manual
comparison (BCP instruction, 2026-07-14).
