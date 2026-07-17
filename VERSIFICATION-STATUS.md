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

Update 2026-07-16/17: **Induction**, **Lists**, and **UsingLean** are now
authored *directly* in Verso — `LF/Induction.lean` / `LF/Lists.lean` /
`LF/UsingLean.lean` are the Verso sources (the old bare sources are archived
locally as `LF/Old<Ch>.lean`, untracked), imported and `{include}`d in
`LF.lean` without the `Verso` suffix, removed from the Makefile's
`LF_CHAPTERS` generation list, and listed in `to_verso.py`'s
`DIRECT_LF_MODULES` so other chapters' `import LF.<Ch>` lines pass through
unchanged.

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
- **` ```importBlock ` blocks**: `_extract_imports` plants `--IMPORTBLOCK`
  sentinels for volume-module imports; the renderer emits an `importBlock`
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
- `Block.importBlock` extension + `@[code_block] importBlock` expander +
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
redefines `PartialMap.update` (etc.) already defined by LF.Lists'
partial-maps preview section, and Verso imports share one environment (see
the old note in LFDraft.lean's history). Resolve by renaming/namespacing one
side or dropping the Lists preview definitions, then run the pipeline.

### Typeclasses

Skipped per BCP (no `LF/Typeclasses.lean` exists yet).

### Merging `origin/main` (required before finishing; 8 commits ahead)

**Merge performed 2026-07-14** (`origin/main`, 8 commits). Resolutions made:
- `LF/IndProp.lean`: only textual conflict — both sides made the same
  `exists 0` fix; kept ours (with explanatory comment).
- `LF.lean`: dropped main's bare-chapter imports for all graduated chapters
  (bare and Verso chapters declare the same names, so both chains cannot be
  imported together); `LF.IndProp` / `LF.IndPropRegexp` are built by
  `check-bare-lean-chapters` in the Makefile instead.
- `SFLMeta/Save.lean`: adopted main's #78 mechanism (`headerImports` +
  `bundleLoop` — prepends each extracted chapter's framework-stripped header
  imports and transitively bundles non-chapter prerequisites like
  CustomTactics, with `lakefileTemplate extraLibs`) as the single source of
  truth for extracted-project imports. Our `Block.importBlock` is now
  **display-only** (renders the import to the book reader; the saver emits
  nothing for it); our `supportModules` copying was removed as redundant.
- Author/dev notes: main's #78 decided notes are `:::dev` **directives**
  (verbatim-fenced body), not ` ```dev ` code blocks — merged CLAUDE.md
  documents this; the ` ```dev ` expander remains for back-compat. Our
  checker policy follows `:::dev`.
- New `-- DEV` … `-- /DEV` region marker (introduced by main's #85 in
  Induction/UsingLean): taught to_verso to route the body to `:::dev`
  (markers consumed) and added `DEV` to `check_verso_markers._POLICY`.
- Post-merge verification: `make verso` + prose/marker/scoping checks re-run
  on all six graduated chapters — prose 0 everywhere, 0 flattenings,
  remaining warnings all in the known-benign classes.

**Post-merge build repair (2026-07-14 late).** Main's improved ADMITDEF
conversion + our graduated chapters exposed a series of latent issues in the
generated-project builds (`make all` exercises them; main never built these
chapters' projects). Fixed, in order:
- lakefileTemplate: skip an extraLib equal to the volume lib (duplicate
  `lean_lib LF` from bundling LF/CustomTactics.lean).
- Characteristic-equation lemmas / test examples proved by `rfl` against
  ADMITDEF'd (student-`sorry`d) definitions now carry trailing `-- ADMITTED`
  (student gets `:= sorry`), matching the existing doubleBin/test_sum1
  convention: Induction natToBin_zero/succ; Tactics forallb/existsb tests ×8;
  Lists nil_sum/cons_sum/eqblist ×3; Logic All_nil/All_cons/beq_list ×4/
  forallb_nil/forallb_cons. Logic In_map_iff/In_app_iff: `-- ADMITTED` moved
  above `induction xs` (a single student `sorry` can't close two goals).
- to_verso: `_BLOCK_MARKER_RE` also normalizes `/- ADMITTED -/`/`/- ADMITDEF -/`
  (standalone AND trailing forms); trailing `-- ADMITTED` conversion handles
  the proof term on a line after `… :=`; **multi-marker close comments like
  `/- /ADMITTED␤GRADE_THEOREM … -/` are NOT recognized** — the close must be
  its own `/- /ADMITTED -/` comment (5 such comments split in Poly; watch for
  the pattern in IndProp/Maps).
- Save.lean stripGuardMsgs: keeps `#guard_msgs` + docstring in extracted files
  when the expectation is an *error* (stripping left deliberately-failing
  examples bare, e.g. Logic's `P ∧ Q = Q ∧ P := by rfl`); still strips
  benign warning:/info: guards.
- `\CHAP{X}` refs (main's new macro → `{ref "X"}[X]`): added the missing
  `tag := "Basics"` to LF/Basics.lean's `%%%`; `\CHAP{Preface}` → plain text
  (no Preface chapter exists — re-link when one does); `\CHAP{Arithmetic}` →
  `\CHAP{Induction}` (where `double` lives).
- Terse-build visibility (terse drops `::::full` wholesale, and to_verso puts
  code following a `FULL:` paragraph inside the region): moved Basics
  `add_succ` out of its `::::full`; moved Induction's `-- FULL` below
  `namespace NatToBin`; made Lists' `abbrev Bag`/`namespace Bag`/`end Bag`,
  `open Bag`, and `option_elim` (+ its two lemmas) terse-visible; moved
  Poly's `seal filter`/`seal List.length` before the exercise-closing `[]`
  (they were escaping the exercise while their `unseal` partners didn't).
- **Exercise/FULL semantics (BCP decision, 2026-07-15): exercises NEST inside
  an enclosing `::::full`** (documented in `_on_exercise_open`), so the terse
  build elides (almost) all exercises — a FULL-scoped "Exercises" section
  drops from terse wholesale, definitions and namespaces included. Two
  supporting rules in to_verso:
  - A `-- /FULL` while a nested exercise is open **force-closes the exercise
    first** (a region cannot outlive an exercise it contains). This is what
    makes the recurring source idiom `-- FULL` / `-- EX… (name)` / `-- /FULL`
    mean "the exercise *banner* is full-only; the theorem after it is
    common" (Tactics beq_eq, Logic even_double_conf), and it prevents a
    straddling region from silently swallowing everything after the
    exercise.
  - When terse-visible material depends on a definition made inside a FULL
    region, the definition must be made terse-visible in the source, case by
    case; the terse generated project (`lake exe sfl lf terse`) is the
    detector. Fixed this way: Induction basic_induction restructured
    (exercise now closes with `-- []` before its `-- /FULL`; `add_comm` /
    `add_assoc` follow as common graded ADMITTED theorems, since terse
    lecture material uses `add_comm`); Poly flatMap_nil/flatMap_cons moved
    *inside* the FULL region with their exercise (no terse consumers).

**FINAL STATE: `make all` passes end to end (exit 0)** — LF/HL/TS books in
all three variants, all nine generated projects compile, both check targets
green, and the six graduated chapters pass prose (0 missing spans) and
marker (0 flattenings) checks.

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
