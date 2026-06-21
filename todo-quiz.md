# TODO: Real quiz support in the Verso pipeline

Context captured 2026-06-21. This file distills a discussion about what it would
take to give quizzes real support in `to_verso.py` + the Verso/SFLMeta build.
(The HIDE region shows up only as a sub-problem; see Part 3.)

## Current state (as of this writing): quizzes are a no-op

Neither the script nor the build does anything meaningful with quizzes. Markers
are stripped or passed through as plain prose/code; no quiz widget is produced.

### `to_verso.py`
QUIZ is recognized in only two cosmetic places:
- **Block→line normalization**, `_BLOCK_MARKER_RE` (scripts/to_verso.py:108):
  a one-line `/- QUIZ -/` is rewritten to `-- QUIZ`.
- **Bare-marker dropping**, `_DROP_MARKER_RE` (scripts/to_verso.py:120-123):
  a comment-body line that is *exactly* `QUIZ`/`/QUIZ` is dropped so its text
  doesn't break Verso markup. The comment at lines 118-119 is explicit that
  region semantics are NOT honored.

There is **no `_QUIZ_OPEN_RE`/`_QUIZ_CLOSE_RE` paired-region handling** in the
main tokenizer, unlike HIDE, SOLUTION, FULL, TERSE, exercises
(scripts/to_verso.py:537-585). Consequences:
- **Line form** (`-- QUIZ` / `-- /QUIZ`, e.g. LF/Induction.lean:107, and the
  `quiz1`/`quiz2` theorems in LF/Lists.lean:1691): markers sit at column 0,
  match no structural regex, fall through to the default `code_line` case
  (scripts/to_verso.py:610-611). Markers and everything between them render as
  ordinary Lean code/comments.
- **Block form** (`/- QUIZ: … -/`, e.g. LF/Logic.lean:139): body starts with
  `QUIZ: …` (trailing text), so it does NOT fullmatch the drop regex — the whole
  thing, `QUIZ:` prefix and all, renders as plain prose.

Either way the interactive quiz (options, correct answer, checking) is lost.

### The Verso build (SFLMeta)
**No Quiz directive at all.** SFLMeta has Bnf, Comment, Details, Exercise,
Grade, Hide, Ignore, Instructors, Save, SlideBreak, Solution, Terse, Theme —
nothing for quizzes. Even if the script emitted a quiz block, the build has
nothing to elaborate it with.

## The crux problem: the source doesn't encode answers machine-readably

The two quiz formats are inconsistent AND neither marks the correct answer in a
form a widget could consume. This is the real work; the plumbing is the easy half.

**Format A — line-form** (LF/Induction.lean:107-119):
```
-- QUIZ
/- question prose with inline (A) none (B) `rewrite` (C) `cases` … -/
-- HIDE
/- review1 -/
theorem review1 … := by rfl      <- correct answer only *implied* by this proof
-- /HIDE
-- /QUIZ
```

**Format B — block-form** (LF/Logic.lean:139-148):
```
/- QUIZ: question
    1. `Prop`
    2. `Nat → Prop`
    …  -/
#check (… : Prop)                <- correct answer only *implied* by this #check
```

So: options are formatted two different ways (inline `(A)…(E)` vs numbered
list), and in neither case is the correct answer explicitly marked — it is only
inferable from an adjacent proof or `#check`.

Chapters that contain quizzes: Induction, Lists, Logic, Poly, IndProp, Tactics.

## Two decisions that drive everything else (think about these first)

1. **Static vs. interactive rendering.**
   - *Static (low effort, recommended to start):* render question + options with
     the answer in a collapsible reveal, reusing the existing `Details` pattern.
     Works in plain HTML, no JS. `toHtml` emits `<ol>` of options + `<details>`
     for the answer. Can upgrade to interactive later WITHOUT touching the script
     or the source convention.
   - *Interactive (higher effort):* `toHtml` emits a `<form>` of radio buttons +
     a JS snippet checking the selection against the marked answer. Needs the
     answer index threaded through `data := Json` (not `Json.null`).

2. **The source answer-convention.** Pick one canonical source form and add an
   explicit answer marker, e.g.:
   ```
   -- QUIZ
   /- To prove …, which tactics do we need?
      (A) none
      (B) `rewrite`
      (C) `cases`
      -- ANSWER: A
   -/
   …
   -- /QUIZ
   ```
   No script can infer this reliably. Decide: marker syntax (`-- ANSWER: A` vs a
   `(*)` on the correct option), and whether to normalize Format B into the line
   form (cleaner) or support both in the tokenizer.

## Work items, once the two decisions are made

### Part 1 — Normalize the source (authoring work, unavoidable)
- One-time pass over the ~6 quiz chapters to add explicit answer markers and a
  single canonical option format.
- Can be *semi*-automated (answer is usually derivable from the adjacent
  proof/`#check`) but needs human review.

### Part 2 — `SFLMeta/Quiz.lean` (parallels SFLMeta/Solution.lean)
- New `block_extension Block.quiz` + `@[directive] quiz`, modeled on
  `Block.solution` (which is itself ~40 lines: a block_extension with a
  `traverse`/`toHtml`, plus a `DirectiveExpanderOf Unit`).
- Static version: `toHtml` emits option list + `<details>` reveal.
- Register wherever SFLMeta aggregates extensions.
- Add `import SFLMeta.Quiz` to the header the script injects, alongside
  `import SFLMeta.Solution` (scripts/to_verso.py:46-49).

### Part 3 — `to_verso.py` tokenizer + emitter
- Add region regexes:
  ```python
  _QUIZ_OPEN_RE  = re.compile(r'^-- QUIZ$')
  _QUIZ_CLOSE_RE = re.compile(r'^-- /QUIZ$')
  ```
- In the main loop, on `_QUIZ_OPEN_RE`, capture to `-- /QUIZ` (model on the HIDE
  branch, scripts/to_verso.py:537), parse question / option list / `ANSWER:`
  marker, emit a `('quiz', …)` token.
- Add `_on_quiz` to the emitter, parallel to `_on_solution_prose`
  (scripts/to_verso.py:858), producing `:::quiz … :::`; dispatch it in `process`
  (scripts/to_verso.py:882).
- **The embedded `-- HIDE` proof inside Format-A quizzes** (this is the "hide"
  part): decide whether to feed it into the answer-reveal or keep hiding it.
- Remove `QUIZ` from `_DROP_MARKER_RE` and the bare-marker handling so it is no
  longer silently swallowed.
- Format B: either normalize to line form in Part 1 (preferred) or add a second
  tokenizer branch.

## Recommended sequencing
1. Settle the two decisions above (static-vs-interactive; source answer-convention).
2. Build the static `SFLMeta/Quiz.lean` (`<details>` reveal) — lowest Verso/JS
   risk, gets quizzes rendering end-to-end.
3. Wire up `to_verso.py` (tokenizer + emitter).
4. Normalize the source chapters.
5. (Later, optional) upgrade `toHtml` to interactive radio-button checking.
