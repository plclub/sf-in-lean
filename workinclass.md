# The `WORKINCLASS` directive: current status and proposed fixes

## Intended semantics

`WORKINCLASS` marks a proof (or a sub-region of a proof) that the
instructor works out *live* during lecture. The intended behavior in the
three generated `.lean` targets is:

| target    | WORKINCLASS body |
|-----------|------------------|
| student   | **shown** (full proof) |
| solutions | **shown** (full proof) |
| terse     | **replaced with `sorry`** |

This is *different* from a normal exercise (`solution!` / `-- SOLUTION`),
where the body is `sorry` in the student build and shown only in
solutions. WORKINCLASS is, in effect, the inverse of `FULL`: it is hidden
(stubbed) only in the lecture/terse build.

## Current status: not implemented (no-op)

WORKINCLASS is **not handled anywhere** in the toolchain. It survives only
as an inert comment, so the proof body leaks into *all three* targets,
including terse.

Trace:

1. **`scripts/to_verso.py` has no WORKINCLASS handling.** A grep for
   `WORKINCLASS` returns nothing. Unlike `FULL`/`TERSE`/`HIDE`/`SOLUTION`/
   `solution!`, the marker falls through to the default case and is emitted
   as a literal comment line *inside* the ` ```lean ` fence.

2. **SFLMeta has no WORKINCLASS mechanism.** There is `Block.terse` /
   `Block.full` (`SFLMeta/Terse.lean`), `Block.solution`
   (`SFLMeta/Solution.lean`), and the `solution!` tactic/term
   (`SFLMeta/Exercise.lean`), but nothing keyed to WORKINCLASS.

3. **The saver structurally cannot distinguish terse from student for a
   plain code block.** In `SFLMeta/Save.lean`, each ` ```lean ` block stores
   exactly two source variants in `Block.leanSaved` — `teacher` and
   `student` — selected by `showSolutions`. The three targets wire up
   (`emitSavedImpl`, `Save.lean:741-762`) as:

   | target    | `isTeacher` | code field used |
   |-----------|-------------|-----------------|
   | student   | `false`     | `student`       |
   | solutions | `true`      | `teacher`       |
   | terse     | `false`     | `student`       |

   Terse and student read the **same** `student` field. For a block with no
   `solution!`, `teacher == student ==` the full proof, so all three
   targets emit the WORKINCLASS proof verbatim.

4. **The older `lf/extract-book.py` never handled it either** — its
   docstring lists `FULL`/`TERSE`/`ADMITDEF`/`ADMITTED`/`SOLUTION`
   substitutions but no WORKINCLASS.

5. **`LF/fixleancomments.py`** treats `-- WORKINCLASS` only as a *protected
   separator* (it stays a `--` line and blocks prose-wrapping) — it does not
   give it any build-variant meaning.

### Worked example (current, broken behavior)

Source — `LF/Induction.lean:352-361`:

```lean
theorem eqb_self : ∀ n : Nat,
    (n == n) = true := by
  -- WORKINCLASS
  intro n
  induction n
  case zero =>
    rfl
  case succ n' ih =>
    rewrite [beq_succ]; exact ih
-- /WORKINCLASS
```

What `to_verso.py` produces — `LF/InductionVerso.lean:217-228` (markers
pass through as comments):

```lean
theorem eqb_self : ∀ n : Nat,
    (n == n) = true := by
  -- WORKINCLASS
  intro n
  induction n
  case zero =>
    rfl
  case succ n' ih =>
    rewrite [beq_succ]; exact ih
-- /WORKINCLASS
```

Generated `.lean` targets — **all three identical** (proof present, no
`sorry`; only the `-- WORKINCLASS` markers may be dropped):

```lean
-- student / solutions / terse  (all the same — BUG: terse should be sorry)
theorem eqb_self : ∀ n : Nat,
    (n == n) = true := by
  intro n
  induction n
  case zero =>
    rfl
  case succ n' ih =>
    rewrite [beq_succ]; exact ih
```

The terse target should instead be:

```lean
-- terse  (desired)
theorem eqb_self : ∀ n : Nat,
    (n == n) = true := by
  sorry
```

---

## Fix option A — block-level (script only, no SFLMeta change)

Have `to_verso.py` expand a WORKINCLASS region into two directive blocks:

* a `::::full` block holding the real proof — kept in student and solutions
  (both non-draft) and hidden in terse (draft); and
* a `::::terse` block holding the theorem with its proof replaced by
  `sorry` — shown only in terse.

This reuses the existing `Block.full` / `Block.terse` traversal
(`SFLMeta/Terse.lean`) and the saver's existing handling of them
(`Save.lean:611-617`), so **no verified Lean metaprogramming changes**.

### What `InductionVerso.lean` would contain (option A)

```
::::full
```lean
theorem eqb_self : ∀ n : Nat,
    (n == n) = true := by
  intro n
  induction n
  case zero =>
    rfl
  case succ n' ih =>
    rewrite [beq_succ]; exact ih
```
::::

::::terse
```lean
theorem eqb_self : ∀ n : Nat,
    (n == n) = true := by
  sorry
```
::::
```

### Resulting targets (option A)

* **student** (non-draft): `::::full` kept, `::::terse` dropped → full proof. ✅
* **solutions** (non-draft): same → full proof. ✅
* **terse** (draft): `::::full` dropped, `::::terse` kept → `sorry` stub. ✅

### Cost / drawbacks of option A

* `to_verso.py` must **synthesize the stub**: keep the signature and any
  tactics *before* the `-- WORKINCLASS` marker, then replace the marked span
  with `sorry`. For a whole-proof region this is trivial; for a
  sub-region (see `injection_ex1` below) the script must reproduce the
  preamble.
* The theorem signature is **duplicated** in the source — two copies to keep
  in sync if edited by hand later.
* The stub is a *hand-built string*, so it is not re-elaborated against the
  real environment the way `solution!` student variants are
  (`Save.lean:elabAndHighlightStudent`). A typo in the synthesized signature
  would only surface when the terse project is built.

### Sub-region example (option A) — `LF/Tactics.lean:419-427`

Source:

```lean
theorem injection_ex1 (n m o : Nat) :
    [n, m] = [o, o] →
    n = m := by
  intro h
  -- WORKINCLASS
  injection h with h1 h2
  injection h2 with h3
  rw [h1, h3]
  -- /WORKINCLASS
```

Option A output must preserve the `intro h` preamble in *both* blocks:

```
::::full
```lean
theorem injection_ex1 (n m o : Nat) :
    [n, m] = [o, o] →
    n = m := by
  intro h
  injection h with h1 h2
  injection h2 with h3
  rw [h1, h3]
```
::::

::::terse
```lean
theorem injection_ex1 (n m o : Nat) :
    [n, m] = [o, o] →
    n = m := by
  intro h
  sorry
```
::::
```

---

## Fix option B — code-level (SFLMeta + marker)

Add a third "terse code" variant so the saver can pick proof-vs-`sorry`
independently of the student/solutions axis.

Sketch of the changes:

1. **A `workinclass!` tactic marker** in `SFLMeta/Exercise.lean`, analogous
   to `solutionTac`. Where `solution!` records *student → `sorry`* /
   *teacher → kept*, `workinclass!` records *terse → `sorry`* / *student &
   solutions → kept*. (It needs a new `terseEditRef` alongside the existing
   `studentEditRef` / `teacherEditRef`.)

2. **A third source variant in `Block.leanSaved`** (`Save.lean`): store
   `(teacher, student, terse)` instead of `(teacher, student)`. The `lean`
   code-block expander computes the terse form by applying the
   `terseEditRef` ranges (replace the `workinclass!` span with `sorry`).

3. **Variant selection in `emitSavedImpl`** keys the chosen field on the
   build variant string (`"terse"` → terse field) rather than the
   `isTeacher` boolean.

### Source marker form (option B)

WORKINCLASS regions become a `workinclass!` tactic block — a single code
block, no duplication:

```lean
theorem eqb_self : ∀ n : Nat,
    (n == n) = true := by
  workinclass!
    intro n
    induction n
    case zero =>
      rfl
    case succ n' ih =>
      rewrite [beq_succ]; exact ih
```

### Resulting targets (option B)

* **student**: `workinclass!` keyword stripped, body kept → full proof. ✅
* **solutions**: same → full proof. ✅
* **terse**: whole `workinclass!(…)` span → `sorry`. ✅

```lean
-- terse
theorem eqb_self : ∀ n : Nat,
    (n == n) = true := by
  sorry
```

### Sub-region example (option B) — `injection_ex1`

Only the marked tactics are wrapped; the preamble is shared automatically
because it is the same single block:

```lean
theorem injection_ex1 (n m o : Nat) :
    [n, m] = [o, o] →
    n = m := by
  intro h
  workinclass!
    injection h with h1 h2
    injection h2 with h3
    rw [h1, h3]
```

Terse target:

```lean
theorem injection_ex1 (n m o : Nat) :
    [n, m] = [o, o] →
    n = m := by
  intro h
  sorry
```

### Cost / drawbacks of option B

* Touches verified Lean metaprogramming (`SFLMeta/Exercise.lean`,
  `SFLMeta/Save.lean`) and widens `Block.leanSaved` from 2 to 3 children —
  the `traverse`/`toHtml`/`toTeX`/saver code all change.
* `to_verso.py` must emit `workinclass!` (with correct indentation of the
  wrapped tactic sequence) rather than two comment markers.

---

## Comparison

| | Option A (block-level) | Option B (code-level) |
|---|---|---|
| Files touched | `to_verso.py` only | `to_verso.py`, `SFLMeta/Exercise.lean`, `SFLMeta/Save.lean` |
| Verified Lean changed | No | Yes |
| Signature duplicated in source | Yes | No |
| Stub re-elaborated against env | No (hand-built string) | Yes (reuses edit-range machinery) |
| Sub-region (preamble) handling | Script reproduces preamble | Automatic (same block) |
| Mirrors existing mechanism | `Block.full`/`Block.terse` | `solution!` |

**Recommendation:** Option A is the smaller, lower-risk change if WORKINCLASS
regions are almost always whole proofs. Option B is cleaner for sub-region
cases and avoids signature duplication, at the cost of editing the verified
metaprogramming. The deciding factor is how many WORKINCLASS regions are
*sub-proofs* (preamble before the marker) rather than whole proofs — those
are awkward under A and natural under B.

## Inventory of WORKINCLASS regions in the source

Plain `.lean` source files containing `-- WORKINCLASS` / `/- WORKINCLASS -/`
regions (excluding `*Verso.lean` generated files and prose mentions):

* `LF/Induction.lean` (1 region)
* `LF/Lists.lean` (1)
* `LF/Logic.lean` (11)
* `LF/Tactics.lean` (3)
* `LF/IndProp.lean` (4)
* `LF/IndPropRegexp.lean` (2)

(`LF/Basics.lean` mentions WORKINCLASS only in a `BCP:` author note, not as
a region. Both line-comment `-- WORKINCLASS … -- /WORKINCLASS` and block-comment
`/- WORKINCLASS -/ … /- /WORKINCLASS -/` forms occur; a fix must handle
both. Some files also use `-- TERSE: WORKINCLASS`, which is a separate,
already-handled TERSE construct and should not be confused with a bare
WORKINCLASS region.)
