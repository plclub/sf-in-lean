<!-- Design + status note, drafted by Claude (AI). -->

# Toward a checked style guide

Status and design notes for making [STYLE.md](STYLE.md) **normative** and
audited **semi-automatically**. This is a planning document, not itself a set of
conventions — the conventions belong in STYLE.md. It records what we were aiming
for and how far we got, so the effort can be picked up later.

## Goal

STYLE.md should be more than advice: contributions (human and AI) should conform
to it, and we should be able to verify conformance from time to time without a
heavy manual sweep. Much of the value is in writing *good* normative conventions
— that is the bulk of the remaining work — but the checking scaffolding below is
what keeps them honest once written.

## Design

Give every convention in STYLE.md a stable **ID** (`LEAN-*`, `PED-*`,
`WRITE-*`): the single handle that checks, reports, and deviation markers all
refer to. Sort each convention by how it can be checked:

| Class | Meaning | Enforcement |
|---|---|---|
| **auto** | mechanically decidable (regex / Lean AST / linter) | CI / `make style-check`, gating |
| **assisted** | a script surfaces *candidates*; a human confirms | advisory report, never gates |
| **manual** | judgement (pedagogy, prose quality) | periodic LLM-assisted + human audit |

Machinery:

1. **`make style-checklist`** regenerates an audit checklist straight from
   STYLE.md, so the checklist can never drift from the doc.
2. **`make style-check`** runs the auto + assisted checks, output grouped by ID;
   CI gates on the auto subset only.
3. **Periodic audit.** For manual conventions, an LLM-assisted pass reviews the
   material changed since the last audit against the generated checklist and
   produces a per-ID report a human adjudicates. Diff-scoped, so it stays cheap.
4. **Marked deviations.** A permitted pedagogical exception is annotated inline,
   naming the ID and the reason (`-- style: LEAN-2 (…)` in Lean, a `:::dev` note
   in prose); a check skips an item whose marker names its ID.

## How far we got

- **STYLE.md** — an initial full convention set (~23 IDs) was drafted, then
  deliberately simplified back to informal section stubs; the draft is preserved
  in the appendix below as a starting point.
- **`scripts/style_check.py`** (in the repo) — a working prototype:
  - `--checklist` generates the audit checklist from STYLE.md;
  - `STYLE-markers` (auto): a `style: <ID>` deviation marker must name a real
    STYLE.md id;
  - `WRITE-7` (assisted): flags wordy / throat-clearing prose — it already
    surfaced real candidates in `LF/Lists.lean`.
  Prose is read from `.md` files and `.lean` comments; adding a check is one
  `Check(...)` entry tagged with the id it enforces.
- **`make style-check` / `make style-checklist`** targets are wired up.

The prototype runs against STYLE.md as it stands; with the conventions
simplified out, `--checklist` is currently near-empty and `STYLE-markers` has no
ids to validate against — both come alive again as soon as the convention set
(with ids) lands back in STYLE.md.

## Next steps

1. Agree the convention set and give each entry a stable id in STYLE.md.
2. Classify each as auto / assisted / manual.
3. Grow the auto checks (e.g. `LEAN-6` stray `sorry` in finished material,
   naming patterns), validating each is low-false-positive on the current tree
   before it gates.
4. Wire a periodic GitHub Action (same shape as `.github/workflows/branch-watch.yml`)
   that posts the audit checklist and assisted notes on a cadence.

## Appendix — drafted convention set (starting point)

_Preserved from the first STYLE.md draft; **not yet authoritative**. Detailed
mechanics for several Lean items live in `STYLE.md` under **Lean Style**._

### Lean conventions
- **LEAN-1 — Mathlib alignment.** Follow the Mathlib style and naming
  conventions, except where an SFL pedagogical convention overrides them.
- **LEAN-2 — Idiomatic Lean.** Write definitions and proofs the way a working
  Lean engineer would; depart from idiom only temporarily, only for pedagogy,
  and say why.
- **LEAN-3 — Tactic discipline.** Introduce and use tactics in the established
  order; never use a tactic before the chapter has taught it.
- **LEAN-4 — Naming and namespaces.** Follow the naming/namespace rules in
  `STYLE.md`.
- **LEAN-5 — Argument visibility.** Choose implicit vs. explicit arguments per
  `CONTRIBUTING.md`.
- **LEAN-6 — Clean elaboration.** Finished material elaborates with no linter
  warnings and no stray `sorry`/`admit`.
- **LEAN-7 — Notation and simplification.** Introduce notation deliberately;
  keep `simp`/normal-form usage consistent.
- **LEAN-8 — Definitions vs. abbreviations.** Follow `CONTRIBUTING.md` when
  choosing `def` vs. `abbrev`.
- **LEAN-9 — Custom arithmetic.** Use SFL's custom `Nat`/arithmetic where the
  chapter calls for it.

### Pedagogical and presentational conventions
- **PED-1 — Exercise-based.** Every important concept is reinforced by hands-on
  exercises, each with a solution.
- **PED-2 — Progressive sophistication.** Ideas, tactics, and idioms are
  introduced small and grown; nothing depends on material not yet met.
- **PED-3 — Proofs teach proof engineering.** Proofs are examples: readable,
  maintainable, idiomatic — not merely goal-closing.
- **PED-4 — Motivate before formalizing.** Introduce the idea and its purpose in
  prose before the Lean that formalizes it.
- **PED-5 — Consistent chapter structure.** New chapters follow the structure
  and rhythm of existing ones.
- **PED-6 — Presentational polish.** Displays, notation, tables, and figures are
  held to a high, consistent bar; diagrams carry an ASCII fallback.
- **PED-7 — Connect to CSLib.** Relate SFL developments to CSLib where natural.

### Writing style
- **WRITE-1 — Chicago Manual of Style.** For grammar/punctuation/usage not
  settled here, follow the Chicago Manual of Style.
- **WRITE-2 — American spelling and the serial comma.**
- **WRITE-3 — Voice.** Address the reader as "you"; the authors are "we"; prefer
  the active voice.
- **WRITE-4 — Tone.** Clear, direct, encouraging; introduce jargon at first use.
- **WRITE-5 — Code in prose.** Identifiers, tactics, and code fragments go in
  `backticks` or a `lean` block, never as plain prose.
- **WRITE-6 — Headings and titles.** Use the surrounding chapter's heading
  style; keep capitalization consistent within a document.
- **WRITE-7 — Concision.** Prefer the shorter, plainer wording; cut throat-
  clearing and redundancy.
