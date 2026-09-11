---
name: proofread
description: Drive a two-round editing pass over one SFL chapter — round 1 is low-level grammar, punctuation, usage, and markup; round 2 fixes the higher-level flow, ordering, and consistency problems found while reading. Each round is a file of anchored edits, applied for the author to review in the editor, then recorded. Use when the author types /proofread [Chapter] or asks for a chapter to be proofread.
---

<!-- This file is maintained by Claude (AI-generated). -->

# Proofreading a chapter

A full pass is **two rounds** over the same chapter, each driven through the
same machinery: round 1 is the low-level pass (commas, agreement, markup),
round 2 the high-level pass (flow, ordering, consistency — the findings of the
high-level read). Each round has three phases, split by the one thing you
cannot do yourself: the author reviewing the edits in their editor. You run
the commands; the author only ever talks to you.

`PROOFREADING.md` at the repo root is the authority on *what* to propose —
read it in full before phase 1, every time. This skill is only about driving.

## Phase 1 — write the round

```
python3 scripts/proofread.py start [<Chapter>]
```

It prints the chapter source to proofread and the round file to write, and
refuses when the working tree is dirty (a pass starts from a clean branch) or
when another round is already in flight. Relay that refusal to the author and
stop — do not commit their work for them, and do not reach for `--allow-dirty`
unless they ask.

Then:

1. Read `PROOFREADING.md` in full — "Writing a round", the house rules, and
   the known non-issues.
2. Read the recorded rejections: `python3 scripts/proofread.py ledger`.
   Nothing already declined, covered by a house rule, or listed as a known
   non-issue may be proposed again.
3. Read the chapter and write the round to the path `start` printed:
   `{"file", "chapter", "round", "proposals": [{"id", "cat", "old", "new",
   "why"}]}`, anchored exactly as `PROOFREADING.md` requires.

Do not edit the chapter yourself — every edit reaches it through the round, so
that the author's accept/decline is what the ledger records.

## Phase 2 — apply, and hand over

```
python3 scripts/proofread.py apply
```

This makes the edits and opens a side-by-side diff in VS Code — a snapshot of
the chapter before the round on the left, the live chapter on the right.
Anchor errors mean nothing was applied: fix the round file and run it again.

Then **end your turn**. Tell the author what is in the round (the category
counts the command printed, and any pair of edits it flagged as sharing one
change block), and ask them to revert what they don't want — the arrow in the
gutter between the panes, or editing the right-hand side directly — and to say
when they're done. Before ending the turn, do the **high-level read** (next
section) and include its findings in the same handover message — it touches no
files, so the author can weigh it while reverting low-level edits. Do not
poll, do not watch the file, do not run `record` on their behalf. They may
answer in a minute or tomorrow; `proofread/state.json` remembers the round
either way.

## The high-level read (during phase 2's wait)

While the author reviews round 1, re-read the chapter as a *reader*, not a
copyeditor: narrative flow and pacing, ideas introduced out of order or used
before they're explained, internal inconsistencies (terminology drift, a
convention announced then broken, examples that don't match the surrounding
prose, prose that misstates what the adjacent proof actually does), heading
structure, redundant or missing transitions, dangling references ("this" with
no displayed statement), and exercises whose grading or difficulty metadata
seems off or missing.

**Never** fold these findings into round 1 and never edit the chapter while
that round is in flight — the author is editing the same file. Report the
findings in prose with the phase-2 handover, ordered by position in the
chapter, each anchored by section name (and a short quote so the author can
search for the spot), with a one-line suggestion where you have one. Say
explicitly when a chapter reads fine and the list is short or empty — a clean
report is a result, not a failure. These findings become **round 2** after
round 1 is recorded and committed.

## Round 2 — the high-level round

After `record`, `lake build`, and the round-1 commit, run `start` again (it
names the next round file) and turn the high-level findings into a second
round through the same three phases. The "low-level only" rule is a round-1
rule; round 2 is exempt by design (see "The high-level round" in
`PROOFREADING.md`). For each finding:

* **If you can see the fix** — a heading at the wrong level, a wrong claim
  about the adjacent proof, an inconsistent variable name, a missing display
  or grading spec with an obvious sibling to copy — make it an anchored edit,
  worded so the diff shows the author exactly what changed and the `why` says
  why. Structural edits (moving a heading, inserting a block) need anchor text
  on *both* sides of the change, or `old`/`new` will contain one another.
* **If the fix needs an author decision** — a design question, a grading
  policy, exercise framing — the edit *inserts* a `:::dev "Claude"` note at
  the spot (no urgency keyword, so it stays visible), stating the problem and
  the plausible options. The note is the deliverable; do not guess at the
  decision.

Then `apply`, hand over, and `record` exactly as in round 1 — and because
round 2 can touch code, headings, and `{lean}` roles, run `lake build
<Vol>.<Ch>` right after `apply` rather than waiting for phase 3. Findings the
author explicitly rejected in the prose report are dropped, not turned into
dev notes.

## Phase 3 — record

When the author says they're done:

```
python3 scripts/proofread.py record
```

It decides kept-vs-declined by reading the chapter back, appends the declines
to `proofread/ledger.jsonl`, and prints the rejection histogram. Then:

* If a category is flagged as worth a house rule, propose the wording and, if
  the author agrees, add the row to the house-rules table in `PROOFREADING.md`.
  A flagged category means the proposer — you — was working from a rule this
  book does not hold; the rule is what stops it recurring in every chapter.
* Report anything `record` called `unclear` (the author rewrote that spot
  themselves, so nothing was recorded and it will come back in a later round).
* Run `lake build <Vol>.<Ch>` and offer to commit the chapter, the ledger, and
  any `PROOFREADING.md` change together.

## Elsewhere in the pass

* Real content problems — a stale reference, a wrong claim, an inconsistent
  term — never go in the round. Report them to the author in prose; they need
  a decision, not a comma.
* `python3 scripts/proofread.py undo` reverses an applied round and leaves it
  for another day, recording nothing. `status` says what is in flight.
