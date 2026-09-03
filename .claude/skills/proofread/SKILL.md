---
name: proofread
description: Drive a low-level grammar, punctuation, usage, and markup pass over one SFL chapter — write a round of anchored edits, apply them for the author to review in the editor, then record which ones they kept. Use when the author types /proofread [Chapter] or asks for a chapter to be proofread.
---

<!-- This file is maintained by Claude (AI-generated). -->

# Proofreading a chapter

A pass has three phases, split by the one thing you cannot do yourself: the
author reviewing the edits in their editor. You run the commands; the author
only ever talks to you.

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

This makes the edits, writes a diff of just this round, and opens both in VS
Code. Anchor errors mean nothing was applied: fix the round file and run it
again.

Then **end your turn**. Tell the author what is in the round (the category
counts the command printed, and any pair of edits it flagged as sharing a git
hunk), and ask them to revert what they don't want — one click per hunk in the
Source Control gutter — and say when they're done. Do not poll, do not watch
the file, do not run `record` on their behalf. They may answer in a minute or
tomorrow; `proofread/state.json` remembers the round either way.

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
