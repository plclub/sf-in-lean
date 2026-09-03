<!-- This file is maintained by Claude (AI-generated). -->

# Proofreading a Chapter

This is the repeatable procedure for a low-level grammar, punctuation, and
usage pass over a chapter. It is deliberately separate from the substantive
editing advice in `STYLE-WRITING.md`: that guide is about what to say, this one
is about commas.

The point of the machinery is that **a decision is made once**. An edit you
decline is recorded, never proposed again, and — once the same kind of
rejection has happened a couple of times — promoted to a house rule that stops
the whole category at the source.

## Doing a pass

Say `/proofread <Chapter>` in a Claude session — that is the whole interface.
Claude reads this file and the ledger, writes a *round* (a JSON file of
anchored edits, under `proofread/rounds/`), applies it, and opens a diff of
just those edits in VS Code alongside the chapter. Revert the edits you don't
want — one click per hunk in the Source Control gutter — and tell Claude you're
done; it records your rejections in `proofread/ledger.jsonl` and reports any
category that has earned a house rule. Then `lake build <Vol>.<Ch>` and commit
the chapter and the ledger together.

Two turns of conversation, then. The review in between can take a minute or a
day, in that session or a later one: `proofread/state.json` holds the round in
flight, so "I'm done" is understood whenever it comes. The round file and the
script are never things you have to open.

**A pass starts from a clean branch.** The round's edits must be the only
uncommitted thing in the chapter — otherwise a reverted hunk cannot be told
from your own work, and neither reconciling nor `undo` is exact. So the pass
refuses to start while `git status` is dirty (its own files under `proofread/`
excepted); commit or stash first. `--allow-dirty` overrides it, at that cost.

`proofread.py undo` reverses the whole round and leaves it for another day.
`proofread.py status` says where you are.

### Never commit a round mid-flight

Committing while a round is applied but unrecorded bakes in your reverts and
loses the rejections. A hook is provided; install it once per clone:

```
git config core.hooksPath scripts/hooks
```

`scripts/hooks/pre-commit` then blocks such a commit (and `git commit
--no-verify` gets past it). Without the hook nothing enforces this — the
`/proofread` flow simply asks Claude to record before committing.

### Doing it by hand

`python3 scripts/proofread.py`, with no arguments and a round already written,
runs the same pass in a terminal: it applies the round, opens the diff, waits
at a prompt while you review, and records when you press return. Ctrl-C stops
without recording; run it again and it resumes mid-review. The phases are
separately available as `proofread.py apply` and `proofread.py record`, which
is what Claude runs; `proofread.py start [<chapter>]` names the chapter source
and the next round file. `proofread.py --help` lists the rest.

The `.diff` file is the round as proposed: it stays next to the round file
afterwards, and it still reads as one list of the proposals once you have begun
reverting hunks in the chapter.

### Edits that share a hunk

`apply` warns when two edits land within a few lines of each other. Those
sit in one git hunk and cannot be reverted independently — fix that spot by
hand instead. Such an edit is then reported as `unclear` and nothing is
recorded for it, so it will come back in a later round.

## The ledger

`proofread/ledger.jsonl` is one JSON object per declined edit, keyed by a hash
of the (old text, new text) pair with whitespace normalized. Anything in it is
dropped from a later round before you see it. That means a round can be
regenerated from scratch — after the chapter has moved on, or by a different
session — and you will only ever be shown decisions you have not already made.
The ledger is tracked in git; it is the memory of the whole exercise.

Read it with `proofread.py ledger [--cat <substring>]`.

## From rejections to rules

At the end of a pass, rejections are printed by category, and any category with
two or more is flagged. A flagged category means the proposer was working from
a rule this book does not hold. Write the rule into the table below and it
stops being proposed at all, in every chapter.

Categories are slash-separated, coarse on the left: `comma/introductory`,
`hyphenation/re-prefix`, `markup/code-font`. Keep reusing existing ones so the
counts mean something. `proofread.py patterns` reprints the histogram any time.

### House rules

These override the Chicago Manual of Style default named in `STYLE-WRITING.md`.
Each was learned from a run of rejections; do not propose against them.

| Rule | Established |
| ---- | ----------- |
| Double spaces after a sentence-ending period are fine; never propose collapsing them. | initial |
| ASCII `--` inside `:::dev` and `:::instructors` note bodies is an author's own shorthand — leave it. Chapter prose uses a real em dash. | initial |

## Known non-issues

Things in the sources that look wrong at a glance and are not. Check here
before reporting a content problem.

| Looks wrong | Why it isn't |
| ----------- | ------------ |
| Prose describing an `sf_expect_failure_in` / `sf_expect_failure_in?` annotation where the Verso block actually says `+error` (e.g. `LF/Basics.lean`). | The prose is written for the *generated* `.lean`, which is what the reader has in front of them. `+error` blocks are extracted as indented `sf_expect_failure_in` blocks — see `SFLMeta/Save/Lean.lean`. |
| The opening sentence of `LF/Induction.lean` — "how to carry out _proofs by induction_, one of the most fundamental reasoning tools in computer science and mathematics, in Lean" — strands "in Lean" at the end. | Deliberate; the author decided on 2026-08-30 to keep the sentence as it stands. Do not propose reordering it. |

## Writing a round

For whoever (or whatever) does the proposing:

* **Read this whole file and `proofread.py ledger` first.** Anything already
  declined, covered by a house rule, or listed under known non-issues must not
  be raised again.
* **Low-level only.** Commas, agreement, articles, hyphenation, misused words,
  markup slips. Not restructuring, not word choice for its own sake, not
  pedagogy — those go through `STYLE-WRITING.md` and a normal editing pass.
* **Two or more blank lines in a row are a slip.** A chapter source uses at
  most a single blank line anywhere — prose, code, note bodies alike — so scan
  for every run of two or more and propose collapsing it to one, under the
  category `formatting/blank-lines`. The exception is a fenced block quoting
  literal output, where the spacing is content; leave those runs alone.
* **Anchor precisely.** Each proposal is `{id, cat, old, new, why}`; `old` must
  occur exactly once in the file, and `old` and `new` must not contain one
  another. Both are enforced, and nothing is applied otherwise, because
  reconciling decides kept-vs-declined by asking which of the two is present.
  Widen an anchor with neighboring words to satisfy this. A blank-line
  collapse needs the whole run *plus* the non-blank line on either side of it
  in both `old` and `new` — the blank lines by themselves are never unique.
* **Categorize honestly.** The category is what makes rejection patterns
  visible; a lazy catch-all category defeats the whole mechanism.
* **Leave real content problems out of the round.** A stale reference, a wrong
  claim, an inconsistent term — report those separately in prose. They need a
  decision, not a comma.
* Proofread the hand-maintained source, not a generated `<Ch>Verso.lean`.
* Write the round to the path `proofread.py start` printed
  (`proofread/rounds/<Ch>-rNN.json`) and do not edit the chapter yourself —
  every edit reaches it through the round, so that what the author accepts and
  declines is what the ledger records.

The driving loop around these rules — which command to run when, and where to
stop and wait for the author — is `.claude/skills/proofread/SKILL.md`.
