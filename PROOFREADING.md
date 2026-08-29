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

Ask Claude to proofread a chapter. It reads this file and the ledger, writes a
*round* under `proofread/rounds/`, and registers it. From there the pass is two
runs of one bare command:

```
python3 scripts/proofread.py          # checks the round, makes every edit,
                                      # writes an isolated diff to read

  read proofread/rounds/<Ch>-rNN.diff, and revert the edits you don't
  want, in the chapter itself

python3 scripts/proofread.py          # saves your choices for good
```

The first run applies everything at once, so reviewing is hunk reversion in
your editor — one click in the VS Code gutter per rejection, no list to keep.
The second run reads the chapter back, works out which edits survived, and
appends the reverted ones to `proofread/ledger.jsonl` as permanent rejections.
Then `lake build <Vol>.<Ch>` and commit the chapter and the ledger together.

The round file is never something you open. `proofread/state.json` remembers
which round is in flight and which of the two runs comes next, so the bare
command always does the right thing; `proofread.py status` will tell you where
you are.

The isolated diff exists because the chapter usually has other uncommitted work
in it — `git diff` would mix your own edits in with the round's. The `.diff`
file has only the round.

Second thoughts before the second run: `proofread.py undo` reverses the whole
round and forgets it, recording nothing.

### Edits that share a hunk

The first run warns when two edits land within a few lines of each other. Those
sit in one git hunk and cannot be reverted independently — fix that spot by
hand instead. The second run reports such an edit as `unclear` and records
nothing for it, so it will come back in a later round.

## The ledger

`proofread/ledger.jsonl` is one JSON object per declined edit, keyed by a hash
of the (old text, new text) pair with whitespace normalized. Anything in it is
dropped from a later round before you see it. That means a round can be
regenerated from scratch — after the chapter has moved on, or by a different
session — and you will only ever be shown decisions you have not already made.
The ledger is tracked in git; it is the memory of the whole exercise.

Read it with `proofread.py ledger [--cat <substring>]`.

## From rejections to rules

The second run prints rejections by category and flags any category with two or
more. A flagged category means the proposer was working from a rule this book
does not hold. Write the rule into the table below and it stops being proposed
at all, in every chapter.

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

## Writing a round

For whoever (or whatever) does the proposing:

* **Read this whole file and `proofread.py ledger` first.** Anything already
  declined, or covered by a house rule above, must not be proposed again.
* **Low-level only.** Commas, agreement, articles, hyphenation, misused words,
  markup slips. Not restructuring, not word choice for its own sake, not
  pedagogy — those go through `STYLE-WRITING.md` and a normal editing pass.
* **Anchor precisely.** Each proposal is `{id, cat, old, new, why}`; `old` must
  occur exactly once in the file, and `old` and `new` must not contain one
  another. The first run enforces both and refuses to apply otherwise, because
  the second run decides kept-vs-declined by asking which of the two is
  present. Widen an anchor with neighboring words to satisfy this.
* **Categorize honestly.** The category is what makes rejection patterns
  visible; a lazy catch-all category defeats the whole mechanism.
* **Leave real content problems out of the round.** A stale reference, a wrong
  claim, an inconsistent term — report those separately in prose. They need a
  decision, not a comma.
* Proofread the hand-maintained source, not a generated `<Ch>Verso.lean`.
* Register the finished round with
  `python3 scripts/proofread.py start proofread/rounds/<Ch>-rNN.json`, then hand
  the bare command to the author.
