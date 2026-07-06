<!-- Claude-generated handoff note (2026-07-06). Temporary; delete once the work
     described here is committed / abandoned. -->

# Handoff: replace inner ``` fences in `:::dev` with raw-body code blocks

## Goal (from the user)
> "I don't like the ``` blocks inside of `:::dev` comments. I remember they were
> added to suppress some parsing errors, but those should be handled more
> directly." Add advice to `CLAUDE.md` so we don't forget, and get rid of the
> inner ``` markers.

## Root cause / design decision
`to_verso.py` emitted author/dev notes as Verso **directives**
(`:::dev … :::`, `:::instructors … :::`). A Verso directive always **parses its
body as markdown**, so arbitrary author prose (`:::`, `*`, `#`, `[…]`,
backticks) could derail the parser. The old workaround wrapped the body in an
inner verbatim ` ``` ` fence (`_verbatim_block`).

The clean fix: a Verso **code block** (`@[code_block]` / `CodeBlockExpanderOf`)
receives its body as a **raw string that is never parsed as markdown**. So a
single tagged fence ` ```dev ` / ` ```instructors ` replaces the
directive-plus-inner-fence entirely. Models already in the repo:
`SFLMeta/Bnf.lean` (` ```bnf `) and `SFLMeta/Save.lean` (` ```lean `).

Key trick: the code block is registered under the *existing directive name* via
the explicit-ident attribute form `@[code_block dev]` (resolves the ident `dev`
to the existing `def dev`). Directives and code blocks live in **separate
expander tables**, so a same-named `@[directive] def dev` and `@[code_block dev]`
coexist; the fence reads ` ```dev ` (clean), not ` ```devBlock `.

## Scope
Converted **`dev`** and **`instructors`** only (both are pure noops — body
dropped at elaboration). Intentionally left `:::hide`, `:::solution`, `:::grade`
on the old `_verbatim_block` inner fence: `solution`/`grade` bodies are meant to
be *consumed* later (solutions build / grading), so they need separate design.

## Changes made (all in working tree, tracked files — `git status` shows them)
1. **`CLAUDE.md`** — new section "Avoid inner ``` fences inside noop author
   blocks" documenting the above (done state, not future work).
2. **`SFLMeta/Comment.lean`** — added `noopCodeBlockFor` helper +
   `@[code_block dev] def devBlock` (returns `Block.other Block.devcomment #[]`).
   The old `@[directive] def dev` is kept (harmless).
3. **`SFLMeta/Instructors.lean`** — added
   `@[code_block instructors] def instructorsBlock` (returns
   `Block.other Block.instructors #[]`).
4. **`scripts/to_verso.py`** — added `_code_block(tag, text)` helper (fence grown
   to outrun internal backtick runs, same logic as `_verbatim_block`).
   `_emit_noop_directive` now appends `_code_block(directive, text)` instead of
   `:::{directive}\n{_verbatim_block(text)}\n:::`. `_verbatim_block` is retained
   (still used by hide/solution/grade).

## Regenerated (untracked — `*Verso.lean` are gitignored, regenerate with the script)
Ran `python3 scripts/to_verso.py LF/<Chapter>.lean LF/<Chapter>Verso.lean` for
all 9 chapters that contain these blocks: Induction, Lists, IndPropRegexp,
IndProp, Maps, Logic, Tactics, UsingLean, Poly. Verified: **no `:::dev` /
`:::instructors` directives remain** in any `*Verso.lean` (`grep` is clean); all
now use ` ```dev ` / ` ```instructors ` code blocks.

## Verification status
- `lake build SFLMeta.Comment SFLMeta.Instructors` — **passes** (code blocks
  compile).
- The `dev`/`instructors` change is provably orthogonal and strictly safer (raw
  body can't break the parser). Confirmed by rebuilding InductionVerso from BOTH
  the old generator output and the new one: **identical failure profile** (4
  source errors), and **0 of them are dev/instructors-related**.
- The remaining InductionVerso (and ListsVerso, IndPropRegexpVerso, …) build
  failures are **PRE-EXISTING and unrelated**: `::::exercise (…)` containing a
  same-width `::::full` (Verso requires the outer directive fence to be strictly
  longer than a nested one). This is a separate `to_verso` generator bug about
  container-fence widths — NOT part of this task.
- A per-file build sweep was **in progress** when work stopped. Partial results
  (all show `dev_related_errors=0`, confirming no regression):
  ```
  InductionVerso:     exit=1 src_errors=4 dev_related_errors=0
  ListsVerso:         exit=1 src_errors=4 dev_related_errors=0
  IndPropRegexpVerso: exit=1 src_errors=4 dev_related_errors=0
  (IndProp, Maps, Logic, Tactics, UsingLean, Poly not yet recorded)
  ```

## To resume on the other machine
1. Re-run the per-file build sweep to finish confirming no regressions
   (from repo root):
   ```sh
   for m in InductionVerso ListsVerso IndPropRegexpVerso IndPropVerso \
            MapsVerso LogicVerso TacticsVerso UsingLeanVerso PolyVerso; do
     lake build "LF.$m" > /tmp/build_$m.log 2>&1; rc=$?
     dev=$(grep -ic 'error:.*dev' /tmp/build_$m.log)
     src=$(grep -c 'error: LF/' /tmp/build_$m.log)
     echo "$m: exit=$rc src_errors=$src dev_related_errors=$dev"
   done
   ```
   Expectation: any `exit=1` files should have `dev_related_errors=0`. If a file
   compiled before (no errors) it must still compile.
   NOTE: `| tail` MASKS lake's exit code — always capture `$?` on the bare `lake
   build`, don't pipe it, or you'll misread a failure as success (this bit us).
2. If a stale `.lake/packages/subverso/.git/index.lock` appears (transient git
   lock, breaks `lake`), remove it: `rm -f .lake/packages/subverso/.git/index.lock`.
3. Decide whether to also convert `:::hide` (also a pure noop — could follow the
   same ` ```hide ` pattern) and, with more design, `:::solution` / `:::grade`.
4. Commit the 4 tracked-file changes when satisfied. (Currently on branch
   `bcp-misc`. Nothing has been committed for this task.)
5. Delete this HANDOFF file once resumed.

## Also note (unrelated, from earlier this session)
An in-progress conflicted merge of PR #58 ("Update ci.yml") was aborted with
`git merge --abort` at the user's request. Working tree is clean w.r.t. that.
