# SF-in-Lean Guide for Contributors

This file records the conventions and important decisions we have made
about writing *Software Foundations in Lean* (SFL): workflow, Lean
coding style, Verso markup, comment conventions, the order in which
tactics are introduced, etc. Please help keep it clear and up to date!

> [!IMPORTANT]
> The present file covers *workflow and mechanics*. For stylistic matters, such
> as Lean conventions, pedagogical and presentational conventions, and writing
> style, see [STYLE.md](STYLE.md). Please have a look at it before contributing.

## Top-level orientation

### Guiding philosophy

These are the tenets of the SFL effort, in order. Consult these tenets
when making a change: If your change is supported by them, then
make it; no need for excessive coordination. If it is not supported by
at least one tenet, then either your change is out of scope or a tenet
is missing. If you are not sure then have a discussion (see below), and
refer to the tenets to drive a decision (potentially updating the tenets).

1. SFL aims for exceptional pedagogy and presentational polish.
2. SFL is _exercise-based_: Every important concept comes with
   hands-on exercises to reinforce it, with solutions.
3. SFL strives to teach _proof engineering_, which involves
   constructing readable and maintainable formalizations and proofs.
    - Corollary: Students should understand particular tactics and
      what they do, starting small and growing in sophistication.
    - Corollary: Definitions and proofs are written in idiomatic Lean
      (mostly the way it is for engineering/maintainability reasons),
      only deviating (temporarily) for strong pedagogical reasons.
      Specific patterns and rules are given later in this file,
      starting with **Lean Style**.
4. SFL developments connect with those in
   [CSLib](https://github.com/leanprover/cslib/tree/main) where
   possible. Some of SFL's languages, semantics, etc. might eventually
   be contributed to CSLib.

### Communicating among ourselves

For discussions, we use a combination of tools.

- **Zulip:** The private
  [SFL contributors channel](https://leanprover.zulipchat.com/#narrow/channel/607217-lean-software-foundations-contributors)
  channel on the Lean Zulip is the main forum for discussing the translation effort.
  If you have a high-level comment or want to start a discussion about an issue
  of general interest, post here. (This channel is private and is expected to
  remain private. If, at some point, we find ourselves with a lot more people
  actively involved and/or no need to keep anything private, we may sunset it.)

  There is also a `lean-software-foundations` channel, which is currently not
  used for much (most people working on SFL are not even subscribed, to avoid
  confusion about where things should go). Its main role for the moment is that
  some of the lead maintainers of Verso are members.

- **GitHub issues:** If you are working with others to tackle a specific GitHub issue,
  you can use comments on that issue for discussion and coordination.

- **In-text:** If you have a local comment that you want someone to think about
  at some point when they have that section of the material paged in, put it
  directly in the appropriate Lean file inside a `:::dev` block; see the
  [style guide](STYLE.md#internal-commentary-directives) for its usage.

- **On PRs:** We prefer _not_ holding longer discussions in annotations on PRs,
  because they tend to either get lost when the PR is merged or delay merging.
  Putting very local or short-term comments in this medium is fine -- or you can
  just make the change by directly adding commits to the PR, if it's clear what
  needs to be done.

These conventions are still developing, so feel free to suggest better ways of
working if you see them!

## Repository organization and Makefile targets

Each volume has its own top-level directory (LF, HL, etc.).

Within that directory, each chapter has a `.lean` file, in Verso format.

Running `make` at the top level produces, for each volume, four
different ready-for-distribution outputs in a temporary top-level
`_out` directory, each with both `.lean` and `.html` variants.

- **student**   (full prose, solutions elided)
- **solutions** (full prose, solutions shown)
- **terse**     (little prose, no solutions, workinclass elided;
                 for lecturing)
- **grading**   (solutions variant with automated grading support)

There are also more specific `make` targets that build faster: see the `Makefile`.

To build everything and preview it locally, do `make serve`,
then visit http://localhost:8000
(`make serve` builds stuff then serves `_out/` on port 8000).

## Git branches and CI

We use Git and GitHub, with some simple conventions:

* The `main` branch must always build.
* Never commit directly to `main`. Instead, create a branch and
submit your changes as a pull request (PR). More on PR cadence below.
* After your PR is merged, delete the branch to keep the repo tidy.

We prefer that people create branches in the sf-in-lean repo rather
than creating forks in their own GitHub accounts for working on stuff.
This makes it easier for everybody to maintain a global view of what's
going on.

Our CI uses a small [GitHub Actions workflow](.github/workflows/ci.yml).
It runs `make` on every pull request and on every push to `main`.

We also have branch protection enabled, which requires the following before merging:
* At least one approval from someone on the `sf-mergers` list before merge is allowed
* No outstanding conversations on the PR
* CI build succeeds

We use a linear history, with squash-and-rebase merges.

## Workflow

General guideline: Prefer just making changes as a PR rather than
talking about them first. To make sure your PR is likely to be
accepted, use your best judgment based on the tenets (above) and
design rules (below) in this file.

PRs should represent coherent pieces of work so that they are easy to
review. As a general guideline: create PRs sooner, in smaller chunks,
rather than later in bigger chunks. A day's worth of changes to a
specific part of some chapter might constitute a coherent set of
changes that can be PR'd and merged by itself, even if you plan to
continue editing the same chapter tomorrow.

### The path to merging a PR

Once you have your PR, submit it in _Draft_ mode to signal that you
are ready for comments. Other SFL collaborators will take a look. Once
discussing has settled, switch the PR to normal mode. Then either Mike
or Benjamin will review and merge it.

How should the discussion go?

1. While in draft mode you are free to comment using the GitHub
commenting feature on the PR, e.g., via the web interface. Before
changing the PR out of draft mode, make sure all discussions on Github are
resolved. Ones that are unresolved can be made into comments in the PR
itself, prefixed with your GitHub ID and a colon.

2. If a review surfaces an issue whose resolution may have broader
implications, please start a thread on Zulip for more discussion.
Record the resolution here in [CONTRIBUTING.md] if appropriate.

3. In-file comments should be deleted if they get resolved.

4. Once a PR moves out of Draft mode, Benjamin and/or Mike will
review it. Please address these comments in a subsequent commit, either
making appropriate changes or else responding in the file with your
own comments.

### Stacked PRs

Sometimes you want to keep working on a follow-up (chunk 2) while chunk 1 is
still waiting for review, and chunk 2 builds on chunk 1. Don't wait — and don't
branch chunk 2 off `main`, or it will show chunk 1's changes too and report
spurious conflicts. Instead **base the second branch and PR on the first
branch**:

```
gh pr create --base <chunk-1-branch> --head <chunk-2-branch>
```

GitHub then diffs chunk 2 against chunk 1, so the PR shows only the incremental
change, with no false conflicts, and it automatically retargets chunk 2's base
to `main` once chunk 1 merges. You can keep stacking (chunk 3 on chunk 2, ...)
and review/merge bottom-up.

One wrinkle: we use **squash-merge** for PRs, and squashing collapses chunk 1 into a
single new commit on `main` that shares no history with the original branch, so after
chunk 1 merges the still-open chunk 2 will suddenly report conflicts. The fix
is a one-time rebase that drops the now-redundant commits and replants your real
work on top of `main`:

```
git fetch origin
git rebase --onto origin/main <old-chunk-1-tip> <chunk-2-branch>
git push --force-with-lease
```

## Tools for coordinating work

We prefer to move fast rather than over-coordinate synchronously, but
we also want to avoid conflicts when possible. We use the [GitHub
issue tracker](https://github.com/plclub/sf-in-lean/issues) for
recording large tasks that need to be done (small or local tasks can
just be recorded in comments in the affected Lean file) and for
keeping track of work in progress, plus the
[Current Activity](https://github.com/plclub/sf-in-lean/issues/123)
meta-issue for getting an overview of who is working where.

1. Assign yourself or others to an issue if it is something you _may_
   work on or you want to be updated on discussions associated with
   the issue.  Being assigned to an issue does _not_ mean that you
   have it "locked" and other people should not work on it or touch
   associated files.
2. When you start working on an issue, assign it to yourself so that
   other people know you are thinking about it (if not already assigned).
3. When you start _actually making changes_, make sure you
   are working on a branch in the main repo (not a fork), and push your
   commits back to `main` frequently, so that others can see which files
   you are touching in the Current Activity meta-issue.
4. When you submit a PR on your work, refer to the relevant issue in the
   PR message. Edit the work-in-progress issue with a pointer to the PR.
5. Resolve the issue when the PR is resolved. Edit the work-in-progress
   to remove the activity.

### Branch activity dashboard

To see at a glance who is working on what, look at the pinned
[Current Activity](https://github.com/plclub/sf-in-lean/issues/123) issue.
It is regenerated automatically every half hour (and when PRs are created or
merged) and shows the status of every active branch and file on the remote.

We use this display very actively to make sure we're not stepping on each
others' toes and see where coordination is required.

Reading the table:

- **Status**: The branch's open PR (or "No PR") and how close it is to merging:
  + "Review required" while a `sfl-mergers` code owner still has to approve
  + "(N unresolved)" open review threads
  + "Ready" once approved with nothing unresolved
  + "🚧 auto-merge held" when auto-merge is on
    but the PR is stuck outside the merge queue
  + "⚠️ conflicts with `main`" when the branch no longer merges cleanly.
- **Overlaps**: Other active branches touching the same files.
  + ⚠️ marks a merge conflict
  + `(includes)` / `(included in)` means this branch fully
  contains / is contained in the other (stacked work, never a conflict)
  + `A ⊃ B` groups a concurrent overlap B under another overlap A that contains it.

`archive/...` branches are omitted.

## Repo organization technicalities (optional)

_Most contributors can skip this section._

### Extractor maintenance

The standalone-`.lean` extractor
(`SFLMeta/Save.lean`) resolves a chapter's dependencies two ways, and one needs
ongoing upkeep: when a chapter imports a Verso chapter from an *earlier volume*
(e.g. `HL.Imp` imports `LF.Typeclasses`), that cross-volume dependency must be
listed in `Targets.lean`'s `crossVol` match; add an entry for every new
such import (it can't be auto-derived, since mapping a module name to its `Part`
needs a compile-time `%doc`). Plain Lean support-lib prerequisites
(`CustomTactics`, `SFLCompat`) are instead bundled verbatim by `bundleLoop` and
need no per-import upkeep.

### Porting chapters from Rocq

The `to_verso` script automates the mechanical parts of translating from Rocq to
Verso-formatted Lean. It leaves all the interesting bits to be translated manually.

Example usage:
```
python3 scripts/to_verso.py old/orig-plf-files/Hoare.v HL/Hoare.lean
```

## AI policy

SFL contributors may use AI tools to help create, validate, and
maintain content in this repo.  AI-generated content, especially
public-facing content such as words and proofs in book chapters,
should be carefully vetted.

For PRs with public-facing content, we follow the [Mathlib AI
policy][mathlib-ai-policy], which mandates summarizing how AI is used
in the PR description. PR descriptions should be written (or at least
carefully rewritten) by hand.

Here is the part of the [Mathlib AI policy][mathlib-ai-policy] that
should be applied when AI tools are adding or changing public-facing content:

> Explain which tool(s) you used and how you used it. This provides
> useful context for reviewers: tools make different mistakes than humans,
> so knowing this makes it easier to spot common errors.

Scripts and other infrastructure in the repository that are used to
help create public-facing content are excluded, i.e., AI usage here
doesn't need to be explained in the PR description.

Instructions for Claude live in [CLAUDE.md] (which also asks Claude to
pay attention to the conventions in this file).

Raw AI output should not be posted to GitHub or Zulip without an
indication that that's what it is.

Scripts that are mostly or wholly AI generated should be marked as
such: these will typically be lower quality than human-created or
heavily vetted code, and people looking at them should understand
that.

[mathlib-ai-policy]: https://leanprover-community.github.io/contribute/index.html#use-of-ai
