# SF-in-Lean Guide for Contributors

This file records the conventions and important decisions we have made
about writing *Software Foundations in Lean* (SFL): workflow, Lean
coding style, Verso markup, comment conventions, the order in which
tactics are introduced, etc. Please help keep it clear and up to date!

> [!IMPORTANT]
> The present file covers *workflow and mechanics*. For stylistic matters,
> such as pedagogical and presentational conventions, see
> [STYLE-CODE.md](STYLE-CODE.md) for Lean and Verso coding conventions,
> and [STYLE-WRITING.md](STYLE-WRITING.md) for writing style advice.
> (Please do have a look before contributing!)

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

  There is also a private `lean-software-foundations` channel, which is currently not
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
  because they tend to either get lost when the PR is merged or else delay merging.
  Putting very local or short-term comments on PRs is fine... or (often simpler) you can
  just make the change by directly adding commits to the PR, if it's clear what
  needs to be done.

These conventions are still developing, so feel free to suggest better ways of
working!

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

These recipes assume `origin` is the shared repo, which is the case if you have
write access and cloned it directly.  If you are working from a fork (the setup
in `ALPHATESTERS.md`), your `origin` is your fork and the shared repo is
`upstream`, so read `upstream/main` for `origin/main` throughout — rebasing onto
your fork's `main` would replant your work on a stale base.

## Tools for coordinating work

### Branch activity dashboard

We prefer to move fast rather than over-coordinate, but we also want
to avoid conflicts when possible. 

To see at a glance who is working on what, look at the pinned
[Current Activity](https://github.com/plclub/sf-in-lean/issues/123) issue.
It is regenerated automatically every half hour (and when PRs are created or
merged) and shows the status of every branch with a PR on the remote.

We rely heavily on this display to make sure we're not stepping on
each others' toes and to see where coordination is required.

### GitHub tools

We use the [GitHub issue
tracker](https://github.com/plclub/sf-in-lean/issues) for recording
large or global tasks that need to be done (small or local tasks can
just be recorded in comments in the affected Lean file) and for
keeping track of work in progress.

### Workflow

1. Assign yourself or others to an issue if it is something you _may_
   work on or you want to be updated on discussions associated with
   the issue.  Being assigned to an issue does _not_ mean that you
   have it "locked" and other people should not work on it or touch
   associated files.
2. When you start working on an issue, assign it to yourself so that
   other people know you are thinking about it (if not already assigned).
3. When you start _actually making changes_, make sure you are working
   on a branch in the main repo (not a fork), make a draft PR so it
   shows up in the Current Activity meta-issue, and push your commits
   frequently so that others can see which files you are touching in
   the Current Activity meta-issue.
4. Refer to the relevant issue(s) in the PR description. Edit the
   work-in-progress issue with a pointer to the PR.
5. Make sure the issue is resolved when the PR is merged (this may happen
   automatically). 


## Repo organization technicalities (optional)

_Most contributors can skip this part._

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

## Volumes and Versions

Version numbers, volume numbers, volume titles, and the release year are *build
facts*, not prose.  Each is recorded in exactly one place and reaches the text
through a Verso role, so a number quoted in a chapter can never drift out of
date.  **Never write any of these out by hand in a chapter.**

**Where each fact lives.**

| Fact | Home |
| --- | --- |
| Volume number and title | the `volumes` table in `SFLMeta/Volume.lean` |
| Which volume a chapter belongs to | `leanOptions = { weak.sfl.volume = "<slug>" }` on that volume's `[[lean_lib]]` in `lakefile.toml` |
| Release version | `version` in `lakefile.toml`, mirrored as `weak.sfl.version` under `[leanOptions]` |
| Release year | `weak.sfl.year` under `[leanOptions]` in `lakefile.toml` |
| Lean toolchain version | `lean-toolchain` (read straight from the compiler; nothing to maintain) |
| Series homepage | `sflHomepage` in `SFLMeta/Volume.lean` |

**Using them in a chapter.**  The roles are defined in `SFLMeta/Version.lean`.
Each takes no content — write the empty brackets:

```
This is version {sflVersion}[] of {volumeName}[] ({sflYear}[]), volume
{volumeNumber}[] of the series, tested with Lean version {leanVersion}[].
```

`{volumeNumber}[]` and `{volumeName}[]` mean *the volume being compiled*.  To
refer to another volume, name it with a slug or a number: `{volumeName "ts"}[]`,
`{volumeNumber "ts"}[]`, `{volumeName 3}[]`.

The recommended-citation BibTeX entry is generated in full, since it is entirely
mechanical.  A Preface asks for it with an empty directive:

```
:::citation
:::
```

which renders the entry for the current volume; `:::citation "ts"` (or
`:::citation 2`) gives another volume's.  The entry's shape — author list,
series, publisher — is `bibtexEntry` in `SFLMeta/Version.lean`, so a change
there updates every volume at once.

**Cutting a release.**  Bump `version` in `lakefile.toml`, bump
`weak.sfl.version` to match, set `weak.sfl.year` to the year of the release, and
tag the commit `v<version>` (Lake's convention, and what Reservoir reads).  The
release year is deliberately a recorded fact rather than the wall-clock year:
two builds of the same tag must agree, and a citation should name the year the
edition was published, not the year someone happened to rebuild it.

**Adding a volume.**  Add a row to `volumes` in `SFLMeta/Volume.lean`, add the
`[[lean_lib]]` with its `weak.sfl.volume` option, and add the `[[lean_exe]]`
that calls `SFLMeta.runVolume` with the same slug.  The slug is the one name
used everywhere a volume is identified mechanically: library and executable
names, the `_out/<slug>/…` build directory, and the saver's volume prefix.

**Why an option and not an import.**  A chapter cannot simply import a module
that says which volume it is in: chapters shared between volumes are the *same
file* (`HL/Slang.lean` and `TS/Slang.lean` are symlinked), so the library doing
the compiling is the only thing that can tell the two builds apart.  Hence the
per-`lean_lib` option.  A chapter compiled outside any volume library gets a
clear error from the role telling it which option to set.

## AI policy

SFL contributors may use AI tools to help create, validate, and
maintain content in this repo. However, our AI policy differs 
depending on whether the content is "user-facing" or not.

### User-facing content

As a rule, we do not use AI to generate any prose that appears in any volume of SFL. 
Contributors may ask AI for feedback on text they have written or use it to check for
spelling or grammar mistakes, but they should apply any AI suggestions manually after 
vetting their quality, rather than having an agent edit their text autonomously. Contributors 
also should not ask AI to produce text and manually edit it afterward. 

This is a strict policy, but we enforce it for a few reasons:
1. It guarantees that all text that enters SFL has been carefully considered and allows us to 
promise our readers that human intent and effort exists behind everything they read. 
2. It ensures that when reviewing text contributions, we do not need to worry about AI 
hallucinations or inaccuracies; we can review for pedagogical thoroughness and style 
without also needing to check accuracy.
3. Over the course of translating this book from the original Software Foundations, we 
have found validating AI text to be challenging; one only sees the final product, so to speak, 
and not all the other choices in presentation and content that could have been made. 
This tends to obscure many subtle points that would be better discussed explicitly. 

For definitions and theorem statements, we apply the same principles and restrictions 
as prose, since getting these exactly right is important to a coherent text. 

For proofs, contributors may use AI to produce a "first draft" of the proof. However, 
AI proofs should be carefully vetted and edited to ensure that they only use
tactics to which readers have been introduced (see the table in [STYLE-CODE.md](STYLE-CODE.md))
and generally follow good Lean style.

Since teaching Lean's syntax and metaprogramming is not an explicit goal of the course, 
syntax definitions and macros, including elaborators, delaborators, and unexpanders, are
not considered "user-facing" and are subject to the non-user-facing content policy
outlined below. However, any prose associated with them that either explains or justifies 
their existence to readers is subject to the same standards as any other prose.

AI generated text may appear inside `:::dev` blocks; often we will use these to keep track of  
feedback from agents that we have not yet incorporated into the text, for example. 
In such cases, the contents of these blocks should be marked as AI-generated. 

We follow the [Mathlib AI policy][mathlib-ai-policy] that
should be applied when AI tools are adding or changing user-facing content:

> Explain which tool(s) you used and how you used it. This provides
> useful context for reviewers: tools make different mistakes than humans,
> so knowing this makes it easier to spot common errors.

In PRs, we summarize how AI is used for that PR
in the PR description. These descriptions should be written by hand
or should include a disclaimer that the description was generated by AI.

### Non-user-facing content

Scripts and other infrastructure in the repository (e.g., the contents of the `SFLMeta` folder) 
that are used to help create user-facing content are not subject 
to the restrictions above. AI may be used here to generate code and documentation, and usage
doesn't need to be explained in the PR description. 

However, scripts and code that are mostly or wholly AI generated should be marked as
such: these will typically be lower quality than human-created or
heavily vetted code, and people looking at them should understand that.

### Other general guidelines

Instructions for Claude live in [CLAUDE.md](CLAUDE.md) (which also
asks Claude to pay attention to the conventions in this file and the style guides).

Raw AI output should not be posted to GitHub or Zulip without an
indication that that's what it is.

[mathlib-ai-policy]: https://leanprover-community.github.io/contribute/index.html#use-of-ai
