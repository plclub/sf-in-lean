# Software Foundations in Lean

This repository contains the work-in-progress sources of [Software Foundations](https://softwarefoundations.cis.upenn.edu/), implemented using Lean.

Why are we carrying out this work? You might wonder. There exist excellent texts on both [programming](https://lean-lang.org/functional_programming_in_lean/) and [theorem proving](https://lean-lang.org/theorem_proving_in_lean4/) in Lean. The [How to Prove It! in Lean](https://djvelleman.github.io/HTPIwL/) book introduces logic and proofs in Lean, and overlaps with SF's Logical Foundations text. The [CSLib](https://github.com/leanprover/cslib/tree/main) effort is building a CS-focused core development in Lean (basically "Mathlib for CS"), overlapping with SF's PL Foundations text. 

We believe that there is room for a pedagogically minded text focusing on the mathematical foundations of writing correct software. But we need to be careful not to reinvent the wheel. We need to ensure that, once complete, SF in Lean complements these existing works and/or notably improves on their limitations.

To this end, and to facilitate rapid development, we offer a list of tenets that guide SF in Lean's development. These tenets will keep us on track when making decisions, and hopefully redirect us away from topics adequately covered elsewhere, and toward clear gaps.

We also offer some rules for distributed collaboration. We want to take input from as many people as possible but develop clear guidelines for taking contributions and resolving disagreements.

**To do**: Explain the difference between SF and SFL, official terminology and
naming, ... 

## Tenets

(In order of priority.)

1. SFL aims for exceptional pedagogy and presentational polish
2. SFL is _exercise-based_: Every important concept has hands-on exercises to reinforce it
3. SFL strives to teach _proof engineering_, which involves constructing readable and maintainable formalizations and proofs
    - Corollary: Students should understand particular tactics and what they do, starting small and growing in sophistication
    - Corollary: Definitions and proofs are written in idiomatic Lean (mostly the way it is for engineering/maintainability reasons), only deviating (temporarily) for pedagogical reasons
4. SFL developments should connect to those in [CSLib](https://github.com/leanprover/cslib/tree/main), as much as possible; e.g., some/all of SFL's fully developed languages, semantics, etc. could have a direct place in CSLib. This implies we should be paying attention to (at the least) and coordinating with (at best) that effort.
5. SFL follows the path of topics of SF in Rocq unless there are specific reasons not to (that align with the above tenets)

### Proof engineering in Lean callouts

We should be following the [style guide](https://leanprover-community.github.io/contribute/style.html) and using the [Lean linter](https://github.com/leanprover-community/mathlib4/wiki/Setting-up-linting-and-testing-for-your-Lean-project). Some things to call out for those more familiar with Rocq:

1. While writing library code, it's fine and necessary to unfold and simplify through definitions. When using that code, the idiomatic way is not to "peek through the interface".

## Rules for collaboration

**To do**: take inspiration from Jimmy Wales' [Seven Rules of Trust](https://en.wikipedia.org/wiki/The_Seven_Rules_of_Trust), which underpin Wikipedia's distributed development.

## Tracking work (who's working on what)

We currently track in-progress work with **GitHub Issues**, not a separate board.

- **One issue per chapter/file.** To claim a piece of work, open (or find) its
  issue and **assign yourself** — the assignee is the single source of truth for
  who is working on what. Use the *"Chapter / file work"* issue template when
  claiming something new.
- **Link your PR.** Put `Closes #<issue>` in the PR description so the issue
  closes automatically when the PR merges.
- **Signal active code** by opening a **draft PR** early; it shows your
  work-in-progress before it's ready for review.
- **At-a-glance status:** the pinned **"Chapter status"** tracking issue lists
  every chapter and its current owner. Keep it up to date as you claim/finish.

(GitHub Projects boards are just a view over these issues; add one later if you
want kanban columns, but the issues above are the actual workflow.)

## Development workflow

`main` must always build. To keep it that way we use a standard
[GitHub flow](https://docs.github.com/en/get-started/using-github/github-flow)
plus a small continuous-integration (CI) check. **Do not commit directly to
`main`** — every change goes through a pull request:

1. Update your local `main`:
   ```
   git switch main
   git pull
   ```
2. Create a branch for your change:
   ```
   git switch -c my-change
   ```
3. Make commits, then push the branch:
   ```
   git push -u origin my-change
   ```
4. Open a Pull Request against `main` on GitHub.
5. CI automatically builds the book on your PR. Once it is green
   (and the PR has been reviewed if appropriate), merge it.

Before opening a PR, build locally to catch problems early — the same check CI runs:

```
lake build     # build the book; fails if anything does not compile
```

### Keeping branches tidy

So old branches don't pile up, set these once:

- Repo **Settings → General → Pull Requests → ☑ Automatically delete head
  branches** — deletes a branch on GitHub when its PR is merged.
- `git config --global fetch.prune true` — every `git fetch`/`pull` then drops
  your local references to branches that were deleted on the server.

After your PR merges, delete the local branch (the GitHub Pull Requests
extension offers to do this for you):

```
git switch main
git pull
git branch -d my-change     # -d is safe: only deletes a fully-merged branch
```

### Continuous integration

CI is a single, deliberately tiny GitHub Actions workflow:
[.github/workflows/ci.yml](.github/workflows/ci.yml). It runs `lake build` on
every pull request and on every push to `main`. The file is commented; to add a
check, add a step.

### Branch protection (one-time GitHub setting)

CI runs on every pull request regardless, so you always see a ✅/❌ **build**
check. Whether a ❌ actually *blocks* merging depends on the plan:

- **Public repo, or private repo on GitHub Team/Enterprise:** branch rulesets
  are enforced — set one up (below) and a red check blocks the merge.
- **Private repo on the Free plan (where we are now):** rulesets can be created
  but are **not enforced**. Treat CI as advisory: **don't merge a red PR.** To
  get real enforcement for free while staying private, link the `plclub` org to
  [GitHub Education](https://education.github.com/), which grants GitHub Team to
  academic organizations at no cost.

To enable enforcement once on a paid/public plan, create a ruleset in
**GitHub → Settings → Rules → Rulesets → New ruleset → New branch ruleset**:

1. **Ruleset name:** e.g. `main must build`; set **Enforcement status** to **Active**.
2. **Target branches → Add a target → Include default branch** (`main`).
3. Enable these rules:
   - ☑ **Require a pull request before merging** (Required approvals: 0, or 1 for a reviewer)
   - ☑ **Require status checks to pass** → add the **build** check
4. Leave the **Bypass list empty** so the rules apply to everyone, admins included.
5. **Create.**

(The `build` check only appears once CI has run on `main` at least once.)

## Building the Verso Documentation

`make` builds the book. It regenerates the generated sources and produces three
HTML variants under `_out/`:

- `_out/student/`   — full prose, solutions elided
- `_out/solutions/` — full prose, solutions shown
- `_out/terse/`     — lecture/live-coding prose, solutions elided

To build everything and preview it locally:

```
make serve
```

then visit http://localhost:8000 (`make serve` builds, then serves `_out/` on
port 8000).

To build a single variant without serving, run e.g. `make lf-student`.

## License

This project is licensed under the Apache License, Version 2.0. See the
[LICENSE](LICENSE) and [NOTICE](NOTICE) files for details. Unless you state
otherwise, any contribution you intentionally submit for inclusion in this
work shall be licensed under the same terms, with no additional terms or
conditions.
