# SF-in-Lean Guide for Contributors

This file records the conventions and important decisions we have made
about writing *Software Foundations in Lean* (SFL): workflow, Lean
coding style, Verso markup, comment conventions, the order in which
tactics are introduced, etc.

We don't have many contributors yet outside the core group that's been
working together on the translation for a couple of months, so there
are certain to be things that are not clear.  Please help us figure
out what those are and document the clarifications in this file.

## Top-level orientation
###    Guiding Philosophy

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
      (Specific patterns and rules are given at the end of this file,
       starting with **Lean Style**.)
4. SFL developments connect with those in
   [CSLib](https://github.com/leanprover/cslib/tree/main) where
   possible. Some of SFL's languages, semantics, etc. might eventually
   be contributed to CSLib.

##    Zulip

The [SFL contributors
  channel](https://leanprover.zulipchat.com/#narrow/channel/607217-lean-software-foundations-contributors)
  channel on the Lean Zulip is the main forum for discussing the translation
  effort. 

## Communicating among ourselves

For discussions, we use a combination of tools.  

- If you have a high-level comment or want to start a discussion about
  an issue of general interest, post on the [SFL contributors Zulip
  channel](https://leanprover.zulipchat.com/#narrow/channel/607217-lean-software-foundations-contributors).  

  This channel is private and is expected to remain private. If, at
  some point, we find ourselves with a lot more people actively
  involved and/or no need to keep anything private, we may sunset it. 

  There is also a `lean-software-foundations` channel, which is
  currently not used for much (most people working on SFL are not even
  subscribed, to avoid confusion about where things should go) -- its
  main role for the moment is that some of the lead maintainers of
  Verso are members.

- If you are working with others to tackle a specific GitHub issue,
  you can use comments on that issue for discussion and coordination.

- If you have a local comment that you want someone to think about at
  some point when they have that section of the material paged in, put
  it directly in the appropriate .lean file, either in a comment (if
  it's a plain .lean file) or in a `:::dev` block (if it's been
  versified), marked with your initials.  These comments are not
  included in the final build products.

  In-text comments can also be used for coordinating work on specific
  issues.

We prefer _not_ holding discussions in annotations on PRs, because
they tend to either get lost when the PR is merged or delay merging.
Putting very local or short-term comments in this medium is fine -- or
you can just make the change by directly editing the PR, if you think
it's clear.

These conventions are still developing, so feel free to suggest better
ways of working if you see them! 

### Repo organization and make-fu

Each volume gets its own top-level directory (LF, HL, etc.).

Within that directory, each chapter gets a `.lean` file, in Verso format.

Running `make` at the top level produces, for each volume, three
different ready-for-distribution outputs in a temporary top-level
`_out` directory, each with both .lean and .html variants.
  - **student**   (full prose, solutions elided)
  - **solutions** (full prose, solutions shown)
  - **terse**     (little prose, no solutions, workinclass elided;
                   for lecturing)

To build everything and preview it locally, do `make serve`,
then visit http://localhost:8000
(`make serve` builds stuff then serves `_out/` on port 8000).

### Git-fu

We use Git and GitHub, with some simple conventions:

* The `main` branch must always build.
* Never commit directly to `main`. Instead, create a branch and
submit your changes as a pull request (PR). More on PR cadence below.
* After your PR is merged, delete the branch to keep the repo tidy.

We prefer that people create branches in the sf-in-lean repo rather
than creating forks in their own GitHub accounts for working on stuff.
This makes it easier for everybody to maintain a global view of what's
going on.

Our CI uses a small GitHub Actions workflow:
[.github/workflows/ci.yml](.github/workflows/ci.yml).
It runs `make` on every pull request and on every push to `main`.

We also have branch protection enabled, which requires the following before merging:
* At least one approval before merge is allowed
* Linear history (use rebase and squash merge)
* CI build succeeds

## Cadence of code changes

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
changing the PR out of draft mode, make sure all discussions on GH are
resolved. Ones that are unresolved can be made into comments in the PR
itself, prefixed with your GitHub ID and a colon.

2. If a review surfaces an issue whose resolution may have broader
implications, please start a thread on on Zulip for more discussion.
Record the resolution here in CONTRIBUTING.md if appropriate.

3. In-file comments should be deleted if they get resolved.

4. Once a PR moves out of Draft mode, Benjamin and/or Mike will
review it. Please address these comments in a subsequent commit, either 
making appropriate changes or else responding in the file with your
own comments.

## Tools for coordinating work

We prefer to move fast rather than over-coordinate synchronously, but
we also want to avoid conflicts when possible. We use the [GitHub
issue tracker](https://github.com/plclub/sf-in-lean/issues) for
recording large tasks that need to be done (small or local tasks can
just be recorded in comments in the affected .lean file) and for
keeping track of work in progress that other people should be careful
not to step on.
1. Assign yourself or others to an issue if it is something you _may_
   work on or you want to be updated on discussions associated with
   the issue.  Being assigned to an issue does _not_ mean that you
   have it "locked" and other people should not work on it or touch
   associated files.
2. When you start working on an issue, assign it to yourself so that
   other people know you are thinking about it (if not already assigned).
3. When you start *actually making changes* on a branch, edit the
   [Work In Progress](https://github.com/plclub/sf-in-lean/issues/25)
   issue (it is pinned at the top of the issues page on GH) so that
   people know to be careful not to step on your work. If/when you have
   a branch for your work, link it from the work-in-progress issue.
4. When you submit a PR on your work, refer to the relevant issue in the
   PR message. Edit the work-in-progress issue with a pointer to the PR.
5. Resolve the issue when the PR is resolved. Edit the work-in-progress
   to remove the activity.

### Status; plain lean vs. verso files (temporary)

At the moment, most of the files in Logical Foundations have been
converted to regular Lean files.  (Programming Language Foundations
remains to be translated.)  The `.lean` files are currently in regular
Lean syntax, but we want them to be formatted as Verso files
("documentation first") and are working on translating them one by
one.  

Benjamin owns the conversion tooling (`scripts/to_verso.py`) and the
eventual native-Verso format decisions, so you can work on a given
`.lean` file in whatever format it exists in at the moment.  But note
that `make` now regenerates and builds each `<Ch>Verso.lean` (via the
`check-verso-chapters` target, which CI runs), so if you edit a
code-forward `.lean` chapter, keep that round-trip green: after a
change, regenerate (`python3 scripts/to_verso.py <Vol>/<Ch>.lean`) and
build the generated Verso (`make check-verso-chapters`).  CLAUDE.md
("Writing comments that survive to_verso") lists the authoring rules
that keep the conversion happy.

## Lean Style

We generally follow the [Mathlib style
guide](https://leanprover-community.github.io/contribute/style.html),
with the caveat around pedagogy in our SFL **Philosophy** (given above),
which requires (among other things) adhering to the order of tactics, given next.
We use the Lean linter by default.

### Tactics: order of introduction

A core pedagogical decision is that tactics are introduced gradually.
The table below lists the tactics **first introduced** in each
chapter, in chapter order. It is derived from the current sources
(tactic-position occurrences in real code, comments excluded) and
should be kept in sync as chapters are rewritten.

| Chapter           | Tactics first introduced |
|-------------------|--------------------------|
| `Basics`          | `rfl`, `intro`, `rewrite`, `cases`, `exact` |
| `Induction`       | `induction`, `have`, `rw`, `<;>` |
| `UsingLean`       | `dsimp`, `calc`, `exact?`, `rw?` |
| `Lists`           | *(none new)* |
| `Poly`            | *(none new)* |
| `Tactics`         | `intros`, `apply` (and `apply … at`), `replace`, `symm`, `injection`, `injections`, `congr`, `assumption`, `contradiction`, `unfold`, `split` |
| `Logic`           | `constructor`, `obtain`, `left`, `right`, `ext`, `by_cases`, `exfalso` |
| `IndProp`         | `rcases`, `subst` |
| `Typeclasses`     | `decide` |
| `Automation`      | `lia`, `try`, `repeat`, `specialize`, `trivial`, `simp` |
| `HL/Imp`          | *(none new)* |

**Notes**
- **`lia` rather than `omega`** The latter is being phased out.
- `IndPropRegexp` has been folded into `Automation`
- `Maps` will be folded into `Typeclasses`
- Candidate tactics still to be placed include `show`, `rename_i`, `revert`, `suffices`, `tauto`. 
- Tactics `grind`, `aesop`, are deferred to a later volume. 

Related notation introduced alongside tactics: anonymous constructor
`⟨…⟩` (`Lists`); destructuring `let ⟨…⟩ := …` and `cases h : …`,
`induction … generalizing …` (`Tactics`); projection/`Iff` syntax
`.left`, `.right`, `.mp`, `.mpr`, and rewriting by an `↔` (`Logic`).

### SFL-specific conventions

* **Structured `cases`/`induction`.** Prefer

  ```lean
  cases b with
  | true  => …
  | false => …
  ```

  over the separate `case` syntax *and* over the bare `·` goal selector — i.e. prefer
  `cases h with | …` / `induction h with …`.
  Put each alternative on its own unindented line beginning with `|`.
  
* **`rewrite` before `rw`** (see tactic chart above) --
  `rw [h]` is roughly `rewrite [h]; rfl`, which is too strong at
  first: it hides the closing `rfl` and makes proofs step
  confusingly (the goal vanishes when you step past the final `]`).
  We introduce `rw` specifically in `Induction.lean` and use from
  then on.

* **`example` for one-off demos.** Prefer `example …` over a named
  `theorem foo …` for throwaway illustrations (tactic demos, "silly" lemmas,
  etc.) that are never referenced later — Lean's `example` doesn't force us to
  invent a name (unlike Rocq).

* **Explicit rewrites over `dsimp`/`simp` through notation** (see
  "Notation and simplification").

* **`sorry` placeholders are checked, not silent.** Where a `sorry`
  appears , wrap it so the warning is asserted:
  ```lean
  /-- warning: declaration uses `sorry` -/
  #guard_msgs in
  example : … := sorry
  ```

* **Aborted/abandoned lemmas** failing proofs and examples with type errors
  should have a `#guard_msgs` above them with the expected error, rather than
  ending with `sorry`.

* **Library vs. client code.** Inside a definition's own library it is
  fine to unfold and simplify through definitions; *using* that code,
  do not "peek through the interface."

### Unicode Text and Formatting

Go Unicode-native! Use subscripts on variables, like x₁ x₂  etc. Use α Γ etc. 
for type variables and other standard notation. Use arrows like → ⇓ for reduction
and evaluation. TODO: Elaborate on guidelines here.

We will use the standard Lean auto-formatter. Until then, here are some formatting
guidelines.

* Keep short branch bodies inline: 
  
  ```lean
  cases b, c with
  | true, false => rfl
  | false, _ => simp
  ```

  *Optionally*, align patterns across alternatives:

  ```lean
  cases b, c with
  | true,  _ => rfl
  | false, _ => simp
  ```

  For multiline branch bodies, put `=>` after the alternative *without* padding
  and indent the body by two spaces, **aligned** with the alternative name:

  ```lean
  cases b with
  | true =>
    simp
    exact h
  | false =>
    rw [h]
    exact hf
  ```
  
* **`rewrite` before `rw`** (see tactic chart above) --
  `rw [h]` is roughly `rewrite [h]; rfl`, which is too strong at
  first: it hides the closing `rfl` and makes proofs step
  confusingly (the goal vanishes when you step past the final `]`).
  We introduce `rw` specifically in `Induction.lean` and use from
  then on.

* **Explicit rewrites over `dsimp`/`simp` through notation** (see
  "Notation and simplification").

* **`sorry` placeholders are checked, not silent.** Where a `sorry`
  appears (incomplete proof, exercise scaffold), wrap it so the
  warning is asserted:
  ```lean
  /-- warning: declaration uses `sorry` -/
  #guard_msgs in
  example : … := sorry
  ```

  The `#guard_msgs` wrapper is checked while the book is compiled.
  In the rendered book and generated projects, the expected-message docstring and
  `#guard_msgs ... in` are stripped.

* **Aborted/abandoned lemmas** become unnamed `example`s closed with
  `sorry` (the SFL analogue of Rocq's `Abort`).

* **`example` for one-off demos.** Prefer `example …` over a named
  `theorem foo …` for throwaway illustrations (tactic demos, "silly" lemmas,
  etc.) that are never referenced later — Lean's `example` doesn't force us to
  invent a name (unlike Rocq).  Reserve names for results used elsewhere or
  graded. (berberman, review of PR #61.)

* **Library vs. client code.** Inside a definition's own library it is
  fine to unfold and simplify through definitions; *using* that code,
  do not "peek through the interface."

* **Name namespaces for what they are, not after a type they contain.**
  A warm-up / redefinition section that shadows later top-level names goes in a
  clearly-named namespace — e.g. `namespace Warmup`, not `namespace AExp` (too
  easily misread as the `Aexp` type, so `AExp.Bexp` reads like a field of
  `Aexp`).  (Rocq's `Module AExp` warm-up in `Imp` became `namespace Warmup`.)

### Notation and simplification

When notation is implemented via typeclass instances, `dsimp [add]` /
`dsimp [app]` do *not* resolve the instance down to the underlying
definition, and `simp` is often too powerful for teaching. So
**rewrite explicitly by equational lemmas** instead — e.g. `n + (m +
1) = n + m + 1` or `(h :: t) ++ l = h :: t ++ l` — rather than
reaching for `dsimp`/`simp`.

### Arithmetic / the custom `Nat`

`Basics` defines its own `Nat` with `zero`/`succ` constructors and
overrides the stdlib typeclasses for `-`, `*`, and `^` (but **not**
`+`, which is too pervasive in the stdlib to shadow safely). Write
arithmetic proofs against these definitions (`add_succ`, `add_zero`,
`mul_succ`, …). `calc`-style equational reasoning is introduced in
`Induction`.


## Verso markup conventions

BCP: Claude-generated material here -- human review needed...

### Chapter file structure

Each chapter is a single `.lean` file in its volume directory.

Sections within a chapter use standard markdown headings (`#`, `##`,
`###`, …) relative to the `#doc` level.

Lean declarations (`def`, `theorem`, `inductive`, etc.) appear directly
in the Verso source and are elaborated by Lean as the book is compiled,
so type errors and broken proofs are caught at build time.  Code that
should appear in the rendered HTML uses fenced `` ```lean `` blocks.

### Fence depth: `:::` vs `::::`

Verso uses colon-fence depth the same way markdown uses backtick depth
for nesting.  Use **three colons** (`:::`) for a directive whose body
contains only prose and code blocks.  Use **four colons** (`::::`)
whenever the body itself contains three-colon directives.

In practice the widths follow the nesting: leaf directives (`:::dev`,
`:::instructors`, `:::hide`, `:::answer`, `:::grade`, `:::solution`, `:::terse`,
`:::slidebreak`) are always three colons; a `::::full` / `::::hide` / `::::quiz`
that nests a leaf uses four; an `:::::exercise` that nests those uses five.
`to_verso` computes the minimal correct width automatically; when hand-authoring,
just make each container strictly wider than everything directly nested inside
it.

### Build variants and prose directives

Every chapter is compiled once but rendered in three _variants_:
- **student** — full prose, solutions elided
- **solutions** — full prose, solutions shown
- **terse** — abridged prose for live-coding / lecturing

Three directives control what prose appears in which variant.

**`::::full … ::::`** — Content for the reading builds (student and
solutions). This is the main narrative that students encounter in the
book. Hidden in the terse build to keep lecture slides uncluttered.

```
::::full
One notable thing about Lean is that its set of built-in features is
_extremely_ small.  For example, instead of the usual palette of
atomic data types (booleans, integers, strings, etc.), Lean offers
a powerful mechanism for defining new data types from scratch…
::::
```

**`:::terse … :::`** — Content shown _only_ in the terse build.
Typically a one- or two-sentence cue for a live-coding presenter,
standing in for the adjacent `::::full` prose.

```
:::terse
A datatype definition:
:::
```

**`:::solution … :::`** — Prose shown only in the **solutions** build.
Use this for worked prose answers to open-ended exercises:
discussions, design rationale, or illustrative code that is not
intended to compile. (For _compilable_ answers inside `lean` blocks,
use `solution!` or `-- SOLUTION`, described below.)

The standard pattern at each presentation point is a `:::terse` cue
followed by a `::::full` narrative block followed by a shared `lean`
code block.  All three builds see the code; only the relevant prose
builds see each prose variant.

### Exercise and grading infrastructure

**`::::exercise (rating := N) (name := "foo") … ::::`** — Marks an
exercise block.  `rating` is a difficulty from 1 (easy) to 5 (hard);
`name` is a short identifier used in headings and cross-references.
Renders as a styled box with stars in HTML; produces a `### Exercise
(N stars): foo` module-doc heading in the extracted `.lean` files.
Should always contain a nested `:::grade` block.

Typical structure:

```
::::exercise (rating := 1) (name := "nandb")
Remove the `sorry`s below and complete the definition of `nandb`…

  [lean block with solution! markers]

:::grade
```
GRADE_THEOREM 1: nandb_test4
```
:::
::::
```

**`:::grade … :::`** — Grading spec, always nested inside
`::::exercise`. Contains one or more `GRADE_THEOREM <pts>: <name>` or
`GRADE_MANUAL <pts>: <name>` lines for autograding scripts. Currently
a noop in all rendered outputs (body discarded at elaboration); the
spec survives verbatim in the Verso source for tooling.

### `lean` block flags

Use ordinary fenced `lean` blocks for examples that should elaborate in
the chapter, appear in the rendered book, affect later Lean blocks,
and be emitted as normal Lean code in generated projects for teachers and students.

Some examples are meant to be shown or checked without becoming persistent code in
generated projects:

|block|rendered book|generated project|
|---|---|---|
|`` ```lean ``|shown|normal (executable) code|
|`` ```lean -show``|hidden|normal code|
|`` ```lean +error``|shown as expected failure|wrapped in `sf_expect_failure ... end`|
|`` ```lean +error -show``(rare)|hidden|wrapped in `sf_expect_failure ... end`|
|`` ```lean -keep``|shown|wrapped in `sf_experiment ... end`|
|`` ```lean -keep -show`` (rare)|hidden|wrapped in `sf_experiment ... end`|

Do not put definitions needed later in `-keep` or `+error` blocks as they will not become
executable declarations in the generated projects, though they still get rendered in the book. 

### Quizzes

**`::::quiz … ::::`** — A multiple-choice review question: the body holds the
question prose and the options, and the answer goes in a nested **`:::answer`**.

* A *provable* answer is a plain (verbatim) ` ``` ` fence holding the Lean
  theorem — shown for reference, not re-elaborated (so it is not type-checked;
  keep it in sync with live definitions by hand).
* A deliberately *false* / unprovable claim is kept as an illustration: state it
  and leave the proof stuck with an explanatory comment (the SFL analogue of
  Rocq's `Abort`) — do **not** `sorry` it, and do **not** make it a live
  ` ```lean ` block.

`:::answer` — like the other author-only tags — is a noop today (dropped from
every build), reserved for a future answer-revealing build.  Use `:::answer`
(not `:::hide`) for a quiz's answer, so that future build can find it.

### Solution mechanisms inside `lean` blocks

Both mechanisms are elaborated by Lean at compile time (errors in the
model solution are caught during the build) and produce two source
variants — teacher (solutions visible) and student (solutions hidden)
— written to `_out/<vol>/solutions/lean/` and
`_out/<vol>/student/lean/`.

**`solution!(expr)`** — Wraps a single term or tactic sequence.
In the teacher variant the `solution!` keyword is stripped, leaving
the body.  In the student variant the entire `solution!(…)` call is
replaced with `sorry`.

```lean
def nandb (b1 : MyBool) (b2 : MyBool) : MyBool
  := solution!(match b1 with
  | .true  => notb b2
  | .false => .true)

example : nandb .true .false = .true := solution!(by rfl)
```

For tactic proofs, write `solution! <tacticSeq>` inside a `by` block.

**`-- SOLUTION … -- END SOLUTION`** — Textual block for answers that
span multiple lines and cannot be wrapped in a single expression: the
constructors of an inductive type, a multi-line proof, etc.  In the
student variant the whole region (markers included) is replaced with a
single `-- FILL IN HERE` comment at the same indentation.  In the
teacher variant the marker lines are stripped and the body is kept.

```lean
inductive Bin : Type where
-- SOLUTION
  | z  : Bin
  | b0 : Bin → Bin
  | b1 : Bin → Bin
-- END SOLUTION
```

**Convention:** prefer `solution!(…)` for a single term or tactic sequence.
Use `-- SOLUTION … -- END SOLUTION` only where the elided region stays *valid as
a comment* — the constructors of an `inductive`, or a whole top-level
declaration (the student sees `-- FILL IN HERE` in its place).

**Do not use `-- SOLUTION` for a `def` body or a proof body.**  Eliding those to
`-- FILL IN HERE` leaves an incomplete `def … :=` or an empty `by` block, which
fails to compile — and a stubbed `def` must keep its *name* defined so later code
still elaborates.  Wrap those in `solution!(…)` instead, so the student variant
becomes `:= sorry` / `by sorry`.  (Use `-- END SOLUTION` as the closer, not
`-- /SOLUTION`; `to_verso` rewrites the code-forward `-- /SOLUTION` to it, but
hand-authored Verso must use `-- END SOLUTION`.)

### Author-only annotations

These directives are invisible in all rendered outputs (HTML, TeX, and
generated `.lean` files).  They exist only in the Verso source.

Write author-facing notes as `:::` **directives** — not ` ```dev ` /
` ```instructors ` code blocks.  A directive's body is parsed as markdown, so
backtick code identifiers (`foo_bar`, `[x]`) and escape markdown-special text
just as you would in `::::full` prose; reach for an inner ` ``` ` fence only when
the body is code-dense or embeds a ` ```lean ` snippet that must not elaborate.
(`to_verso` generates these directives with the body verbatim-fenced, which is
always safe; a hand pass can un-fence and inline the markdown.)

Pick the tag by intent — `:::instructors` (instructor notes), `:::dev` (author
TODOs / review threads), `:::answer` (a quiz's answer — see **Quizzes**),
`:::hide` (genuinely hidden content).  All are noops today (dropped from every
build), so the choice is *semantic*: the name reserves each for a future build
that could treat it differently (reveal `:::answer`, show `:::instructors` to
instructors).

**`:::instructors … :::`** — Notes for instructors: pacing advice,
classroom caveats, which sections to skip for a short course, etc.

```
:::instructors
This file takes about two hours in a not-too-rushed lecture.
Assign Basics + Induction together as the first week's homework.
:::
```

**`:::dev … :::`** — Internal author commentary: unresolved design
questions, inline review threads, TODO items.  Use freely.

```
:::dev
BCP: Still not happy with this explanation — the namespace story
feels rushed.  See GitHub discussion #42.
:::
```

**`:::hide … :::`** — Marks a region hidden from all rendered outputs.
In native Verso chapters, prefer `:::dev` or `:::instructors` for
author notes.  The `:::hide` directive exists primarily for
code-forward source files where `-- HIDE … -- /HIDE` comments are
translated to `:::hide` blocks by the conversion script.

### Code-forward comments → Verso directives (`to_verso`)

(Claude-drafted; human review welcome.)  Chapters still authored as
code-forward `.lean` are converted by `scripts/to_verso.py`, which
routes their comments to the directives above:

* `-- FULL … -- /FULL` → `::::full`; `-- TERSE: /- … -/` → `:::terse`.
* Author/dev notes (`/- BCP: … -/`, `-- MWH: …`, `/- NDS'25: … -/`,
  `/- NOTATION: … -/`, …) → `:::dev`; `/- INSTRUCTORS: … -/` and
  `-- INSTRUCTORS:` → `:::instructors`; `-- HIDE … -- /HIDE` and
  `/- HIDE: … -/` → `:::hide` / `:::dev`.  The recognized tag set is
  `_DEV_TAGS` in the script — add a new author initial or keyword there
  (one place) so it routes cleanly instead of leaking into the chapter
  as prose.
* Author/dev bodies are emitted verbatim-fenced, so arbitrary markup
  inside a note is always safe.  Prose *outside* notes is real markdown:
  a fenced block must use a plain `` ``` `` fence (never a language tag
  such as `` ```coq ``), and raw object-language operator notation
  (`=[ … ]=>`, quoted notation strings) must be fenced or backticked or
  it breaks the parser.

Full authoring rules are in CLAUDE.md ("Checking to_verso outputs" /
"Writing comments that survive to_verso").

### Structural and presentation blocks

**`:::details (summary := "…") … :::`** — A collapsible disclosure
block.  The `summary` string appears as a clickable one-line teaser;
the body is hidden until the reader expands it.  Implemented with
native HTML `<details>/<summary>` (no JavaScript required).  Good for
encoding details, macro plumbing, or helper notation that is correct
but not central to the main narrative.  In generated `.lean` files the
body is emitted inlined, preceded by a short `_Details: …` comment.

**`:::ignore … :::`** — Content that appears in HTML and TeX but is
**omitted** from the generated `.lean` files.  Use it to wrap prose,
diagrams, or declarations that make sense in the book context but
would be confusing or redundant in the standalone extracted source.
Unlike the author-annotation directives, `:::ignore` content _is_
visible to students reading the HTML book.

**`:::slidebreak … :::`** — A slide-break marker with no body. In the
terse build it renders as `<div class="slide-break">` (a hook for
CSS-based slide tooling).  In full builds and in all generated `.lean`
files it emits nothing.  Written as a self-closing empty block:

```
:::slidebreak
:::
```

### BNF grammars

Use fenced `` ```bnf `` blocks to typeset object-language grammars.
Productions end with `;`; alternatives are separated by `|`.
A plain identifier is a non-terminal; a double-quoted string is a
terminal; an identifier with a **leading underscore** is a schematic
meta-variable, rendered in italics (`_x` → *x*).

```
t ::= "true" | "false" | "if" t "then" t "else" t | _x ;
T ::= "Bool" | T "->" T ;
```

HTML renders BNF as a styled table.  The saver emits the raw source
text as a `--`-comment in generated `.lean` files, so the grammar
survives in the extracted source.

The `bnf%` term-mode syntax provides the same grammar inline in a Lean
expression, for cases where the grammar is computed programmatically.

### Diagrams with ASCII fallback

For diagrams that need a text fallback in the extracted `.lean` files,
use `:::diagramWithAlt` with two children: a code block containing the
diagram (e.g., SVG), and a plain code block containing the ASCII art.
HTML renders only the diagram child; the saver emits only the ASCII
fallback wrapped in a `/-! … -/` module-doc comment.

### Verso markup for nicer HTML

Beyond the structural directives above, the Manual genre offers **inline roles**
that enrich expository prose in the HTML.  Use them where they add value (and
don't over-link — link the first substantive mention in a passage, not every
occurrence):

* `` {name}`Foo.bar` `` — a clickable identifier that hovers to show its
  type/signature and links to its definition.  Use for references to real
  declarations (defs, theorems, constructors, types) in prose.  **Caveat:** the
  name must resolve *in scope at that point in the document* — defined earlier
  and reachable (mind namespaces and forward references), or the build fails.  So
  this is a targeted, build-verified pass, not a global `` `x` ``→`` {name}`x` ``
  replace; and it applies only in visible prose (not inside `lean` blocks, quiz
  options, or dropped author notes).
* `` {lean}`expr` `` — an inline *elaborated expression* (any term or type, with
  hover types).  Use when a whole expression — not just a single name — belongs
  in prose, e.g. `` {lean}`Aexp → Nat` `` or `` {lean}`Coe Ident Aexp` ``.
* `{ref "tag"}[link text]` — a cross-reference link to a section.  Tag the target
  by putting a `%%% tag := "the-tag" %%%` block right under its heading, then
  reference it with `{ref "the-tag"}[…]`.  Use for "see the X section
  above/below" phrasings.
* `` {tactic}`simp` `` — links a tactic name to its documentation; good for prose
  that mentions tactics.
* `` {deftech}`term` `` / `` {tech}`term` `` — define a technical term (glossary
  entry + anchor) and link its later uses.  Good for a chapter's recurring
  defined terms.
* Also available: `{option}` (Lean options), `` {module}`Foo` `` (module links),
  `{margin}[…]` (sidebar notes), `{index}` / `{see}` / `{seeAlso}` (book index),
  `{citep}` / `{citet}` (bibliography).

## Porting chapters from Rocq

The `to_verso` script automates the mechanical parts of translating from Rocq to 
Verso-formatted Lean.  It leaves all the interesting bits to be translated manually.

Example usage: 
```
python3 scripts/to_verso.py old/orig-plf-files/Hoare.v HL/Hoare.lean
```

## (Temp) Porting from Rocq: comment fidelity and framing

(Claude-drafted; human review welcome.)  

When porting a Rocq
`sfdev/<vol>/<Ch>.v` to `<Ch>.lean`:

* **Preserve the whole comment layer.**  Carry over every internal
  dev/instructor note (keep the original prefix/attribution), translate
  `(* HIDE *)` content (re-marked `-- HIDE`/`/- HIDE: … -/`), and expand
  condensed prose back to the source's full wording.  Nothing is
  silently dropped.
* **Make the chapter stand on its own.**  Don't reference the porting
  process, and don't narrate "the Rocq original did X" in the
  reader-facing (`::::full`) text.  Park Rocq-specific material that has
  no Lean analogue (custom grammars, `Set Printing`, `Locate`, `Ltac`,
  dropped proof variants) in `/- Claude: … -/` dev notes as reminders
  for a future pass.  Rewrite genuine pedagogy that the source happened
  to narrate via Rocq into Lean-native `::::full` prose.

Full details (and the marker/HIDE mechanics) are in CLAUDE.md, "Porting
a chapter from Rocq: comment fidelity" and "Framing translated
comments".

## AI policy

SFL contributors may use AI tools to help create, validate, and
maintain content in this repo.  AI-generated content, especially
public-facing content such as words and proofs in book chapters,
should be carefully vetted.

Instructions for Claude live in `CLAUDE.md` (which also asks Claude to
pay attention to the conventions in this file).

Raw AI output should not be posted to GitHub or zulip without an
indication that that's what it is.  

Scripts that are mostly or wholly AI generated should be marked as
such, because these will typically be lower quality than human-created
or heavily vetted code, and people looking at them should understand
that.
