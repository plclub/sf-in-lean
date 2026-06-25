# SF-in-Lean Style Guide

This file records the conventions and the most important decisions we have made
about writing *Software Foundations in Lean* (SFL): Lean coding style, Verso
markup, comment conventions, the order in which tactics are introduced, etc.

## Guiding Philosophy

1. SFL aims for exceptional pedagogy and presentational polish.
2. SFL is _exercise-based_: Every important concept comes with hands-on exercises to reinforce it, with solutions.
3. SFL strives to teach _proof engineering_, which involves
   constructing readable and maintainable formalizations and proofs.
    - Corollary: Students should understand particular tactics and what 
      they do, starting small and growing in sophistication.
    - Corollary: Definitions and proofs are written in idiomatic Lean 
      (mostly the way it is for engineering/maintainability reasons), 
      only deviating (temporarily) for strong pedagogical reasons.
4. SFL developments connect with those in
   [CSLib](https://github.com/leanprover/cslib/tree/main) where
   possible. Some of SFL's languages, semantics, etc. might eventually
   find a place in CSLib. 

## Collaboration Conventions

We are still figuring out good mechanisms for coordinating who is
working on what and avoiding stepping on each other's work. For the
moment, use the Zulip *Lock Thread* channel to announce where you are
working and coordinate with others that may be touching the same
files. Make PRs frequently so that your local changes get folded back
into the main branch as quickly as possible.

For discussions, we've been using a combination of tools:

- If you want to start a discussion about an issue of general
  interest, post on the [SFL contributors Zulip
  channel](https://leanprover.zulipchat.com/#narrow/channel/607217-lean-software-foundations-contributors).  

- If you want someone to think about your comment at some point when
  they have some particular part of the material paged in, put it
  directly in the .lean file, either in a comment (if it's a plain
  .lean file) or in a `:::dev` block (if it's been versified), marked
  with your initials.

- We are still exploring how best to use GitHub issues for SFL.

We prefer _not_ holding discussions in annotations on PRs, because
they tend to either get lost when the PR is merged or delay merging.
Putting very local or short-term comments in this medium is fine -- or
you can just make the change by directly editing the PR, if you think
it's clear.

## Git-fu

We use git and github, with some simple conventions:

* The `main` branch must always build. 
* Never commit directly to `main`. Instead, branch, edit, make a PR,
  wait for CI to go green (and for others to review, if appropriate),
  then merge.  
* After your PR is merged, delete the branch to keep the repo tidy.
* Don't merge a red PR.

Our CI uses a small GitHub Actions workflow:
[.github/workflows/ci.yml](.github/workflows/ci.yml). 
It runs `make` on every pull request and on every push to `main`. 

## Organization and Make-fu

Each volume gets its own top-level directory (LF, HL, etc.).  

Within that directory, each chapter gets a .lean file, in Verso format.

Running `make` at the top level produces, for each volume, 
three different ready-for-distribution outputs 
in a temporary top-level `_out` directory, each with both .lean and .html variants.
  - **student**   (full prose, solutions elided)
  - **solutions** (full prose, solutions shown)
  - **terse**     (little prose, no solutions, workinclass elided;
                   for lecturing)

To build everything and preview it locally, do `make serve`, 
then visit http://localhost:8000 
(`make serve` builds stuff then serves `_out/` on port 8000).

## Status; plain lean vs. verso files (temporary)

At the moment, most of the files in Logical Foundations have been
converted to regular lean files.  (Programming Language Foundations
remains to be translated.)  The .lean files are currently in regular
Lean syntax, but we want them to be formatted as Verso files
("documentation first") and are working on translating them one by
one.  

Benjamin is the only person that needs to worry about the details
here: Everyone else can just work on a given .lean file in whatever
format it exists in at the moment.  In particular, no one except
Benjamin should ever need to run the `to_verso.py` script.

## Lean Style

**BCP: This section needs reviewed.**

We generally follow the [Mathlib style
guide](https://leanprover-community.github.io/contribute/style.html)
and use the Lean linter by default. 

SFL-specific conventions:

* **Structured `cases`/`induction`.** Prefer
  ```lean
  cases b
  case true  => …
  case false => …
  ```
  over `cases b with | …` *and* over the bare `·` goal selector — i.e. prefer
  `cases h; case …` / `induction h; case …`. Select cases with named `case`s,
  un-indented and without a leading `.`, and **align the `=>`** as above.
  Use the `·` selector only when the goal names are not meaningful.
  
* **`rewrite` before `rw`** (see next section).

* **Explicit rewrites over `dsimp`/`simp` through notation** (see "Notation and
  simplification").

* **`sorry` placeholders are checked, not silent.** Where a `sorry` appears
  (incomplete proof, exercise scaffold), wrap it so the warning is asserted:
  ```lean
  /-- warning: declaration uses `sorry` -/
  #guard_msgs in
  example : … := sorry
  ```

* **Aborted/abandoned lemmas** become unnamed `example`s closed with `sorry`
  (the SFL analogue of Rocq's `Abort`).

* **Library vs. client code.** Inside a definition's own library it is fine to
  unfold and simplify through definitions; *using* that code, do not "peek
  through the interface."

### `rewrite` vs `rw`

`rw [h]` is roughly `rewrite [h]; rfl`, which is too strong for the
first chapters: it hides the closing `rfl` and makes proofs step
confusingly (the goal vanishes when you step past the final `]`).
Decision (JC): **use `rewrite` the first time, keep using it
explicitly in the early arithmetic proofs, then introduce `rw` in
`Induction` and use `rw` predominantly from there on.**

### Notation and simplification

When notation is implemented via typeclass instances, `dsimp [add]` /
`dsimp [app]` do *not* resolve the instance down to the underlying definition,
and `simp` is often too powerful for teaching. So **rewrite explicitly by
equational lemmas** instead — e.g. `n + (m + 1) = n + m + 1` or
`(h :: t) ++ l = h :: t ++ l` — rather than reaching for `dsimp`/`simp`.

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

In practice: `::::full`, `::::terse`, `::::exercise`, and `::::solution`
almost always use four colons because they commonly nest `:::grade`,
`:::instructors`, or similar leaf blocks inside them.  Author-annotation
directives (`:::dev`, `:::instructors`, `:::hide`, `:::grade`) are always
leaves and always use three colons.

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
Use this for worked prose answers to open-ended exercises: discussions,
design rationale, or illustrative code that is not intended to compile.
(For _compilable_ answers inside `lean` blocks, use `solution!` or
`-- SOLUTION`, described below.)

The standard pattern at each presentation point is a `:::terse` cue
followed by a `::::full` narrative block followed by a shared `lean`
code block.  All three builds see the code; only the relevant prose
builds see each prose variant.

### Exercise and grading infrastructure

**`::::exercise (rating := N) (name := "foo") … ::::`** — Marks an
exercise block.  `rating` is a difficulty from 1 (easy) to 5 (hard);
`name` is a short identifier used in headings and cross-references.
Renders as a styled box with stars in HTML; produces a
`### Exercise (N stars): foo` module-doc heading in the extracted `.lean`
files.  Should always contain a nested `:::grade` block.

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

**`:::grade … :::`** — Grading spec, always nested inside `::::exercise`.
Contains one or more `GRADE_THEOREM <pts>: <name>` or
`GRADE_MANUAL <pts>: <name>` lines for autograding scripts.
Currently a noop in all rendered outputs (body discarded at elaboration);
the spec survives verbatim in the Verso source for tooling.

### Solution mechanisms inside `lean` blocks

Both mechanisms are elaborated by Lean at compile time (errors in the
model solution are caught during the build) and produce two source
variants — teacher (solutions visible) and student (solutions hidden) —
written to `_out/<vol>/solutions/lean/` and `_out/<vol>/student/lean/`.

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

**Convention:** prefer `solution!(…)` for single-term / single-tactic
answers; use `-- SOLUTION` blocks for multi-line answers.

### Author-only annotations

These directives are invisible in all rendered outputs (HTML, TeX, and
generated `.lean` files).  They exist only in the Verso source.

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
author notes.  The `:::hide` directive exists primarily for code-forward
source files where `-- HIDE … -- /HIDE` comments are translated to
`:::hide` blocks by the conversion script.

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

**`:::slidebreak … :::`** — A slide-break marker with no body.
In the terse build it renders as `<div class="slide-break">` (a hook
for CSS-based slide tooling).  In full builds and in all generated
`.lean` files it emits nothing.  Written as a self-closing empty block:

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


## Tactics: order of introduction

A core pedagogical decision is that tactics are introduced gradually. The table
below lists the tactics **first introduced** in each chapter, in chapter order.
It is derived from the current sources (tactic-position occurrences in real
code, comments excluded) and should be kept in sync as chapters are rewritten;
chapters past `Logic` are still in flux.

| Chapter           | Tactics first introduced |
|-------------------|--------------------------|
| `Basics`          | `rfl`, `intro`, `rewrite`, `cases`, `exact` |
| `Induction`       | `induction`, `have`, `rw`, `calc`, `generalize` |
| `Lists`           | `dsimp` |
| `Poly`            | *(none new)* |
| `Tactics`         | `intros`, `apply` (and `apply … at`), `replace`, `symm`, `injection`, `injections`, `congr`, `assumption`, `contradiction`, `unfold`, `split` |
| `Logic`           | `constructor`, `obtain`, `left`, `right`, `ext`, `by_cases`, `exfalso` |
| `IndProp`         | `simp`, `rcases`, `subst`, `omega` |
| `Maps`            | *(none new)* |
| `IndPropRegexp`   | `specialize`, `trivial` |
| `UsingLean`       | *(none new)* |

Related notation introduced alongside tactics: anonymous constructor `⟨…⟩`
(`Lists`); destructuring `let ⟨…⟩ := …` and `cases h : …`,
`induction … generalizing …` (`Tactics`); projection/`Iff` syntax `.left`,
`.right`, `.mp`, `.mpr`, and rewriting by an `↔` (`Logic`).

**Tactics deliberately deferred / under discussion** (per FPiL's caution that
`grind` is overwhelming for beginners): candidates still to be placed include
`show`, `rename_i`, `revert`, `subst`, `suffices`. Powerful automation
(`simp` heavy use, `tauto`, `omega`, `decide`) is concentrated in a future
**Automation** chapter; `grind`, `aesop`, and `try` are deferred to a later
volume. The `RegExp` development moves out of `IndProp` into that Automation
chapter.

## AI policy

SFL contributors may use AI tools to help create, validate, and
maintain content in this repo.  AI-generated content, especially
public-facing content such as words and proofs in book chapters,
should be carefully vetted.

Instructions for Claude live in `CLAUDE.md` (which also asks Claude to
pay attention to the conventions in this file).