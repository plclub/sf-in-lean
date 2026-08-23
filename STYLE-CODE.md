# SF-in-Lean Code Style Guide

This file explains our conventions for how SFL is written and structured.
[CONTRIBUTING.md](CONTRIBUTING.md) covers *workflow and mechanics*;
this file is about *code style*.

## Lean Style Conventions

We generally follow the Mathlib
[style guide](https://leanprover-community.github.io/contribute/style.html)
and [naming conventions](https://leanprover-community.github.io/contribute/naming.html),
with the caveat around pedagogy in our [Guiding Philosophy](CONTRIBUTING.md#guiding-philosophy).

### Tactics and notations

A core pedagogical decision is that tactics are introduced gradually.
The table below lists the tactics first introduced in each chapter,
in chapter order. It is derived from the current sources
(tactic-position occurrences in real code, comments excluded)
and should be kept in sync as chapters are rewritten.
Do not use tactics before they are first introduced,
and do not use tactics not in this table; in particular,
`omega`, `grind`, and `aesop` may not be used in volumes `LF`, `HL`, and `TS`.

| Chapter           | Tactics first introduced |
| ----------------- | ------------------------ |
| `Basics`          | `rfl`, `intro`, `rewrite`, `cases`, `exact` |
| `Induction`       | `induction`, `have`, `rw`, `<;>` |
| `UsingLean`       | `dsimp`, `calc`, `exact?`, `rw?` |
| `Lists`           | *(none new)* |
| `Poly`            | *(none new)* |
| `Tactics`         | `apply` (and `apply ... at`), `replace`, `specialize`, `symm`, `injection`, `injections`, `congr`, `assumption`, `contradiction`, `induction ... generalizing ...`, `unfold`, `cases ... : ...`, `split` |
| `Logic`           | `constructor`, `obtain`, `left`, `right`, `ext`, `by_cases`, `exfalso` |
| `IndProp`         | `subst` |
| `Automation`      | `lia`, `try`, `repeat`, `specialize`, `trivial`, `simp`, `generalize` |
| `Typeclasses`     | `decide` |
| `Slang`           | `fun_induction`, `simp_all` |
| `HL` chapters     | *(none new)* |
| `HL/Hoare`        | `show` (in a solution only), `apply_rules` |

Additional notation beyond the `Basics` is also introduced gradually alongside
the tactics. The table below similarly lists new notation, which should also be
kept in sync.

| Chapter   | Notations first introduced |
| --------- | -------------------------- |
| `Lists`   | `structure`, `⟨...⟩` anonymous constructors, `.` accessors, `bif` |
| `Poly`    | `{...}` implicit arguments, `_` holes, `@` explicit application |
| `Tactics` | `let ⟨...⟩ := ...` |
| `Logic`   | rewriting by `↔` |

#### Notes

- `omega` is being phased out in favor of `lia`.
- `IndPropRegexp` has been folded into `Automation`.
- `Maps` has been folded into `Typeclasses`; the total- and partial-map
  development now lives there. (`LF/Maps.lean` has been deleted; Rocq's `Maps.v`
  remains the source for the prose.)
- Candidate tactics still to be placed include
  `show`, `rename_i`, `revert`, `suffices`, `tauto`.
- `grind` and `aesop` are deferred to a later volume, following
  FPiL's caution that `grind` is overwhelming for beginners.

### Syntactic considerations

#### Case analyses and induction

Prefer `cases ... with` and `induction ... with` over `case` or `·` goal
selectors, with each alternative on its own unindented line.

```lean
cases b with
| true  => ...
| false => ...
```

Keep short branch bodies inline.

```lean
cases b, c with
| true, false => rfl
| false, _ => simp
```

Optionally, align patterns across alternatives.

```lean
cases b, c with
| true,  _ => rfl
| false, _ => simp
```

For multiline branch bodies, don't pad the `=>`, and indent the body to align
with the alternative name.

```lean
cases b with
| true =>
  simp
  exact h
| false =>
  rw [h]
  exact hf
```

#### Names and namespaces

Follow the Lean library's naming conventions:

- Theorems and proof names use `snake_case`, e.g. `add_swap`, `rev_app_distr`
- Types and propositions (including definitions returning `Prop`) use
  `PascalCase`, e.g. `Aexp`, `IsValue`
- Other values and functions use `camelCase`, e.g. `isEven`, `doubleBin`

Also follow Lean's variable naming conventions, using primes `'`, `''`, ...
and numerical subscripts `₁`, `₂`, ... as needed:

- `α`, `β`, `γ`, ... for type variables
- `a`, `b`, `c`, ... for propositions
- `p`, `q`, `r`, ... for predicates (functions into `Prop`)
- `m`, `n`, `k`, ... for natural numbers
- `h` for hypotheses
- `f` and `g` for functions
- `l` for lists

Almost always, definitions and theorems relating to a type belong in a
namespace with the same name as the type. Define the type first, then open its
companion namespace and use bare member names inside it:

```lean
inductive Tm where
  ...

namespace Tm

def IsValue (t : Tm) : Prop := ...

theorem value_is_nf (t : Tm) (h : IsValue t) : IsNormalForm t := by
  ...

end Tm
```

#### Theorem types and arguments

Put a theorem's ordinary arguments before the colon rather than introducing them
with `∀` in its result. Likewise, when a proof would begin by introducing a
hypothesis, put a named hypothesis before the colon:

```lean
theorem foo {α : Type} (x : α) (h : P x) : Q x := by
  ...
```

rather than:

```lean
theorem foo : ∀ {α : Type} (x : α), P x → Q x := by
  intro h
  ...
```

This is not an absolute rule: keep quantifiers or implications in the resulting
type when they are naturally part of the theorem's conclusion, when partial
application of the theorem is useful, or the declaration is defined by `|`
pattern matching.

In `Basics`, explicit `∀` and `intro` may be used when they are being introduced.
After declaration arguments have been explained in section
"Displaying Theorem Statements", use the idiomatic declaration argument form
consistently.

Declaration types that overflow onto subsequent lines take an extra level of
indentation relative to the declaration body:

```lean
theorem map_cons {α β : Type} {f : α → β}
    {head : α} {tail : List α} :
    map f (head :: tail) = f head :: map f tail := by
  rfl
```

#### Type annotations

Always give binders explicit type annotations, even when Lean can infer them.
For example, write `(n : Nat)`, `{α : Type}`, and `(h : P)` rather than bare
`n`, `{α}`, or `h`.

Type parameters should normally be implicit when later arguments determine them:

```lean
theorem isNil_cons {α : Type} (x : α) (xs : List α) :
    isNil (x :: xs) = False := by
  ...
```

#### Implicit arguments

For small equational lemmas for `rw` or `simp`, make arguments implicit when the
displayed equation determines them. This follows the style of Lean's list lemmas.
For example, `map_cons` can be used simply as `rw [map_cons]`:

```lean
theorem map_cons {α β : Type} {f : α → β}
    {head : α} {tail : List α} :
    map f (head :: tail) = f head :: map f tail := by
  ...
```

However, do _not_ make a theorem's main inputs implicit merely because
unification could infer them from the conclusion. Keep the principal function,
collection, point, or other subject explicit when callers are likely to apply
the theorem directly. For example:

```lean
theorem foldMap_correct {α β : Type}
    (f : α → β) (l : List α) :
    foldMap f l = map f l := by
  ...

theorem uncurry_curry {α β γ : Type}
    (f : α → β → γ) (x : α) (y : β) :
    prodCurry (prodUncurry f) x y = f x y := by
  ...
```

If those arguments were implicit, callers would need
named arguments such as `(f := f)` and `(l := l)`.

An index may be implicit when treating it as inferred data is natural for the
theorem's use:

```lean
theorem isEven_iff_Even {n : Nat} :
    isEven n = true ↔ Even n := by
  ...
```

### Incomplete code, expected errors, and diagnostics

Use `sorry` to admit a declaration, `+error` to show code that Lean rejects,
`-keep` to keep a block from changing the later environment,
` ```leanOutput ` when the output itself is being checked,
and `#guard_msgs` for internal checks that are not student-facing.

#### `sorry`

Use `sorry` when an unfinished declaration must remain available to later code,
as with an exercise scaffold or a theorem used below. Do _not_ normally wrap it
in `#guard_msgs`, as the generic warning is not what we are testing.

````lean
```lean
theorem pumping ... : ... := by
  sorry
```
````

#### `+error`

Use `+error` for stuck proofs, failed tactics, incomplete matches, type errors,
and other code that Lean should reject.

If the point is simply that `rfl` fails, use an expected-error block rather
than checking its diagnostic:

````lean
```lean +error
example (a b : Nat) : a + b = b + a := by
  -- `rfl` doesn't work here!
  rfl
```
````

Likewise, leave a one-off stuck proof unfinished instead of closing it with `sorry`:

````lean
```lean +error
example (c n : Nat) :
    myRepeat n c ++ myRepeat n c = myRepeat n (c + c) := by
  induction c with
  ...
  | succ c' ih =>
    ...
    -- Now we seem to be stuck.
```
````

#### `-keep`

Use `-keep` for successful code whose declarations or other effects should not
reach later blocks. This instance, for example, is deliberately misleading:

````lean
```lean -keep
instance : HasOne Nat where
  one := 2
```
````

Combine `-keep` with `+error` when a failed declaration would otherwise reserve
its name:

````lean
```lean +error -keep
def x : Nat := "str"
```
````

Without `-keep`, `x` cannot be redefined later in the chapter.

#### ` ```leanOutput `

Use `(name := <identifier>)` with a later `leanOutput` block to check that the
Lean block indeed produced the expected output, e.g.

````
```lean (name := example)
#check Bool.true
```

```leanOutput example
Bool.true : Bool
```
````

Use `leanOutput` with named `+error` blocks to check for the expected error
message, e.g.

````
```lean +error (name := test)
def incomplete (n : Nat) : Nat :=
    match n
```

```leanOutput test
unexpected end of input; expected 'with'
```
````

#### `#guard_msgs`

Use `#guard_msgs` for testing diagnostic messages that are not intended to be student-facing.
For example, `Imp` checks its custom delaborator this way:

````lean
```lean
/-- info: aexp {3 + X * 2} : Aexp -/
#guard_msgs in
#check aexp {3 + (X * 2)}
```
````

### Notation and simplification

When notation is implemented via typeclass instances, `dsimp [add]` does *not*
resolve the instance down to the underlying definition, and `simp` is often too
powerful for teaching. Instead, rewrite explicitly by characterizing lemmas when
possible, e.g. `n + (m + 1) = n + m + 1` or `(h :: t) ++ l = h :: t ++ l`.

When using `simp` with declarations (only in or after `Automation.lean`),
tag theorems with `@[simp]`, not definitions:

```lean
/- Do not use @[simp] here! -/
def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => succ (add n m')

@[simp] /- Use it here instead... -/
theorem add_zero : ∀ n : Nat, n + zero = n := by
  intro n
  rfl

@[simp] /- ... and here. -/
theorem add_succ : ∀ n m : Nat, n + (succ m) = succ (n + m) := by
  intro n m
  rfl
```

### Unfolding

Inside a definition's own library, it's fine to unfold and simplify through
definitions; when *using* that code, do not "peek through the interface."

### Definitions vs. abbreviations

Abbreviations let syntax-based tactics like `rw` and `simp` to see the underlying term implicitly.
Abbreviations should never be used for functions; use definitions plus characterizing lemmas instead.
To encapsulate a type with an API boundary, use a definition rather than an abbreviation.
However, abbreviations can be used to create type aliases that do not intend to encapsulate an inner type.

As an example, the `DefDemoGood` is idiomatic, whereas the `AbbrevDemoBad` is not:

```lean
namespace AbbrevDemoBad

abbrev Bag := List Nat
abbrev Bag.empty : Bag := []
theorem Bag.foo : empty ++ empty = empty := by
  rw [List.append_nil]

end AbbrevDemoBad

namespace DefDemoGood

def Bag := List Nat
deriving Append

def Bag.empty : Bag := []
theorem Bag.empty_def : Bag.empty = [] := rfl
theorem Bag.append_nil (s : Bag) : s ++ empty = s := List.append_nil s
theorem Bag.foo : empty ++ empty = empty := by
  rw [Bag.append_nil]

end DefDemoGood
```

### Theorems vs. examples

Prefer `example : ...` over a named `theorem foo : ...` for throwaway
illustrations (tactic demos, "silly" lemmas, etc.) that are never referenced
later. Reserve names for results used elsewhere or for graded exercises.

## Verso Markup Conventions

Each chapter is a single `.lean` file in its volume directory.
Sections within a chapter use standard Markdown headings (`#`, `##`,
`###`, …) relative to the `#doc` level.

Unfenced text is parsed as Markdown and rendered with formatting,
while text in code fences ` ``` ` is parsed as code.
Verso directives fenced by `:::` control when and how the contained Markdown is
rendered, and is also used for tooling. The subsections below list the various
types of code and directive blocks that are used.

### `lean` blocks

Fenced `lean` blocks in a file are type checked in the order they appear as if
the file contained only those Lean blocks, as is usual in literate programming.
They are rendered in the HTML as code blocks with hoverable doc comments and
expandable proof states in tactics.

These blocks may take a `(name := <identifier>)` option for use by a later
`leanOutput` block. They may also take additional boolean options:

| Option | HTML book | Extracted Lean | Usage |
| ------ | --------- | -------------- | ----- |
| `-show` | not rendered | normal code | For hiding unexplained technical code from the book narrative |
| `+error` | rendered as code block with error | code in `sf_expect_failure` block | For demonstrating expected errors while supressing error diagnostics |
| `-keep` | rendered as code block | code in `sf_experiment` block | For successfully checking code without affecting later blocks |

Combine `+error` and `-keep` to produce a block that is expected to fail,
and whose declarations don't affect later blocks.
Combine `+error` and `(name := <identifier>)` to produce a block whose error
message gets checked by ` ```leanOutput <identifier> `.
See the previous sections for more detailed usage guidelines.

### BNF grammar blocks

Fenced `bnf` blocks render as typeset object-language grammars.
Productions begin with a metavariable and `::=`, followed by alternatives
separated by `|`, and end with `;`.
Plain identifiers are nonterminals, while quoted strings are terminals.
Each variant may have a string comment enclosed by parentheses.
For instance, the grammar

````
```bnf
t ::= x ("variable")
    | "λ" x ":" T "." t ("abstraction")
    | t t ("application") ;
```
````

is rendered as comments in the extracted Lean

```lean
-- t ::= x                     (variable)
--     | λ x : T . t           (abstraction)
--     | t t                   (application)
```

and as a similar table in the HTML.

### Display blocks

Fenced `display` blocks are not type checked, and are rendered verbatim in the
HTML as plain code blocks and in the extracted Lean as indented comments.

Fenced `displayMath` blocks contain TeX math equations;
they are rendered in the HTML as typeset math using KaTeX,
and in the extracted Lean as verbatim indented comments.
Each line is a separate equation.

### Inline roles

Inline roles of the form `{<role>}[<text>]` provide intertext linking and
hovertext in the HTML. If the text is a single piece of content,
such as an inline code snippet or an italicized phrase,
the brackets may be omitted.

* `{ref <string>}[<text>]`:
  a cross-reference to the section in the corresponding `<string>.lean` file
* `` {lean}`<expression>` ``:
  typechecked Lean code with usual hover and navigation behavior
* `` {name}`<identifier>` ``:
  like `{lean}`, but a single identifier that navigates to its declaration
* `` {tactic}`<tactic>` ``:
  a single syntax highlighted tactic with no navigation or hover
* `{deftech}_<text>_`, `{tech}_<text>_`:
  a defined technical term appearing in the glossary;
  a link that navigates to the defining instance of that term
* `{citep}[]`/`{citet}[]`: a parenthetical/textual citation

### Directive fence depth

Verso uses colon depth on directives the same way Markdown uses backtick depth
for nesting. A directive requires at least three colons (`:::`);
and may be nested within other directives with strictly more colons.
For instance,

````lean
::::exercise
Prove that {lean}`1 = 1`.

:::solution
```lean
theorem one_equals_one : 1 = 1 := rfl
```
:::
::::
````

is an exercise that contains a solution.

### Build variants and prose directives

Every chapter is compiled once but rendered in four variants:

- **student**: full prose, solutions elided
- **solutions**: full prose, solutions shown
- **grading**: full prose, solutions shown, with grading attributes
- **terse**: abridged prose for live-coding / lecturing

A number of directives control what prose appears in which variants.
There is no difference between how the solutions and the grading variants are
rendered in the HTML, so what applies to the solutions variant below
also applies to the grading variant.

#### `:::full`

_Rendered in student and solutions variants._

The main narrative that students encounter in the book, which is hidden in the terse variant to keep lecture slides uncluttered.

#### `:::terse`

_Rendered in terse variant only._

Typically a one- or two-sentence cue for a live-coding presenter.
The standard pattern at each presentation point is a `:::terse` cue, followed
by the `:::full` narrative prose it stands in for, followed by a shared
` ```lean` code block.

#### `:::solution`

_Rendered in solutions variant only._

Worked prose answers to open-ended exercises: discussions, design rationale,
or illustrative code that is not intended to compile.
(For _compilable_ answers inside `lean` blocks,
use `solution!` as described above.)

#### `:::suppressPreviousHeaderWhenTerse`

_Rendered in student and solutions variants._

Marks the section heading immediately above as full-only for reading.
Headings cannot be nested inside `:::full` directives,
since headings create document sections while directives hold blocks,
so this is a workaround.
An entire section can be marked as full-only using a heading followed by
this directive, followed by a full directive, e.g.

```lean
# Additional Exercises

:::suppressPreviousHeaderWhenTerse
:::

:::full
This is an exercise.
:::
```

### Exercise and grading directives

#### `:::exercise`

_Rendered in all variants._

An exercise block rendered as `Exercise ★ (foo)` in the HTML
and as a comment `-- ### Exercise (1 star): foo ⭐` in the extracted Lean files.
It takes the following options:

* `(rating := <number>)` (required): difficulty from 1 (easy) to 5 (hard); a
  rating outside that range is a build error
* `(name := <identifier>)` (required): name used in headings and cross-references
* `(level := <identifier>)` (optional): additional difficulty warning (currently only `Advanced`)
* `(optional := <identifier>)` (optional): `Yes` marks an exercise the reader
  may skip; the default is `No`
* `(manual := <boolean>)` (optional): marks the exercise for manual grading

#### `:::gradeTheorem <number> <identifier>...`, `:::grade`

_Not rendered._

`gradetheorem` is an autograding specification for an exercise with
a point value and one or more declarations, while `grade` is a manual
grading specification. The manual specification has the following format:

````
:::grade
```
GRADE_MANUAL <number>: <identifier>...
```
:::
````

Every exercise **must** contain a nested grading directive.
The usual structure is an exercise statement, followed by a code block,
followed by a grading directive, e.g.

````
::::exercise (rating := 1) (name := "mul_simpl_rules")
Remove {tactic}`sorry` and prove the simplification rules for {name}`mul` below.

```lean
theorem mul_zero : ∀ n : Nat, n * zero = zero := by
  solution!
    ...

theorem mul_succ : ∀ n m : Nat, n * (succ m) = (n * m) + n := by
  solution!
    ...
```

:::gradeTheorem "0.5" mul_zero mul_succ
:::
::::
````

In the grading Lean variant, autograding specifications are extracted to
`attribute [autogradedProof <number>] <identifier>...`.

### Exercise solution mechanisms

#### `solution!`, `workinclass!`, `suggested!`

There are several tacticals that replace a term or a sequence of tactics
depending on the variant. A solution term is placed within parentheses.

````
```lean
def nandb (b1 : Bool) (b2 : Bool) : Bool
  := solution!(match b1 with
  | .true  => notb b2
  | .false => .true)

```
````

A solution proof is placed in an indented block of tactics.

````
```lean
theorem false_or (b : Bool) : (.false || b) = b := by
  solution!
    rfl
```
````

The tactical and its term or proof is replaced either by `sorry` or by
the term or proof itself, dedented to sit at the tactical's own column. The
replacements are summarized below.

| Tactical       | `solutions` | `student` | `terse`     | Usage |
| -------------- | ----------- | --------- | ----------- | ----- |
| `solution!`    | shown       | `sorry`   | `sorry`     | For homework exercises |
| `workinclass!` | shown       | shown     | `sorry`     | For work in class |
| `suggested!`   | shown       | `sorry` with proof in comment | shown | For exercises with a suggested proof to modify |

#### `-- SOLUTION`

Entire lines of code can also be replaced by beginning with a `-- SOLUTION`
comment and ending with a `-- END SOLUTION` comment. The comments are stripped
in the solutions variant, while all lines are replaced by a `-- FILL IN HERE`
comment in the student and terse variants. Use this only when omitting the lines entirely still compiles, such as for the constructors of an inductive type.

````
```lean
inductive Bin : Type where
-- SOLUTION
  | z  : Bin
  | b0 : Bin → Bin
  | b1 : Bin → Bin
-- END SOLUTION
```
````

### Quiz and solution directives

#### `:::quiz`, `:::quizSolution`

_Rendered in all variants._

A multiple-choice quiz block, which _may_ contain a nested solution block.
The solutions are hidden behind a "Show solution" button in the HTML,
and not rendered in the extracted Lean files.
Quizzes are formatted as follows.

````
::::quiz
How do you prove this?

```display
example : 1 = 1
```

(A) You can't
(B) I don't know how
(C) {tactic}`rfl`

:::quizSolution
```lean
example : 1 = 1 := by rfl
```
:::
::::
````

### Internal commentary directives

#### `:::dev`

A developer note that may take the following options:

* `<string>`: the author of the note
* `NOW` | `BeforeNextRelease` | `PotentialImprovement`: an urgency level
* `(year := <number>)`: the year of authorship

Authors should be in the form `Full Name (github-handle)`.
Notes marked as `PotentialImprovement` are not rendered;
unmarked notes or those marked as `NOW` or `BeforeNextRelease` are rendered
in all variants, appearing as yellow boxes labelled with "Note to developers
(Author)" in the HTML and as comments in the extracted Lean.

#### `:::instructors`

_Not rendered._

An instructor note for pacing advice, classroom caveats,
which sections to skip for a short course, etc.

### Structural and presentation directives

#### `:::hide`

_Not rendered._

Prefer to use `:::dev` or `:::instructor` with an explanation of why
this content is hidden.

#### `:::ignore`

_Rendered in all variants but **not** in the extracted Lean._

Used to wrap prose, diagrams, or declarations that make sense in the
book context but would be confusing or redundant in the extracted Lean.

#### `:::slidebreak`

_Rendered (invisibly) in terse variant only._

In the HTML, this renders as `<div class="slide-break"></div>`
as a hook for CSS-based slide tooling.
This directive is always written as a self-closing empty block.

```
:::slidebreak
:::
```

#### `:::details "<summary>"`

_Rendered in all variants._

In the HTML, this is rendered as a collapsible `<details>` element
with the given `<summary>` text, or "Details" when it is omitted.
In the extracted Lean, this is rendered preceded by a
`-- THESE DETAILS CAN BE SKIPPED: <summary>` comment and followed by a
`-- END DETAILS` comment.
Good for encoding details, macro plumbing, or helper notation that is correct
but not central to the main narrative.

#### `:::diagramWithAlt`

_Rendered in all variants._

A diagram with two required blocks:
a `diagram` code block containing Lean code for an Illuminate diagram,
rendered in the HTML, and a verbatim code block containing the ASCII fallback,
rendered as a comment in the extracted Lean.

The `diagram` code block takes two options:

* `(cssWidth := <length>)` | `(cssScale := <number>)`:
  an explicit CSS length or scaling factor for HTML rendering;
  defaults to `(cssScale := 1)`
* `(texWidth := <length>)`:
  an explicit TeX length for PDF rendering;
  defaults to `(texWidth := "\textwidth")`

The following is an example from `TS.Stlc.lean`:

````
:::diagramWithAlt
```diagram (cssWidth := "28em") (texWidth := "20em")
SFLMeta.Diagrams.lambdaCubeDiagram
```

```
                         Calculus of Constructions
 type operators +--------+
               /|       /|
              / |      / |
polymorphism +--------+  |
             |  |     |  |
             |  +-----|--+
             | /      | /
             |/       |/
             +--------+ dependent types
          STLC
```
:::
````

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
