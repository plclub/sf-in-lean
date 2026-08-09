# SF-in-Lean Writing Style Advice

This file gives some advice on writing new material for SFL. It is based on general experience and in particular on pedagogy and polishing improvements made in pull requests to SFL.

**Imagine your audience.** What do students know, prior to this course? Probably your audience is diverse, and they have taken different paths to get here. What do they know _so far_ from this course, at the point you are writing? Leverage concepts they know and don't use terms or concepts they don't know. Don't re-explain things they know well, but reminders of a non-recent concept or term are good; readers will forget things you told them a while back. 

As an example: `LF/Typeclasses.lean` does this in one sentence: it reminds readers that "Chapter Poly introduced parametric polymorphism, declaring a type variable with no constraint on it," before immediately moving past it to what's new.

**Context, Gap, Solution (CGS).** Readers want to know _why_ they are reading or doing something. They will suspend impatience temporarily, but not for long. A good structure is three parts: what do we want to do, what is stopping us from doing it, and what do we do about that? 

Common anti-patterns that are close to this structure but not quite it:
1. The problem is stated but is too big. Then it's a long path to get to the solution without it being obvious why that's the right path. To address this, you want to break the big problem down into smaller problems, each of which has the three-part structure.
2. The solution is not an obvious match to the problem. For example, the solution might appear to be more than is demanded by the problem — why not something simpler? Either the solution should be simpler, or some explanation is needed.

The "Why We Need Typeclasses" section of `LF/Typeclasses.lean` is close to a model of this: it poses a concrete problem (a `Nat`-only `elem` function that we want to generalize), tries the obvious generalization and watches it fail with a puzzling error, tries a tedious explicit-parameter workaround, and only then introduces typeclasses as the solution — each step small enough to motivate the next, rather than one big "here's typeclasses."

**Start from something specific that the reader knows; work to something general.** This advice brings together the two bits of advice above. It has the benefit that you begin "on the same page" with your reader, and then you make small deltas that are easy to be confident about before making bigger leaps. Almost certainly you should follow this advice by using _good examples_, from small/simple to more general. `LF/Poly.lean` does this well: it starts from the concrete `BoolList` type, explicitly compares it back to the `Natlist` from the previous chapter, and only then generalizes to the polymorphic `MyList α`.

**Minimize complexity.** This may seem obvious, but the general principle has many specific implications. For SFL, one big risk is jumping to "real Lean" too quickly, at a cost to good pedagogy. Always ask yourself the high-level question: _How can I make this simpler?_ 

Manifestations:
1. When explaining by example, it's good to reuse examples rather than introducing new ones. Don't use one large and complex example when two simple ones would do. (`LF/Typeclasses.lean` motivates `MyGetElem` by calling back to `BEq` and `EmptyCollection`, examples the reader has already seen earlier in the same chapter, rather than reaching for a new analogy.)
2. A multi-step solution to a problem is often preferable over a one-step solution when concerns can be separated. Ask yourself: can I break this solution into smaller, simpler parts?
3. Avoid giving a full, expert-level solution if it solves problems you can't or don't want to explain right now. It's okay to sometimes ask people to suspend disbelief, but we'd generally prefer to avoid it.

**Don't forget exercises.** SFL's signature style is that it offers exercises for each interesting concept. Just as we develop examples for explanation purposes, we need exercises for readers to test their understanding. Consider making an explanation+example into an explanation+exercise. `LF/IndProp.lean` does this directly: right after explaining induction-on-evidence, it says "The following exercises provide simpler examples of this technique, to help you familiarize yourself with it," handing the technique straight to the reader.

**Cutting is good.** As material evolves, it tends to grow. The temptation is not to get rid of anything, ever. Ask yourself, considering all of the above: "Does this serve my goal? Does my audience need this?" If the answer is "not everybody, but some might benefit," you could either
1. put it in a hidden-by-default `:::details` block, if it's relatively short (1-2 pages in the HTML), or
2. add an appendix that dives into the details.

(But don't waste too much time on this while we are still building out the core content.) SFL doesn't yet have a `:::details` block in active use, but chapters already reach for the same idea informally with `(Optional)` and `Aside:` section headers — e.g. "More on Notation (Optional)" and "Structural Recursion (Optional)" in `LF/Basics.lean` — which are good candidates to convert once `:::details` sees wider adoption.
:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement
This paragraph might go stale quickly.
:::

---

## Examples 

The pairs below are real polishing diffs pulled from the repo's git history, each illustrating one of the principles above. *(This section was compiled by Claude, from `git log`/`git show` on `LF/Basics.lean`, `LF/Induction.lean`, and `LF/Typeclasses.lean`. It has been human-reviewed; it does not perfectly illustrate the above ideas, but the examples are hopefully useful nevertheless.)*


### 1. Concrete instructions beat descriptive summary

**Principle:** Minimize complexity · **Commit:** `fcf1418` "Polishing pass over Basics" · **File:** `LF/Basics.lean`

Before, three overlapping paragraphs *described* what the InfoView does:

> "In VS Code, development of Lean code is supported by the Lean Extension... which provides an interactive 'InfoView' panel that displays the results of commands like `#eval`... You can hover over expressions in the source code to see their types... The InfoView always follows your cursor, and Lean typechecks the file as you edit it... You can also use the InfoView to explore the definitions of functions and types that you're using..."

After, the same content is one pass of short imperative sentences tied to the example already on screen:

> "Observe the result in the Lean InfoView panel. This panel displays the results of commands like `#eval`... You can command-click on a type or variable name to navigate to its definition. Try this with the mention of `nextWorkingDay` in the above `#eval`."

Telling the reader what to *do* with the example in front of them replaces three restatements of what the panel is *for*.

### 2. Cut editorial asides

**Principle:** It's good to cut things · **Commit:** `fcf1418` · **File:** `LF/Basics.lean`

Before:

> "This helps to encapsulate the object's definition... In simple examples such conventions may seem trivial or even silly; in complex codebases, it is the only way to maintain crucial invariants that prevent a system from becoming unmaintainable. The same principle applies to definitions and proofs in Lean."

After:

> "Lean takes inspiration from object-oriented programming in favoring the use of _encapsulation_. In OOP, it is considered poor style to expose the fields of an object in its interface... In idiomatic Lean, it is similarly considered poor style to 'peek' through definitions using `rfl`..."

The aside defending *why* OOP encapsulation matters is cut; the OOP-to-Lean comparison is made directly instead, one paragraph instead of two.
:::dev "Benjamin Pierce (bcpierce00)"
I only see one paragraph in both before and after?
:::


### 3. Motivate a typeclass with a real consumer, not an abstract spec

**Principle:** Context/Gap/Solution · **Commit:** `4ef8065` "Typeclasses: motivate HasOne/DefaultValue with a real consumer, headOr" · **File:** `LF/Typeclasses.lean`

Before, the chapter jumped straight to an abstract spec — flagged by the author's own note left in the text:

> ":::dev \"mwhicks1\" PotentialImprovement — As a programmer, I wouldn't imagine defining a `structure` to 'specify' that a type has at least one inhabitant... I wonder if we should redo `HasOne` entirely."
>
> "Suppose we want to specify that a type has at least one inhabitant, i.e., that it is not empty. A `structure`... can express this directly:"

After, a concrete consumer supplies the motivation:

> "Suppose we want a function that returns the first element of a list, defaulting to a given value if the list is empty... This works, but again it's tedious: every caller has to supply an element of `α` to default to, even when there's an obvious choice... Getting Lean to fill in `defaultValue` automatically takes two things."

The `headOr` function gives the reader a reason to want `DefaultValue` before it's defined, resolving the author's own dev-note doubt about the original framing.

### 4. Reuse an example instead of inventing a hypothetical

**Principle:** Minimize complexity · **Commit:** `f103dbf` "Editing pass over Typeclasses" · **File:** `LF/Typeclasses.lean`

Before, flagged by a reviewer note ("This next paragraph gets pretty tangled — can it be streamlined?"):

> "Suppose, just for the sake of argument, that we wanted to define total maps as `List (α × β)` or `Std.HashMap α β`. Neither of these are functions, so the syntax `∅ 1` wouldn't work..."

After:

> "While `TotalMap`s happen to be implemented as functions under the hood, we would prefer not to expose this fact in their public interface... As a first attempt at a query operation, playing the role that `find` played for the Lists chapter's list-based maps, we could define a function `getElem`..."

The invented hypothetical is replaced by a callback to `find`, an example the reader already saw in the Lists chapter.

### 5. Chain together examples the reader has already met

**Principle:** Minimize complexity · **Commit:** `15fbdb4` "Re-work motivation for MyGetElem" · **File:** `LF/Typeclasses.lean`

Before, the notation-as-typeclass idea leaned on a single analogy plus a forward reference to material not yet covered:

> "This is the same pattern behind `==`: writing `a == b` is notation for `BEq.beq`... (indeed, `MyGetElem` is a simpler form of the standard library's `GetElem`)."

After, it chains together two examples already met earlier in the same chapter:

> "We have seen the approach already with `==`... We also just saw overloaded notation for `EmptyCollection` above, where `∅` is notation for `EmptyCollection.emptyCollection`. Our typeclass `MyGetElem` is a simpler version of the standard library's `GetElem` typeclass..."

### 6. State the takeaway in words before the general/formal picture

**Principle:** Start specific, then generalize · **Commit:** `9308d9d` "DHS pass over the induction chapter" · **File:** `LF/Induction.lean`

Before, a commuting-square diagram was presented on its own, with the plain-English gloss only in a `:::dev` note debating whether to move it:

> "Prove that the following diagram commutes:" [diagram follows] — with a dev note: "BCP: I think it's fine, though the english version could precede the diagram instead of following it..."

After, the sentence-level statement precedes the diagram:

> "Prove that the following diagram commutes — that is, incrementing a binary number and then converting it to a (unary) natural number yields the same result as first converting it to a natural number and then incrementing:" [diagram follows]

The fix is literally the reviewer's own suggestion, applied: give the reader the intuitive statement before the more abstract categorical picture.
