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
    - Corollary: Definitions and proofs are written in idiomatic Lean (mostly the way it is for engineering/maintainability reasons), only deviating (temporarily) for pedagogical reasons -- more below
5. SFL follows the path of topics of SF in Rocq unless there are specific reasons not to
6. SFL developments should connect to those in [CSLib](https://github.com/leanprover/cslib/tree/main), as much as possible; e.g., some/all of SFL's fully developed languages, semantics, etc. could have a direct place in CSLib. This implies we should be paying attention to (at the least) and coordinating with (at best) that effort.

### Proof engineering in Lean callouts

We should be following the [style guide](https://leanprover-community.github.io/contribute/style.html) and using the [Lean linter](https://github.com/leanprover-community/mathlib4/wiki/Setting-up-linting-and-testing-for-your-Lean-project). Some things to call out for those more familiar with Rocq:

1. While writing library code, it's fine and necessary to unfold and simplify through definitions. When using that code, the idiomatic way is not to "peek through the interface".

## Rules for collaboration

**To do**: take inspiration from Jimmy Wales' [Seven Rules of Trust](https://en.wikipedia.org/wiki/The_Seven_Rules_of_Trust), which underpin Wikipedia's distributed development.
