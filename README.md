# Software Foundations, Lean version

This repository contains the work-in-progress sources of [Software Foundations](https://softwarefoundations.cis.upenn.edu/), implemented using Lean.

Why are we carrying out this work? You might wonder. There exist excellent texts on both [programming](https://lean-lang.org/functional_programming_in_lean/) and [theorem proving](https://lean-lang.org/theorem_proving_in_lean4/) in Lean. The [How to Prove It! in Lean](https://djvelleman.github.io/HTPIwL/) book introduces logic and proofs in Lean, and overlaps with SF's Logical Foundations text. The [CSLib](https://github.com/leanprover/cslib/tree/main) effort is building a CS-focused core development in Lean (basically "Mathlib for CS"), overlapping with SF's PL Foundations text. 

We believe that there is room for a pedagogically minded text focusing on the mathematical foundations of writing correct software. But we need to be careful not to reinvent the wheel. We need to ensure that, once complete, SF in Lean complements these existing works and/or notably improves on their limitations.

To this end, and to facilitate rapid development, we offer a list of tenets that guide SF in Lean's development. These tenets will keep us on track when making decisions, and hopefully redirect us away from topics adequately covered elsewhere, and toward clear gaps.

We also offer some rules for distributed collaboration. We want to take input from as many people as possible, but develop clear guidelines for taking contributions and resolving disagreements.

## Tenets

1. Human understanding via clear pedagogy is primary
1. Prefer to write definitions and proofs in idiomatic Lean, only deviating temporarily for pedagogical reasons
1. When in doubt, follow the path of topics taken by SF in Rocq; deviations should have good, specific reasons

**To do**: Complete these.

## Rules for collaboration

**To do**: take inspiration from Jimmy Wales' [Seven Rules of Trust](https://en.wikipedia.org/wiki/The_Seven_Rules_of_Trust), which underpin Wikipedia's distributed development.