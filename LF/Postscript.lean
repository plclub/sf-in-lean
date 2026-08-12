import SFLMeta
open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Postscript" =>
%%%
tag := "Postscript"
htmlSplit := .never
file := some "Postscript"
%%%

Congratulations: We've reached the end of _Logical Foundations_!

# Looking Back

We've covered quite a bit of ground. Along the way, we developed three
connected themes:

_Functional programming_:

- recursive definitions over immutable data
- higher-order functions
- polymorphism

:::slidebreak
:::

_Logic_, the mathematical basis for software engineering:

```
       logic                        calculus
--------------------   ~   ----------------------------
software engineering       mechanical/civil engineering
```

- inductively defined propositions and relations
- inductive proofs
- proof objects

:::slidebreak
:::

_Lean_, an industrial-strength proof assistant:

- a functional programming language
- tactics for constructing proofs
- proof automation

# Looking Forward

The next volumes carry these ideas into programming-language theory
and program verification:

- _{volumeName "ts"}[]_ develops operational semantics and type systems,
  including the simply typed lambda calculus and the progress and
  preservation theorems.

- _{volumeName "hl"}[]_ introduces imperative programs and Hoare logic,
  a framework for stating and proving correctness properties of programs
  with mutable state.

Both volumes build directly on the definitions and proof techniques
introduced here.

# Resources

This volume also contains optional sections and exercises that develop
some topics further.

For questions about Lean, the
[Lean community Zulip](https://leanprover.zulipchat.com/) is an active
place to ask questions and discuss formalization.

The following books continue in several different directions:

- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
  explores Lean as a programming language.
- [Theorem Proving in Lean 4](https://docs.lean-lang.org/theorem_proving_in_lean4/)
  gives a systematic introduction to Lean's logic and proof language.
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
  develops formalized mathematics using Lean and Mathlib.
