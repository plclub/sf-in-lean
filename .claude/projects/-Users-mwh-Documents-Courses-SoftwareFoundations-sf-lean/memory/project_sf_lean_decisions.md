---
name: SF-Lean Translation Decisions
description: Key design decisions for translating Software Foundations from Rocq to Lean
type: project
---

Translating Software Foundations "Logical Foundations" from Rocq to Lean.

Source: /Users/mwh/Documents/Courses/SoftwareFoundations/sfdev/lf/*.v
Target: /Users/mwh/Documents/Courses/SoftwareFoundations/sf-lean/lf/*.lean

Chapter order: Basics, Induction, Lists, Poly, Tactics, Logic, IndProp, Maps, ProofObjects, IndPrinciples, Rel, Imp, ImpParser, ImpCEvalFun, Extraction, Auto, AltAuto

## Decisions

1. **Stdlib usage**: Hybrid approach — define our own types initially (inside a namespace) to teach concepts, then transition to Lean's built-in Nat/Bool/List when we need their ecosystem.

2. **Extraction chapter**: Replace with a chapter on Lean's compilation model (compiling to C, compiler treatment of types, writing efficient Lean code).

3. **Auto/AltAuto chapters**: Rewrite to teach Lean's automation ecosystem: simp lemmas, aesop, omega/decide, and custom tactic writing.

4. **File format**: Standard .lean files with `--` comments for all prose and metadata. Do NOT use `/-- -/` doc comments for prose — they can only appear immediately before declarations and cannot be stacked or placed inside proof blocks.

5. **if/Decidable**: Only use `if` with Bool in early chapters. Introduce Decidable typeclass later (around Logic or IndProp).

6. **Metadata**: Preserve all instructor comments, terse/full markers, solutions, and grading markers, adapted to `--` comment syntax.

7. **Proof style**: Idiomatic Lean — write proofs the way an experienced Lean user would. Use simp, omega, decide where appropriate.

8. **Dot notation**: Use `.constructor` dot notation in pattern matches where the expected type is known (e.g., `| .monday => .tuesday`). Use fully qualified names (e.g., `Day.friday`) at the top level where Lean can't infer the type (like `#eval` arguments).

9. **Named examples**: Lean's `example` doesn't take a name. Place the original Rocq name as a `--` comment on the line immediately above the `example`. This allows post-processing to match examples to names for grading.

10. **Custom types avoid name clashes**: When defining custom versions of built-in types (like `Bool`), use a distinct name (e.g., `MyBool`) rather than shadowing in a namespace, to avoid ambiguity issues.

11. **`deriving` introduction**: Introduce `deriving BEq, Repr` in the Lists chapter, where it's applied to a recursive type (lists) and the auto-generated code is genuinely interesting. Do NOT introduce it in Basics/LateDays where the types are flat enums.

12. **Typeclasses chapter (future idea)**: Consider a standalone chapter on Lean's typeclass system. This could cover `BEq`, `Repr`, `Ord`, `Inhabited`, `ToString`, custom typeclasses, instance resolution, and `Decidable`. Would be a natural Lean-specific addition with no Rocq equivalent.

13. **No omega in early chapters**: Basics and Induction use only `rfl`, `rw`, `simp`, `cases`, `induction`, `intro`, `exact`, `have`. Do not use `omega` until it is explicitly introduced (TBD which chapter).

14. **Tactic introduction discipline**: Every tactic must be introduced with prose before its first use, including in ADMITTED solutions. Tactic introduction order across chapters: Basics introduces `rfl`, `intro`, `rw`, `cases`, `simp`, `exact`, `<;>`; Induction introduces `induction`, `simp only`, `have`; Lists uses only previously introduced tactics.

15. **Typeclasses introduced organically in Lists**: Type classes (`HAppend`, `BEq`) are introduced in Lists when the need arises (wanting `++` for our custom `app`). Brief intro: "a type class is an interface, an instance is an implementation." Reference FPIL Chapter 3 for full story. Polymorphic typeclasses deferred to Poly chapter.

**Why:** These decisions balance pedagogical faithfulness to SF with idiomatic Lean style.
**How to apply:** Consult these decisions when translating each chapter.
