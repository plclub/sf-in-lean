# Postscript: content comparison

This report compares two Lean translations of the SF `Postscript` chapter:

- **`LF/Postscript.lean`** — a fresh, faithful draft produced by
  `scripts/to_verso.py` directly from `old/orig-lf-files/Postscript.v`. It is a
  mechanical Rocq→Verso conversion; the prose is the original SF text and still
  refers to **Rocq/Coq**.
- **`LF/Postscript-Roger.lean`** — an earlier, partially hand-translated
  version that has begun adapting the text to **Lean** and, in the "Looking
  Forward" section, substantially rewritten it.

Only **differences in content** are reported. Pure formatting/markup
differences (import block, `\-` list escaping, code-fence style, `:::dev` vs
bare comment form) are ignored.

---

## 1. Content the two versions share

- The opening dev note "The FULL version could use some real text".
- The **Congratulations** line.
- The **Looking Back** review list: functional programming (declarative style,
  higher-order functions, polymorphism); logic (the
  `logic / software engineering ~ calculus / …engineering` diagram, inductive
  sets/relations, inductive proofs, proof objects); and the proof-assistant
  bullet (functional core language, core tactics, automation).
- The functional-programming **book recommendations**: *Learn You a Haskell*
  (Lipovača 2011), *Real World Haskell* (O'Sullivan/Goerzen/Stewart 2008), and
  "…many other excellent books on Haskell, OCaml, Scheme, Racket, Scala, F#…".
- The pointer to the **Postscript of *Programming Language Foundations*** for
  real-world verification applications.

---

## 2. Prover renaming (Rocq/Coq → Lean)

| Location | `Postscript.lean` (faithful) | `Postscript-Roger.lean` (hand) |
|---|---|---|
| Congratulations | "end of *Logical Foundations*!" | "end of *Logical Foundations in Lean*!" |
| Looking Back, last bullet | "*Rocq*, an industrial-strength proof assistant" | "*Lean*, an industrial-strength proof assistant" |
| Resources, Q&A forum | "the `#coq` area of **Stack Overflow**" (with URL) | "the **Lean Zulip** (TODO LINK)" |
| Resources, further reading | "further resources for **Rocq**" | "further resources for **Lean**" |
| Resources, verified systems | "applications of **Rocq** … 2017 DeepSpec Summer School" (with URL) | "applications of **Lean** … TODO LEAN MATERIALS" |

---

## 3. "Looking Forward" — substantially rewritten

This is the largest content difference.

**Faithful draft (`Postscript.lean`)** keeps the original's short, generic
paragraph — "you have several choices for further reading in later volumes …
some accessible immediately, others require a few chapters from Volume 2,
*Programming Language Foundations* … The Preface chapter in each volume gives
details about prerequisites." — followed by a **dev note** proposing per-volume
advertising blurbs for *Programming Language Foundations* (vol. 2) and *Verified
Functional Algorithms* (vol. 3, Appel).

**Hand version (`Postscript-Roger.lean`)** replaces all of this with new,
Lean-specific prose:
- "As of August 2026, there are two more volumes written in Lean."
- A **_Hoare Logic_** paragraph (reasoning about imperative programs, embeddable
  in Lean's type system).
- A **_Type Systems_** paragraph (type systems as a correctness tool).
- A note that these combine into **_Programming Language Foundations in Lean_**.
- A paragraph on the "in Lean" tag, the original Rocq series, the Lean→Rocq
  learning curve, and the invitation to help translate (see `CONTRIBUTING.md`,
  the `sf-dev` team).

The original's mention of *Verified Functional Algorithms* (Appel, vol. 3) is
**dropped**; the per-volume dev note is dropped in favor of this live prose.

---

## 4. Resources — content added / dropped

- **Added in Roger:** a test line at the very top, "Testing
  `{citet Bib.bertot2004}[]`." (a Verso citation smoke-test, not real content).
- **Table-of-contents / dependency-diagram links:** both mention them; the
  faithful draft has working HTML anchors, Roger replaces them with
  `(TODO LINK)` placeholders.
- **Rocq reading list dropped:** the faithful draft lists two classic Rocq
  books — *Certified Programming with Dependent Types* (Chlipala 2013) and
  *Interactive Theorem Proving … Coq'Art* (Bertot & Castéran 2004). Roger
  replaces the whole sub-list with "**TODO LEAN RESOURCES**".
- **DeepSpec 2017 pointer dropped:** the faithful draft gives the DeepSpec
  Summer School lectures + URL; Roger replaces it with "**TODO LEAN
  MATERIALS**".

---

## 5. Summary

For **Looking Forward**, `Postscript-Roger.lean` is *ahead* of the faithful
draft — it already describes the real Lean volume landscape (Hoare Logic, Type
Systems) and should be the basis going forward. For **Resources**, Roger has
correctly identified what must change (Stack-Overflow→Zulip, Rocq books → Lean
books, DeepSpec → Lean materials) but has left them all as `TODO`s, so the
faithful draft is the only one with concrete (if Rocq-centric) content there.
See `Postscript-recommendations.md`.
