# Postscript: recommendations for the Lean edition

Recommendations for what should change in the `Postscript` chapter now that the
whole course is in **Lean**, not Rocq. Written against the faithful
`LF/Postscript.lean` draft, noting where `LF/Postscript-Roger.lean` is already
ahead.

Unlike the Preface, the Postscript is a natural home for a *deliberate* note
about the Lean/Rocq relationship (the wider SF series is still Rocq), so a
reader-useful mention of Rocq here is appropriate rather than something to
scrub.

---

## 1. Write the real opening text
The `:::dev "The FULL version could use some real text"` note is still true.
Give the chapter a proper valedictory paragraph rather than the bare
"Congratulations" line, and use the "in Lean" title consistently.

## 2. Looking Back
- Rename the closing bullet "*Rocq*, an industrial-strength proof assistant" →
  "*Lean*, …" (Roger did this). Everything else in the review list (functional
  programming, the logic/calculus analogy diagram, inductive definitions/proofs,
  proof objects, functional core / tactics / automation) is
  edition-independent and stays as is.

## 3. Looking Forward — adopt Roger's rewrite, then verify the facts
Roger's version is the right direction and should be the basis: it names the
actual Lean volumes that exist rather than the old Rocq volume lineup.
Recommendations:
- **Confirm the volume landscape** before publishing. Roger says "As of August
  2026, there are two more volumes written in Lean" — **Hoare Logic** and **Type
  Systems** — combined as **_Programming Language Foundations in Lean_**. Verify
  this matches the actual repo state (the additional working dirs include `HL/`
  and `TS/`, consistent with this) and adjust the count/names if it has changed.
- **Fix the Lean/Rocq direction error** in Roger's heritage paragraph: it says
  "Switching from **Lean to Rocq** has a medium-sized learning curve" — in
  context (a reader who has just learned Lean and might explore the Rocq-based
  volumes) the intended direction reads backwards; state clearly which way the
  reader would be moving and why.
- Decide whether to keep the "please help translate / see `CONTRIBUTING.md` /
  write the `sf-dev` team" invitation in the public book or move it to a
  `:::instructors`/`:::dev` note. It is useful but developer-facing.
- The original's pointer to *Verified Functional Algorithms* (Appel, vol. 3)
  was dropped; add it back only if/when a Lean edition of that volume exists.

## 4. Resources — replace Rocq pointers with Lean ones
Roger correctly flagged every item here but left them as `TODO`s. Concrete fills:
- **Q&A / community:** replace "the `#coq` area of Stack Overflow" with the
  **Lean Zulip** (`https://leanprover.zulipchat.com`) — the primary Lean
  community forum. (Roger's "Lean Zulip (TODO LINK)" just needs the URL.)
- **Functional-programming books:** keep *Learn You a Haskell* and *Real World
  Haskell* — still relevant and language-agnostic. Optionally add **_Functional
  Programming in Lean_** (David Thrane Christiansen) here, since it teaches FP in
  the very language of the course.
- **Rocq reading list → Lean reading list:** replace *Certified Programming with
  Dependent Types* (Chlipala) and *Coq'Art* (Bertot & Castéran) with the Lean
  canon: **_Theorem Proving in Lean 4_**, **_Mathematics in Lean_**, **_The
  Hitchhiker's Guide to Logical Verification_**, and **_Functional Programming in
  Lean_**. (Fills Roger's "TODO LEAN RESOURCES".)
- **Verified-systems applications:** the DeepSpec 2017 Summer School pointer is
  Rocq-based; replace with Lean verified-systems / applied-Lean resources, or
  drop. (Fills Roger's "TODO LEAN MATERIALS".)
- Restore working links for the **table of contents** and **chapter dependency
  diagram** (Roger left them as `(TODO LINK)`); use the Verso cross-reference
  mechanism rather than raw `toc.html`/`deps.html` anchors.

## 5. Cleanup
- Remove the top-of-file smoke-test line "Testing `{citet Bib.bertot2004}[]`."
  once citation rendering is confirmed elsewhere — it is not real content.
  (Note: if `Bib.bertot2004` is a Rocq-era reference, make sure the bibliography
  entries the chapter cites still exist in the Lean edition's `Bib`.)
- Convert any surviving `TODO` markers into proper
  `:::dev … PotentialImprovement` notes per `CLAUDE.md`.
