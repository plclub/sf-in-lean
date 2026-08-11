# Preface: recommendations for the Lean edition

These are recommendations for what should change in the `Preface` chapter now
that the whole course is in **Lean**, not Rocq. They are written against the
faithful `LF/Preface.lean` draft (the complete, still-Rocq-centric text), and
note where `LF/Preface-Roger.lean` has already made a good start.

The overarching principle (per `CLAUDE.md`, "Framing translated comments"): the
chapter must **stand on its own for a Lean reader** who has never seen the Rocq
source. It should not read as a port — no "originally in Rocq, now translated"
narration in the main prose — except where a deliberate, reader-useful note
about the Lean/Rocq relationship is warranted (and those belong in the
Postscript, not here).

---

## 1. Global prover renaming
Replace every **Rocq/Coq** reference with **Lean** in ordinary prose:
- "the Rocq prover" → "the Lean prover"; "a script for Rocq" → "a script for
  Lean"; "formalized in Rocq" → "formalized in Lean".
- FP-languages list: "…Erlang, F\*, and Rocq." → "…Erlang, F\*, and Lean."
- "Rocq itself can be viewed as a combination of a small but extremely
  expressive functional programming language…" → keep the phrasing but say
  **Lean** (and restore "a small but", which Roger accidentally dropped and
  garbled to "combination an").

## 2. Welcome section — how to frame the Lean edition
- Keep it clean and Lean-native. Roger's added "this is the first translation
  of the Rocq series to Lean" paragraph is reasonable framing, but per the
  house style it is better placed as a short forward-looking note or in the
  Postscript rather than as the second paragraph of the book. **Recommendation:**
  keep one sentence acknowledging the Lean edition and its heritage, move the
  longer "translation effort / support of the communities" material out of the
  main flow (a `:::dev` or the Postscript).

## 3. Proof Assistants subsection
- In the proof-assistant list, keep Lean but present it as *the* tool of this
  course; the list itself ("Isabelle, Agda, Twelf, ACL2, PVS, F\*, HOL4, …,
  Rocq") can stay — Rocq belongs there as a peer system.
- "This course is based around **Lean**, a proof assistant … under development
  since **2013** …" — the year fix Roger made is correct (Lean announced by
  Leonardo de Moura at Microsoft Research in 2013; Lean 4 is the current
  generation). Keep the "kernel is a simple proof-checker / high-level tactics /
  language for defining new tactics" description — all true of Lean.
- **Rewrite the "successes" list for Lean** (this is the big TODO Roger left
  blank). Candidate replacements, keeping the four-category shape:
  - *Modeling / verifying programming languages & systems*: Lean's use in
    verified-systems and PL research.
  - *Certified software*: e.g. verified cryptography and compiler-adjacent work.
  - *Realistic dependently-typed functional programming*: Lean 4 is a full
    programming language implemented largely in itself; **Mathlib** is the
    flagship library.
  - *Higher-order-logic mathematics*: the **Liquid Tensor Experiment** (Scholze's
    challenge, completed 2022), the **Polynomial Freiman–Ruzsa** formalization
    (2023), the sphere-eversion project, and AI-for-math work (e.g. AlphaProof)
    built on Lean.
  Verify names/dates before publishing; these are the strongest, most current
  Lean achievements analogous to CompCert / 4-color / Feit–Thompson.
- The Iris/VST `HIDE` dev note can be dropped or replaced with a Lean analogue.

## 4. "Rocq vs. Coq" section — drop it
This entire naming-history section is Rocq-specific and has no place in a Lean
book. Roger already dropped it; **recommend removing it** (optionally preserving
a one-line `:::dev` pointer for anyone maintaining both editions). Restore the
**"Functional Programming" heading** that went missing when this area was edited.

## 5. Practicalities → System Requirements & Installation
This is the section needing the most Lean-native rewriting:
- **Version metavariable:** replace "tested with Rocq `$COQVERSION`" with a Lean
  toolchain version. Roger's dev note is right that Verso makes a live
  metavariable easy — implement it rather than hard-coding.
- **Recommended installation:** rewrite for the Lean toolchain — **`elan`**
  (Lean version manager), the **Lean 4 VS Code extension**, and `lake` for
  building the project. Describe cloning/opening the SF-in-Lean project and
  building with `lake build`. If a web/Docker path is offered, describe the
  actual one for this repo (Roger's "Web Version (TODO WRITE)" is a placeholder).
- **Delete the Rocq-specific IDE material:** VSRocq/`vsrocqtop`, Proof General
  and its `C-c` command list, RocqIDE and the `coqide -async-proofs …`
  invocation, and the Docker/`_CoqProject`/`.vo`-OCaml-mismatch troubleshooting.
  Replace with the (much shorter) Lean equivalents; most of this simply goes
  away because the Lean VS Code extension + `elan`/`lake` is the single blessed
  path.

## 6. Exercises
- Star ratings and the advanced/optional explanation carry over unchanged.
- **Verify the autograder point table** (1/2/3/6/10) still matches the Lean
  grading tooling (`:::gradeTheorem` / `SFLMeta/Grade.lean`); update if the Lean
  autograder scores differently.
- Keep the "**Please do not post solutions**" warning verbatim.

## 7. Downloading the files
- "A tar file … collection of Rocq scripts and HTML files" → describe how the
  Lean sources are actually distributed (git repo + `lake`, or a released
  archive of `.lean` files). Rename the heading to "Downloading the Lean Files"
  (Roger did this).

## 8. Recommended Citation Format
- The BibTeX template is fine structurally; ensure the `series`/`note` and
  volume metadata reflect the Lean edition (title, version string, URL).

## 9. Resources
- **Sample Exams:** keep the CIS 5000 exam compendium pointer, but strengthen
  the caveat — these exams are in **Rocq** notation, so "some drift of notations"
  understates it for a Lean reader. Roger's "TODO Update with Lean -> Rocq" flags
  exactly this.
- **Lecture Videos:** the DeepSpec videos are Rocq-based; keep with a clear note
  that they use Rocq, or replace with Lean lecture material if available.

## 10. Note for Instructors / Authors of Record
- The copyright-assignment text and Authors-of-Record list are
  edition-independent and should stay. Consider one added clause naming the
  Author(s) of Record for the **Lean edition / translation** so provenance is
  unambiguous. Resolve Roger's "TODO ASK BENJAMIN" and "TODO NOTE ROCQ VERSION!"
  markers by deciding this explicitly.

## 11. Cleanup
- Remove all `TODO`/scaffolding markers (`-- TODO REWRITE`, `-- END TODO`,
  `-- TODO ASK BENJAMIN`, `TODO NOTE ROCQ VERSION!`, `(TODO WRITE)`,
  `(TODO LEAN VERSION METAVARIABLE)`) once the corresponding content is written,
  converting any that must survive into proper `:::dev … PotentialImprovement`
  notes per `CLAUDE.md`.
