# Preface: content comparison

This report compares two Lean translations of the SF `Preface` chapter:

- **`LF/Preface.lean`** — a fresh, faithful draft produced by
  `scripts/to_verso.py` directly from `old/orig-lf-files/Preface.v`. It is a
  mechanical Rocq→Verso conversion: the prose is the original SF text and still
  refers throughout to **Rocq/Coq**.
- **`LF/Preface-Roger.lean`** — an earlier, partially hand-translated version
  that has begun adapting the text to **Lean** but is incomplete (littered with
  `TODO` markers and dropped passages).

Only **differences in content** are reported. Pure formatting/markup
differences (heading syntax, `#####` divider lines, `:::dev` vs bare comment
form, backslash-escaping, blank-line counts, import blocks) are ignored.

---

## 1. Content the two versions share

The following material is present, and substantively identical in wording, in
both files:

- The three-thread overview (logic / proof assistants / functional programming).
- The **Overview** section prose.
- The **Logic** subsection (including the `HIDE` dev note "That last claim is
  now only true if people read some optional chapters").
- The **Functional Programming** body prose (pure computation, benefits,
  parallelism/Map-Reduce, the "bridge between logic and CS" paragraph).
- The **Exercises** section: star ratings, the autograder point table
  (1/2/3/6/10), the advanced/optional explanation, and the "**Please do not
  post solutions**" warning.
- **Downloading the … Files**, **Chapter Dependencies**, and the **Recommended
  Citation Format** BibTeX block.
- **Resources → Sample Exams** and **Lecture Videos**.
- **Note for Instructors and Contributors** (copyright-assignment text and
  Authors-of-Record list) — identical wording.
- **Thanks** (NSF Expeditions grant 1521523).

---

## 2. Prover renaming (Rocq/Coq → Lean)

The pervasive difference: `Preface.lean` says **Rocq/Coq** everywhere the
original does; `Preface-Roger.lean` has changed most of these to **Lean**.
Concrete content-bearing instances:

| Location | `Preface.lean` (faithful) | `Preface-Roger.lean` (hand) |
|---|---|---|
| Welcome, topics list | "the **Rocq** prover" | "the **Lean** prover" |
| Welcome, novelty | "a script for **Rocq** … session with **Rocq** … formalized in **Rocq**" | "…**Lean**…" |
| Logical Foundations blurb | "…and the **Rocq** prover." | "…and the **Lean** prover." |
| Proof-assistant list | "Isabelle, Agda, Twelf, ACL2, PVS, F\*, HOL4, **Lean, and Rocq**" | reordered to "…HOL4, **Rocq, and Lean**" |
| "This course is based around…" | "**Rocq** … under development since **1983**" | "**Lean** … under development since **2013**" |
| FP-languages list | "…Erlang, F\*, and **Rocq**." | "…Erlang, F⋆, and **Lean**." |
| "…itself can be viewed as…" | "**Rocq** itself … a combination of **a small but** extremely expressive functional programming language" | "**Lean** itself … a combination **an** extremely expressive…" (drops "a small but"; minor garble "combination an") |

---

## 3. Content ADDED in `Preface-Roger.lean` (not in the faithful draft)

- **New "this is a Lean port" paragraph** in **Welcome** (has no counterpart in
  the original):
  > "It is important to note that the *Software Foundations* series is
  > originally written using the *Rocq* proof assistant— another theorem prover
  > which is similar to but distinct from Lean. This book marks the first effort
  > in translating the Rocq-based series to Lean— an effort that will
  > (hopefully!) continue with the generous support of the Lean and Rocq
  > communities."

- Numerous **`TODO` work-markers** with no analogue in the source:
  `-- TODO REWRITE` / `-- END TODO`, `change this to lean and mention recent
  lean successes`, `companies should be updated!`, the `$COQVERSION`
  metavariable dev note, `TODO Update with Lean -> Rocq`, `-- TODO ASK
  BENJAMIN`, `TODO NOTE ROCQ VERSION!`, `(TODO LEAN VERSION METAVARIABLE)`,
  `(TODO WRITE)`.

---

## 4. Content DROPPED in `Preface-Roger.lean` (present in the faithful draft)

This is the bulk of the substantive difference — Roger's version omits large
tracts of the original text.

### 4a. Whole sections/headings missing
- **"Functional Programming" subsection heading** — dropped; the body prose
  runs on without its header.
- **Entire "Rocq vs. Coq" section** — the whole naming-history passage
  ("Until 2025, the Rocq prover was known as Coq…", the Inria Rocquencourt /
  Roc bird etymology, and the "transitional state" note) is **absent**.

### 4b. Proof-assistant *successes* list gutted
The faithful draft carries the four concrete achievement bullets:
- **Modeling PLs**: JavaCard common-criteria certification; x86/LLVM/C specs.
- **Certified software/hardware**: CompCert, CertiKOS, floating-point, CertiCrypt/FCF/SSProve, verified RISC-V.
- **Dependent-type FP**: Hoare Type Theory.
- **Higher-order logic**: the 4-color theorem, Feit–Thompson theorem.

Plus the `HIDE` dev note suggesting Iris/VST.

In Roger's version all four are replaced by stubs: only the JavaCard bullet
survives; the rest read "…to build **TODO**", "…inspired numerous innovations.
For example, **TODO**", "…For example, **TODO**", with a dev note "change this
to lean and mention recent lean successes". **All concrete achievement content
is lost.**

### 4c. Installation instructions largely removed
- **Recommended Installation Method: VSCode + Docker** — the faithful draft has
  the full step-by-step (install Docker; install VSCode; Dev Containers
  extension; download the `.tgz`/`.devcontainer`/`_CoqProject`; *Open Folder* →
  Reopen in Container; verify VSRocq with `alt+downarrow`; the `vsrocqtop`
  troubleshooting; `Coq:` key-bindings) plus a long dev note with a "KNOWN
  PROBLEMS" troubleshooting appendix. Roger keeps only a single sentence and a
  stray "KNOWN PROBLEMS" line under a "Web Version (TODO WRITE)" heading;
  everything else is dropped.
- **Alternative Installation Methods** — the faithful draft lists the Rocq
  Platform install, and three IDEs: *VsCoq*, *Proof General* (with the full
  `C-c C-n` / `C-c C-u` / `C-c C-RET` / `C-c C-.` / `C-c .` command list and the
  `company-coq`/`control-lock` tip), and *RocqIDE* (with the
  `coqide -async-proofs off …` invocation). Roger keeps only the "Lean 4 VS Code
  extension" bullet; **Proof General and RocqIDE, and all the key-binding /
  command-line detail, are dropped.**

### 4d. Further Reading
- Both keep the pointer to the Postscript and Bib; Roger renames the target
  from `Bib` to `Bib.lean` (content-equivalent pointer).

---

## 5. Summary

`Preface-Roger.lean` is best understood as a *first-pass adaptation*: it has
done the easy global Rocq→Lean renaming and the year/heritage framing, but has
**deleted rather than translated** every Rocq-specific block of substance — the
achievements list, the "Rocq vs. Coq" history, and nearly all of the
installation instructions — leaving `TODO` placeholders in their place. The
freshly generated `Preface.lean` is complete and faithful but entirely
Rocq-centric. A finished chapter needs the *coverage* of `Preface.lean` with the
*Lean orientation* of `Preface-Roger.lean`; see `Preface-recommendations.md`.
