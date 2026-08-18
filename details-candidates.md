# `:::details` candidates — survey pass

*Survey only. No chapter file was modified by the pass that produced this list.*

## How to use this file

Every entry below is a **proposal** to wrap a region of a chapter in a
`:::details "…"` directive. Read down the list and **delete any entry that should
not be wrapped**; whatever is left will be applied verbatim in a follow-up pass.

Each entry is a single top-level bullet with its sub-bullets indented under it, so
one entry deletes in one motion (select the `- [ ] **L…**` line through the last
indented line under it).

Notes that apply to the whole list:

* **Line ranges are inclusive and name the region that goes *inside* the
  directive.** Where the range starts/ends on a ```` ``` ```` fence line, the whole
  fenced block is wrapped. Where the range starts/ends *inside* an existing fenced
  block, the block has to be **split** into two (or three) fenced blocks first —
  those entries carry a `- Caveat:` line saying so.
* **Elaboration is preserved.** `:::details` is not a noop: its body elaborates
  (so live Lean inside stays checked by `lake build`) and the saver emits the
  contents unwrapped into the generated `.lean`. No candidate in this list loses
  checking by being wrapped. Splitting one ```` ```lean ```` block into two is
  likewise safe — an unclosed `section`/`namespace` may span blocks (`TS/Stlc.lean`
  already does exactly this at L1656/L1689).
* **Colon counts.** Verso nesting requires the *outer* directive to have more
  colons than the inner one. All the `HL/Hoare.lean` extension-module candidates
  sit inside a `::::::full` (6 colons), so they must be written `:::::details` (5)
  or fewer. Everything else in this list is at document level; use `::::details`
  (4 colons, matching the house style in `HL/Imp.lean` and `TS/Stlc.lean`) when
  the body contains a fenced code block.
* Entries are sorted **high → medium → low** within each file.
* Summaries follow house style: `"Notation encoding: <what>"` for notation
  plumbing, a plain descriptive phrase otherwise.

---

# LF

Files scanned: `Preface.lean`, `Basics.lean`, `Induction.lean`, `UsingLean.lean`,
`Lists.lean`, `Poly.lean`, `Tactics.lean`, `Logic.lean`, `IndProp.lean`,
`Automation.lean`, `Typeclasses.lean`, `Postscript.lean`.

LF is nearly clean: it has almost no metaprogramming, and the one place that
already needed hiding (`LF/Basics.lean:1387`) is already wrapped. Only two strong
candidates.

### LF/Lists.lean

- [ ] **L290–L304** — `scoped infixr` for `::`, the `[...]` list-notation `macro`, and the two `app_unexpander`s (`unexpandNil`, `unexpandCons`)
  - Suggested summary: `"Notation encoding: list notation"`
  - Prose signal: "Don't worry too much about what this is doing:" (L288)
  - Confidence: high
  - Caveat: the prose at L306–L308 immediately *after* the block explains it
    ("We first define `::` as right-associative _notation_ … and then define list
    notation _macro_ with _unexpander_"). That paragraph reads fine with the code
    collapsed, but consider moving it *inside* the directive body above the fence,
    the way `TS/Stlc.lean:399–406` does.

### LF/Typeclasses.lean

- [ ] **L659–L671** — `namespace MyGetElem` with the `scoped macro_rules` for `xs[i]` and the `@[app_unexpander getElem]` `unexpandGetElem`
  - Suggested summary: `"Notation encoding: map indexing"`
  - Prose signal: "Don't worry about following the mechanism in detail — the `macro_rules` and the `app_unexpander` below are minor technicalities." (L653–L654)
  - Confidence: high
  - Caveat: L673–L676 refers back to the block ("we only need to define the
    `macro_rules`, not the `notation`"). Still readable collapsed, but that
    sentence would sit more naturally inside the directive body.

- [ ] **L740–L741** — the `notation a:55 " →ₜ " b:55 " ; " m:55 => TotalMap.update m a b` line only
  - Suggested summary: `"Notation encoding: total-map update"`
  - Prose signal: none (L734–L738 *explains* the choice of a direct `notation` over a typeclass)
  - Confidence: low
  - Caveat: requires splitting the fenced block L740–L750 — the two theorems at
    L743–L749 are chapter content and must stay visible. Arguably the notation is
    taught here rather than hidden; a plausible cull.

- [ ] **L1118–L1120** — the two `notation … " →ₚ " …` declarations for partial-map update
  - Suggested summary: `"Notation encoding: partial-map update"`
  - Prose signal: none ("We also introduce a similar notation for it as for total maps." L1110)
  - Confidence: low
  - Caveat: requires splitting the fenced block L1112–L1123 around `def update`
    (L1115–L1116) and `def examplePmap` (L1122). Probably not worth it — a
    plausible cull.

### LF/Automation.lean

- [ ] **L694** — `attribute [pp_nodot] RegExp.Char RegExp.App RegExp.Union RegExp.Star`
  - Suggested summary: `"Pretty-printing the regexp constructors"`
  - Prose signal: none
  - Confidence: low
  - Caveat: requires splitting the fenced block L684–L695; the `deriving BEq,
    DecidableEq, Repr` clause on L692 is part of the `inductive` and cannot be
    separated from it. One line for the cost of an extra fence — a plausible cull.

---

# HL

Files scanned: `Preface.lean`, `Slang.lean`, `Imp.lean`, `Hoare.lean`.
(`HL/Slang.lean` is byte-identical to `TS/Slang.lean`; it is covered once here and
has no candidates — its `scoped notation` declarations are all taught in prose.)

`HL/Hoare.lean` is where the bulk of the remaining work is: the four extension
modules (`If1`, `RepeatExercise`, `Himp`, `HoareAssertAssume`) each re-declare the
whole Imp command grammar, and none of those copies is collapsed.

### HL/Hoare.lean

- [ ] **L567–L630** — the assertion grammar: `scoped syntax` for `assn(…)`/`{{ … }}`, the `@[term_elab assn] assnElab` term elaborator, and the two `macro_rules` groups
  - Suggested summary: `"Notation encoding: assertions"`
  - Prose signal: "There is no need to understand the details of how these notations work." (L501)
  - Confidence: high
  - Note: this is the single highest-value candidate in the repo — 64 lines of raw
    `Lean.Elab` metaprogramming (`mkApp6`, `Meta.synthInstance`, …) sitting in the
    reader's path with an explicit "no need to understand" immediately above it.
    Its companion delaborator block at L1590–L1698 is *already* a `:::details`.

- [ ] **L3006–L3044** — the `if1_com` syntax category: `declare_syntax_cat`, the seven `syntax` productions, and the `macro_rules` for `imp1 { … }`
  - Suggested summary: `"Notation encoding: If1 commands"`
  - Prose signal: "The first step is to extend the syntax of commands and introduce the usual notations.  (We've done this for you, in a separate namespace to prevent polluting the global name space. …)" (L2984–L2987), plus an author note `:::instructors Copy of template com` at L3002–L3004
  - Confidence: high
  - Caveat: inside a `::::::full` opened at L2973 — write as `:::::details`.

- [ ] **L3945–L3979** — the rest of the `rpt_com` category: the six copied `syntax` productions and the `macro_rules` for `impr { … }`
  - Suggested summary: `"Notation encoding: Repeat-Imp commands"`
  - Prose signal: `:::instructors Copy of template com` at L3941–L3943 — the block is verbatim boilerplate copied from the Imp grammar
  - Confidence: high
  - Caveat: inside a `::::::full` opened at L3910 — write as `:::::details`. The
    *preceding* block L3934–L3939 (the `repeat … until` production) is the new,
    chapter-relevant production and should stay visible.

- [ ] **L4462–L4497** — the copied `himp_com` productions and the `macro_rules` for `imph { … }`
  - Suggested summary: `"Notation encoding: Himp commands"`
  - Prose signal: `:::instructors Copy of template com` at L4458–L4460
  - Confidence: high
  - Caveat: requires splitting the fenced block L4462–L4526 immediately before
    `inductive Com.EvalR` (L4498), which is chapter content. Inside a `::::::full`
    opened at L4430 — write as `:::::details`.

- [ ] **L4691–L4727** — the copied `haa_com` productions and the `macro_rules` for `impa { … }`
  - Suggested summary: `"Notation encoding: assert/assume-Imp commands"`
  - Prose signal: `:::instructors Copy of template com` at L4687–L4689
  - Confidence: high
  - Caveat: inside a `::::::full` opened at L4640 — write as `:::::details`. The
    preceding block L4678–L4685 introduces the new `assert`/`assume` production and
    should stay visible.

- [ ] **L1105–L1121** — `namespace ValidHoareTriple` with the `scoped syntax` for `{{ P }} c {{ Q }}` and its `macro_rules`
  - Suggested summary: `"Notation encoding: Hoare triples"`
  - Prose signal: none directly, but it is the immediate continuation of the "no need to understand the details" assertion-notation material (L501)
  - Confidence: medium

- [ ] **L1465–L1472** — the `syntax`/`macro_rules` for the assertion-substitution notation `P [X ↦ a]`
  - Suggested summary: `"Notation encoding: assertion substitution"`
  - Prose signal: none
  - Confidence: medium
  - Caveat: the notation itself is taught (`def Assertion.sub` at L1448–L1451 stays
    visible, and L1474–L1478 shows the surface form). Only the encoding is hidden.

- [ ] **L3127–L3138** — `namespace ValidHoareTriple` with the `scoped syntax`/`macro_rules` for If1 triples, plus `open scoped ValidHoareTriple`
  - Suggested summary: `"Notation encoding: If1 Hoare triples"`
  - Prose signal: "Now we have to repeat the definition and notation of Hoare triples, so that they will use the updated `Com` type." (L3116–L3117)
  - Confidence: medium
  - Caveat: requires splitting the fenced block L3119–L3139 after `def ValidHoareTriple` (L3120–L3125), which is chapter content. Inside a `::::::full` (L2973) — write as `:::::details`.

- [ ] **L4035–L4046** — `namespace ValidHoareTriple` with the `scoped syntax`/`macro_rules` for Repeat-Imp triples, plus `open scoped ValidHoareTriple`
  - Suggested summary: `"Notation encoding: Repeat-Imp Hoare triples"`
  - Prose signal: "A couple of definitions from above, copied here so they use the new `Com.EvalR`." (L4028–L4029)
  - Confidence: medium
  - Caveat: requires splitting the fenced block L4031–L4047 after `def ValidHoareTriple` (L4032–L4033). **This block is inside a `:::::exercise` opened at L3984** (itself inside a `::::::full` at L3983) — nesting a `::::details` there is legal but check the rendering, and cull this one if you would rather not put a disclosure inside an exercise body.

- [ ] **L4534–L4545** — `namespace ValidHoareTriple` with the `scoped syntax`/`macro_rules` for Himp triples, plus `open scoped ValidHoareTriple`
  - Suggested summary: `"Notation encoding: Himp Hoare triples"`
  - Prose signal: "The definition of Hoare triples is exactly as before." (L4528)
  - Confidence: medium
  - Caveat: requires splitting the fenced block L4530–L4546 after `def ValidHoareTriple` (L4531–L4532). Inside a `::::::full` (L4430) — write as `:::::details`.

- [ ] **L4810–L4823** — `namespace ValidHoareTriple` with the `scoped syntax`/`macro_rules` for assert/assume triples, plus `open scoped ValidHoareTriple`
  - Suggested summary: `"Notation encoding: assert/assume Hoare triples"`
  - Prose signal: none (the interesting `def ValidHoareTriple` is in its own block at L4795–L4801 and stays visible)
  - Confidence: medium
  - Caveat: inside a `::::::full` opened at L4731 — write as `:::::details`. No split needed; the whole fenced block is plumbing.

- [ ] **L4521–L4525** — the `scoped notation`/`scoped syntax`/`scoped macro_rules` re-declaring `st =[ c ]=> st'` for Himp
  - Suggested summary: `"Notation encoding: the Himp evaluation arrow"`
  - Prose signal: none
  - Confidence: low
  - Caveat: requires a *second* split of the fenced block L4462–L4526 (see the L4462–L4497 entry above), leaving `inductive Com.EvalR` L4498–L4519 as a middle block. Three fences for five lines — cull unless you want the module's plumbing uniformly hidden. The same five-line tail exists at L3083–L3087 (If1), L4021–L4025 (Repeat), and L4783–L4787 (HAA), each with the same trade-off.

- [ ] **L4449–L4455** — `declare_syntax_cat himp_com` and the `havoc` production
  - Suggested summary: `"Notation encoding: the havoc production"`
  - Prose signal: none
  - Confidence: low
  - Caveat: requires splitting the fenced block L4438–L4456 after the `Com`
    inductive (L4441–L4447). This is the *new* production for this module, so it is
    arguably content — the `Copy of template com` boilerplate that follows it is the
    real candidate (see L4462–L4497).

- [ ] **L4679–L4684** — `declare_syntax_cat haa_com` and the `assert`/`assume` production
  - Suggested summary: `"Notation encoding: the assert/assume production"`
  - Prose signal: none
  - Confidence: low
  - Caveat: same reasoning as the `havoc` entry above — this is the new production
    for the module. Inside a `::::::full` (L4640).

- [ ] **L2797** — `instance : Coe Bexp Assertion := ⟨bassertion⟩`
  - Suggested summary: `"Bexp to Assertion coercion"`
  - Prose signal: none
  - Confidence: low
  - Caveat: requires splitting the fenced block L2791–L2798; `def bassertion` and
    its `@[simp]` lemma (L2792–L2795) are content. One line — a plausible cull.

### HL/Imp.lean

- [ ] **L1097–L1103** — `notation:40 … " =[ " c " ]=> " …` plus the `syntax`/`macro_rules` that also accept a bare `imp_com` between the brackets
  - Suggested summary: `"Notation encoding: the evaluation arrow"`
  - Prose signal: none
  - Confidence: medium
  - Caveat: requires splitting the fenced block L1078–L1104 after `inductive
    Com.EvalR` (L1079–L1095), which is core chapter content the reader must see. The
    `notation` line itself is arguably taught (the inference rules above it are
    written with `=[ ]=>`); the `syntax`/`macro_rules` pair at L1101–L1103 is pure
    plumbing, so an alternative is to wrap only those three lines.

- [ ] **L599–L619** — the twelve `@[simp]` characterization lemmas for `Aexp.eval` and `Bexp.eval`
  - Suggested summary: `"Simp lemmas for the evaluators"`
  - Prose signal: none
  - Confidence: low
  - Caveat: requires splitting the fenced block L578–L620 after the two `eval`
    definitions (L581–L597). The pattern is *taught* in `Slang` (L151–L157 there);
    here it is repetition, but a reader may want to see the state-passing versions.
    A plausible cull.

- [ ] **L230–L250** and **L261–L271** — the `imp_aexp` syntax category and its `macro_rules`
  - Suggested summary: `"Notation encoding: arithmetic expressions"` / `"Notation encoding: arithmetic expressions, macro rules"`
  - Prose signal: "You do not need to understand exactly what these declarations do." (L213)
  - Confidence: low
  - Caveat: **these two blocks are deliberately left uncollapsed.** The prose at
    L216–L227 walks through them line by line as the worked exemplar, and then says
    "Boolean expressions and, later, commands follow this same pattern exactly, so
    their declarations are collapsed where they appear: open one if you want to see
    the pattern repeated, and skip them otherwise." Wrapping these would require
    rewriting that paragraph. Listed only because the prose signal is so explicit;
    most likely a cull.

- [ ] **L350–L359** — the three coercion instances `Coe Ident Aexp`, `OfNat Aexp n`, `Coe Bool Bexp`
  - Suggested summary: `"Coercions into Aexp and Bexp"`
  - Prose signal: none — L337–L348 explains each of the three instances in detail
  - Confidence: low
  - Caveat: matches the "coercion instances that exist purely for surface syntax"
    rule, but the chapter explicitly teaches them here. A plausible cull.

---

# TS

Files scanned: `Preface.lean`, `Slang.lean`, `Smallstep.lean`, `Types.lean`,
`Stlc.lean`.

`TS/Stlc.lean` is already the best-covered file in the repo (six `:::details`) and
sets the house pattern for the hygiene-off / re-declare idiom. `TS/Types.lean` uses
that same idiom twice but only collapses the delaborator half.
`TS/Smallstep.lean` has **no candidates** — its `scoped notation` declarations are
one-liners the prose introduces as content.

### TS/Types.lean

- [ ] **L826–L849** — the hygienic re-declaration of the judgment `macro_rules`, `delabTy`, and the `@[app_unexpander Tm.HasType]` unexpander
  - Suggested summary: `"Notation encoding: printing judgments back"`
  - Prose signal: "Unlike `⟶`, the judgment builds on the custom `tm` syntactic category, so it must use `syntax`/`macro_rules` rather than `notation` — which is why it still needs the `app_unexpander` to print the judgment back." (L789–L792)
  - Confidence: high
  - Caveat: requires splitting the fenced block L795–L853 after `end` (L824) and
    before the `example` at L851. Exactly mirrors `TS/Stlc.lean:1684–1695` +
    `1697–…`, so the split is house-standard. Note this reuses the wording of the
    existing summary at `TS/Types.lean:231`; disambiguate as
    `"Notation encoding: printing judgments back"` vs. the existing
    `"Notation encoding: printing terms back"`.

- [ ] **L800–L811** — the two `syntax:max "<{ ⊢ … }>"` declarations plus `section` / `set_option hygiene false in` / `local macro_rules`
  - Suggested summary: `"Notation encoding: the typing judgment"`
  - Prose signal: "As with `Tm.Step`, we define the relation using its own notation, inside a `section` with `set_option hygiene false` so the bare name `Tm.HasType` in the expansion resolves to the relation being defined" (L786–L789)
  - Confidence: medium
  - Caveat: requires splitting the fenced block L795–L853 so that `inductive Ty`
    (L796–L798) and `inductive Tm.HasType` (L813–L823) stay visible. The `section`
    opened at L803 is closed at L824 in a *later* block — legal, and already done
    this way in `TS/Stlc.lean`.

- [ ] **L163–L196** — `declare_syntax_cat tm`, its seven `syntax` productions, and the `macro_rules` for `<{ … }>`
  - Suggested summary: `"Notation encoding: terms"`
  - Prose signal: "You do not need to understand exactly how the declarations below work" (L150)
  - Confidence: low
  - Caveat: **deliberately left uncollapsed.** The same sentence continues "…; every
    object language in this book is given its syntax the same way, so it is worth
    seeing the pattern once", and L154–L160 walks the block line by line. Wrapping
    it means rewriting that paragraph. Same situation as `HL/Imp.lean:230`; most
    likely a cull.

### TS/Stlc.lean

- [ ] **L902–L906** — `section` / `set_option hygiene false in` / `local macro_rules (kind := tmBracket)` introducing the substitution bracket
  - Suggested summary: `"Notation encoding: substitution, hygiene setup"`
  - Prose signal: the file's own framing at L385–L386 — "How that works is in the collapsed blocks below; nothing later in the chapter depends on it."
  - Confidence: medium
  - Caveat: requires splitting the fenced block L901–L929 so `def subst`
    (L908–L923) stays visible. This is precisely the shape already used at
    L1655–L1662 / L1664–L1682 / L1684–L1695 in the same file, so it makes the
    chapter internally consistent.

- [ ] **L924–L928** — `end` closing the hygiene-off section, plus the hygienic re-declaration of the substitution `macro_rules`
  - Suggested summary: `"Notation encoding: substitution, for real"`
  - Prose signal: same as above; compare the existing `"Notation encoding: the judgment, for real"` at L1684
  - Confidence: medium
  - Caveat: the second half of the same split. Apply together with the L902–L906
    entry, or cull both.

---

## Summary

| Volume | Files scanned | High | Medium | Low | Total |
| ------ | ------------- | ---- | ------ | --- | ----- |
| LF     | 12            | 2    | 0      | 3   | 5     |
| HL     | 4             | 5    | 7      | 7   | 19    |
| TS     | 5             | 1    | 3      | 1   | 5     |
| **All**| **21**        | **8**| **10** |**11**| **29**|

### Coverage notes

* **Scanned** (all 21 chapter files reachable from `LF.lean`, `HL.lean`, `TS.lean`):
  `LF/{Preface,Basics,Induction,UsingLean,Lists,Poly,Tactics,Logic,IndProp,Automation,Typeclasses,Postscript}.lean`,
  `HL/{Preface,Slang,Imp,Hoare}.lean`,
  `TS/{Preface,Slang,Smallstep,Types,Stlc}.lean`.
  All of these are already Verso-format sources included directly in the `#doc`.
* **Skipped, generated / unregistered**: `LF/LogicVerso.lean`,
  `LF/IndPropVerso.lean`, `LF/IndPropRegexpVerso.lean`, `LF/MapsVerso.lean` — none
  is imported by `LF.lean`; the first two are stale `to_verso` output whose
  hand-maintained counterparts (`LF/Logic.lean`, `LF/IndProp.lean`) *are* in the
  book, and the other two are unregistered drafts.
* **Skipped, not chapters**: `LF/Scratch.lean`, `LF/CustomTactics.lean` (tactic
  infrastructure, not book text), all of `SFLMeta/`, `old/`, `_out/`.
* **Files with no candidates**: `LF/Preface.lean`, `LF/Induction.lean`,
  `LF/UsingLean.lean`, `LF/Poly.lean`, `LF/Tactics.lean`, `LF/Logic.lean`,
  `LF/IndProp.lean`, `LF/Postscript.lean`, `HL/Preface.lean`, `HL/Slang.lean`,
  `TS/Preface.lean`, `TS/Slang.lean`, `TS/Smallstep.lean`. These chapters contain
  no metaprogramming beyond one-line `scoped notation` declarations that the prose
  introduces as content.
* `HL/Slang.lean` and `TS/Slang.lean` are byte-identical; anything applied to one
  must be applied to the other. (Neither has candidates, so this is moot for now.)
