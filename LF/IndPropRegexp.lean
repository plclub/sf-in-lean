-- IndPropRegexp: Regular Expressions (Case Study from IndProp)

/- Claude: PERFORMANCE NOTE (Claude-generated) — why the generated
   `IndPropRegexpVerso` build carries document-level `maxHeartbeats` and
   `maxRecDepth` options (emitted by `DOC_LEVEL_OPTIONS["IndPropRegexp"]` in
   `scripts/to_verso.py`). Nothing below has been executed beyond the two
   experiments explicitly marked VERIFIED.

   Symptom. The bare chapter (`LF/IndPropRegexp.lean`) builds at Lean's
   defaults, but the generated Verso chapter fails with (1) a `(deterministic)
   timeout at isDefEq` on `weak_pumping_app`, and (2) once heartbeats are
   raised, `maximum recursion depth reached in the code generator` plus a
   `noncomputable ... block✝` error on the deep `::::::full` sections.

   Root cause — both limits are hit in DOCUMENT-SCOPED passes, not in the proofs
   themselves:
   - Heartbeats: Verso's InlineLean re-drives elaboration during syntax
     highlighting (attaching type/hover info per token). The pumping proofs are
     heavy enough that highlighting `weak_pumping_app` alone exceeds the default
     200000. The budget resets per top-level declaration, not per block.
   - Recursion depth: the Lean code generator walks the generated
     `Verso.Doc.Block` document term; this chapter's deep directive nesting
     (`::::::full` around `:::::exercise` around code) overflows the default
     limit, and the dependent def then reports as noncomputable.

   Alternatives considered (why the obvious ones do NOT work):
   - Splitting the big `lean` code block into smaller blocks: VERIFIED not to
     help. Isolating `weak_pumping_app` in its own block still times out at
     200000 — the budget is per-declaration, and that one proof is over budget
     by itself.
   - Scoping the bump with `set_option maxHeartbeats ... in` on the theorem:
     VERIFIED not to help. The cost is in the highlighting pass, which runs
     after the command and honors only document-level options, not a
     per-theorem `... in`.
   - Slimming `weak_pumping_app`'s proof (fewer broad `simp`/`omega` calls):
     would cut the heartbeat cost but not the recursion-depth cost.

   Current fix. `DOC_LEVEL_OPTIONS["IndPropRegexp"]` emits, just before `#doc`,
   `set_option maxHeartbeats 2000000` and `set_option maxRecDepth 100000`. Other
   chapters are untouched.

   Proposed next step (NOT yet done). Extract the heavy `App` case of
   `weak_pumping_app` into a named helper lemma — the same pattern the chapter
   already uses for `star_app` (`star_app_aux`) and `mstar''` (`mstar''_aux`).
   That turns one over-budget declaration into several under-budget ones, each
   highlighted against its own fresh 200000 budget, and would likely let us drop
   the `maxHeartbeats` override. Caveats: (a) it does NOT remove the
   `maxRecDepth` line, which is driven by document nesting depth and is
   independent of any single proof; (b) each extracted lemma must itself stay
   under 200000 (confirm empirically); (c) it edits verbatim SF exercise proofs,
   so it is a small pedagogy call, not a purely mechanical change. -/

-- HIDEFROMHTML
import LF.IndProp
-- /HIDEFROMHTML

set_option linter.unusedSimpArgs false

-- BCP: Recheck title -- should just be called Regexp.lean

-- ########################################################
-- * Case Study: Regular Expressions

-- ** Definitions

-- Regular expressions are a natural language for describing sets of
-- strings. Their syntax is defined as follows:

inductive RegExp (α : Type) : Type where
  | EmptySet
  | EmptyStr
  | Char (c : α)
  | App (r1 r2 : RegExp α)
  | Union (r1 r2 : RegExp α)
  | Star (r : RegExp α)
deriving BEq, DecidableEq, Repr

-- Note that this definition is _polymorphic_: Regular
-- expressions in `RegExp α` describe strings with characters drawn
-- from `α` -- which in this exercise we represent as _lists_ with
-- elements from `α`.

-- We connect regular expressions and strings by defining when a
-- regular expression _matches_ some string:

open RegExp in
inductive ExpMatch {α : Type} : List α → RegExp α → Prop where
  | MEmpty : ExpMatch [] EmptyStr
  | MChar (c : α) : ExpMatch [c] (Char c)
  | MApp {s1 : List α} {re1 : RegExp α} {s2 : List α} {re2 : RegExp α}
         (h1 : ExpMatch s1 re1) (h2 : ExpMatch s2 re2)
       : ExpMatch (s1 ++ s2) (App re1 re2)
  | MUnionL {s1 : List α} {re1 : RegExp α} (re2 : RegExp α)
            (h1 : ExpMatch s1 re1) : ExpMatch s1 (Union re1 re2)
  | MUnionR {s2 : List α} (re1 : RegExp α) {re2 : RegExp α}
            (h2 : ExpMatch s2 re2) : ExpMatch s2 (Union re1 re2)
  | MStar0 (re : RegExp α) : ExpMatch [] (Star re)
  | MStarApp {s1 s2 : List α} {re : RegExp α}
             (h1 : ExpMatch s1 re) (h2 : ExpMatch s2 (Star re))
           : ExpMatch (s1 ++ s2) (Star re)

-- Notation: `s =~ re` for `ExpMatch s re`
infix:40 " =~ " => ExpMatch

-- Notice that the clause "EmptySet does not match any string" is not
-- explicitly reflected in the definition. The _lack_ of a rule gives
-- us the behavior we want.

-- Because `ExpMatch` is an inductive family with non-trivial indices
-- (involving `List.append`), Lean's `cases` tactic sometimes has
-- trouble with dependent elimination. We provide inversion lemmas
-- that work around this.

-- Inversion: nothing matches EmptySet
theorem ExpMatch.not_emptySet {α : Type} {s : List α} :
    ¬ (s =~ RegExp.EmptySet) := by
  intro h
  generalize heq : RegExp.EmptySet = re at h
  induction h <;> simp at heq

-- Inversion: EmptyStr matches only []
theorem ExpMatch.emptyStr_inv {α : Type} {s : List α}
    (h : s =~ RegExp.EmptyStr) : s = [] := by
  generalize heq : RegExp.EmptyStr = re at h
  induction h <;> simp at heq; rfl

-- Inversion: Char c matches only [c]
theorem ExpMatch.char_inv {α : Type} {s : List α} {c : α}
    (h : s =~ RegExp.Char c) : s = [c] := by
  generalize heq : RegExp.Char c = re at h
  induction h with
  | MChar c' => exact RegExp.Char.inj heq ▸ rfl
  | _ => simp at heq

-- Inversion: App
theorem ExpMatch.app_inv {α : Type} {s : List α} {re1 re2 : RegExp α}
    (h : s =~ RegExp.App re1 re2) :
    ∃ s1 s2, s = s1 ++ s2 ∧ s1 =~ re1 ∧ s2 =~ re2 := by
  generalize heq : RegExp.App re1 re2 = re at h
  induction h with
  | MApp h1 h2 _ _ =>
    obtain ⟨rfl, rfl⟩ := RegExp.App.inj heq
    exact ⟨_, _, rfl, h1, h2⟩
  | _ => simp at heq

-- Inversion: Union
theorem ExpMatch.union_inv {α : Type} {s : List α} {re1 re2 : RegExp α}
    (h : s =~ RegExp.Union re1 re2) : s =~ re1 ∨ s =~ re2 := by
  generalize heq : RegExp.Union re1 re2 = re at h
  induction h with
  | MUnionL _ h1 _ =>
    obtain ⟨rfl, rfl⟩ := RegExp.Union.inj heq; left; exact h1
  | MUnionR _ h2 _ =>
    obtain ⟨rfl, rfl⟩ := RegExp.Union.inj heq; right; exact h2
  | _ => simp at heq

-- ** Examples

-- reg_exp_ex1
example : [1] =~ RegExp.Char 1 :=
  ExpMatch.MChar 1

-- reg_exp_ex2
example : [1, 2] =~ RegExp.App (RegExp.Char 1) (RegExp.Char 2) :=
  ExpMatch.MApp (ExpMatch.MChar 1) (ExpMatch.MChar 2)

-- reg_exp_ex3
example : ¬ ([1, 2] =~ RegExp.Char 1) := by
  intro h; have := ExpMatch.char_inv h; simp at this

-- FULL
def regExpOfList {α : Type} (l : List α) : RegExp α :=
  match l with
  | [] => RegExp.EmptyStr
  | x :: l' => RegExp.App (RegExp.Char x) (regExpOfList l')

-- reg_exp_ex4
example : [1, 2, 3] =~ regExpOfList [1, 2, 3] := by
  simp [regExpOfList]
  apply ExpMatch.MApp (ExpMatch.MChar 1)
  apply ExpMatch.MApp (ExpMatch.MChar 2)
  apply ExpMatch.MApp (ExpMatch.MChar 3)
  exact ExpMatch.MEmpty
-- /FULL

-- MStar1
theorem mstar1 {α : Type} {s : List α} {re : RegExp α}
    (h : s =~ re) : s =~ RegExp.Star re := by
  rw [show s = s ++ [] from by simp]
  exact ExpMatch.MStarApp h (ExpMatch.MStar0 re)

-- FULL
-- EX3 (exp_match_ex1)
-- GRADE_THEOREM 0.5: EmptySet_is_empty
-- GRADE_THEOREM 0.5: MUnion'
-- GRADE_THEOREM 2: MStar'

-- emptySet_is_empty
theorem emptySet_is_empty {α : Type} (s : List α) :
    ¬ (s =~ RegExp.EmptySet) :=
  -- ADMITTED
  ExpMatch.not_emptySet
  -- /ADMITTED

-- MUnion'
theorem munion' {α : Type} {s : List α} {re1 re2 : RegExp α}
    (h : s =~ re1 ∨ s =~ re2) : s =~ RegExp.Union re1 re2 := by
  -- ADMITTED
  rcases h with h1 | h2
  · exact ExpMatch.MUnionL re2 h1
  · exact ExpMatch.MUnionR re1 h2
  -- /ADMITTED

-- MStar'
theorem mstar' {α : Type} {ss : List (List α)} {re : RegExp α}
    (h : ∀ s, s ∈ ss → s =~ re) :
    ss.foldr (· ++ ·) [] =~ RegExp.Star re := by
  -- ADMITTED
  induction ss with
  | nil => exact ExpMatch.MStar0 re
  | cons s ss' ih =>
    simp [List.foldr]
    apply ExpMatch.MStarApp
    · exact h s (List.Mem.head ss')
    · exact ih (fun s' hs' => h s' (List.Mem.tail s hs'))
  -- /ADMITTED
-- [] (end exp_match_ex1)
-- /FULL

-- The main theorem: characters in matched strings appear in the regex.

def reChars {α : Type} (re : RegExp α) : List α :=
  match re with
  | RegExp.EmptySet => []
  | RegExp.EmptyStr => []
  | RegExp.Char x => [x]
  | RegExp.App re1 re2 => reChars re1 ++ reChars re2
  | RegExp.Union re1 re2 => reChars re1 ++ reChars re2
  | RegExp.Star re => reChars re

-- in_re_match
-- WORKINCLASS
theorem in_re_match {α : Type} {s : List α} {re : RegExp α} {x : α}
    (hmatch : s =~ re) (hin : x ∈ s) : x ∈ reChars re := by
  induction hmatch with
  | MEmpty => simp at hin
  | MChar c => simp [reChars]; simp at hin; exact hin
  | MApp h1 h2 ih1 ih2 =>
    simp [reChars, List.mem_append]
    simp [List.mem_append] at hin
    rcases hin with hin1 | hin2
    · left; exact ih1 hin1
    · right; exact ih2 hin2
  | MUnionL _ h1 ih =>
    simp [reChars, List.mem_append]; left; exact ih hin
  | MUnionR _ h2 ih =>
    simp [reChars, List.mem_append]; right; exact ih hin
  | MStar0 => simp at hin
  | MStarApp h1 h2 ih1 ih2 =>
    simp [reChars, List.mem_append] at hin ⊢
    rcases hin with hin1 | hin2
    · exact ih1 hin1
    · exact ih2 hin2
-- /WORKINCLASS

-- FULL
-- EX4 (re_not_empty)
-- GRADE_THEOREM 3: re_not_empty
-- GRADE_THEOREM 3: re_not_empty_correct

-- ADMITDEF
def reNotEmpty {α : Type} (re : RegExp α) : Bool :=
  match re with
  | RegExp.EmptySet => false
  | RegExp.EmptyStr => true
  | RegExp.Char _ => true
  | RegExp.App re1 re2 => reNotEmpty re1 && reNotEmpty re2
  | RegExp.Union re1 re2 => reNotEmpty re1 || reNotEmpty re2
  | RegExp.Star _ => true
-- /ADMITDEF

-- re_not_empty_correct
theorem re_not_empty_correct {α : Type} (re : RegExp α) :
    (∃ s, s =~ re) ↔ reNotEmpty re = true := by
  -- ADMITTED
  induction re with
  | EmptySet =>
    simp [reNotEmpty]; intro s h; exact absurd h ExpMatch.not_emptySet
  | EmptyStr =>
    simp [reNotEmpty]; exact ⟨[], ExpMatch.MEmpty⟩
  | Char x =>
    simp [reNotEmpty]; exact ⟨[x], ExpMatch.MChar x⟩
  | App re1 re2 ih1 ih2 =>
    simp [reNotEmpty, Bool.and_eq_true]
    constructor
    · rintro ⟨s, h⟩
      obtain ⟨s1, s2, _, h1, h2⟩ := ExpMatch.app_inv h
      exact ⟨ih1.mp ⟨_, h1⟩, ih2.mp ⟨_, h2⟩⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨s1, hs1⟩ := ih1.mpr h1
      obtain ⟨s2, hs2⟩ := ih2.mpr h2
      exact ⟨s1 ++ s2, ExpMatch.MApp hs1 hs2⟩
  | Union re1 re2 ih1 ih2 =>
    simp [reNotEmpty, Bool.or_eq_true]
    constructor
    · rintro ⟨s, h⟩
      rcases ExpMatch.union_inv h with h1 | h2
      · left; exact ih1.mp ⟨_, h1⟩
      · right; exact ih2.mp ⟨_, h2⟩
    · rintro (h1 | h2)
      · obtain ⟨s, hs⟩ := ih1.mpr h1; exact ⟨s, ExpMatch.MUnionL _ hs⟩
      · obtain ⟨s, hs⟩ := ih2.mpr h2; exact ⟨s, ExpMatch.MUnionR _ hs⟩
  | Star re _ =>
    simp [reNotEmpty]; exact ⟨[], ExpMatch.MStar0 re⟩
  -- /ADMITTED
-- [] (end re_not_empty)
-- /FULL

-- ** The `remember` / `generalize` pattern

-- When doing induction on evidence for `ExpMatch`, we sometimes need
-- to remember that the regex has specific structure (e.g., `Star re`).
-- In Lean 4, we achieve this by factoring the proof into a helper
-- lemma where the regex is a parameter and the equation is a hypothesis.

-- star_app (helper)
private theorem star_app_aux {α : Type} {s1 : List α} {re : RegExp α}
    (re' : RegExp α) (h1 : s1 =~ re') (heq : re' = RegExp.Star re) :
    ∀ s2, s2 =~ RegExp.Star re → s1 ++ s2 =~ RegExp.Star re := by
  induction h1 with
  | MEmpty => simp at heq
  | MChar => simp at heq
  | MApp _ _ => simp at heq
  | MUnionL _ _ => simp at heq
  | MUnionR _ _ => simp at heq
  | MStar0 => intro s2 h2; simp; exact h2
  | MStarApp hmatch1 _ _ ih2 =>
    obtain rfl := RegExp.Star.inj heq
    intro s2 h2
    rw [List.append_assoc]
    exact ExpMatch.MStarApp hmatch1 (ih2 rfl _ h2)

-- star_app
theorem star_app {α : Type} {s1 s2 : List α} {re : RegExp α}
    (h1 : s1 =~ RegExp.Star re) (h2 : s2 =~ RegExp.Star re) :
    s1 ++ s2 =~ RegExp.Star re :=
  star_app_aux _ h1 rfl _ h2

-- FULL
-- EX4? (exp_match_ex2)

-- MStar'' (helper)
private theorem mstar''_aux {α : Type} {s : List α} {re : RegExp α}
    (re' : RegExp α) (h : s =~ re') (heq : re' = RegExp.Star re) :
    ∃ ss : List (List α),
      s = ss.foldr (· ++ ·) [] ∧ ∀ s', s' ∈ ss → s' =~ re := by
  induction h with
  | MEmpty => simp at heq
  | MChar => simp at heq
  | MApp _ _ => simp at heq
  | MUnionL _ _ => simp at heq
  | MUnionR _ _ => simp at heq
  | MStar0 =>
    exact ⟨[], rfl, fun _ h => by simp at h⟩
  | MStarApp hmatch1 _ _ ih2 =>
    obtain rfl := RegExp.Star.inj heq
    obtain ⟨ss, hfold, hall⟩ := ih2 rfl
    exact ⟨_ :: ss, by simp only [List.foldr]; rw [← hfold],
      fun s' hs' => by
        simp only [List.mem_cons] at hs'
        rcases hs' with rfl | hs'
        · exact hmatch1
        · exact hall s' hs'⟩

-- MStar''
theorem mstar'' {α : Type} {s : List α} {re : RegExp α}
    (h : s =~ RegExp.Star re) :
    ∃ ss : List (List α),
      s = ss.foldr (· ++ ·) [] ∧ ∀ s', s' ∈ ss → s' =~ re :=
  -- ADMITTED
  mstar''_aux _ h rfl
  -- /ADMITTED
-- [] (end exp_match_ex2)

-- ** The "Weak" Pumping Lemma

namespace Pumping

def pumpingConstant {α : Type} (re : RegExp α) : Nat :=
  match re with
  | RegExp.EmptySet => 1
  | RegExp.EmptyStr => 1
  | RegExp.Char _ => 2
  | RegExp.App re1 re2 => pumpingConstant re1 + pumpingConstant re2
  | RegExp.Union re1 re2 => pumpingConstant re1 + pumpingConstant re2
  | RegExp.Star r => pumpingConstant r

theorem pumping_constant_ge_1 {α : Type} (re : RegExp α) :
    pumpingConstant re ≥ 1 := by
  induction re with
  | EmptySet => simp [pumpingConstant]
  | EmptyStr => simp [pumpingConstant]
  | Char _ => simp [pumpingConstant]
  | App re1 _ ih1 _ => simp [pumpingConstant]; omega
  | Union re1 _ ih1 _ => simp [pumpingConstant]; omega
  | Star _ ih => simp [pumpingConstant]; exact ih

theorem pumping_constant_0_false {α : Type} (re : RegExp α)
    (h : pumpingConstant re = 0) : False := by
  have := pumping_constant_ge_1 re; omega

def napp {α : Type} (n : Nat) (l : List α) : List α :=
  match n with
  | 0 => []
  | n' + 1 => l ++ napp n' l

theorem napp_plus {α : Type} (n m : Nat) (l : List α) :
    napp (n + m) l = napp n l ++ napp m l := by
  induction n with
  | zero => simp [napp]
  | succ n ih =>
    simp only [Nat.succ_add, napp]
    rw [ih, List.append_assoc]

theorem napp_star {α : Type} {m : Nat} {s1 s2 : List α} {re : RegExp α}
    (hs1 : s1 =~ re) (hs2 : s2 =~ RegExp.Star re) :
    napp m s1 ++ s2 =~ RegExp.Star re := by
  induction m with
  | zero => simp [napp]; exact hs2
  | succ m ih =>
    simp only [napp]
    rw [List.append_assoc]
    exact ExpMatch.MStarApp hs1 ih

-- EX5A? (pumping)
-- The (weak) pumping lemma. Advanced exercise.

theorem weak_pumping_char : ∀ {α : Type} (x : α),
  pumpingConstant (.Char x) <= List.length [x] ->
  ∃ s1 s2 s3 : List α,
    [x] = s1 ++ s2 ++ s3 ∧ s2 ≠ [ ] ∧
    (∀ m : Nat, s1 ++ napp m s2 ++ s3 =~ .Char x) := by
  -- ADMITTED
  intro α x contra
  simp [pumpingConstant] at contra
  -- /ADMITTED

theorem weak_pumping_app : ∀ {α : Type}
                         (s1 s2 : List α) (re1 re2 : RegExp α),
  s1 =~ re1 ->
  s2 =~ re2 ->
  (pumpingConstant re1 <= List.length s1 ->
  ∃ s2 s3 s4 : List α,
    s1 = s2 ++ s3 ++ s4 /\
    s3 ≠ [ ] /\
    (∀ m : Nat, s2 ++ napp m s3 ++ s4 =~ re1)) ->
  (pumpingConstant re2 <= List.length s2 ->
    ∃ s1 s3 s4 : List α,
      s2 = s1 ++ s3 ++ s4 /\
      s3 ≠ [ ] /\
      (∀ m : Nat, s1 ++ napp m s3 ++ s4 =~ re2)) ->
  pumpingConstant (.App re1 re2) <= List.length (s1 ++ s2) ->
  ∃ s0 s3 s4 : List α,
    s1 ++ s2 = s0 ++ s3 ++ s4 /\
    s3 ≠ [ ] /\
    (∀ m : Nat, s0 ++ napp m s3 ++ s4 =~ .App re1 re2) := by
  intro α s1 s2 re1 re2 Hmatch1 Hmatch2 IH1 IH2 Hlen
  obtain H | H :
    pumpingConstant re1 <= List.length s1 ∨ pumpingConstant re2 <= List.length s2 := by
  -- ADMITTED
    rw [app_length] at Hlen
    apply add_le_cases
    apply Hlen
  -- /ADMITTED
  . specialize IH1 H
    let ⟨s12, s13, s14, H1, H2, H3⟩ := IH1
    rw [H1]
    exists s12; exists s13; exists (s14 ++ s2)
    constructor
    . rw [←List.append_assoc]
    constructor
    . assumption
    . intro m; specialize H3 m
      rw [←List.append_assoc]
      apply ExpMatch.MApp
      assumption
      assumption
  . specialize IH2 H
    let ⟨s21, s22, s23, H1, H2, H3⟩ := IH2
    rw [H1]
    exists (s1 ++ s21); exists s22; exists s23
    constructor
    . rw [←List.append_assoc, ←List.append_assoc]
    constructor
    . assumption
    . intro m; specialize H3 m
      rw [List.append_assoc, List.append_assoc]
      apply ExpMatch.MApp
      assumption
      rw [←List.append_assoc]
      assumption

theorem weak_pumping_union_l :  ∀ {α : Type} (s1 : List α) (re1 re2 : RegExp α),
  s1 =~ re1 ->
  (pumpingConstant re1 <= List.length s1 ->
    ∃ s2 s3 s4 : List α,
      s1 = s2 ++ s3 ++ s4 /\
      s3 ≠ [ ] /\
      (∀ m : Nat, s2 ++ napp m s3 ++ s4 =~ re1)) ->
  pumpingConstant (.Union re1 re2) <= List.length s1 ->
  ∃ s0 s2 s3 : List α,
    s1 = s0 ++ s2 ++ s3 /\
    s2 ≠ [ ] /\
    (∀ m : Nat, s0 ++ napp m s2 ++ s3 =~ .Union re1 re2) := by
  intro α s1 re1 re2 Hmatch IH Hlen
  have H : pumpingConstant re1 <= List.length s1 := by
  -- ADMITTED
    simp only [pumpingConstant] at Hlen
    apply Nat.le_trans _ Hlen
    exact Nat.le_add_right _ _
  -- /ADMITTED
  -- ADMITTED
  specialize IH H
  let ⟨s11, s12, s13, H1, H2, H3⟩ := IH
  exists s11; exists s12; exists s13
  constructor
  . assumption
  constructor
  . assumption
  . intro m; specialize H3 m
    apply ExpMatch.MUnionL
    assumption
  -- /ADMITTED

theorem weak_pumping_union_r : ∀ {α : Type} (s2 : List α) (re1 re2 : RegExp α),
  s2 =~ re2 ->
  (pumpingConstant re2 <= List.length s2 ->
    ∃ s1 s3 s4 : List α,
      s2 = s1 ++ s3 ++ s4 /\
      s3 ≠ [ ] /\
      (∀ m : Nat, s1 ++ napp m s3 ++ s4 =~ re2)) ->
  pumpingConstant (.Union re1 re2) <= List.length s2 ->
  ∃ s1 s0 s3 : List α,
    s2 = s1 ++ s0 ++ s3 /\
    s0 ≠ [ ] /\
    (∀ m : Nat, s1 ++ napp m s0 ++ s3 =~ .Union re1 re2) := by
  -- symmetric to the previous
  intro α s2 re1 re2 Hmatch IH Hlen
  have H : pumpingConstant re2 <= List.length s2 := by
  -- ADMITTED
    simp only [pumpingConstant] at Hlen
    apply Nat.le_trans _ Hlen
    exact Nat.le_add_left _ _
  -- /ADMITTED
  -- ADMITTED
  specialize IH H
  let ⟨s21, s22, s23, H1, H2, H3⟩ := IH
  exists s21; exists s22; exists s23
  constructor
  . assumption
  constructor
  . assumption
  . intro m; specialize H3 m
    apply ExpMatch.MUnionR
    assumption
  -- /ADMITTED

theorem weak_pumping_star_zero : ∀ {α : Type} (re : RegExp α),
  pumpingConstant (.Star re) <= @List.length α [] ->
  ∃ s1 s2 s3 : List α,
    [ ] = s1 ++ s2 ++ s3 /\
    s2 ≠ [ ] /\
    (∀ m : Nat, s1 ++ napp m s2 ++ s3 =~ .Star re) := by
  -- ADMITTED
  intro α re Hp
  simp only [List.length_nil] at Hp
  -- TODO (DHS): On the face of it it's kind of strange that generalizing like this
  -- is necessary; in the Rocq version of this we teach students to think about inversion
  -- like flipping the inference rule; i.e., given the fact that I know H, what can I
  -- conclude must have been true in order for H to be true. Needing to generalize
  -- our hypothesis is a bit weird when we think about inversion this way. How to explain?
  generalize h : 0 = k at Hp
  cases Hp
  case step => cases h
  case refl =>
    have h2 := pumping_constant_ge_1 re
    simp only [pumpingConstant] at h
    rw [← h] at h2; cases h2
  -- /ADMITTED

theorem weak_pumping_star_app : ∀ {α : Type}  (s1 s2 : List α) (re : RegExp α),
  s1 =~ re ->
  s2 =~ .Star re ->
  (pumpingConstant re <= List.length s1 ->
    ∃ s2 s3 s4 : List α,
      s1 = s2 ++ s3 ++ s4
      /\ s3  ≠ [ ] /\
      (∀ m : Nat, s2 ++ napp m s3 ++ s4 =~ re)) ->
  (pumpingConstant (.Star re) <= List.length s2 ->
    ∃ s1 s3 s4 : List α,
      s2 = s1 ++ s3 ++ s4 /\
      s3  ≠ [ ] /\
      (∀ m : Nat, s1 ++ napp m s3 ++ s4 =~ .Star re)) ->
  pumpingConstant (.Star re) <= List.length (s1 ++ s2) ->
  ∃ s0 s3 s4 : List α,
    s1 ++ s2 = s0 ++ s3 ++ s4 /\
    s3  ≠ [ ] /\
    (∀ m : Nat, s0 ++ napp m s3 ++ s4 =~ .Star re)  := by
  -- ADMITTED
  intro T s1 s2 re Hmatch1 Hmatch2 IH1 IH2 Hlen
  rw [app_length] at *
  obtain Hs1len0 | ⟨s1len, Hs1re1⟩ | Hs1re1 :
    (List.length s1 = 0
      ∨ (List.length s1 ≠ 0 /\ List.length s1 < pumpingConstant re)
      ∨ pumpingConstant re <= List.length s1) := by
    cases s1
    . left; rfl
    . case cons h s1' =>
      right
      have Hcases : (List.length (h :: s1') < pumpingConstant re
                    \/ pumpingConstant re <= List.length (h :: s1')) := by
        apply lt_ge_cases
      cases Hcases
      . left; constructor
        . intro contra
          contradiction
        . assumption
      . right; assumption
  . have Hs1nil : s1 = [] := by
      cases s1; rfl; contradiction
    subst Hs1nil
    simp only [List.length_nil, Nat.zero_add] at Hlen
    apply IH2; apply Hlen
  . exists []; exists s1; exists s2
    constructor; rfl
    constructor
    . intro contra; subst contra; contradiction
    . intro m; apply napp_star
      assumption
      assumption
  . specialize IH1 Hs1re1
    let ⟨s11, s12, s13, H1, H2, H3⟩ := IH1
    exists s11; exists s12; exists (s13 ++ s2)
    rw [H1]
    constructor
    . rw [List.append_assoc]
    constructor
    . assumption
    . intro m; specialize H3 m
      rw [←List.append_assoc]
      apply ExpMatch.MStarApp
      . assumption
      . assumption
  -- /ADMITTED

theorem weak_pumping {α : Type} {re : RegExp α} {s : List α}
    (hmatch : s =~ re) (hlen : pumpingConstant re ≤ s.length) :
    ∃ s1 s2 s3 : List α,
      s = s1 ++ s2 ++ s3 ∧ s2 ≠ [] ∧
      ∀ m, s1 ++ napp m s2 ++ s3 =~ re := by
  -- ADMITTED
  induction hmatch
  . simp [pumpingConstant] at hlen
  . apply weak_pumping_char; assumption
  . apply weak_pumping_app <;> assumption
  . apply weak_pumping_union_l <;> assumption
  . apply weak_pumping_union_r <;> assumption
  . apply weak_pumping_star_zero <;> assumption
  . apply weak_pumping_star_app <;> assumption
  -- /ADMITTED

-- The (strong) pumping lemma.

theorem pumping {α : Type} {re : RegExp α} {s : List α}
    (_hmatch : s =~ re) (_hlen : pumpingConstant re ≤ s.length) :
    ∃ s1 s2 s3 : List α,
      s = s1 ++ s2 ++ s3 ∧ s2 ≠ [] ∧
      s1.length + s2.length ≤ pumpingConstant re ∧
      ∀ m, s1 ++ napp m s2 ++ s3 =~ re := by
  -- ADMITTED
  sorry
  -- /ADMITTED

end Pumping
-- [] (end pumping)
-- /FULL

-- #######################################################
-- * Case Study: Improving Reflection

-- ** The `Reflect` type

-- In Lean, the `Decidable` typeclass serves a similar role. But for
-- pedagogical purposes, we define a custom `Reflect` type:

inductive Reflect (P : Prop) : Bool → Prop where
  | ReflectT (h : P) : Reflect P true
  | ReflectF (h : ¬P) : Reflect P false

-- iff_reflect
-- WORKINCLASS
theorem iff_reflect {P : Prop} {b : Bool} (h : P ↔ b = true) :
    Reflect P b := by
  cases b with
  | true => exact Reflect.ReflectT (h.mpr rfl)
  | false =>
    apply Reflect.ReflectF
    intro hp; have := h.mp hp; contradiction
-- /WORKINCLASS

-- FULL
-- EX2! (reflect_iff)
theorem reflect_iff {P : Prop} {b : Bool} (h : Reflect P b) :
    P ↔ b = true := by
  -- ADMITTED
  cases h with
  | ReflectT hp => exact ⟨fun _ => rfl, fun _ => hp⟩
  | ReflectF hnp =>
    exact ⟨fun hp => absurd hp hnp, fun hf => by contradiction⟩
  -- /ADMITTED
-- [] (end reflect_iff)
-- /FULL

-- eqbP
theorem eqbP (n m : Nat) : Reflect (n = m) (n == m) := by
  apply iff_reflect
  simp [BEq.beq, Nat.beq_eq]

-- filter_not_empty_In'
theorem filter_not_empty_In' (n : Nat) (l : List Nat)
    (h : List.filter (fun x => n == x) l ≠ []) : n ∈ l := by
  induction l with
  | nil => simp at h
  | cons m l' ih =>
    simp only [List.mem_cons]
    match hb : n == m, eqbP n m with
    | true, Reflect.ReflectT heq => left; exact heq
    | false, Reflect.ReflectF _ =>
      right; apply ih
      change List.filter (fun x => n == x) l' ≠ []
      simpa [List.filter, hb] using h

-- FULL
-- EX3! (eqbP_practice)

def count (n : Nat) (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | m :: l' => (if n == m then 1 else 0) + count n l'

-- eqbP_practice
theorem eqbP_practice (n : Nat) (l : List Nat)
    (h : count n l = 0) : n ∉ l := by
  -- ADMITTED
  induction l with
  | nil => simp
  | cons m l' ih =>
    simp only [List.mem_cons, not_or]
    match hb : n == m, eqbP n m with
    | true, Reflect.ReflectT heq =>
      simp [count, hb] at h
    | false, Reflect.ReflectF hneq =>
      have hcount : count n l' = 0 := by simp [count, hb] at h; exact h
      exact ⟨hneq, ih hcount⟩
  -- /ADMITTED
-- [] (end eqbP_practice)
-- /FULL

-- FULL
-- #######################################################
-- ** Extended Exercise: A Verified Regular-Expression Matcher

-- Each provable `Prop` is equivalent to `True`.
theorem provable_equiv_true {P : Prop} (h : P) : P ↔ True :=
  ⟨fun _ => trivial, fun _ => h⟩

-- Each `Prop` whose negation is provable is equivalent to `False`.
theorem not_equiv_false' {P : Prop} (h : ¬P) : P ↔ False :=
  ⟨h, False.elim⟩

-- null_matches_none
theorem null_matches_none {α : Type} (s : List α) :
    (s =~ RegExp.EmptySet) ↔ False :=
  not_equiv_false' ExpMatch.not_emptySet

-- empty_matches_eps
theorem empty_matches_eps {α : Type} (s : List α) :
    s =~ RegExp.EmptyStr ↔ s = [] :=
  ⟨ExpMatch.emptyStr_inv, fun h => h ▸ ExpMatch.MEmpty⟩

-- empty_nomatch_ne
theorem empty_nomatch_ne {α : Type} (a : α) (s : List α) :
    (a :: s =~ RegExp.EmptyStr) ↔ False :=
  not_equiv_false' (fun h => by have := ExpMatch.emptyStr_inv h; simp at this)

-- char_nomatch_char
theorem char_nomatch_char {α : Type} {a b : α} (s : List α)
    (hne : b ≠ a) : (b :: s =~ RegExp.Char a) ↔ False :=
  not_equiv_false' (fun h => by
    have hinv := ExpMatch.char_inv h
    -- hinv : b :: s = [a]
    simp at hinv; exact hne hinv.1)

-- char_eps_suffix
theorem char_eps_suffix {α : Type} (a : α) (s : List α) :
    a :: s =~ RegExp.Char a ↔ s = [] :=
  ⟨fun h => by
    have hinv := ExpMatch.char_inv h
    -- hinv : a :: s = [a]
    simp at hinv; exact hinv,
   fun h => h ▸ ExpMatch.MChar a⟩

-- app_exists
theorem app_exists {α : Type} (s : List α) (re0 re1 : RegExp α) :
    s =~ RegExp.App re0 re1 ↔
    ∃ s0 s1, s = s0 ++ s1 ∧ s0 =~ re0 ∧ s1 =~ re1 := by
  constructor
  · exact ExpMatch.app_inv
  · rintro ⟨s0, s1, rfl, h0, h1⟩; exact ExpMatch.MApp h0 h1

-- EX3? (app_ne)
-- app_ne
theorem app_ne {α : Type} (a : α) (s : List α) (re0 re1 : RegExp α) :
    a :: s =~ RegExp.App re0 re1 ↔
    ([] =~ re0 ∧ a :: s =~ re1) ∨
    ∃ s0 s1, s = s0 ++ s1 ∧ a :: s0 =~ re0 ∧ s1 =~ re1 := by
  -- ADMITTED
  rw [app_exists]
  constructor
  · rintro ⟨s0, s1, heq, h0, h1⟩
    cases s0 with
    | nil => left; exact ⟨h0, heq ▸ h1⟩
    | cons b s0' =>
      right
      have : a :: s = (b :: s0') ++ s1 := heq
      simp at this; obtain ⟨rfl, rfl⟩ := this
      exact ⟨s0', s1, rfl, h0, h1⟩
  · rintro (⟨h0, h1⟩ | ⟨s0, s1, rfl, h0, h1⟩)
    · exact ⟨[], a :: s, rfl, h0, h1⟩
    · exact ⟨a :: s0, s1, rfl, h0, h1⟩
  -- /ADMITTED
-- [] (end app_ne)

-- union_disj
theorem union_disj {α : Type} (s : List α) (re0 re1 : RegExp α) :
    s =~ RegExp.Union re0 re1 ↔ s =~ re0 ∨ s =~ re1 :=
  ⟨ExpMatch.union_inv, fun h => h.elim (ExpMatch.MUnionL re1) (ExpMatch.MUnionR re0)⟩

-- Helper lemma for decomposing l1 ++ l2 = a :: s
private theorem append_eq_cons_cases {α : Type} {l1 l2 : List α} {a : α} {s : List α}
    (h : l1 ++ l2 = a :: s) :
    (l1 = [] ∧ l2 = a :: s) ∨ (∃ t, l1 = a :: t ∧ s = t ++ l2) := by
  cases l1 with
  | nil => left; simp at h; exact ⟨rfl, h⟩
  | cons b t => right; simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨t, rfl, rfl⟩

-- EX3? (star_ne)
-- star_ne (helper)
private theorem star_ne_aux {α : Type} (a : α) (s : List α) (re : RegExp α)
    (re' : RegExp α) (s' : List α) (h : s' =~ re')
    (heqs : s' = a :: s) (heqre : re' = RegExp.Star re) :
    ∃ s0 s1, s = s0 ++ s1 ∧ a :: s0 =~ re ∧ s1 =~ RegExp.Star re := by
  induction h generalizing s with
  | MEmpty => simp at heqre
  | MChar => simp at heqre
  | MApp _ _ => simp at heqre
  | MUnionL _ _ => simp at heqre
  | MUnionR _ _ => simp at heqre
  | MStar0 => simp at heqs
  | MStarApp h1 h2 _ ih2 =>
    obtain rfl := RegExp.Star.inj heqre
    rcases append_eq_cons_cases heqs with ⟨rfl, rfl⟩ | ⟨t, rfl, rfl⟩
    · exact ih2 s rfl rfl
    · exact ⟨t, _, rfl, h1, h2⟩

-- star_ne
theorem star_ne {α : Type} (a : α) (s : List α) (re : RegExp α) :
    a :: s =~ RegExp.Star re ↔
    ∃ s0 s1, s = s0 ++ s1 ∧ a :: s0 =~ re ∧ s1 =~ RegExp.Star re := by
  -- ADMITTED
  constructor
  · intro h; exact star_ne_aux a s re _ _ h rfl rfl
  · rintro ⟨s0, s1, rfl, h0, h1⟩; exact ExpMatch.MStarApp h0 h1
  -- /ADMITTED
-- [] (end star_ne)

-- The definition of our regex matcher will include two fixpoint
-- functions.

def reflMatchesEps (m : RegExp Nat → Bool) : Prop :=
  ∀ re : RegExp Nat, Reflect ([] =~ re) (m re)

-- EX2? (match_eps)
-- ADMITDEF
def matchEps (re : RegExp Nat) : Bool :=
  match re with
  | RegExp.EmptySet => false
  | RegExp.EmptyStr => true
  | RegExp.Char _ => false
  | RegExp.App re0 re1 => matchEps re0 && matchEps re1
  | RegExp.Union re0 re1 => matchEps re0 || matchEps re1
  | RegExp.Star _ => true
-- /ADMITDEF
-- [] (end match_eps)

-- Helper to get Bool value from Reflect
private theorem reflect_true {P : Prop} {b : Bool} (h : P) (hr : Reflect P b) :
    b = true := by
  cases hr with | ReflectT _ => rfl | ReflectF hn => exact absurd h hn

private theorem reflect_false {P : Prop} {b : Bool} (h : ¬P) (hr : Reflect P b) :
    b = false := by
  cases hr with | ReflectT hp => exact absurd hp h | ReflectF _ => rfl

-- EX3? (match_eps_refl)
-- match_eps_refl
theorem match_eps_refl : reflMatchesEps matchEps := by
  -- ADMITTED
  intro re
  induction re with
  | EmptySet =>
    simp [matchEps]; exact Reflect.ReflectF ExpMatch.not_emptySet
  | EmptyStr =>
    simp [matchEps]; exact Reflect.ReflectT ExpMatch.MEmpty
  | Char _ =>
    simp [matchEps]
    exact Reflect.ReflectF (fun h => by have := ExpMatch.char_inv h; simp at this)
  | App re1 re2 ih1 ih2 =>
    simp only [matchEps]
    match hb1 : matchEps re1, ih1 with
    | true, Reflect.ReflectT h1 =>
      match hb2 : matchEps re2, ih2 with
      | true, Reflect.ReflectT h2 =>
        simp [hb1, hb2]; exact Reflect.ReflectT (ExpMatch.MApp h1 h2)
      | false, Reflect.ReflectF h2 =>
        simp [hb1, hb2]
        apply Reflect.ReflectF; intro h
        obtain ⟨s1, s2, heq, _, h2'⟩ := ExpMatch.app_inv h
        simp at heq; obtain ⟨_, rfl⟩ := heq; exact h2 h2'
    | false, Reflect.ReflectF h1 =>
      simp [hb1]
      apply Reflect.ReflectF; intro h
      obtain ⟨s1, s2, heq, h1', _⟩ := ExpMatch.app_inv h
      simp at heq; obtain ⟨rfl, _⟩ := heq; exact h1 h1'
  | Union re1 re2 ih1 ih2 =>
    simp only [matchEps]
    match hb1 : matchEps re1, ih1 with
    | true, Reflect.ReflectT h1 =>
      simp [hb1]; exact Reflect.ReflectT (ExpMatch.MUnionL re2 h1)
    | false, Reflect.ReflectF h1 =>
      match hb2 : matchEps re2, ih2 with
      | true, Reflect.ReflectT h2 =>
        simp [hb1, hb2]; exact Reflect.ReflectT (ExpMatch.MUnionR re1 h2)
      | false, Reflect.ReflectF h2 =>
        simp [hb1, hb2]
        apply Reflect.ReflectF; intro h
        rcases ExpMatch.union_inv h with h' | h'
        · exact h1 h'
        · exact h2 h'
  | Star re _ =>
    simp [matchEps]; exact Reflect.ReflectT (ExpMatch.MStar0 re)
  -- /ADMITTED
-- [] (end match_eps_refl)

-- Regex derivatives.

def isDer {α : Type} (re : RegExp α) (a : α) (re' : RegExp α) : Prop :=
  ∀ s, a :: s =~ re ↔ s =~ re'

def Derives (d : Nat → RegExp Nat → RegExp Nat) : Prop :=
  ∀ a re, isDer re a (d a re)

-- EX3? (derive)
-- ADMITDEF
def derive (a : Nat) (re : RegExp Nat) : RegExp Nat :=
  match re with
  | RegExp.EmptySet => RegExp.EmptySet
  | RegExp.EmptyStr => RegExp.EmptySet
  | RegExp.Char x => if a == x then RegExp.EmptyStr else RegExp.EmptySet
  | RegExp.App re0 re1 =>
    RegExp.Union (RegExp.App (derive a re0) re1)
          (if matchEps re0 then derive a re1 else RegExp.EmptySet)
  | RegExp.Union re0 re1 => RegExp.Union (derive a re0) (derive a re1)
  | RegExp.Star re => RegExp.App (derive a re) (RegExp.Star re)
-- /ADMITDEF
-- [] (end derive)

-- test_der0
example : matchEps (derive 99 RegExp.EmptySet) = false := rfl
-- test_der1
example : matchEps (derive 99 (RegExp.Char 99)) = true := rfl
-- test_der2
example : matchEps (derive 99 (RegExp.Char 100)) = false := rfl
-- test_der3
example : matchEps (derive 99 (RegExp.App (RegExp.Char 99) RegExp.EmptyStr)) = true := rfl
-- test_der4
example : matchEps (derive 99 (RegExp.App RegExp.EmptyStr (RegExp.Char 99))) = true := rfl
-- test_der5
example : matchEps (derive 99 (RegExp.Star (RegExp.Char 99))) = true := rfl
-- test_der6
example : matchEps (derive 100 (derive 99 (RegExp.App (RegExp.Char 99) (RegExp.Char 100)))) = true := rfl
-- test_der7
example : matchEps (derive 100 (derive 99 (RegExp.App (RegExp.Char 100) (RegExp.Char 99)))) = false := rfl

-- EX4? (derive_corr)
-- derive_corr
theorem derive_corr : Derives derive := by
  -- ADMITTED
  intro a re
  unfold isDer
  induction re with
  | EmptySet =>
    intro s; simp [derive]
    exact (null_matches_none _).trans (null_matches_none _).symm
  | EmptyStr =>
    intro s; simp [derive]
    exact (empty_nomatch_ne a s).trans (null_matches_none _).symm
  | Char x =>
    intro s; simp [derive]
    by_cases h : a = x
    · subst h; simp [BEq.beq, Nat.beq_eq]
      exact (char_eps_suffix a s).trans (empty_matches_eps s).symm
    · simp [BEq.beq, Nat.beq_eq, h]
      exact (char_nomatch_char s h).trans (null_matches_none s).symm
  | App re0 re1 ih0 ih1 =>
    intro s
    rw [app_ne a s re0 re1]; simp [derive]
    rw [union_disj, app_exists]
    constructor
    · rintro (⟨h0, h1⟩ | ⟨s0, s1, heq, h0, h1⟩)
      · have hmeps := match_eps_refl re0
        cases hb : matchEps re0 with
        | true =>
          right; rw [hb] at hmeps; exact (ih1 s).mp h1
        | false =>
          rw [hb] at hmeps
          cases hmeps with | ReflectF hn => exact absurd h0 hn
      · left; exact ⟨s0, s1, heq, (ih0 s0).mp h0, h1⟩
    · rintro (⟨s0, s1, heq, h0, h1⟩ | h)
      · right; exact ⟨s0, s1, heq, (ih0 s0).mpr h0, h1⟩
      · have hmeps := match_eps_refl re0
        cases hb : matchEps re0 with
        | true =>
          rw [hb] at hmeps; simp [hb] at h; left
          cases hmeps with | ReflectT hp => exact ⟨hp, (ih1 s).mpr h⟩
        | false =>
          simp [hb] at h
          exact absurd h (null_matches_none s).mp
  | Union re0 re1 ih0 ih1 =>
    intro s; simp [derive]
    constructor
    · intro h
      rcases (union_disj _ _ _).mp h with h' | h'
      · exact (union_disj _ _ _).mpr (Or.inl ((ih0 s).mp h'))
      · exact (union_disj _ _ _).mpr (Or.inr ((ih1 s).mp h'))
    · intro h
      rcases (union_disj _ _ _).mp h with h' | h'
      · exact (union_disj _ _ _).mpr (Or.inl ((ih0 s).mpr h'))
      · exact (union_disj _ _ _).mpr (Or.inr ((ih1 s).mpr h'))
  | Star re ih =>
    intro s; simp [derive]
    rw [star_ne a s re, app_exists]
    exact ⟨fun ⟨s0, s1, h1, h2, h3⟩ => ⟨s0, s1, h1, (ih s0).mp h2, h3⟩,
           fun ⟨s0, s1, h1, h2, h3⟩ => ⟨s0, s1, h1, (ih s0).mpr h2, h3⟩⟩
  -- /ADMITTED
-- [] (end derive_corr)

-- A function `m` _matches regexes_ if it evaluates to a value that
-- reflects whether `re` matches `s`.
def matchesRegex (m : List Nat → RegExp Nat → Bool) : Prop :=
  ∀ (s : List Nat) (re : RegExp Nat), Reflect (s =~ re) (m s re)

-- EX2? (regex_match)
-- ADMITDEF
def regexMatch (s : List Nat) (re : RegExp Nat) : Bool :=
  match s with
  | [] => matchEps re
  | a :: s' => regexMatch s' (derive a re)
-- /ADMITDEF
-- [] (end regex_match)

-- EX3? (regex_match_correct)
-- regex_match_correct
theorem regex_match_correct : matchesRegex regexMatch := by
  -- ADMITTED
  intro s
  induction s with
  | nil => exact match_eps_refl
  | cons a s' ih =>
    intro re
    simp [regexMatch]
    have hr := ih (derive a re)
    match hb : regexMatch s' (derive a re), hr with
    | true, Reflect.ReflectT h =>
      exact Reflect.ReflectT ((derive_corr a re s').mpr h)
    | false, Reflect.ReflectF h =>
      exact Reflect.ReflectF (fun hmatch => h ((derive_corr a re s').mp hmatch))
  -- /ADMITTED
-- [] (end regex_match_correct)
-- /FULL
