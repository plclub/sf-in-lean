import SFLMeta
import TS.Stlc
import LF.CustomTactics
open Verso.Genre Manual
open SFLMeta

#doc (Manual) "StlcProp: Properties of STLC" =>
%%%
tag := "StlcProp"
htmlSplit := .never
file := some "StlcProp"
%%%

:::instructors
This is a good lecture to do mostly at the board (and
therefore not much work has gone into the TERSE version).  It may
be useful to distribute a one-page handout with all the STLC rules for
typing and the step relation, to avoid too much jumping back and
forth on the screen.

Here's a possible cheat sheet:
:::

::::terse
THE SIMPLY TYPED LAMBDA CALCULUS

Syntax:
```bnf
t ::= x ("variable")
    | "λ" x ":" τ "." t ("abstraction")
    | t t ("application")
    | "true" ("constant true")
    | "false" ("constant false")
    | "if" t "then" t "else" t ("conditional") ;
```
Values:
```bnf
v ::= "λ" x ":" τ "." t | "true" | "false" ;
```

Substitution:
```display
[x:=s]x               = s
[x:=s]y               = y                     if x ≠ y
[x:=s](λx:τ. t)       = λx:τ. t
[x:=s](λy:τ. t)       = λy:τ. [x:=s]t         if x ≠ y
[x:=s](t₁ t₂)         = ([x:=s]t₁) ([x:=s]t₂)
[x:=s]true            = true
[x:=s]false           = false
[x:=s](if t₁ then t₂ else t₃) =
                if [x:=s]t₁ then [x:=s]t₂ else [x:=s]t₃
```

Small-step operational semantics:
```
                              v.IsValue
                       -----------------------                    (appAbs)
                        (λx:τ. t) v ⟶ [x:=v]t

                              t₁ ⟶ t₁'
                          ----------------                        (app1)
                           t₁ t₂ ⟶ t₁' t₂

                             v₁.IsValue
                              t₂ ⟶ t₂'
                          ----------------                        (app2)
                           v₁ t₂ ⟶ v₁ t₂'

                  --------------------------------                (ifTrue)
                   (if true then t₁ else t₂) ⟶ t₁

                  ---------------------------------               (ifFalse)
                   (if false then t₁ else t₂) ⟶ t₂

                              t₁ ⟶ t₁'
        ----------------------------------------------------      (ifStep)
         (if t₁ then t₂ else t₃) ⟶ (if t₁' then t₂ else t₃)
```

Typing:
```
                              Γ x = τ₁
                            ------------                       (var)
                             Γ ⊢ x ⦂ τ₁

                        x ↦ τ₂ ; Γ ⊢ t₁ ⦂ τ₁
                      -------------------------                (abs)
                       Γ ⊢ λx:τ₂. t₁ ⦂ τ₂ → τ₁

                          Γ ⊢ t₁ ⦂ τ₂ → τ₁
                            Γ ⊢ t₂ ⦂ τ₂
                         ------------------                    (app)
                           Γ ⊢ t₁ t₂ ⦂ τ₁

                          -----------------                    (tru)
                           Γ ⊢ true ⦂ Bool

                         ------------------                    (fls)
                          Γ ⊢ false ⦂ Bool

             Γ ⊢ t₁ ⦂ Bool    Γ ⊢ t₂ ⦂ τ₁    Γ ⊢ t₃ ⦂ τ₁
            ---------------------------------------------      (ite)
                   Γ ⊢ if t₁ then t₂ else t₃ ⦂ τ₁
```
::::

:::instructors
Ori 2020: we have slightly simplified the preservation proof.  We still need
the substitution lemma, but the latter is proved using weakening.
:::

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2022)
In Wadler's "PLF in Agda", he defines an "animator" for STLC terms using the
proof terms for progress + preservation.  This would be a FANTASTIC example
(or, perhaps better, exercise!) for this chapter.
:::

In this chapter, we develop the fundamental theory of the Simply
Typed Lambda Calculus — in particular, the type safety
theorem.

We pick up where the {ref "Stlc"}[Stlc] chapter left off, so everything below
lives in the same namespace as the definitions it is about.

```lean
namespace Stlc

open scoped MyGetElem
```

# Canonical Forms

::::full
As we saw for the very simple language in the {ref "Types"}[Types]
chapter, the first step in establishing basic properties of
reduction and types is to identify the possible _canonical
forms_ (i.e., well-typed values) belonging to each type.  For
`Bool`, these are again the boolean values `true` and `false`; for
arrow types, they are lambda-abstractions.
::::

Formally, we will need these lemmas only for terms that are not
only well typed but _closed_ — i.e., well typed in the empty
context.

```lean
theorem canonical_forms_bool (t : Tm) (hτ : <{ ∅ ⊢ ~t ⦂ Bool }>) (hv : t.IsValue) :
    t = <{ true }> ∨ t = <{ false }> := by
  cases hv with
  | abs x τ t₁ => cases hτ
  | tru => left; rfl
  | fls => right; rfl

theorem canonical_forms_fun (t : Tm) (τ₁ τ₂ : Ty)
    (hτ : <{ ∅ ⊢ ~t ⦂ ~τ₁ → ~τ₂ }>) (hv : t.IsValue) :
    ∃ x u, t = <{ λ ~x : ~τ₁ . ~u }> := by
  cases hv with
  | abs x τ t₁ => cases hτ with | abs _ _ _ _ _ _ =>
    exists x, t₁
  | tru => cases hτ
  | fls => cases hτ
```

# Progress

::::full
The _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term is a value, or it
can take a reduction step.  The proof is a relatively
straightforward extension of the progress proof we saw in the
{ref "Types"}[Types] chapter.  We give the proof in English first, then
the formal version.
::::

::::terse
The _progress_ theorem tells us that closed, well-typed
terms are not stuck.
::::

::::full
_Proof_: By induction on the derivation of `∅ ⊢ t ⦂ τ`.

- The last rule of the derivation cannot be `HasType.var`, since a
  variable is never well typed in an empty context.

- The `HasType.tru`, `HasType.fls`, and `HasType.abs` cases are trivial, since in
  each of these cases we can see by inspecting the rule that `t`
  is a value.

- If the last rule of the derivation is `HasType.app`, then `t` has the
  form `t₁ t₂` for some `t₁` and `t₂`, where `∅ ⊢ t₁ ⦂ τ₂ → τ`
  and `∅ ⊢ t₂ ⦂ τ₂` for some type `τ₂`.  The induction hypothesis
  for the first subderivation says that either `t₁` is a value or
  else it can take a reduction step.

    - If `t₁` is a value, then consider `t₂`, which by the
      induction hypothesis for the second subderivation must also
      either be a value or take a step.

        - Suppose `t₂` is a value.  Since `t₁` is a value with an
          arrow type, it must be a lambda abstraction; hence `t₁ t₂` can take a step by `Step.appAbs`.

        - Otherwise, `t₂` can take a step, and hence so can `t₁ t₂` by `Step.app2`.

    - If `t₁` can take a step, then so can `t₁ t₂` by `Step.app1`.

- If the last rule of the derivation is `HasType.ite`, then `t = if t₁ then t₂ else t₃`, where `t₁` has type `Bool`.  The first IH
  says that `t₁` either is a value or takes a step.

    - If `t₁` is a value, then since it has type `Bool` it must be
      either `true` or `false`.  If it is `true`, then `t` steps to
      `t₂`; otherwise it steps to `t₃`.

    - Otherwise, `t₁` takes a step, and therefore so does `t` (by
      `Step.ifStep`).
::::

```lean
theorem progress (t : Tm) (τ : Ty) (hτ : <{ ∅ ⊢ ~t ⦂ ~τ }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  generalize hΓ : (∅ : Context) = Γ at hτ
  induction hτ with
  | var Γ x τ₁ h =>
    subst hΓ
    -- Contradictory: variables cannot be typed in an empty context.
    rw [PartialMap.getElem_empty] at h
    cases h
  | abs => left; constructor
  | tru => left; constructor
  | fls => left; constructor
  | app Γ τ₁ τ₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    -- `t = t₁ t₂`.  Proceed by cases on whether `t₁` is a value or steps.
    subst hΓ
    right
    cases ih₁ rfl with
    | inl hv₁ =>
      cases ih₂ rfl with
      | inl hv₂ =>
        obtain ⟨x, u, rfl⟩ := canonical_forms_fun t₁ _ _ h₁ hv₁
        exists <{ [~x := ~t₂] ~u }>
        constructor
        assumption
      | inr hs₂ =>
        obtain ⟨t₂', h⟩ := hs₂
        exists <{ ~t₁ ~t₂' }>
        constructor <;> assumption
    | inr hs₁ =>
      obtain ⟨t₁', h⟩ := hs₁
      exists <{ ~t₁' ~t₂ }>
      constructor <;> assumption
  | ite Γ t₁ t₂ t₃ τ₁ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    subst hΓ
    right
    cases ih₁ rfl with
    | inl hv₁ =>
      cases canonical_forms_bool t₁ h₁ hv₁ with
      | inl he =>
        subst he
        exists t₂
        constructor
      | inr he =>
        subst he
        exists t₃
        constructor
    | inr hs₁ =>
      obtain ⟨t₁', h⟩ := hs₁
      exists <{ if ~t₁' then ~t₂ else ~t₃ }>
      constructor
      assumption
```

::::::full
:::::exercise (rating := 3) (name := "progress_from_term_ind") (level := Advanced)

Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

```lean
theorem progress' (t : Tm) (τ : Ty) (hτ : <{ ∅ ⊢ ~t ⦂ ~τ }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  solution!
    induction t generalizing τ with
    | var x =>
      cases hτ with
      | var _ _ _ h => rw [PartialMap.getElem_empty] at h; cases h
    | abs x τ₂ t₁ _ =>
      left
      constructor
    | tru =>
      left
      constructor
    | fls =>
      left
      constructor
    | app t₁ t₂ ih₁ ih₂ =>
      right
      cases hτ with
      | app _ _ τ₂ _ _ h₁ h₂ =>
        cases ih₁ _ h₁ with
        | inl hv₁ =>
          obtain ⟨x, u, rfl⟩ := canonical_forms_fun t₁ _ _ h₁ hv₁
          cases ih₂ _ h₂ with
          | inl hv₂ =>
            exists <{ [~x := ~t₂] ~u }>
            constructor <;> assumption
          | inr hs₂ =>
            obtain ⟨t₂', h⟩ := hs₂
            exists <{ (λ ~x : ~τ₂ . ~u) ~t₂' }>
            apply Step.app2 <;> assumption
        | inr hs₁ =>
          obtain ⟨t₁', h⟩ := hs₁
          exists <{ ~t₁' ~t₂ }>
          apply Step.app1
          assumption
    | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
      right
      cases hτ with
      | ite _ _ _ _ _ h₁ h₂ h₃ =>
        cases ih₁ _ h₁ with
        | inl hv₁ =>
          cases canonical_forms_bool t₁ h₁ hv₁ with
          | inl he =>
            subst he
            exists t₂
            apply Step.ifTrue
          | inr he =>
            subst he
            exists t₃
            apply Step.ifFalse
        | inr hs₁ =>
          obtain ⟨t₁', h⟩ := hs₁
          exists <{ if ~t₁' then ~t₂ else ~t₃ }>
          apply Step.ifStep
          assumption
```
:::gradeTheorem "3" progress'
:::
:::::
::::::

# Preservation

::::full
The other half of the type soundness property is the
preservation of types during reduction.  For this part, we'll need
to develop some technical machinery for reasoning about variables
and substitution.  Working from top to bottom (from the high-level
property we are actually interested in to the lowest-level
technical lemmas that are needed by various cases of the more
interesting proofs), the story goes like this:

  - The _preservation theorem_ is proved by induction on a typing
    derivation and case analysis on the step relation,
    pretty much as we did in the {ref "Types"}[Types] chapter.
    The one case that is significantly different is the one for
    the `Step.appAbs` rule, whose definition uses the substitution
    operation.  To see that this step preserves typing, we need to
    know that the substitution itself does.  So we prove a...

  - _substitution lemma_, stating that substituting a (closed,
    well-typed) term `s` for a variable `x` in a term `t`
    preserves the type of `t`.  The proof goes by induction on the
    form of `t` and requires looking at all the different cases in
    the definition of substitution.  This time, for the variables
    case, we discover that we need to deduce from the fact that a
    term `s` has type S in the empty context the fact that `s` has
    type S in every context. For this we prove a...

  - _weakening_ lemma, showing that typing is preserved under
    "extensions" to the context `Γ`.

To make Lean happy, though, we need to formalize the story in the
opposite order, starting with weakening...
::::

::::terse
For preservation, we need some technical machinery for reasoning
about variables and substitution.

  - The _preservation theorem_ is proved by induction on a typing
    derivation and case analysis on the step relation,
    pretty much as we did in the {ref "Types"}[Types] chapter.

    Main novelty: `Step.appAbs` uses the substitution operation.

    To see that this step preserves typing, we need to know that
    the substitution itself does.  So we prove a...
::::

:::slidebreak
:::

::::terse
- _substitution lemma_, stating that substituting a (closed,
well-typed) term `s` for a variable `x` in a term `t`
preserves the type of `t`.

The proof goes by induction on the form of `t` and requires
looking at all the different cases in the definition of
substitution.

Tricky case: variables.

In this case, we need to deduce from the fact that a term `s`
has type S in the empty context the fact that `s` has type S
in every context.

For this we prove a...
::::

:::slidebreak
:::

::::terse
- _weakening_ lemma, showing that typing is preserved under
"extensions" to the context `Γ`.
::::

:::slidebreak
:::

::::terse
To make Lean happy, we need to formalize all this in the opposite
order...
::::

## The Weakening Lemma

First, we show that typing is preserved under "extensions" to the
context `Γ`.  (Recall map inclusion, `Γ ⊆ Γ'`, from the `Typeclasses` chapter.)

```lean
theorem weakening {Γ Γ' : Context} {t : Tm} {τ : Ty}
    (hi : Γ ⊆ Γ') (ht : <{ ~Γ ⊢ ~t ⦂ ~τ }>) : <{ ~Γ' ⊢ ~t ⦂ ~τ }> := by
  induction ht generalizing Γ' with
  | var _ x _ h =>
    constructor
    exact hi h
  | abs _ x _ _ _ _ ih =>
    constructor
    apply ih
    apply PartialMap.update_subset
    assumption
  | app _ _ _ _ _ _ _ ih₁ ih₂ =>
    constructor
    · apply ih₁
      exact hi
    · apply ih₂
      exact hi
  | tru => constructor
  | fls => constructor
  | ite _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ =>
    constructor
    · apply ih₁
      exact hi
    · apply ih₂
      exact hi
    · apply ih₃
      exact hi
```

Through judicious use of `apply_rules`, we can heavily automate this proof.
The tactic after `with` is applied to every case of the {tactic}`induction`
and handles all the cases using {tactic}`apply_rules`'s automation.
We must give the tactic access to all the `HasType` constructors and the
{name}`PartialMap.update_subset` lemma for this to work:

```lean
theorem weakening' {Γ Γ' : Context} {t : Tm} {τ : Ty}
    (hi : Γ ⊆ Γ') (ht : <{ ~Γ ⊢ ~t ⦂ ~τ }>) : <{ ~Γ' ⊢ ~t ⦂ ~τ }> := by
  induction ht generalizing Γ' with (apply_rules [PartialMap.update_subset] using StlcTyping)
```

:::slidebreak
:::

The following simple corollary is what we actually need below.

```lean
theorem weakening_empty {Γ : Context} {t : Tm} {τ : Ty} (ht : <{ ∅ ⊢ ~t ⦂ ~τ }>) :
    <{ ~Γ ⊢ ~t ⦂ ~τ }> := by
  apply weakening (Γ := ∅)
  -- this is the "manual" way to show that the empty context is a subset of any context:
  -- show that a 'lookup' in it is impossible.
  · intros x b contra
    contradiction
  · assumption
```

## The Substitution Lemma

Now we come to the conceptual heart of the proof that reduction
preserves types — namely, the observation that _substitution_
preserves types.

::::full
Formally, the so-called _substitution lemma_ says this:
Suppose we have a term `t` with a free variable `x`, and suppose
we've assigned a type `τ` to `t` under the assumption that `x` has
some type `τ'`.  Also, suppose that we have some other term `v` and
that we've shown that `v` has type `τ'`.  Then, since `v` satisfies
the assumption we made about `x` when typing `t`, we can
substitute `v` for each of the occurrences of `x` in `t` and
obtain a new term that still has type `τ`.
::::

::::terse
The _substitution lemma_ says:

- Suppose we have a term `t` with a free variable `x`, and
  suppose we've been able to assign a type `τ` to `t` under the
  assumption that `x` has some type `τ'`.

- Also, suppose that we have some other term `v` and that we've
  shown that `v` has type `τ'`.

- Then we can substitute `v` for each of the occurrences of
  `x` in `t` and obtain a new term that still has type `τ`.
::::

:::slidebreak
:::

```lean
theorem substitution_preserves_typing (Γ : Context) (x : String) (τ' : Ty)
    (t v : Tm) (τ : Ty)
    (hτ : <{ ~x ↦ ~τ' ; ~Γ ⊢ ~t ⦂ ~τ }>) (hv : <{ ∅ ⊢ ~v ⦂ ~τ' }>) :
    <{ ~Γ ⊢ [~x := ~v] ~t ⦂ ~τ }> := by
  -- By induction on `t`; in each case we get at the derivation of `hτ`.
  induction t generalizing Γ τ with
  | var y =>
    cases hτ with
    | var _ _ _ h =>
      by_cases hxy : x = y
      · subst hxy
        rw [PartialMap.update_eq] at h
        rw [subst_var_eq]
        have hτ'τ : τ' = τ := by
          apply Option.some.inj
          exact h
        subst hτ'τ
        apply weakening_empty
        exact hv
      · rw [PartialMap.update_neq hxy] at h
        rw [subst_var_ne _ _ _ hxy]
        constructor
        exact h
  | app t₁ t₂ ih₁ ih₂ =>
    cases hτ with
    | app _ _ _ _ _ h₁ h₂ =>
      rw [subst_app]
      constructor
      · apply ih₁
        exact h₁
      · apply ih₂
        exact h₂
  | abs y S t₁ ih =>
    cases hτ with
    | abs _ _ _ _ _ h =>
      by_cases hxy : x = y
      · subst hxy
        rw [subst_abs_eq]
        rw [PartialMap.update_shadow] at h
        constructor
        exact h
      · rw [subst_abs_ne _ _ _ _ _ hxy]
        rw [PartialMap.update_permute (Ne.symm hxy)] at h
        constructor
        apply ih
        exact h
  | tru =>
    cases hτ with
    | tru =>
      rw [subst_tru]
      constructor
  | fls =>
    cases hτ with
    | fls =>
      rw [subst_fls]
      constructor
  | ite c t e ihc iht ihe =>
    cases hτ with
    | ite _ _ _ _ _ h₁ h₂ h₃ =>
      rw [subst_ite]
      constructor
      · apply ihc
        exact h₁
      · apply iht
        exact h₂
      · apply ihe
        exact h₃
```

::::full
The substitution lemma can be viewed as a kind of "commutation
property."  Intuitively, it says that substitution and typing can
be done in either order: we can either assign types to the terms
`t` and `v` separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to `[x:=v] t`; the result is the same either
way.

_Proof_: We show, by induction on `t`, that for all `τ` and
`Γ`, if `x ↦ τ' ; Γ ⊢ t ⦂ τ` and `∅ ⊢ v ⦂ τ'`, then
`Γ ⊢ [x:=v]t ⦂ τ`.

  - If `t` is a variable there are two cases to consider,
    depending on whether `t` is `x` or some other variable.

      - If `t = x`, then from the fact that `x ↦ τ' ; Γ ⊢ x ⦂ τ` we conclude that `τ' = τ`.  We must show that `[x:=v]x = v` has type `τ` under `Γ`, given the assumption that
        `v` has type `τ' = τ` under the empty context.  This
        follows from the weakening lemma.

      - If `t` is some variable `y` that is not equal to `x`, then
        we need only note that `y` has the same type under `x ↦ τ' ; Γ` as under `Γ`.

  - If `t` is an abstraction `λy:S. t₀`, then `τ = S → τ₁` and
    the IH tells us, for all `Γ'` and `τ₀`, that if `x ↦ τ' ; Γ' ⊢ t₀ ⦂ τ₀`, then `Γ' ⊢ [x:=v]t₀ ⦂ τ₀`.
    Moreover, by inspecting the typing rules we see it must be
    the case that `y ↦ S ; x ↦ τ' ; Γ ⊢ t₀ ⦂ τ₁`.

    The substitution in the conclusion behaves differently
    depending on whether `x` and `y` are the same variable.

    First, suppose `x = y`.  Then, by the definition of
    substitution, `[x:=v]t = t`, so we just need to show `Γ ⊢ t ⦂ τ`.  Using `HasType.abs`, we need to show that `y ↦ S ; Γ ⊢ t₀ ⦂ τ₁`. But we know `y ↦ S ; x ↦ τ' ; Γ ⊢ t₀ ⦂ τ₁`,
    and the claim follows since `x = y`.

    Second, suppose `x ≠ y`. Again, using `HasType.abs`,
    we need to show that `y ↦ S ; Γ ⊢ [x:=v]t₀ ⦂ τ₁`.
    Since `x ≠ y`, we have
    `y ↦ S ; x ↦ τ' ; Γ = x ↦ τ' ; y ↦ S ; Γ`. So
    we have `x ↦ τ' ; y ↦ S ; Γ ⊢ t₀ ⦂ τ₁`. Then, the
    IH applies (taking `Γ' = y ↦ S ; Γ`), giving us
    `y ↦ S ; Γ ⊢ [x:=v]t₀ ⦂ τ₁`, as required.

  - If `t` is an application `t₁ t₂`, the result follows
    straightforwardly from the definition of substitution and the
    induction hypotheses.

  - The remaining cases are similar to the application case.
::::

::::full
One technical subtlety in the statement of the above lemma is that
we assume `v` has type `τ'` in the _empty_ context — in other
words, we assume `v` is closed.  (Since we are using a simple
definition of substitution that is not capture-avoiding, it doesn't
make sense to substitute non-closed terms into other terms.
Fortunately, closed terms are all we need!)
::::

::::::full
:::::exercise (rating := 3) (name := "substitution_preserves_typing_from_typing_ind") (level := Advanced)

Show that substitution_preserves_typing can also be
proved by induction on typing derivations instead
of induction on terms.

```lean
theorem substitution_preserves_typing_from_typing_ind (Γ : Context) (x : String) (τ' : Ty)
    (t v : Tm) (τ : Ty)
    (hτ : <{ ~x ↦ ~τ' ; ~Γ ⊢ ~t ⦂ ~τ }>) (hv : <{ ∅ ⊢ ~v ⦂ ~τ' }>) :
    <{ ~Γ ⊢ [~x := ~v] ~t ⦂ ~τ }> := by
  solution!
    generalize hΓ : (x →ₚ τ' ; Γ) = Γ₀ at hτ
    induction hτ generalizing Γ with
    | var _ y τ₁ h =>
      subst hΓ
      by_cases hxy : x = y
      · subst hxy
        rw [PartialMap.update_eq] at h
        rw [subst_var_eq]
        have hτ'τ : τ' = τ₁ := by
          apply Option.some.inj
          exact h
        subst hτ'τ
        apply weakening_empty
        exact hv
      · rw [PartialMap.update_neq hxy] at h
        rw [subst_var_ne _ _ _ hxy]
        constructor
        exact h
    | abs _ y _ _ _ hb ih =>
      subst hΓ
      by_cases hxy : x = y
      · subst hxy
        rw [subst_abs_eq]
        rw [PartialMap.update_shadow] at hb
        constructor
        exact hb
      · rw [subst_abs_ne _ _ _ _ _ hxy]
        constructor
        apply ih
        apply PartialMap.update_permute
        exact hxy
    | app _ _ _ _ _ _ _ ih₁ ih₂ =>
      rw [subst_app]
      constructor
      · apply ih₁
        exact hΓ
      · apply ih₂
        exact hΓ
    | tru =>
      rw [subst_tru]
      constructor
    | fls =>
      rw [subst_fls]
      constructor
    | ite _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ =>
      rw [subst_ite]
      constructor
      · apply ih₁
        exact hΓ
      · apply ih₂
        exact hΓ
      · apply ih₃
        exact hΓ
```
:::gradeTheorem "3" substitution_preserves_typing_from_typing_ind
:::
:::::

::::::

## Main Theorem

We now have the ingredients we need to prove preservation: if a
closed, well-typed term `t` has type `τ` and takes a step to `t'`,
then `t'` is also a closed term with type `τ`.  In other words,
the small-step reduction relation preserves types.

```lean
theorem preservation (t t' : Tm) (τ : Ty)
    (hτ : <{ ∅ ⊢ ~t ⦂ ~τ }>) (hs : t ⟶ t') : <{ ∅ ⊢ ~t' ⦂ ~τ }> := by
  generalize hΓ : (∅ : Context) = Γ at hτ
  induction hτ generalizing t' with
  | var => cases hs
  | abs => cases hs
  | tru => cases hs
  | fls => cases hs
  | app Γ τ₁ τ₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    subst hΓ
    cases hs with
    | appAbs _ _ _ _ _ =>
      -- The one interesting case: the desired result is the substitution lemma.
      cases h₁ with
      | abs _ _ _ _ _ hb =>
        apply substitution_preserves_typing
        · exact hb
        · exact h₂
    | app1 _ t₁' _ h =>
      constructor
      · apply ih₁
        · exact h
        · rfl
      · exact h₂
    | app2 _ _ t₂' _ h =>
      constructor
      · exact h₁
      · apply ih₂
        · exact h
        · rfl
  | ite Γ t₁ t₂ t₃ τ₁ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    subst hΓ
    cases hs with
    | ifTrue => exact h₂
    | ifFalse => exact h₃
    | ifStep _ t₁' _ _ h =>
      constructor
      · apply ih₁
        · exact h
        · rfl
      · exact h₂
      · exact h₃
```

::::full
_Proof_: By induction on the derivation of `∅ ⊢ t ⦂ τ`.

- We can immediately rule out `HasType.var`, `HasType.abs`, `HasType.tru`, and
  `HasType.fls` as final rules in the derivation, since in each of these
  cases `t` cannot take a step.

- If the last rule in the derivation is `HasType.app`, then `t = t₁ t₂`,
  and there are subderivations showing that `∅ ⊢ t₁ ⦂ τ₂ → τ` and
  `∅ ⊢ t₂ ⦂ τ₂` plus two induction hypotheses: (1) `t₁ ⟶ t₁'`
  implies `∅ ⊢ t₁' ⦂ τ₂ → τ` and (2) `t₂ ⟶ t₂'` implies `∅ ⊢ t₂' ⦂ τ₂`.  There are now three subcases to consider, one for
  each rule that could be used to show that `t₁ t₂` takes a step
  to `t'`.

    - If `t₁ t₂` takes a step by `Step.app1`, with `t₁` stepping to
      `t₁'`, then, by the first IH, `t₁'` has the same type as
      `t₁` (`∅ ⊢ t₁' ⦂ τ₂ → τ`), and hence by `HasType.app` `t₁' t₂` has
      type `τ`.

    - The `Step.app2` case is similar, using the second IH.

    - If `t₁ t₂` takes a step by `Step.appAbs`, then `t₁ = λx:τ₀. t₀` and `t₁ t₂` steps to `[x:=t₂]t₀`; the desired
      result now follows from the substitution lemma.

- If the last rule in the derivation is `HasType.ite`, then `t = if t₁ then t₂ else t₃`, with `∅ ⊢ t₁ ⦂ Bool`, `∅ ⊢ t₂ ⦂ τ₁`, and
  `∅ ⊢ t₃ ⦂ τ₁`, and with three induction hypotheses: (1) `t₁ ⟶ t₁'` implies `∅ ⊢ t₁' ⦂ Bool`, (2) `t₂ ⟶ t₂'` implies `∅ ⊢ t₂' ⦂ τ₁`, and (3) `t₃ ⟶ t₃'` implies `∅ ⊢ t₃' ⦂ τ₁`.

  There are again three subcases to consider, depending on how `t`
  steps.

    - If `t` steps to `t₂` or `t₃` by `Step.ifTrue` or
      `Step.ifFalse`, the result is immediate, since `t₂` and `t₃`
      have the same type as `t`.

    - Otherwise, `t` steps by `Step.ifStep`, and the desired
      conclusion follows directly from the first induction
      hypothesis.
::::

::::::full
:::::exercise (rating := 2) (name := "subject_expansion_stlc") (manual := true)
An exercise in the {ref "Types"}[Types] chapter asked about the _subject
expansion_ property for the simple language of arithmetic and
boolean expressions.  This property did not hold for that language,
and it also fails for STLC.  That is, it is not always the case that,
if `t ⟶ t'` and `∅ ⊢ t' ⦂ τ`, then `∅ ⊢ t ⦂ τ`.
Show this by giving a counter-example that does _not involve
conditionals_.

:::solution
For example,
`(λx:Bool → Bool. true) true` is ill typed, but it evaluates
to the well-typed term `true`.
:::
:::dev "Roger Burtonpatel (rogerburtonpatel)"
This solution has to be rewritten; it is unreadable.
:::
```lean
theorem not_subject_expansion :
    ∃ (t t' : Tm) (τ : Ty), t ⟶ t' ∧ <{ ∅ ⊢ ~t' ⦂ ~τ }> ∧ ¬ <{ ∅ ⊢ ~t ⦂ ~τ }> := by
    -- Hint: for giving counterexamples in STLC, give each witness
    -- with `exists <{ … }>`.  This works for both terms and types, as
    -- in `<{true}>` and `<{ Bool }>`.
    solution!(
      exists <{ (λ x : Bool → Bool . true) true }>, <{true}>, <{Bool}>
      constructor
      . constructor; constructor
      . constructor
        . constructor
        . intro contra
          inversion contra with
          | app τ h₁ h₂ =>
            inversion h₂
            . inversion h₁
      )
```

:::ignore
Alternative formulation.

```lean -show
theorem not_subject_expansion_alt :
    ¬ (∀ (t t' : Tm) (τ : Ty), t ⟶ t' ∧ <{ ∅ ⊢ ~t' ⦂ ~τ }> → <{ ∅ ⊢ ~t ⦂ ~τ }>) := by
  intro hse
  have hτ : <{ ∅ ⊢ (λ x : Bool → Bool . λ y : Bool . y) true ⦂ Bool → Bool }> := by
    apply hse _ <{ λ y : Bool . y }>
    constructor
    · apply Step.appAbs
      constructor
    · apply HasType.abs
      apply HasType.var
      rfl
  cases hτ with
  | app _ _ _ _ _ h₁ h₂ =>
    cases h₁ with
    | abs _ _ _ _ _ _ =>
      cases h₂
```
:::

:::grade
`GRADE_MANUAL 2: subject_expansion_stlc`
:::
:::::

::::::

# Type Soundness

:::suppressPreviousHeaderWhenTerse
:::

::::::full
:::::exercise (rating := 2) (name := "type_soundness") (optional := true)
Put progress and preservation together and show that a well-typed
term can _never_ reach a stuck state.

```lean
def Tm.IsStuck (t : Tm) : Prop := IsNormalForm Step t ∧ ¬ t.IsValue

theorem type_soundness (t t' : Tm) (τ : Ty)
    (hτ : <{ ∅ ⊢ ~t ⦂ ~τ }>) (hm : t ⟶* t') : ¬ t'.IsStuck := by
  intro hst
  obtain ⟨hnf, hnv⟩ := hst
  induction hm with
  | refl u =>
    solution!
      cases progress u τ hτ with
      | inl hv => exact hnv hv
      | inr hs => exact hnf hs
  | step u w z h₁ _ ih =>
    solution!
      apply ih
      · apply preservation
        · exact hτ
        · exact h₁
      · exact hnf
      · exact hnv
```
:::::

::::::

# Uniqueness of Types

:::suppressPreviousHeaderWhenTerse
:::

::::::full
:::::exercise (rating := 3) (name := "unique_types")
Another nice property of the STLC is that types are unique: a
given term (in a given context) has at most one type.

```lean
theorem unique_types (Γ : Context) (e : Tm) (τ τ' : Ty)
    (h : <{ ~Γ ⊢ ~e ⦂ ~τ }>) (h' : <{ ~Γ ⊢ ~e ⦂ ~τ' }>) : τ = τ' := by
  solution!
    induction h generalizing τ' with
    | var _ _ _ hx =>
      cases h' with
      | var _ _ _ hx' =>
        rw [hx] at hx'
        injection hx'
    | abs _ _ τ₁ _ _ _ ih =>
      cases h' with
      | abs _ _ τ₁' _ _ hb' =>
        have heq : τ₁ = τ₁' := by
          apply ih
          exact hb'
        rw [heq]
    | app _ _ _ _ _ _ _ ih₁ _ =>
      cases h' with
      | app _ _ _ _ _ hf' _ =>
        have harrow := ih₁ _ hf'
        injection harrow
    | tru => cases h' with | tru => rfl
    | fls => cases h' with | fls => rfl
    | ite _ _ _ _ _ _ _ _ _ ih₂ _ =>
      cases h' with
      | ite _ _ _ _ _ _ h₂' _ =>
        apply ih₂
        exact h₂'
```
:::::

:::instructors
Since weakening suffices for the preservation theorem,
this whole section got demoted to optional when we changed to the
weakening presentation. But it introduces some useful terminology,
so keeping it as such.
:::
::::::

# Context Invariance (Optional)

:::suppressPreviousHeaderWhenTerse
:::

::::::full
Another standard technical lemma associated with typed languages
is _context invariance_. It states that typing is preserved under
"inessential changes" to the context `Γ` — in particular,
changes that do not affect any of the free variables of the
term. In this section, we establish this property for our system,
introducing some other standard terminology on the way.

First, we need to define the _free variables_ in a term — i.e.,
variables that are used in the term in positions that are _not_ in
the scope of an enclosing function abstraction binding a variable
of the same name.

More technically, a variable `x` _appears free in_ a term `t` if
`t` contains some occurrence of `x` that is not under an
abstraction labeled `x`. For example:
  - `y` appears free, but `x` does not, in `λx:τ → τ'. x y`
  - both `x` and `y` appear free in `(λx:τ → τ'. x y) x`
  - no variables appear free in `λx:τ → τ'. λy:τ. x y`

We write this `x ∈ᶠ t`, reading the relation as "`x` is one of the free
variables of `t`".  Formally:

```lean
section
set_option hygiene false in
local infix:50 " ∈ᶠ " => AppearsFreeIn

inductive AppearsFreeIn (x : String) : Tm → Prop where
  | var : x ∈ᶠ (Tm.var x)
  | app1 (t₁ t₂ : Tm) (h : x ∈ᶠ t₁) : x ∈ᶠ <{ ~t₁ ~t₂ }>
  | app2 (t₁ t₂ : Tm) (h : x ∈ᶠ t₂) : x ∈ᶠ <{ ~t₁ ~t₂ }>
  | abs (y : String) (τ₁ : Ty) (t₁ : Tm) (hne : y ≠ x) (h : x ∈ᶠ t₁) :
      x ∈ᶠ <{ λ ~y : ~τ₁ . ~t₁ }>
  | ite1 (t₁ t₂ t₃ : Tm) (h : x ∈ᶠ t₁) : x ∈ᶠ <{ if ~t₁ then ~t₂ else ~t₃ }>
  | ite2 (t₁ t₂ t₃ : Tm) (h : x ∈ᶠ t₂) : x ∈ᶠ <{ if ~t₁ then ~t₂ else ~t₃ }>
  | ite3 (t₁ t₂ t₃ : Tm) (h : x ∈ᶠ t₃) : x ∈ᶠ <{ if ~t₁ then ~t₂ else ~t₃ }>
end

scoped infix:50 " ∈ᶠ " => AppearsFreeIn
```

The _free variables_ of a term are just the variables that appear
free in it.  This gives us another way to define _closed_ terms —
arguably a better one, since it applies even to ill-typed
terms.  Indeed, this is the standard definition of the term
"closed."

```lean
def Tm.Closed (t : Tm) : Prop := ∀ x, ¬ x ∈ᶠ t
```

Conversely, an _open_ term is one that may contain free
variables.  (I.e., every term is an open term; the closed terms
are a subset of the open ones.  "Open" precisely means "possibly
containing free variables.")

:::::exercise (rating := 1) (name := "afi") (manual := true) (optional := true)
(Officially optional, but strongly recommended!) In the space
below, write out the rules of the `∈ᶠ` relation in
informal inference-rule notation.  (Use whatever notational
conventions you like — the point of the exercise is just for you
to think a bit about the meaning of each rule.)  Although this is
a rather low-level, technical definition, understanding it is
crucial to understanding substitution and its properties, which
are really the crux of the lambda-calculus.

:::solution
LATER: Fill in an official solution
(no solution yet)
:::

:::grade
`GRADE_MANUAL 1: afi`
:::
:::::

Next, we show that if a variable `x` appears free in a term `t`,
and if we know `t` is well typed in context `Γ`, then it
must be the case that `Γ` assigns a type to `x`.

_Proof_: We show, by induction on the proof that `x` appears free
in `t`, that, for all contexts `Γ`, if `t` is well typed under
`Γ`, then `Γ` assigns some type to `x`.

- If the last rule used is `AppearsFreeIn.var`, then `t = x`, and from the
  assumption that `t` is well typed under `Γ` we have
  immediately that `Γ` assigns a type to `x`.

- If the last rule used is `AppearsFreeIn.app1`, then `t = t₁ t₂` and `x`
  appears free in `t₁`.  Since `t` is well typed under `Γ`, we
  can see from the typing rules that `t₁` must also be, and the IH
  then tells us that `Γ` assigns `x` a type.

- Almost all the other cases are similar: `x` appears free in a
  subterm of `t`, and since `t` is well typed under `Γ`, we
  know the subterm of `t` in which `x` appears is well typed under
  `Γ` as well, and the IH gives us exactly the conclusion we
  want.

- The only remaining case is `AppearsFreeIn.abs`.  In this case `t = λy:τ₁. t₁` and `x` appears free in `t₁`, and we also know that
  `x` is different from `y`.  The difference from the previous
  cases is that, whereas `t` is well typed under `Γ`, its body
  `t₁` is well typed under `y ↦ τ₁ ; Γ`, so the IH allows us
  to conclude that `x` is assigned some type by the extended
  context `y ↦ τ₁ ; Γ`.  To conclude that `Γ` assigns a
  type to `x`, we appeal to lemma `PartialMap.update_neq`, noting that `x`
  and `y` are different variables.

:::::exercise (rating := 2) (name := "free_in_context")
Complete the following proof.

```lean
theorem free_in_context (x : String) (t : Tm) (τ : Ty) (Γ : Context)
    (ha : x ∈ᶠ t) (hτ : <{ ~Γ ⊢ ~t ⦂ ~τ }>) : ∃ τ', Γ[x] = some τ' := by
  induction ha generalizing Γ τ with
  | var =>
    cases hτ with
    | var _ _ _ h =>
      constructor
      exact h
  | app1 _ _ _ ih =>
    cases hτ with
    | app _ _ _ _ _ h₁ _ =>
      apply ih
      exact h₁
  | app2 _ _ _ ih =>
    cases hτ with
    | app _ _ _ _ _ _ h₂ =>
      apply ih
      exact h₂
  | abs y _ _ hne _ ih =>
    solution!
      cases hτ with
      | abs _ _ _ _ _ hb =>
        obtain ⟨τ', h⟩ := ih _ _ hb
        rw [PartialMap.update_neq hne] at h
        exists τ'
  | ite1 _ _ _ _ ih =>
    cases hτ with
    | ite _ _ _ _ _ h₁ _ _ =>
      apply ih
      exact h₁
  | ite2 _ _ _ _ ih =>
    cases hτ with
    | ite _ _ _ _ _ _ h₂ _ =>
      apply ih
      exact h₂
  | ite3 _ _ _ _ ih =>
    cases hτ with
    | ite _ _ _ _ _ _ _ h₃ =>
      apply ih
      exact h₃
```
:::::

From the `free_in_context` lemma, it immediately follows that any
term `t` that is well typed in the empty context is closed (it has
no free variables).

:::::exercise (rating := 2) (name := "typable_empty_closed") (optional := true)
```lean
theorem typable_empty_closed (t : Tm) (τ : Ty) (hτ : <{ ∅ ⊢ ~t ⦂ ~τ }>) : t.Closed := by
  solution!
    intro x ha
    obtain ⟨τ', hc⟩ := free_in_context x t τ ∅ ha hτ
    rw [PartialMap.getElem_empty] at hc
    cases hc
```
:::::

Finally, we establish _context invariance_.  It is useful in cases
when we have a proof of some typing relation `Γ ⊢ t ⦂ τ`,
and we need to replace `Γ` by a different context `Γ'`.
When is it safe to do this?  Intuitively, it must at least be the
case that `Γ'` assigns the same types as `Γ` to all the
variables that appear free in `t`. In fact, this is the only
condition that is needed.

_Proof_: By induction on the derivation of `Γ ⊢ t ⦂ τ`.

- If the last rule in the derivation was `HasType.var`, then `t = x` and
  `Γ x = τ`.  By assumption, `Γ' x = τ` as well, and hence
  `Γ' ⊢ t ⦂ τ` by `HasType.var`.

- If the last rule was `HasType.abs`, then `t = λy:τ₂. t₁`, with `τ = τ₂ → τ₁` and `y ↦ τ₂ ; Γ ⊢ t₁ ⦂ τ₁`.  The induction
  hypothesis states that for any context `Γ''`, if `y ↦ τ₂ ; Γ` and `Γ''` assign the same types to all the free
  variables in `t₁`, then `t₁` has type `τ₁` under `Γ''`.
  Let `Γ'` be a context which agrees with `Γ` on the free
  variables in `t`; we must show `Γ' ⊢ λy:τ₂. t₁ ⦂ τ₂ → τ₁`.

  By `HasType.abs`, it suffices to show that `y ↦ τ₂ ; Γ' ⊢ t₁ ⦂ τ₁`.  By the IH (setting `Γ'' = y ↦ τ₂ ; Γ'`), it
  suffices to show that `y ↦ τ₂ ; Γ` and `y ↦ τ₂ ; Γ'` agree
  on all the variables that appear free in `t₁`.

  Any variable occurring free in `t₁` must be either `y` or some
  other variable.  `y ↦ τ₂ ; Γ` and `y ↦ τ₂ ; Γ'` clearly
  agree on `y`.  Otherwise, note that any variable other than `y`
  that occurs free in `t₁` also occurs free in `t = λy:τ₂. t₁`,
  and by assumption `Γ` and `Γ'` agree on all such
  variables; hence so do `y ↦ τ₂ ; Γ` and `y ↦ τ₂ ; Γ'`.

- If the last rule was `HasType.app`, then `t = t₁ t₂`, with `Γ ⊢ t₁ ⦂ τ₂ → τ` and `Γ ⊢ t₂ ⦂ τ₂`.  One induction
  hypothesis states that for all contexts `Γ'`, if `Γ'`
  agrees with `Γ` on the free variables in `t₁`, then `t₁` has
  type `τ₂ → τ` under `Γ'`; there is a similar IH for `t₂`.
  We must show that `t₁ t₂` also has type `τ` under `Γ'`,
  given the assumption that `Γ'` agrees with `Γ` on all
  the free variables in `t₁ t₂`.  By `HasType.app`, it suffices to show
  that `t₁` and `t₂` each have the same type under `Γ'` as
  under `Γ`.  But all free variables in `t₁` are also free in
  `t₁ t₂`, and similarly for `t₂`; hence the desired result
  follows from the induction hypotheses.

:::::exercise (rating := 3) (name := "context_invariance") (optional := true)
Complete the following proof.

```lean
theorem context_invariance (Γ Γ' : Context) (t : Tm) (τ : Ty)
    (hτ : <{ ~Γ ⊢ ~t ⦂ ~τ }>) (hf : ∀ x, x ∈ᶠ t → Γ[x] = Γ'[x]) :
    <{ ~Γ' ⊢ ~t ⦂ ~τ }> := by
  induction hτ generalizing Γ' with
  | var _ x _ h =>
    solution!
      constructor
      rw [← h]
      symm
      apply hf
      constructor
  | abs _ y _ _ _ _ ih =>
    solution!
      constructor
      apply ih
      intro z hz
      by_cases hyz : y = z
      · subst hyz; rw [PartialMap.update_eq, PartialMap.update_eq]
      -- The only tricky step.
      · rw [PartialMap.update_neq hyz, PartialMap.update_neq hyz]
        apply hf
        apply AppearsFreeIn.abs <;> assumption
  | app _ _ _ t₁ t₂ _ _ ih₁ ih₂ =>
    solution!
      constructor
      · apply ih₁
        intro z hz
        apply hf
        apply AppearsFreeIn.app1
        exact hz
      · apply ih₂
        intro z hz
        apply hf
        apply AppearsFreeIn.app2
        exact hz
  | tru => constructor
  | fls => constructor
  | ite _ t₁ t₂ t₃ _ _ _ _ ih₁ ih₂ ih₃ =>
    constructor
    · apply ih₁
      intro z hz
      apply hf
      apply AppearsFreeIn.ite1
      exact hz
    · apply ih₂
      intro z hz
      apply hf
      apply AppearsFreeIn.ite2
      exact hz
    · apply ih₃
      intro z hz
      apply hf
      apply AppearsFreeIn.ite3
      exact hz
```
:::::

The context invariance lemma can actually be used in place of the
weakening lemma to prove the crucial substitution lemma stated
earlier.
::::::

# Additional Exercises

:::suppressPreviousHeaderWhenTerse
:::

::::::full
:::::exercise (rating := 1) (name := "progress_preservation_statement") (manual := true) (optional := true)
(Officially optional, but strongly recommended!) Without peeking
at their statements above, write down the progress and
preservation theorems for the simply typed lambda-calculus (as Lean
theorems).  You can write `sorry` for the proofs.

:::dev BeforeNextRelease
At least one person was confused by what to name these. We
could simplify life by giving the names explicitly and just
omitting the bodies.  Indeed, once we do that we could autograde
this by demanding that what they write be identical to what we
wrote above! Maybe a better way to solve this would be to have the
following template.  BCP 21: Yes, do this!!
:::

```
theorem progress_statement :
    FILL IN HERE := by
  apply progress

theorem preservation_statement :
    FILL IN HERE := by
  apply preservation
```

:::solution
See `progress` and `preservation` above.  Their statements are:

```
theorem progress_statement (t : Tm) (τ : Ty) (hτ : <{ ∅ ⊢ ~t ⦂ ~τ }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  sorry

theorem preservation_statement (t t' : Tm) (τ : Ty)
    (hτ : <{ ∅ ⊢ ~t ⦂ ~τ }>) (hs : t ⟶ t') : <{ ∅ ⊢ ~t' ⦂ ~τ }> := by
  sorry
```
:::

:::grade
`GRADE_MANUAL 1: progress_preservation_statement`
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation1") (manual := true)
Suppose we add a new term `zap` with the following reduction rule

```
                         ---------                  (zap)
                         t ⟶ zap
```

and the following typing rule:

```
                        -----------                 (zap)
                        Γ ⊢ zap ⦂ τ
```

Which of the following properties of the STLC remain true in
the presence of these rules?  For each property, write either
"remains true" or "becomes false." If a property becomes
false, give a counterexample.

- Determinism of `Step`

:::solution
Becomes false. For instance `(if true then false else true) ⟶ false`
and `(if true then false else true) ⟶ zap`.
:::

- Progress

:::solution
Remains true. Every term (including `zap`) can take a step to `zap`.
:::

- Preservation

:::solution
Remains true. `zap` can have any type.
:::

:::grade
`GRADE_MANUAL 2: stlc_variation1`
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation2") (manual := true)
Suppose instead that we add a new term `foo` with the following
reduction rules:

```
                       -----------------                (foo1)
                        (λx:A. x) ⟶ foo

                         ------------                   (foo2)
                          foo ⟶ true
```

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

- Determinism of `Step`

:::solution
Becomes false. The term `(λx:Bool. x) true` might step
to either `true` by the rule `Step.appAbs` or
to `foo true` by the rules `Step.app1` and `Step.foo1`.
:::

- Progress

:::solution
Remains true. We are only adding to the step relation, and
this can never damage progress.
:::

- Preservation

:::solution
Becomes false. For example,
`∅ ⊢ λx:Bool. x ⦂ Bool → Bool` and `(λx:Bool. x) ⟶ foo` by `Step.foo1`,
but, since we have no typing rules for `foo`, we cannot prove that
`∅ ⊢ foo ⦂ Bool → Bool`.
:::

:::grade
`GRADE_MANUAL 2: stlc_variation2`
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation3") (manual := true)
Suppose instead that we remove the rule `Step.app1` from the `Step`
relation. Which of the following properties of the STLC remain
true in the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

- Determinism of `Step`

:::solution
Remains true. Removing reduction rules can only make `Step`
more deterministic.
:::

- Progress

:::solution
Becomes false. For example,
`((λx:Bool → Bool. λy:Bool → Bool. x) (λz:Bool. z)) (λz:Bool. z)`
is well typed, but stuck.
:::

- Preservation

:::solution
Remains true. Removing reduction rules can't break preservation.
:::

:::grade
`GRADE_MANUAL 2: stlc_variation3`
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation4") (optional := true)
Suppose instead that we add the following new rule to the
reduction relation:

```
            ----------------------------------        (funnyIfTrue)
             (if true then t₁ else t₂) ⟶ true
```

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

- Determinism of `Step`

:::solution
Becomes false, for instance:
`(if true then false else false) ⟶ false` and
`(if true then false else false) ⟶ true`
:::

- Progress

:::solution
Remains true. We are only adding to the step relation, and
this can never damage progress.
:::

- Preservation

:::solution
Becomes false. For example,
`∅ ⊢ if true then (λx:Bool. x) else (λx:Bool. x) ⦂ Bool → Bool`
and `(if true then (λx:Bool. x) else (λx:Bool. x)) ⟶ true`
but it's not the case that `∅ ⊢ true ⦂ Bool → Bool`.
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation5") (optional := true)
Suppose instead that we add the following new rule to the typing
relation:

```
                 Γ ⊢ t₁ ⦂ Bool → Bool → Bool
                        Γ ⊢ t₂ ⦂ Bool
                ------------------------------       (funnyApp)
                       Γ ⊢ t₁ t₂ ⦂ Bool
```

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

- Determinism of `Step`

:::solution
Remains true. We are only adding to the typing relation, and
this can never damage determinism of `Step`.
:::

- Progress

:::solution
Remains true. Since the new rule still requires that `t₁` is
a function we can still apply `Step.appAbs` to show progress.
:::

- Preservation

:::solution
Becomes false. For example,
`∅ ⊢ (λx:Bool. λy:Bool. x) true ⦂ Bool`
and `(λx:Bool. λy:Bool. x) true ⟶ λy:Bool. true`
but it's not the case that `∅ ⊢ λy:Bool. true ⦂ Bool`
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation6") (optional := true)
Suppose instead that we add the following new rule to the typing
relation:

```
                        Γ ⊢ t₁ ⦂ Bool
                        Γ ⊢ t₂ ⦂ Bool
                      ------------------            (funnyApp')
                      Γ ⊢ t₁ t₂ ⦂ Bool
```

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

- Determinism of `Step`

:::solution
Remains true. We are not changing the `Step` relation.
:::

- Progress

:::solution
Becomes false. For instance, `true true` is a term that
becomes typable (at type `Bool`), but which is stuck.
:::

- Preservation

:::solution
Remains true. There are 3 ways `t₁ t₂` can reduce. For
`Step.app1` and `Step.app2` we can still apply the induction
hypothesis. To reduce `t₁ t₂` using `Step.appAbs`
`t₁` would need to be a function, but functions don't have
type `Bool`.
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation7") (optional := true)
Suppose we add the following new rule to the typing relation
of the STLC:

```
                       ------------------------     (funnyAbs)
                        ∅ ⊢ λx:Bool. t ⦂ Bool
```

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

- Determinism of `Step`

:::solution
Remains true. We're not changing the `Step` relation.
:::

- Progress

:::solution
Becomes false. For instance `if (λx:Bool. false) then false else false`
is a term that would become typable, although it is stuck.
:::

- Preservation

:::solution
Remains true. `λx:Bool. t` doesn't step.
:::
:::::

::::::

:::ignore
The STLC typing relation with the `funnyAbs` rule of `stlc_variation7` added,
and a proof that progress then fails.

```lean -show
namespace StlcVar1

inductive HasType : Context → Tm → Ty → Prop where
  | var (Γ : Context) (x : String) (τ₁ : Ty) (h : Γ[x] = some τ₁) :
      HasType Γ (.var x) τ₁
  | abs (Γ : Context) (x : String) (τ₁ τ₂ : Ty) (t₁ : Tm)
      (h : HasType (x →ₚ τ₂ ; Γ) t₁ τ₁) :
      HasType Γ <{ λ ~x : ~τ₂ . ~t₁ }> <{ ~τ₂ → ~τ₁ }>
  | app (Γ : Context) (τ₁ τ₂ : Ty) (t₁ t₂ : Tm)
      (h₁ : HasType Γ t₁ <{ ~τ₂ → ~τ₁ }>) (h₂ : HasType Γ t₂ τ₂) :
      HasType Γ <{ ~t₁ ~t₂ }> τ₁
  | tru (Γ : Context) : HasType Γ <{ true }> <{ Bool }>
  | fls (Γ : Context) : HasType Γ <{ false }> <{ Bool }>
  | ite (Γ : Context) (t₁ t₂ t₃ : Tm) (τ₁ : Ty)
      (h₁ : HasType Γ t₁ <{ Bool }>) (h₂ : HasType Γ t₂ τ₁) (h₃ : HasType Γ t₃ τ₁) :
      HasType Γ <{ if ~t₁ then ~t₂ else ~t₃ }> τ₁
  | funnyAbs (x : String) (t₁ : Tm) :
      HasType ∅ <{ λ ~x : Bool . ~t₁ }> <{ Bool }>

theorem no_progress :
    ∃ t τ, HasType ∅ t τ ∧ ¬ t.IsValue ∧ ¬ ∃ t', t ⟶ t' := by
  exists <{ if (λ x : Bool . false) then false else false }>, <{ Bool }>
  constructor
  · apply HasType.ite
    · apply HasType.funnyAbs
    · apply HasType.fls
    · apply HasType.fls
  constructor
  · intro hv
    cases hv
  · intro ⟨t', hs⟩
    cases hs with
    | ifStep _ _ _ _ h => cases h

end StlcVar1
```
:::

```lean
end Stlc
```

## Exercise: STLC with Arithmetic

:::suppressPreviousHeaderWhenTerse
:::

::::full
To see how the STLC might function as the core of a real
programming language, let's extend it with a concrete base
type of numbers and some constants and primitive
operators.

The arithmetic we are adding is the arithmetic of the {ref "Slang"}[Slang]
chapter — numeric constants and multiplication — together with the
successor, predecessor, and zero-test operations of the
{ref "Types"}[Types] chapter.  What is new is the setting: those operations now
live in a language that also has variables, abstraction, and application, so
an arithmetic computation can be packaged up as a function and passed around
as a value.
::::

::::terse
Let's extend the STLC with a base type of numbers, some constants, and
some primitive operators.
::::

```lean
namespace StlcArith

open scoped MyGetElem
```

To types, we add a base type of natural numbers (and remove
booleans, for brevity).

```lean
inductive Ty where
  | arrow (τ₁ τ₂ : Ty)
  | nat
```

To terms, we add natural number constants, along with
successor, predecessor, multiplication, and zero-testing.

```lean
inductive Tm where
  | var (x : String)
  | app (t₁ t₂ : Tm)
  | abs (x : String) (τ : Ty) (t : Tm)
  | const (n : Nat)
  | succ (t : Tm)
  | pred (t : Tm)
  | mult (t₁ t₂ : Tm)
  | ite0 (c t e : Tm)
```

::::full
`StlcArith` is a *different* language from the STLC of this chapter, not an
extension of it, so it needs its own concrete syntax.  Rather than invent a new
one, we reuse the grammars set up in the {ref "Stlc"}[Stlc] chapter — the
syntax categories `stlcTy`, `stlcTm`, and `stlcVar` — and give them a new
meaning here.  Terms and types of this language are therefore written inside
the same `<{ … }>` brackets, with the same `~e` escape back to Lean.
::::

:::instructors
The three grammars — `stlcTy`, `stlcTm`, and (below) `stlcCtx` — are meant to
be read as *templates*.  A new Stlc-like language reuses the categories, adds
productions for whatever constructs it has that the template lacks, and
supplies a `macro_rules` group mapping every production to its own
constructors.  Because the new rules are `scoped`, they are in force only where
the language's namespace is open, so each language keeps its own reading of the
brackets.  If anything changes in one of these grammars, make the same
adjustment in all the others.
:::

::::details "Notation encoding: types"
The type grammar needs no new productions: `Nat` is a bare identifier, which
the template already accepts, and arrows and parentheses are unchanged.  Only
the `macro_rules` are new, and they differ from the STLC's in just two places
— the identifier `Nat` names this language's base type, and the arrow builds
this language's {name}`StlcArith.Ty.arrow`.

```lean
scoped macro_rules (kind := Stlc.tyBracket)
  | `(<{ ~$τ:term }>)    => pure τ
  | `(<{ ($τ:stlcTy) }>) => `(<{ $τ:stlcTy }>)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Nat" => `(Ty.nat)
      | _ => `(($x : Ty))
  | `(<{ $τ₁:stlcTy → $τ₂:stlcTy }>)  => `(Ty.arrow <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)
  | `(<{ $τ₁:stlcTy -> $τ₂:stlcTy }>) => `(Ty.arrow <{ $τ₁:stlcTy }> <{ $τ₂:stlcTy }>)
```
::::

::::details "Notation encoding: terms"
Terms do need new productions: a numeral, an infix `*`, and the zero test.
Multiplication binds looser than application and tighter than `λ`, so `x * y z`
multiplies `x` by the application `y z`; it associates to the right, so
`x * y * z` is `x * (y * z)`.

`succ` and `pred` get no production of their own.  Making them keywords would
reserve those words globally — and we would then be unable to write `succ` as
a case name in a proof, including for Lean's own {name}`Nat`.  Instead they are
written as though they were functions applied to an argument, `succ t`, and the
application rule below recognizes them.  `if0` *is* a keyword, since `then` and
`else` leave no other option; that is why the constructor above is called
{name}`StlcArith.Tm.ite0` rather than `if0`, just as the STLC's conditional is
{name}`Stlc.Tm.ite`.

```lean
scoped syntax:max num : stlcTm
scoped syntax:60 stlcTm:61 " * " stlcTm:60 : stlcTm
scoped syntax:50 "if0 " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

open Lean in
scoped macro_rules (kind := Stlc.tmBracket)
  | `(<{ ~$e:term }>)    => pure e
  | `(<{ ($t:stlcTm) }>) => `(<{ $t:stlcTm }>)
  | `(<{ $n:num }>)      => `(Tm.const $n)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Nat"  => Macro.throwErrorAt x "`Nat` is a type, not a term"
      | "succ" => Macro.throwErrorAt x "`succ` must be applied to an argument"
      | "pred" => Macro.throwErrorAt x "`pred` must be applied to an argument"
      | _      => `(Tm.var $(quote x.getId.toString))
  | `(<{ $t₁:stlcTm $t₂:stlcTm }>) =>
      match t₁ with
      | `(stlcTm| $f:ident) =>
          match f.getId.toString with
          | "succ" => `(Tm.succ <{ $t₂:stlcTm }>)
          | "pred" => `(Tm.pred <{ $t₂:stlcTm }>)
          | _      => `(Tm.app <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
      | _ => `(Tm.app <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
  | `(<{ λ $x : $τ . $t }>) => do
      `(Tm.abs $(← Stlc.varStr x) <{ $τ:stlcTy }> <{ $t:stlcTm }>)
  | `(<{ $t₁:stlcTm * $t₂:stlcTm }>) => `(Tm.mult <{ $t₁:stlcTm }> <{ $t₂:stlcTm }>)
  | `(<{ if0 $c then $t else $e }>) =>
      `(Tm.ite0 <{ $c:stlcTm }> <{ $t:stlcTm }> <{ $e:stlcTm }>)
```
::::

::::details "Notation encoding: printing it back"
As in the {ref "Stlc"}[Stlc] chapter, a delaborator runs the grammar backwards,
so that goals mentioning these terms and types read in the concrete syntax.
The parenthesizers registered there are for the whole syntax category, so they
serve this language too and are not repeated.

```lean
open Lean in
/-- Is `s` usable as a bare variable in `stlcTm` rather than as reserved syntax? -/
def isPlainTmVarName (s : String) : Bool :=
  Stlc.isPlainName s && s != "Nat" && s != "succ" && s != "pred"

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTy` concrete syntax from a `Ty` value. -/
partial def delabTyInner : DelabM (TSyntax `stlcTy) := do
  let stx ←
    match_expr ← getExpr with
    | Ty.nat => `(stlcTy| $(mkIdent `Nat):ident)
    | Ty.arrow _ _ => do
        let a ← withAppFn <| withAppArg delabTyInner
        let b ← withAppArg delabTyInner
        `(stlcTy| $a → $b)
    | _ => do
        match ← delab with
        | `($i:ident) => `(stlcTy| $i:ident)
        | e => `(stlcTy| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
/-- Rebuild `stlcTm` concrete syntax from a `Tm` value. -/
partial def delabTmInner : DelabM (TSyntax `stlcTm) := do
  let stx ←
    match_expr ← getExpr with
    | Tm.var _ => do
        let x ← withAppArg delab
        match x with
        | `($s:str) =>
            if isPlainTmVarName s.getString then
              `(stlcTm| $(mkIdent (Name.mkSimple s.getString)):ident)
            else
              let var : Term := mkIdent ``StlcArith.Tm.var
              `(stlcTm| ~($var $x))
        | _ =>
            let var : Term := mkIdent ``StlcArith.Tm.var
            `(stlcTm| ~($var $x))
    | Tm.const _ => do
        let n ← withAppArg delab
        match n with
        | `($n:num) => `(stlcTm| $n:num)
        | _ =>
            let const : Term := mkIdent ``StlcArith.Tm.const
            `(stlcTm| ~($const $n))
    | Tm.app _ _ => do
        let f ← withAppFn <| withAppArg delabTmInner
        let a ← withAppArg delabTmInner
        `(stlcTm| $f $a)
    | Tm.abs _ _ _ => do
        let x ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
        let τ ← withAppFn <| withAppArg delabTyInner
        let t ← withAppArg delabTmInner
        `(stlcTm| λ $x : $τ . $t)
    | Tm.succ _ => do
        let t ← withAppArg delabTmInner
        `(stlcTm| $(mkIdent `succ):ident $t)
    | Tm.pred _ => do
        let t ← withAppArg delabTmInner
        `(stlcTm| $(mkIdent `pred):ident $t)
    | Tm.mult _ _ => do
        let a ← withAppFn <| withAppArg delabTmInner
        let b ← withAppArg delabTmInner
        `(stlcTm| $a * $b)
    | Tm.ite0 _ _ _ => do
        let c ← withAppFn <| withAppFn <| withAppArg delabTmInner
        let t ← withAppFn <| withAppArg delabTmInner
        let e ← withAppArg delabTmInner
        `(stlcTm| if0 $c then $t else $e)
    | _ => do
        -- `subst` is defined below, so it is matched by name rather than with
        -- `match_expr`; a substitution prints in its own bracket notation.
        let e ← getExpr
        if e.getAppFn.constName? == some `StlcArith.subst && e.getAppNumArgs == 3 then
          let x ← withAppFn <| withAppFn <| withAppArg Stlc.delabVarInner
          let s ← withAppFn <| withAppArg delabTmInner
          let t ← withAppArg delabTmInner
          `(stlcTm| [$x := $s] $t)
        else
          match ← delab with
          | `($i:ident) => `(stlcTm| $i:ident)
          | e => `(stlcTm| ~$e)
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.StlcArith.Ty.nat, delab app.StlcArith.Ty.arrow]
def delabTy : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Ty.nat => true | Ty.arrow _ _ => true | _ => false
  match ← delabTyInner with
  | `(stlcTy| ~$e) => pure e
  | e => `(<{ $e:stlcTy }>)

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.StlcArith.Tm.var, delab app.StlcArith.Tm.app, delab app.StlcArith.Tm.abs,
  delab app.StlcArith.Tm.const, delab app.StlcArith.Tm.succ, delab app.StlcArith.Tm.pred,
  delab app.StlcArith.Tm.mult, delab app.StlcArith.Tm.ite0]
def delabTm : Delab := whenPPOption getPPNotation do
  guard <| match_expr ← getExpr with
    | Tm.var _ => true | Tm.app _ _ => true | Tm.abs _ _ _ => true
    | Tm.const _ => true | Tm.succ _ => true | Tm.pred _ => true
    | Tm.mult _ _ => true | Tm.ite0 _ _ _ => true
    | _ => false
  match ← delabTmInner with
  | `(stlcTm| ~($e)) => pure e
  | `(stlcTm| ~$e) => pure e
  | e => `(<{ $e:stlcTm }>)
```
::::

:::ignore
Checks that the extended grammar parses the way it should.

```lean -show
#check <{ λ x : Nat . x }>
#check <{ if0 x then x else x }>
#check <{ if0 y x then x else x }>
#check <{ if0 (y x) then x else x }>
#check <{ x * y * z }>
#check <{ succ (pred x) }>
#check <{ succ x y }>
#check <{ x (succ y) }>
#check <{ x * y z }>
#check <{ x * y (succ z) }>
#check <{ z x y }>
#check <{ z x * y }>
#check <{ λ x : Nat . λ y : Nat . if0 x then 0 else pred (x * y) }>
```
:::

::::::full
In this extended exercise, your job is to finish formalizing the
definition and properties of the STLC extended with arithmetic.
Specifically:

Fill in the core definitions for `StlcArith`, by starting with the rules
and terms which are the same as the STLC.  Then prove the key lemmas and
theorems we provide.  You will need to define and prove helper lemmas,
as before.

Make sure Lean accepts the whole file before submitting.

:::::exercise (rating := 5) (name := "StlcArith.subst")
Substitution is defined exactly as it was for the STLC, with one clause per new
constructor.

::::details "Why the definition is wrapped in a section"
Substitution is written using its own `[x := s] t` notation, which is being
defined at the same time, so — as in the {ref "Stlc"}[Stlc] chapter — the rule
is first declared `local`, with hygiene off so that the `subst` in its expansion
refers to the function being defined, and then declared again for real once the
section closes.
::::

```lean
section
set_option hygiene false in
local macro_rules (kind := Stlc.tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← Stlc.varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)

def subst (x : String) (s : Tm) (t : Tm) : Tm := solution!(
  match t with
  -- `.var y`, not `<{ ~y }>`: `y` is the variable's *name*, a `String`.
  | .var y =>
      if x = y then s else t
  | <{ λ ~y : ~τ . ~t₁ }> =>
      if x = y then t else <{ λ ~y : ~τ . [~x := ~s] ~t₁ }>
  | <{ ~t₁ ~t₂ }> =>
      <{ ([~x := ~s] ~t₁) ([~x := ~s] ~t₂) }>
  | .const _ =>
      t
  | <{ succ ~t₁ }> =>
      <{ succ ([~x := ~s] ~t₁) }>
  | <{ pred ~t₁ }> =>
      <{ pred ([~x := ~s] ~t₁) }>
  | <{ ~t₁ * ~t₂ }> =>
      <{ ([~x := ~s] ~t₁) * ([~x := ~s] ~t₂) }>
  | <{ if0 ~t₁ then ~t₂ else ~t₃ }> =>
      <{ if0 [~x := ~s] ~t₁ then [~x := ~s] ~t₂ else [~x := ~s] ~t₃ }>)
end

macro_rules (kind := Stlc.tmBracket)
  | `(<{ [$x := $s] $t }>) => do
      `(subst $(← Stlc.varStr x) <{ $s:stlcTm }> <{ $t:stlcTm }>)
```

:::autogradedHole subst
:::

::::details "Notation encoding: substitution"
One more line registers substitutions with the printer, so that a goal
mentioning one reads as `[x := s] t` rather than as a `subst` application.

```lean
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.StlcArith.subst]
def delabSubst : Delab := whenPPOption getPPNotation do
  match ← delabTmInner with
  | `(stlcTm| ~$e) => pure e
  | e => `(<{ $e:stlcTm }>)
```
::::

You will also want one `@[simp]` simplification lemma per constructor, saying
how your `subst` behaves on that constructor, in the style of the
{ref "Stlc"}[Stlc] chapter — the substitution lemma below is proved by
rewriting with them rather than by unfolding the definition.  Two of the
constructors need two lemmas apiece, since substitution treats a bound name
differently depending on whether it is the name being substituted for.

```lean
section
variable (x y : String) (s t t₁ t₂ t₃ : Tm) (τ : Ty) (n : Nat)
-- SOLUTION
@[simp] theorem subst_var_eq : <{ [~x := ~s] ~(Tm.var x) }> = s := by
  simp [subst]

@[simp] theorem subst_var_ne (h : x ≠ y) : <{ [~x := ~s] ~(Tm.var y) }> = .var y := by
  simp [subst, h]

@[simp] theorem subst_abs_eq : <{ [~x := ~s] (λ ~x : ~τ . ~t) }> = <{ λ ~x : ~τ . ~t }> := by
  simp [subst]

@[simp] theorem subst_abs_ne (h : x ≠ y) :
    <{ [~x := ~s] (λ ~y : ~τ . ~t) }> = <{ λ ~y : ~τ . [~x := ~s] ~t }> := by
  simp [subst, h]

@[simp] theorem subst_app :
    <{ [~x := ~s] (~t₁ ~t₂) }> = <{ ([~x := ~s] ~t₁) ([~x := ~s] ~t₂) }> := rfl

@[simp] theorem subst_const : <{ [~x := ~s] ~(Tm.const n) }> = .const n := rfl

@[simp] theorem subst_succ :
    <{ [~x := ~s] (succ ~t₁) }> = <{ succ ([~x := ~s] ~t₁) }> := rfl

@[simp] theorem subst_pred :
    <{ [~x := ~s] (pred ~t₁) }> = <{ pred ([~x := ~s] ~t₁) }> := rfl

@[simp] theorem subst_mult :
    <{ [~x := ~s] (~t₁ * ~t₂) }> = <{ ([~x := ~s] ~t₁) * ([~x := ~s] ~t₂) }> := rfl

@[simp] theorem subst_ite0 :
    <{ [~x := ~s] (if0 ~t₁ then ~t₂ else ~t₃) }> =
      <{ if0 [~x := ~s] ~t₁ then [~x := ~s] ~t₂ else [~x := ~s] ~t₃ }> := rfl
-- END SOLUTION
end
```

Next, the values.

```lean
inductive Tm.IsValue : Tm → Prop where
-- SOLUTION
  -- In the pure STLC, function abstractions were the only values:
  | abs (x : String) (τ₂ : Ty) (t₁ : Tm) : Tm.IsValue <{ λ ~x : ~τ₂ . ~t₁ }>
  -- now the numbers are values too.
  | const (n : Nat) : Tm.IsValue (.const n)
-- END SOLUTION
```

:::autogradedHole Tm.IsValue
:::

Now the reduction relation.

```lean
section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
-- SOLUTION
  -- The three rules for application are from STLC;
  | appAbs (x : String) (τ : Ty) (t v : Tm) (hv : v.IsValue) :
      <{ (λ ~x : ~τ . ~t) ~v }> ⟶ <{ [~x := ~v] ~t }>
  | app1 (t₁ t₁' t₂ : Tm) (h : t₁ ⟶ t₁') :
      <{ ~t₁ ~t₂ }> ⟶ <{ ~t₁' ~t₂ }>
  | app2 (v₁ t₂ t₂' : Tm) (hv : v₁.IsValue) (h : t₂ ⟶ t₂') :
      <{ ~v₁ ~t₂ }> ⟶ <{ ~v₁ ~t₂' }>
  -- the rest say how the arithmetic operators evaluate their arguments and
  -- what they compute once those arguments are numbers.
  | succ (t₁ t₁' : Tm) (h : t₁ ⟶ t₁') :
      <{ succ ~t₁ }> ⟶ <{ succ ~t₁' }>
  | succConst (n : Nat) :
      <{ succ ~(Tm.const n) }> ⟶ Tm.const (1 + n)
  | pred (t₁ t₁' : Tm) (h : t₁ ⟶ t₁') :
      <{ pred ~t₁ }> ⟶ <{ pred ~t₁' }>
  | predConst (n : Nat) :
      <{ pred ~(Tm.const n) }> ⟶ Tm.const (n - 1)
  | multConst (n₁ n₂ : Nat) :
      <{ ~(Tm.const n₁) * ~(Tm.const n₂) }> ⟶ Tm.const (n₁ * n₂)
  | mult1 (t₁ t₁' t₂ : Tm) (h : t₁ ⟶ t₁') :
      <{ ~t₁ * ~t₂ }> ⟶ <{ ~t₁' * ~t₂ }>
  | mult2 (v₁ t₂ t₂' : Tm) (hv : v₁.IsValue) (h : t₂ ⟶ t₂') :
      <{ ~v₁ * ~t₂ }> ⟶ <{ ~v₁ * ~t₂' }>
  | if0Step (t₁ t₁' t₂ t₃ : Tm) (h : t₁ ⟶ t₁') :
      <{ if0 ~t₁ then ~t₂ else ~t₃ }> ⟶ <{ if0 ~t₁' then ~t₂ else ~t₃ }>
  | if0Zero (t₂ t₃ : Tm) :
      <{ if0 0 then ~t₂ else ~t₃ }> ⟶ t₂
  | if0Nonzero (n : Nat) (t₂ t₃ : Tm) :
      <{ if0 ~(Tm.const (n + 1)) then ~t₂ else ~t₃ }> ⟶ t₃
-- END SOLUTION
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'
```

:::autogradedHole Step
:::

An example:

```lean
-- SOLUTION
-- Our solution uses [normalize]. It is fine if the student either follows this
-- strategy or proceeds by hand.
attribute [StlcArithEval] Tm.IsValue.abs Tm.IsValue.const
attribute [StlcArithEval] Step.appAbs Step.app1 Step.app2 Step.succ Step.succConst
  Step.pred Step.predConst Step.multConst Step.mult1 Step.mult2 Step.if0Step
  Step.if0Zero Step.if0Nonzero
-- END SOLUTION

theorem Nat_step_example : ∃ t, <{ (λ x : Nat . λ y : Nat . x * y) 3 2 }> ⟶* t := by
  solution!
    exists <{ 6 }>
    normalize using StlcArithEval
```

:::gradeTheorem "5" StlcArith.Nat_step_example
:::

:::dev BeforeNextRelease
The reduction example above ought to be joined by a bigger one — something to
replace the factorial example that used to live here.
:::

A typing context is a partial map from variables to types, exactly as before.

```lean
abbrev Context := PartialMap String Ty
```

::::details "Notation encoding: contexts and judgments"
The context grammar `stlcCtx` is reused as well; only the map it denotes is new,
since the types it stores are this language's.  As with `subst`, the judgment
rule is introduced twice: `local` and hygiene-free while the relation is being
declared, then again for real.

```lean
open Lean in
/-- The `Context` denoted by a context expression. -/
partial def ctxTerm (G : TSyntax `stlcCtx) : MacroM Term :=
  match G with
  | `(stlcCtx| ∅)   => `((∅ : Context))
  | `(stlcCtx| ~$e) => pure e
  | `(stlcCtx| $x:stlcVar ↦ $τ:stlcTy ; $G:stlcCtx) => do
      `(PartialMap.update $(← ctxTerm G) $(← Stlc.varStr x) <{ $τ:stlcTy }>)
  | _ => Macro.throwUnsupported

section StlcArith
set_option hygiene false in
local macro_rules (kind := Stlc.judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $τ:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $τ:stlcTy }>)
```
::::

Now the typing relation.

```lean
inductive HasType : Context → Tm → Ty → Prop where
-- SOLUTION
  -- The typing rules for variables, abstraction, and application are from STLC.
  | var (Γ : Context) (x : String) (τ₁ : Ty) (h : Γ[x] = some τ₁) :
      <{ ~Γ ⊢ ~(Tm.var x) ⦂ ~τ₁ }>
  | abs (Γ : Context) (x : String) (τ₁ τ₂ : Ty) (t₁ : Tm)
      (h : <{ ~x ↦ ~τ₂ ; ~Γ ⊢ ~t₁ ⦂ ~τ₁ }>) :
      <{ ~Γ ⊢ λ ~x : ~τ₂ . ~t₁ ⦂ ~τ₂ → ~τ₁ }>
  | app (Γ : Context) (τ₁ τ₂ : Ty) (t₁ t₂ : Tm)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ ~τ₂ → ~τ₁ }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~τ₂ }>) :
      <{ ~Γ ⊢ ~t₁ ~t₂ ⦂ ~τ₁ }>
  -- The remaining five are the typing rules for arithmetic expressions.
  | const (Γ : Context) (n : Nat) :
      <{ ~Γ ⊢ ~(Tm.const n) ⦂ Nat }>
  | succ (Γ : Context) (t₁ : Tm) (h : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) :
      <{ ~Γ ⊢ succ ~t₁ ⦂ Nat }>
  | pred (Γ : Context) (t₁ : Tm) (h : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) :
      <{ ~Γ ⊢ pred ~t₁ ⦂ Nat }>
  | mult (Γ : Context) (t₁ t₂ : Tm)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ Nat }>) :
      <{ ~Γ ⊢ ~t₁ * ~t₂ ⦂ Nat }>
  | ite0 (Γ : Context) (t₁ t₂ t₃ : Tm) (τ₀ : Ty)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~τ₀ }>)
      (h₃ : <{ ~Γ ⊢ ~t₃ ⦂ ~τ₀ }>) :
      <{ ~Γ ⊢ if0 ~t₁ then ~t₂ else ~t₃ ⦂ ~τ₀ }>
-- END SOLUTION
```

:::autogradedHole HasType
:::

::::details "Notation encoding: the judgment, for real"
Closing the section retires the hygiene-free rule; the same rule is then
declared again, hygienically, for every later use, and a pair of unexpanders
prints judgments back in their own notation.

```lean
end StlcArith

scoped macro_rules (kind := Stlc.judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $τ:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $τ:stlcTy }>)

open Lean PrettyPrinter in
/-- Rebuild `stlcCtx` syntax from the term syntax of a `Context`, so that a
context prints as `x ↦ Nat ; Γ` rather than as a chain of map updates. -/
partial def unexpandCtx : Term → UnexpandM (TSyntax `stlcCtx)
  | `(∅) => `(stlcCtx| ∅)
  | `($x:str →ₚ $τ) => do
      unexpandCtx (← `($x →ₚ $τ ; ∅))
  | `($x:str →ₚ $τ ; $G) => do
      let G' ← unexpandCtx G
      let x' : TSyntax `stlcVar ←
        if Stlc.isPlainName x.getString then
          `(stlcVar| $(mkIdent (Name.mkSimple x.getString)):ident)
        else `(stlcVar| ~$x)
      match τ with
      | `(<{ $τ':stlcTy }>) => `(stlcCtx| $x':stlcVar ↦ $τ' ; $G')
      | _                   => `(stlcCtx| $x':stlcVar ↦ ~($τ) ; $G')
  | G => `(stlcCtx| ~($G))

open Lean PrettyPrinter in
@[app_unexpander StlcArith.HasType]
def HasType.unexpand : Unexpander
  | `($_ $G <{ $t:stlcTm }> <{ $τ:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ $τ }>)
  | `($_ $G <{ $t:stlcTm }> $τ) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ ~($τ) }>)
  | `($_ $G $t <{ $τ:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ $τ }>)
  | `($_ $G $t $τ) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ ~($τ) }>)
  | _ => throw ()
```
::::

An example:

```lean
theorem Nat_typing_example : <{ ∅ ⊢ (λ x : Nat . λ y : Nat . x * y) 3 2 ⦂ Nat }> := by
  solution!
    apply HasType.app (τ₂ := Ty.nat)
    · apply HasType.app (τ₂ := Ty.nat)
      · apply HasType.abs
        apply HasType.abs
        apply HasType.mult
        · apply HasType.var
          rfl
        · apply HasType.var
          rfl
      · apply HasType.const
    · apply HasType.const
```

:::gradeTheorem "5" StlcArith.Nat_typing_example
:::
:::::

::::::

### The Technical Theorems

:::suppressPreviousHeaderWhenTerse
:::

::::::full
The next lemmas are proved _exactly_ as before.

:::::exercise (rating := 4) (name := "StlcArith.weakening")
```lean
theorem weakening (Γ Γ' : Context) (t : Tm) (τ : Ty)
    (hi : Γ ⊆ Γ') (hτ : <{ ~Γ ⊢ ~t ⦂ ~τ }>) : <{ ~Γ' ⊢ ~t ⦂ ~τ }> := by
  solution!
    induction hτ generalizing Γ' with
    | var _ x _ h =>
      constructor
      exact hi h
    | abs _ x _ _ _ _ ih =>
      constructor
      apply ih
      apply PartialMap.update_subset
      assumption
    | app _ _ _ _ _ _ _ ih₁ ih₂ =>
      constructor
      · apply ih₁
        exact hi
      · apply ih₂
        exact hi
    | const _ n => constructor
    | succ _ _ _ ih =>
      constructor
      apply ih
      exact hi
    | pred _ _ _ ih =>
      constructor
      apply ih
      exact hi
    | mult _ _ _ _ _ ih₁ ih₂ =>
      constructor
      · apply ih₁
        exact hi
      · apply ih₂
        exact hi
    | ite0 _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ =>
      constructor
      · apply ih₁
        exact hi
      · apply ih₂
        exact hi
      · apply ih₃
        exact hi
```

:::gradeTheorem "6" StlcArith.weakening
:::

The two helper lemmas that weakening is for are also proved just as they were
for the STLC.

```lean
-- SOLUTION
theorem weakening_empty (Γ : Context) (t : Tm) (τ : Ty) (hτ : <{ ∅ ⊢ ~t ⦂ ~τ }>) :
    <{ ~Γ ⊢ ~t ⦂ ~τ }> := by
  apply weakening ∅
  · intros x b contra
    contradiction
  · assumption

theorem substitution_preserves_typing (Γ : Context) (x : String) (τ' : Ty)
    (t v : Tm) (τ : Ty)
    (hτ : <{ ~x ↦ ~τ' ; ~Γ ⊢ ~t ⦂ ~τ }>) (hv : <{ ∅ ⊢ ~v ⦂ ~τ' }>) :
    <{ ~Γ ⊢ [~x := ~v] ~t ⦂ ~τ }> := by
  induction t generalizing Γ τ with
  | var y =>
    cases hτ with
    | var _ _ _ h =>
      by_cases hxy : x = y
      · subst hxy
        rw [PartialMap.update_eq] at h
        rw [subst_var_eq]
        have hτ'τ : τ' = τ := by
          apply Option.some.inj
          exact h
        subst hτ'τ
        apply weakening_empty
        exact hv
      · rw [PartialMap.update_neq hxy] at h
        rw [subst_var_ne _ _ _ hxy]
        constructor
        exact h
  | app t₁ t₂ ih₁ ih₂ =>
    cases hτ with
    | app _ _ _ _ _ h₁ h₂ =>
      rw [subst_app]
      constructor
      · apply ih₁
        exact h₁
      · apply ih₂
        exact h₂
  | abs y S t₁ ih =>
    cases hτ with
    | abs _ _ _ _ _ h =>
      by_cases hxy : x = y
      · subst hxy
        rw [subst_abs_eq]
        rw [PartialMap.update_shadow] at h
        constructor
        exact h
      · rw [subst_abs_ne _ _ _ _ _ hxy]
        rw [PartialMap.update_permute (Ne.symm hxy)] at h
        constructor
        apply ih
        exact h
  | const n =>
    cases hτ with
    | const =>
      rw [subst_const]
      constructor
  | succ t₁ ih =>
    cases hτ with
    | succ _ _ h =>
      rw [subst_succ]
      constructor
      apply ih
      exact h
  | pred t₁ ih =>
    cases hτ with
    | pred _ _ h =>
      rw [subst_pred]
      constructor
      apply ih
      exact h
  | mult t₁ t₂ ih₁ ih₂ =>
    cases hτ with
    | mult _ _ _ h₁ h₂ =>
      rw [subst_mult]
      constructor
      · apply ih₁
        exact h₁
      · apply ih₂
        exact h₂
  | ite0 t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    cases hτ with
    | ite0 _ _ _ _ _ h₁ h₂ h₃ =>
      rw [subst_ite0]
      constructor
      · apply ih₁
        exact h₁
      · apply ih₂
        exact h₂
      · apply ih₃
        exact h₃
-- END SOLUTION
```
:::::

::::::

### Preservation

:::suppressPreviousHeaderWhenTerse
:::

::::::full
:::::exercise (rating := 4) (name := "StlcArith.preservation")
_Hint_: you will need to define and prove the same helper lemmas we used
before.

```lean
theorem preservation (t t' : Tm) (τ : Ty)
    (hτ : <{ ∅ ⊢ ~t ⦂ ~τ }>) (hs : t ⟶ t') : <{ ∅ ⊢ ~t' ⦂ ~τ }> := by
  solution!
    generalize hΓ : (∅ : Context) = Γ at hτ
    induction hτ generalizing t' with
    | var => cases hs
    | abs => cases hs
    | const => cases hs
    | app Γ τ₁ τ₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      subst hΓ
      cases hs with
      | appAbs _ _ _ _ _ =>
        -- The one interesting case: the desired result is the substitution lemma.
        cases h₁ with
        | abs _ _ _ _ _ hb =>
          apply substitution_preserves_typing
          · exact hb
          · exact h₂
      | app1 _ t₁' _ h =>
        constructor
        · apply ih₁
          · exact h
          · rfl
        · exact h₂
      | app2 _ _ t₂' _ h =>
        constructor
        · exact h₁
        · apply ih₂
          · exact h
          · rfl
    | succ Γ t₁ h ih =>
      subst hΓ
      cases hs with
      | succ _ t₁' hst =>
        constructor
        apply ih
        · exact hst
        · rfl
      | succConst n => constructor
    | pred Γ t₁ h ih =>
      subst hΓ
      cases hs with
      | pred _ t₁' hst =>
        constructor
        apply ih
        · exact hst
        · rfl
      | predConst n => constructor
    | mult Γ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      subst hΓ
      cases hs with
      | multConst _ _ => constructor
      | mult1 _ t₁' _ hst =>
        constructor
        · apply ih₁
          · exact hst
          · rfl
        · exact h₂
      | mult2 _ _ t₂' _ hst =>
        constructor
        · exact h₁
        · apply ih₂
          · exact hst
          · rfl
    | ite0 Γ t₁ t₂ t₃ τ₀ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
      subst hΓ
      cases hs with
      | if0Step _ t₁' _ _ hst =>
        constructor
        · apply ih₁
          · exact hst
          · rfl
        · exact h₂
        · exact h₃
      | if0Zero => exact h₂
      | if0Nonzero => exact h₃
```
:::gradeTheorem "6" StlcArith.preservation
:::
:::::

::::::

### Progress

:::suppressPreviousHeaderWhenTerse
:::

::::::full

:::::exercise (rating := 4) (name := "StlcArith.progress")
```lean
theorem progress (t : Tm) (τ : Ty) (hτ : <{ ∅ ⊢ ~t ⦂ ~τ }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  solution!
    generalize hΓ : (∅ : Context) = Γ at hτ
    induction hτ with
    | var Γ x τ₁ h =>
      subst hΓ
      -- Contradictory: variables cannot be typed in an empty context.
      rw [PartialMap.getElem_empty] at h
      cases h
    | abs =>
      left
      constructor
    | const _ n =>
      left
      constructor
    | app Γ τ₁ τ₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      right
      subst hΓ
      cases ih₁ rfl with
      | inl hv₁ =>
        cases ih₂ rfl with
        | inl hv₂ =>
          -- `t₁` is a value of arrow type, so it is an abstraction, not a number.
          cases hv₁ with
          | abs x τ u =>
            exists <{ [~x := ~t₂] ~u }>
            apply Step.appAbs
            assumption
          | const n => cases h₁
        | inr hs₂ =>
          obtain ⟨t₂', h⟩ := hs₂
          exists <{ ~t₁ ~t₂' }>
          apply Step.app2 <;> assumption
      | inr hs₁ =>
        obtain ⟨t₁', h⟩ := hs₁
        exists <{ ~t₁' ~t₂ }>
        apply Step.app1
        assumption
    | succ Γ t₁ h ih =>
      right
      subst hΓ
      cases ih rfl with
      | inl hv =>
        cases hv with
        | abs => cases h
        | const n =>
          exists .const (1 + n)
          apply Step.succConst
      | inr hs =>
        obtain ⟨t₁', hst⟩ := hs
        exists <{ succ ~t₁' }>
        apply Step.succ
        assumption
    | pred Γ t₁ h ih =>
      right
      subst hΓ
      cases ih rfl with
      | inl hv =>
        cases hv with
        | abs => cases h
        | const n =>
          exists .const (n - 1)
          apply Step.predConst
      | inr hs =>
        obtain ⟨t₁', hst⟩ := hs
        exists <{ pred ~t₁' }>
        apply Step.pred
        assumption
    | mult Γ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      right
      subst hΓ
      cases ih₁ rfl with
      | inl hv₁ =>
        cases ih₂ rfl with
        | inl hv₂ =>
          cases hv₁ with
          | abs => cases h₁
          | const n₁ =>
            cases hv₂ with
            | abs => cases h₂
            | const n₂ =>
              exists .const (n₁ * n₂)
              apply Step.multConst
        | inr hs₂ =>
          obtain ⟨t₂', hst⟩ := hs₂
          exists <{ ~t₁ * ~t₂' }>
          apply Step.mult2 <;> assumption
      | inr hs₁ =>
        obtain ⟨t₁', hst⟩ := hs₁
        exists <{ ~t₁' * ~t₂ }>
        apply Step.mult1
        assumption
    | ite0 Γ t₁ t₂ t₃ τ₀ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
      right
      subst hΓ
      cases ih₁ rfl with
      | inl hv₁ =>
        cases hv₁ with
        | abs => cases h₁
        | const n =>
          cases n with
          | zero =>
            exists t₂
            apply Step.if0Zero
          | succ n' =>
            exists t₃
            apply Step.if0Nonzero
      | inr hs₁ =>
        obtain ⟨t₁', hst⟩ := hs₁
        exists <{ if0 ~t₁' then ~t₂ else ~t₃ }>
        apply Step.if0Step
        assumption
```
:::gradeTheorem "6" StlcArith.progress
:::
:::::

::::::

```lean
end StlcArith
```

:::dev PotentialImprovement
```
(a) Is there a type τ that makes
x ↦ τ ; ∅ ⊢ if0 ((λx:Nat. pred x) x.fst) then x.snd else (x.fst, x.fst) ⦂ Nat * Nat
provable? If so, what is it?
Answer: Yes: τ = Nat * (Nat * Nat).
(b) Are there types S and τ that make
∅ ⊢ λx:τ. λy:τ. x y ⦂ S
provable? If so, what are they?
Answer: No; it would have to be the case that τ = τ → S, but there can be no such
(finite) type τ.

-----------------------

(a) Suppose we add a term foo with the following evaluation rules:
(λx:A. x) ⟶ foo    (foo1)
foo ⟶ 0            (foo2)
Do progress and preservation continue to hold after this change, or does one (or do both) fail?
Why?
Answer: Preservation fails, since we have no typing rules for foo but λx:A. x has type A → A.
Progress still holds: we are only adding to the step relation, and this can never damage progress.
(b) Suppose we add a term zap, with the following evaluation rule
t ⟶ zap            (zap)
and the following typing rule:
Γ ⊢ zap ⦂ τ        (zap)
Do progress and preservation continue to hold after this change, or does one (or do both) fail?
Why?
Answer: Both properties continue to hold. Progress holds trivially: every term can take a step to
zap! Preservation holds because zap can have any type.
(c) Suppose we change appAbs to the following rule:
(λx:τ. t₁₂) t₂ ⟶ [x:=t₂]t₁₂    (appAbs')
Do progress and preservation continue to hold after this change, or does one (or do both) fail?
Why?
Answer: Both properties continue to hold. (Substitution preserves typing irrespective of whether
the term being substituted into another term is a value or not.)
```
:::
