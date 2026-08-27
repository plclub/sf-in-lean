import SFLMeta
import TS.Stlc
import LF.CustomTactics
open Verso.Genre Manual
open SFLMeta

set_option maxHeartbeats 1000000

#doc (Manual) "StlcProp: Properties of STLC" =>
%%%
tag := "StlcProp"
htmlSplit := .never
file := some "StlcProp"
%%%

:::dev "Claude" NOW
The document-level `set_option maxHeartbeats 1000000` above is needed by
`substitution_preserves_typing`, and it has to be *document-level*: the cost is
not in the proof itself (the same proof elaborates well inside budget as plain
Lean) but in Verso's InlineLean highlighting pass, which re-drives elaboration
to attach type and hover information. That pass honors only document-level
options — a `set_option maxHeartbeats ... in` on the theorem was verified not
to help here, and neither does splitting the code block, since the budget is
per-declaration. `LF/IndPropRegexpVerso.lean` carries the same override and
documents the mechanism at length.

The way to remove this would be to break the substitution lemma's variable and
abstraction cases out as named helper lemmas, so each is highlighted against
its own fresh budget — the pattern `IndPropRegexp` uses for `star_app_aux`.
That is a pedagogy call (it changes how the central proof of the chapter
reads), so it is left for review rather than done here.
:::

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
    | "λ" x ":" T "." t ("abstraction")
    | t t ("application")
    | "true" ("constant true")
    | "false" ("constant false")
    | "if" t "then" t "else" t ("conditional") ;
```
Values:
```bnf
v ::= "λ" x ":" T "." t | "true" | "false" ;
```

Substitution:
```display
[x:=s]x               = s
[x:=s]y               = y                     if x ≠ y
[x:=s](λx:T. t)       = λx:T. t
[x:=s](λy:T. t)       = λy:T. [x:=s]t         if x ≠ y
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
                        (λx:T. t) v ⟶ [x:=v]t

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
                              Γ x = T₁
                            ------------                       (var)
                             Γ ⊢ x ⦂ T₁

                        x ↦ T₂ ; Γ ⊢ t₁ ⦂ T₁
                      -------------------------                (abs)
                       Γ ⊢ λx:T₂. t₁ ⦂ T₂ → T₁

                          Γ ⊢ t₁ ⦂ T₂ → T₁
                            Γ ⊢ t₂ ⦂ T₂
                         ------------------                    (app)
                           Γ ⊢ t₁ t₂ ⦂ T₁

                          -----------------                    (tru)
                           Γ ⊢ true ⦂ Bool

                         ------------------                    (fls)
                          Γ ⊢ false ⦂ Bool

             Γ ⊢ t₁ ⦂ Bool    Γ ⊢ t₂ ⦂ T₁    Γ ⊢ t₃ ⦂ T₁
            ---------------------------------------------      (ite)
                   Γ ⊢ if t₁ then t₂ else t₃ ⦂ T₁
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
theorem canonical_forms_bool (t : Tm) (hT : <{ ∅ ⊢ ~t ⦂ Bool }>) (hv : t.IsValue) :
    t = <{ true }> ∨ t = <{ false }> := by
  cases hv with
  | abs x T t₁ => cases hT
  | tru => left; rfl
  | fls => right; rfl

theorem canonical_forms_fun (t : Tm) (T₁ T₂ : Ty)
    (hT : <{ ∅ ⊢ ~t ⦂ ~T₁ → ~T₂ }>) (hv : t.IsValue) :
    ∃ x u, t = <{ λ ~x : ~T₁ . ~u }> := by
  cases hv with
  | abs x T t₁ => cases hT with | abs _ _ _ _ _ _ =>
    exists x, t₁
  | tru => cases hT
  | fls => cases hT
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

```lean
theorem progress (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  generalize hΓ : (∅ : Context) = Γ at hT
  induction hT with
  | var Γ x T₁ h =>
    subst hΓ
    -- Contradictory: variables cannot be typed in an empty context.
    rw [PartialMap.getElem_empty] at h
    cases h
  | abs => left; constructor
  | tru => left; constructor
  | fls => left; constructor
  | app Γ T₁ T₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    -- `t = t₁ t₂`.  Proceed by cases on whether `t₁` is a value or steps.
    right
    cases ih₁ hΓ with
    | inl hv₁ =>
      cases ih₂ hΓ with
      | inl hv₂ =>
        obtain ⟨x, u, rfl⟩ := canonical_forms_fun t₁ _ _ (hΓ ▸ h₁) hv₁
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
  | ite Γ t₁ t₂ t₃ T₁ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    right
    cases ih₁ hΓ with
    | inl hv₁ =>
      cases canonical_forms_bool t₁ (hΓ ▸ h₁) hv₁ with
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

::::full
_Proof_: By induction on the derivation of `⊢ t ⦂ T`.

- The last rule of the derivation cannot be `HasType.var`, since a
  variable is never well typed in an empty context.

- The `HasType.tru`, `HasType.fls`, and `HasType.abs` cases are trivial, since in
  each of these cases we can see by inspecting the rule that `t`
  is a value.

- If the last rule of the derivation is `HasType.app`, then `t` has the
  form `t₁ t₂` for some `t₁` and `t₂`, where `⊢ t₁ ⦂ T₂ → T`
  and `⊢ t₂ ⦂ T₂` for some type `T₂`.  The induction hypothesis
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

::::::full
:::::exercise (rating := 3) (name := "progress_from_term_ind") (level := Advanced)

Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

```lean
-- IN PROGRESS
theorem progress' (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  solution!
    induction t generalizing T with
    | var x =>
      cases hT with
      | var _ _ _ h => rw [PartialMap.getElem_empty] at h; cases h
    | abs x T₂ t₁ _ => exact .inl (.abs ..)
    | tru => exact .inl .tru
    | fls => exact .inl .fls
    | app t₁ t₂ ih₁ ih₂ =>
      right
      cases hT with
      | app _ _ T₂ _ _ h₁ h₂ =>
        cases ih₁ _ h₁ with
        | inl hv₁ =>
          obtain ⟨x, u, rfl⟩ := canonical_forms_fun t₁ _ _ h₁ hv₁
          cases ih₂ _ h₂ with
          | inl hv₂ => exact ⟨<{ [~x := ~t₂] ~u }>, .appAbs x T₂ u t₂ hv₂⟩
          | inr hs₂ => obtain ⟨t₂', h⟩ := hs₂; exact ⟨_, .app2 _ t₂ t₂' hv₁ h⟩
        | inr hs₁ => obtain ⟨t₁', h⟩ := hs₁; exact ⟨_, .app1 t₁ t₁' t₂ h⟩
    | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
      right
      cases hT with
      | ite _ _ _ _ _ h₁ h₂ h₃ =>
        cases ih₁ _ h₁ with
        | inl hv₁ =>
          cases canonical_forms_bool t₁ h₁ hv₁ with
          | inl he => subst he; exact ⟨t₂, .ifTrue t₂ t₃⟩
          | inr he => subst he; exact ⟨t₃, .ifFalse t₂ t₃⟩
        | inr hs₁ => obtain ⟨t₁', h⟩ := hs₁; exact ⟨_, .ifStep t₁ t₁' t₂ t₃ h⟩
```
:::::
:::autogradedHole progress'
:::

:::gradeTheorem "3" progress'
:::
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
-- IN PROGRESS
theorem weakening (Γ Γ' : Context) (t : Tm) (T : Ty)
    (hi : Γ ⊆ Γ') (hT : <{ ~Γ ⊢ ~t ⦂ ~T }>) : <{ ~Γ' ⊢ ~t ⦂ ~T }> := by
  induction hT generalizing Γ' with
  | var _ x _ h => exact .var _ x _ (hi h)
  | abs _ x _ _ _ _ ih => exact .abs _ x _ _ _ (ih _ (PartialMap.update_subset _ _ _ _ hi))
  | app _ _ _ _ _ _ _ ih₁ ih₂ => exact .app _ _ _ _ _ (ih₁ _ hi) (ih₂ _ hi)
  | tru => exact .tru _
  | fls => exact .fls _
  | ite _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ => exact .ite _ _ _ _ _ (ih₁ _ hi) (ih₂ _ hi) (ih₃ _ hi)
```

:::slidebreak
:::

The following simple corollary is what we actually need below.

```lean
theorem weakening_empty (Γ : Context) (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) :
    <{ ~Γ ⊢ ~t ⦂ ~T }> :=
  weakening _ _ _ _
    (fun h => by
      rw [PartialMap.getElem_empty] at h
      cases h) hT
```

## The Substitution Lemma

Now we come to the conceptual heart of the proof that reduction
preserves types — namely, the observation that _substitution_
preserves types.

::::full
Formally, the so-called _substitution lemma_ says this:
Suppose we have a term `t` with a free variable `x`, and suppose
we've assigned a type `T` to `t` under the assumption that `x` has
some type `U`.  Also, suppose that we have some other term `v` and
that we've shown that `v` has type `U`.  Then, since `v` satisfies
the assumption we made about `x` when typing `t`, we can
substitute `v` for each of the occurrences of `x` in `t` and
obtain a new term that still has type `T`.
::::

::::terse
The _substitution lemma_ says:

- Suppose we have a term `t` with a free variable `x`, and
  suppose we've been able to assign a type `T` to `t` under the
  assumption that `x` has some type `U`.

- Also, suppose that we have some other term `v` and that we've
  shown that `v` has type `U`.

- Then we can substitute `v` for each of the occurrences of
  `x` in `t` and obtain a new term that still has type `T`.
::::

:::slidebreak
:::

```lean
-- IN PROGRESS
theorem substitution_preserves_typing (Γ : Context) (x : String) (U : Ty)
    (t v : Tm) (T : Ty)
    (hT : <{ ~x ↦ ~U ; ~Γ ⊢ ~t ⦂ ~T }>) (hv : <{ ∅ ⊢ ~v ⦂ ~U }>) :
    <{ ~Γ ⊢ [~x := ~v] ~t ⦂ ~T }> := by
  -- By induction on `t`; in each case we get at the derivation of `hT`.
  induction t generalizing Γ T with
  | var y =>
    cases hT with
    | var _ _ _ h =>
      by_cases hxy : x = y
      · subst hxy
        rw [PartialMap.update_eq] at h
        rw [subst_var_eq]
        have hUT : U = T := Option.some.inj h
        subst hUT
        exact weakening_empty _ _ _ hv
      · rw [PartialMap.update_neq hxy] at h
        rw [subst_var_ne _ _ _ hxy]
        exact .var _ y _ h
  | app t₁ t₂ ih₁ ih₂ =>
    cases hT with
    | app _ _ _ _ _ h₁ h₂ => rw [subst_app]; exact .app _ _ _ _ _ (ih₁ _ _ h₁) (ih₂ _ _ h₂)
  | abs y S t₁ ih =>
    cases hT with
    | abs _ _ _ _ _ h =>
      by_cases hxy : x = y
      · subst hxy
        rw [subst_abs_eq]
        rw [PartialMap.update_shadow] at h
        exact .abs _ _ _ _ _ h
      · rw [subst_abs_ne _ _ _ _ _ hxy]
        rw [PartialMap.update_permute (Ne.symm hxy)] at h
        exact .abs _ _ _ _ _ (ih _ _ h)
  | tru => cases hT with | tru => rw [subst_tru]; exact .tru _
  | fls => cases hT with | fls => rw [subst_fls]; exact .fls _
  | ite c t e ihc iht ihe =>
    cases hT with
    | ite _ _ _ _ _ h₁ h₂ h₃ =>
      rw [subst_ite]
      exact .ite _ _ _ _ _ (ihc _ _ h₁) (iht _ _ h₂) (ihe _ _ h₃)
```

::::full
The substitution lemma can be viewed as a kind of "commutation
property."  Intuitively, it says that substitution and typing can
be done in either order: we can either assign types to the terms
`t` and `v` separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to ` `x:=v` t`; the result is the same either
way.

_Proof_: We show, by induction on `t`, that for all `T` and
`Γ`, if `x ↦ U; Γ ⊢ t ⦂ T` and `⊢ v ⦂ U`, then
`Γ ⊢ [x:=v]t ⦂ T`.

  - If `t` is a variable there are two cases to consider,
    depending on whether `t` is `x` or some other variable.

      - If `t = x`, then from the fact that `x ↦ U; Γ ⊢ x ⦂ T` we conclude that `U = T`.  We must show that `[x:=v]x = v` has type `T` under `Γ`, given the assumption that
        `v` has type `U = T` under the empty context.  This
        follows from the weakening lemma.

      - If `t` is some variable `y` that is not equal to `x`, then
        we need only note that `y` has the same type under `x ↦ U; Γ` as under `Γ`.

  - If `t` is an abstraction `λy:S. t₀`, then `T = S→T₁` and
    the IH tells us, for all `Γ'` and `T₀`, that if `x ↦ U; Γ' ⊢ t₀ ⦂ T₀`, then `Γ' ⊢ [x:=v]t₀ ⦂ T₀`.
    Moreover, by inspecting the typing rules we see it must be
    the case that `y ↦ S; x ↦ U; Γ ⊢ t₀ ⦂ T₁`.

    The substitution in the conclusion behaves differently
    depending on whether `x` and `y` are the same variable.

    First, suppose `x = y`.  Then, by the definition of
    substitution, `[x:=v]t = t`, so we just need to show `Γ ⊢ t ⦂ T`.  Using `HasType.abs`, we need to show that `y ↦ S; Γ ⊢ t₀ ⦂ T₁`. But we know `y ↦ S; x ↦ U; Γ ⊢ t₀ ⦂ T₁`,
    and the claim follows since `x = y`.

    Second, suppose `x <> y`. Again, using `HasType.abs`,
    we need to show that `y ↦ S; Γ ⊢ [x:=v]t₀ ⦂ T₁`.
    Since `x <> y`, we have
    `y ↦ S; x ↦ U; Γ = x ↦ U; y ↦ S; Γ`. So
    we have `x ↦ U; y ↦ S; Γ ⊢ t₀ ⦂ T₁`. Then, the
    the IH applies (taking `Γ' = y ↦ S; Γ`), giving us
    `y ↦ S; Γ ⊢ [x:=v]t₀ ⦂ T₁`, as required.

  - If `t` is an application `t₁ t₂`, the result follows
    straightforwardly from the definition of substitution and the
    induction hypotheses.

  - The remaining cases are similar to the application case.
::::

::::full
One technical subtlety in the statement of the above lemma is that
we assume `v` has type `U` in the _empty_ context — in other
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
-- IN PROGRESS
theorem substitution_preserves_typing_from_typing_ind (Γ : Context) (x : String) (U : Ty)
    (t v : Tm) (T : Ty)
    (hT : <{ ~x ↦ ~U ; ~Γ ⊢ ~t ⦂ ~T }>) (hv : <{ ∅ ⊢ ~v ⦂ ~U }>) :
    <{ ~Γ ⊢ [~x := ~v] ~t ⦂ ~T }> := by
  solution!
    generalize hΓ : (x →ₚ U ; Γ) = Γ₀ at hT
    induction hT generalizing Γ with
    | var _ y T₁ h =>
      subst hΓ
      by_cases hxy : x = y
      · subst hxy
        rw [PartialMap.update_eq] at h
        rw [subst_var_eq]
        have hUT : U = T₁ := Option.some.inj h
        subst hUT
        exact weakening_empty _ _ _ hv
      · rw [PartialMap.update_neq hxy] at h
        rw [subst_var_ne _ _ _ hxy]
        exact .var _ y _ h
    | abs _ y _ _ _ hb ih =>
      subst hΓ
      by_cases hxy : x = y
      · subst hxy
        rw [subst_abs_eq]
        rw [PartialMap.update_shadow] at hb
        exact .abs _ _ _ _ _ hb
      · rw [subst_abs_ne _ _ _ _ _ hxy]
        exact .abs _ _ _ _ _ (ih _ (PartialMap.update_permute hxy))
    | app _ _ _ _ _ _ _ ih₁ ih₂ =>
      rw [subst_app]; exact .app _ _ _ _ _ (ih₁ _ hΓ) (ih₂ _ hΓ)
    | tru => rw [subst_tru]; exact .tru _
    | fls => rw [subst_fls]; exact .fls _
    | ite _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ =>
      rw [subst_ite];
      constructor <;> simp_all
```
:::autogradedHole substitution_preserves_typing_from_typing_ind
:::

:::gradeTheorem "3" substitution_preserves_typing_from_typing_ind
:::
:::::


::::::

## Main Theorem

We now have the ingredients we need to prove preservation: if a
closed, well-typed term `t` has type `T` and takes a step to `t'`,
then `t'` is also a closed term with type `T`.  In other words,
the small-step reduction relation preserves types.

```lean
-- IN PROGRESS
theorem preservation (t t' : Tm) (T : Ty)
    (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) (hs : t ⟶ t') : <{ ∅ ⊢ ~t' ⦂ ~T }> := by
  generalize hΓ : (∅ : Context) = Γ at hT
  induction hT generalizing t' with
  | var => cases hs
  | abs => cases hs
  | tru => cases hs
  | fls => cases hs
  | app Γ T₁ T₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    subst hΓ
    cases hs with
    | appAbs _ _ _ _ _ =>
      -- The one interesting case: the desired result is the substitution lemma.
      cases h₁ with
      | abs _ _ _ _ _ hb => exact substitution_preserves_typing _ _ _ _ _ _ hb h₂
    | app1 _ t₁' _ h => exact .app _ _ _ _ _ (ih₁ t₁' h rfl) h₂
    | app2 _ _ t₂' _ h => exact .app _ _ _ _ _ h₁ (ih₂ t₂' h rfl)
  | ite Γ t₁ t₂ t₃ T₁ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    subst hΓ
    cases hs with
    | ifTrue => exact h₂
    | ifFalse => exact h₃
    | ifStep _ t₁' _ _ h => exact .ite _ _ _ _ _ (ih₁ t₁' h rfl) h₂ h₃
```

::::full
_Proof_: By induction on the derivation of `⊢ t ⦂ T`.

- We can immediately rule out `HasType.var`, `HasType.abs`, `HasType.tru`, and
  `HasType.fls` as final rules in the derivation, since in each of these
  cases `t` cannot take a step.

- If the last rule in the derivation is `HasType.app`, then `t = t₁ t₂`,
  and there are subderivations showing that `⊢ t₁ ⦂ T₂→T` and
  `⊢ t₂ ⦂ T₂` plus two induction hypotheses: (1) `t₁ ⟶ t₁'`
  implies `⊢ t₁' ⦂ T₂→T` and (2) `t₂ ⟶ t₂'` implies `⊢ t₂' ⦂ T₂`.  There are now three subcases to consider, one for
  each rule that could be used to show that `t₁ t₂` takes a step
  to `t'`.

    - If `t₁ t₂` takes a step by `Step.app1`, with `t₁` stepping to
      `t₁'`, then, by the first IH, `t₁'` has the same type as
      `t₁` (`⊢ t₁' ⦂ T₂→T`), and hence by `HasType.app` `t₁' t₂` has
      type `T`.

    - The `Step.app2` case is similar, using the second IH.

    - If `t₁ t₂` takes a step by `Step.appAbs`, then `t₁ = λx:T₀. t₀` and `t₁ t₂` steps to `[x0:=t₂]t₀`; the desired
      result now follows from the substitution lemma.

- If the last rule in the derivation is `HasType.ite`, then `t = if t₁ then t₂ else t₃`, with `⊢ t₁ ⦂ Bool`, `⊢ t₂ ⦂ T₁`, and
  `⊢ t₃ ⦂ T₁`, and with three induction hypotheses: (1) `t₁ ⟶ t₁'` implies `⊢ t₁' ⦂ Bool`, (2) `t₂ ⟶ t₂'` implies `⊢ t₂' ⦂ T₁`, and (3) `t₃ ⟶ t₃'` implies `⊢ t₃' ⦂ T₁`.

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
if `t ⟶ t'` and `empty ⊢ t' ⦂ T`, then `empty ⊢ t ⦂ T`.
Show this by giving a counter-example that does _not involve
conditionals_.

:::solution
For example,
`((\a:Bool→Bool, λy:Bool. y) true)` is ill typed, but it evaluates
to the well-typed term `λy:Bool. y`,
:::
:::dev
RAB: This solution has to be rewritten; it is unreadable.
:::
```lean
theorem not_subject_expansion :
    ∃ (t t' : Tm) (T : Ty), t ⟶ t' ∧ <{ ∅ ⊢ ~t' ⦂ ~T }> ∧ ¬ <{ ∅ ⊢ ~t ⦂ ~T }> := by
    solution!(
      exists <{ (λ x : Bool → Bool . true) true }>, <{true}>, <{Bool}>
      constructor
      . constructor; constructor
      . constructor
        . constructor
        . intro contra
          inversion contra with
          | app T h₁ h₂ =>
            inversion h₂
            . inversion h₁
      )
```

::::hide
```
/- Alternative formulation. -/
Theorem not_subject_expansion_alt:
  ~ (forall t t' T, t ⟶ t' /\ <{ empty ⊢ t' ⦂ T }> -> <{ empty ⊢ t ⦂ T }>).
Proof.
  solution!
    intro HSE.
    assert (HT: <{ empty ⊢ (\x:(Bool -> Bool), \y:Bool, y) true ⦂ Bool -> Bool}> ).
    { apply HSE with (t' := <{ \y:Bool, y }>).
      split.
      { apply Step.appAbs. apply v_true. }
      { apply HasType.abs. apply HasType.var. reflexivity. } }
    inversion HT.
    inversion H2.
    rewrite <- H10 in H4.
    inversion H4.
  Qed.
```
::::

:::grade
`GRADE_MANUAL 2: subject_expansion_stlc`
:::
:::::

::::::

# Type Soundness

:::suppressPreviousHeaderWhenTerse
:::

::::::full
:::::exercise (rating := 2) (name := "type_soundness")
Put progress and preservation together and show that a well-typed
term can _never_ reach a stuck state.

```lean
def Tm.IsStuck (t : Tm) : Prop := IsNormalForm Step t ∧ ¬ t.IsValue

theorem type_soundness (t t' : Tm) (T : Ty)
    (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) (hm : t ⟶* t') : ¬ t'.IsStuck := by
  intro hst
  obtain ⟨hnf, hnv⟩ := hst
  solution!
    induction hm with
    | refl u =>
      cases progress u T hT with
      | inl hv => exact hnv hv
      | inr hs => exact hnf hs
    | step u w z h₁ _ ih => exact ih (preservation u w T hT h₁) hnf hnv
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
-- AI
theorem unique_types (Γ : Context) (e : Tm) (T T' : Ty)
    (h : <{ ~Γ ⊢ ~e ⦂ ~T }>) (h' : <{ ~Γ ⊢ ~e ⦂ ~T' }>) : T = T' := by
  solution!
    induction h generalizing T' with
    | var _ _ _ hx => cases h' with | var _ _ _ hx' => exact Option.some.inj (hx.symm.trans hx')
    | abs _ _ _ _ _ _ ih => cases h' with | abs _ _ _ _ _ hb' => rw [ih _ hb']
    | app _ _ _ _ _ _ _ ih₁ _ =>
      cases h' with
      | app _ _ _ _ _ hf' _ => exact (Ty.arrow.inj (ih₁ _ hf')).2
    | tru => cases h' with | tru => rfl
    | fls => cases h' with | fls => rfl
    | ite _ _ _ _ _ _ _ _ _ ih₂ _ => cases h' with | ite _ _ _ _ _ _ h₂' _ => exact ih₂ _ h₂'
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

More technically, a variable `x` _appears free in_ a term _t_ if
`t` contains some occurrence of `x` that is not under an
abstraction labeled `x`. For example:
  - `y` appears free, but `x` does not, in `λx:T→U. x y`
  - both `x` and `y` appear free in `(λx:T→U. x y) x`
  - no variables appear free in `λx:T→U. λy:T. x y`

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
  | abs (y : String) (T₁ : Ty) (t₁ : Tm) (hne : y ≠ x) (h : x ∈ᶠ t₁) :
      x ∈ᶠ <{ λ ~y : ~T₁ . ~t₁ }>
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

:::::exercise (rating := 1) (name := "afi")
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

```lean
-- IN PROGRESS
theorem free_in_context (x : String) (t : Tm) (T : Ty) (Γ : Context)
    (ha : x ∈ᶠ t) (hT : <{ ~Γ ⊢ ~t ⦂ ~T }>) : ∃ T', Γ[x] = some T' := by
  solution!
    induction ha generalizing Γ T with
    | var => cases hT with | var _ _ _ h => exact ⟨_, h⟩
    | app1 _ _ _ ih => cases hT with | app _ _ _ _ _ h₁ _ => exact ih _ _ h₁
    | app2 _ _ _ ih => cases hT with | app _ _ _ _ _ _ h₂ => exact ih _ _ h₂
    | abs y _ _ hne _ ih =>
      cases hT with
      | abs _ _ _ _ _ hb =>
        obtain ⟨T', h⟩ := ih _ _ hb
        rw [PartialMap.update_neq hne] at h
        exact ⟨T', h⟩
    | ite1 _ _ _ _ ih => cases hT with | ite _ _ _ _ _ h₁ _ _ => exact ih _ _ h₁
    | ite2 _ _ _ _ ih => cases hT with | ite _ _ _ _ _ _ h₂ _ => exact ih _ _ h₂
    | ite3 _ _ _ _ ih => cases hT with | ite _ _ _ _ _ _ _ h₃ => exact ih _ _ h₃
```

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

- The only remaining case is `AppearsFreeIn.abs`.  In this case `t = λy:T₁. t₁` and `x` appears free in `t₁`, and we also know that
  `x` is different from `y`.  The difference from the previous
  cases is that, whereas `t` is well typed under `Γ`, its body
  `t₁` is well typed under `y ↦ T₁; Γ`, so the IH allows us
  to conclude that `x` is assigned some type by the extended
  context `y ↦ T₁; Γ`.  To conclude that `Γ` assigns a
  type to `x`, we appeal to lemma `PartialMap.update_neq`, noting that `x`
  and `y` are different variables.

:::::exercise (rating := 2) (name := "free_in_context")
Complete the following proof.

:::::

From the `free_in_context` lemma, it immediately follows that any
term `t` that is well typed in the empty context is closed (it has
no free variables).

:::::exercise (rating := 2) (name := "typable_empty__closed")
```lean
theorem typable_empty_closed (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) : t.Closed := by
  solution!
    intro x ha
    obtain ⟨T', hc⟩ := free_in_context x t T ∅ ha hT
    rw [PartialMap.getElem_empty] at hc
    cases hc
```
:::::

Finally, we establish _context invariance_.  It is useful in cases
when we have a proof of some typing relation `Γ ⊢ t ⦂ T`,
and we need to replace `Γ` by a different context `Γ'`.
When is it safe to do this?  Intuitively, it must at least be the
case that `Γ'` assigns the same types as `Γ` to all the
variables that appear free in `t`. In fact, this is the only
condition that is needed.

```lean
-- IN PROGRESS
theorem context_invariance (Γ Γ' : Context) (t : Tm) (T : Ty)
    (hT : <{ ~Γ ⊢ ~t ⦂ ~T }>) (hf : ∀ x, x ∈ᶠ t → Γ[x] = Γ'[x]) :
    <{ ~Γ' ⊢ ~t ⦂ ~T }> := by
  solution!
    induction hT generalizing Γ' with
    | var _ x _ h => exact .var _ x _ ((hf x .var) ▸ h)
    | abs _ y _ _ _ _ ih =>
      refine .abs _ _ _ _ _ (ih _ ?_)
      intro z hz
      by_cases hyz : y = z
      · subst hyz; rw [PartialMap.update_eq, PartialMap.update_eq]
      -- The only tricky step.
      · rw [PartialMap.update_neq hyz, PartialMap.update_neq hyz]
        exact hf z (.abs y _ _ hyz hz)
    | app _ _ _ t₁ t₂ _ _ ih₁ ih₂ =>
      exact .app _ _ _ _ _ (ih₁ _ (fun z hz => hf z (.app1 t₁ t₂ hz)))
                           (ih₂ _ (fun z hz => hf z (.app2 t₁ t₂ hz)))
    | tru => exact .tru _
    | fls => exact .fls _
    | ite _ t₁ t₂ t₃ _ _ _ _ ih₁ ih₂ ih₃ =>
      exact .ite _ _ _ _ _ (ih₁ _ (fun z hz => hf z (.ite1 t₁ t₂ t₃ hz)))
                           (ih₂ _ (fun z hz => hf z (.ite2 t₁ t₂ t₃ hz)))
                           (ih₃ _ (fun z hz => hf z (.ite3 t₁ t₂ t₃ hz)))
```

_Proof_: By induction on the derivation of `Γ ⊢ t ⦂ T`.

- If the last rule in the derivation was `HasType.var`, then `t = x` and
  `Γ x = T`.  By assumption, `Γ' x = T` as well, and hence
  `Γ' ⊢ t ⦂ T` by `HasType.var`.

- If the last rule was `HasType.abs`, then `t = λy:T₂. t₁`, with `T = T₂ → T₁` and `y ↦ T₂; Γ ⊢ t₁ ⦂ T₁`.  The induction
  hypothesis states that for any context `Γ''`, if `y ↦ T₂; Γ` and `Γ''` assign the same types to all the free
  variables in `t₁`, then `t₁` has type `T₁` under `Γ''`.
  Let `Γ'` be a context which agrees with `Γ` on the free
  variables in `t`; we must show `Γ' ⊢ λy:T₂. t₁ ⦂ T₂ → T₁`.

  By `HasType.abs`, it suffices to show that `y ↦ T₂; Γ' ⊢ t₁ ⦂ T₁`.  By the IH (setting `Γ'' = y ↦ T₂;Γ'`), it
  suffices to show that `y ↦ T₂;Γ` and `y ↦ T₂;Γ'` agree
  on all the variables that appear free in `t₁`.

  Any variable occurring free in `t₁` must be either `y` or some
  other variable.  `y ↦ T₂; Γ` and `y ↦ T₂; Γ'` clearly
  agree on `y`.  Otherwise, note that any variable other than `y`
  that occurs free in `t₁` also occurs free in `t = λy:T₂. t₁`,
  and by assumption `Γ` and `Γ'` agree on all such
  variables; hence so do `y ↦ T₂; Γ` and `y ↦ T₂; Γ'`.

- If the last rule was `HasType.app`, then `t = t₁ t₂`, with `Γ ⊢ t₁ ⦂ T₂ → T` and `Γ ⊢ t₂ ⦂ T₂`.  One induction
  hypothesis states that for all contexts `Γ'`, if `Γ'`
  agrees with `Γ` on the free variables in `t₁`, then `t₁` has
  type `T₂ → T` under `Γ'`; there is a similar IH for `t₂`.
  We must show that `t₁ t₂` also has type `T` under `Γ'`,
  given the assumption that `Γ'` agrees with `Γ` on all
  the free variables in `t₁ t₂`.  By `HasType.app`, it suffices to show
  that `t₁` and `t₂` each have the same type under `Γ'` as
  under `Γ`.  But all free variables in `t₁` are also free in
  `t₁ t₂`, and similarly for `t₂`; hence the desired result
  follows from the induction hypotheses.

:::::exercise (rating := 3) (name := "context_invariance")
Complete the following proof.

:::::

The context invariance lemma can actually be used in place of the
weakening lemma to prove the crucial substitution lemma stated
earlier.
::::::

# Additional Exercises

:::suppressPreviousHeaderWhenTerse
:::

::::::full
:::::exercise (rating := 1) (name := "progress_preservation_statement")
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

::::hide
```
 Theorem progress' :
 FILL IN HERE
Proof. apply progress. Qed.
```
::::

:::solution
COMMENT: `untagged (* .. *) comment at prose position in the Rocq source — probably an error there; decide whether it is book prose or an author note`
See progress and preservation from before.
:::

:::grade
`GRADE_MANUAL 1: progress_preservation_statement`
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation1") (manual := true)
Suppose we add a new term `zap` with the following reduction rule

```display
---------                  (ST_Zap)
t --> zap
```

and the following typing rule:

```display
-------------------           (T_Zap)
Γ ⊢ zap ⦂ T
```

Which of the following properties of the STLC remain true in
the presence of these rules?  For each property, write either
"remains true" or "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

:::solution
        - Becomes false. For instance `(if true then false else true) ⟶ false`
and `(if true then false else true) ⟶ zap`.
:::

- Progress

:::solution
- Remains true. Every term (including `zap`) can take a step to `zap`.
:::

- Preservation

:::solution
- Remains true. `zap` can have any type.
:::

:::grade
`GRADE_MANUAL 2: stlc_variation1`
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation2") (manual := true)
Suppose instead that we add a new term `foo` with the following
reduction rules:

```display
-----------------                (ST_Foo1)
(\x:A, x) --> foo

  ------------                   (ST_Foo2)
  foo --> true
```

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

:::solution
```
        - Becomes false. The term [(\x:Bool, x) true] might step
to either [true] by the rule Step.appAbs or
to [foo true] by the rule Step.app1 and ST_Foo1.
```
:::

- Progress

:::solution
        - Remains true. We are only adding to the step relation, and
this can never damage progress.
:::

- Preservation

:::solution
```
        - Becomes false. For example,
[⊢ \x:Bool,x ⦂ Bool->Bool] and [(\x:Bool,x) --> foo] by (ST_Foo1),
but, since we have no typing rules for foo, we cannot prove that
[⊢ foo ⦂ Bool->Bool].
```
:::

:::grade
`GRADE_MANUAL 2: stlc_variation2`
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation3") (manual := true)
Suppose instead that we remove the rule `Step.app1` from the `step`
relation. Which of the following properties of the STLC remain
true in the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

:::solution
        - Remains true. Removing reduction rules can only make `step`
more deterministic.
:::

- Progress

:::solution
        - Becomes false. For example,
`((\x:Bool→Bool, \y:Bool→Bool, x) (λz:Bool. z)) (λz:Bool. z)`
is well typed, but stuck.
:::

- Preservation

:::solution
- Remains true. Removing reduction rules can't break preservation.
:::

:::grade
`GRADE_MANUAL 2: stlc_variation3`
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation4")
Suppose instead that we add the following new rule to the
reduction relation:

```display
----------------------------------        (ST_FunnyIfTrue)
(if true then t₁ else t₂) --> true
```

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

:::solution
        - Becomes false, for instance:
`(if true then false else false) ⟶ false` and
`(if true then false else false) ⟶ true`
:::

- Progress

:::solution
        - Remains true. We are only adding to the step relation, and
this can never damage progress.
:::

- Preservation

:::solution
        - Becomes false. For example,
`⊢ if true then (λx:Bool. x) else (λx:Bool. x) ⦂ Bool→Bool`
and `(if true then (λx:Bool. x) else (λx:Bool. x)) ⟶ true`
but it's not the case that `⊢ true ⦂ Bool → Bool`.
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation5")
Suppose instead that we add the following new rule to the typing
relation:

```display
Γ ⊢ t₁ ⦂ Bool->Bool->Bool
    Γ ⊢ t₂ ⦂ Bool
---------------------------------       (T_FunnyApp)
   Γ ⊢ t₁ t₂ ⦂ Bool
```

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

:::solution
        - Remains true. We are only adding to the typing relation, and
this can never damage determinism of `step`.
:::

- Progress

:::solution
```
        - Remains true. Since the new rule still requires that [t₁] is
a function we can still apply Step.appAbs to show progress.
```
:::

- Preservation

:::solution
        - Becomes false. For example,
`⊢ λx:Bool. λy:Bool. x true ⦂ Bool`
and `(λx:Bool. λy:Bool. x) true ⟶ λy:Bool. true`
but it's not the case that `⊢ λy:Bool. true ⦂ Bool`
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation6")
Suppose instead that we add the following new rule to the typing
relation:

```display
Γ ⊢ t₁ ⦂ Bool
Γ ⊢ t₂ ⦂ Bool
------------------------            (T_FunnyApp')
Γ ⊢ t₁ t₂ ⦂ Bool
```

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

:::solution
- Remains true. We are not changing the `step` relation.
:::

- Progress

:::solution
        - Becomes false. For instance, `true true` is a term that
becomes typable (at type `Bool`), but which is stuck.
:::

- Preservation

:::solution
        - Remains true. There are 3 ways `t₁ t₂` can reduce. For
`Step.app1` and `Step.app2` we can still apply the induction
hypothesis. To reduce `t₁ t₂` using `Step.appAbs`
`t₁` would need to be a function, but functions don't have
type `Bool`.
:::
:::::

:::::exercise (rating := 2) (name := "stlc_variation7")
Suppose we add the following new rule to the typing relation
of the STLC:

```display
---------------------- (T_FunnyAbs)
⊢ \x:Bool,t ⦂ Bool
```

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

:::solution
- Remains true. We're not changing the `step` relation.
:::

- Progress

:::solution
```
        - Becomes false. For instance [if (\x:Bool,false) then false
else false] is a term that would become typable, although it
is stuck.
```
:::

- Preservation

:::solution
- Remains true. `λx:Bool. t` doesn't step.
:::
:::::

::::::

::::hide
```
Module StlcVar1.

Inductive has_type : context -> tm -> ty -> Prop :=
  | HasType.var : forall Γ x T₁,
      Γ x = Some T₁ ->
      <{ Γ ⊢ x ⦂ T₁ }>
  | HasType.abs : forall Γ x T₂ T₁ t₁,
      <{ x |-> T₂ ; Γ ⊢ t₁ ⦂ T₁ }> ->
      <{ Γ ⊢ \x:T₂, t₁ ⦂ T₂ -> T₁ }>
  | HasType.app : forall T₁ T₂ Γ t₁ t₂,
      <{ Γ ⊢ t₁ ⦂ T₂ -> T₁ }> ->
      <{ Γ ⊢ t₂ ⦂ T₂ }> ->
      <{ Γ ⊢ t₁ t₂ ⦂ T₁ }>
  | HasType.tru : forall Γ,
      <{ Γ ⊢ true ⦂ Bool }>
  | HasType.fls : forall Γ,
      <{ Γ ⊢ false ⦂ Bool }>
  | HasType.ite : forall t₁ t₂ t₃ T₁ Γ,
      <{ Γ ⊢ t₁ ⦂ Bool }> ->
      <{ Γ ⊢ t₂ ⦂ T₁ }> ->
      <{ Γ ⊢ t₃ ⦂ T₁ }> ->
      <{ Γ ⊢ if t₁ then t₂ else t₃ ⦂ T₁ }>
  | T_Strange : forall x t₁,
      <{ empty ⊢ \x:Bool, t₁ ⦂ Bool }>

where "<{ Γ '⊢' t '⦂' T }>"  := (has_type Γ t T).

Hint Constructors has_type : core.

Theorem no_progress : exists t T,
     <{ empty ⊢ t ⦂ T }> /\
     ~value t /\ ~(exists t', t --> t').
Proof.
  exists <{if (\x:Bool, false) then false else false}>.
  exists <{{ Bool }}>. split; [| split].
  - (* has_type *) eauto.
  - (* ~value *) intro Hc. inversion Hc.
  - (* ~steps *) intro Hc. destruct Hc as [x Hx].
    inversion Hx. subst.
    inversion H3.
Qed.

End StlcVar1.
```
::::

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
  | arrow (T₁ T₂ : Ty)
  | nat
```

To terms, we add natural number constants, along with
successor, predecessor, multiplication, and zero-testing.

```lean
inductive Tm where
  | var (x : String)
  | app (t₁ t₂ : Tm)
  | abs (x : String) (T : Ty) (t : Tm)
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
  | `(<{ ~$T:term }>)    => pure T
  | `(<{ ($T:stlcTy) }>) => `(<{ $T:stlcTy }>)
  | `(<{ $x:ident }>) =>
      match x.getId.toString with
      | "Nat" => `(Ty.nat)
      | _ => `(($x : Ty))
  | `(<{ $T₁:stlcTy → $T₂:stlcTy }>)  => `(Ty.arrow <{ $T₁:stlcTy }> <{ $T₂:stlcTy }>)
  | `(<{ $T₁:stlcTy -> $T₂:stlcTy }>) => `(Ty.arrow <{ $T₁:stlcTy }> <{ $T₂:stlcTy }>)
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
  | `(<{ λ $x : $T . $t }>) => do
      `(Tm.abs $(← Stlc.varStr x) <{ $T:stlcTy }> <{ $t:stlcTm }>)
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
        let T ← withAppFn <| withAppArg delabTyInner
        let t ← withAppArg delabTmInner
        `(stlcTm| λ $x : $T . $t)
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

:::dev "Claude"
The Rocq source builds this grammar with custom entries, and a few pieces of
that have no Lean counterpart: the `<{{ x }}>` quotation for shifting into
type-parsing mode (Lean works out from context which of the two brackets is
meant), the `$( t )` escape into arbitrary Rocq `constr` notation (our `~e`
already does that, in both grammars), and the two coercions
`tm_var : string >-> tm` and `tm_const : nat >-> tm`, which let a bare string or
numeral stand for a term.  Here a bare identifier and a bare numeral are
productions of the term grammar itself, so no coercions are needed.
:::

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
  | <{ λ ~y : ~T . ~t₁ }> =>
      if x = y then t else <{ λ ~y : ~T . [~x := ~s] ~t₁ }>
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
variable (x y : String) (s t t₁ t₂ t₃ : Tm) (T : Ty) (n : Nat)
-- SOLUTION
@[simp] theorem subst_var_eq : <{ [~x := ~s] ~(Tm.var x) }> = s := by
  simp [subst]

@[simp] theorem subst_var_ne (h : x ≠ y) : <{ [~x := ~s] ~(Tm.var y) }> = .var y := by
  simp [subst, h]

@[simp] theorem subst_abs_eq : <{ [~x := ~s] (λ ~x : ~T . ~t) }> = <{ λ ~x : ~T . ~t }> := by
  simp [subst]

@[simp] theorem subst_abs_ne (h : x ≠ y) :
    <{ [~x := ~s] (λ ~y : ~T . ~t) }> = <{ λ ~y : ~T . [~x := ~s] ~t }> := by
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

Next, the values.  In the pure STLC, function abstractions were the only
values; now the numbers are values too.

```lean
inductive Tm.IsValue : Tm → Prop where
-- SOLUTION
  | abs (x : String) (T₂ : Ty) (t₁ : Tm) : Tm.IsValue <{ λ ~x : ~T₂ . ~t₁ }>
  | const (n : Nat) : Tm.IsValue (.const n)
-- END SOLUTION
```

Now the reduction relation.  The three rules for application are the STLC's;
the rest say how the arithmetic operators evaluate their arguments and what
they compute once those arguments are numbers.

```lean
section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
-- SOLUTION
  | appAbs (x : String) (T : Ty) (t v : Tm) (hv : v.IsValue) :
      <{ (λ ~x : ~T . ~t) ~v }> ⟶ <{ [~x := ~v] ~t }>
  | app1 (t₁ t₁' t₂ : Tm) (h : t₁ ⟶ t₁') :
      <{ ~t₁ ~t₂ }> ⟶ <{ ~t₁' ~t₂ }>
  | app2 (v₁ t₂ t₂' : Tm) (hv : v₁.IsValue) (h : t₂ ⟶ t₂') :
      <{ ~v₁ ~t₂ }> ⟶ <{ ~v₁ ~t₂' }>
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

An example:

```lean
-- AI
theorem Nat_step_example : ∃ t, <{ (λ x : Nat . λ y : Nat . x * y) 3 2 }> ⟶* t := by
  solution!
    refine ⟨<{ 6 }>, ?_⟩
    apply Multi.step (y := <{ (λ y : Nat . 3 * y) 2 }>)
    · exact .app1 _ _ _ (.appAbs "x" _ _ _ (.const 3))
    apply Multi.step (y := <{ 3 * 2 }>)
    · exact .appAbs "y" _ _ _ (.const 2)
    apply Multi.step (y := <{ 6 }>)
    · exact .multConst 3 2
    · rfl
```

:::autogradedHole StlcArith.Nat_step_example
:::

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
  | `(stlcCtx| $x:stlcVar ↦ $T:stlcTy ; $G:stlcCtx) => do
      `(PartialMap.update $(← ctxTerm G) $(← Stlc.varStr x) <{ $T:stlcTy }>)
  | _ => Macro.throwUnsupported

section StlcArith
set_option hygiene false in
local macro_rules (kind := Stlc.judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $T:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $T:stlcTy }>)
```
::::

The typing rules for variables, abstraction, and application are the STLC's.
The remaining four are the typing rules for arithmetic expressions.

```lean
inductive HasType : Context → Tm → Ty → Prop where
-- SOLUTION
  | var (Γ : Context) (x : String) (T₁ : Ty) (h : Γ[x] = some T₁) :
      <{ ~Γ ⊢ ~(Tm.var x) ⦂ ~T₁ }>
  | abs (Γ : Context) (x : String) (T₁ T₂ : Ty) (t₁ : Tm)
      (h : <{ ~x ↦ ~T₂ ; ~Γ ⊢ ~t₁ ⦂ ~T₁ }>) :
      <{ ~Γ ⊢ λ ~x : ~T₂ . ~t₁ ⦂ ~T₂ → ~T₁ }>
  | app (Γ : Context) (T₁ T₂ : Ty) (t₁ t₂ : Tm)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ ~T₂ → ~T₁ }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~T₂ }>) :
      <{ ~Γ ⊢ ~t₁ ~t₂ ⦂ ~T₁ }>
  | const (Γ : Context) (n : Nat) :
      <{ ~Γ ⊢ ~(Tm.const n) ⦂ Nat }>
  | succ (Γ : Context) (t₁ : Tm) (h : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) :
      <{ ~Γ ⊢ succ ~t₁ ⦂ Nat }>
  | pred (Γ : Context) (t₁ : Tm) (h : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) :
      <{ ~Γ ⊢ pred ~t₁ ⦂ Nat }>
  | mult (Γ : Context) (t₁ t₂ : Tm)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ Nat }>) :
      <{ ~Γ ⊢ ~t₁ * ~t₂ ⦂ Nat }>
  | ite0 (Γ : Context) (t₁ t₂ t₃ : Tm) (T₀ : Ty)
      (h₁ : <{ ~Γ ⊢ ~t₁ ⦂ Nat }>) (h₂ : <{ ~Γ ⊢ ~t₂ ⦂ ~T₀ }>)
      (h₃ : <{ ~Γ ⊢ ~t₃ ⦂ ~T₀ }>) :
      <{ ~Γ ⊢ if0 ~t₁ then ~t₂ else ~t₃ ⦂ ~T₀ }>
-- END SOLUTION
```

::::details "Notation encoding: the judgment, for real"
Closing the section retires the hygiene-free rule; the same rule is then
declared again, hygienically, for every later use, and a pair of unexpanders
prints judgments back in their own notation.

```lean
end StlcArith

scoped macro_rules (kind := Stlc.judgeBracket)
  | `(<{ $G:stlcCtx ⊢ $t:stlcTm ⦂ $T:stlcTy }>) => do
      `(HasType $(← ctxTerm G) <{ $t:stlcTm }> <{ $T:stlcTy }>)

open Lean PrettyPrinter in
/-- Rebuild `stlcCtx` syntax from the term syntax of a `Context`, so that a
context prints as `x ↦ Nat ; Γ` rather than as a chain of map updates. -/
partial def unexpandCtx : Term → UnexpandM (TSyntax `stlcCtx)
  | `(∅) => `(stlcCtx| ∅)
  | `($x:str →ₚ $T) => do
      unexpandCtx (← `($x →ₚ $T ; ∅))
  | `($x:str →ₚ $T ; $G) => do
      let G' ← unexpandCtx G
      let x' : TSyntax `stlcVar ←
        if Stlc.isPlainName x.getString then
          `(stlcVar| $(mkIdent (Name.mkSimple x.getString)):ident)
        else `(stlcVar| ~$x)
      match T with
      | `(<{ $T':stlcTy }>) => `(stlcCtx| $x':stlcVar ↦ $T' ; $G')
      | _                   => `(stlcCtx| $x':stlcVar ↦ ~($T) ; $G')
  | G => `(stlcCtx| ~($G))

open Lean PrettyPrinter in
@[app_unexpander StlcArith.HasType]
def HasType.unexpand : Unexpander
  | `($_ $G <{ $t:stlcTm }> <{ $T:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ $T }>)
  | `($_ $G <{ $t:stlcTm }> $T) =>
      do `(<{ $(← unexpandCtx G) ⊢ $t ⦂ ~($T) }>)
  | `($_ $G $t <{ $T:stlcTy }>) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ $T }>)
  | `($_ $G $t $T) =>
      do `(<{ $(← unexpandCtx G) ⊢ ~($t) ⦂ ~($T) }>)
  | _ => throw ()
```
::::

An example:

```lean
-- AI
theorem Nat_typing_example : <{ ∅ ⊢ (λ x : Nat . λ y : Nat . x * y) 3 2 ⦂ Nat }> :=
  solution!(
    .app _ _ Ty.nat _ _
      (.app _ _ Ty.nat _ _
        (.abs _ _ _ _ _ (.abs _ _ _ _ _ (.mult _ _ _ (.var _ "x" _ rfl) (.var _ "y" _ rfl))))
        (.const _ 3))
      (.const _ 2))
```

:::autogradedHole StlcArith.Nat_typing_example
:::

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
-- AI
theorem weakening (Γ Γ' : Context) (t : Tm) (T : Ty)
    (hi : Γ ⊆ Γ') (hT : <{ ~Γ ⊢ ~t ⦂ ~T }>) : <{ ~Γ' ⊢ ~t ⦂ ~T }> := by
  solution!
    induction hT generalizing Γ' with
    | var _ x _ h => exact .var _ x _ (hi h)
    | abs _ x _ _ _ _ ih => exact .abs _ x _ _ _ (ih _ (PartialMap.update_subset _ _ _ _ hi))
    | app _ _ _ _ _ _ _ ih₁ ih₂ => exact .app _ _ _ _ _ (ih₁ _ hi) (ih₂ _ hi)
    | const _ n => exact .const _ n
    | succ _ _ _ ih => exact .succ _ _ (ih _ hi)
    | pred _ _ _ ih => exact .pred _ _ (ih _ hi)
    | mult _ _ _ _ _ ih₁ ih₂ => exact .mult _ _ _ (ih₁ _ hi) (ih₂ _ hi)
    | ite0 _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ =>
      exact .ite0 _ _ _ _ _ (ih₁ _ hi) (ih₂ _ hi) (ih₃ _ hi)
```

:::autogradedHole StlcArith.weakening
:::

:::gradeTheorem "6" StlcArith.weakening
:::

The two helper lemmas that weakening is for are also proved just as they were
for the STLC.

```lean
-- AI
theorem weakening_empty (Γ : Context) (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) :
    <{ ~Γ ⊢ ~t ⦂ ~T }> :=
  solution!(
    weakening _ _ _ _
      (fun h => by rw [PartialMap.getElem_empty] at h; cases h) hT)
-- AI
theorem substitution_preserves_typing (Γ : Context) (x : String) (U : Ty)
    (t v : Tm) (T : Ty)
    (hT : <{ ~x ↦ ~U ; ~Γ ⊢ ~t ⦂ ~T }>) (hv : <{ ∅ ⊢ ~v ⦂ ~U }>) :
    <{ ~Γ ⊢ [~x := ~v] ~t ⦂ ~T }> := by
  solution!
    induction t generalizing Γ T with
    | var y =>
      cases hT with
      | var _ _ _ h =>
        by_cases hxy : x = y
        · subst hxy
          rw [PartialMap.update_eq] at h
          rw [subst_var_eq]
          have hUT : U = T := Option.some.inj h
          subst hUT
          exact weakening_empty _ _ _ hv
        · rw [PartialMap.update_neq hxy] at h
          rw [subst_var_ne _ _ _ hxy]
          exact .var _ y _ h
    | app t₁ t₂ ih₁ ih₂ =>
      cases hT with
      | app _ _ _ _ _ h₁ h₂ =>
        rw [subst_app]; exact .app _ _ _ _ _ (ih₁ _ _ h₁) (ih₂ _ _ h₂)
    | abs y S t₁ ih =>
      cases hT with
      | abs _ _ _ _ _ h =>
        by_cases hxy : x = y
        · subst hxy
          rw [subst_abs_eq]
          rw [PartialMap.update_shadow] at h
          exact .abs _ _ _ _ _ h
        · rw [subst_abs_ne _ _ _ _ _ hxy]
          rw [PartialMap.update_permute (Ne.symm hxy)] at h
          exact .abs _ _ _ _ _ (ih _ _ h)
    | const n => cases hT with | const => rw [subst_const]; exact .const _ n
    | succ t₁ ih => cases hT with | succ _ _ h => rw [subst_succ]; exact .succ _ _ (ih _ _ h)
    | pred t₁ ih => cases hT with | pred _ _ h => rw [subst_pred]; exact .pred _ _ (ih _ _ h)
    | mult t₁ t₂ ih₁ ih₂ =>
      cases hT with
      | mult _ _ _ h₁ h₂ => rw [subst_mult]; exact .mult _ _ _ (ih₁ _ _ h₁) (ih₂ _ _ h₂)
    | ite0 t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
      cases hT with
      | ite0 _ _ _ _ _ h₁ h₂ h₃ =>
        rw [subst_ite0]
        exact .ite0 _ _ _ _ _ (ih₁ _ _ h₁) (ih₂ _ _ h₂) (ih₃ _ _ h₃)
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
theorem preservation (t t' : Tm) (T : Ty)
-- AI
    (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) (hs : t ⟶ t') : <{ ∅ ⊢ ~t' ⦂ ~T }> := by
  solution!
    generalize hΓ : (∅ : Context) = Γ at hT
    induction hT generalizing t' with
    | var => cases hs
    | abs => cases hs
    | const => cases hs
    | app Γ T₁ T₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      subst hΓ
      cases hs with
      | appAbs _ _ _ _ _ =>
        -- The one interesting case: the desired result is the substitution lemma.
        cases h₁ with
        | abs _ _ _ _ _ hb => exact substitution_preserves_typing _ _ _ _ _ _ hb h₂
      | app1 _ t₁' _ h => exact .app _ _ _ _ _ (ih₁ t₁' h rfl) h₂
      | app2 _ _ t₂' _ h => exact .app _ _ _ _ _ h₁ (ih₂ t₂' h rfl)
    | succ Γ t₁ h ih =>
      subst hΓ
      cases hs with
      | succ _ t₁' hst => exact .succ _ _ (ih t₁' hst rfl)
      | succConst n => exact .const _ _
    | pred Γ t₁ h ih =>
      subst hΓ
      cases hs with
      | pred _ t₁' hst => exact .pred _ _ (ih t₁' hst rfl)
      | predConst n => exact .const _ _
    | mult Γ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      subst hΓ
      cases hs with
      | multConst _ _ => exact .const _ _
      | mult1 _ t₁' _ hst => exact .mult _ _ _ (ih₁ t₁' hst rfl) h₂
      | mult2 _ _ t₂' _ hst => exact .mult _ _ _ h₁ (ih₂ t₂' hst rfl)
    | ite0 Γ t₁ t₂ t₃ T₀ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
      subst hΓ
      cases hs with
      | if0Step _ t₁' _ _ hst => exact .ite0 _ _ _ _ _ (ih₁ t₁' hst rfl) h₂ h₃
      | if0Zero => exact h₂
      | if0Nonzero => exact h₃
```
:::autogradedHole StlcArith.preservation
:::

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
-- AI
theorem progress (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  solution!
    generalize hΓ : (∅ : Context) = Γ at hT
    induction hT with
    | var Γ x T₁ h =>
      subst hΓ
      -- Contradictory: variables cannot be typed in an empty context.
      rw [PartialMap.getElem_empty] at h
      cases h
    | abs => exact .inl (.abs ..)
    | const _ n => exact .inl (.const n)
    | app Γ T₁ T₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      right
      subst hΓ
      cases ih₁ rfl with
      | inl hv₁ =>
        cases ih₂ rfl with
        | inl hv₂ =>
          -- `t₁` is a value of arrow type, so it is an abstraction, not a number.
          cases hv₁ with
          | abs x T u => exact ⟨<{ [~x := ~t₂] ~u }>, .appAbs x T u t₂ hv₂⟩
          | const n => cases h₁
        | inr hs₂ =>
          obtain ⟨t₂', h⟩ := hs₂; exact ⟨<{ ~t₁ ~t₂' }>, .app2 t₁ t₂ t₂' hv₁ h⟩
      | inr hs₁ =>
        obtain ⟨t₁', h⟩ := hs₁; exact ⟨<{ ~t₁' ~t₂ }>, .app1 t₁ t₁' t₂ h⟩
    | succ Γ t₁ h ih =>
      right
      subst hΓ
      cases ih rfl with
      | inl hv =>
        cases hv with
        | abs => cases h
        | const n => exact ⟨.const (1 + n), .succConst n⟩
      | inr hs => obtain ⟨t₁', hst⟩ := hs; exact ⟨<{ succ ~t₁' }>, .succ t₁ t₁' hst⟩
    | pred Γ t₁ h ih =>
      right
      subst hΓ
      cases ih rfl with
      | inl hv =>
        cases hv with
        | abs => cases h
        | const n => exact ⟨.const (n - 1), .predConst n⟩
      | inr hs => obtain ⟨t₁', hst⟩ := hs; exact ⟨<{ pred ~t₁' }>, .pred t₁ t₁' hst⟩
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
            | const n₂ => exact ⟨.const (n₁ * n₂), .multConst n₁ n₂⟩
        | inr hs₂ =>
          obtain ⟨t₂', hst⟩ := hs₂
          exact ⟨<{ ~t₁ * ~t₂' }>, .mult2 t₁ t₂ t₂' hv₁ hst⟩
      | inr hs₁ =>
        obtain ⟨t₁', hst⟩ := hs₁; exact ⟨<{ ~t₁' * ~t₂ }>, .mult1 t₁ t₁' t₂ hst⟩
    | ite0 Γ t₁ t₂ t₃ T₀ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
      right
      subst hΓ
      cases ih₁ rfl with
      | inl hv₁ =>
        cases hv₁ with
        | abs => cases h₁
        | const n =>
          cases n with
          | zero => exact ⟨t₂, .if0Zero t₂ t₃⟩
          | succ n' => exact ⟨t₃, .if0Nonzero n' t₂ t₃⟩
      | inr hs₁ =>
        obtain ⟨t₁', hst⟩ := hs₁
        exact ⟨<{ if0 ~t₁' then ~t₂ else ~t₃ }>, .if0Step t₁ t₁' t₂ t₃ hst⟩
```
:::autogradedHole StlcArith.progress
:::

:::gradeTheorem "6" StlcArith.progress
:::
:::::

::::::

```lean
end StlcArith
```

:::dev "Claude"
The source's grading file weights this exercise at 28 points — 10 for
`STLCArith.subst` and 6 each for `weakening`, `preservation`, and `progress`.
The three theorems carry those weights directly; the 10 points for the
definitions are split between the two examples that exercise them,
`Nat_step_example` and `Nat_typing_example`, since a definition has no
autogradable statement of its own.  Names are qualified (`StlcArith.progress`)
so the grader can tell them apart from this chapter's own `progress` and
`preservation`.
:::

:::dev PotentialImprovement
```
(a) Is there a type T that makes
x:T ⊢ if0 ((\x:nat, pred x) x,fst) then x.snd else (x.fst, x.fst) : (nat * nat)
provable? If so, what is it?
Answer: Yes: T = nat * (nat * nat).
(b) Are there types S and T that make
empty ⊢ \x:T, \y:T, x y : S
provable? If so, what are they?
Answer: No; it would have to be the case that T = T -> S, but there can be no such (
nite) type
T.

-----------------------

(a) Suppose we add a term foo with the following evaluation rules:
(\x:A, x) --> foo (ST_Foo1)
foo --> 0 (ST_Foo2)
Do progress and preservation continue to hold after this change, or does one (or do both) fail?
Why?
Answer: Preservation fails, since we have no typing rules for foo but \x:A, x has type A!A.
Progress still holds: we are only adding to the step relation, and this can never damage progress.
(b) Suppose we add a term zap, with the following evaluation rule
t --> zap (ST_Zap)
and the following typing rule:
Γ ⊢ zap : T (T_Zap)
Do progress and preservation continue to hold after this change, or does one (or do both) fail?
Why?
Answer: Both properties continue to hold. Progress holds trivially: every term can take a step to
zap! Preservation holds because zap can have any type.
(c) Suppose we change Step.appAbs to the following rule:
(\x:T, t₁2) t₂ --> [x:=t₂]t₁2 (Step.appAbs')
Do progress and preservation continue to hold after this change, or does one (or do both) fail?
Why?
Answer: Both properties continue to hold. (Substitution preserves typing irrespective of whether
the term being substituted into another term is a value or not.)
```
:::
