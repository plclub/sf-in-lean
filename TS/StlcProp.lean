import SFLMeta
import TS.Stlc

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
options -- a `set_option maxHeartbeats ... in` on the theorem was verified not
to help here, and neither does splitting the code block, since the budget is
per-declaration. `LF/IndPropRegexpVerso.lean` carries the same override and
documents the mechanism at length.

The way to remove this would be to break the substitution lemma's variable and
abstraction cases out as named helper lemmas, so each is highlighted against
its own fresh budget -- the pattern `IndPropRegexp` uses for `star_app_aux`.
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
                               value v
                       -----------------------                    (appAbs)
                        (λx:T. t) v ⟶ [x:=v]t

                              t₁ ⟶ t₁'
                          ----------------                        (app1)
                           t₁ t₂ ⟶ t₁' t₂

                              value v₁
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

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2021)
The `stlc_arith` exercise needs cleaning up -- instead of asking people to copy
stuff over, we should give the headers of all the definitions and just ask
them to complete them.
:::

:::dev "Benjamin Pierce (bcpierce00)" BeforeNextRelease (year := 2022)
In Wadler's "PLF in Agda", he defines an "animator" for STLC terms using the
proof terms for progress + preservation.  This would be a FANTASTIC example
(or, perhaps better, exercise!) for this chapter.
:::

In this chapter, we develop the fundamental theory of the Simply
Typed Lambda Calculus -- in particular, the type safety
theorem.

We pick up where the {ref "Stlc"}[Stlc] chapter left off, so everything below
lives in the same namespace as the definitions it is about.

```lean
namespace Stlc
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
only well typed but _closed_ -- i.e., well typed in the empty
context.

```lean
theorem canonical_forms_bool (t : Tm) (hT : <{ ∅ ⊢ ~t ⦂ Bool }>) (hv : t.IsValue) :
    t = <{ true }> ∨ t = <{ false }> := by
  cases hv with
  | abs x T t₁ => cases hT
  | tru => exact .inl rfl
  | fls => exact .inr rfl

theorem canonical_forms_fun (t : Tm) (T₁ T₂ : Ty)
    (hT : <{ ∅ ⊢ ~t ⦂ ~T₁ → ~T₂ }>) (hv : t.IsValue) :
    ∃ x u, t = <{ λ ~x : ~T₁ . ~u }> := by
  cases hv with
  | abs x T t₁ => cases hT with | abs _ _ _ _ _ _ => exact ⟨x, t₁, rfl⟩
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
    rw [PartialMap.apply_empty] at h
    cases h
  | abs => exact .inl (.abs ..)
  | tru => exact .inl .tru
  | fls => exact .inl .fls
  | app Γ T₁ T₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    -- `t = t₁ t₂`.  Proceed by cases on whether `t₁` is a value or steps.
    right
    cases ih₁ hΓ with
    | inl hv₁ =>
      cases ih₂ hΓ with
      | inl hv₂ =>
        obtain ⟨x, u, rfl⟩ := canonical_forms_fun t₁ _ _ (hΓ ▸ h₁) hv₁
        exact ⟨<{ [~x := ~t₂] ~u }>, .appAbs x T₂ u t₂ hv₂⟩
      | inr hs₂ => obtain ⟨t₂', h⟩ := hs₂; exact ⟨<{ ~t₁ ~t₂' }>, .app2 t₁ t₂ t₂' hv₁ h⟩
    | inr hs₁ => obtain ⟨t₁', h⟩ := hs₁; exact ⟨<{ ~t₁' ~t₂ }>, .app1 t₁ t₁' t₂ h⟩
  | ite Γ t₁ t₂ t₃ T₁ h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    right
    cases ih₁ hΓ with
    | inl hv₁ =>
      cases canonical_forms_bool t₁ (hΓ ▸ h₁) hv₁ with
      | inl he => subst he; exact ⟨t₂, .ifTrue t₂ t₃⟩
      | inr he => subst he; exact ⟨t₃, .ifFalse t₂ t₃⟩
    | inr hs₁ =>
      obtain ⟨t₁', h⟩ := hs₁
      exact ⟨<{ if ~t₁' then ~t₂ else ~t₃ }>, .ifStep t₁ t₁' t₂ t₃ h⟩
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
:::gradeTheorem 3 "progress'"
:::

Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

```lean
theorem progress' (t : Tm) (T : Ty) (hT : <{ ∅ ⊢ ~t ⦂ ~T }>) :
    t.IsValue ∨ ∃ t', t ⟶ t' := by
  solution!
    induction t generalizing T with
    | var x =>
      cases hT with
      | var _ _ _ h => rw [PartialMap.apply_empty] at h; cases h
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
    the definition of substitition.  This time, for the variables
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
substitition.

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
theorem weakening (Γ Γ' : Context) (t : Tm) (T : Ty)
    (hi : Γ ⊆ Γ') (hT : <{ ~Γ ⊢ ~t ⦂ ~T }>) : <{ ~Γ' ⊢ ~t ⦂ ~T }> := by
  induction hT generalizing Γ' with
  | var _ x _ h => exact .var _ x _ (hi x _ h)
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
    (fun x T h => by rw [PartialMap.apply_empty] at h; cases h) hT
```

## The Substitution Lemma

Now we come to the conceptual heart of the proof that reduction
preserves types -- namely, the observation that _substitution_
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
      · rw [PartialMap.update_neq _ _ _ hxy] at h
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
        rw [PartialMap.update_permute _ _ _ _ _ (Ne.symm hxy)] at h
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
we assume `v` has type `U` in the _empty_ context -- in other
words, we assume `v` is closed.  (Since we are using a simple
definition of substition that is not capture-avoiding, it doesn't
make sense to substitute non-closed terms into other terms.
Fortunately, closed terms are all we need!)
::::

::::::full
:::::exercise (rating := 3) (name := "substitution_preserves_typing_from_typing_ind") (level := Advanced)
:::gradeTheorem 3 "substitution_preserves_typing_from_typing_ind"
:::

Show that substitution_preserves_typing can also be
proved by induction on typing derivations instead
of induction on terms.

```lean
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
      · rw [PartialMap.update_neq _ _ _ hxy] at h
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
        exact .abs _ _ _ _ _ (ih _ (PartialMap.update_permute _ _ _ _ _ hxy))
    | app _ _ _ _ _ _ _ ih₁ ih₂ =>
      rw [subst_app]; exact .app _ _ _ _ _ (ih₁ _ hΓ) (ih₂ _ hΓ)
    | tru => rw [subst_tru]; exact .tru _
    | fls => rw [subst_fls]; exact .fls _
    | ite _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ =>
      rw [subst_ite]; exact .ite _ _ _ _ _ (ih₁ _ hΓ) (ih₂ _ hΓ) (ih₃ _ hΓ)
```
:::::

::::::

## Main Theorem

We now have the ingredients we need to prove preservation: if a
closed, well-typed term `t` has type `T` and takes a step to `t'`,
then `t'` is also a closed term with type `T`.  In other words,
the small-step reduction relation preserves types.

```lean
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
COMMENT: `untagged (* .. *) comment at prose position in the Rocq source -- probably an error there; decide whether it is book prose or an author note`
For example,
`((\a:Bool→Bool, λy:Bool. y) true)` is ill typed, but it evaluates
to the well-typed term `λy:Bool. y`,
:::

```lean
theorem not_subject_expansion :
    ∃ (t t' : Tm) (T : Ty), t ⟶ t' ∧ <{ ∅ ⊢ ~t' ⦂ ~T }> ∧ ¬ <{ ∅ ⊢ ~t ⦂ ~T }> := by
  solution!
    refine ⟨<{ (λ x : Bool → Bool . λ y : Bool . y) true }>, <{ λ y : Bool . y }>,
            <{ Bool → Bool }>, ?_, ?_, ?_⟩
    · exact .appAbs "x" _ _ _ .tru
    · exact .abs _ _ _ _ _ (.var _ "y" _ rfl)
    · intro hc
      cases hc with
      | app _ _ _ _ _ hf ha => cases ha with | tru => cases hf
```

::::hide
```
/- Alternative formulation. -/
Theorem not_subject_expansion_alt:
  ~ (forall t t' T, t --> t' /\ <{ empty ⊢ t' ⦂ T }> -> <{ empty ⊢ t ⦂ T }>).
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
"inessential changes" to the context `Γ` -- in particular,
changes that do not affect any of the free variables of the
term. In this section, we establish this property for our system,
introducing some other standard terminology on the way.

First, we need to define the _free variables_ in a term -- i.e.,
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
free in it.  This gives us another way to define _closed_ terms --
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
conventions you like -- the point of the exercise is just for you
to think a bit about the meaning of each rule.)  Although this is
a rather low-level, technical definition, understanding it is
crucial to understanding substitution and its properties, which
are really the crux of the lambda-calculus.

:::solution
COMMENT: `untagged (* .. *) comment at prose position in the Rocq source -- probably an error there; decide whether it is book prose or an author note`
(no solution yet) -/
/- LATER: Fill in an official solution
:::

:::grade
`GRADE_MANUAL 1: afi`
:::
:::::

Next, we show that if a variable `x` appears free in a term `t`,
and if we know `t` is well typed in context `Γ`, then it
must be the case that `Γ` assigns a type to `x`.

```lean
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
        rw [PartialMap.update_neq _ _ _ hne] at h
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
    rw [PartialMap.apply_empty] at hc
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
      · rw [PartialMap.update_neq _ _ _ hyz, PartialMap.update_neq _ _ _ hyz]
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

:::dev
HIDE: BCP 20: Maybe this deserves an exercise?  BCP 21: Nah. People
can just try it if they really want.
:::
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
COMMENT: `untagged (* .. *) comment at prose position in the Rocq source -- probably an error there; decide whether it is book prose or an author note`
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

:::dev "Claude" NOW
**This extended exercise is not yet ported.**  In the Rocq source it extends the
STLC with a base type of natural numbers (dropping booleans) and constants,
`succ`, `pred`, `*`, and `if0`, then asks the reader to supply `subst`, `value`,
`step`, `has_type`, and to redo `weakening`, `preservation`, and `progress` for
the extended language.  It is worth 28 of the chapter's ~47 graded points
(`STLCArith.subst` 10, `STLCArith.weakening` 6, `STLCArith.preservation` 6,
`STLCArith.progress` 6), so it cannot stay dropped.

Porting it means a second syntax-category family alongside `stlcTy`/`stlcTm`,
since `STLCArith` is a *different* language rather than an extension of this
one.  That is a chunk of notation plumbing on the scale of the encoding section
of the `Stlc` chapter, which is why it is a separate pass.

Before doing that pass, get the improved version of the exercise: the Rocq
source notes that commit `c54534533ff94cc5869e768b78d126deab91214c` of the SF
repository has a better one, and BCP'21 records the intent -- give students the
headers of all the definitions and ask them to complete them, rather than asking
them to copy material over.
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
