/- Maps: Total and Partial Maps -/

import LF.CustomTactics

/- CH: This is just the code with the prose left out, but I've left comments mentioning
  various issues and my thought processes

  BCP: My understanding from the meeting on 6/25 is that this chapter will be folded into
  Typeclasses as an example.
-/

/-
  CH: First a general comment that I found even this simple file very annoying to write
  without a minimal Mathlib/batteries dependency. I want to clarify again that I completely understand
  hiding most of this, but there are some simple syntax extentions that are ubiqutous in the ecosystem
  that I think omitting is distracting. Some examples:

  - `#check` only has its command syntax. With Mathlib imported it allows doing this within a proof,
    which I think can be very nice and prevent confusing errors

  - there are places where I was explicit about universes because the `Type*` syntax for
    fresh universes is missing. I'd much rather write `α β : Type*` versus ever needing to write
    `universe u v`

  - some basic code actions are missing
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

/- CH: Daniel suggested this being a good place to introduce some simple typeclasses.
  Given all the discussion about `if` versus `bif`, I concluded that it is simplest to
  present this using booleans, essentially because they have simpler typeclasses and
  the student will have maybe a less confusing time without needing to use simprocs

  These are the equivalents of the string theorems mentioned, though I naturally used a few others
  while writing proofs that we might want to present too
-/

#check ReflBEq.rfl
#check beq_iff_eq
#check beq_eq_false_iff_ne

/- CH: I made a slight design departure by using `Inhabited`, so that each type has a global
  default as opposed to passing this around. I find it idiomatic, but feel free to rework as this
  is not crucial.
-/
variable {α : Type u} {β : Type v} [BEq α] [ReflBEq α] [LawfulBEq α] [Inhabited β]

def TotalMap (α : Type u) (β : Type v) := α → β

/-
  CH: The biggest thing that I think is essential to depart from SF on is this line:
    "Note that we don't need to define a find operation on this representation of maps because
    it is just function application!"

  In idiomatic Lean it is considered "definitional equality abuse" (often shortened to "defeq abuse") to
  look through the definition of a type like `TotalMap` in this way. It's become more common in
  recent years to actually make types like this a one-field structure to strongly enforce this, but
  I thought that would be confusing here.

  What I do is make a `GetElem` instance, which is how the `m[a]` notation is managed for containers
  in Lean. Once we define some basic theorems we should never have to unfold this. This may
  seem a bit silly for such a simple example, but I think it is valuble to teach this sort of design
  from the beginning.
-/

instance : GetElem (TotalMap α β) α β (fun _ _ => True) where
  getElem m a _ := m a

-- CH: for the `∅` notation, relying on `[Inhabited β]`
instance : EmptyCollection (TotalMap α β) where
  emptyCollection _ := default

namespace TotalMap

-- CH: These are the sort of "API" lemmas that we always define to accompany a notation
theorem getElem_def (m : TotalMap α β) (a : α) : m[a] = m a :=
  rfl

def update (m : TotalMap α β) (a : α) (b : β) : TotalMap α β :=
  fun a' => bif a == a' then b else m[a']

-- CH: Note the `|>.` syntax. This is a pipe that then uses dot notation to access the namespace
-- of the preceding type

def example_map :=
  (∅ : TotalMap String Bool)
    |>.update "foo" true
    |>.update "bar" true

notation a " →ₜ " b " ; " m => TotalMap.update m a b

example : example_map = "bar" →ₜ true; "foo" →ₜ true ; ∅ := rfl

example : example_map["baz"] = false := rfl

example : example_map["foo"] = true := rfl

example : example_map["quux"] = false := rfl

example : example_map["bar"] = true := rfl

theorem apply_empty (a : α) : (∅ : TotalMap α β)[a] = default := rfl

/-
  CH: Note that I am using `rewrite` here. The difference is that the more common `rw` is
  essentially `rewrite [...]; rfl`, which I think is confusing for teaching. Some existing
  learning materials redefine `rw` so you can use the short and familiar name without this problem.
-/

theorem update_eq (m : TotalMap α β) (a : α) (b : β) : (a →ₜ b; m)[a] = b := by
  unfold update
  rewrite [getElem_def, ReflBEq.rfl, cond_true]
  rfl

theorem update_neq (m : TotalMap α β) (a₁ a₂ : α) (h : a₁ ≠ a₂) (b : β) :
    (a₁ →ₜ b; m)[a₂] = m[a₂] := by
  by_cases h' : a₁ = a₂
  · contradiction
  · unfold update
    rewrite [getElem_def, beq_false_of_ne h, cond_false]
    rfl

-- CH: presumably `ext` will have been explained before this when introducing `funext`

@[ext]
theorem ext (m₁ m₂ : TotalMap α β) (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := funext h

theorem update_shadow (m : TotalMap α β) (a : α) (b₁ b₂ : β) :
    (a →ₜ b₂; a →ₜ b₁; m) = (a →ₜ b₂ ; m) := by
  ext a'
  by_cases h : a = a'
  · subst h
    rewrite [update_eq, update_eq]
    rfl
  · rewrite [update_neq _ _ _ h, update_neq _ _ _ h, update_neq _ _ _ h]
    rfl

theorem update_same (m : TotalMap α β) (a : α) : (a →ₜ m[a]; m) = m := by
  ext a'
  by_cases h : a = a'
  · subst h
    rw [update_eq]
  · rw [update_neq _ _ _ h]

theorem update_permute (m : TotalMap α β) (a₁ a₂ : α) (b₁ b₂ : β) (h : a₁ ≠ a₂) :
    (a₁ →ₜ b₁; a₂ →ₜ b₂; m) = (a₂ →ₜ b₂; a₁ →ₜ b₁; m) := by
  ext a'
  by_cases h₁ : a₁ = a'
  · subst h₁
    rw [update_eq, update_neq _ _ _ h.symm, update_eq]
  · rw [update_neq _ _ _ h₁]
    by_cases h₂ : a₂ = a'
    · subst h₂
      rw [update_eq, update_eq]
    · rw [update_neq _ _ _ h₂, update_neq _ _ _ h₂, update_neq _ _ _ h₁]

end TotalMap

/-
  CH: This being a `abbrev` is a design decision of not having to duplicate all the typeclasses, but
  if this is confusing for any reason, feel free to change.
-/

abbrev PartialMap (α : Type u) (β : Type v) := TotalMap α (Option β)

-- CH: This instance might be confusing at this point.  Removed for the
-- PartialMap development and restored at `end PartialMap` below: a module-scope
-- removal that leaks to end-of-file breaks the Verso build's `tag`/`file`
-- (Tag → Option Tag) metadata coercion, which is forced at end-of-document.
-- (The erase form `[-instance]` can't be scoped `local`, hence the manual pair.)
attribute [-instance] optionCoe

namespace PartialMap

def update (m : PartialMap α β) (a : α) (b : β) : PartialMap α β := (a →ₜ some b; m)

notation a " →ₚ " b " ; " m => PartialMap.update m a b

/- CH: Again, more "API lemmas". The cannonical way to switch between the different
  maps should be this theorem relating their notations. -/
theorem totalMap_eq {m} (a : α) (b : β) : (a →ₚ b ; m) = (a →ₜ some b ; m) := rfl

@[ext]
theorem ext (m₁ m₂ : PartialMap α β) (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := funext h

theorem apply_empty (a : α) : (∅ : PartialMap α β)[a] = none := rfl

theorem update_eq (m : PartialMap α β) (a : α) (b : β) : (a →ₚ b; m)[a] = some b := by
  rw [totalMap_eq, TotalMap.update_eq]

-- CH: `auto` mentioned here, what do we want??

theorem update_neq (m : PartialMap α β) (a₁ a₂ : α) (h : a₁ ≠ a₂) (b : β) :
    (a₁ →ₚ b; m)[a₂] = m[a₂] := by
  rw [totalMap_eq, TotalMap.update_neq _ _ _  h]

theorem update_shadow (m : PartialMap α β) (a : α) (b₁ b₂ : β) :
    (a →ₚ b₂; a →ₚ b₁; m) = (a →ₚ b₂ ; m) := by
  simp [totalMap_eq]
  exact TotalMap.update_shadow m a (some b₁) (some b₂)

theorem update_same (m : PartialMap α β) (a : α) (b : β) (h : m[a] = some b) :
    (a →ₚ b; m) = m := by
  rw [totalMap_eq, ← h, TotalMap.update_same]

theorem update_permute (m : PartialMap α β) (a₁ a₂ : α) (b₁ b₂ : β) (h : a₁ ≠ a₂) :
    (a₁ →ₚ b₁; a₂ →ₚ b₂; m) = (a₂ →ₚ b₂; a₁ →ₚ b₁; m) := by
  simp only [totalMap_eq]
  exact TotalMap.update_permute m a₁ a₂ (some b₁) (some b₂) h

def Subset (m₁ m₂ : PartialMap α β) : Prop :=
  ∀ (a : α) (b : β), m₁[a] = some b → m₂[a] = some b

instance : HasSubset (PartialMap α β) where
  Subset := PartialMap.Subset

def subset_def (m₁ m₂ : PartialMap α β) :
    m₁ ⊆ m₂ ↔ (∀ (a : α) (b : β), m₁[a] = some b → m₂[a] = some b) := .rfl

theorem update_subset (m₁ m₂ : PartialMap α β) (a : α) (b : β) (h : m₁ ⊆ m₂) :
    (a →ₚ b; m₁) ⊆ (a →ₚ b; m₂) := by
  rw [subset_def]
  intro a' b' eq
  rw [← eq]
  by_cases eq : a = a'
  · subst eq
    simp [update_eq]
  · simp only [update_neq _ _ _ eq] at *
    rw [h a' b' eq]
    symm
    assumption

end PartialMap

-- BCP: The following was added by Claude to repair a build error in
-- the next chapter, but I'm not sure it's the best fix.  An expert
-- should take a look.

-- Restore the `Option` coercion removed above (see the `attribute [-instance]`
-- note), so it is in effect at end-of-document for Verso's metadata coercion.
attribute [instance] optionCoe
