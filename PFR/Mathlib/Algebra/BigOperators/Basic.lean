import Mathlib.Algebra.BigOperators.Basic

open scoped BigOperators

open Function Set

@[to_additive]
lemma prod_eq_of_injOn {α β R : Type*} [CommMonoid R] [Fintype β] {s : Finset α} {t : Finset β}
    (e : α → β) (he : InjOn e s) (h'e : MapsTo e s t)
    {f : α → R} {g : β → R} (h : ∀ i ∈ s, f i = g (e i))
    (h' : ∀ i ∈ (t : Set β) \ e '' s, g i = 1) :
    ∏ i in s, f i = ∏ j in t, g j := by
  classical
  have A : ∏ j in s.image e, g j = ∏ j in t, g j := by
    apply (Finset.prod_subset (Finset.image_subset_iff.mpr h'e) _)
    intro x hx h'x
    exact h' _ ⟨hx, by simpa using h'x⟩
  have B : ∏ i in s, f i = ∏ j in s.image e, g j := by
    apply Finset.prod_bij (fun x _ ↦ e x) (fun a ha ↦ Finset.mem_image_of_mem e ha) h
      (fun a₁ a₂ ha₁ ha₂ a ↦ he ha₁ ha₂ a) (fun b hb ↦ by simpa [eq_comm] using hb)
  exact B.trans A

@[to_additive]
lemma prod_eq_of_injective {α β R : Type*} [CommMonoid R] [Fintype α] [Fintype β]
    (e : α → β) (hf : Injective e)
    {f : α → R} {g : β → R} (h : ∀ i, f i = g (e i))
    (h' : ∀ i ∉ range e, g i = 1) :
    ∏ i, f i = ∏ j, g j := by
  apply prod_eq_of_injOn e (injOn_of_injective hf _) (by simp) (fun i _hi ↦ h i)
    (fun i hi ↦ h' _ (by simpa using hi))
