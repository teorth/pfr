import Mathlib.Algebra.BigOperators.Basic

open scoped BigOperators

open Function Set

@[to_additive]
lemma prod_injOn {α β R : Type*} [CommMonoid R] [Fintype β] {s : Finset α} {t : Finset β}
    (e : α → β) (hf : InjOn e s) (h'' : MapsTo e s t)
    {f : α → R} {g : β → R} (h : ∀ i ∈ s, f i = g (e i))
    (h' : ∀ i ∈ (t : Set β) \ e '' s, g i = 1) :
    ∏ i in s, f i = ∏ j in t, g j := by
  classical
  let t' := s.image e
  have A : ∏ j in t', g j = ∏ j in t, g j := by
    apply (Finset.prod_subset (Finset.image_subset_iff.mpr h'') _)
    intro x hx h'x
    exact h' _ ⟨hx, by simpa using h'x⟩
  have B : ∏ i in s, f i = ∏ j in t', g j := by
    apply Finset.prod_bij (fun x _ ↦ e x) (fun a ha ↦ Finset.mem_image_of_mem e ha) h
      (fun a₁ a₂ ha₁ ha₂ a ↦ hf ha₁ ha₂ a) (fun b hb ↦ by simpa [eq_comm] using hb)
  exact B.trans A
