import Mathlib.Algebra.BigOperators.Basic

open Function
open scoped BigOperators

namespace Finset

@[to_additive]
lemma prod_eq_of_injOn {α β R : Type*} [CommMonoid R] {s : Finset α} {t : Finset β}
    (e : α → β) {f : α → R} {g : β → R} (he : Set.InjOn e s) (h'e : Set.MapsTo e s t)
    (h : ∀ i ∈ s, f i = g (e i)) (h' : ∀ i ∈ t, i ∉ e '' s → g i = 1) :
    ∏ i in s, f i = ∏ j in t, g j := by
  classical
  exact (prod_nbij e (fun a ↦ mem_image_of_mem e) he (by simp [Set.surjOn_image]) h).trans $
    prod_subset (image_subset_iff.2 h'e) $ by simpa using h'

@[to_additive]
lemma prod_eq_of_injective {α β R : Type*} [CommMonoid R] [Fintype α] [Fintype β]
    (e : α → β) (hf : Injective e) {f : α → R} {g : β → R} (h : ∀ i, f i = g (e i))
    (h' : ∀ i ∉ Set.range e, g i = 1) : ∏ i, f i = ∏ j, g j :=
  prod_eq_of_injOn e (hf.injOn _) (by simp) (fun i _ ↦ h i) (by simpa using h')
