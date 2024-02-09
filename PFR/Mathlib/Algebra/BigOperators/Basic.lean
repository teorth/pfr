import Mathlib.Algebra.BigOperators.Basic
import PFR.Mathlib.Data.Finset.Basic

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

end Finset

namespace Finset
variable {ι κ α : Type*} [CommMonoid α]
open scoped BigOperators

-- TODO: Replace `Finset.prod_fiberwise`

@[to_additive]
lemma prod_prod_filter_eq [DecidableEq κ] (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : ι → α) :
    ∏ j in t, ∏ i in s.filter fun i ↦ g i = j, f i = ∏ i in s.filter fun i ↦ g i ∈ t, f i := by
  rw [← prod_disjiUnion, disjiUnion_filter_eq]

@[to_additive]
lemma prod_prod_filter_eq' [DecidableEq κ] (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : κ → α) :
    ∏ j in t, ∏ _i in s.filter fun i ↦ g i = j, f j = ∏ i in s.filter fun i ↦ g i ∈ t, f (g i) := by
  calc
    _ = ∏ j in t, ∏ i in s.filter fun i ↦ g i = j, f (g i) :=
        prod_congr rfl fun j _ ↦ prod_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2]
    _ = _ := prod_prod_filter_eq _ _ _ _

end Finset

namespace Finset
variable {ι κ α : Type*} [CommMonoid α] {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α}
open scoped BigOperators

lemma sum_card_filter_eq [DecidableEq κ] (s : Finset ι) (t : Finset κ) (g : ι → κ) :
    ∑ j in t, (s.filter fun i ↦ g i = j).card = (s.filter fun i ↦ g i ∈ t).card := by
  simpa only [card_eq_sum_ones] using sum_sum_filter_eq _ _ _ _

end Finset
