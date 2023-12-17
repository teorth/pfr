import Mathlib.SetTheory.Cardinal.Finite
import PFR.Mathlib.Data.Set.Finite

open Function Set

variable {α β : Type*} {f : α → β} {s : Set α}

namespace Nat

lemma card_eq_finset_card {s : Finset α} : Nat.card s = s.card := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

lemma card_eq_toFinset_card (hs : s.Finite) : Nat.card s = hs.toFinset.card := by
  simp only [←Nat.card_eq_finset_card, Finite.mem_toFinset]

lemma card_image_le (hs : s.Finite) : Nat.card (f '' s) ≤ Nat.card s :=
  have := hs.to_subtype; card_le_card_of_surjective (imageFactorization f s) surjective_onto_image

lemma card_image_of_injOn (hf : s.InjOn f) : Nat.card (f '' s) = Nat.card s := by
  classical
  obtain hs | hs := s.finite_or_infinite
  · have := hs.fintype
    have := fintypeImage s f
    simp_rw [Nat.card_eq_fintype_card, Set.card_image_of_inj_on hf]
  · have := hs.to_subtype
    have := (hs.image hf).to_subtype
    simp [Nat.card_eq_zero_of_infinite]

lemma card_image_of_injective (hf : Injective f) (s : Set α) :
    Nat.card (f '' s) = Nat.card s := card_image_of_injOn $ hf.injOn _

lemma card_image_equiv (e : α ≃ β) : Nat.card (e '' s) = Nat.card s :=
    Nat.card_congr (e.image s).symm

lemma card_preimage_of_injOn {s : Set β} (hf : (f ⁻¹' s).InjOn f) (hsf : s ⊆ range f) :
    Nat.card (f ⁻¹' s) = Nat.card s := by
  rw [← Nat.card_image_of_injOn hf, image_preimage_eq_iff.2 hsf]

lemma card_preimage_of_injective {s : Set β} (hf : Injective f) (hsf : s ⊆ range f) :
    Nat.card (f ⁻¹' s) = Nat.card s := card_preimage_of_injOn (hf.injOn _) hsf

end Nat

namespace Set

lemma card_singleton_prod (a : α) (B : Set β) : Nat.card ({a} ×ˢ B) = Nat.card B := by
  rw [Set.singleton_prod, Nat.card_image_of_injective (Prod.mk.inj_left a)]

lemma card_prod_singleton (A : Set α) (b : β) :
    Nat.card (A ×ˢ {b}) = Nat.card A := by
  rw [Set.prod_singleton, Nat.card_image_of_injective (Prod.mk.inj_right b)]

end Set
