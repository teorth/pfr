import Mathlib.Data.Set.Finite
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card

open Function Set

lemma Set.nat_card_image_of_injective {α β : Type*} {s : Set α} {f : α → β}
    (H : Injective f) (hs : s.Finite) : Nat.card (f '' s) = Nat.card s := by
  classical
  have := hs.fintype
  have := fintypeImage s f
  convert card_image_of_injective s H
  exact Nat.card_eq_fintype_card
  exact Nat.card_eq_fintype_card

lemma Function.Injective.finite_preimage {α β : Type*} {s : Set β} {f : α → β}
  (hf : Function.Injective f) (hs : s.Finite) : (f ⁻¹' s).Finite :=
  hs.preimage (hf.injOn _)

lemma Function.Injective.nat_card_preimage {α β : Type*} {s : Set β} {f : α → β}
    (hf : Injective f) (s_fin : s.Finite) (hs : s ⊆ range f) : Nat.card (f ⁻¹' s) = Nat.card s := by
  have : Fintype (f ⁻¹' s) := (hf.finite_preimage s_fin).fintype
  conv_rhs => rw [← image_preimage_eq_iff.2 hs,
    Set.nat_card_image_of_injective hf (hf.finite_preimage s_fin)]

lemma Nat.card_image_le {α β: Type*} {s : Set α} {f : α → β} (hs : s.Finite) :
    Nat.card (f '' s) ≤ Nat.card s := by
  simp only [Set.Nat.card_coe_set_eq]
  exact Set.ncard_image_le hs

lemma Nat.card_singleton_prod {α β : Type*} (a : α) (B : Set β) : Nat.card ({a} ×ˢ B) = Nat.card B := by
  by_cases hB : Set.Finite B
  · rw[Set.singleton_prod, Set.nat_card_image_of_injective (Prod.mk.inj_left a) hB]
  · rw[Set.Infinite.card_eq_zero hB, Set.Infinite.card_eq_zero <| Set.Infinite.prod_right hB ⟨a,by rfl⟩]

lemma Nat.card_prod_singleton {α β : Type*} (A : Set α) (b : β) : Nat.card (A ×ˢ {b}) = Nat.card A := by
  by_cases hA : Set.Finite A
  · rw[Set.prod_singleton, Set.nat_card_image_of_injective (Prod.mk.inj_right b) hA]
  · rw[Set.Infinite.card_eq_zero hA, Set.Infinite.card_eq_zero <| Set.Infinite.prod_left hA ⟨b,by rfl⟩]
