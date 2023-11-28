import Mathlib.Data.Set.Finite
import Mathlib.SetTheory.Cardinal.Finite

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
