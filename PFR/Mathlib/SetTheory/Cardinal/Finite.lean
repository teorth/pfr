import Mathlib.SetTheory.Cardinal.Finite

open Function Set

variable {α β : Type*} {f : α → β} {s : Set α}

lemma Nat.card_eq_finset_card {s : Finset α} : Nat.card s = s.card := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

lemma Nat.card_eq_toFinset_card (hs : s.Finite) : Nat.card s = hs.toFinset.card := by
  simp only [←Nat.card_eq_finset_card, Finite.mem_toFinset]

lemma Nat.card_image_of_injective (hf : Injective f) (hs : s.Finite) :
    Nat.card (f '' s) = Nat.card s := by
  classical
  have := hs.fintype
  have := fintypeImage s f
  simp_rw [Nat.card_eq_fintype_card, Set.card_image_of_injective _ hf]

lemma Nat.card_image_equiv (e : α ≃ β) : Nat.card (e '' s) = Nat.card s :=
    Nat.card_congr (e.image s).symm

lemma Function.Injective.nat_card_preimage {α β : Type*} {s : Set β} {f : α → β}
    (hf : Injective f) (s_fin : s.Finite) (hs : s ⊆ range f) : Nat.card (f ⁻¹' s) = Nat.card s := by
  have : Fintype (f ⁻¹' s) := (s_fin.preimage $ hf.injOn _).fintype
  conv_rhs =>
    rw [← image_preimage_eq_iff.2 hs, Nat.card_image_of_injective hf (s_fin.preimage $ hf.injOn _)]
