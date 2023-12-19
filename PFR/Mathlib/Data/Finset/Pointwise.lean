import Mathlib.Data.Finset.Pointwise
import PFR.Mathlib.Data.Set.Pointwise.Finite
import PFR.Mathlib.SetTheory.Cardinal.Finite

open scoped Pointwise

namespace Set
variable {α β : Type*}

section MulAction
variable [Group α] [MulAction α β]

@[to_additive]
lemma card_smul_set (a : α) (s : Set β) : Nat.card ↥(a • s) = Nat.card s :=
  Nat.card_image_of_injective (MulAction.injective a) _

end MulAction

section Mul
variable [Mul α] [IsCancelMul α] {s t : Set α}

@[to_additive]
lemma card_mul_le : Nat.card (s * t) ≤ Nat.card s * Nat.card t := by
  classical
  obtain h | h := (s * t).infinite_or_finite
  · simp [Set.Infinite.card_eq_zero h]
  obtain ⟨hs, ht⟩ | rfl | rfl := finite_mul.1 h
  · lift s to Finset α using hs
    lift t to Finset α using ht
    rw [← Finset.coe_mul]
    simpa [-Finset.coe_mul] using Finset.card_mul_le
  all_goals simp

end Mul

variable [Group α] {s t : Set α}

@[to_additive (attr := simp)]
lemma card_inv (s : Set α) : Nat.card ↥(s⁻¹) = Nat.card s := by
  rw [← image_inv, Nat.card_image_of_injective inv_injective]

@[to_additive]
lemma card_div_le : Nat.card (s / t) ≤ Nat.card s * Nat.card t := by
  rw [div_eq_mul_inv, ← card_inv t]; exact card_mul_le
