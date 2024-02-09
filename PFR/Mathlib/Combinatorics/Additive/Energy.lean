import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Finset.Pointwise
import PFR.Mathlib.Algebra.BigOperators.Basic

open scoped BigOperators Pointwise

variable {α : Type*} [DecidableEq α]

namespace Finset
section Mul
variable [Mul α] {s s₁ s₂ t t₁ t₂ : Finset α}

notation3:max "Eₘ[" s ", " t "]" => Finset.multiplicativeEnergy s t
notation3:max "E[" s ", " t "]" => Finset.additiveEnergy s t
notation3:max "Eₘ[" s "]" => Finset.multiplicativeEnergy s s
notation3:max "E[" s "]" => Finset.additiveEnergy s s

@[to_additive additiveEnergy_eq_card_filter]
lemma multiplicativeEnergy_eq_card_filter (s t : Finset α) :
    Eₘ[s, t] = (((s ×ˢ t) ×ˢ s ×ˢ t).filter fun ((a, b), c, d) ↦ a * b = c * d).card := by
  refine Finset.card_congr (fun ((a, b), c, d) _ ↦ ((a, c), b, d)) (by aesop) (by aesop)
    fun ((a, b), c, d) h ↦ ⟨((a, c), b, d), by simpa [and_and_and_comm] using h⟩

@[to_additive additiveEnergy_eq_sum_sq']
lemma multiplicativeEnergy_eq_sum_sq' (s : Finset α) :
    Eₘ[s] = ∑ a in s * s, ((s ×ˢ s).filter fun (x, y) ↦ x * y = a).card ^ 2 := by
  simp_rw [multiplicativeEnergy_eq_card_filter, sq, ← card_product]
  rw [← card_disjiUnion]
  swap
  · aesop (add simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left])
  · congr
    aesop (add unsafe mul_mem_mul)

@[to_additive additiveEnergy_eq_sum_sq]
lemma multiplicativeEnergy_eq_sum_sq [Fintype α] (s : Finset α) :
    Eₘ[s] = ∑ a, ((s ×ˢ s).filter fun (x, y) ↦ x * y = a).card ^ 2 := by
  simp_rw [multiplicativeEnergy_eq_card_filter, sq, ← card_product]
  rw [← card_disjiUnion]
  swap
  · aesop (add simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left])
  · congr
    aesop

@[to_additive card_sq_le_card_mul_additiveEnergy]
lemma card_sq_le_card_mul_multiplicativeEnergy (s t : Finset α) :
    ((s ×ˢ s).filter fun (x, y) ↦ x * y ∈ t).card^2 ≤ t.card * Eₘ[s] := by
  calc
    _ = (∑ b in t, ((s ×ˢ s).filter fun (x, y) ↦ x * y = b).card) ^ 2 := by
        rw [← sum_card_filter_eq]
    _ ≤ t.card * ∑ b in t, ((s ×ˢ s).filter fun (x, y) ↦ x * y = b).card ^ 2 := by
        simpa using sum_mul_sq_le_sq_mul_sq (α := ℕ) _ 1 _
    _ ≤ t.card * ∑ a in s * s, ((s ×ˢ s).filter fun (x, y) ↦ x * y = a).card ^ 2 := by
        refine mul_le_mul_left' (sum_le_sum_of_ne_zero ?_) _
        aesop (add simp [filter_eq_empty_iff]) (add unsafe mul_mem_mul)
    _ = t.card * Eₘ[s] := by rw [multiplicativeEnergy_eq_sum_sq']

end Mul
end Finset
