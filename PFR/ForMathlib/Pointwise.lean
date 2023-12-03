import Mathlib.Data.Finset.Pointwise
import PFR.Mathlib.SetTheory.Cardinal.Finite

open scoped Pointwise

@[to_additive]
lemma Nat.card_mul_singleton {G : Type*} [Group G] (A : Set G) (x : G) :
    Nat.card (A * ({x} : Set G)) = Nat.card A := by
  have : (Equiv.mulRight x) '' A = A * {x} := by simp
  rw [← this, Nat.card_image_equiv]

@[to_additive]
lemma Set.finite_mul_iff {G : Type*} [Group G] (A B : Set G) :
    (A * B).Finite ↔ A = ∅ ∨ B = ∅ ∨ (A.Finite ∧ B.Finite) := by
  rw [←not_infinite]
  refine (infinite_image2 (fun _ _ ↦ (mul_left_injective _).injOn _)
    fun _ _ ↦ (mul_right_injective _).injOn _).not.trans ?_
  simp [not_or, -not_and, not_and_or, not_nonempty_iff_eq_empty]
  aesop

@[to_additive]
lemma Nat.card_mul_le {G : Type*} [Group G] (A B : Set G) :
    Nat.card (A * B) ≤ Nat.card A * Nat.card B := by
  classical
  rcases Set.infinite_or_finite (A * B) with h|h
  · simp [Set.Infinite.card_eq_zero h]
  rcases Set.eq_empty_or_nonempty A with rfl|hA
  · simp
  rcases Set.eq_empty_or_nonempty B with rfl|hB
  · simp
  obtain ⟨Afin, Bfin⟩ : Set.Finite A ∧ Set.Finite B := by
    simpa [Set.finite_mul_iff, hA.ne_empty, hB.ne_empty] using h
  rw [Nat.card_eq_toFinset_card h, Nat.card_eq_toFinset_card Afin, Nat.card_eq_toFinset_card Bfin]
  convert Finset.card_mul_le (s := Afin.toFinset) (t := Bfin.toFinset)
  ext z
  simp [← Finset.mem_coe]
