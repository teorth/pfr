import Mathlib.GroupTheory.Sylow
import PFR.Mathlib.Algebra.Order.Archimedean

open Nat

/-! Move the content of this section close to `Sylow.exists_subgroup_card_pow_prime`. -/
namespace Sylow
variable {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] (h : IsPGroup p G)

lemma exists_subgroup_card_eq {s : ℕ} (hs : p ^ s ≤ Nat.card G) :
    ∃ (H : Subgroup G), Nat.card H = p ^ s := by
  classical
  let A : Fintype G := by
    have : Nat.card G ≠ 0 := by linarith [one_le_pow s p hp.out.pos]
    have : Finite G := finite_of_card_ne_zero this
    exact Fintype.ofFinite G
  suffices ∃ (H : Subgroup G), Fintype.card H = p ^ s by simpa [card_eq_fintype_card]
  apply Sylow.exists_subgroup_card_pow_prime
  rcases IsPGroup.iff_card.mp h with ⟨k, hk⟩
  simp_rw [card_eq_fintype_card] at hk hs ⊢
  rw [hk] at hs ⊢
  have : s ≤ k := (pow_le_pow_iff (Prime.one_lt hp.out)).1 hs
  exact pow_dvd_pow p this

lemma exists_subgroup_subset_card_eq {s : ℕ} {H : Subgroup G} (hs : p ^ s ≤ Nat.card H) :
    ∃ (H' : Subgroup G), Nat.card H' = p ^ s ∧ H' ≤ H := by
  rcases exists_subgroup_card_eq (IsPGroup.to_subgroup h H) hs with ⟨H', H'card⟩
  let L := H'.map H.subtype
  refine ⟨L, ?_, Subgroup.map_subtype_le H'⟩
  convert H'card using 1
  let e : H' ≃* L := H'.equivMapOfInjective (Subgroup.subtype H) H.subtype_injective
  exact card_congr e.symm.toEquiv

lemma exists_subgroup_subset_card_le {k : ℕ} (H : Subgroup G)
    (hk : k ≤ Nat.card H) (h'k : k ≠ 0) :
    ∃ (H' : Subgroup G), Nat.card H' ≤ k ∧ k < p * Nat.card H' ∧ H' ≤ H := by
  obtain ⟨s, sk, ks⟩ : ∃ s, p ^ s ≤ k ∧ k < p ^ (s + 1) :=
    exists_nat_pow_near' (one_le_iff_ne_zero.mpr h'k) (Prime.one_lt hp.out)
  rcases exists_subgroup_subset_card_eq h (sk.trans hk) with ⟨H', H'card, H'H⟩
  simp only [_root_.pow_succ] at ks
  rw [← H'card] at sk ks
  exact ⟨H', sk, ks, H'H⟩

end Sylow
