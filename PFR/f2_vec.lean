import Mathlib.Data.Finset.Pointwise
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic
import PFR.ForMathlib.Miscellaneous

/-!
# Finite field vector spaces

Here we define the notion of a vector space over a finite field, and record basic results about it.

## Main classes

* `ElementaryAddCommGroup`: An elementary p-group.

-/


/-- An elementary `p`-group, i.e., a commutative additive group in which every nonzero element has
order exactly `p`. -/
class ElementaryAddCommGroup (G : Type*) [AddCommGroup G] (p : outParam ℕ) : Prop where
  orderOf_of_ne {x : G} (hx : x ≠ 0) : addOrderOf x = p
-- may want to change this to p . x = 0 for all x

namespace ElementaryAddCommGroup

/-- In an elementary abelian $p$-group, every finite subgroup $H$ contains a further subgroup of cardinality between $k$ and $pk$, if $k \leq |H|$.-/
lemma exists_subgroup_subset_card_le {G : Type*} {p : ℕ}
    [AddCommGroup G] [h : ElementaryAddCommGroup G p] [Fact p.Prime]
    {k : ℕ} (H : AddSubgroup G) (hk : k ≤ Nat.card H) (h'k : k ≠ 0) :
    ∃ (H' : AddSubgroup G), Nat.card H' ≤ k ∧ k < p * Nat.card H' ∧ H' ≤ H := by
  let Gm := Multiplicative G
  have hm : IsPGroup p Gm := by
    intro gm
    rcases eq_or_ne gm 1 with rfl|hg
    · exact ⟨0, by simp⟩
    · refine ⟨1, ?_⟩
      have : Multiplicative.toAdd gm ≠ 0 := hg
      simpa [h.orderOf_of_ne this] using addOrderOf_nsmul_eq_zero (Multiplicative.toAdd gm)
  let Hm : Subgroup Gm := AddSubgroup.toSubgroup H
  rcases Sylow.exists_subgroup_subset_card_le hm Hm hk h'k with ⟨H'm, H'mk, kH'm, H'mHm⟩
  exact ⟨AddSubgroup.toSubgroup.symm H'm, H'mk, kH'm, H'mHm⟩

variable [AddCommGroup G] [elem : ElementaryAddCommGroup G 2]

@[simp]
lemma sub_eq_add ( x y : G ) : x - y = x + y := by
  rw [sub_eq_add_neg, add_right_inj, ← add_eq_zero_iff_neg_eq]
  by_cases h : y = 0
  · simp only [h, add_zero]
  · simpa only [elem.orderOf_of_ne h, two_nsmul] using (addOrderOf_nsmul_eq_zero y)

@[simp]
lemma add_self ( x : G ) : x + x = 0 := by
  rw [← sub_eq_add]
  simp


@[simp]
lemma neg_eq_self ( x : G ) : - x = x := by
  simpa [-sub_eq_add] using sub_eq_add 0 x

lemma sum_add_sum_eq_sum ( x y z : G ) : (x + y) + (y + z) = x + z := by
  rw [← sub_eq_add x y]
  abel

lemma sum_add_sum_add_sum_eq_zero ( x y z : G ) : (x + y) + (y + z) + (z + x) = 0 := by
  rw [sum_add_sum_eq_sum, add_comm x z, add_self]

open Function

@[simp] lemma char_smul_eq_zero {Γ : Type*} [AddCommGroup Γ] [ElementaryAddCommGroup Γ p] (x : Γ) :
    p • x = 0 := by
  by_cases hx : x = 0
  · simp only [hx, smul_zero]
  · have obs := ElementaryAddCommGroup.orderOf_of_ne hx
    rw [addOrderOf] at obs
    simpa only [obs, add_left_iterate, add_zero] using
      iterate_minimalPeriod (f := fun z ↦ x + z) (x := 0)

lemma char_ne_one_of_nonzero {Γ : Type*} [AddCommGroup Γ] [ElementaryAddCommGroup Γ p] {x : Γ}
    (x_ne_zero : x ≠ 0) : p ≠ 1 := by
  have obs := ElementaryAddCommGroup.orderOf_of_ne x_ne_zero
  rw [addOrderOf] at obs
  by_contra maybe_one
  apply x_ne_zero
  simpa only [obs, maybe_one, iterate_succ, iterate_zero, comp_apply, add_zero, id_eq] using
    iterate_minimalPeriod (f := fun z ↦ x + z) (x := 0)

lemma two_le_char_of_nonzero {Γ : Type*} [NeZero p] [AddCommGroup Γ] [ElementaryAddCommGroup Γ p] {x : Γ}
    (x_ne_zero : x ≠ 0) : 2 ≤ p := by
  by_contra maybe_small
  have p_le_one : p ≤ 1 := by linarith
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp p_le_one with hp|hp
  · simp_all only [neZero_zero_iff_false]
  · exact char_ne_one_of_nonzero x_ne_zero hp

lemma mem_periodicPts {Γ : Type*} [NeZero p] [AddCommGroup Γ] [ElementaryAddCommGroup Γ p]
    {x : Γ} (y : Γ) : y ∈ periodicPts (fun z ↦ x + z) := by
  simp only [periodicPts, IsPeriodicPt, add_left_iterate, Set.mem_setOf_eq]
  exact ⟨p, Fin.size_pos', by simp [IsFixedPt]⟩

open Nat in
instance (Ω Γ : Type*) (p : ℕ) [NeZero p] [AddCommGroup Γ] [ElementaryAddCommGroup Γ p] :
    ElementaryAddCommGroup (Ω → Γ) p where
  orderOf_of_ne := by
    intro f f_ne_zero
    have iter_p : (fun x ↦ f + x)^[p] 0 = 0 := by
      ext ω
      simp
    have no_less : ∀ n, 0 < n → n < p → (fun x ↦ f + x)^[n] 0 ≠ 0 := by
      intro n n_pos n_lt_p
      apply ne_iff.mpr
      obtain ⟨ω, hfω⟩ := show ∃ ω, f ω ≠ 0 from ne_iff.mp f_ne_zero
      existsi ω
      have obs := ElementaryAddCommGroup.orderOf_of_ne hfω
      rw [addOrderOf] at obs
      by_contra con
      apply not_isPeriodicPt_of_pos_of_lt_minimalPeriod (f := fun x ↦ f ω + x) (x := 0)
              n_pos.ne.symm (by simpa only [obs] using n_lt_p)
      simp_rw [IsPeriodicPt, IsFixedPt]
      convert con
      simp
    rw [addOrderOf, minimalPeriod]
    have mem_pPts : 0 ∈ periodicPts (fun g ↦ f + g) := by
      rw [periodicPts]
      existsi p
      rw [IsPeriodicPt, IsFixedPt]
      refine ⟨Fin.size_pos', ?_⟩
      ext ω
      simp
    simp only [mem_pPts, gt_iff_lt, dite_true]
    classical
    rw [find_eq_iff]
    refine ⟨⟨Fin.size_pos', iter_p⟩, ?_⟩
    intro n n_lt_p
    by_contra con
    exact no_less n con.1 n_lt_p con.2

lemma pi.sub_eq_add {ι} ( x y : ι → G ) : x - y = x + y := by simp

end ElementaryAddCommGroup
