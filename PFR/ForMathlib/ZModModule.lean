import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Finsupp.Fintype
import Mathlib.GroupTheory.Sylow
import PFR.Mathlib.Data.ZMod.Basic

open Function Set ZMod

namespace Module
variable {p n : ℕ} {G : Type*} [AddCommGroup G]

abbrev quotient_group {H : AddSubgroup G} (hH : ∀ x, p • x ∈ H) : Module (ZMod p) (G ⧸ H) :=
  AddCommGroup.zmodModule (by simpa [QuotientAddGroup.forall_mk, ← QuotientAddGroup.mk_nsmul])

section general
variable [Module (ZMod n) G]

lemma isPGroup_multiplicative : IsPGroup n (Multiplicative G) := by
  simpa [IsPGroup, Multiplicative.forall] using fun _ ↦ ⟨1, by simp [← ofAdd_nsmul]⟩

variable (n) in
lemma exists_finsupp {A : Set G} {x : G} (hx : x ∈ Submodule.span ℤ A) :
    ∃ μ : A →₀ ZMod n, (μ.sum fun a r ↦ (ZMod.cast r : ℤ) • (a : G)) = x := by
  rcases mem_span_set.1 hx with ⟨w, hw, rfl⟩; clear hx
  use (w.subtypeDomain A).mapRange (↑) Int.cast_zero
  rw [Finsupp.sum_mapRange_index (by simp)]
  set A' := w.support.preimage ((↑) : A → G) injOn_subtype_val
  erw [Finsupp.sum_subtypeDomain_index hw
    (h := fun (a : G) (r : ℤ) ↦ (ZMod.cast (r : ZMod n) : ℤ) • a)]
  refine (Finsupp.sum_congr ?_).symm
  intro g _
  generalize w g = r
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (ZMod.cast (r : ZMod n) : ℤ) = r + n * k := by
    use -(r / n)
    rw_mod_cast [ZMod.coe_intCast, Int.emod_def, sub_eq_add_neg, mul_neg]
  simp [hk, add_smul, mul_smul]

end general

/-- In an elementary abelian $p$-group, every finite subgroup $H$ contains a further subgroup of
cardinality between $k$ and $pk$, if $k \leq |H|$.-/
lemma exists_submodule_subset_card_le (hp : p.Prime) [Module (ZMod p) G] {k : ℕ}
    (H : Submodule (ZMod p) G) (hk : k ≤ Nat.card H) (h'k : k ≠ 0) :
    ∃ (H' : Submodule (ZMod p) G), Nat.card H' ≤ k ∧ k < p * Nat.card H' ∧ H' ≤ H := by
  obtain ⟨H'm, H'mHm, H'mk, kH'm⟩ := Sylow.exists_subgroup_le_card_le
    (H := AddSubgroup.toSubgroup ((AddSubgroup.toZModSubmodule _).symm H)) hp
      isPGroup_multiplicative hk h'k
  exact ⟨AddSubgroup.toZModSubmodule _ (AddSubgroup.toSubgroup.symm H'm), H'mk, kH'm, H'mHm⟩

end Module
