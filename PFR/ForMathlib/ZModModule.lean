import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow

open Function Set ZMod

namespace ZModModule
variable {p : ℕ} {G : Type*} [AddCommGroup G]

/-- In an elementary abelian $p$-group, every finite subgroup $H$ contains a further subgroup of
cardinality between $k$ and $pk$, if $k \leq |H|$.-/
lemma exists_submodule_subset_card_le (hp : p.Prime) [Module (ZMod p) G] {k : ℕ}
    (H : Submodule (ZMod p) G) (hk : k ≤ Nat.card H) (h'k : k ≠ 0) :
    ∃ (H' : Submodule (ZMod p) G), Nat.card H' ≤ k ∧ k < p * Nat.card H' ∧ H' ≤ H := by
  obtain ⟨H'm, H'mHm, H'mk, kH'm⟩ := Sylow.exists_subgroup_le_card_le
    (H := AddSubgroup.toSubgroup ((AddSubgroup.toZModSubmodule _).symm H)) hp
      isPGroup_multiplicative hk h'k
  exact ⟨AddSubgroup.toZModSubmodule _ (AddSubgroup.toSubgroup.symm H'm), H'mk, kH'm, H'mHm⟩

end ZModModule
