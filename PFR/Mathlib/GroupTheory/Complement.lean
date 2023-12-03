import Mathlib.GroupTheory.Complement

open Set
open scoped Pointwise

namespace Subgroup
variable {G : Type*} [Group G]

@[to_additive]
lemma IsComplement.mul_eq {G : Type*} [Group G] {A B : Set G} (h : IsComplement A B) :
    A * B = univ := by
  apply eq_univ_iff_forall.2 (fun x ↦ ?_)
  rcases (h.existsUnique x).exists with ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, rfl⟩
  exact mem_mul.2 ⟨y, z, hy, hz, rfl⟩

@[to_additive AddSubgroup.IsComplement.mul_card_eq]
lemma IsComplement.mul_card_eq {G : Type*} [Group G] {A B : Set G} (h : IsComplement A B) :
    Nat.card A * Nat.card B = Nat.card G := by
  convert Nat.card_congr (Equiv.ofBijective _ h)
  exact (Nat.card_prod ↑A ↑B).symm

/-- Given two subgroups `H' ⊆ H`, there exists a transversal `c` to `H'` inside `H`. -/
@[to_additive]
lemma exists_mul_eq_subgroup_of_le {H' H : Subgroup G} (h : H' ≤ H) :
    ∃ (c : Set G), c * (H' : Set G) = H ∧ Nat.card c * Nat.card H' = Nat.card H := by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [h]
  rw [this]
  obtain ⟨c, cmem, -⟩ : ∃ c ∈ Subgroup.leftTransversals H'', (1 : H) ∈ c :=
    Subgroup.exists_left_transversal 1
  refine ⟨H.subtype '' c, ?_, ?_⟩
  · have A : H.subtype '' (c * (H'' : Set H)) = H.subtype '' c * (H''.map H.subtype) :=
      image_mul (Subgroup.subtype H)
    rw [← A, IsComplement.mul_eq cmem]
    simp
    rfl
  · have I : Nat.card c * Nat.card H'' = Nat.card H := IsComplement.mul_card_eq cmem
    have J : Nat.card (H''.map H.subtype) = Nat.card H'' :=
      Nat.card_congr (Equiv.Set.image H.subtype _ (subtype_injective H)).symm
    rw [← I, Nat.card_congr (Equiv.Set.image H.subtype _ (subtype_injective H)).symm, J]

end Subgroup
