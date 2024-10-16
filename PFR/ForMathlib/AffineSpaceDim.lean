import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness

variable {G : Type*} [AddCommGroup G]

/-- If G ≅ ℤᵈ then there is a subgroup H of G such that A lies in a coset of H. This is helpful to
give the equivalent definition of `dimension`. Here this is stated in greated generality since the
proof carries over automatically. -/
lemma exists_coset_cover (A : Set G) :
    ∃ (d : ℕ), ∃ (S : Submodule ℤ G) (v : G), Module.finrank ℤ S = d ∧ ∀ a ∈ A, a - v ∈ S :=
  ⟨Module.finrank ℤ (⊤ : Submodule ℤ G), ⊤, by simp⟩

-- TODO: Redefine as `Module.finrank ℤ (vectorSpan ℤ A)`
open scoped Classical in
/-- The dimension of the affine span over `ℤ` of a subset of an additive group. -/
noncomputable def dimension (A : Set G) : ℕ := Nat.find (exists_coset_cover A)

lemma dimension_le_of_coset_cover (A : Set G) (S : Submodule ℤ G) (v : G)
    (hA : ∀ a ∈ A, a - v ∈ S) : dimension A ≤ Module.finrank ℤ S := by
  classical exact Nat.find_le ⟨S , v, rfl, hA⟩

lemma dimension_le_rank [Module.Finite ℤ G] (A : Set G) : dimension A ≤ Module.finrank ℤ G := by
  simpa using dimension_le_of_coset_cover A ⊤ 0 (by simp)
