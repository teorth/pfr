import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import PFR.Mathlib.LinearAlgebra.Dimension.Finrank

open scoped Pointwise

namespace AffineSpace
variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P] {s : Set P}
  {S : Submodule k V}

variable (k) in
open scoped Classical in
/-- The dimension of the affine span over `ℤ` of a subset of an additive group. -/
noncomputable def finrank (s : Set P) : ℕ := (vectorSpan k s).finrank

variable (k) in
@[simp]
lemma finrank_vadd_set (s : Set P) (v : V) : finrank k (v +ᵥ s) = AffineSpace.finrank k s := by
  simp [finrank]

variable (k) in
@[simp] lemma finrank_empty [Nontrivial k] : finrank k (∅ : Set P) = 0 := by simp [finrank]

variable [StrongRankCondition k]

lemma finrank_le_submoduleFinrank [Module.Finite k S] (q : P) (hs : ∀ p ∈ s, p -ᵥ q ∈ S) :
    finrank k s ≤ S.finrank := by
  refine Submodule.finrank_mono ?_
  simpa [vectorSpan, Submodule.span_le, Set.vsub_subset_iff]
    using fun a ha b hb ↦ S.sub_mem (hs _ ha) (hs _ hb)

lemma finrank_le_moduleFinrank [Module.Finite k V] : finrank k s ≤ Module.finrank k V :=
  (vectorSpan k s).finrank_le

end AffineSpace
