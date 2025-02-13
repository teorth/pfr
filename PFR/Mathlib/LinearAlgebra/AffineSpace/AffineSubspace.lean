import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace

open scoped Pointwise

namespace AffineSpace
variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P] {s : Set P}
  {S : Submodule k V}

@[simp] lemma vectorSpan_vadd (s : Set P) (v : V) : vectorSpan k (v +ᵥ s) = vectorSpan k s := by
  simp [vectorSpan]

end AffineSpace
