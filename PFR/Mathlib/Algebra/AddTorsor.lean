import Mathlib.Algebra.AddTorsor

open scoped Pointwise

namespace Set
variable {G P : Type*} [AddCommGroup G] [AddTorsor G P]

@[simp] lemma vadd_set_vsub_vadd_set (v : G) (s t : Set P) : (v +ᵥ s) -ᵥ (v +ᵥ t) = s -ᵥ t := by
  ext; simp [mem_vsub, mem_vadd_set]

end Set
