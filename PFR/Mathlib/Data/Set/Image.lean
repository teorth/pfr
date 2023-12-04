import Mathlib.Data.Set.Image

namespace Subtype
variable {α : Type*}

@[simp]
lemma image_preimage_coe' (p : α → Prop) (s : Set α) :
    val '' (val ⁻¹' s : Set {a // p a}) = {a ∈ s | p a} := image_preimage_coe _ _

end Subtype
