import Mathlib.GroupTheory.Subgroup.Pointwise

open Set
open scoped Pointwise

namespace SubgroupClass
variable {S G : Type*} [SetLike S G]

section DivInvMonoid
variable [DivInvMonoid G] [SubgroupClass S G]

@[to_additive (attr := simp, norm_cast)]
lemma coe_mul_coe (H : S) : H * H = (H : Set G) := by aesop (add simp mem_mul)

end DivInvMonoid

section DivisionMonoid
variable [DivisionMonoid G] [SubgroupClass S G]

@[to_additive (attr := simp, norm_cast)] lemma inv_coe (H : S) : (H : Set G)⁻¹ = H := by aesop

@[to_additive (attr := simp, norm_cast)]
lemma coe_div_coe (H : S) : H / H = (H : Set G) := by simp [div_eq_mul_inv]

end DivisionMonoid
end SubgroupClass
