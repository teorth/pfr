import Mathlib.Data.Set.Pointwise.SMul

scoped[Pointwise] attribute [instance] Set.divisionCommMonoid Set.subtractionCommMonoid

open scoped Pointwise

namespace Set
variable {α : Type*}

section Mul
variable [Mul α]

@[to_additive] lemma singleton_mul' (a : α) (s : Set α) : {a} * s = a • s := singleton_mul

open scoped RightActions

@[to_additive]
lemma mul_singleton' (s : Set α) (a : α) : s * {a} = s <• a := mul_singleton

end Mul

section CommGroup
variable [CommGroup α]

@[to_additive] lemma smul_div_smul_comm (a : α) (s : Set α) (b : α) (t : Set α) :
    a • s / b • t = (a / b) • (s / t) := by
  simp_rw [← singleton_mul', mul_div_mul_comm _ s, singleton_div_singleton]

end CommGroup
end Set
