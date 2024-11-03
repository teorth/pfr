import Mathlib.Data.Set.Pointwise.SMul

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
end Set
