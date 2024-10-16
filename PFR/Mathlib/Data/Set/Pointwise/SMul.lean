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

section CommGroup
variable [CommGroup α]

@[to_additive] lemma smul_div_smul_comm (a : α) (s : Set α) (b : α) (t : Set α) :
    a • s / b • t = (a / b) • (s / t) := by
  simp_rw [← singleton_mul', mul_div_mul_comm _ s, singleton_div_singleton]

end CommGroup

section graph
variable {F α β : Type*} [Group α] [CommGroup β] [FunLike F α β] [MonoidHomClass F α β]

@[to_additive]
lemma smul_graphOn (x : α × β) (s : Set α) (f : F) :
    x • s.graphOn f = (x.1 • s).graphOn fun a ↦ x.2 / f x.1 * f a := by
  ext ⟨a, b⟩
  simp [mem_smul_set_iff_inv_smul_mem, Prod.ext_iff, and_comm (a := _ = a), inv_mul_eq_iff_eq_mul,
    mul_left_comm _ _⁻¹, eq_inv_mul_iff_mul_eq, ← mul_div_right_comm, div_eq_iff_eq_mul, mul_comm b]

@[to_additive]
lemma smul_graphOn_univ (x : α × β) (f : F) :
    x • univ.graphOn f = univ.graphOn fun a ↦ x.2 / f x.1 * f a := by simp [smul_graphOn]

end graph
end Set
