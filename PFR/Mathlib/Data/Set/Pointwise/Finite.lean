import Mathlib.Data.Set.Pointwise.Finite
import PFR.Mathlib.Data.Set.Finite

open scoped Pointwise

namespace Set
variable {α : Type*} [Mul α] [IsCancelMul α] {s t : Set α}

@[to_additive]
lemma finite_mul : (s * t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ :=
  finite_image2  (fun _ _ ↦ (mul_left_injective _).injOn _)
    fun _ _ ↦ (mul_right_injective _).injOn _

end Set
