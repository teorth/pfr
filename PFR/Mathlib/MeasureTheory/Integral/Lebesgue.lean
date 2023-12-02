import Mathlib.MeasureTheory.Integral.Lebesgue

open ENNReal
open scoped BigOperators

namespace MeasureTheory
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

attribute [simp] lintegral_dirac

-- TODO: Change RHS of `lintegral_fintype`
lemma lintegral_eq_sum (μ : Measure α) (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂μ = ∑ x, μ {x} * f x := by
  simp_rw [lintegral_fintype, mul_comm]

end MeasureTheory
