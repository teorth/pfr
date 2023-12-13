import Mathlib.MeasureTheory.Integral.Lebesgue

open ENNReal
open scoped BigOperators

namespace MeasureTheory
variable {α : Type*}  [MeasurableSpace α] [MeasurableSingletonClass α]

attribute [simp] lintegral_dirac

-- TODO: Change RHS of `lintegral_fintype`
lemma lintegral_eq_sum (μ : Measure α) (f : α → ℝ≥0∞) [Fintype α] : ∫⁻ x, f x ∂μ = ∑ x, μ {x} * f x := by
  simp_rw [lintegral_fintype, mul_comm]

lemma lintegral_eq_sum_countable (μ : Measure α) (f : α → ℝ≥0∞) [Countable α] : ∫⁻ x, f x ∂μ = ∑' x, μ {x} * f x := by
  simp_rw [lintegral_countable', mul_comm]

end MeasureTheory
