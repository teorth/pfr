import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

open ENNReal

namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
variable [MeasurableSingletonClass α]

-- TODO: Change RHS of `lintegral_fintype`
lemma lintegral_eq_sum (μ : Measure α) (f : α → ℝ≥0∞) [Fintype α] :
    ∫⁻ x, f x ∂μ = ∑ x, μ {x} * f x := by
  simp_rw [lintegral_fintype, mul_comm]

lemma lintegral_eq_tsum (μ : Measure α) (f : α → ℝ≥0∞) [Countable α] :
    ∫⁻ x, f x ∂μ = ∑' x, μ {x} * f x := by
  simp_rw [lintegral_countable', mul_comm]

-- TODO: Change RHS of `lintegral_finset`
lemma setLIntegral_eq_sum (μ : Measure α) (s : Finset α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ = ∑ x ∈ s, μ {x} * f x := by
  simp_rw [mul_comm, lintegral_finset]

lemma lintegral_eq_single (μ : Measure α) (a : α) (f : α → ℝ≥0∞) (ha : ∀ b ≠ a, f b = 0) :
    ∫⁻ x, f x ∂μ = f a * μ {a} := by
  rw [← lintegral_add_compl f (A := {a}) (MeasurableSet.singleton a), lintegral_singleton,
    setLIntegral_congr_fun (g := fun _ ↦ 0) (MeasurableSet.compl (MeasurableSet.singleton a)),
    lintegral_zero, add_zero]
  simp +contextual [Set.EqOn, ha]

end MeasureTheory
