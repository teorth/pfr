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

lemma lintegral_eq_zero_of_ae_zero {μ : Measure α} {f : α → ℝ≥0∞} {E : Set α} (hE: μ Eᶜ = 0) (hf: ∀ x ∈ E, f x = 0) (hmes: MeasurableSet E) : ∫⁻ x, f x ∂μ = 0 := by
  rw [<- lintegral_add_compl f hmes, set_lintegral_measure_zero Eᶜ f hE, set_lintegral_congr_fun (f := f) (g := (fun _ ↦ 0)) hmes]
  . simp
  exact ae_of_all μ hf

end MeasureTheory
