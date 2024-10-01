import Mathlib.MeasureTheory.Integral.Lebesgue

/-!
# TODO

Rename `setLIntegral_congr` to `setLIntegral_congr_set`
-/

open ENNReal

namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α]

attribute [simp] lintegral_dirac

lemma lintegral_eq_zero_of_ae_zero {μ : Measure α} {f : α → ℝ≥0∞} {E : Set α} (hE: μ Eᶜ = 0) (hf: ∀ x ∈ E, f x = 0) (hmes: MeasurableSet E) : ∫⁻ x, f x ∂μ = 0 := by
  rw [← lintegral_add_compl f hmes, setLIntegral_measure_zero Eᶜ f hE,
    setLIntegral_congr_fun (f := f) (g := (fun _ ↦ 0)) hmes]
  · simp
  exact ae_of_all μ hf

lemma lintegral_eq_setLIntegral {μ : Measure α} {s : Set α} (hs : μ sᶜ = 0) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  rw [← setLIntegral_univ, ← setLIntegral_congr]; rwa [ae_eq_univ]

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
  simp (config := { contextual := true}) [ha]

end MeasureTheory
