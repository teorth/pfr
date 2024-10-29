import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The measure of a connected component of a space depends continuously on a finite measure
-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

lemma FiniteMeasure.continuous_integral_boundedContinuousFunction
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] (f : α →ᵇ ℝ) :
    Continuous (fun (μ : FiniteMeasure α) ↦ ∫ x, f x ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  exact continuousAt_of_tendsto_nhds
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp tendsto_id f)

lemma ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] (f : α →ᵇ ℝ) :
    Continuous fun μ : ProbabilityMeasure α ↦ ∫ x, f x ∂μ := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  exact continuousAt_of_tendsto_nhds
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp tendsto_id f)

lemma lintegral_indicatorBCF {α : Type*} [TopologicalSpace α] [MeasurableSpace α] (μ : Measure α)
    {s : Set α} (s_clopen : IsClopen s) (s_mble : MeasurableSet s) :
    ∫⁻ x, ENNReal.ofReal (BoundedContinuousFunction.indicator s s_clopen x) ∂μ = μ s := by
  convert lintegral_indicator_one s_mble
  simp
  rename_i x
  by_cases hx : x ∈ s <;> simp [hx]

lemma integral_indicatorBCF {α : Type*} [TopologicalSpace α] [MeasurableSpace α] (μ : Measure α)
    {s : Set α} (s_clopen : IsClopen s) (s_mble : MeasurableSet s) :
    ∫ x, BoundedContinuousFunction.indicator s s_clopen x ∂μ = (μ s).toReal :=
  integral_indicator_one s_mble

end MeasureTheory
