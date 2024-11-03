import PFR.ForMathlib.MeasureReal
import PFR.Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The measure of a connected component of a space depends continuously on a finite measure
-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal
open scoped Topology ENNReal NNReal BoundedContinuousFunction

section measure_of_component

/-- The measure of any connected component depends continuously on the `FiniteMeasure`.-/
lemma continuous_finiteMeasure_apply_of_isClopen
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {s : Set α} (s_clopen : IsClopen s) :
    Continuous fun μ : FiniteMeasure α ↦ (μ : Measure α).real s := by
  convert FiniteMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.indicator s s_clopen)
  have s_mble : MeasurableSet s := s_clopen.isOpen.measurableSet
  rw [integral_indicatorBCF _ s_clopen s_mble]
  rfl

/-- The probability of any connected component depends continuously on the `ProbabilityMeasure`.-/
lemma continuous_probabilityMeasure_apply_of_isClopen
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {s : Set α} (s_clopen : IsClopen s) :
    Continuous fun μ : ProbabilityMeasure α ↦ (μ : Measure α).real s := by
  convert ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.indicator s s_clopen)
  have s_mble : MeasurableSet s := s_clopen.isOpen.measurableSet
  rw [integral_indicatorBCF _ s_clopen s_mble]
  rfl

end measure_of_component -- section
