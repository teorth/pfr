import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The measure of a connected component of a space depends continuously on a finite measure
-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal
open scoped Topology ENNReal NNReal BoundedContinuousFunction

section measure_of_component

lemma continuous_integral_finiteMeasure
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] (f : α →ᵇ ℝ) :
    Continuous (fun (μ : FiniteMeasure α) ↦ ∫ x, f x ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  exact continuousAt_of_tendsto_nhds
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp tendsto_id f)

lemma continuous_integral_probabilityMeasure
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] (f : α →ᵇ ℝ) :
    Continuous fun μ : ProbabilityMeasure α ↦ ∫ x, f x ∂μ := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  exact continuousAt_of_tendsto_nhds
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp tendsto_id f)

/-- The indicator function of a clopen set, as a bounded continuous function. -/
noncomputable def indicatorBCF {α : Type*} [TopologicalSpace α]
    {s : Set α} (s_clopen : IsClopen s) :
    BoundedContinuousFunction α ℝ where
      toFun := s.indicator (fun _ ↦ (1 : ℝ))
      continuous_toFun := continuous_indicator (by simp [s_clopen]) $ continuous_const.continuousOn
      map_bounded' := by
        use 1
        intro x y
        by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
        · simp only [hx, hy, indicator_of_mem, dist_self, zero_le_one]
        · simp only [hx, hy, indicator_of_mem, not_false_eq_true, indicator_of_not_mem,
                      dist_zero_right, norm_one, le_refl]
        · simp only [hx, hy, not_false_eq_true, indicator_of_not_mem, indicator_of_mem,
                      dist_zero_left, norm_one, le_refl]
        · simp only [hx, hy, not_false_eq_true, indicator_of_not_mem, dist_self, zero_le_one]

@[simp] lemma indicatorBCF_apply {α : Type*} [TopologicalSpace α]
    {s : Set α} (s_clopen : IsClopen s) (x : α) :
    indicatorBCF s_clopen x = s.indicator (fun _ ↦ (1 : ℝ)) x := rfl

lemma lintegral_indicatorBCF {α : Type*} [TopologicalSpace α] [MeasurableSpace α] (μ : Measure α)
    {s : Set α} (s_clopen : IsClopen s) (s_mble : MeasurableSet s) :
    ∫⁻ x, ENNReal.ofReal (indicatorBCF s_clopen x) ∂μ = μ s := by
  convert lintegral_indicator_one s_mble
  rename_i x
  by_cases hx : x ∈ s <;> simp [hx]

lemma integral_indicatorBCF {α : Type*} [TopologicalSpace α] [MeasurableSpace α] (μ : Measure α)
    {s : Set α} (s_clopen : IsClopen s) (s_mble : MeasurableSet s) :
    ∫ x, (indicatorBCF s_clopen x) ∂μ = (μ s).toReal := integral_indicator_one s_mble

end measure_of_component -- section
