import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityMeasure Topology Metric Filter Set ENNReal NNReal
open scoped Topology ENNReal NNReal

/-- The measure of any connected component depends continuously on the `FiniteMeasure`.-/
lemma continuous_finiteMeasure_apply_of_isClopen
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {s : Set α} (s_clopen : IsClopen s) :
    Continuous fun μ : FiniteMeasure α ↦ (μ : Measure α).real s := by
  convert FiniteMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.indicator s s_clopen)
  have s_mble : MeasurableSet s := s_clopen.isOpen.measurableSet
  simp [integral_indicator, s_mble, Measure.real]

/-- The probability of any connected component depends continuously on the `ProbabilityMeasure`.-/
lemma continuous_probabilityMeasure_apply_of_isClopen
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {s : Set α} (s_clopen : IsClopen s) :
    Continuous fun μ : ProbabilityMeasure α ↦ (μ : Measure α).real s := by
  convert ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.indicator s s_clopen)
  have s_mble : MeasurableSet s := s_clopen.isOpen.measurableSet
  simp [integral_indicator, s_mble, Measure.real]

variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X] [BorelSpace X]

lemma continuous_pmf_apply' (i : X) :
    Continuous fun μ : ProbabilityMeasure X ↦ (μ : Measure X).real {i} :=
  continuous_probabilityMeasure_apply_of_isClopen (s := {i}) $ isClopen_discrete _

lemma continuous_pmf_apply (i : X) : Continuous fun μ : ProbabilityMeasure X ↦ μ {i} := by
  -- KK: The coercion fight here is one reason why I now prefer ℝ-valued and not ℝ≥0-valued probas.
  convert continuous_real_toNNReal.comp (continuous_pmf_apply' i)
  ext
  simp [Measure.real, Function.comp_apply]
  rfl

open Filter in
lemma tendsto_lintegral_of_forall_of_finite [Finite X] {ι : Type*} {L : Filter ι}
    (μs : ι → Measure X) (μ : Measure X)
    (f : X →ᵇ ℝ≥0) (h : ∀ (x : X), Tendsto (fun i ↦ μs i {x}) L (𝓝 (μ {x}))) :
    Tendsto (fun i ↦ ∫⁻ x, f x ∂(μs i)) L (𝓝 (∫⁻ x, f x ∂μ)) := by
  cases nonempty_fintype X
  simp only [lintegral_fintype]
  refine tendsto_finset_sum Finset.univ ?_
  exact fun x _ ↦ ENNReal.Tendsto.const_mul (h x) (Or.inr ENNReal.coe_ne_top)

/-- Probability measures on a finite space tend to a limit if and only if the probability masses
of all points tend to the corresponding limits. Version in ℝ≥0. -/
lemma ProbabilityMeasure.tendsto_iff_forall_apply_tendsto {ι α : Type*} {L : Filter ι} [Finite α]
    [TopologicalSpace α] [DiscreteTopology α] [MeasurableSpace α] [BorelSpace α]
    (μs : ι → ProbabilityMeasure α) (μ : ProbabilityMeasure α) :
    Tendsto μs L (𝓝 μ) ↔ ∀ a, Tendsto (μs · {a}) L (𝓝 (μ {a})) := by
  constructor <;> intro h
  · exact fun a ↦ ((continuous_pmf_apply a).continuousAt (x := μ)).tendsto.comp h
  · apply ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mpr
    intro f
    apply tendsto_lintegral_of_forall_of_finite
    intro a
    -- TODO: rename `ENNReal.continuous_coe` to `ENNReal.continuous_ofNNReal`?
    convert ENNReal.continuous_coe.continuousAt.tendsto.comp (h a)
    · simp [Function.comp_apply, ennreal_coeFn_eq_coeFn_toMeasure]
    · simp [ennreal_coeFn_eq_coeFn_toMeasure]

/-- Probability measures on a finite space tend to a limit if and only if the probability masses
of all points tend to the corresponding limits. Version in ℝ≥0∞. -/
lemma ProbabilityMeasure.tendsto_iff_forall_apply_tendsto_ennreal
    {ι α : Type*} {L : Filter ι} [Finite α]
    [TopologicalSpace α] [DiscreteTopology α] [MeasurableSpace α] [BorelSpace α]
    (μs : ι → ProbabilityMeasure α) (μ : ProbabilityMeasure α) :
    Tendsto μs L (𝓝 μ) ↔ ∀ a, Tendsto (fun n ↦ (μs n : Measure α) {a}) L
      (𝓝 ((μ : Measure α) {a})) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_apply_tendsto]
  simp [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.tendsto_coe]
