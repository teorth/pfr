import PFR.ForMathlib.CompactProb
import Mathlib.Tactic.Peel
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Continuity of products of probability measures on finite types

TODO: we have the continuity of the product measure in mathlib, in full generality, so this file
could be adapted to greater generality using this, or removed completely.
-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

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

/-- If probability measures on two finite spaces tend to limits, then the products of them
on the product space tend to the product of the limits.
TODO: In Mathlib, this should be done on all separable metrizable spaces. -/
lemma ProbabilityMeasure.tendsto_prod_of_tendsto_of_tendsto
    {ι : Type*} {L : Filter ι} {α β : Type*}
    [Finite α] [TopologicalSpace α] [DiscreteTopology α] [MeasurableSpace α] [BorelSpace α]
    [Finite β] [TopologicalSpace β] [DiscreteTopology β] [MeasurableSpace β] [BorelSpace β]
    (μs : ι → ProbabilityMeasure α) (μ : ProbabilityMeasure α) (μs_lim : Tendsto μs L (𝓝 μ))
    (νs : ι → ProbabilityMeasure β) (ν : ProbabilityMeasure β) (νs_lim : Tendsto νs L (𝓝 ν)) :
    Tendsto (fun i ↦ (μs i).prod (νs i)) L (𝓝 (μ.prod ν)) := by
  apply (ProbabilityMeasure.tendsto_iff_forall_apply_tendsto _ _).mpr
  intro ab
  have aux : {ab} = {ab.1} ×ˢ {ab.2} := toFinset_inj.mp rfl
  simp_rw [aux, prod_prod]
  have obs_μs := ((continuous_pmf_apply ab.1).continuousAt (x := μ)).tendsto.comp μs_lim
  have obs_νs := ((continuous_pmf_apply ab.2).continuousAt (x := ν)).tendsto.comp νs_lim
  exact tendsto_mul.comp (Tendsto.prodMk_nhds obs_μs obs_νs)
