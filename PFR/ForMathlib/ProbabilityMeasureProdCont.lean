import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
import PFR.ForMathlib.FiniteMeasureProd
import PFR.ForMathlib.CompactProb
--import Mathlib

/-!
# Continuity of products of probability measures on finite types

-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction BigOperators

namespace MeasureTheory

/-- Finite measures on a finite space tend to a limit if and only if the probability masses
of all points tend to the corresponding limits. -/
lemma FiniteMeasure.tendsto_iff_forall_apply_tendsto
    {ι : Type*} {L : Filter ι} [NeBot L]
    {α : Type*} [Fintype α] [TopologicalSpace α] [DiscreteTopology α] [MeasurableSpace α]
    [BorelSpace α] (μs : ι → FiniteMeasure α) (μ : FiniteMeasure α) :
    Tendsto μs L (𝓝 μ) ↔ ∀ (a : α), Tendsto (fun i ↦ μs i {a}) L (𝓝 (μ {a})) := by
  sorry

/-- Probability measures on a finite space tend to a limit if and only if the probability masses
of all points tend to the corresponding limits. -/
lemma ProbabilityMeasure.tendsto_iff_forall_apply_tendsto
    {ι : Type*} {L : Filter ι} [NeBot L]
    {α : Type*} [Fintype α] [TopologicalSpace α] [DiscreteTopology α] [MeasurableSpace α]
    [BorelSpace α] (μs : ι → ProbabilityMeasure α) (μ : ProbabilityMeasure α) :
    Tendsto μs L (𝓝 μ) ↔ ∀ (a : α), Tendsto (fun i ↦ μs i {a}) L (𝓝 (μ {a})) := by
  constructor <;> intro h
  · exact fun a ↦ ((continuous_pmf_apply a).continuousAt (x := μ)).tendsto.comp h
  · apply ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mpr
    intro f
    apply tendsto_lintegral_of_forall_of_fintype
    intro a
    simp at h ⊢
    -- TODO: rename `ENNReal.continuous_coe` to `ENNReal.continuous_ofNNReal`
    convert ENNReal.continuous_coe.continuousAt.tendsto.comp (h a)
    simp only [Function.comp_apply, ne_eq, ennreal_coeFn_eq_coeFn_toMeasure, coe_toNNReal]
    simp only [ne_eq, ennreal_coeFn_eq_coeFn_toMeasure]

end MeasureTheory -- namespace
