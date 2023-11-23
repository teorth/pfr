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
  sorry -- Almost the same as below (some earlier lemmas need restating, too).

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
    -- TODO: rename `ENNReal.continuous_coe` to `ENNReal.continuous_ofNNReal`?
    convert ENNReal.continuous_coe.continuousAt.tendsto.comp (h a)
    simp only [Function.comp_apply, ne_eq, ennreal_coeFn_eq_coeFn_toMeasure, coe_toNNReal]
    simp only [ne_eq, ennreal_coeFn_eq_coeFn_toMeasure]

-- To Mathlib
instance {α : Type*} [Fintype α] [TopologicalSpace α] : SecondCountableTopology α where
  is_open_generated_countable := by
    use {U | IsOpen U}
    exact ⟨to_countable {U | IsOpen U}, TopologicalSpace.isTopologicalBasis_opens.eq_generateFrom⟩

/-- Probability measures on a finite space tend to a limit if and only if the probability masses
of all points tend to the corresponding limits. -/
lemma ProbabilityMeasure.tendsto_prod_of_tendsto_of_tendsto
    {ι : Type*} {L : Filter ι} [NeBot L] {α β : Type*}
    [Fintype α] [TopologicalSpace α] [DiscreteTopology α] [MeasurableSpace α] [BorelSpace α]
    [Fintype β] [TopologicalSpace β] [DiscreteTopology β] [MeasurableSpace β] [BorelSpace β]
    (μs : ι → ProbabilityMeasure α) (μ : ProbabilityMeasure α) (μs_lim : Tendsto μs L (𝓝 μ))
    (νs : ι → ProbabilityMeasure β) (ν : ProbabilityMeasure β) (νs_lim : Tendsto νs L (𝓝 ν)) :
    Tendsto (fun i ↦ (μs i).prod (νs i)) L (𝓝 (μ.prod ν)) := by
  apply (ProbabilityMeasure.tendsto_iff_forall_apply_tendsto _ _).mpr
  intro ab
  have aux : {ab} = {ab.1} ×ˢ {ab.2} := toFinset_inj.mp rfl
  simp_rw [aux, prod_prod]
  have obs_μs := ((continuous_pmf_apply ab.1).continuousAt (x := μ)).tendsto.comp μs_lim
  have obs_νs := ((continuous_pmf_apply ab.2).continuousAt (x := ν)).tendsto.comp νs_lim
  exact tendsto_mul.comp (Tendsto.prod_mk_nhds obs_μs obs_νs)

end MeasureTheory -- namespace
