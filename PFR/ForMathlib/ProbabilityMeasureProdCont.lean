import PFR.ForMathlib.CompactProb
import PFR.ForMathlib.FiniteMeasureProd

/-!
# Continuity of products of probability measures on finite types
-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

/-- Probability measures on a finite space tend to a limit if and only if the probability masses
of all points tend to the corresponding limits. -/
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
    simp only [Function.comp_apply, ne_eq, ennreal_coeFn_eq_coeFn_toMeasure, coe_toNNReal]
    simp only [ne_eq, ennreal_coeFn_eq_coeFn_toMeasure]

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
  exact tendsto_mul.comp (Tendsto.prod_mk_nhds obs_μs obs_νs)

-- TODO: Prove more generally in Mathlib.
instance t1Space_probabilityMeasure_of_finite {α : Type*}
    [Finite α] [TopologicalSpace α] [DiscreteTopology α] [MeasurableSpace α] [BorelSpace α] :
    T1Space (ProbabilityMeasure α) := by
  cases nonempty_fintype α; exact probabilityMeasureHomeoStdSimplex.symm.t1Space

/-- The product of two probability measures on finite spaces depend continuously on the two
probability measures.
TODO: In Mathlib, this should be done on all separable metrizable spaces. -/
lemma ProbabilityMeasure.continuous_prod_of_finite {α β : Type*}
    [Finite α] [TopologicalSpace α] [DiscreteTopology α] [MeasurableSpace α] [BorelSpace α]
    [Finite β] [TopologicalSpace β] [DiscreteTopology β] [MeasurableSpace β] [BorelSpace β] :
    Continuous (fun (⟨μ, ν⟩ : ProbabilityMeasure α × ProbabilityMeasure β) ↦ (μ.prod ν)) := by
  rw [continuous_iff_continuousAt]
  intro μν
  apply continuousAt_of_tendsto_nhds (y := μν.1.prod μν.2)
  apply ProbabilityMeasure.tendsto_prod_of_tendsto_of_tendsto
  · apply continuous_fst.tendsto
  · apply continuous_snd.tendsto

end MeasureTheory -- namespace
