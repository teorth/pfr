import Mathlib.Probability.ConditionalProbability
import PFR.ForMathlib.FiniteRange

/-!
## TODO
Less explicit arguments to `cond_eq_zero_of_meas_eq_zero`
-/

namespace ProbabilityTheory
open MeasureTheory Set

/- [TODO]: `sum_meas_smul_cond_fiber'` should substitute `sum_meas_smul_cond_fiber` in Mathlib once
the definition of `FiniteRange` is in Mathlib.-/
variable {Ω α : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
 [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The **law of total probability** for a random variable taking finitely many values: a measure
`μ` can be expressed as a linear combination of its conditional measures `μ[|X ← x]` on fibers of a
random variable `X` valued in a fintype. -/
lemma sum_meas_smul_cond_fiber' {X : Ω → α} (hX : Measurable X) [finX : FiniteRange X]
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∑ x ∈ finX.toFinset, μ (X ⁻¹' {x}) • μ[|X ← x] = μ := by
  ext E hE
  calc
    _ = ∑ x ∈ finX.toFinset, μ (X ⁻¹' {x} ∩ E) := by
      simp only [Measure.coe_finset_sum, Measure.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_comm (μ _), cond_mul_eq_inter _ (hX (.singleton _))]
    _ = _ := by
      have : ⋃ x ∈ finX.toFinset, X ⁻¹' {x} ∩ E = E := by ext _; simp
      rw [← measure_biUnion_finset _ fun _ _ ↦ (hX (.singleton _)).inter hE, this]
      aesop (add simp [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_left])

end ProbabilityTheory
