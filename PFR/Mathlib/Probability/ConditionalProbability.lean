import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import PFR.Mathlib.MeasureTheory.Measure.MeasureSpace

open ENNReal MeasureTheory MeasurableSpace Measure
open scoped BigOperators

variable {Ω α β γ : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {s t : Set Ω}

namespace ProbabilityTheory

@[inherit_doc cond] -- TODO: Also tag the two existing notations
scoped notation:60 μ "[|" T " ← " t "]" => μ[|T ⁻¹' {t}]

lemma cond_absolutelyContinuous : μ[|s] ≪ μ :=
  smul_absolutelyContinuous.trans restrict_le_self.absolutelyContinuous

/-- `μ[|s]` is always a finite measure. -/
instance cond_isFiniteMeasure : IsFiniteMeasure (μ[|s]) := by
  constructor
  simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, MeasurableSet.univ,
    Measure.restrict_apply, Set.univ_inter, smul_eq_mul, ProbabilityTheory.cond,
    ← ENNReal.div_eq_inv_mul]
  exact ENNReal.div_self_le_one.trans_lt ENNReal.one_lt_top

lemma cond_eq_zero_of_measure_eq_zero (hμs : μ s = 0) : μ[|s] = 0 := by
  simp [cond, restrict_eq_zero.2 hμs]

@[simp] lemma cond_eq_zero (hμs : μ s ≠ ⊤) : μ[|s] = 0 ↔ μ s = 0 := by simp [cond, hμs]

variable [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

/-- The law of total probability : a measure $\mu$ can be expressed as a mixture of its conditional measures $\mu[|Y^{-1}\{y\}]$ from a finitely valued random variable $Y$.-/
lemma law_of_total_probability {Y : Ω → T}
    (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] :
    μ = ∑ y, μ (Y ⁻¹' {y}) • (μ[|Y ← y]) := by
  apply Measure.ext
  intro E hE
  simp only [Measure.coe_finset_sum, smul_toOuterMeasure, OuterMeasure.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  have : μ E = ∑ y : T, μ (Y ⁻¹' {y} ∩ E) := by
    have : E = ⋃ y ∈ Set.univ, Y ⁻¹' {y} ∩ E := by
      simp; ext _; simp
    nth_rewrite 1 [this]
    convert measure_biUnion_finset _ _
    . simp
    · intro _ _ _ _ hyz
      apply Disjoint.inf_left
      apply Disjoint.inf_right
      apply Disjoint.preimage
      simp [hyz]
    intro b _
    exact MeasurableSet.inter (hY (MeasurableSet.singleton b)) hE
  rw [this]
  congr with y
  rcases eq_or_ne (μ (Y ⁻¹' {y})) 0 with hy | hy
  . simp [hy]
    exact measure_inter_null_of_null_left E hy
  symm
  rw [mul_comm, cond_mul_eq_inter _ (hY (MeasurableSet.singleton y)) hy]

end ProbabilityTheory
