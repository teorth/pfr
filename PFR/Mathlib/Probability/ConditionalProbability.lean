import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import PFR.Mathlib.MeasureTheory.Measure.MeasureSpace

open ENNReal MeasureTheory MeasurableSpace Measure

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

end ProbabilityTheory
