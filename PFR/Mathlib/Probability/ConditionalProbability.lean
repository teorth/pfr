import Mathlib.Probability.ConditionalProbability

open MeasureTheory

variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}

namespace ProbabilityTheory

/-- The axiomatic definition of conditional probability derived from a measure-theoretic one. -/
lemma cond_real_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[|s].real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  simp [Measure.real, cond_apply hms]

/-- The conditional probability measure of any finite measure on any set of positive measure
is a probability measure. -/
theorem cond_isProbabilityMeasure_of_real {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (hcs : μ.real s ≠ 0) :
    IsProbabilityMeasure μ[|s] := by
  apply cond_isProbabilityMeasure_of_finite
  · intro h
    simp [measureReal_def, h] at hcs
  · intro h
    simp [measureReal_def, h] at hcs

end ProbabilityTheory
