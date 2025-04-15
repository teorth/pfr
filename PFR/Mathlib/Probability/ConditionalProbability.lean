import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ConditionalProbability

open MeasureTheory

variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}

namespace ProbabilityTheory

/-- The axiomatic definition of conditional probability derived from a measure-theoretic one. -/
lemma cond_real_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[|s].real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  simp [Measure.real, cond_apply hms]

end ProbabilityTheory
