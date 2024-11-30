import Mathlib.Probability.ConditionalProbability

open MeasureTheory Measure

namespace ProbabilityTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

lemma ae_cond_mem {s : Set Ω} (hs : MeasurableSet s) : ∀ᵐ x ∂μ[|s], x ∈ s :=
  ae_smul_measure (ae_restrict_mem hs) _

end ProbabilityTheory
