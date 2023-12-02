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

end ProbabilityTheory
