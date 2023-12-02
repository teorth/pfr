import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

@[simp, norm_cast]
lemma ProbabilityMeasure.coe_mk (μ : Measure Ω) (hμ) :
    ProbabilityMeasure.toMeasure ⟨μ, hμ⟩ = μ := rfl
