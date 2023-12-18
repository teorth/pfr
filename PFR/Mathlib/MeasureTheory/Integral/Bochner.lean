import Mathlib.MeasureTheory.Integral.Bochner

open scoped BigOperators ENNReal

namespace MeasureTheory
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

-- TODO: Replace `integral_fintype`?
lemma integral_eq_sum (μ : Measure α) [IsFiniteMeasure μ] [MeasurableSingletonClass α] [Fintype α]
    (f : α → E) : ∫ x, f x ∂μ = ∑ x, (μ {x}).toReal • f x :=
  integral_fintype _ $ integrable_of_fintype _ _

end MeasureTheory
