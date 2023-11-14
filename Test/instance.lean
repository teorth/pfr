import Mathlib.Probability.StrongLaw
import Mathlib.Probability.ConditionalProbability

attribute [-instance] MeasureTheory.Measure.Subtype.measureSpace

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal
open MeasureTheory

noncomputable section

def Subtype.probSpace {α : Type*} [MeasureSpace α] {E : Set α} : MeasureSpace E :=
  { volume := Measure.comap Subtype.val (ProbabilityTheory.cond ℙ E : Measure α) }

attribute [local instance] Subtype.probSpace

variable {Ω : Type*} [MeasureSpace Ω]

instance {E : Set Ω} : IsFiniteMeasure (ℙ : Measure E) := sorry

instance {E : Set Ω} [IsFiniteMeasure (ℙ : Measure Ω)] [Fact (0 < ℙ E)] :
  IsProbabilityMeasure (ℙ : Measure E) := sorry

lemma foo (f : Ω → ℝ) (hf : Integrable f) (E : Set Ω) :
  Integrable (fun (x : E) ↦ f x : E → ℝ) := sorry

variable [IsProbabilityMeasure (ℙ : Measure Ω)]
