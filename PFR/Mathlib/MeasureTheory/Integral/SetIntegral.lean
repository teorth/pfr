import Mathlib.MeasureTheory.Integral.SetIntegral
import PFR.Mathlib.MeasureTheory.Integral.Bochner

open scoped BigOperators ENNReal

namespace MeasureTheory
variable {α E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

lemma setIntegral_eq_sum (μ : Measure α) [IsFiniteMeasure μ] (s : Finset α) (f : α → E) :
    ∫ x in s, f x ∂μ = ∑ x in s, (μ {x}).toReal • f x := by
  refine integral_finset _ _ $ IntegrableOn.integrable ?_
  observe : s = ⋃ x ∈ s, {x}
  simp [this, integrableOn_finset_iUnion, measure_lt_top]

lemma integral_eq_sum' (μ : Measure α) [IsFiniteMeasure μ] {s : Finset α} (hs : μ sᶜ = 0)
    (f : α → E) : ∫ x, f x ∂μ = ∑ x in s, (μ {x}).toReal • f x := by
  have hA' : (s : Set α) =ᵐ[μ] Set.univ := by rwa [MeasureTheory.ae_eq_univ]
  rw [← integral_univ, ← setIntegral_congr_set_ae hA']
  exact setIntegral_eq_sum μ s f

end MeasureTheory
