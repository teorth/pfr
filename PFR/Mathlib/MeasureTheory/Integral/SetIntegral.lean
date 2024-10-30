import Mathlib.MeasureTheory.Integral.SetIntegral

open scoped ENNReal

namespace MeasureTheory
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma integral_eq_setIntegral {μ : Measure α} {s : Set α} (hs : μ sᶜ = 0) (f : α → E) :
    ∫ x, f x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← setIntegral_univ, ← setIntegral_congr_set]; rwa [ae_eq_univ]

end MeasureTheory
