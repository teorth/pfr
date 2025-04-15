import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace MeasureTheory
variable {E α : Type*} {_ : MeasurableSpace α}
variable [NormedAddCommGroup E] [hE : CompleteSpace E] [NormedSpace ℝ E] {μ : Measure α}

-- TODO: Replace `integral_finset`
lemma integral_finset' [MeasurableSingletonClass α] (s : Finset α) {f : α → E}
    (hf : IntegrableOn f s μ) : ∫ x in s, f x ∂μ = ∑ x ∈ s, μ.real {x} • f x := by
  simp [integral_countable _ s.countable_toSet hf, ← Finset.tsum_subtype', Measure.real]

-- TODO: Replace `integral_fintype`
theorem integral_fintype' [MeasurableSingletonClass α] [Fintype α] {f : α → E}
    (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x, μ.real {x} • f x := by
  -- NB: Integrable f does not follow from Fintype, because the measure itself could be non-finite
  rw [← integral_finset' .univ, Finset.coe_univ, Measure.restrict_univ]
  simp [Finset.coe_univ, Measure.restrict_univ, hf]

end MeasureTheory
