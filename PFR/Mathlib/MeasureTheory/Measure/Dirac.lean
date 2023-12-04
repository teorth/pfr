import Mathlib.MeasureTheory.Measure.Dirac

namespace MeasureTheory.Measure
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure α}
  {p : α → Prop}

lemma ae_iff_of_fintype : (∀ᵐ x ∂μ, p x) ↔ ∀ x, μ {x} ≠ 0 → p x := by
  rw [ae_iff]
  conv_lhs => rw [← Measure.sum_smul_dirac μ]
  simp [or_iff_not_imp_left, imp_false]
