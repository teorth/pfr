import Mathlib.MeasureTheory.Measure.Dirac

namespace MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α] {a : α}

instance dirac.instIsFiniteMeasure : IsFiniteMeasure (dirac a) := inferInstance
instance dirac.instSigmaFinite : SigmaFinite (dirac a) := inferInstance

end MeasureTheory.Measure

namespace MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure α}
  {p : α → Prop}

lemma ae_iff_of_countable [Countable α] : (∀ᵐ x ∂μ, p x) ↔ ∀ x, μ {x} ≠ 0 → p x := by
  rw [ae_iff]
  conv_lhs => rw [← Measure.sum_smul_dirac μ]
  rw [Measure.sum_apply_of_countable, tsum_eq_zero_iff ENNReal.summable]
  simp [or_iff_not_imp_left, imp_false]

lemma ae_iff_of_fintype [Fintype α] : (∀ᵐ x ∂μ, p x) ↔ ∀ x, μ {x} ≠ 0 → p x := ae_iff_of_countable
