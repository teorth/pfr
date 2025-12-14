import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open Set

namespace MeasureTheory
variable {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] {μ : Measure Ω} {s : Set Ω}

lemma measure_eq_univ_of_forall_singleton (hμ : ∀ x ∈ sᶜ, μ {x} = 0) : μ s = μ .univ := by
  apply le_antisymm (measure_mono (subset_univ _))
  rw [← Set.union_compl_self s]
  apply (measure_union_le _ _).trans
  have : μ sᶜ = 0 := (measure_null_iff_singleton (Set.to_countable _)).2 fun i ↦ hμ _
  simp [this]

end MeasureTheory
