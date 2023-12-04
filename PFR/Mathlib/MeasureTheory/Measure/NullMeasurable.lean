import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

open scoped BigOperators

namespace MeasureTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β]

lemma measure_preimage_fst_singleton_eq_sum [Fintype β] (μ : Measure (α × β)) (x : α) :
    μ (Prod.fst ⁻¹' {x}) = ∑ y, μ {(x, y)} := by
  have : Prod.fst ⁻¹' {x} = ⋃ y : β, {(x, y)} := by ext y; simp [Prod.ext_iff, eq_comm]
  rw [this, measure_iUnion, tsum_eq_sum] <;> simp [Pairwise]

lemma measure_preimage_snd_singleton_eq_sum [Fintype α] (μ : Measure (α × β)) (y : β) :
    μ (Prod.snd ⁻¹' {y}) = ∑ x, μ {(x, y)} := by
  have : Prod.snd ⁻¹' {y} = ⋃ x : α, {(x, y)} := by ext y; simp [Prod.ext_iff, eq_comm]
  rw [this, measure_iUnion, tsum_eq_sum] <;> simp [Pairwise]

end MeasureTheory
