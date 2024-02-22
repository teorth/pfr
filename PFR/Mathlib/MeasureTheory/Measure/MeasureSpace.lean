import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace MeasureTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β]

lemma full_measure_of_null_compl {μ : Measure α} {A : Finset α} (hA : μ Aᶜ = 0) :
    μ A = μ Set.univ := by
  simpa [hA] using measure_add_measure_compl (μ := μ) (s := A) (by measurability)
