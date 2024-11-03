import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace MeasureTheory
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [MeasurableSingletonClass α]

lemma IntegrableOn.finset {μ : Measure α} [IsFiniteMeasure μ] {s : Finset α} {f : α → E} :
    IntegrableOn f s μ := by
  rw [← s.toSet.biUnion_of_singleton]
  simp [integrableOn_finset_iUnion, measure_lt_top]

end MeasureTheory
