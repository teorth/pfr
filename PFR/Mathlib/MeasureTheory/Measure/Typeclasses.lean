import Mathlib.MeasureTheory.Measure.Typeclasses

namespace MeasureTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
  [MeasurableSingletonClass β]

instance IsFiniteMeasure_comap_equiv {μ : Measure α} (f : β ≃ᵐ α) [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.comap f) := by
  constructor
  rw [Measure.comap_apply f (MeasurableEquiv.injective f) _ μ MeasurableSet.univ]
  . exact measure_lt_top μ (⇑f '' Set.univ)
  · exact fun _ ↦ (MeasurableEquiv.measurableSet_image f).mpr
