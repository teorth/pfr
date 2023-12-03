import Mathlib.MeasureTheory.MeasurableSpace.Basic

namespace MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

instance _root_.ULift.instMeasurableSpace : MeasurableSpace (ULift Ω) :=
  ‹MeasurableSpace Ω›.map ULift.up

lemma measurable_down : Measurable (ULift.down : ULift Ω → Ω) := fun _ ↦ id
lemma measurable_up : Measurable (ULift.up : Ω → ULift Ω) := fun _ ↦ id

end MeasureTheory
