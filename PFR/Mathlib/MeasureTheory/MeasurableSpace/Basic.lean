import Mathlib.MeasureTheory.MeasurableSpace.Basic

namespace MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

instance _root_.ULift.instMeasurableSpace : MeasurableSpace (ULift Ω) :=
  ‹MeasurableSpace Ω›.map ULift.up

lemma measurable_down : Measurable (ULift.down : ULift Ω → Ω) := fun _ ↦ id
lemma measurable_up : Measurable (ULift.up : Ω → ULift Ω) := fun _ ↦ id

end MeasureTheory

section
variable {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → Prop}

lemma Measurable.and (hf : Measurable f) (hg : Measurable g) : Measurable (fun ω ↦ f ω ∧ g ω) :=
  measurableSet_setOf.1 $ hf.setOf.inter hg.setOf

lemma Measurable.or (hf : Measurable f) (hg : Measurable g) : Measurable (fun ω ↦ f ω ∨ g ω) :=
  measurableSet_setOf.1 $ hf.setOf.union hg.setOf

-- TODO: Other logic operators

end
