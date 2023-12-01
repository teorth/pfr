import Mathlib.MeasureTheory.MeasurableSpace.Defs

open Set Function Equiv
open scoped Classical

variable {α β γ δ δ' : Type*} {ι : Sort*} {s t u : Set α}

/-- Typeclass for a measurable space to be discrete, namely ever-/
class DiscreteMeasurableSpace (α : Type*) [MeasurableSpace α] : Prop where
  eq_top : ‹MeasurableSpace α› = ⊤

variable [MeasurableSpace α] [MeasurableSpace β]

section DiscreteMeasurableSpace
variable [DiscreteMeasurableSpace α]

@[simp]
lemma measurableSet_discrete (s : Set α) : MeasurableSet s :=
(DiscreteMeasurableSpace.eq_top (α := α)).symm ▸ trivial

lemma measurable_discrete (f : α → β) : Measurable f := fun _ _ ↦ measurableSet_discrete _

end DiscreteMeasurableSpace

instance [Countable α] [MeasurableSingletonClass α] : DiscreteMeasurableSpace α where
  eq_top := by
    ext s
    simp only [MeasurableSpace.measurableSet_top, iff_true]
    rw [← biUnion_of_singleton s]
    exact MeasurableSet.biUnion s.to_countable (fun _ _ ↦ measurableSet_singleton _)
