import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import PFR.Mathlib.MeasureTheory.MeasurableSpace.Defs

instance DiscreteMeasurableSpace.toBorelSpace {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] : BorelSpace α := by
  constructor; ext; simp [MeasurableSpace.measurableSet_generateFrom]
