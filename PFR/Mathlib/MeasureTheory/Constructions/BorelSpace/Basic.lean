import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

instance DiscreteMeasurableSpace.toBorelSpace {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] : BorelSpace α := by
  constructor; ext; simp [MeasurableSpace.measurableSet_generateFrom, measurableSet_discrete]
