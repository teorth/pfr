import Mathlib.MeasureTheory.MeasurableSpace.Basic

instance Quotient.instDiscreteMeasurableSpace {α} {s : Setoid α} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] : DiscreteMeasurableSpace (Quotient s) where
  forall_measurableSet _ := measurableSet_quotient.2 .of_discrete

@[to_additive]
instance QuotientGroup.instDiscreteMeasurableSpace {G} [Group G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G] (S : Subgroup G) : DiscreteMeasurableSpace (G ⧸ S) :=
  Quotient.instDiscreteMeasurableSpace
