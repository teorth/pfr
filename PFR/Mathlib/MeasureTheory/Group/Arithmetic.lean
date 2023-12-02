import Mathlib.MeasureTheory.Group.Arithmetic
import PFR.Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory

variable {M : Type*} [MeasurableSpace M] [Mul M] [Div M] [Inv M]

@[to_additive] -- See note [lower instance priority]
instance DiscreteMeasurableSpace.toMeasurableMul [DiscreteMeasurableSpace M] :
    MeasurableMul M where
  measurable_const_mul _ := measurable_discrete _
  measurable_mul_const _ := measurable_discrete _

@[to_additive DiscreteMeasurableSpace.toMeasurableAdd₂] -- See note [lower instance priority]
instance DiscreteMeasurableSpace.toMeasurableMul₂ [DiscreteMeasurableSpace (M × M)] :
    MeasurableMul₂ M := ⟨measurable_discrete _⟩

@[to_additive] -- See note [lower instance priority]
instance DiscreteMeasurableSpace.toMeasurableInv [DiscreteMeasurableSpace M] :
    MeasurableInv M := ⟨measurable_discrete _⟩

@[to_additive] -- See note [lower instance priority]
instance DiscreteMeasurableSpace.toMeasurableDiv [DiscreteMeasurableSpace M] :
    MeasurableDiv M where
  measurable_const_div _ := measurable_discrete _
  measurable_div_const _ := measurable_discrete _

@[to_additive DiscreteMeasurableSpace.toMeasurableSub₂] -- See note [lower instance priority]
instance DiscreteMeasurableSpace.toMeasurableDiv₂ [DiscreteMeasurableSpace (M × M)] :
    MeasurableDiv₂ M := ⟨measurable_discrete _⟩
