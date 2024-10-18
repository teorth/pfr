import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace MeasureTheory.Measure
variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

lemma comap_swap (μ : Measure (α × β)) : μ.comap Prod.swap = μ.map Prod.swap :=
  (MeasurableEquiv.prodComm ..).comap_symm
