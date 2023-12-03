import Mathlib.Topology.Separation
import PFR.Mathlib.Topology.ContinuousOn

open Set

section
variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [One β] {f : α → β}

@[to_additive]
lemma continuous_mulIndicator_singleton [T1Space α] (ha : IsOpen {a}) :
    Continuous (mulIndicator {a} f) :=
  continuous_mulIndicator (by simp [IsClopen.frontier_eq ⟨ha, isClosed_singleton⟩]) $ by simp

end
