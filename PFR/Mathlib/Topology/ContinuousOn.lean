import Mathlib.Topology.ContinuousOn
import Mathlib.Algebra.IndicatorFunction --TODO: Cut down the imports of `Algebra.IndicatorFunction`

open Set

attribute [simp] continuousOn_singleton

section
variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [One β] {f : α → β} {s : Set α}

@[to_additive]
lemma continuous_mulIndicator (hs : ∀ a ∈ frontier s, f a = 1) (hf : ContinuousOn f (closure s)) :
     Continuous (mulIndicator s f) := by
  classical exact continuous_piecewise hs hf continuousOn_const

@[to_additive]
protected lemma Continuous.mulIndicator (hs : ∀ a ∈ frontier s, f a = 1) (hf : Continuous f) :
    Continuous (mulIndicator s f) := by
  classical exact hf.piecewise hs continuous_const

end
