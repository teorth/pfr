import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

instance {M : Type*} [Finite M] [MeasurableSpace M] [MeasurableSingletonClass M]
    [TopologicalSpace M] [DiscreteTopology M] : BorelSpace M := by
  have h₁ : ∀ s, @MeasurableSet M inferInstance s :=
    fun s ↦ Set.Countable.measurableSet s.to_countable
  have h₂ : ∀ s, @MeasurableSet M (borel M) s :=
    fun s ↦ MeasurableSpace.measurableSet_generateFrom <| isOpen_discrete s
  exact ⟨by aesop⟩
