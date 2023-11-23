import Mathlib.Probability.IdentDistrib

/- To move close to Set.Finite.measurableSet-/
lemma Set.Finite.MeasurableSet
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {s : Set α} (hs : s.Finite) :
    MeasurableSet s :=
  hs.countable.measurableSet

/- To move close to Set.Finite.measurableSet-/
lemma measurableSet_of_countable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (s : Set α) : MeasurableSet s :=
  s.to_countable.measurableSet

section

open Set

lemma Nat.card_eq_finset_card {α : Type*} {s : Finset α} : Nat.card s = s.card := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

lemma Nat.card_eq_toFinset_card {α : Type*} {s : Set α} (hs : s.Finite) :
    Nat.card s = hs.toFinset.card := by
  simp only [← Nat.card_eq_finset_card, Finite.mem_toFinset]

end

section

open Set MeasureTheory Measure

lemma measure_preimage_eq_zero_iff_of_countable {Ω : Type*} {S : Type*} [MeasurableSpace Ω]
    {H : Set S} {X : Ω → S} {μ : Measure Ω} (hs : H.Countable) :
    μ (X ⁻¹' H) = 0 ↔ ∀ x ∈ H, μ (X ⁻¹' {x}) = 0 := by
  have : Countable H := countable_coe_iff.mpr hs
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · apply le_antisymm ((measure_mono _).trans h.le) (zero_le _)
    apply preimage_mono
    simp [hx]
  · apply le_antisymm _ (zero_le _)
    calc
    μ (X ⁻¹' H) = μ (⋃ x : H, X ⁻¹' {(x : S)}) := by simp
    _ ≤ ∑' x : H, μ (X ⁻¹' {(x : S)}) := measure_iUnion_le _
    _ = ∑' x : H, 0 := by congr with x; exact h x x.2
    _ = 0 := by simp

end
