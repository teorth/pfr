import Mathlib


-- some code experimenting with using a dependent type setting for conditional measure in which the conditioned space has its universal set restricted to the event.  Ultimately abandoned.

open MeasureTheory


attribute [coe] Lean.Internal.coeM

/-- A technical lemma to compare the internal Lean set coercion with what Subtype.val produces.  Thanks to Patrick Massot for code. --/
lemma set_coerce {X : Type*} {E : Set X} {F : Set E} : (Subtype.val '' F) = (F : Set X) := by
  dsimp [Lean.Internal.coeM]
  ext x
  simp only [Set.iUnion_coe_set, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
  constructor
  · rintro ⟨a, ha, rfl⟩
    use a, a.property, ha
    rfl
  · rintro ⟨_, xE, xF, rfl⟩
    use ⟨x, xE⟩

/-- The restricted measure on a subset agrees with the original measure. -/
lemma measure_restrict {X : Type*} [hX: MeasureTheory.MeasureSpace X] {E : Set X} (hE: MeasurableSet E) {F : Set E} (hF : MeasurableSet
F) : MeasureTheory.MeasureSpace.volume F = MeasureTheory.MeasureSpace.volume (F : Set X) := by
  rw [← set_coerce]
  dsimp [SetCoe.measureSpace]
  rw [MeasureTheory.Measure.comap_apply]
  . exact Subtype.val_injective
  . intro s hs
    exact MeasurableSet.subtype_image hE hs
  exact hF
