import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Basic
import PFR.ForMathlib.Pair


/-- The property of having a finite range. -/
class FiniteRange {Ω G : Type*} (X : Ω → G) : Prop where
  finite : (Set.range X).Finite

noncomputable def FiniteRange.fintype {Ω G : Type*} (X : Ω → G) [hX: FiniteRange X] : Fintype (Set.range X) := hX.finite.fintype

noncomputable def FiniteRange.toFinset {Ω G : Type*} (X : Ω → G) [hX: FiniteRange X] : Finset G := @Set.toFinset _ _ hX.fintype

/-- If the codomain of X is finite, then X has finite range.  -/
instance {Ω G : Type*} (X : Ω → G) [Fintype G] : FiniteRange X where
  finite := Set.toFinite (Set.range X)

example {Ω G : Type*} (X : Ω → G) [Fintype G] : FiniteRange X := by infer_instance

/-- If X has finite range, then any function of X has finite range.  -/
instance {Ω G H : Type*} (X : Ω → G) (f : G → H) [hX: FiniteRange X] : FiniteRange (f ∘ X) where
  finite := by
    rw [Set.range_comp f X]
    exact Set.Finite.image f hX.finite

/-- If X, Y have finite range, then so does the pair ⟨ X, Y ⟩. -/
instance {Ω G H : Type*} (X : Ω → G) (Y : Ω → H) [hX: FiniteRange X] [hY: FiniteRange Y]: FiniteRange (⟨ X, Y ⟩) where
  finite := by
    have : Set.range (⟨ X, Y⟩) ⊆ (Set.range X) ×ˢ (Set.range Y) := by
      intro ⟨ x, y ⟩ hz
      simp [Set.mem_range] at hz ⊢
      rcases hz with ⟨ω, hω⟩
      exact ⟨ ⟨ ω, hω.1 ⟩, ⟨ ω, hω.2 ⟩ ⟩
    exact Set.Finite.subset (Set.Finite.prod hX.finite hY.finite) this

/-- The sum of two functions with finite range, has finite range. -/
instance {Ω G : Type*} (X : Ω → G) (Y : Ω → G) [AddGroup G] [hX: FiniteRange X] [hY: FiniteRange Y] : FiniteRange (X+Y) := by
  show FiniteRange ((fun p ↦ p.1 + p.2) ∘ ⟨ X, Y ⟩)
  infer_instance

/-- The difference of two functions with finite range, has finite range. -/
instance {Ω G : Type*} (X : Ω → G) (Y : Ω → G) [AddGroup G] [hX: FiniteRange X] [hY: FiniteRange Y] : FiniteRange (X-Y) := by
  show FiniteRange ((fun p ↦ p.1 - p.2) ∘ ⟨ X, Y ⟩)
  infer_instance

/-- The multiple of a function of finite range by a constant, has finite range. -/
instance {Ω G : Type*} (X : Ω → G) [AddGroup G] [hX: FiniteRange X] (c : ℤ) : FiniteRange (c • X) := by
  show FiniteRange ((fun x ↦ c • x) ∘ X)
  infer_instance
