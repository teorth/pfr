import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import PFR.ForMathlib.Pair


/-- The property of having a finite range. -/
class FiniteRange {Ω G : Type*} (X : Ω → G) : Prop where
  finite : (Set.range X).Finite

/-- fintype structure on the range of a finite range map. -/
noncomputable def FiniteRange.fintype {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] :
    Fintype (Set.range X) := hX.finite.fintype

/-- The range of a finite range map, as a finset. -/
noncomputable def FiniteRange.toFinset {Ω G : Type*} (X : Ω → G) [hX: FiniteRange X] : Finset G :=
    @Set.toFinset _ _ hX.fintype

/-- If the codomain of X is finite, then X has finite range.  -/
instance {Ω G : Type*} (X : Ω → G) [Fintype G] : FiniteRange X where
  finite := Set.toFinite (Set.range X)

example {Ω G : Type*} (X : Ω → G) [Fintype G] : FiniteRange X := by infer_instance

/-- Functions ranging in a Finset have finite range -/
lemma finiteRange_of_finset {Ω G : Type*} (f: Ω → G) (A : Finset G) (h : ∀ ω, f ω ∈ A) :
    FiniteRange f := by
  constructor
  apply Set.Finite.subset (Finset.finite_toSet A)
  intro y hy
  simp only [Set.mem_range] at hy
  rcases hy with ⟨ω, rfl⟩
  exact h ω

lemma FiniteRange.range {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] :
    Set.range X = FiniteRange.toFinset X := by
  simp [FiniteRange.toFinset]

lemma FiniteRange.mem {Ω G : Type*} (X : Ω → G) [FiniteRange X] (ω : Ω) :
    X ω ∈ FiniteRange.toFinset X := by
  rw [← Finset.mem_coe, ← FiniteRange.range X]
  simp

@[simp]
lemma FiniteRange.mem_iff {Ω G : Type*} (X : Ω → G) [FiniteRange X] (x : G) :
    x ∈ FiniteRange.toFinset X ↔ ∃ ω, X ω = x := by
  rw [← Finset.mem_coe, ← FiniteRange.range X]
  simp

/-- Constants have finite range -/
instance {Ω G : Type*} (c : G) : FiniteRange (fun _ : Ω ↦ c) := by
  apply finiteRange_of_finset _ { c }
  simp

/-- If X has finite range, then any function of X has finite range.  -/
instance {Ω G H : Type*} (X : Ω → G) (f : G → H) [hX: FiniteRange X] : FiniteRange (f ∘ X) where
  finite := by
    rw [Set.range_comp f X]
    exact Set.Finite.image f hX.finite

/-- If X has finite range, then X of any function has finite range.  -/
instance {Ω Ω' G : Type*} (X : Ω → G) (f : Ω' → Ω) [hX: FiniteRange X] : FiniteRange (X ∘ f) := by
  apply finiteRange_of_finset _ (FiniteRange.toFinset X)
  intro ω
  exact FiniteRange.mem X (f ω)

/-- If X, Y have finite range, then so does the pair ⟨X, Y⟩. -/
instance {Ω G H : Type*} (X : Ω → G) (Y : Ω → H) [hX: FiniteRange X] [hY: FiniteRange Y] :
    FiniteRange (⟨X, Y⟩) where
  finite := by
    have : Set.range (⟨X, Y⟩) ⊆ (Set.range X) ×ˢ (Set.range Y) := by
      intro ⟨x, y⟩ hz
      simp only [Set.mem_range, Prod.mk.injEq, Set.mem_prod] at hz ⊢
      rcases hz with ⟨ω, hω⟩
      exact ⟨⟨ω, hω.1⟩, ω, hω.2⟩
    exact Set.Finite.subset (Set.Finite.prod hX.finite hY.finite) this

/-- The product of functions of finite range, has finite range.   -/
@[to_additive "The sum of functions of finite range, has finite range."]
instance FiniteRange.prod {Ω G : Type*} (X : Ω → G) (Y : Ω → G) [Group G]
    [hX: FiniteRange X] [hY: FiniteRange Y] : FiniteRange (X*Y) := by
  show FiniteRange ((fun p ↦ p.1 * p.2) ∘ ⟨X, Y⟩)
  infer_instance

/-- The quotient of two functions with finite range, has finite range. -/
@[to_additive "The difference of functions of finite range, has finite range."]
instance FiniteRange.div {Ω G : Type*} (X : Ω → G) (Y : Ω → G) [Group G]
    [hX: FiniteRange X] [hY: FiniteRange Y] : FiniteRange (X/Y) := by
  show FiniteRange ((fun p ↦ p.1 / p.2) ∘ ⟨X, Y⟩)
  infer_instance

/-- The inverse of a function of finite range, has finite range.-/
@[to_additive "The negation of a function of finite range, has finite range."]
instance FiniteRange.inv {Ω G : Type*} (X : Ω → G) [Group G] [hX: FiniteRange X] :
    FiniteRange X⁻¹ := by
  show FiniteRange ((fun p ↦ p⁻¹) ∘ X)
  infer_instance

/-- A function of finite range raised to a constant power, has finite range.  -/
@[to_additive "The multiple of a function of finite range by a constant, has finite range."]
instance FiniteRange.pow {Ω G : Type*} (X : Ω → G) [Group G] [hX: FiniteRange X] (c : ℤ) :
    FiniteRange (X^c) := by
  show FiniteRange ((fun x ↦ x^c) ∘ X)
  infer_instance


open MeasureTheory

lemma FiniteRange.full {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] {X : Ω → G} (hX: Measurable X) [FiniteRange X] (μ: Measure Ω) :
    (μ.map X) (FiniteRange.toFinset X) = μ Set.univ := by
  rw [Measure.map_apply hX]
  congr
  ext ω; simp
  measurability

lemma FiniteRange.null_of_compl {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : Measure Ω) (X : Ω → G) [FiniteRange X] :
    (μ.map X) (FiniteRange.toFinset X : Set G)ᶜ = 0 := by
  by_cases hX : AEMeasurable X μ
  · rw [Measure.map_apply₀ hX]
    convert measure_empty
    ext ω
    simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Finset.mem_coe, mem_iff,
      exists_apply_eq_apply, not_true_eq_false, Set.mem_empty_iff_false]
    simp only [NullMeasurableSet.compl_iff]
    refine MeasurableSet.nullMeasurableSet ?_
    measurability
  · simp [hX]
