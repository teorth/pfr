import Mathlib.MeasureTheory.Measure.Map

/-- The property of having a finite range. -/
class FiniteRange {Ω G : Type*} (X : Ω → G) : Prop where
  finite : (Set.range X).Finite

/-- fintype structure on the range of a finite range map. -/
noncomputable def FiniteRange.fintype {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] :
    Fintype (Set.range X) := hX.finite.fintype

/-- The range of a finite range map, as a finset. -/
noncomputable def FiniteRange.toFinset {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] : Finset G :=
    @Set.toFinset _ _ hX.fintype

/-- If the codomain of X is finite, then X has finite range. -/
instance {Ω G : Type*} (X : Ω → G) [Fintype G] : FiniteRange X where
  finite := Set.toFinite (Set.range X)

example {Ω G : Type*} (X : Ω → G) [Fintype G] : FiniteRange X := by infer_instance

/-- Functions ranging in a Finset have finite range -/
lemma finiteRange_of_finset {Ω G : Type*} (f : Ω → G) (A : Finset G) (h : ∀ ω, f ω ∈ A) :
    FiniteRange f := by
  constructor
  apply Set.Finite.subset (Finset.finite_toSet A)
  intro y hy
  simp only [Set.mem_range] at hy
  rcases hy with ⟨ω, rfl⟩
  exact h ω

lemma FiniteRange.range {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] :
    Set.range X = FiniteRange.toFinset X := by simp [FiniteRange.toFinset]

lemma FiniteRange.mem {Ω G : Type*} (X : Ω → G) [FiniteRange X] (ω : Ω) :
    X ω ∈ FiniteRange.toFinset X := by
  simp_rw [← Finset.mem_coe, ← FiniteRange.range X, Set.mem_range, exists_apply_eq_apply]

@[simp]
lemma FiniteRange.mem_iff {Ω G : Type*} (X : Ω → G) [FiniteRange X] (x : G) :
    x ∈ FiniteRange.toFinset X ↔ ∃ ω, X ω = x := by
  simp_rw [← Finset.mem_coe, ← FiniteRange.range X, Set.mem_range]

/-- Constants have finite range -/
instance {Ω G : Type*} (c : G) : FiniteRange (fun _ : Ω ↦ c) := by
  apply finiteRange_of_finset _ { c }
  simp

/-- If X has finite range, then any function of X has finite range. -/
instance {Ω G H : Type*} (X : Ω → G) (f : G → H) [hX : FiniteRange X] : FiniteRange (f ∘ X) where
  finite := (Set.range_comp f X) ▸ Set.Finite.image f hX.finite

/-- If X has finite range, then X of any function has finite range. -/
instance {Ω Ω' G : Type*} (X : Ω → G) (f : Ω' → Ω) [hX : FiniteRange X] : FiniteRange (X ∘ f) := by
  apply finiteRange_of_finset _ (FiniteRange.toFinset X)
  intro ω
  exact FiniteRange.mem X (f ω)

/-- If X, Y have finite range, then so does the pair ⟨X, Y⟩. -/
instance {Ω G H : Type*} (X : Ω → G) (Y : Ω → H) [hX : FiniteRange X] [hY : FiniteRange Y] :
    FiniteRange fun ω ↦ (X ω, Y ω) where
  finite := (hX.finite.prod hY.finite).subset (Set.range_pair_subset ..)

/-- The product of functions of finite range, has finite range. -/
@[to_additive /-- The sum of functions of finite range, has finite range. -/]
instance FiniteRange.mul {Ω G : Type*} (X Y : Ω → G) [Mul G]
    [hX: FiniteRange X] [hY: FiniteRange Y] : FiniteRange (X * Y) := by
  show FiniteRange ((fun p ↦ p.1 * p.2) ∘ fun ω ↦ (X ω, Y ω))
  infer_instance

/-- The product of functions of finite range, has finite range. -/
@[to_additive /-- The sum of functions of finite range, has finite range. -/]
instance FiniteRange.mul' {Ω G : Type*} (X Y : Ω → G) [Mul G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange fun ω ↦ X ω * Y ω := FiniteRange.mul ..

/-- The quotient of two functions with finite range, has finite range. -/
@[to_additive /-- The difference of functions of finite range, has finite range. -/]
instance FiniteRange.div {Ω G : Type*} (X Y : Ω → G) [Div G]
    [hX : FiniteRange X] [hY : FiniteRange Y] : FiniteRange (X/Y) := by
  show FiniteRange ((fun p ↦ p.1 / p.2) ∘ fun ω ↦ (X ω, Y ω))
  infer_instance

/-- The product of functions of finite range, has finite range. -/
@[to_additive /-- The sum of functions of finite range, has finite range. -/]
instance FiniteRange.div' {Ω G : Type*} (X Y : Ω → G) [Div G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange fun ω ↦ X ω / Y ω := FiniteRange.div ..

/-- The inverse of a function of finite range, has finite range.-/
@[to_additive /-- The negation of a function of finite range, has finite range. -/]
instance FiniteRange.inv {Ω G : Type*} (X : Ω → G) [Inv G] [hX : FiniteRange X] :
    FiniteRange X⁻¹ := by
  show FiniteRange ((fun p ↦ p⁻¹) ∘ X)
  infer_instance

/-- The product of functions of finite range, has finite range. -/
@[to_additive /-- The sum of functions of finite range, has finite range. -/]
instance FiniteRange.inv' {Ω G : Type*} (X : Ω → G) [Inv G] [FiniteRange X] :
    FiniteRange fun ω ↦ (X ω)⁻¹ := FiniteRange.inv _

/-- A function of finite range raised to a constant power, has finite range. -/
@[to_additive /-- The multiple of a function of finite range by a constant, has finite range. -/]
instance FiniteRange.zpow {Ω G : Type*} (X : Ω → G) [Pow G ℤ] [hX : FiniteRange X] (n : ℤ) :
    FiniteRange (X ^ n) := by
  show FiniteRange ((· ^ n) ∘ X)
  infer_instance

/-- A function of finite range raised to a constant power, has finite range. -/
@[to_additive /-- The multiple of a function of finite range by a constant, has finite range. -/]
instance FiniteRange.zpow' {Ω G : Type*} (X : Ω → G) [Pow G ℤ] [FiniteRange X] (n : ℤ) :
    FiniteRange fun ω ↦ X ω ^ n := FiniteRange.zpow ..

/-- The product of a finite number of functions with finite range, has finite range. -/
@[to_additive /-- The sum of a finite number of functions with finite range, has finite range. -/]
instance FiniteRange.finprod {Ω G I : Type*} [CommMonoid G] {s : Finset I} (X : I → Ω → G)
    [∀ i, FiniteRange (X i)] :
    FiniteRange (∏ i ∈ s, X i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    change FiniteRange (fun _ ↦ 1)
    infer_instance
  | @insert k s hk IH =>
    classical
    have h_eq : ∏ j ∈ insert k s, X j = X k * ∏ j ∈ s, X j := Finset.prod_insert hk
    suffices h : FiniteRange (X k * ∏ j ∈ s, X j) from by
      convert h
      exact h_eq
    exact FiniteRange.mul (X k) (∏ j ∈ s, X j)

open MeasureTheory

lemma FiniteRange.full {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] {X : Ω → G} (hX : Measurable X) [FiniteRange X] (μ: Measure Ω) :
    (μ.map X) (FiniteRange.toFinset X) = μ Set.univ := by
  rw [Measure.map_apply hX]
  congr
  ext ω; simp
  measurability

lemma FiniteRange.real_full {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] {X : Ω → G} (hX : Measurable X) [FiniteRange X] (μ: Measure Ω) :
    (μ.map X).real (FiniteRange.toFinset X) = μ.real Set.univ := by
  simp [measureReal_def, FiniteRange.full hX]

lemma FiniteRange.null_of_compl {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : Measure Ω) (X : Ω → G) [FiniteRange X] :
    (μ.map X) (FiniteRange.toFinset X : Set G)ᶜ = 0 := by
  by_cases hX : AEMeasurable X μ
  · rw [Measure.map_apply₀ hX]
    convert measure_empty (μ := μ)
    ext ω
    simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Finset.mem_coe, mem_iff,
      exists_apply_eq_apply, not_true_eq_false, Set.mem_empty_iff_false]
    simp only [NullMeasurableSet.compl_iff]
    refine MeasurableSet.nullMeasurableSet ?_
    measurability
  · simp [hX]
