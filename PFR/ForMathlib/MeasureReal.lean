import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Finiteness
import PFR.Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Measures as real valued-functions

Given a measure `μ`, we define `μ.real` as the function sending a set `s` to `(μ s).toReal`, and
develop a basic API around this.

We essentially copy relevant lemmas from the files `MeasureSpaceDef.lean`, `NullMeasurable.lean` and
`MeasureSpace.lean`, and adapt them by replacing in their name `measure` with `measureReal`.

Many lemmas require an assumption that some set has finite measure. These assumptions are written
in the form `(h : μ s ≠ ∞ := by finiteness)`, where `finiteness` is a new tactic (still in prototype
form) for goals of the form `≠ ∞`.

There are certainly many missing lemmas. The idea is to add the missing ones as we notice that they
would be useful while doing the project.

I haven't transferred any lemma involving infinite sums, as summability issues are really
more painful with reals than nonnegative extended reals. I don't expect we will need them in the
project, but we should probably add them back in the long run if they turn out to be useful.
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal symmDiff

variable {ι Ω S : Type*}

section aux_lemmas

@[simp]
lemma Finset.sum_measure_singleton {S : Type*} {s : Finset S} {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] (μ : Measure S) :
    ∑ x in s, μ {x} = μ s := by
  change ∑ x in s, μ (id ⁻¹' {x}) = _
  rw [sum_measure_preimage_singleton]
  · simp
  · simp

@[simp]
lemma Finset.sum_toReal_measure_singleton {S : Type*} {s : Finset S} {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] (μ : Measure S) [IsFiniteMeasure μ] :
    ∑ x in s, (μ {x}).toReal = (μ s).toReal := by
  rw [← ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)]
  simp

-- probably don't need this version but it was stated previously and will need to search for and
-- eliminate any explicit uses
lemma sum_measure_singleton {S : Type*} [Fintype S] {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] (μ : Measure S) :
    ∑ x, μ {x} = μ Set.univ := by
  simp

-- probably don't need this version but it was stated previously and will need to search for and
-- eliminate any explicit uses
lemma sum_toReal_measure_singleton {S : Type*} [Fintype S] {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] (μ : Measure S) [IsFiniteMeasure μ] :
    ∑ x : S, (μ {x}).toReal = (μ Set.univ).toReal := by
  simp

variable [MeasurableSpace Ω]

/-- Variant of `sum_measure_preimage_singleton` using real numbers rather than extended nonnegative
reals. -/
lemma sum_measure_preimage_singleton' (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Type*}
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] {Y : Ω → T} (hY : Measurable Y) :
    ∑ y : T, (μ (Y ⁻¹' {y})).toReal = 1 := by
  rw [← ENNReal.toReal_sum, sum_measure_preimage_singleton] <;>
    simp [hY .of_discrete, measure_ne_top]

end aux_lemmas

namespace MeasureTheory

variable {α : Type*} {β : Type*} {_ : MeasurableSpace α} [MeasurableSpace β] (μ : Measure α)

/-- The real-valued version of a measure. Maps infinite measure sets to zero. Use as `μ.real s`. -/
protected def Measure.real (s : Set α) : ℝ := (μ s).toReal

theorem measureReal_def (s : Set α) : μ.real s = (μ s).toReal := rfl

variable {μ}
variable {s s₁ s₂ t : Set α}

section move_to_MeasureSpace.lean

theorem measure_ne_top_of_subset (h : s ⊆ t) (ht : μ t ≠ ∞) : μ s ≠ ∞ :=
  (measure_lt_top_of_subset h ht).ne

theorem measure_diff_eq_top (hs : μ s = ∞) (ht : μ t ≠ ∞) : μ (s \ t) = ∞ := by
  contrapose! hs
  apply ((measure_mono (subset_diff_union s t)).trans_lt _).ne
  apply (measure_union_le _ _).trans_lt
  exact ENNReal.add_lt_top.2 ⟨hs.lt_top, ht.lt_top⟩

theorem measure_symmDiff_eq_top (hs : μ s ≠ ∞) (ht : μ t = ∞) : μ (s ∆ t) = ∞ :=
  measure_mono_top subset_union_right (measure_diff_eq_top ht hs)

end move_to_MeasureSpace.lean

theorem measureReal_eq_zero_iff (h : μ s ≠ ∞ := by finiteness) :
    μ.real s = 0 ↔ μ s = 0 := by
  rw [Measure.real, ENNReal.toReal_eq_zero_iff]
  simp [h]

@[simp] theorem measureReal_zero (s : Set α) : (0 : Measure α).real s = 0 := by
  simp [measureReal_def]

@[simp] theorem measureReal_nonneg : 0 ≤ μ.real s := ENNReal.toReal_nonneg

@[simp] theorem measureReal_empty : μ.real ∅ = 0 :=
  by simp [Measure.real]

@[simp] theorem IsProbabilityMeasure.measureReal_univ [IsProbabilityMeasure μ] :
    μ.real Set.univ = 1 := by
  simp [Measure.real]

theorem measureReal_univ_pos [IsFiniteMeasure μ] [NeZero μ] : 0 < μ.real Set.univ := by
  rw [measureReal_def]
  apply ENNReal.toReal_pos
  exact NeZero.ne (μ Set.univ)
  finiteness

theorem measureReal_univ_ne_zero [IsFiniteMeasure μ] [NeZero μ] : μ.real Set.univ ≠ 0 :=
  measureReal_univ_pos.ne'

theorem nonempty_of_measureReal_ne_zero (h : μ.real s ≠ 0) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h' => h <| h'.symm ▸ measureReal_empty

@[simp] theorem measureReal_smul_apply (c : ℝ≥0∞) : (c • μ).real s = c.toReal • μ.real s := by
  rw [measureReal_def, smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rfl

theorem map_measureReal_apply {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    (μ.map f).real s = μ.real (f ⁻¹' s) := by
  rw [measureReal_def, map_apply hf hs]
  rfl

@[gcongr] theorem measureReal_mono (h : s₁ ⊆ s₂) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ ≤ μ.real s₂ :=
  ENNReal.toReal_mono h₂ (measure_mono h)

theorem measureReal_mono_null (h : s₁ ⊆ s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ = 0 := by
  rw [measureReal_eq_zero_iff h'₂] at h₂
  simp [Measure.real, measure_mono_null h h₂]

theorem measureReal_le_measureReal_union_left (h : μ t ≠ ∞ := by finiteness) :
    μ.real s ≤ μ.real (s ∪ t) := by
  rcases eq_top_or_lt_top (μ s) with hs|hs
  · simp [Measure.real, hs]
  · exact measureReal_mono subset_union_left (measure_union_lt_top hs h.lt_top).ne

theorem measureReal_le_measureReal_union_right (h : μ s ≠ ∞ := by finiteness) :
    μ.real t ≤ μ.real (s ∪ t) := by
  rw [union_comm]
  exact measureReal_le_measureReal_union_left h

theorem measureReal_union_le (s₁ s₂ : Set α) : μ.real (s₁ ∪ s₂) ≤ μ.real s₁ + μ.real s₂ := by
  rcases eq_top_or_lt_top (μ (s₁ ∪ s₂)) with h|h
  · simp only [Measure.real, h, ENNReal.top_toReal]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · have A : μ s₁ ≠ ∞ := measure_ne_top_of_subset subset_union_left h.ne
    have B : μ s₂ ≠ ∞ := measure_ne_top_of_subset subset_union_right h.ne
    simp only [Measure.real, ← ENNReal.toReal_add A B]
    exact ENNReal.toReal_mono (by simp [A, B]) (measure_union_le _ _)

theorem measureReal_biUnion_finset_le {β : Type*} (s : Finset β) (f : β → Set α) :
    μ.real (⋃ b ∈ s, f b) ≤ ∑ p in s, μ.real (f p) := by
  classical
  induction' s using Finset.induction_on with x s hx IH
  · simp
  · simp only [hx, Finset.mem_insert, iUnion_iUnion_eq_or_left, not_false_eq_true,
      Finset.sum_insert]
    exact (measureReal_union_le _ _).trans (by gcongr)

theorem measureReal_iUnion_fintype_le {β : Type*} [Fintype β] (f : β → Set α) :
    μ.real (⋃ b, f b) ≤ ∑ p, μ.real (f p) := by
  convert measureReal_biUnion_finset_le Finset.univ f
  simp

theorem measureReal_iUnion_fintype {β : Type*} [Fintype β] {f : β → Set α}
    (hn : Pairwise (Disjoint on f))
    (h : ∀ i, MeasurableSet (f i)) (h' : ∀ i, μ (f i) ≠ ∞ := by finiteness) :
    μ.real (⋃ b, f b) = ∑ p, μ.real (f p) := by
  rw [measureReal_def, measure_iUnion hn h, tsum_fintype, ENNReal.toReal_sum (fun i _hi ↦ h' i)]
  rfl

theorem measureReal_union_null (h₁ : μ.real s₁ = 0) (h₂ : μ.real s₂ = 0) :
    μ.real (s₁ ∪ s₂) = 0 := by
  apply le_antisymm _ measureReal_nonneg
  exact (measureReal_union_le s₁ s₂).trans (by simp [h₁, h₂])

@[simp]
theorem measureReal_union_null_iff
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = 0 ↔ μ.real s₁ = 0 ∧ μ.real s₂ = 0 := by
  have : μ (s₁ ∪ s₂) ≠ ∞ := measure_union_ne_top h₁ h₂
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => measureReal_union_null h.1 h.2⟩
  · exact measureReal_mono_null subset_union_left h this
  · exact measureReal_mono_null subset_union_right h this

/-- If two sets are equal modulo a set of measure zero, then `μ.real s = μ.real t`. -/
theorem measureReal_congr (H : s =ᵐ[μ] t) : μ.real s = μ.real t := by
  simp [Measure.real, measure_congr H]

theorem measureReal_inter_add_diff₀ (s : Set α) (ht : NullMeasurableSet t μ)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s ∩ t) + μ.real (s \ t) = μ.real s := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_add, measure_inter_add_diff₀ s ht]
  · exact measure_ne_top_of_subset inter_subset_left h
  · exact measure_ne_top_of_subset diff_subset h

theorem measureReal_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
  have : μ (s ∪ t) ≠ ∞ :=
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h₁.lt_top, h₂.lt_top⟩ )).ne
  rw [← measureReal_inter_add_diff₀ (s ∪ t) ht this, Set.union_inter_cancel_right, union_diff_right,
    ← measureReal_inter_add_diff₀ s ht h₁]
  ac_rfl

theorem measureReal_union_add_inter₀' (hs : NullMeasurableSet s μ) (t : Set α)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
  rw [union_comm, inter_comm, measureReal_union_add_inter₀ t hs h₂ h₁, add_comm]

theorem measureReal_union₀ (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) = μ.real s + μ.real t := by
  simp only [Measure.real]
  rw [measure_union₀ ht hd, ENNReal.toReal_add h₁ h₂]

theorem measureReal_union₀' (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) = μ.real s + μ.real t := by
  rw [union_comm, measureReal_union₀ hs (AEDisjoint.symm hd) h₂ h₁, add_comm]

theorem measureReal_add_measureReal_compl₀ [IsFiniteMeasure μ] {s : Set α}
    (hs : NullMeasurableSet s μ) :
    μ.real s + μ.real sᶜ = μ.real univ := by
  rw [← measureReal_union₀' hs aedisjoint_compl_right, union_compl_self]

theorem measureReal_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂)
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = μ.real s₁ + μ.real s₂ :=
  measureReal_union₀ h.nullMeasurableSet hd.aedisjoint h₁ h₂

theorem measureReal_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁)
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = μ.real s₁ + μ.real s₂ :=
  measureReal_union₀' h.nullMeasurableSet hd.aedisjoint h₁ h₂

theorem measureReal_inter_add_diff (s : Set α) (ht : MeasurableSet t)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s ∩ t) + μ.real (s \ t) = μ.real s := by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add, measure_inter_add_diff _ ht]
  · exact measure_ne_top_of_subset inter_subset_left h
  · exact measure_ne_top_of_subset diff_subset h

theorem measureReal_diff_add_inter (s : Set α) (ht : MeasurableSet t)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s \ t) + μ.real (s ∩ t) = μ.real s :=
  (add_comm _ _).trans (measureReal_inter_add_diff s ht h)

theorem measureReal_union_add_inter (s : Set α) (ht : MeasurableSet t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t :=
  measureReal_union_add_inter₀ s ht.nullMeasurableSet h₁ h₂

theorem measureReal_union_add_inter' (hs : MeasurableSet s) (t : Set α)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t :=
  measureReal_union_add_inter₀' hs.nullMeasurableSet t h₁ h₂

lemma measureReal_symmDiff_eq (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∆ t) = μ.real (s \ t) + μ.real (t \ s) := by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add, measure_symmDiff_eq hs ht]
  · exact measure_ne_top_of_subset diff_subset h₁
  · exact measure_ne_top_of_subset diff_subset h₂

lemma measureReal_symmDiff_le (s t u : Set α)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∆ u) ≤ μ.real (s ∆ t) + μ.real (t ∆ u) := by
  rcases eq_top_or_lt_top (μ u) with hu|hu
  · have : μ (s ∆ u) = ∞ := measure_symmDiff_eq_top h₁ hu
    simp only [measureReal_def, this, ENNReal.top_toReal]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · apply le_trans _ (measureReal_union_le (s ∆ t) (t ∆ u))
    apply measureReal_mono (symmDiff_triangle s t u) ?_
    exact measure_union_ne_top (measure_symmDiff_ne_top h₁ h₂) (measure_symmDiff_ne_top h₂ hu.ne)

theorem measureReal_add_measureReal_compl [IsFiniteMeasure μ] (h : MeasurableSet s) :
    μ.real s + μ.real sᶜ = μ.real univ :=
  measureReal_add_measureReal_compl₀ h.nullMeasurableSet

theorem measureReal_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ)
    (h : ∀ b ∈ s, μ (f b) ≠ ∞ := by finiteness) :
    μ.real (⋃ b ∈ s, f b) = ∑ p in s, μ.real (f p) := by
  simp only [measureReal_def, measure_biUnion_finset₀ hd hm, ENNReal.toReal_sum h]

theorem measureReal_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) (h : ∀ b ∈ s, μ (f b) ≠ ∞ := by finiteness) :
    μ.real (⋃ b ∈ s, f b) = ∑ p in s, μ.real (f p) :=
  measureReal_biUnion_finset₀ hd.aedisjoint (fun b hb ↦ (hm b hb).nullMeasurableSet) h

/-- If `s` is a `Finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem sum_measureReal_preimage_singleton {β : Type*} (s : Finset β) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) (h : ∀ a ∈ s, μ (f ⁻¹' {a}) ≠ ∞ := by finiteness) :
    (∑ b in s, μ.real (f ⁻¹' {b})) = μ.real (f ⁻¹' ↑s) := by
  simp only [measureReal_def, ← sum_measure_preimage_singleton s hf, ENNReal.toReal_sum h]

/-- If `s` is a `Finset`, then the sums of the real measures of the singletons in the set is the
real measure of the set. -/
@[simp] theorem Finset.sum_realMeasure_singleton [MeasurableSingletonClass α] [IsFiniteMeasure μ]
    (s : Finset α) :
    (∑ b in s, μ.real {b}) = μ.real s :=
  Finset.sum_toReal_measure_singleton ..

theorem measureReal_diff_null' (h : μ.real (s₁ ∩ s₂) = 0) (h' : μ s₁ ≠ ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ := by
  simp only [measureReal_def]
  rw [measure_diff_null']
  apply (measureReal_eq_zero_iff _).1 h
  exact measure_ne_top_of_subset inter_subset_left h'

theorem measureReal_diff_null (h : μ.real s₂ = 0) (h' : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ := by
  rcases eq_top_or_lt_top (μ s₁) with H|H
  · simp [measureReal_def, H, measure_diff_eq_top H h']
  · exact measureReal_diff_null' (measureReal_mono_null inter_subset_right h h') H.ne

theorem measureReal_add_diff (hs : MeasurableSet s) (t : Set α)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real s + μ.real (t \ s) = μ.real (s ∪ t) := by
  rw [← measureReal_union' (@disjoint_sdiff_right _ s t) hs h₁
    (measure_ne_top_of_subset diff_subset h₂), union_diff_self]

theorem measureReal_diff' (s : Set α) (hm : MeasurableSet t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s \ t) = μ.real (s ∪ t) - μ.real t := by
  rw [union_comm, ← measureReal_add_diff hm s h₂ h₁]
  ring

theorem measureReal_diff (h : s₂ ⊆ s₁) (h₂ : MeasurableSet s₂)
    (h₁ : μ s₁ ≠ ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ - μ.real s₂ := by
  rw [measureReal_diff' _ h₂ h₁ (measure_ne_top_of_subset h h₁), union_eq_self_of_subset_right h]

theorem le_measureReal_diff (h : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ - μ.real s₂ ≤ μ.real (s₁ \ s₂) := by
  simp only [tsub_le_iff_left]
  calc
    μ.real s₁ ≤ μ.real (s₂ ∪ s₁) := measureReal_le_measureReal_union_right h
    _ = μ.real (s₂ ∪ s₁ \ s₂) := congr_arg μ.real union_diff_self.symm
    _ ≤ μ.real s₂ + μ.real (s₁ \ s₂) := measureReal_union_le _ _

theorem measureReal_diff_lt_of_lt_add (hs : MeasurableSet s) (hst : s ⊆ t) (ε : ℝ)
    (h : μ.real t < μ.real s + ε) (ht' : μ t ≠ ∞ := by finiteness) :
    μ.real (t \ s) < ε := by
  rw [measureReal_diff hst hs ht']; linarith

theorem measureReal_diff_le_iff_le_add (hs : MeasurableSet s) (hst : s ⊆ t) (ε : ℝ)
    (ht' : μ t ≠ ∞ := by finiteness) :
    μ.real (t \ s) ≤ ε ↔ μ.real t ≤ μ.real s + ε := by
  rw [measureReal_diff hst hs ht', tsub_le_iff_left]

theorem measureReal_eq_measureReal_of_null_diff {s t : Set α} (hst : s ⊆ t)
    (h_nulldiff : μ.real (t \ s) = 0) (h : μ (t \ s) ≠ ∞ := by finiteness) :
    μ.real s = μ.real t := by
  rw [measureReal_eq_zero_iff h] at h_nulldiff
  simp [measureReal_def, measure_eq_measure_of_null_diff hst h_nulldiff]

theorem measureReal_eq_measureReal_of_between_null_diff {s₁ s₂ s₃ : Set α}
    (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0)
    (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
    μ.real s₁ = μ.real s₂ ∧ μ.real s₂ = μ.real s₃ := by
  have A : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ :=
    measure_eq_measure_of_between_null_diff h12 h23 ((measureReal_eq_zero_iff h').1 h_nulldiff)
  simp [measureReal_def, A.1, A.2]

theorem measureReal_eq_measureReal_smaller_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0)
    (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
    μ.real s₁ = μ.real s₂ :=
  (measureReal_eq_measureReal_of_between_null_diff h12 h23 h_nulldiff h').1

theorem measureReal_eq_measureReal_larger_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0) (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
    μ.real s₂ = μ.real s₃ :=
  (measureReal_eq_measureReal_of_between_null_diff h12 h23 h_nulldiff h').2

theorem measureReal_compl [IsFiniteMeasure μ] (h₁ : MeasurableSet s) :
    μ.real sᶜ = μ.real univ - μ.real s := by
  rw [compl_eq_univ_diff]
  exact measureReal_diff (subset_univ s) h₁

theorem measureReal_union_congr_of_subset {t₁ t₂ : Set α} (hs : s₁ ⊆ s₂)
    (hsμ : μ.real s₂ ≤ μ.real s₁) (ht : t₁ ⊆ t₂) (htμ : μ.real t₂ ≤ μ.real t₁)
    (h₁ : μ s₂ ≠ ∞ := by finiteness) (h₂ : μ t₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ t₁) = μ.real (s₂ ∪ t₂) := by
  simp [measureReal_def]
  rw [measure_union_congr_of_subset hs _ ht]
  · exact (ENNReal.toReal_le_toReal h₂ (measure_ne_top_of_subset ht h₂)).1 htμ
  · exact (ENNReal.toReal_le_toReal h₁ (measure_ne_top_of_subset hs h₁)).1 hsμ

/- TODO: use NullMeasurable sets like in the mathlib file. -/
theorem sum_measureReal_le_measureReal_univ [IsFiniteMeasure μ] {s : Finset ι} {t : ι → Set α}
    (h : ∀ i ∈ s, MeasurableSet (t i)) (H : Set.PairwiseDisjoint (↑s) t) :
    (∑ i in s, μ.real (t i)) ≤ μ.real (univ : Set α) := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (fun i hi ↦ measure_ne_top _ _)]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact sum_measure_le_measure_univ (fun i hi ↦ (h i hi).nullMeasurableSet) H.aedisjoint

/-- Pigeonhole principle for measure spaces: if `s` is a `Finset` and
`∑ i in s, μ.real (t i) > μ.real univ`, then one of the intersections `t i ∩ t j` is not empty.
TODO: use NullMeasurable sets like in the mathlib file. -/
theorem exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal
    {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    {s : Finset ι} {t : ι → Set α} (h : ∀ i ∈ s, MeasurableSet (t i))
    (H : μ.real (univ : Set α) < ∑ i in s, μ.real (t i)) :
    ∃ i ∈ s, ∃ j ∈ s, ∃ _h : i ≠ j, (t i ∩ t j).Nonempty := by
  apply exists_nonempty_inter_of_measure_univ_lt_sum_measure μ
    (fun i hi ↦ (h i hi).nullMeasurableSet)
  apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) _).1
  · convert H
    rw [ENNReal.toReal_sum (fun i hi ↦ measure_ne_top _ _)]
    rfl
  · exact (ENNReal.sum_lt_top.2 (fun i hi ↦ measure_lt_top _ _)).ne

/-- If two sets `s` and `t` are included in a set `u` of finite measure,
and `μ.real s + μ.real t > μ.real u`, then `s` intersects `t`.
Version assuming that `t` is measurable. -/
theorem nonempty_inter_of_measureReal_lt_add {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (ht : MeasurableSet t) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ.real u < μ.real s + μ.real t)
    (hu : μ u ≠ ∞ := by finiteness) :
    (s ∩ t).Nonempty := by
  apply nonempty_inter_of_measure_lt_add μ ht h's h't
  apply (ENNReal.toReal_lt_toReal hu _).1
  · rw [ENNReal.toReal_add (measure_ne_top_of_subset h's hu) (measure_ne_top_of_subset h't hu)]
    exact h
  · exact ENNReal.add_ne_top.2 ⟨measure_ne_top_of_subset h's hu, measure_ne_top_of_subset h't hu⟩

/-- If two sets `s` and `t` are included in a set `u` of finite measure,
and `μ.real s + μ.real t > μ.real u`, then `s` intersects `t`.
Version assuming that `s` is measurable. -/
theorem nonempty_inter_of_measureReal_lt_add' {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (hs : MeasurableSet s) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ.real u < μ.real s + μ.real t)
    (hu : μ u ≠ ∞ := by finiteness) :
    (s ∩ t).Nonempty := by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measureReal_lt_add μ hs h't h's h hu

theorem measureReal_prod_prod {μ : Measure α} {ν : Measure β} [SigmaFinite ν] (s : Set α)
    (t : Set β) :
    (μ.prod ν).real (s ×ˢ t) = μ.real s * ν.real t := by
  simp only [measureReal_def, prod_prod, ENNReal.toReal_mul]

theorem ext_iff_measureReal_singleton [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {μ1 μ2 : Measure S} [IsFiniteMeasure μ1] [IsFiniteMeasure μ2] :
    μ1 = μ2 ↔ ∀ x, μ1.real {x} = μ2.real {x} := by
  rw [Measure.ext_iff_singleton]
  congr! with x
  have h1 : μ1 {x} ≠ ⊤ := by finiteness
  have h2 : μ2 {x} ≠ ⊤ := by finiteness
  rw [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff]
  simp [h1, h2]

end MeasureTheory

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: applications of `μ.real` are nonnegative. -/
@[positivity MeasureTheory.Measure.real _ _]
def evalMeasureReal : PositivityExt where eval {_ _} _zα _pα e := do
  let .app (.app _ a) b ← whnfR e | throwError "not measureReal"
  let p ← mkAppOptM ``MeasureTheory.measureReal_nonneg #[none, none, a, b]
  pure (.nonnegative p)

end Mathlib.Meta.Positivity
section aux_lemmas

lemma measureReal_preimage_fst_singleton_eq_sum {S T : Type*} {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] [Fintype T] {_ : MeasurableSpace T}
    [MeasurableSingletonClass T] (μ : Measure (S × T)) [IsFiniteMeasure μ] (x : S) :
    μ.real (Prod.fst ⁻¹' {x}) = ∑ y : T, μ.real {(x, y)} := by
  rw [measureReal_def, measure_preimage_fst_singleton_eq_sum, ENNReal.toReal_sum]
  · rfl
  intros
  finiteness

lemma measureReal_preimage_snd_singleton_eq_sum {S T : Type*} [Fintype S] {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] {_ : MeasurableSpace T}
    [MeasurableSingletonClass T] (μ : Measure (S × T)) [IsFiniteMeasure μ] (y : T) :
    μ.real (Prod.snd ⁻¹' {y}) = ∑ x : S, μ.real {(x, y)} := by
  rw [measureReal_def, measure_preimage_snd_singleton_eq_sum, ENNReal.toReal_sum]
  · rfl
  intros
  finiteness

end aux_lemmas
