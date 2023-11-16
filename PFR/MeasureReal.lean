/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris Van Doorn
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation

/-!
# Measures as real valued-functions

Given a measure `μ`, we define `μ.real` as the function sending a set `s` to `(μ s).toReal`, and
develop a basic API around this.
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal

macro "finiteness" : tactic => `(tactic|apply measure_ne_top)

namespace MeasureTheory

variable {α : Type*} {_ : MeasurableSpace α} (μ : Measure α)

protected def Measure.real (s : Set α) : ℝ :=
  (μ s).toReal

protected def Measure.nnreal (s : Set α) : ℝ≥0 :=
  (μ s).toNNReal

variable {μ}
variable {s s₁ s₂ t : Set α}

theorem measure_ne_top_of_subset (h : s ⊆ t) (ht : μ t ≠ ∞) : μ s ≠ ∞ :=
  (measure_lt_top_of_subset h ht).ne

theorem measureReal_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂)
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = μ.real s₁ + μ.real s₂ := by
  simp only [Measure.real]
  rw [measure_union hd h, ENNReal.toReal_add h₁ h₂]

theorem measureReal_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁)
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = μ.real s₁ + μ.real s₂ := by
  simp only [Measure.real]
  rw [measure_union' hd h, ENNReal.toReal_add h₁ h₂]

theorem measureReal_inter_add_diff (s : Set α) (ht : MeasurableSet t)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s ∩ t) + μ.real (s \ t) = μ.real s := by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add, measure_inter_add_diff _ ht]
  · exact measure_ne_top_of_subset (inter_subset_left _ _) h
  · exact measure_ne_top_of_subset (diff_subset _ _) h

theorem measureReal_diff_add_inter (s : Set α) (ht : MeasurableSet t)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s \ t) + μ.real (s ∩ t) = μ.real s :=
  (add_comm _ _).trans (measureReal_inter_add_diff s ht h)

theorem measureReal_union_add_inter (s : Set α) (ht : MeasurableSet t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
  have : μ (s ∪ t) ≠ ∞ := sorry
  rw [← measureReal_inter_add_diff (s ∪ t) ht this, Set.union_inter_cancel_right, union_diff_right,
    ← measure_inter_add_diff s ht]
  ac_rfl
#align measure_theory.measure_union_add_inter MeasureTheory.measure_union_add_inter

theorem measure_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [union_comm, inter_comm, measure_union_add_inter t hs, add_comm]
#align measure_theory.measure_union_add_inter' MeasureTheory.measure_union_add_inter'

lemma measure_symmDiff_eq (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ (s ∆ t) = μ (s \ t) + μ (t \ s) := by
  simpa only [symmDiff_def, sup_eq_union] using measure_union disjoint_sdiff_sdiff (ht.diff hs)

lemma measure_symmDiff_le (s t u : Set α) :
    μ (s ∆ u) ≤ μ (s ∆ t) + μ (t ∆ u) :=
  le_trans (μ.mono $ symmDiff_triangle s t u) (measure_union_le (s ∆ t) (t ∆ u))

theorem measure_add_measure_compl (h : MeasurableSet s) : μ s + μ sᶜ = μ univ :=
  measure_add_measure_compl₀ h.nullMeasurableSet
#align measure_theory.measure_add_measure_compl MeasureTheory.measure_add_measure_compl

theorem measure_biUnion₀ {s : Set β} {f : β → Set α} (hs : s.Countable)
    (hd : s.Pairwise (AEDisjoint μ on f)) (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) := by
  haveI := hs.toEncodable
  rw [biUnion_eq_iUnion]
  exact measure_iUnion₀ (hd.on_injective Subtype.coe_injective fun x => x.2) fun x => h x x.2
#align measure_theory.measure_bUnion₀ MeasureTheory.measure_biUnion₀

theorem measure_biUnion {s : Set β} {f : β → Set α} (hs : s.Countable) (hd : s.PairwiseDisjoint f)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) :=
  measure_biUnion₀ hs hd.aedisjoint fun b hb => (h b hb).nullMeasurableSet
#align measure_theory.measure_bUnion MeasureTheory.measure_biUnion

theorem measure_sUnion₀ {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise (AEDisjoint μ))
    (h : ∀ s ∈ S, NullMeasurableSet s μ) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion, measure_biUnion₀ hs hd h]
#align measure_theory.measure_sUnion₀ MeasureTheory.measure_sUnion₀

theorem measure_sUnion {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise Disjoint)
    (h : ∀ s ∈ S, MeasurableSet s) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion, measure_biUnion hs hd h]
#align measure_theory.measure_sUnion MeasureTheory.measure_sUnion

theorem measure_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑ p in s, μ (f p) := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, ← tsum_fintype]
  exact measure_biUnion₀ s.countable_toSet hd hm
#align measure_theory.measure_bUnion_finset₀ MeasureTheory.measure_biUnion_finset₀

theorem measure_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑ p in s, μ (f p) :=
  measure_biUnion_finset₀ hd.aedisjoint fun b hb => (hm b hb).nullMeasurableSet
#align measure_theory.measure_bUnion_finset MeasureTheory.measure_biUnion_finset

/-- The measure of an a.e. disjoint union (even uncountable) of null-measurable sets is at least
the sum of the measures of the sets. -/
theorem tsum_meas_le_meas_iUnion_of_disjoint₀ {ι : Type*} [MeasurableSpace α] (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) := by
  rcases show Summable fun i => μ (As i) from ENNReal.summable with ⟨S, hS⟩
  rw [hS.tsum_eq]
  refine' tendsto_le_of_eventuallyLE hS tendsto_const_nhds (eventually_of_forall _)
  intro s
  simp only [← measure_biUnion_finset₀ (fun _i _hi _j _hj hij => As_disj hij) fun i _ => As_mble i]
  exact measure_mono (iUnion₂_subset_iUnion (fun i : ι => i ∈ s) fun i : ι => As i)

/-- The measure of a disjoint union (even uncountable) of measurable sets is at least the sum of
the measures of the sets. -/
theorem tsum_meas_le_meas_iUnion_of_disjoint {ι : Type*} [MeasurableSpace α] (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) :=
  tsum_meas_le_meas_iUnion_of_disjoint₀ μ (fun i ↦ (As_mble i).nullMeasurableSet)
    (fun _ _ h ↦ Disjoint.aedisjoint (As_disj h))
#align measure_theory.tsum_meas_le_meas_Union_of_disjoint MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint

/-- If `s` is a countable set, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem tsum_measure_preimage_singleton {s : Set β} (hs : s.Countable) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑' b : s, μ (f ⁻¹' {↑b})) = μ (f ⁻¹' s) := by
  rw [← Set.biUnion_preimage_singleton, measure_biUnion hs (pairwiseDisjoint_fiber f s) hf]
#align measure_theory.tsum_measure_preimage_singleton MeasureTheory.tsum_measure_preimage_singleton

/-- If `s` is a `Finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem sum_measure_preimage_singleton (s : Finset β) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑ b in s, μ (f ⁻¹' {b})) = μ (f ⁻¹' ↑s) := by
  simp only [← measure_biUnion_finset (pairwiseDisjoint_fiber f s) hf,
    Finset.set_biUnion_preimage_singleton]
#align measure_theory.sum_measure_preimage_singleton MeasureTheory.sum_measure_preimage_singleton

theorem measure_diff_null' (h : μ (s₁ ∩ s₂) = 0) : μ (s₁ \ s₂) = μ s₁ :=
  measure_congr <| diff_ae_eq_self.2 h
#align measure_theory.measure_diff_null' MeasureTheory.measure_diff_null'

theorem measure_diff_null (h : μ s₂ = 0) : μ (s₁ \ s₂) = μ s₁ :=
  measure_diff_null' <| measure_mono_null (inter_subset_right _ _) h
#align measure_theory.measure_diff_null MeasureTheory.measure_diff_null

theorem measure_add_diff (hs : MeasurableSet s) (t : Set α) : μ s + μ (t \ s) = μ (s ∪ t) := by
  rw [← measure_union' (@disjoint_sdiff_right _ s t) hs, union_diff_self]
#align measure_theory.measure_add_diff MeasureTheory.measure_add_diff

theorem measure_diff' (s : Set α) (hm : MeasurableSet t) (h_fin : μ t ≠ ∞) :
    μ (s \ t) = μ (s ∪ t) - μ t :=
  Eq.symm <| ENNReal.sub_eq_of_add_eq h_fin <| by rw [add_comm, measure_add_diff hm, union_comm]
#align measure_theory.measure_diff' MeasureTheory.measure_diff'

theorem measure_diff (h : s₂ ⊆ s₁) (h₂ : MeasurableSet s₂) (h_fin : μ s₂ ≠ ∞) :
    μ (s₁ \ s₂) = μ s₁ - μ s₂ := by rw [measure_diff' _ h₂ h_fin, union_eq_self_of_subset_right h]
#align measure_theory.measure_diff MeasureTheory.measure_diff

theorem le_measure_diff : μ s₁ - μ s₂ ≤ μ (s₁ \ s₂) :=
  tsub_le_iff_left.2 <|
    calc
      μ s₁ ≤ μ (s₂ ∪ s₁) := measure_mono (subset_union_right _ _)
      _ = μ (s₂ ∪ s₁ \ s₂) := (congr_arg μ union_diff_self.symm)
      _ ≤ μ s₂ + μ (s₁ \ s₂) := measure_union_le _ _

#align measure_theory.le_measure_diff MeasureTheory.le_measure_diff

theorem measure_diff_lt_of_lt_add (hs : MeasurableSet s) (hst : s ⊆ t) (hs' : μ s ≠ ∞) {ε : ℝ≥0∞}
    (h : μ t < μ s + ε) : μ (t \ s) < ε := by
  rw [measure_diff hst hs hs']; rw [add_comm] at h
  exact ENNReal.sub_lt_of_lt_add (measure_mono hst) h
#align measure_theory.measure_diff_lt_of_lt_add MeasureTheory.measure_diff_lt_of_lt_add

theorem measure_diff_le_iff_le_add (hs : MeasurableSet s) (hst : s ⊆ t) (hs' : μ s ≠ ∞) {ε : ℝ≥0∞} :
    μ (t \ s) ≤ ε ↔ μ t ≤ μ s + ε := by rw [measure_diff hst hs hs', tsub_le_iff_left]
#align measure_theory.measure_diff_le_iff_le_add MeasureTheory.measure_diff_le_iff_le_add

theorem measure_eq_measure_of_null_diff {s t : Set α} (hst : s ⊆ t) (h_nulldiff : μ (t \ s) = 0) :
    μ s = μ t := measure_congr <|
      EventuallyLE.antisymm (HasSubset.Subset.eventuallyLE hst) (ae_le_set.mpr h_nulldiff)
#align measure_theory.measure_eq_measure_of_null_diff MeasureTheory.measure_eq_measure_of_null_diff

theorem measure_eq_measure_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃)
    (h_nulldiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ := by
  have le12 : μ s₁ ≤ μ s₂ := measure_mono h12
  have le23 : μ s₂ ≤ μ s₃ := measure_mono h23
  have key : μ s₃ ≤ μ s₁ :=
    calc
      μ s₃ = μ (s₃ \ s₁ ∪ s₁) := by rw [diff_union_of_subset (h12.trans h23)]
      _ ≤ μ (s₃ \ s₁) + μ s₁ := (measure_union_le _ _)
      _ = μ s₁ := by simp only [h_nulldiff, zero_add]

  exact ⟨le12.antisymm (le23.trans key), le23.antisymm (key.trans le12)⟩
#align measure_theory.measure_eq_measure_of_between_null_diff MeasureTheory.measure_eq_measure_of_between_null_diff

theorem measure_eq_measure_smaller_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ :=
  (measure_eq_measure_of_between_null_diff h12 h23 h_nulldiff).1
#align measure_theory.measure_eq_measure_smaller_of_between_null_diff MeasureTheory.measure_eq_measure_smaller_of_between_null_diff

theorem measure_eq_measure_larger_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ (s₃ \ s₁) = 0) : μ s₂ = μ s₃ :=
  (measure_eq_measure_of_between_null_diff h12 h23 h_nulldiff).2
#align measure_theory.measure_eq_measure_larger_of_between_null_diff MeasureTheory.measure_eq_measure_larger_of_between_null_diff

theorem measure_compl (h₁ : MeasurableSet s) (h_fin : μ s ≠ ∞) : μ sᶜ = μ univ - μ s := by
  rw [compl_eq_univ_diff]
  exact measure_diff (subset_univ s) h₁ h_fin
#align measure_theory.measure_compl MeasureTheory.measure_compl

@[simp]
theorem union_ae_eq_left_iff_ae_subset : (s ∪ t : Set α) =ᵐ[μ] s ↔ t ≤ᵐ[μ] s := by
  rw [ae_le_set]
  refine'
    ⟨fun h => by simpa only [union_diff_left] using (ae_eq_set.mp h).1, fun h =>
      eventuallyLE_antisymm_iff.mpr
        ⟨by rwa [ae_le_set, union_diff_left],
          HasSubset.Subset.eventuallyLE <| subset_union_left s t⟩⟩
#align measure_theory.union_ae_eq_left_iff_ae_subset MeasureTheory.union_ae_eq_left_iff_ae_subset

@[simp]
theorem union_ae_eq_right_iff_ae_subset : (s ∪ t : Set α) =ᵐ[μ] t ↔ s ≤ᵐ[μ] t := by
  rw [union_comm, union_ae_eq_left_iff_ae_subset]
#align measure_theory.union_ae_eq_right_iff_ae_subset MeasureTheory.union_ae_eq_right_iff_ae_subset

theorem ae_eq_of_ae_subset_of_measure_ge (h₁ : s ≤ᵐ[μ] t) (h₂ : μ t ≤ μ s) (hsm : MeasurableSet s)
    (ht : μ t ≠ ∞) : s =ᵐ[μ] t := by
  refine' eventuallyLE_antisymm_iff.mpr ⟨h₁, ae_le_set.mpr _⟩
  replace h₂ : μ t = μ s; exact h₂.antisymm (measure_mono_ae h₁)
  replace ht : μ s ≠ ∞; exact h₂ ▸ ht
  rw [measure_diff' t hsm ht, measure_congr (union_ae_eq_left_iff_ae_subset.mpr h₁), h₂, tsub_self]
#align measure_theory.ae_eq_of_ae_subset_of_measure_ge MeasureTheory.ae_eq_of_ae_subset_of_measure_ge

/-- If `s ⊆ t`, `μ t ≤ μ s`, `μ t ≠ ∞`, and `s` is measurable, then `s =ᵐ[μ] t`. -/
theorem ae_eq_of_subset_of_measure_ge (h₁ : s ⊆ t) (h₂ : μ t ≤ μ s) (hsm : MeasurableSet s)
    (ht : μ t ≠ ∞) : s =ᵐ[μ] t :=
  ae_eq_of_ae_subset_of_measure_ge (HasSubset.Subset.eventuallyLE h₁) h₂ hsm ht
#align measure_theory.ae_eq_of_subset_of_measure_ge MeasureTheory.ae_eq_of_subset_of_measure_ge

theorem measure_iUnion_congr_of_subset [Countable β] {s : β → Set α} {t : β → Set α}
    (hsub : ∀ b, s b ⊆ t b) (h_le : ∀ b, μ (t b) ≤ μ (s b)) : μ (⋃ b, s b) = μ (⋃ b, t b) := by
  rcases Classical.em (∃ b, μ (t b) = ∞) with (⟨b, hb⟩ | htop)
  · calc
      μ (⋃ b, s b) = ∞ := top_unique (hb ▸ (h_le b).trans <| measure_mono <| subset_iUnion _ _)
      _ = μ (⋃ b, t b) := Eq.symm <| top_unique <| hb ▸ measure_mono (subset_iUnion _ _)
  push_neg at htop
  refine' le_antisymm (measure_mono (iUnion_mono hsub)) _
  set M := toMeasurable μ
  have H : ∀ b, (M (t b) ∩ M (⋃ b, s b) : Set α) =ᵐ[μ] M (t b) := by
    refine' fun b => ae_eq_of_subset_of_measure_ge (inter_subset_left _ _) _ _ _
    · calc
        μ (M (t b)) = μ (t b) := measure_toMeasurable _
        _ ≤ μ (s b) := (h_le b)
        _ ≤ μ (M (t b) ∩ M (⋃ b, s b)) :=
          measure_mono <|
            subset_inter ((hsub b).trans <| subset_toMeasurable _ _)
              ((subset_iUnion _ _).trans <| subset_toMeasurable _ _)
    · exact (measurableSet_toMeasurable _ _).inter (measurableSet_toMeasurable _ _)
    · rw [measure_toMeasurable]
      exact htop b
  calc
    μ (⋃ b, t b) ≤ μ (⋃ b, M (t b)) := measure_mono (iUnion_mono fun b => subset_toMeasurable _ _)
    _ = μ (⋃ b, M (t b) ∩ M (⋃ b, s b)) := (measure_congr (EventuallyEq.countable_iUnion H).symm)
    _ ≤ μ (M (⋃ b, s b)) := (measure_mono (iUnion_subset fun b => inter_subset_right _ _))
    _ = μ (⋃ b, s b) := measure_toMeasurable _
#align measure_theory.measure_Union_congr_of_subset MeasureTheory.measure_iUnion_congr_of_subset

theorem measure_union_congr_of_subset {t₁ t₂ : Set α} (hs : s₁ ⊆ s₂) (hsμ : μ s₂ ≤ μ s₁)
    (ht : t₁ ⊆ t₂) (htμ : μ t₂ ≤ μ t₁) : μ (s₁ ∪ t₁) = μ (s₂ ∪ t₂) := by
  rw [union_eq_iUnion, union_eq_iUnion]
  exact measure_iUnion_congr_of_subset (Bool.forall_bool.2 ⟨ht, hs⟩) (Bool.forall_bool.2 ⟨htμ, hsμ⟩)
#align measure_theory.measure_union_congr_of_subset MeasureTheory.measure_union_congr_of_subset

@[simp]
theorem measure_iUnion_toMeasurable [Countable β] (s : β → Set α) :
    μ (⋃ b, toMeasurable μ (s b)) = μ (⋃ b, s b) :=
  Eq.symm <|
    measure_iUnion_congr_of_subset (fun _b => subset_toMeasurable _ _) fun _b =>
      (measure_toMeasurable _).le
#align measure_theory.measure_Union_to_measurable MeasureTheory.measure_iUnion_toMeasurable

theorem measure_biUnion_toMeasurable {I : Set β} (hc : I.Countable) (s : β → Set α) :
    μ (⋃ b ∈ I, toMeasurable μ (s b)) = μ (⋃ b ∈ I, s b) := by
  haveI := hc.toEncodable
  simp only [biUnion_eq_iUnion, measure_iUnion_toMeasurable]
#align measure_theory.measure_bUnion_to_measurable MeasureTheory.measure_biUnion_toMeasurable

@[simp]
theorem measure_toMeasurable_union : μ (toMeasurable μ s ∪ t) = μ (s ∪ t) :=
  Eq.symm <|
    measure_union_congr_of_subset (subset_toMeasurable _ _) (measure_toMeasurable _).le Subset.rfl
      le_rfl
#align measure_theory.measure_to_measurable_union MeasureTheory.measure_toMeasurable_union

@[simp]
theorem measure_union_toMeasurable : μ (s ∪ toMeasurable μ t) = μ (s ∪ t) :=
  Eq.symm <|
    measure_union_congr_of_subset Subset.rfl le_rfl (subset_toMeasurable _ _)
      (measure_toMeasurable _).le
#align measure_theory.measure_union_to_measurable MeasureTheory.measure_union_toMeasurable

theorem sum_measure_le_measure_univ {s : Finset ι} {t : ι → Set α}
    (h : ∀ i ∈ s, MeasurableSet (t i)) (H : Set.PairwiseDisjoint (↑s) t) :
    (∑ i in s, μ (t i)) ≤ μ (univ : Set α) := by
  rw [← measure_biUnion_finset H h]
  exact measure_mono (subset_univ _)
#align measure_theory.sum_measure_le_measure_univ MeasureTheory.sum_measure_le_measure_univ

theorem tsum_measure_le_measure_univ {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i))
    (H : Pairwise (Disjoint on s)) : (∑' i, μ (s i)) ≤ μ (univ : Set α) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun s =>
    sum_measure_le_measure_univ (fun i _hi => hs i) fun i _hi j _hj hij => H hij
#align measure_theory.tsum_measure_le_measure_univ MeasureTheory.tsum_measure_le_measure_univ

/-- Pigeonhole principle for measure spaces: if `∑' i, μ (s i) > μ univ`, then
one of the intersections `s i ∩ s j` is not empty. -/
theorem exists_nonempty_inter_of_measure_univ_lt_tsum_measure {m : MeasurableSpace α}
    (μ : Measure α) {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i))
    (H : μ (univ : Set α) < ∑' i, μ (s i)) : ∃ (i j : _) (_h : i ≠ j), (s i ∩ s j).Nonempty := by
  contrapose! H
  apply tsum_measure_le_measure_univ hs
  intro i j hij
  exact disjoint_iff_inter_eq_empty.mpr (H i j hij)
#align measure_theory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure MeasureTheory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure

/-- Pigeonhole principle for measure spaces: if `s` is a `Finset` and
`∑ i in s, μ (t i) > μ univ`, then one of the intersections `t i ∩ t j` is not empty. -/
theorem exists_nonempty_inter_of_measure_univ_lt_sum_measure {m : MeasurableSpace α} (μ : Measure α)
    {s : Finset ι} {t : ι → Set α} (h : ∀ i ∈ s, MeasurableSet (t i))
    (H : μ (univ : Set α) < ∑ i in s, μ (t i)) :
    ∃ i ∈ s, ∃ j ∈ s, ∃ _h : i ≠ j, (t i ∩ t j).Nonempty := by
  contrapose! H
  apply sum_measure_le_measure_univ h
  intro i hi j hj hij
  exact disjoint_iff_inter_eq_empty.mpr (H i hi j hj hij)
#align measure_theory.exists_nonempty_inter_of_measure_univ_lt_sum_measure MeasureTheory.exists_nonempty_inter_of_measure_univ_lt_sum_measure

/-- If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `t` is measurable. -/
theorem nonempty_inter_of_measure_lt_add {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (ht : MeasurableSet t) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ u < μ s + μ t) :
    (s ∩ t).Nonempty := by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! h
  calc
    μ s + μ t = μ (s ∪ t) := (measure_union h ht).symm
    _ ≤ μ u := measure_mono (union_subset h's h't)

#align measure_theory.nonempty_inter_of_measure_lt_add MeasureTheory.nonempty_inter_of_measure_lt_add

/-- If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `s` is measurable. -/
theorem nonempty_inter_of_measure_lt_add' {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (hs : MeasurableSet s) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ u < μ s + μ t) :
    (s ∩ t).Nonempty := by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measure_lt_add μ hs h't h's h
#align measure_theory.nonempty_inter_of_measure_lt_add' MeasureTheory.nonempty_inter_of_measure_lt_add'


#exit
