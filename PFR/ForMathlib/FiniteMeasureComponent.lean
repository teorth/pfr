import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic
import PFR.MeasureReal

/-!
# The measure of a connected component of a space depends continuously on a finite measure

-/


open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction

section measure_of_component

#check IsClopen

lemma continuous_indicator_const {α β : Type*} [TopologicalSpace α]
    [Zero β] [TopologicalSpace β] {b : β} {s : Set α} (s_clopen : IsClopen s) :
    Continuous (indicator s (fun _ ↦ b)) := by
  rw [continuous_def]
  intro t _
  classical
  have aux := @indicator_const_preimage_eq_union α β _ s t b _ _
  rw [aux]
  apply IsOpen.union
  · by_cases ht : b ∈ t
    · simp only [ht, ite_true, s_clopen.isOpen]
    · simp only [ht, ite_false, isOpen_empty]
  · by_cases ht : 0 ∈ t
    · simp only [ht, ite_true, isOpen_compl_iff, s_clopen.isClosed]
    · simp only [ht, ite_false, isOpen_empty]

--#check IsolatedPoint -- Does not exist. What is the Mathlib-spelling?

lemma continuous_indicator_singleton {α : Type*} [TopologicalSpace α] [T1Space α]
    {a : α} (ha : IsOpen {a}) :
    Continuous (indicator {a} (fun _ ↦ (1 : ℝ≥0))) :=
  continuous_indicator_const ⟨ha, T1Space.t1 a⟩

lemma continuous_integral_finiteMeasure
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] (f : α →ᵇ ℝ) :
    Continuous (fun (μ : FiniteMeasure α) ↦ ∫ x, f x ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply continuousAt_of_tendsto_nhds
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp tendsto_id f

noncomputable def indicatorBCF {α : Type*} [TopologicalSpace α]
    {s : Set α} (s_clopen : IsClopen s) :
    BoundedContinuousFunction α ℝ where
      toFun := s.indicator (fun _ ↦ (1 : ℝ))
      continuous_toFun := continuous_indicator_const s_clopen
      map_bounded' := by
        use 1
        intro x y
        by_cases hx : x ∈ s
        · by_cases hy : y ∈ s
          · simp only [hx, hy, indicator_of_mem, dist_self, zero_le_one]
          · simp only [hx, hy, indicator_of_mem, not_false_eq_true, indicator_of_not_mem,
                       dist_zero_right, norm_one, le_refl]
        · by_cases hy : y ∈ s
          · simp only [hx, hy, not_false_eq_true, indicator_of_not_mem, indicator_of_mem,
                       dist_zero_left, norm_one, le_refl]
          · simp only [hx, hy, not_false_eq_true, indicator_of_not_mem, dist_self, zero_le_one]

@[simp] lemma indicatorBCF_apply  {α : Type*} [TopologicalSpace α]
    {s : Set α} (s_clopen : IsClopen s) (x : α) :
    indicatorBCF s_clopen x = s.indicator (fun _ ↦ (1 : ℝ)) x := rfl

lemma lintegral_indicatorBCF {α : Type*} [TopologicalSpace α] [MeasurableSpace α] (μ : Measure α)
    {s : Set α} (s_clopen : IsClopen s) (s_mble : MeasurableSet s) :
    ∫⁻ x, ENNReal.ofReal (indicatorBCF s_clopen x) ∂μ = μ s := by
  convert lintegral_indicator_one s_mble
  rename_i x
  by_cases hx : x ∈ s <;> simp [hx]

lemma integral_indicatorBCF {α : Type*} [TopologicalSpace α] [MeasurableSpace α] (μ : Measure α)
    {s : Set α} (s_clopen : IsClopen s) (s_mble : MeasurableSet s) :
    ∫ x, (indicatorBCF s_clopen x) ∂μ = (μ s).toReal := integral_indicator_one s_mble

/-- The measure of any connected component depends continuously on the `FiniteMeasure`. -/
lemma continuous_finiteMeasure_apply_of_isOpen_of_isClosed
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {s : Set α} (s_clopen : IsClopen s) :
    Continuous (fun (μ : FiniteMeasure α) ↦ (μ : Measure α).real s) := by
  convert continuous_integral_finiteMeasure (indicatorBCF s_clopen)
  have s_mble : MeasurableSet s := s_clopen.isOpen.measurableSet
  rw [integral_indicatorBCF _ s_clopen s_mble]
  rfl

end measure_of_component -- section
