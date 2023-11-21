import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
--import Mathlib

/-!
# Products of finite measures and probability measures

-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction BigOperators

namespace MeasureTheory

@[simp] lemma FiniteMeasure.toMeasure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : FiniteMeasure α) (f : α → β) :
    (μ.map f).toMeasure = μ.toMeasure.map f := rfl

section FiniteMeasure_product

namespace FiniteMeasure

variable {α : Type*} [MeasurableSpace α]
-- [TopologicalSpace α] [OpensMeasurableSpace α]
variable {β : Type*} [MeasurableSpace β]
-- [TopologicalSpace β] [OpensMeasurableSpace β]


/-- The binary product of finite measures. -/
noncomputable def prod (μ : FiniteMeasure α) (ν : FiniteMeasure β) : FiniteMeasure (α × β) :=
  ⟨μ.toMeasure.prod ν.toMeasure, Measure.prod.instIsFiniteMeasure μ.toMeasure ν.toMeasure⟩

variable (μ : FiniteMeasure α) (ν : FiniteMeasure β)

@[simp] lemma toMeasure_prod : (μ.prod ν).toMeasure = μ.toMeasure.prod ν.toMeasure := rfl

lemma prod_apply (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ x, ν.toMeasure (Prod.mk x ⁻¹' s) ∂μ) := by
  simp [@Measure.prod_apply α β _ _ μ ν _ s s_mble]

lemma prod_apply_symm (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ y, μ.toMeasure ((fun x ↦ ⟨x, y⟩) ⁻¹' s) ∂ν) := by
  simp [@Measure.prod_apply_symm α β _ _ μ ν _ _ s s_mble]

lemma prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t := by simp

lemma mass_prod : (μ.prod ν).mass = μ.mass * ν.mass := by
  simp only [mass, univ_prod_univ.symm, toMeasure_prod]
  rw [← ENNReal.toNNReal_mul]
  exact congr_arg ENNReal.toNNReal (Measure.prod_prod univ univ)

lemma zero_prod : (0 : FiniteMeasure α).prod ν = 0 := by
  rw [← mass_zero_iff, mass_prod, zero_mass, zero_mul]

lemma prod_zero : μ.prod (0 : FiniteMeasure β) = 0 := by
  rw [← mass_zero_iff, mass_prod, zero_mass, mul_zero]

@[simp] lemma map_fst_prod : (μ.prod ν).map Prod.fst = (ν univ) • μ := by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_map, toMeasure_prod, Measure.map_fst_prod]
  ext s s_mble
  simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul]
  sorry

@[simp] lemma map_snd_prod : (μ.prod ν).map Prod.snd = (μ univ) • ν := by
  sorry

lemma map_prod_map {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpace β']
    {f : α → α'} {g : β → β'}  (f_mble : Measurable f) (g_mble : Measurable g):
    (μ.map f).prod (ν.map g) = (μ.prod ν).map (Prod.map f g) := by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble] <;> exact IsFiniteMeasure.toSigmaFinite _

lemma prod_apply_null {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s = 0 ↔ (fun x ↦ ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0 := by
  convert Measure.measure_prod_null (μ := μ.toMeasure) (ν := ν.toMeasure) hs
  · simp only [toMeasure_prod, toNNReal_eq_zero_iff, or_iff_left_iff_imp]
    intro con
    by_contra
    exact measure_ne_top _ _ con
  · constructor <;> intro h <;> filter_upwards [h] with p hp
    · simp only [Pi.zero_apply] at *
      rcases (ENNReal.toNNReal_eq_zero_iff _).mp hp with (h'|con)
      · exact h'
      · by_contra
        exact measure_ne_top _ _ con
    · simp only [Pi.zero_apply] at *
      exact (ENNReal.toNNReal_eq_zero_iff _).mpr (Or.inl hp)

lemma measure_ae_null_of_prod_null {s : Set (α × β)} (h : μ.prod ν s = 0) :
    (fun x ↦ ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0 := by
  convert Measure.measure_ae_null_of_prod_null (μ := μ.toMeasure) (ν := ν.toMeasure) (s := s) ?_
  · constructor <;> intro h <;> filter_upwards [h] with p hp
    · simp only [Pi.zero_apply] at *
      rcases (ENNReal.toNNReal_eq_zero_iff _).mp hp with (h'|con)
      · exact h'
      · by_contra
        exact measure_ne_top _ _ con
    · simp only [Pi.zero_apply] at *
      exact (ENNReal.toNNReal_eq_zero_iff _).mpr (Or.inl hp)
  · simp [toNNReal_eq_zero_iff] at h
    rcases h with (h'|con)
    · exact h'
    · by_contra
      exact measure_ne_top _ _ con

lemma prod_swap : (μ.prod ν).map Prod.swap = ν.prod μ := by
  apply Subtype.ext
  simp [Measure.prod_swap]

/-
lemma prod_sum {ι : Type*} [Fintype ι] (νs : ι → FiniteMeasure β) :
    μ.prod (∑ i, νs i) = ∑ i, μ.prod (νs i) := by
  sorry

lemma sum_prod {ι : Type*} [Fintype ι] (μs : ι → FiniteMeasure β) :
    (∑ i, μs i).prod ν = ∑ i, (μs i).prod ν := by
  sorry
 -/

variable [TopologicalSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [OpensMeasurableSpace β]

lemma tendsto_prod [SecondCountableTopology α] {ι : Type*} {L : Filter ι}
    {μνs : ι → FiniteMeasure α × FiniteMeasure β} {μν : FiniteMeasure α × FiniteMeasure β}
    (h_lim : L.Tendsto μνs (𝓝 μν)) :
    L.Tendsto (fun i ↦ (μνs i).1.prod (μνs i).2) (𝓝 (μν.1.prod μν.2)) := by
  rw [nhds_prod_eq] at h_lim
  --simp [tendsto_prod_iff] at h_lim
  --rw [Tendsto.prod_mk_nhds] at h_lim
  --rw [tendsto_nhds_prod] at h_lim
  rw [tendsto_iff_forall_integral_tendsto]
  sorry

lemma continuous_prod [SecondCountableTopology α] :
    Continuous (fun (μν : FiniteMeasure α × FiniteMeasure β) ↦ μν.1.prod μν.2) := by
  haveI : T1Space (FiniteMeasure (α × β)) := sorry -- Under some reasonable hypotheses?
  --haveI : T1Space (FiniteMeasure α × FiniteMeasure β) := sorry
  apply continuous_iff_continuousAt.mpr
  intro ⟨μ, ν⟩
  let μν : FiniteMeasure α × FiniteMeasure β := ⟨μ, ν⟩
  apply continuousAt_of_tendsto_nhds (y := μ.prod ν)
  -- Assume also second countability!
  haveI : Nonempty (α × β) := sorry -- ...otherwise trivial
  apply (@tendsto_normalize_iff_tendsto (α × β) _ _ (μ.prod ν) _ _ _
          (𝓝 μν) (fun κ ↦ κ.1.prod κ.2) ?_).mp
  · refine ⟨?_, ?_⟩
    · -- **This is the main sorry!**
      -- Oh $#!, there is a universe misprint in the statement of `tendsto_of_forall_isOpen_le_liminf`
      have := @tendsto_of_forall_isOpen_le_liminf
      sorry
    · sorry  -- The easy case.
  · sorry -- ...otherwise trivial
  --apply tendsto_of_forall_isOpen_le_liminf
  --have := tendsto_of_liminf
  --have := @tendsto_iff_forall_integral_tendsto (α × β) _ _ _ ?_ ?_  -- (μ.prod ν)
  --sorry

#check continuousAt_of_tendsto_nhds
#check T1Space

lemma continuous_prod' [SecondCountableTopology β] :
    Continuous (fun (μν : FiniteMeasure α × FiniteMeasure β) ↦ μν.1.prod μν.2) := by
  sorry

end FiniteMeasure -- namespace

end FiniteMeasure_product -- section

section ProbabilityMeasure_product
end ProbabilityMeasure_product -- section

end MeasureTheory -- namespace
