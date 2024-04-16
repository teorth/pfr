import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.CondDistrib
import PFR.Mathlib.MeasureTheory.Integral.Lebesgue
import PFR.Mathlib.MeasureTheory.Measure.NullMeasurable
import PFR.Mathlib.Probability.Kernel.MeasureCompProd

/-!
# Disintegration of kernels in finite spaces

We can write `κ : kernel S (T × U)` as a composition-product `(fst κ) ⊗ₖ (condKernel κ)` where
`fst κ : kernel S T` and `condKernel : kernel (S × T) U` is defined in this file.

-/

open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

lemma _root_.MeasureTheory.lintegral_piecewise {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) (f g : α → ℝ≥0∞) [∀ j, Decidable (j ∈ s)] :
    ∫⁻ a, s.piecewise f g a ∂μ = ∫⁻ a in s, f a ∂μ + ∫⁻ a in sᶜ, g a ∂μ := by
  rw [← lintegral_add_compl _ hs]
  congr 1
  · refine set_lintegral_congr_fun hs ?_
    exact ae_of_all μ (fun a ha ↦ Set.piecewise_eq_of_mem _ _ _ ha)
  · refine set_lintegral_congr_fun hs.compl ?_
    exact ae_of_all μ (fun a ha ↦ Set.piecewise_eq_of_not_mem _ _ _ ha)

lemma MeasureTheory.Measure.condKernel_apply {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} [MeasurableSingletonClass α] [StandardBorelSpace β] [Nonempty β]
    (μ : Measure (α × β)) [IsFiniteMeasure μ] {x : α} (hx : μ.fst {x} ≠ 0)
    {s : Set β} (hs : MeasurableSet s) :
    μ.condKernel x s = (μ.fst {x})⁻¹ * μ ({x} ×ˢ s) := by
  nth_rewrite 3 [measure_eq_compProd μ]
  rw [Measure.compProd_apply]
  swap; · refine measurableSet_prod.mpr (Or.inl ⟨measurableSet_singleton x, hs⟩)
  classical
  have : ∀ a, μ.condKernel a (Prod.mk a ⁻¹' {x} ×ˢ s)
      = ({x} : Set α).indicator (fun a ↦ μ.condKernel a s) a := by
    intro a
    by_cases hax : a = x
    · simp only [hax, Set.singleton_prod, Set.mem_singleton_iff, Set.indicator_of_mem]
      congr
      ext y : 1
      simp
    · simp only [Set.singleton_prod, Set.mem_singleton_iff, hax, not_false_eq_true,
        Set.indicator_of_not_mem]
      have : Prod.mk a ⁻¹' (Prod.mk x '' s) = ∅ := by
        ext y
        simp [Ne.symm hax]
      simp only [this, OuterMeasure.empty']
  simp_rw [this]
  rw [MeasureTheory.lintegral_indicator _ (measurableSet_singleton x)]
  simp only [restrict_singleton, lintegral_smul_measure, lintegral_dirac]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top μ.fst _), one_mul]

instance instStandardBorelSpace_discreteMeasurableSpace {α : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [Countable α] :
    StandardBorelSpace α := by
  let bot : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  infer_instance

namespace ProbabilityTheory

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Countable S] [Nonempty S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [Countable T] [Nonempty T] [MeasurableSpace T] [DiscreteMeasurableSpace T]
  [Countable U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]

namespace kernel

section condKernel

/-- Kernel such that `κ : kernel T (S × U)` is equal to `(fst κ) ⊗ₖ (condKernel κ)`. -/
noncomputable
def condKernel (κ : kernel T (S × U)) [IsFiniteKernel κ] :
    kernel (T × S) U where
  val := fun ts ↦ (κ ts.1).condKernel ts.2
  property := measurable_of_countable _

lemma condKernel_apply (κ : kernel T (S × U)) [IsFiniteKernel κ] (x : T × S) :
    condKernel κ x = (κ x.1).condKernel x.2 := rfl

instance (κ : kernel T (S × U)) [IsFiniteKernel κ] : IsMarkovKernel (condKernel κ) := by
  constructor
  intro a
  rw [condKernel_apply]
  infer_instance

lemma condKernel_apply' (κ : kernel T (S × U)) [IsFiniteKernel κ]
    (x : T × S) (hx : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0) {s : Set U} (hs : MeasurableSet s) :
    condKernel κ x s
      = (κ x.1 (Prod.fst ⁻¹' {x.2}))⁻¹ * (κ x.1) ({x.2} ×ˢ s) := by
  rw [condKernel_apply, Measure.condKernel_apply _ _ hs,
    Measure.fst_apply (measurableSet_singleton _)]
  rwa [Measure.fst_apply (measurableSet_singleton _)]

lemma condKernel_compProd_apply' (κ : kernel T S) [IsFiniteKernel κ]
    (η : kernel (T × S) U) [IsMarkovKernel η]
    (x : T × S) (hx : κ x.1 {x.2} ≠ 0) {s : Set U} (hs : MeasurableSet s) :
    condKernel (κ ⊗ₖ η) x s = η x s := by
  have hx' : (κ ⊗ₖ η) x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0 := by
    rwa [compProd_preimage_fst _ _ (measurableSet_singleton _)]
  rw [condKernel_apply' _ _ hx' hs, compProd_apply _ _ _ ((measurableSet_singleton _).prod hs),
    kernel.compProd_apply, lintegral_eq_single _ x.2, lintegral_eq_single _ x.2]
  . simp
    rw [mul_comm, mul_assoc]
    set a := (κ x.1) {x.2}
    suffices a * a⁻¹ = 1 by simp [this]
    refine ENNReal.mul_inv_cancel hx ?_
    exact measure_ne_top (κ x.1) {x.2}
  . intro b hb; simp [hb.symm]
  . intro b hb; simp [hb]
  · measurability

lemma condKernel_compProd_apply (κ : kernel T S) [IsFiniteKernel κ]
    (η : kernel (T × S) U) [IsMarkovKernel η]
    (x : T × S) (hx : κ x.1 {x.2} ≠ 0) :
    condKernel (κ ⊗ₖ η) x = η x := by
  ext s hs
  convert condKernel_compProd_apply' κ η x hx hs

lemma condKernel_compProd_ae_eq (κ : kernel T S) [IsFiniteKernel κ]
    (η : kernel (T × S) U) [IsMarkovKernel η] (μ : Measure T) [IsFiniteMeasure μ]:
    condKernel (κ ⊗ₖ η) =ᵐ[μ ⊗ₘ κ] η := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [condKernel_compProd_apply]
  rw [Measure.compProd_apply (measurableSet_singleton _), lintegral_eq_sum_countable] at hx
  simp only [Set.mem_singleton_iff, ne_eq, Finset.sum_eq_zero_iff, tsum_eq_zero_iff ENNReal.summable, mul_eq_zero,
    forall_true_left, not_forall] at hx
  obtain ⟨y, hy⟩ := hx
  push_neg at hy
  classical
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod_right_eq_if] at hy
  simp only [ne_eq, Set.mem_singleton_iff] at hy
  by_cases hyx1 : y = x.1
  · simp only [hyx1, ite_true] at hy
    exact hy.2
  · simp [hyx1] at hy

lemma condKernel_prod_ae_eq (κ : kernel T S) [IsFiniteKernel κ]
    (η : kernel T U) [IsMarkovKernel η] [IsFiniteMeasure μ] :
    condKernel (κ ×ₖ η) =ᵐ[μ ⊗ₘ κ] prodMkRight S η := condKernel_compProd_ae_eq _ _ _

lemma disintegration (κ : kernel T (S × U)) [IsFiniteKernel κ] :
    κ = (kernel.fst κ) ⊗ₖ (condKernel κ) := by
  ext x s hs
  rw [compProd_apply _ _ _ hs, lintegral_fst]
  swap; · exact measurable_kernel_prod_mk_left' hs x
  rw [lintegral_eq_sum_countable, ENNReal.tsum_prod']
  change κ x s = ∑' a : S, ∑' b : U, κ x {(a, b)} * condKernel κ (x, a) (Prod.mk a ⁻¹' s)
  simp_rw [ENNReal.tsum_mul_right, ← measure_preimage_fst_singleton_eq_sum_countable (κ x)]
  have : ∑' a : S, (κ x (Prod.fst ⁻¹' {a})) * condKernel κ (x, a) (Prod.mk a ⁻¹' s)
      = ∑' a : S, κ x (Prod.fst ⁻¹' {a} ∩ {su | (a, su.2) ∈ s}) := by
    congr with a
    by_cases ha : κ x (Prod.fst ⁻¹' {a}) = 0
    · simp only [ha, zero_mul]
      exact (measure_mono_null (Set.inter_subset_left _ _) ha).symm
    · rw [condKernel_apply' κ _ (by exact ha) (measurable_prod_mk_left hs), ← mul_assoc,
      ENNReal.mul_inv_cancel ha (measure_ne_top _ _), one_mul]
      congr
  simp_rw [this]
  have : ⋃ a, Prod.fst ⁻¹' {a} ∩ {su | (a, su.2) ∈ s} = s := by ext a; simp
  conv_lhs => rw [← this]
  rw [measure_iUnion]
  · intro a a' haa'
    rw [Function.onFun, Set.disjoint_iff]
    intro su
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, and_imp]
    intro h1 _ h1' _
    exact haa' (h1.symm.trans h1')
  · refine fun _ ↦ (measurable_fst (measurableSet_singleton _)).inter ?_
    exact measurable_prod_mk_left.comp measurable_snd hs

lemma ae_eq_condKernel_of_compProd_eq (κ : kernel T (S × U)) [IsFiniteKernel κ]
    (η : kernel (T × S) U) [IsMarkovKernel η] [IsFiniteMeasure μ] (h : (fst κ) ⊗ₖ η = κ) :
    η =ᵐ[μ ⊗ₘ fst κ] condKernel κ := by
  have : condKernel κ = condKernel ((fst κ) ⊗ₖ η) := by congr; exact h.symm
  rw [this]
  exact (condKernel_compProd_ae_eq _ _ _).symm

lemma condKernel_map_prod_mk_left {V : Type*} [Nonempty V] [MeasurableSpace V]
    [DiscreteMeasurableSpace V] [Countable V]
    (κ : kernel T (S × U)) [IsMarkovKernel κ] (μ : Measure T) [IsFiniteMeasure μ]
    (f : (S × U) → V) :
    condKernel (map κ (fun p ↦ (p.1, f p)) (measurable_of_countable _))
      =ᵐ[μ ⊗ₘ fst κ] snd ((condKernel κ) ⊗ₖ (deterministic (fun x : (T × S) × U ↦ f (x.1.2, x.2))
          (measurable_of_countable _))) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.compProd_apply (measurableSet_singleton _), lintegral_eq_sum_countable] at hx
  simp only [ne_eq, tsum_eq_zero_iff ENNReal.summable, Finset.mem_univ, mul_eq_zero, forall_true_left,
    not_forall] at hx
  obtain ⟨y, hy⟩ := hx
  push_neg at hy
  rw [fst_apply' _ _ (measurable_prod_mk_left (measurableSet_singleton _))] at hy
  simp only [ne_eq, Set.mem_preimage, Set.mem_singleton_iff] at hy
  have hyx1 : y = x.1 := by
    by_contra hy_ne
    refine hy.2 ?_
    rw [← Prod.eta x]
    simp_rw [Prod.mk.inj_iff]
    simp [hy_ne]
  rw [hyx1] at hy
  ext s hs
  rw [snd_apply' _ _ hs, compProd_deterministic_apply]
  swap; · exact measurable_snd hs
  simp only [Set.mem_setOf_eq]
  have h_ne_zero : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0 := by
    refine fun h_zero ↦ hy.2 ?_
    refine measure_mono_null ?_ h_zero
    intro p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    conv_lhs => rw [← Prod.eta x, Prod.mk.inj_iff]
    exact fun h ↦ h.2
  have h_preimage : (fun p ↦ (p.1, f p)) ⁻¹' (Prod.fst ⁻¹' {x.2}) = Prod.fst ⁻¹' {x.2} := by
    ext p; simp
  rw [condKernel_apply' _ _ _ hs, condKernel_apply' _ _ h_ne_zero]
  rotate_left
  · exact (measurable_of_countable f).comp measurable_prod_mk_left hs
  · rw [map_apply' _ _ _ (measurable_fst (measurableSet_singleton _)), h_preimage]
    exact h_ne_zero
  rw [map_apply' _ _ _ (measurable_fst (measurableSet_singleton _)), h_preimage]
  congr
  rw [map_apply' _ _ _ ((measurableSet_singleton _).prod hs)]
  congr
  ext p
  simp only [Set.singleton_prod, Set.mem_preimage, Set.mem_image, Prod.mk.injEq,
    exists_eq_right_right, Set.mem_setOf_eq]
  refine ⟨fun h ↦ ⟨p.2, ?_, ?_⟩, fun ⟨p2, h_mem, h_eq⟩ ↦ ?_⟩
  · rw [h.2, Prod.mk.eta]
    exact h.1
  · rw [h.2, Prod.mk.eta]
  · rw [← h_eq]
    simp [h_mem]

end condKernel

end kernel

section condDistrib

variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

lemma condDistrib_apply' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ]
    (x : T) (hYx : μ (Y ⁻¹' {x}) ≠ 0) {s : Set S} (hs : MeasurableSet s) :
    condDistrib X Y μ x s = (μ (Y ⁻¹' {x}))⁻¹ * μ (Y ⁻¹' {x} ∩ X ⁻¹' s) := by
  rw [condDistrib, Measure.condKernel_apply _ _ hs]
  · rw [fst_map_prod_mk hX, Measure.map_apply hY (measurableSet_singleton _),
      Measure.map_apply (hY.prod_mk hX) ((measurableSet_singleton _).prod hs)]
    congr
  · rwa [fst_map_prod_mk hX, Measure.map_apply hY (measurableSet_singleton _)]

lemma condDistrib_apply (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (x : T) (hYx : μ (Y ⁻¹' {x}) ≠ 0) :
    condDistrib X Y μ x = (μ[|Y ⁻¹' {x}]).map X := by
  ext s hs
  rw [condDistrib_apply' hX hY μ x hYx hs, Measure.map_apply hX hs,
    cond_apply _ (hY (measurableSet_singleton _))]

lemma condDistrib_ae_eq (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
    condDistrib X Y μ =ᵐ[μ.map Y] fun x ↦ (μ[|Y ⁻¹' {x}]).map X := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply hY (measurableSet_singleton _)] at hx
  exact condDistrib_apply hX hY μ x hx

lemma condDistrib_comp (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : S → U) :
    condDistrib (f ∘ X) Y μ
      =ᵐ[μ.map Y] kernel.map (condDistrib X Y μ) f (measurable_of_countable _) := by
  have hf : Measurable f := measurable_of_countable _
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply hY (measurableSet_singleton _)] at hx
  ext s hs
  rw [condDistrib_apply' (hf.comp hX) hY _ _ hx hs, kernel.map_apply' _ _ _ hs,
    condDistrib_apply' hX hY _ _ hx (hf hs), Set.preimage_comp]

lemma condDistrib_fst_of_ne_zero
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) [IsFiniteMeasure μ]
    (u : U) (hu : μ (Z ⁻¹' {u}) ≠ 0) :
    kernel.fst (condDistrib (fun a ↦ (X a, Y a)) Z μ) u
      = condDistrib X Z μ u := by
  ext A hA
  rw [kernel.fst_apply' _ _ hA, condDistrib_apply' (hX.prod_mk hY) hZ _ _ hu]
  swap; · exact measurable_fst hA
  rw [condDistrib_apply' hX hZ _ _ hu hA]
  rfl

lemma condDistrib_fst_ae_eq (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    kernel.fst (condDistrib (fun a ↦ (X a, Y a)) Z μ)
      =ᵐ[μ.map Z] condDistrib X Z μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [condDistrib_fst_of_ne_zero hX hY hZ]
  rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx

lemma condDistrib_snd_of_ne_zero (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] (u : U) (hu : μ (Z ⁻¹' {u}) ≠ 0) :
    kernel.snd (condDistrib (fun a ↦ (X a, Y a)) Z μ) u
      = condDistrib Y Z μ u := by
  ext A hA
  rw [kernel.snd_apply' _ _ hA, condDistrib_apply' (hX.prod_mk hY) hZ _ _ hu]
  swap; · exact measurable_snd hA
  rw [condDistrib_apply' hY hZ _ _ hu hA]
  rfl

lemma condDistrib_snd_ae_eq (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    kernel.snd (condDistrib (fun a ↦ (X a, Y a)) Z μ)
      =ᵐ[μ.map Z] condDistrib Y Z μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [condDistrib_snd_of_ne_zero hX hY hZ]
  rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx

lemma condKernel_condDistrib_ae_eq
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
  kernel.condKernel (condDistrib (fun a ↦ (X a, Y a)) Z μ) =ᵐ[μ.map (fun ω ↦ (Z ω, X ω))]
    condDistrib Y (fun ω ↦ (Z ω, X ω)) μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply (hZ.prod_mk hX) (measurableSet_singleton _)] at hx
  ext A hA
  have hx1 : μ (Z ⁻¹' {x.1}) ≠ 0 := by
    refine fun h_null ↦ hx (measure_mono_null ?_ h_null)
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    rw [← Prod.eta x, Prod.mk.inj_iff] at hω
    exact hω.1
  rw [kernel.condKernel_apply' _ _ _ hA]
  swap
  · rw [condDistrib_apply' (hX.prod_mk hY) hZ _ _ hx1]
    swap
    · exact measurable_fst (measurableSet_singleton _)
    simp only [ne_eq, mul_eq_zero, ENNReal.inv_eq_zero, measure_ne_top μ, false_or]
    convert hx
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    conv_rhs => rw [← Prod.eta x]
    exact Prod.mk.inj_iff.symm
  rw [condDistrib_apply' (hX.prod_mk hY) hZ _ _ hx1]
  swap
  · exact measurable_fst (measurableSet_singleton _)
  rw [condDistrib_apply' (hX.prod_mk hY) hZ _ _ hx1]
  swap
  · exact (measurable_fst (measurableSet_singleton _)).inter (measurable_snd hA)
  rw [condDistrib_apply' hY (hZ.prod_mk hX) _ _ hx hA]
  have : (fun a ↦ (X a, Y a)) ⁻¹' (Prod.fst ⁻¹' {x.2}) = X ⁻¹' {x.2} := by rfl
  simp_rw [this]
  have : (fun a ↦ (X a, Y a)) ⁻¹' ({x.2} ×ˢ A) = X ⁻¹' {x.2} ∩ Y ⁻¹' A := by
    ext y;
    simp only [Set.singleton_prod, Set.mem_preimage, Set.mem_image, Prod.mk.injEq,
      exists_eq_right_right, Set.mem_inter_iff, Set.mem_singleton_iff]
    tauto
  simp_rw [this]
  have : (fun a ↦ (Z a, X a)) ⁻¹' {x} = Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
    conv_lhs => rw [← Prod.eta x, Prod.mk.inj_iff]
  rw [this, ENNReal.mul_inv (Or.inr (measure_ne_top _ _)), inv_inv]
  swap; · left; simp [hx1]
  calc (μ (Z ⁻¹' {x.1})) * (μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2}))⁻¹ *
      ((μ (Z ⁻¹' {x.1}))⁻¹ * μ (Z ⁻¹' {x.1} ∩ (X ⁻¹' {x.2} ∩ Y ⁻¹' A)))
    = (μ (Z ⁻¹' {x.1})) * (μ (Z ⁻¹' {x.1}))⁻¹ * (μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2}))⁻¹ *
      μ (Z ⁻¹' {x.1} ∩ (X ⁻¹' {x.2} ∩ Y ⁻¹' A)) := by
        ring
  _ = (μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2}))⁻¹ * μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2} ∩ Y ⁻¹' A) := by
        rw [ENNReal.mul_inv_cancel hx1 (measure_ne_top _ _), one_mul, Set.inter_assoc]

lemma swap_condDistrib_ae_eq (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    kernel.comap (condDistrib Y (fun a ↦ (X a, Z a)) μ) Prod.swap measurable_swap
      =ᵐ[μ.map (fun ω ↦ (Z ω, X ω))] condDistrib Y (fun ω ↦ (Z ω, X ω)) μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  ext A hA
  rw [kernel.comap_apply']
  have h_swap : (fun a ↦ (X a, Z a)) ⁻¹' {Prod.swap x} = (fun a ↦ (Z a, X a)) ⁻¹' {x} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Prod.eta x, Prod.swap_prod_mk, Prod.mk.inj_iff, Prod.mk.inj_iff, and_comm]
  rw [condDistrib_apply' hY (hX.prod_mk hZ) _ _ _ hA]
  swap; · rwa [Measure.map_apply (hZ.prod_mk hX) (measurableSet_singleton _), ← h_swap] at hx
  rw [condDistrib_apply' hY (hZ.prod_mk hX) _ _ _ hA]
  swap; · rwa [Measure.map_apply (hZ.prod_mk hX) (measurableSet_singleton _)] at hx
  rw [h_swap]

lemma condDistrib_const_unit (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    kernel.condKernel (kernel.const Unit (μ.map (fun ω ↦ (X ω, Y ω))))
      =ᵐ[μ.map (fun ω ↦ ((), X ω))] kernel.prodMkLeft Unit (condDistrib Y X μ) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  have : (fun a ↦ ((), X a)) ⁻¹' {x} = X ⁻¹' {x.2} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Prod.eta x, Prod.mk.inj_iff]
    simp
  rw [Measure.map_apply (measurable_const.prod_mk hX) (measurableSet_singleton _), this] at hx
  ext s hs
  rw [kernel.condKernel_apply' _ _ _ hs]
  swap
  · rw [kernel.const_apply,
      Measure.map_apply (hX.prod_mk hY) (measurable_fst (measurableSet_singleton _))]
    exact hx
  simp_rw [kernel.const_apply,
    Measure.map_apply (hX.prod_mk hY) (measurable_fst (measurableSet_singleton _)),
    Measure.map_apply (hX.prod_mk hY) ((measurableSet_singleton _).prod hs)]
  rw [kernel.prodMkLeft_apply', condDistrib_apply' hY hX _ _ hx hs]
  rfl

lemma condDistrib_unit_right (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    condDistrib X (fun _ ↦ ()) μ = kernel.const Unit (μ.map X) := by
  ext x s hs
  rw [condDistrib_apply' hX measurable_const _ _ _ hs]
  · simp only [Set.mem_singleton_iff, Set.preimage_const_of_mem, measure_univ, inv_one,
      Set.univ_inter, one_mul]
    rw [kernel.const_apply, Measure.map_apply hX hs]
  · simp

lemma map_compProd_condDistrib (hX : Measurable X) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ.map Z ⊗ₘ condDistrib X Z μ = μ.map (fun ω ↦ (Z ω, X ω)) := by
  ext A hA
  rw [Measure.map_apply (hZ.prod_mk hX) hA, Measure.compProd_apply hA, lintegral_eq_sum_countable]
  have : ∑' x : U, μ.map Z {x} * condDistrib X Z μ x (Prod.mk x ⁻¹' A)
      = ∑' x : U, μ (Z ⁻¹' {x} ∩ (fun ω ↦ (x, X ω)) ⁻¹' A) := by
    congr 1 with x
    rw [Measure.map_apply hZ (measurableSet_singleton _)]
    by_cases hx : μ (Z ⁻¹' {x}) = 0
    · simp only [hx, zero_mul, Set.mem_setOf_eq, Set.preimage_setOf_eq]
      exact (measure_mono_null (Set.inter_subset_left _ _) hx).symm
    rw [condDistrib_apply' hX hZ _ _ hx]
    swap; · exact (measurable_prod_mk_left hA)
    rw [← mul_assoc, ENNReal.mul_inv_cancel hx (measure_ne_top _ _), one_mul]
    congr
  rw [this]
  have : (fun a ↦ (Z a, X a)) ⁻¹' A = ⋃ x, Z ⁻¹' {x} ∩ ((fun a ↦ (x, X a)) ⁻¹' A) := by
    ext ω
    simp
  rw [this, measure_iUnion]
  · intro i j hij
    rw [Function.onFun]
    refine Disjoint.mono (Set.inter_subset_left _ _) (Set.inter_subset_left _ _) ?_
    rw [Set.disjoint_iff]
    intro z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      and_imp]
    exact fun hi hj ↦ hij (hi.symm.trans hj)
  intro u
  exact (hZ (measurableSet_singleton _)).inter (measurable_const.prod_mk hX hA)

section Independence

variable {V : Type*} [Countable V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]
  {W : Ω → V}

lemma condDistrib_eq_prod_of_indepFun
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IndepFun (fun ω ↦ (X ω, Z ω)) (fun ω ↦ (Y ω, W ω)) μ) :
    condDistrib (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (Z ω, W ω)) μ
      =ᵐ[μ.map (fun ω ↦ (Z ω, W ω))] kernel.prodMkRight V (condDistrib X Z μ)
        ×ₖ kernel.prodMkLeft U (condDistrib Y W μ) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply (hZ.prod_mk hW) (measurableSet_singleton _)] at hx
  ext s hs
  rw [condDistrib_apply (hX.prod_mk hY) (hZ.prod_mk hW) _ _ hx, kernel.prod_apply' _ _ _ hs]
  simp_rw [kernel.prodMkLeft_apply, kernel.prodMkRight_apply]
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod] at hx
  have hxZ : μ (Z ⁻¹' {x.1}) ≠ 0 := fun h0 ↦ hx (measure_mono_null (Set.inter_subset_left _ _) h0)
  have hxW : μ (W ⁻¹' {x.2}) ≠ 0 := fun h0 ↦ hx (measure_mono_null (Set.inter_subset_right _ _) h0)
  simp_rw [lintegral_eq_sum_countable, condDistrib_apply hX hZ μ _ hxZ,
    condDistrib_apply hY hW μ _ hxW, Measure.map_apply (hX.prod_mk hY) hs]
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod,
    cond_apply _ ((hZ (measurableSet_singleton _)).inter (hW (measurableSet_singleton _)))]
  simp_rw [Measure.map_apply hX (measurableSet_singleton _),
    cond_apply _ (hZ (measurableSet_singleton _))]
  change (μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2}))⁻¹
      * μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2} ∩ (fun a ↦ (X a, Y a)) ⁻¹' s)
    = ∑' x_1, (μ (Z ⁻¹' {x.1}))⁻¹ * μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x_1})
      * ((μ[|W ⁻¹' {x.2}]).map Y) (Prod.mk x_1 ⁻¹' s)
  simp_rw [Measure.map_apply hY (measurable_prod_mk_left hs),
    cond_apply _ (hW (measurableSet_singleton _))]
  have hZW : IndepFun Z W μ := by
    have h' := IndepFun.comp h measurable_snd measurable_snd
    exact h'
  have h_indep1 : (μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2}))⁻¹
      = (μ (Z ⁻¹' {x.1}))⁻¹ * (μ (W ⁻¹' {x.2}))⁻¹ := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul.mp hZW _ _ (measurableSet_singleton _)
      (measurableSet_singleton _), ENNReal.mul_inv (Or.inl hxZ) (Or.inl (measure_ne_top _ _))]
  rw [h_indep1]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]
  congr 1
  simp_rw [← mul_assoc, mul_comm _ (μ (W ⁻¹' {x.2}))⁻¹, mul_assoc, ENNReal.tsum_mul_left]
  congr 1
  have h_Union : (fun ω ↦ (X ω, Y ω)) ⁻¹' s = ⋃ a, ((X ⁻¹' {a}) ∩ (Y ⁻¹' (Prod.mk a ⁻¹' s))) := by
    ext1; simp
  rw [h_Union, Set.inter_iUnion, measure_iUnion]
  rotate_left
  · intro i j hij
    rw [Function.onFun, Set.disjoint_iff]
    intro y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      and_imp]
    exact fun _ _ h3 _ _ _ h7 _ ↦ hij (h3.symm.trans h7)
  · intro b
    refine ((hZ (measurableSet_singleton _)).inter (hW (measurableSet_singleton _))).inter ?_
    exact (hX (measurableSet_singleton _)).inter (hY (measurable_prod_mk_left hs))
  congr with b
  calc μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2} ∩ (X ⁻¹' {b} ∩ Y ⁻¹' (Prod.mk b ⁻¹' s)))
    = μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {b} ∩ (W ⁻¹' {x.2} ∩ Y ⁻¹' (Prod.mk b ⁻¹' s))) := by
        rw [Set.inter_assoc, ← Set.inter_assoc (W ⁻¹' {x.2}), Set.inter_comm (W ⁻¹' {x.2}),
          ← Set.inter_assoc, ← Set.inter_assoc, ← Set.inter_assoc]
  _ = μ ((fun ω ↦ (X ω, Z ω)) ⁻¹' {(b, x.1)}
      ∩ ((fun ω ↦ (Y ω, W ω)) ⁻¹' ((Prod.mk b ⁻¹' s) ×ˢ {x.2}))) := by
        rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod, Set.inter_comm (Z ⁻¹' {x.1}),
          Set.mk_preimage_prod, Set.inter_comm (W ⁻¹' {x.2})]
  _ = μ ((fun ω ↦ (X ω, Z ω)) ⁻¹' {(b, x.1)})
      * μ ((fun ω ↦ (Y ω, W ω)) ⁻¹' ((Prod.mk b ⁻¹' s) ×ˢ {x.2})) := by
        refine indepFun_iff_measure_inter_preimage_eq_mul.mp h _ _ (measurableSet_singleton _) ?_
        exact (measurable_prod_mk_left hs).prod (measurableSet_singleton _)
  _ = μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {b}) * μ (W ⁻¹' {x.2} ∩ Y ⁻¹' (Prod.mk b ⁻¹' s)) := by
        rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod, Set.inter_comm (Z ⁻¹' {x.1}),
          Set.mk_preimage_prod, Set.inter_comm (W ⁻¹' {x.2})]

end Independence

end condDistrib

end ProbabilityTheory


open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators


namespace ProbabilityTheory.kernel

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
 [Countable S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
 [Countable T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
 [Countable U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
 [Countable V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]

lemma _root_.MeasureTheory.Measure.compProd_apply_singleton (μ : Measure T) [SFinite μ]
    (κ : kernel T S) [IsSFiniteKernel κ] (t : T) (s : S) :
    (μ ⊗ₘ κ) {(t, s)} = κ t {s} * μ {t} := by
  rw [Measure.compProd_apply (measurableSet_singleton _)]
  have : ∀ a, κ a (Prod.mk a ⁻¹' {(t, s)}) = ({t} : Set T).indicator (fun _ ↦ κ t {s}) a := by
    intro a
    by_cases ha : a = t
    · simp only [ha, Set.mem_singleton_iff, Set.indicator_of_mem]
      congr
      ext y
      simp
    · simp only [Set.mem_singleton_iff, ha, not_false_eq_true, Set.indicator_of_not_mem]
      suffices Prod.mk a ⁻¹' {(t, s)} = ∅ by simp [this]
      ext y
      simp [ha]
  simp_rw [this]
  rw [lintegral_indicator _ (measurableSet_singleton _)]
  simp

lemma _root_.MeasureTheory.Measure.ae_of_compProd_eq_zero {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} [SFinite μ] {κ : kernel α β} [IsSFiniteKernel κ]
    {s : Set (α × β)} (hs : (μ ⊗ₘ κ) s = 0) :
    ∀ᵐ a ∂μ, κ a (Prod.mk a ⁻¹' s) = 0 := by
  let t := toMeasurable (μ ⊗ₘ κ) s
  have ht : (μ ⊗ₘ κ) t = 0 := by
    unfold_let t
    rwa [measure_toMeasurable]
  rw [Measure.compProd_apply (measurableSet_toMeasurable _ _), lintegral_eq_zero_iff] at ht
  swap; · exact measurable_kernel_prod_mk_left (measurableSet_toMeasurable _ _)
  filter_upwards [ht] with a ha
  refine measure_mono_null ?_ ha
  intro y
  simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage]
  intro hy
  exact subset_toMeasurable (μ ⊗ₘ κ) s hy

lemma _root_.MeasureTheory.Measure.ae_of_ae_compProd {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} [SFinite μ] {κ : kernel α β} [IsSFiniteKernel κ]
    {p : α × β → Prop} (hp : ∀ᵐ x ∂(μ ⊗ₘ κ), p x) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b) := by
  rw [ae_iff] at hp
  have hp' := Measure.ae_of_compProd_eq_zero hp
  filter_upwards [hp'] with a ha
  rw [ae_iff]
  convert ha

lemma compProd_congr [SFinite μ] {κ κ' : kernel T S} [IsMarkovKernel κ] [IsMarkovKernel κ']
    {η η' : kernel (T × S) U} [IsMarkovKernel η] [IsMarkovKernel η']
    (hκ : κ =ᵐ[μ] κ') (hη : η =ᵐ[μ ⊗ₘ κ] η') :
    κ ⊗ₖ η =ᵐ[μ] κ' ⊗ₖ η' := by
  have hη' := Measure.ae_of_ae_compProd hη
  filter_upwards [hκ, hη'] with a haκ haη
  ext s hs
  rw [compProd_apply _ _ _ hs, compProd_apply _ _ _ hs, ← haκ]
  refine lintegral_congr_ae ?_
  filter_upwards [haη] with b hb
  rw [hb]

/-- The analogue of FiniteSupport for probability kernels. -/
noncomputable def FiniteKernelSupport (κ : kernel T S) : Prop :=
  ∀ t, ∃ A : Finset S, κ t Aᶜ = 0

noncomputable def AEFiniteKernelSupport (κ : kernel T S) (μ : Measure T) : Prop :=
  ∀ᵐ t ∂μ, ∃ A : Finset S, κ t Aᶜ = 0

lemma FiniteKernelSupport.aefiniteKernelSupport {κ : kernel T S} (hκ : FiniteKernelSupport κ)
    (μ : Measure T) :
    AEFiniteKernelSupport κ μ :=
  ae_of_all μ hκ

noncomputable
def AEFiniteKernelSupport.mk [hS : Nonempty S] {κ : kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    kernel T S := by
  classical
  exact kernel.piecewise (s := {t | ∃ A : Finset S, κ t Aᶜ = 0}) (by measurability)
    κ (kernel.const _ (Measure.dirac hS.some))

lemma AEFiniteKernelSupport.finiteKernelSupport_mk [hS : Nonempty S] {κ : kernel T S}
    (hκ : AEFiniteKernelSupport κ μ) :
    FiniteKernelSupport hκ.mk := by
  intro t
  classical
  rw [AEFiniteKernelSupport.mk, piecewise_apply]
  split_ifs with ht
  · exact ht
  · refine ⟨{hS.some}, ?_⟩
    simp

lemma AEFiniteKernelSupport.ae_eq_mk {κ : kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    κ =ᵐ[μ] hκ.mk := by
  filter_upwards [hκ] with t ht
  classical
  rw [AEFiniteKernelSupport.mk, kernel.piecewise_apply, if_pos (by exact ht)]

instance AEFiniteKernelSupport.isMarkovKernel_mk [hS : Nonempty S]
    {κ : kernel T S} [IsMarkovKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsMarkovKernel hκ.mk := by
  rw [AEFiniteKernelSupport.mk]
  infer_instance

lemma aefiniteKernelSupport_iff {κ : kernel T S} {μ : Measure T} :
    AEFiniteKernelSupport κ μ ↔ ∃ κ' : kernel T S, FiniteKernelSupport κ' ∧ κ' =ᵐ[μ] κ := by
  refine ⟨fun h ↦ ⟨h.mk, h.finiteKernelSupport_mk, h.ae_eq_mk.symm⟩, fun ⟨κ', hκ', h_eq⟩ ↦ ?_⟩
  filter_upwards [h_eq] with x hx
  rw [← hx]
  exact hκ' x

/-- Finite kernel support locally implies uniform finite kernel support. -/
lemma local_support_of_finiteKernelSupport {κ : kernel T S} (h : FiniteKernelSupport κ) (A : Finset T) :
    ∃ B : Finset S, ∀ t ∈ A, (κ t) Bᶜ = 0 := by
  classical
  use Finset.biUnion A (fun t ↦ (h t).choose)
  intro t ht
  set B := (h t).choose
  refine measure_mono_null ?_ (h t).choose_spec
  intro s; simp
  contrapose!; intro h
  use t

/-- Finite range implies finite kernel support. -/
lemma finiteKernelSupport_of_finite_range [Fintype S] (κ : kernel T S) : FiniteKernelSupport κ := by
  intro t
  use Finset.univ
  simp

/-- Deterministic kernels have finite kernel support.-/
lemma finiteKernelSupport_of_deterministic (f : T × S → U) :
    FiniteKernelSupport (deterministic f (measurable_of_countable f)) := by
  intro (t,s)
  use { f (t,s) }
  rw [kernel.deterministic_apply' (by measurability) _ (by measurability)]
  simp

/-- maps preserve finite kernel support. -/
lemma finiteKernelSupport_of_map {κ : kernel T S} (hκ : FiniteKernelSupport κ)
    {f : S → U} (hf : Measurable f) :
    FiniteKernelSupport (map κ f hf) := by
  intro t
  rcases hκ t with ⟨A, hA⟩
  classical
  use Finset.image f A
  rw [kernel.map_apply' _ _ _ (by measurability)]
  refine measure_mono_null ?_ hA
  intro s; simp; contrapose!; intro hs; use s

lemma AEFiniteKernelSupport.map {κ : kernel T S} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) {f : S → U} (hf : Measurable f) :
    AEFiniteKernelSupport (kernel.map κ f hf) μ := by
  filter_upwards [hκ] with t ⟨A, hA⟩
  classical
  use Finset.image f A
  rw [kernel.map_apply' _ _ _ (by measurability)]
  refine measure_mono_null ?_ hA
  intro s; simp; contrapose!; intro hs; use s

/-- comaps preserve finite kernel support. -/
lemma finiteKernelSupport_of_comap {κ : kernel T S} (hκ : FiniteKernelSupport κ)
    {f : U → T} (hf : Measurable f) :
    FiniteKernelSupport (comap κ f hf) := by
  intro u
  rcases hκ (f u) with ⟨A, hA⟩
  use A
  rwa [kernel.comap_apply]

lemma AEFiniteKernelSupport.comap_equiv {κ : kernel T S} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) (f : U ≃ᵐ T) :
    AEFiniteKernelSupport (kernel.comap κ f f.measurable) (μ.comap f) := by
  rw [← @MeasurableEquiv.map_symm]
  rw [AEFiniteKernelSupport]
  simp_rw [kernel.comap_apply]
  rw [ae_map_iff f.symm.measurable.aemeasurable]
  swap; · measurability
  simp only [MeasurableEquiv.apply_symm_apply]
  exact hκ

/-- Projecting a kernel to first coordinate preserves finite kernel support. -/
lemma finiteKernelSupport_of_fst {κ : kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (fst κ) :=
  finiteKernelSupport_of_map hκ measurable_fst

lemma AEFiniteKernelSupport.fst {κ : kernel T (S × U)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (fst κ) μ :=
  hκ.map measurable_fst

/-- Projecting a kernel to second coordinate preserves finite kernel support. -/
lemma finiteKernelSupport_of_snd {κ : kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (snd κ) :=
  finiteKernelSupport_of_map hκ measurable_snd

lemma AEFiniteKernelSupport.snd {κ : kernel T (S × U)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (snd κ) μ :=
  hκ.map measurable_snd

/-- Conditioning a kernel preserves finite kernel support. -/
lemma aefiniteKernelSupport_of_cond {κ : kernel T (S × U)} [hU: Nonempty U]
    (μ : Measure T) [IsFiniteMeasure μ] (hκ : AEFiniteKernelSupport κ μ) [IsFiniteKernel κ] :
    AEFiniteKernelSupport (condKernel κ) (μ ⊗ₘ (kernel.fst κ)) := by
  rw [AEFiniteKernelSupport, ae_iff_of_countable] at hκ ⊢
  intro (t, s) hts
  simp only [Measure.compProd_apply_singleton, ne_eq, mul_eq_zero] at hts
  push_neg at hts
  rcases hκ t hts.2 with ⟨A, hA⟩
  classical
  use Finset.image Prod.snd A
  rw [condKernel_apply']
  rotate_left
  · rw [kernel.fst_apply' _ _ (measurableSet_singleton _)] at hts
    exact hts.1
  · measurability
  simp only [Finset.coe_image, Set.singleton_prod, mul_eq_zero, ENNReal.inv_eq_zero]
  right
  refine measure_mono_null ?_ hA
  intro x
  simp only [Set.mem_image, Set.mem_compl_iff, Finset.mem_coe, Prod.exists, exists_eq_right,
    not_exists, forall_exists_index, and_imp]
  intro y h hsyx
  rw [← hsyx]
  exact h s

/-- Swapping a kernel right preserves finite kernel support. -/
lemma finiteKernelSupport_of_swapRight {κ : kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (swapRight κ) :=
  finiteKernelSupport_of_map hκ measurable_swap

lemma AEFiniteKernelSupport.swapRight {κ : kernel T (S × U)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (swapRight κ) μ :=
  hκ.map measurable_swap

/-- Products preserve finite kernel support. -/
lemma finiteKernelSupport_of_prod {κ : kernel T S} {η : kernel T U}
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    FiniteKernelSupport (κ ×ₖ η) := by
  intro t
  rcases hκ t with ⟨A, hA⟩
  rcases hη t with ⟨B, hB⟩
  use A ×ˢ B
  rw [kernel.prod_apply' _ _ _ (by measurability)]
  apply lintegral_eq_zero_of_ae_zero hA _ (by measurability)
  intro s hs
  refine measure_mono_null ?_ hB
  intro u; simp; tauto

lemma AEFiniteKernelSupport.prod {κ : kernel T S} {η : kernel T U}
    [IsMarkovKernel κ] [IsMarkovKernel η] {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    AEFiniteKernelSupport (κ ×ₖ η) μ := by
  filter_upwards [hκ, hη] with x ⟨A, hκA⟩ ⟨B, hηB⟩
  use A ×ˢ B
  rw [Finset.coe_product, Set.compl_prod_eq_union, prod_apply, measure_union_null_iff,
    Measure.prod_prod, Measure.prod_prod, hκA, hηB, zero_mul, mul_zero, and_self]

/-- Composition-product preserves finite kernel support -/
lemma finiteKernelSupport_of_compProd {κ : kernel T S} [IsMarkovKernel κ] {η : kernel (T × S) U}
    [IsMarkovKernel η] (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    FiniteKernelSupport (κ ⊗ₖ η) := by
  intro t
  rcases hκ t with ⟨A, hA⟩
  rcases (local_support_of_finiteKernelSupport hη ({t} ×ˢ A)) with ⟨B, hB⟩
  use (A ×ˢ B)
  rw [kernel.compProd_apply _ _ _ (by measurability), lintegral_eq_sum' _ hA]
  apply Finset.sum_eq_zero
  intro s hs
  simp; left
  refine measure_mono_null ?_ (hB (t, s) (by simp [hs]))
  intro u; simp; tauto

lemma AEFiniteKernelSupport.compProd {κ : kernel T S} {η : kernel (T × S) U}
    [IsMarkovKernel κ] [IsMarkovKernel η] {μ : Measure T} [SFinite μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    AEFiniteKernelSupport (κ ⊗ₖ η) μ := by
  rw [aefiniteKernelSupport_iff]
  refine ⟨hκ.mk ⊗ₖ hη.mk, ?_, ?_⟩
  · exact finiteKernelSupport_of_compProd hκ.finiteKernelSupport_mk hη.finiteKernelSupport_mk
  · have h_meas_eq : μ ⊗ₘ hκ.mk = μ ⊗ₘ κ := Measure.compProd_congr hκ.ae_eq_mk.symm
    refine compProd_congr hκ.ae_eq_mk.symm ?_
    convert hη.ae_eq_mk.symm

/-- prodMkRight preserves finite kernel support. -/
lemma finiteKernelSupport_of_prodMkRight {κ : kernel T S} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (prodMkRight U κ) :=
  finiteKernelSupport_of_comap hκ _

protected lemma AEFiniteKernelSupport.prodMkRight {κ : kernel T S} (hκ : AEFiniteKernelSupport κ μ)
    (ν : Measure U) [SFinite ν] :
    AEFiniteKernelSupport (prodMkRight U κ) (μ.prod ν) := by
  rw [aefiniteKernelSupport_iff]
  refine ⟨prodMkRight U hκ.mk, finiteKernelSupport_of_prodMkRight hκ.finiteKernelSupport_mk, ?_⟩
  rw [Filter.EventuallyEq]
  change ∀ᵐ (x : T × U) ∂(μ.prod ν), x ∈ {y | (prodMkRight U (mk hκ)) y = (prodMkRight U κ) y}
  rw [Measure.ae_prod_mem_iff_ae_ae_mem]
  · filter_upwards [hκ.ae_eq_mk] with x hx
    simp [hx]
  · simp only [prodMkRight_apply, measurableSet_setOf]
    exact measurable_of_countable _

/-- prodMkLeft preserves finite kernel support. -/
lemma finiteKernelSupport_of_prodMkLeft {κ : kernel T S} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (prodMkLeft U κ) :=
  finiteKernelSupport_of_comap hκ _

protected lemma AEFiniteKernelSupport.prodMkLeft {κ : kernel T S} (hκ : AEFiniteKernelSupport κ μ)
    (ν : Measure U) [SFinite μ] :
    AEFiniteKernelSupport (prodMkLeft U κ) (ν.prod μ) := by
  rw [aefiniteKernelSupport_iff]
  refine ⟨prodMkLeft U hκ.mk, finiteKernelSupport_of_prodMkLeft hκ.finiteKernelSupport_mk, ?_⟩
  rw [Filter.EventuallyEq]
  change ∀ᵐ (x : U × T) ∂(ν.prod μ), x ∈ {y | prodMkLeft U (mk hκ) y = prodMkLeft U κ y}
  rw [Measure.ae_prod_mem_iff_ae_ae_mem]
  · refine ae_of_all _ (fun y ↦ ?_)
    filter_upwards [hκ.ae_eq_mk] with x hx
    simp [hx]
  · simp only [prodMkRight_apply, measurableSet_setOf]
    exact measurable_of_countable _

end ProbabilityTheory.kernel
