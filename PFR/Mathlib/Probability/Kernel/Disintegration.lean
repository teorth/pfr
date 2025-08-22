import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.CondDistrib
import PFR.Mathlib.Data.Prod.Basic
import PFR.Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import PFR.Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Disintegration of kernels in finite spaces

We can write `κ : Kernel S (T × U)` as a composition-product `(fst κ) ⊗ₖ (condKernel κ)` where
`fst κ : Kernel S T` and `condKernel : Kernel (S × T) U` is defined in this file.

-/

open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace T] [MeasurableSpace U]

namespace Kernel

section condKernel

variable [Countable U] [Nonempty U] [DiscreteMeasurableSpace U]

/-
/-- Kernel such that `κ : Kernel T (S × U)` is equal to `(fst κ) ⊗ₖ (condKernel κ)`. -/
noncomputable
def condKernel (κ : Kernel T (S × U)) [IsFiniteKernel κ] :
    kernel (T × S) U where
  val := fun ts ↦ (κ ts.1).condKernel ts.2
  property := .of_discrete
-/

lemma condKernel_apply (κ : Kernel T (S × U)) [IsFiniteKernel κ] (x : T × S)
    (hx : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0) :
    condKernel κ x = (κ x.1).condKernel x.2 := by
  have h := condKernel_apply_eq_condKernel κ x.1
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h
  refine h x.2 ?_
  rwa [fst_apply' _ _ (.singleton _)]

lemma condKernel_apply' (κ : Kernel T (S × U)) [IsFiniteKernel κ]
    (x : T × S) (hx : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0) (s : Set U) :
    condKernel κ x s
      = (κ x.1 (Prod.fst ⁻¹' {x.2}))⁻¹ * (κ x.1) ({x.2} ×ˢ s) := by
  rw [condKernel_apply _ _ hx, Measure.condKernel_apply_of_ne_zero,
    Measure.fst_apply (.singleton _)]
  rwa [Measure.fst_apply (.singleton _)]

lemma condKernel_compProd_apply' (κ : Kernel T S) [IsFiniteKernel κ]
    (η : Kernel (T × S) U) [IsMarkovKernel η]
    (x : T × S) (hx : κ x.1 {x.2} ≠ 0) {s : Set U} (hs : MeasurableSet s) :
    condKernel (κ ⊗ₖ η) x s = η x s := by
  have hx' : (κ ⊗ₖ η) x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0 := by
    rwa [compProd_preimage_fst (.singleton _)]
  rw [condKernel_apply' _ _ hx', compProd_apply ((measurableSet_singleton _).prod hs),
    Kernel.compProd_apply, lintegral_eq_single _ x.2, lintegral_eq_single _ x.2]
  · simp [Set.preimage_preimage, mul_comm]
    simp [← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top (κ x.1) {x.2})]
  · intro b hb
    rw [Set.eq_empty_of_forall_notMem (s := _ ⁻¹' _) (by simp [hb]), measure_empty]
  · intro b hb
    simp [hb, Set.preimage_preimage]
  · measurability

lemma condKernel_compProd_apply (κ : Kernel T S) [IsFiniteKernel κ]
    (η : Kernel (T × S) U) [IsMarkovKernel η]
    (x : T × S) (hx : κ x.1 {x.2} ≠ 0) :
    condKernel (κ ⊗ₖ η) x = η x := by
  ext s hs
  convert condKernel_compProd_apply' κ η x hx hs

lemma disintegration (κ : Kernel T (S × U)) [IsFiniteKernel κ] :
    κ = (Kernel.fst κ) ⊗ₖ (condKernel κ) := by
  ext x s hs
  rw [compProd_apply hs, lintegral_fst]
  swap; · exact measurable_kernel_prodMk_left' hs x
  rw [lintegral_eq_tsum, ENNReal.tsum_prod']
  change κ x s = ∑' a : S, ∑' b : U, κ x {(a, b)} * condKernel κ (x, a) (Prod.mk a ⁻¹' s)
  simp_rw [ENNReal.tsum_mul_right, ← measure_preimage_fst_singleton_eq_tsum (κ x)]
  have : ∑' a : S, (κ x (Prod.fst ⁻¹' {a})) * condKernel κ (x, a) (Prod.mk a ⁻¹' s)
      = ∑' a : S, κ x (Prod.fst ⁻¹' {a} ∩ {su | (a, su.2) ∈ s}) := by
    congr with a
    by_cases ha : κ x (Prod.fst ⁻¹' {a}) = 0
    · simp only [ha, zero_mul]
      exact (measure_mono_null Set.inter_subset_left ha).symm
    · rw [condKernel_apply' κ _ ha, ← mul_assoc,
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
  · refine fun _ ↦ (measurable_fst (.singleton _)).inter ?_
    exact measurable_prodMk_left.comp measurable_snd hs

variable [Countable T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]

lemma condKernel_compProd_ae_eq
    (κ : Kernel T S) [IsFiniteKernel κ]
    (η : Kernel (T × S) U) [IsMarkovKernel η] (μ : Measure T) [IsFiniteMeasure μ]:
    condKernel (κ ⊗ₖ η) =ᵐ[μ ⊗ₘ κ] η := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [condKernel_compProd_apply]
  rw [Measure.compProd_apply (.singleton _), lintegral_eq_tsum] at hx
  simp only [ne_eq, ENNReal.summable.tsum_eq_zero_iff, mul_eq_zero, not_forall] at hx
  obtain ⟨y, hy⟩ := hx
  push_neg at hy
  classical
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod_right_eq_if] at hy
  simp only [ne_eq, Set.mem_singleton_iff] at hy
  by_cases hyx1 : y = x.1
  · simp only [hyx1, ite_true] at hy
    exact hy.2
  · simp [hyx1] at hy

lemma condKernel_prod_ae_eq (κ : Kernel T S) [IsFiniteKernel κ] {μ}
    (η : Kernel T U) [IsMarkovKernel η] [IsFiniteMeasure μ] :
    condKernel (κ ×ₖ η) =ᵐ[μ ⊗ₘ κ] prodMkRight S η := condKernel_compProd_ae_eq _ _ _

lemma ae_eq_condKernel_of_compProd_eq (κ : Kernel T (S × U)) [IsFiniteKernel κ] {μ}
    (η : Kernel (T × S) U) [IsMarkovKernel η] [IsFiniteMeasure μ] (h : (fst κ) ⊗ₖ η = κ) :
    η =ᵐ[μ ⊗ₘ fst κ] condKernel κ := by
  have : condKernel κ = condKernel ((fst κ) ⊗ₖ η) := by congr; exact h.symm
  rw [this]
  exact (condKernel_compProd_ae_eq _ _ _).symm

lemma condKernel_map_prodMk_left {V : Type*} [Nonempty V] [MeasurableSpace V]
    [DiscreteMeasurableSpace V] [Countable V]
    (κ : Kernel T (S × U)) [IsMarkovKernel κ] (μ : Measure T) [IsFiniteMeasure μ]
    (f : (S × U) → V) :
    condKernel (map κ (fun p ↦ (p.1, f p)))
      =ᵐ[μ ⊗ₘ fst κ] snd ((condKernel κ) ⊗ₖ (deterministic (fun x : (T × S) × U ↦ f (x.1.2, x.2))
          .of_discrete)) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.compProd_apply (.singleton _), lintegral_eq_tsum] at hx
  simp only [ne_eq, ENNReal.summable.tsum_eq_zero_iff, mul_eq_zero, not_forall] at hx
  obtain ⟨y, hy⟩ := hx
  push_neg at hy
  rw [fst_apply' _ _ (measurable_prodMk_left (.singleton _))] at hy
  simp only [ne_eq, Set.mem_preimage, Set.mem_singleton_iff] at hy
  have hyx1 : y = x.1 := by
    by_contra hy_ne
    refine hy.2 ?_
    rw [← Prod.eta x]
    simp_rw [Prod.mk_inj]
    simp [hy_ne]
  rw [hyx1] at hy
  ext s hs
  rw [snd_apply' _ _ hs, compProd_deterministic_apply _ (measurable_snd hs)]
  have h_ne_zero : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0 := by
    refine fun h_zero ↦ hy.2 ?_
    refine measure_mono_null ?_ h_zero
    intro p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    conv_lhs => rw [← Prod.eta x, Prod.mk_inj]
    exact fun h ↦ h.2
  have h_preimage : (fun p ↦ (p.1, f p)) ⁻¹' (Prod.fst ⁻¹' {x.2}) = Prod.fst ⁻¹' {x.2} := by
    ext p; simp
  rw [condKernel_apply' _ _ _, condKernel_apply' _ _ h_ne_zero]; swap
  · rw [map_apply' _ .of_discrete _ (measurable_fst (.singleton _)),
      h_preimage]
    exact h_ne_zero
  rw [map_apply' _ .of_discrete _ (measurable_fst (.singleton _)), h_preimage]
  congr
  rw [map_apply' _ .of_discrete _ ((measurableSet_singleton _).prod hs)]
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

end Kernel

section condDistrib

variable [MeasurableSingletonClass T]
variable [Countable U] [DiscreteMeasurableSpace U]

variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

lemma condDistrib_apply' [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ] (x : T) (hYx : μ (Y ⁻¹' {x}) ≠ 0) {s : Set S} (hs : MeasurableSet s) :
    condDistrib X Y μ x s = (μ (Y ⁻¹' {x}))⁻¹ * μ (Y ⁻¹' {x} ∩ X ⁻¹' s) := by
  rw [condDistrib_apply_of_ne_zero hX]
  · rw [Measure.map_apply hY (.singleton _),
      Measure.map_apply (hY.prodMk hX) ((measurableSet_singleton _).prod hs)]
    congr
  · rwa [Measure.map_apply hY (.singleton _)]

lemma condDistrib_apply [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (x : T) (hYx : μ (Y ⁻¹' {x}) ≠ 0) :
    condDistrib X Y μ x = (μ[|Y ⁻¹' {x}]).map X := by
  ext s hs
  rw [condDistrib_apply' hX hY μ x hYx hs, Measure.map_apply hX hs,
    cond_apply (hY (.singleton _))]

variable [Countable T]

lemma condDistrib_ae_eq [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
    condDistrib X Y μ =ᵐ[μ.map Y] fun x ↦ (μ[|Y ⁻¹' {x}]).map X := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply hY (.singleton _)] at hx
  exact condDistrib_apply hX hY μ x hx

lemma condDistrib_comp [Nonempty S] [Nonempty U]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ] (f : S → U) :
    condDistrib (f ∘ X) Y μ
      =ᵐ[μ.map Y] Kernel.map (condDistrib X Y μ) f := by
  have hf : Measurable f := .of_discrete
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply hY (.singleton _)] at hx
  ext s hs
  rw [condDistrib_apply' (hf.comp hX) hY _ _ hx hs,
    Kernel.map_apply' _ .of_discrete _ hs,
    condDistrib_apply' hX hY _ _ hx (hf hs), Set.preimage_comp]

variable [Nonempty T]

lemma condDistrib_fst_of_ne_zero [Nonempty S]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) [IsFiniteMeasure μ]
    (u : U) (hu : μ (Z ⁻¹' {u}) ≠ 0) :
    Kernel.fst (condDistrib (fun a ↦ (X a, Y a)) Z μ) u
      = condDistrib X Z μ u := by
  ext A hA
  rw [Kernel.fst_apply' _ _ hA, condDistrib_apply' (hX.prodMk hY) hZ _ _ hu]
  swap; · exact measurable_fst hA
  rw [condDistrib_apply' hX hZ _ _ hu hA]
  rfl

lemma condDistrib_fst_ae_eq [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.fst (condDistrib (fun a ↦ (X a, Y a)) Z μ)
      =ᵐ[μ.map Z] condDistrib X Z μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [condDistrib_fst_of_ne_zero hX hY hZ]
  rwa [Measure.map_apply hZ (.singleton _)] at hx

lemma condDistrib_snd_of_ne_zero [Nonempty S]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] (u : U) (hu : μ (Z ⁻¹' {u}) ≠ 0) :
    Kernel.snd (condDistrib (fun a ↦ (X a, Y a)) Z μ) u
      = condDistrib Y Z μ u := by
  ext A hA
  rw [Kernel.snd_apply' _ _ hA, condDistrib_apply' (hX.prodMk hY) hZ _ _ hu]
  swap; · exact measurable_snd hA
  rw [condDistrib_apply' hY hZ _ _ hu hA]
  rfl

lemma condDistrib_snd_ae_eq [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.snd (condDistrib (fun a ↦ (X a, Y a)) Z μ)
      =ᵐ[μ.map Z] condDistrib Y Z μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [condDistrib_snd_of_ne_zero hX hY hZ]
  rwa [Measure.map_apply hZ (.singleton _)] at hx

lemma condKernel_condDistrib_ae_eq [Nonempty S]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
  Kernel.condKernel (condDistrib (fun a ↦ (X a, Y a)) Z μ) =ᵐ[μ.map (fun ω ↦ (Z ω, X ω))]
    condDistrib Y (fun ω ↦ (Z ω, X ω)) μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply (hZ.prodMk hX) (.singleton _)] at hx
  ext A hA
  have hx1 : μ (Z ⁻¹' {x.1}) ≠ 0 := by
    refine fun h_null ↦ hx (measure_mono_null ?_ h_null)
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    rw [← Prod.eta x, Prod.mk_inj] at hω
    exact hω.1
  rw [Kernel.condKernel_apply']
  swap
  · rw [condDistrib_apply' (hX.prodMk hY) hZ _ _ hx1]
    swap
    · exact measurable_fst (.singleton _)
    simp only [ne_eq, mul_eq_zero, ENNReal.inv_eq_zero, measure_ne_top μ, false_or]
    convert hx
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    conv_rhs => rw [← Prod.eta x]
    exact Prod.mk_inj.symm
  rw [condDistrib_apply' (hX.prodMk hY) hZ _ _ hx1]
  swap
  · exact measurable_fst (.singleton _)
  rw [condDistrib_apply' (hX.prodMk hY) hZ _ _ hx1]
  swap
  · exact (measurable_fst (.singleton _)).inter (measurable_snd hA)
  rw [condDistrib_apply' hY (hZ.prodMk hX) _ _ hx hA]
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
    conv_lhs => rw [← Prod.eta x, Prod.mk_inj]
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
    Kernel.comap (condDistrib Y (fun a ↦ (X a, Z a)) μ) Prod.swap measurable_swap
      =ᵐ[μ.map (fun ω ↦ (Z ω, X ω))] condDistrib Y (fun ω ↦ (Z ω, X ω)) μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  ext A hA
  rw [Kernel.comap_apply']
  have h_swap : (fun a ↦ (X a, Z a)) ⁻¹' {Prod.swap x} = (fun a ↦ (Z a, X a)) ⁻¹' {x} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Prod.eta x, Prod.swap_mk, Prod.mk_inj, Prod.mk_inj, and_comm]
  rw [condDistrib_apply' hY (hX.prodMk hZ) _ _ _ hA]
  swap; · rwa [Measure.map_apply (hZ.prodMk hX) (.singleton _), ← h_swap] at hx
  rw [condDistrib_apply' hY (hZ.prodMk hX) _ _ _ hA]
  swap; · rwa [Measure.map_apply (hZ.prodMk hX) (.singleton _)] at hx
  rw [h_swap]

lemma condDistrib_const_unit (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.condKernel (Kernel.const Unit (μ.map (fun ω ↦ (X ω, Y ω))))
      =ᵐ[μ.map (fun ω ↦ ((), X ω))] Kernel.prodMkLeft Unit (condDistrib Y X μ) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  have : (fun a ↦ ((), X a)) ⁻¹' {x} = X ⁻¹' {x.2} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Prod.eta x, Prod.mk_inj]
    simp
  rw [Measure.map_apply (measurable_const.prodMk hX) (.singleton _), this] at hx
  ext s hs
  rw [Kernel.condKernel_apply']
  swap
  · rw [Kernel.const_apply,
      Measure.map_apply (hX.prodMk hY) (measurable_fst (.singleton _))]
    exact hx
  simp_rw [Kernel.const_apply,
    Measure.map_apply (hX.prodMk hY) (measurable_fst (.singleton _)),
    Measure.map_apply (hX.prodMk hY) ((measurableSet_singleton _).prod hs)]
  rw [Kernel.prodMkLeft_apply', condDistrib_apply' hY hX _ _ hx hs]
  rfl

lemma condDistrib_unit_right [Nonempty S]
    (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    condDistrib X (fun _ ↦ ()) μ = Kernel.const Unit (μ.map X) := by
  ext x s hs
  rw [condDistrib_apply' hX measurable_const _ _ _ hs]
  · simp only [Set.mem_singleton_iff, Set.preimage_const_of_mem, measure_univ, inv_one,
      Set.univ_inter, one_mul]
    rw [Kernel.const_apply, Measure.map_apply hX hs]
  · simp

lemma map_compProd_condDistrib [Nonempty S] (hX : Measurable X) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ.map Z ⊗ₘ condDistrib X Z μ = μ.map (fun ω ↦ (Z ω, X ω)) := by
  ext A hA
  rw [Measure.map_apply (hZ.prodMk hX) hA, Measure.compProd_apply hA, lintegral_eq_tsum]
  have : ∑' x : U, μ.map Z {x} * condDistrib X Z μ x (Prod.mk x ⁻¹' A)
      = ∑' x : U, μ (Z ⁻¹' {x} ∩ (fun ω ↦ (x, X ω)) ⁻¹' A) := by
    congr 1 with x
    rw [Measure.map_apply hZ (.singleton _)]
    by_cases hx : μ (Z ⁻¹' {x}) = 0
    · simp [hx, measure_mono_null Set.inter_subset_left hx]
    rw [condDistrib_apply' hX hZ _ _ hx]
    swap; · exact (measurable_prodMk_left hA)
    rw [← mul_assoc, ENNReal.mul_inv_cancel hx (measure_ne_top _ _), one_mul]
    congr
  rw [this]
  have : (fun a ↦ (Z a, X a)) ⁻¹' A = ⋃ x, Z ⁻¹' {x} ∩ ((fun a ↦ (x, X a)) ⁻¹' A) := by
    ext ω
    simp
  rw [this, measure_iUnion]
  · intro i j hij
    rw [Function.onFun]
    refine Disjoint.mono Set.inter_subset_left Set.inter_subset_left ?_
    rw [Set.disjoint_iff]
    intro z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      and_imp]
    exact fun hi hj ↦ hij (hi.symm.trans hj)
  intro u
  exact (hZ (.singleton _)).inter (measurable_const.prodMk hX hA)

section Independence

variable {V : Type*} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
  {W : Ω → V}

lemma condDistrib_eq_prod_of_indepFun [Nonempty S]
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IndepFun (fun ω ↦ (X ω, Z ω)) (fun ω ↦ (Y ω, W ω)) μ) :
    condDistrib (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (Z ω, W ω)) μ
      =ᵐ[μ.map (fun ω ↦ (Z ω, W ω))] Kernel.prodMkRight V (condDistrib X Z μ)
        ×ₖ Kernel.prodMkLeft U (condDistrib Y W μ) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply (hZ.prodMk hW) (.singleton _)] at hx
  ext s hs
  rw [condDistrib_apply (hX.prodMk hY) (hZ.prodMk hW) _ _ hx, Kernel.prod_apply' _ _ _ hs]
  simp_rw [Kernel.prodMkLeft_apply, Kernel.prodMkRight_apply]
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod] at hx
  have hxZ : μ (Z ⁻¹' {x.1}) ≠ 0 := fun h0 ↦ hx (measure_mono_null Set.inter_subset_left h0)
  have hxW : μ (W ⁻¹' {x.2}) ≠ 0 := fun h0 ↦ hx (measure_mono_null Set.inter_subset_right h0)
  simp_rw [lintegral_eq_tsum, condDistrib_apply hX hZ μ _ hxZ,
    condDistrib_apply hY hW μ _ hxW, Measure.map_apply (hX.prodMk hY) hs]
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod,
    cond_apply ((hZ (.singleton _)).inter (hW (.singleton _)))]
  simp_rw [Measure.map_apply hX (.singleton _),
    cond_apply (hZ (.singleton _))]
  change (μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2}))⁻¹
      * μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2} ∩ (fun a ↦ (X a, Y a)) ⁻¹' s)
    = ∑' x_1, (μ (Z ⁻¹' {x.1}))⁻¹ * μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x_1})
      * ((μ[|W ⁻¹' {x.2}]).map Y) (Prod.mk x_1 ⁻¹' s)
  simp_rw [Measure.map_apply hY (measurable_prodMk_left hs),
    cond_apply (hW (.singleton _))]
  have hZW : IndepFun Z W μ := by
    have h' := IndepFun.comp h measurable_snd measurable_snd
    exact h'
  have h_indep1 : (μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2}))⁻¹
      = (μ (Z ⁻¹' {x.1}))⁻¹ * (μ (W ⁻¹' {x.2}))⁻¹ := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul.mp hZW _ _ (.singleton _)
      (.singleton _), ENNReal.mul_inv (Or.inl hxZ) (Or.inl (measure_ne_top _ _))]
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
    refine ((hZ (.singleton _)).inter (hW (.singleton _))).inter ?_
    exact (hX (.singleton _)).inter (hY (measurable_prodMk_left hs))
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
        refine indepFun_iff_measure_inter_preimage_eq_mul.mp h _ _ (.singleton _) ?_
        exact (measurable_prodMk_left hs).prod (.singleton _)
  _ = μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {b}) * μ (W ⁻¹' {x.2} ∩ Y ⁻¹' (Prod.mk b ⁻¹' s)) := by
        rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod, Set.inter_comm (Z ⁻¹' {x.1}),
          Set.mk_preimage_prod, Set.inter_comm (W ⁻¹' {x.2})]

end Independence

end condDistrib

end ProbabilityTheory

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory


namespace ProbabilityTheory.Kernel

variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]

lemma _root_.MeasureTheory.Measure.compProd_apply_singleton
    [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (μ : Measure T) [SFinite μ]
    (κ : Kernel T S) [IsSFiniteKernel κ] (t : T) (s : S) :
    (μ ⊗ₘ κ) {(t, s)} = κ t {s} * μ {t} := by
  rw [Measure.compProd_apply (.singleton _)]
  have : ∀ a, κ a (Prod.mk a ⁻¹' {(t, s)}) = ({t} : Set T).indicator (fun _ ↦ κ t {s}) a := by
    intro a
    by_cases ha : a = t
    · simp only [ha, Set.mem_singleton_iff, Set.indicator_of_mem]
      congr
      ext y
      simp
    · simp only [Set.mem_singleton_iff, ha, not_false_eq_true, Set.indicator_of_notMem]
      suffices Prod.mk a ⁻¹' {(t, s)} = ∅ by simp [this]
      ext y
      simp [ha]
  simp_rw [this]
  rw [lintegral_indicator (.singleton _)]
  simp

lemma _root_.MeasureTheory.Measure.ae_of_compProd_eq_zero {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ]
    {s : Set (α × β)} (hs : (μ ⊗ₘ κ) s = 0) :
    ∀ᵐ a ∂μ, κ a (Prod.mk a ⁻¹' s) = 0 := by
  let t := toMeasurable (μ ⊗ₘ κ) s
  have ht : (μ ⊗ₘ κ) t = 0 := by
    unfold t
    rwa [measure_toMeasurable]
  rw [Measure.compProd_apply (measurableSet_toMeasurable _ _), lintegral_eq_zero_iff] at ht
  swap; · exact measurable_kernel_prodMk_left (measurableSet_toMeasurable _ _)
  filter_upwards [ht] with a ha
  exact measure_mono_null (fun y hy ↦ subset_toMeasurable (μ ⊗ₘ κ) s hy) ha

lemma _root_.MeasureTheory.Measure.ae_of_ae_compProd {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ]
    {p : α × β → Prop} (hp : ∀ᵐ x ∂(μ ⊗ₘ κ), p x) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b) := by
  rw [ae_iff] at hp
  have hp' := Measure.ae_of_compProd_eq_zero hp
  filter_upwards [hp'] with a ha
  rw [ae_iff]
  convert ha

lemma compProd_congr_ae {μ} [SFinite μ] {κ κ' : Kernel T S} [IsSFiniteKernel κ] [IsSFiniteKernel κ']
    {η η' : Kernel (T × S) U} [IsSFiniteKernel η] [IsSFiniteKernel η']
    (hκ : κ =ᵐ[μ] κ') (hη : η =ᵐ[μ ⊗ₘ κ] η') :
    κ ⊗ₖ η =ᵐ[μ] κ' ⊗ₖ η' := by
  have hη' := Measure.ae_of_ae_compProd hη
  filter_upwards [hκ, hη'] with a haκ haη
  ext s hs
  rw [compProd_apply hs, compProd_apply hs, ← haκ]
  refine lintegral_congr_ae ?_
  filter_upwards [haη] with b hb
  rw [hb]

/-- The analogue of FiniteSupport for probability kernels. -/
noncomputable def FiniteKernelSupport (κ : Kernel T S) : Prop :=
  ∀ t, ∃ A : Finset S, κ t Aᶜ = 0

/-- A kernel `κ` has almost everywhere finite support wrt a measure `μ` if, for almost every
point `t`, then `κ t` has finite support. Note that we don't require any uniformity wrt `t`. -/
noncomputable def AEFiniteKernelSupport (κ : Kernel T S) (μ : Measure T) : Prop :=
  ∀ᵐ t ∂μ, ∃ A : Finset S, κ t Aᶜ = 0

lemma FiniteKernelSupport.aefiniteKernelSupport {κ : Kernel T S} (hκ : FiniteKernelSupport κ)
    (μ : Measure T) :
    AEFiniteKernelSupport κ μ :=
  ae_of_all μ hκ

@[simp] lemma finiteKernelSupport_zero : FiniteKernelSupport (0 : Kernel T S) :=
  fun t ↦ ⟨∅, by simp⟩

@[simp] lemma aefiniteKernelSupport_zero {μ} : AEFiniteKernelSupport (0 : Kernel T S) μ :=
  finiteKernelSupport_zero.aefiniteKernelSupport _

section

variable [Countable T] [MeasurableSingletonClass T] {μ : Measure T}

set_option linter.unusedVariables false in
/-- The definition doesn't use `hκ`, but we keep it here still as it doesn't give anything
interesting otherwise. -/
noncomputable
def AEFiniteKernelSupport.mk {μ} {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    Kernel T S := by
  classical
  exact if hS : Nonempty S then
    Kernel.piecewise (s := {t | ∃ A : Finset S, κ t Aᶜ = 0}) (by measurability)
      κ (Kernel.const _ (Measure.dirac hS.some))
  else 0

@[simp] lemma AEFiniteKernelSupport.mk_zero
    {h : AEFiniteKernelSupport (0 : Kernel T S) μ} : h.mk = 0 := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp [mk]
  ext x
  by_cases hx : x ∈ {t | ∃ A : Finset S, (0 : Kernel T S) t Aᶜ = 0} <;>
    simp [AEFiniteKernelSupport.mk, Kernel.piecewise, hS]

@[simp] lemma AEFiniteKernelSupport.mk_eq_zero_of_isEmpty
    [IsEmpty S] {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    hκ.mk = 0 := by
  simp [mk]

open Classical in
lemma AEFiniteKernelSupport.mk_eq
    [hS : Nonempty S] {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    hκ.mk = Kernel.piecewise (s := {t | ∃ A : Finset S, κ t Aᶜ = 0}) (by measurability)
      κ (Kernel.const _ (Measure.dirac hS.some)) := by
  simp [mk, hS]

lemma AEFiniteKernelSupport.finiteKernelSupport_mk [MeasurableSingletonClass S] {κ : Kernel T S}
    (hκ : AEFiniteKernelSupport κ μ) :
    FiniteKernelSupport hκ.mk := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp
  intro t
  classical
  rw [mk_eq, piecewise_apply]
  split_ifs with ht
  · exact ht
  · refine ⟨{hS.some}, ?_⟩
    simp

lemma AEFiniteKernelSupport.ae_eq_mk
    {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    κ =ᵐ[μ] hκ.mk := by
  rcases isEmpty_or_nonempty S with hS | hS
  · filter_upwards with x
    ext s
    simp [Set.eq_empty_of_isEmpty s]
  filter_upwards [hκ] with t ht
  classical
  rw [AEFiniteKernelSupport.mk_eq, Kernel.piecewise_apply, if_pos (by exact ht)]

instance AEFiniteKernelSupport.isMarkovKernel_mk
    {κ : Kernel T S} [IsMarkovKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsMarkovKernel hκ.mk := by
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨fun x ↦ (IsEmpty.false x).elim⟩
  inhabit T
  have : Nonempty S := (κ default).nonempty_of_neZero
  rw [AEFiniteKernelSupport.mk_eq]
  infer_instance

instance AEFiniteKernelSupport.isZeroOrMarkovKernel_mk
    {κ : Kernel T S} [IsZeroOrMarkovKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsZeroOrMarkovKernel hκ.mk := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp only [mk_zero]
    infer_instance
  · infer_instance

instance AEFiniteKernelSupport.isSFiniteKernel_mk
    {κ : Kernel T S} [IsSFiniteKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsSFiniteKernel hκ.mk := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp only [mk_eq_zero_of_isEmpty]; infer_instance
  rw [AEFiniteKernelSupport.mk_eq]
  infer_instance

lemma aefiniteKernelSupport_iff [MeasurableSingletonClass S] {κ : Kernel T S} {μ : Measure T} :
    AEFiniteKernelSupport κ μ ↔ ∃ κ' : Kernel T S, FiniteKernelSupport κ' ∧ κ' =ᵐ[μ] κ := by
  refine ⟨fun h ↦ ⟨h.mk, h.finiteKernelSupport_mk, h.ae_eq_mk.symm⟩, fun ⟨κ', hκ', h_eq⟩ ↦ ?_⟩
  filter_upwards [h_eq] with x hx
  rw [← hx]
  exact hκ' x

end

/-- Finite kernel support locally implies uniform finite kernel support. -/
lemma local_support_of_finiteKernelSupport
    {κ : Kernel T S} (h : FiniteKernelSupport κ) (A : Finset T) :
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
lemma finiteKernelSupport_of_finite_range [Fintype S] (κ : Kernel T S) : FiniteKernelSupport κ := by
  intro t
  use Finset.univ
  simp

/-- Deterministic kernels have finite kernel support.-/
lemma FiniteKernelSupport.deterministic [Countable S] [Countable T]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    (f : T × S → U) :
    FiniteKernelSupport (deterministic f .of_discrete) := by
  intro (t, s)
  use {f (t, s)}
  rw [Kernel.deterministic_apply' (by measurability) _ (by measurability)]
  simp

/-- maps preserve finite kernel support. -/
lemma FiniteKernelSupport.map [MeasurableSingletonClass U]
    {κ : Kernel T S} (hκ : FiniteKernelSupport κ) (f : S → U) :
    FiniteKernelSupport (map κ f) := by
  by_cases hf : Measurable f
  · intro t
    rcases hκ t with ⟨A, hA⟩
    classical
    use Finset.image f A
    rw [Kernel.map_apply' _ hf]
    · refine measure_mono_null ?_ hA
      intro s; simp; contrapose!; intro hs; use s
    · apply MeasurableSet.compl
      apply Set.Finite.measurableSet
      exact Finset.finite_toSet (Finset.image f A)
  · simp [map_of_not_measurable _ hf]

lemma AEFiniteKernelSupport.map [MeasurableSingletonClass U] {κ : Kernel T S} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) {f : S → U} :
    AEFiniteKernelSupport (Kernel.map κ f) μ := by
  by_cases hf : Measurable f
  · filter_upwards [hκ] with t ⟨A, hA⟩
    classical
    use Finset.image f A
    rw [Kernel.map_apply' _ hf]
    · refine measure_mono_null ?_ hA
      intro s; simp; contrapose!; intro hs; use s
    · apply MeasurableSet.compl
      apply Set.Finite.measurableSet
      exact Finset.finite_toSet (Finset.image f A)
  · simp [map_of_not_measurable _ hf]

/-- comaps preserve finite kernel support. -/
lemma FiniteKernelSupport.comap {κ : Kernel T S} (hκ : FiniteKernelSupport κ)
    {f : U → T} (hf : Measurable f) :
    FiniteKernelSupport (comap κ f hf) := by
  intro u
  rcases hκ (f u) with ⟨A, hA⟩
  use A
  rwa [Kernel.comap_apply]

lemma AEFiniteKernelSupport.comap_equiv [Countable U] [MeasurableSingletonClass U]
  {κ : Kernel T S} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) (f : U ≃ᵐ T) :
    AEFiniteKernelSupport (Kernel.comap κ f f.measurable) (μ.comap f) := by
  rw [← @MeasurableEquiv.map_symm]
  rw [AEFiniteKernelSupport]
  simp_rw [Kernel.comap_apply]
  rw [ae_map_iff f.symm.measurable.aemeasurable]
  · simp only [MeasurableEquiv.apply_symm_apply]
    exact hκ
  · measurability

/-- Projecting a kernel to first coordinate preserves finite kernel support. -/
lemma FiniteKernelSupport.fst [MeasurableSingletonClass S]
   {κ : Kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (fst κ) := by
  rw [fst_eq]
  apply hκ.map

lemma AEFiniteKernelSupport.fst [MeasurableSingletonClass S] {κ : Kernel T (S × U)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (fst κ) μ := by
  rw [fst_eq]
  apply hκ.map

/-- Projecting a kernel to second coordinate preserves finite kernel support. -/
lemma FiniteKernelSupport.snd [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (snd κ) := by
  rw [snd_eq]
  apply hκ.map

lemma AEFiniteKernelSupport.snd [MeasurableSingletonClass U] {κ : Kernel T (S × U)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (snd κ) μ := by
  rw [snd_eq]
  apply hκ.map

/-- Conditioning a kernel preserves finite kernel support. -/
lemma aefiniteKernelSupport_of_cond {κ : Kernel T (S × U)} [hU : Nonempty U]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] [Countable U] [Countable S] [Countable T]
    (μ : Measure T) [IsFiniteMeasure μ] (hκ : AEFiniteKernelSupport κ μ) [IsFiniteKernel κ] :
    AEFiniteKernelSupport (condKernel κ) (μ ⊗ₘ (Kernel.fst κ)) := by
  rw [AEFiniteKernelSupport, ae_iff_of_countable] at hκ ⊢
  intro (t, s) hts
  simp [Measure.compProd_apply_singleton, ne_eq, mul_eq_zero] at hts
  push_neg at hts
  rcases hκ t hts.2 with ⟨A, hA⟩
  classical
  use Finset.image Prod.snd A
  rw [condKernel_apply']; swap
  · rw [Kernel.fst_apply' _ _ (.singleton _)] at hts
    exact hts.1
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
lemma FiniteKernelSupport.swapRight
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (swapRight κ) := by
  rw [swapRight_eq]
  apply hκ.map

lemma AEFiniteKernelSupport.swapRight {κ : Kernel T (S × U)} {μ : Measure T}
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (swapRight κ) μ := by
  rw [swapRight_eq]
  apply hκ.map

/-- Products preserve finite kernel support. -/
lemma FiniteKernelSupport.prod {κ : Kernel T S} {η : Kernel T U}
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    FiniteKernelSupport (κ ×ₖ η) := by
  intro t
  rcases hκ t with ⟨A, hA⟩
  rcases hη t with ⟨B, hB⟩
  use A ×ˢ B
  rw [Kernel.prod_apply' _ _ _ (by measurability)]
  apply lintegral_eq_zero_of_ae_zero hA _ (by measurability)
  intro s hs
  refine measure_mono_null ?_ hB
  intro u; simp; tauto

lemma AEFiniteKernelSupport.prod {κ : Kernel T S} {η : Kernel T U}
    [IsMarkovKernel κ] [IsMarkovKernel η] {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    AEFiniteKernelSupport (κ ×ₖ η) μ := by
  filter_upwards [hκ, hη] with x ⟨A, hκA⟩ ⟨B, hηB⟩
  use A ×ˢ B
  rw [Finset.coe_product, Set.compl_prod_eq_union, prod_apply, measure_union_null_iff,
    Measure.prod_prod, Measure.prod_prod, hκA, hηB, zero_mul, mul_zero, and_self]

/-- Composition-product preserves finite kernel support -/
lemma FiniteKernelSupport.compProd [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    {κ : Kernel T S} {η : Kernel (T × S) U}
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    FiniteKernelSupport (κ ⊗ₖ η) := by
  by_cases hκ' : IsSFiniteKernel κ; swap
  · simp [compProd_of_not_isSFiniteKernel_left _ _ hκ']
  by_cases hη' : IsSFiniteKernel η; swap
  · simp [compProd_of_not_isSFiniteKernel_right _ _ hη']
  intro t
  rcases hκ t with ⟨A, hA⟩
  rcases (local_support_of_finiteKernelSupport hη ({t} ×ˢ A)) with ⟨B, hB⟩
  use A ×ˢ B
  rw [Kernel.compProd_apply (by measurability), lintegral_eq_setLIntegral hA,
    setLIntegral_eq_sum]
  apply Finset.sum_eq_zero
  intro s hs
  simp
  right
  refine measure_mono_null ?_ (hB (t, s) (by simp [hs]))
  intro u; simp; tauto

lemma AEFiniteKernelSupport.compProd [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    {κ : Kernel T S} {η : Kernel (T × S) U} {μ : Measure T} [SFinite μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    AEFiniteKernelSupport (κ ⊗ₖ η) μ := by
  by_cases hκ' : IsSFiniteKernel κ; swap
  · simp [compProd_of_not_isSFiniteKernel_left _ _ hκ']
  by_cases hη' : IsSFiniteKernel η; swap
  · simp [compProd_of_not_isSFiniteKernel_right _ _ hη']
  rw [aefiniteKernelSupport_iff]
  refine ⟨hκ.mk ⊗ₖ hη.mk, ?_, ?_⟩
  · exact hκ.finiteKernelSupport_mk.compProd hη.finiteKernelSupport_mk
  · have h_meas_eq : μ ⊗ₘ hκ.mk = μ ⊗ₘ κ := Measure.compProd_congr hκ.ae_eq_mk.symm
    refine compProd_congr_ae hκ.ae_eq_mk.symm ?_
    convert hη.ae_eq_mk.symm

/-- prodMkRight preserves finite kernel support. -/
lemma FiniteKernelSupport.prodMkRight {κ : Kernel T S} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (prodMkRight U κ) :=
  hκ.comap _

protected lemma AEFiniteKernelSupport.prodMkRight [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U] [Countable U] {μ}
    {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ)
    (ν : Measure U) [SFinite ν] :
    AEFiniteKernelSupport (prodMkRight U κ) (μ.prod ν) := by
  rw [aefiniteKernelSupport_iff]
  refine ⟨prodMkRight U hκ.mk, hκ.finiteKernelSupport_mk.prodMkRight, ?_⟩
  rw [Filter.EventuallyEq]
  change ∀ᵐ (x : T × U) ∂(μ.prod ν), x ∈ {y | (prodMkRight U (mk hκ)) y = (prodMkRight U κ) y}
  rw [Measure.ae_prod_mem_iff_ae_ae_mem]
  · filter_upwards [hκ.ae_eq_mk] with x hx
    simp [hx]
  · simp only [prodMkRight_apply, measurableSet_setOf]
    exact .of_discrete

/-- prodMkLeft preserves finite kernel support. -/
lemma FiniteKernelSupport.prodMkLeft {κ : Kernel T S} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (prodMkLeft U κ) :=
  hκ.comap _

protected lemma AEFiniteKernelSupport.prodMkLeft [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U] [Countable U] {μ}
    {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ)
    (ν : Measure U) [SFinite μ] :
    AEFiniteKernelSupport (prodMkLeft U κ) (ν.prod μ) := by
  rw [aefiniteKernelSupport_iff]
  refine ⟨prodMkLeft U hκ.mk, hκ.finiteKernelSupport_mk.prodMkLeft , ?_⟩
  rw [Filter.EventuallyEq]
  change ∀ᵐ (x : U × T) ∂(ν.prod μ), x ∈ {y | prodMkLeft U (mk hκ) y = prodMkLeft U κ y}
  rw [Measure.ae_prod_mem_iff_ae_ae_mem]
  · refine ae_of_all _ fun y ↦ ?_
    filter_upwards [hκ.ae_eq_mk] with x hx
    simp [hx]
  · simpa using .of_discrete

end ProbabilityTheory.Kernel
