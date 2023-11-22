
import PFR.Entropy.MeasureCompProd

/-!
# Disintegration of kernels in finite spaces

We can write `κ : kernel S (T × U)` as a composition-product `(fst κ) ⊗ₖ (condKernel κ)` where
`fst κ : kernel S T` and `condKernel : kernel (S × T) U` is defined in this file.

## Main definitions

* `measureEntropy`: entropy of a measure `μ`, denoted by `Hm[μ]`
* `measureMutualInfo`: mutual information of a measure over a product space, denoted by `Im[μ]`,
  equal to `Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ]`

## Notations

* `Hm[μ] = measureEntropy μ`
* `Im[μ] = measureMutualInfo μ`
-/

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators


namespace ProbabilityTheory

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]

variable {κ : kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}

namespace kernel

section condKernel

/-- An auxiliary definition for `condKernel`. -/
noncomputable
def condKernelAux (κ : kernel T (S × U)) : kernel (T × S) (S × U) where
  val := fun x : T × S ↦ (κ x.1)[|Prod.fst ⁻¹' {x.2}]
  property := measurable_of_countable _

lemma condKernelAux_apply (κ : kernel T (S × U)) (x : T × S) :
    condKernelAux κ x = (κ x.1)[|Prod.fst ⁻¹' {x.2}] := rfl

lemma condKernelAux_apply' (κ : kernel T (S × U)) (x : T × S) (s : Set (S × U)) :
    condKernelAux κ x s
      = ((κ x.1) (Prod.fst ⁻¹' {x.2}))⁻¹ * (κ x.1) (Prod.fst ⁻¹' {x.2} ∩ s) := by
  rw [condKernelAux_apply, cond_apply _ (measurable_fst (measurableSet_singleton _))]

instance (κ : kernel T (S × U)) : IsFiniteKernel (condKernelAux κ) := by
  constructor
  refine ⟨1, ENNReal.one_lt_top, fun x ↦ ?_⟩
  rw [condKernelAux_apply']
  simp
  by_cases hx : (κ x.1) (Prod.fst ⁻¹' {x.2}) = 0
  · simp [hx]
  by_cases hx' : (κ x.1) (Prod.fst ⁻¹' {x.2}) = ∞
  · simp [hx']
  rw [ENNReal.inv_mul_cancel hx hx']

/-- Kernel such that `κ : kernel T (S × U)` is equal to `(fst κ) ⊗ₖ (condKernel κ)`.
We define it using `kernel.piecewise` to ensure it is always a Markov kernel, which would otherwise
not be the case for `x : T × S` such that `κ x.1 (Prod.fst ⁻¹' {x.2}) = 0`. -/
noncomputable
def condKernel [hU : Nonempty U] (κ : kernel T (S × U)) : kernel (T × S) U :=
  kernel.piecewise (s := {x | κ x.1 (Prod.fst ⁻¹' {x.2}) = 0})
    (measurable_of_countable _ (measurableSet_singleton _))
    (kernel.deterministic (fun _ ↦ hU.some) measurable_const)
    (kernel.map (condKernelAux κ) Prod.snd measurable_snd)

variable [hU : Nonempty U]

lemma condKernel_apply (κ : kernel T (S × U)) (x : T × S) :
  condKernel κ x = if (κ x.1 (Prod.fst ⁻¹' {x.2}) = 0)
    then Measure.dirac hU.some else ((κ x.1)[|Prod.fst ⁻¹' {x.2}]).map Prod.snd := rfl

lemma condKernel_apply_of_eq_zero (κ : kernel T (S × U)) (x : T × S)
    (hx : κ x.1 (Prod.fst ⁻¹' {x.2}) = 0) :
    condKernel κ x = Measure.dirac hU.some :=
  if_pos hx

lemma condKernel_apply_of_ne_zero (κ : kernel T (S × U)) (x : T × S)
    (hx : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0) :
    condKernel κ x = ((κ x.1)[|Prod.fst ⁻¹' {x.2}]).map Prod.snd :=
  if_neg hx

lemma condKernel_apply' (κ : kernel T (S × U)) (x : T × S) (hx : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0)
    {s : Set U} (hs : MeasurableSet s) :
    condKernel κ x s
      = ((κ x.1) (Prod.fst ⁻¹' {x.2}))⁻¹ * (κ x.1) (Prod.fst ⁻¹' {x.2} ∩ Prod.snd ⁻¹' s) := by
  rw [condKernel_apply_of_ne_zero _ _ hx, Measure.map_apply measurable_snd hs,
    cond_apply _ (measurable_fst (measurableSet_singleton _))]

lemma condKernel_compProd_apply' (κ : kernel T S) [IsFiniteKernel κ]
    (η : kernel (T × S) U) [IsMarkovKernel η]
    (x : T × S) (hx : κ x.1 {x.2} ≠ 0) {s : Set U} (hs : MeasurableSet s) :
    condKernel (κ ⊗ₖ η) x s = η x s := by
  have hx' : (κ ⊗ₖ η) x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0 := by
    rwa [compProd_preimage_fst _ _ (measurableSet_singleton _)]
  rw [condKernel_apply' _ _ hx' hs,
    compProd_apply _ _ _ (measurable_fst (measurableSet_singleton _))]
  simp only [Set.mem_preimage, Set.mem_singleton_iff, lintegral_eq_sum]
  rw [Finset.sum_eq_single x.2 _ (by simp)]
  swap
  · simp only [Finset.mem_univ, ne_eq, mul_eq_zero, forall_true_left]
    intro b hb
    simp [hb]
  rw [compProd_apply _ _ _
    (((measurable_fst (measurableSet_singleton _))).inter (measurable_snd hs)), lintegral_eq_sum]
  simp only [Prod.mk.eta, Set.setOf_true, measure_univ, mul_one, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]
  rw [Finset.sum_eq_single x.2 _ (by simp)]
  swap
  · simp only [Finset.mem_univ, ne_eq, mul_eq_zero, forall_true_left]
    intro b hb
    simp [hb]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top _ _), one_mul]
  simp

lemma condKernel_compProd_apply (κ : kernel T S) [IsFiniteKernel κ]
    (η : kernel (T × S) U) [IsMarkovKernel η]
    (x : T × S) (hx : κ x.1 {x.2} ≠ 0) :
    condKernel (κ ⊗ₖ η) x = η x := by
  ext s hs
  exact condKernel_compProd_apply' κ η x hx hs

lemma condKernel_compProd_ae_eq (κ : kernel T S) [IsFiniteKernel κ]
    (η : kernel (T × S) U) [IsMarkovKernel η] (μ : Measure T) [IsFiniteMeasure μ] :
    condKernel (κ ⊗ₖ η) =ᵐ[μ ⊗ₘ κ] η := by
  rw [Filter.EventuallyEq, ae_iff_of_fintype]
  intro x hx
  rw [condKernel_compProd_apply]
  rw [Measure.compProd_apply _ _ (measurableSet_singleton _), lintegral_eq_sum] at hx
  simp only [Set.mem_singleton_iff, ne_eq, Finset.sum_eq_zero_iff, Finset.mem_univ, mul_eq_zero,
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
    condKernel (κ ×ₖ η) =ᵐ[μ ⊗ₘ κ] prodMkRight η S := condKernel_compProd_ae_eq _ _ _

instance (κ : kernel T (S × U)) : IsFiniteKernel (condKernel κ) := by
  rw [condKernel]; infer_instance

instance (κ : kernel T (S × U)) [IsMarkovKernel κ] : IsMarkovKernel (condKernel κ) := by
  constructor
  intro a
  rw [condKernel_apply]
  split_ifs with h
  · infer_instance
  · constructor
    rw [Measure.map_apply measurable_snd MeasurableSet.univ,
      cond_apply _ (measurable_fst (measurableSet_singleton _))]
    simp only [Set.preimage_univ, Set.inter_univ]
    rw [ENNReal.inv_mul_cancel h (measure_ne_top _ _)]

lemma disintegration (κ : kernel T (S × U)) [IsFiniteKernel κ] :
    κ = (kernel.fst κ) ⊗ₖ (condKernel κ) := by
  ext x s hs
  rw [compProd_apply _ _ _ hs, lintegral_fst]
  swap; · exact measurable_kernel_prod_mk_left' hs x
  rw [lintegral_eq_sum, Fintype.sum_prod_type]
  change κ x s = ∑ a : S, ∑ b : U, κ x {(a, b)} * condKernel κ (x, a) (Prod.mk a ⁻¹' s)
  simp_rw [← Finset.sum_mul, ← measure_preimage_fst_singleton_eq_sum (κ x)]
  have : ∑ a : S, (κ x (Prod.fst ⁻¹' {a})) * condKernel κ (x, a) (Prod.mk a ⁻¹' s)
      = ∑ a : S, κ x (Prod.fst ⁻¹' {a} ∩ {su | (a, su.2) ∈ s}) := by
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
  · rw [tsum_eq_sum]
    simp
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
  conv_rhs => rw [← h]
  exact (condKernel_compProd_ae_eq _ _ _).symm

lemma condKernel_map_prod_mk_left {V : Type*} [Nonempty V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
    (κ : kernel T (S × U)) [IsMarkovKernel κ] (μ : Measure T) [IsFiniteMeasure μ]
    (f : (S × U) → V) :
    condKernel (map κ (fun p ↦ (p.1, f p)) (measurable_of_finite _))
      =ᵐ[μ ⊗ₘ fst κ] snd ((condKernel κ) ⊗ₖ (deterministic (fun x : (T × S) × U ↦ f (x.1.2, x.2))
          (measurable_of_finite _))) := by
  rw [Filter.EventuallyEq, ae_iff_of_fintype]
  intro x hx
  rw [Measure.compProd_apply _ _ (measurableSet_singleton _), lintegral_eq_sum] at hx
  simp only [ne_eq, Finset.sum_eq_zero_iff, Finset.mem_univ, mul_eq_zero, forall_true_left,
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
  · exact (measurable_of_finite f).comp measurable_prod_mk_left hs
  · rw [map_apply' _ _ _ (measurable_fst (measurableSet_singleton _)), h_preimage]
    exact h_ne_zero
  rw [map_apply' _ _ _ (measurable_fst (measurableSet_singleton _)), h_preimage]
  congr
  rw [map_apply' _ _ _ (((measurable_fst (measurableSet_singleton _))).inter (measurable_snd hs))]
  congr
  ext p
  simp only [Set.preimage_inter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.preimage_setOf_eq, Set.mem_setOf_eq, and_congr_right_iff]
  intro h_eq
  simp [h_eq.symm]

end condKernel

end kernel

section condEntropyKernel

variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

noncomputable
def condEntropyKernel (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    kernel T S :=
  kernel.comap
    (kernel.condKernel (kernel.const Unit (μ.map (fun ω ↦ (Y ω, X ω)))))
    (Prod.mk ()) measurable_prod_mk_left

lemma isMarkovKernel_condEntropyKernel (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsMarkovKernel (condEntropyKernel X Y μ) := by
  rw [condEntropyKernel]
  have : IsProbabilityMeasure (μ.map (fun ω ↦ (Y ω, X ω))) :=
    isProbabilityMeasure_map (hY.prod_mk hX).aemeasurable
  infer_instance

lemma condEntropyKernel_apply' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    (x : T) (hYx : μ (Y ⁻¹' {x}) ≠ 0) {s : Set S} (hs : MeasurableSet s) :
    condEntropyKernel X Y μ x s = (μ (Y ⁻¹' {x}))⁻¹ * μ (Y ⁻¹' {x} ∩ X ⁻¹' s) := by
  rw [condEntropyKernel, kernel.comap_apply', kernel.condKernel_apply' _ _ _ hs]
  · rw [kernel.const_apply,
      Measure.map_apply (hY.prod_mk hX) (measurable_fst (measurableSet_singleton _)),
      Measure.map_apply (hY.prod_mk hX)
        ((measurable_fst (measurableSet_singleton _)).inter (measurable_snd hs))]
    have : (fun a ↦ (Y a, X a)) ⁻¹' (Prod.fst ⁻¹' {x}) = Y ⁻¹' {x} := rfl
    rw [this]
    have : (fun a ↦ (Y a, X a)) ⁻¹' (Prod.fst ⁻¹' {x} ∩ Prod.snd ⁻¹' s) = Y ⁻¹' {x} ∩ X ⁻¹' s := by
      ext a
      simp
    rw [this]
  · rw [kernel.const_apply,
      Measure.map_apply (hY.prod_mk hX) (measurable_fst (measurableSet_singleton _))]
    exact hYx

lemma condEntropyKernel_apply (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    (x : T) (hYx : μ (Y ⁻¹' {x}) ≠ 0) :
    condEntropyKernel X Y μ x = (μ[|Y ⁻¹' {x}]).map X := by
  ext s hs
  rw [condEntropyKernel_apply' hX hY μ x hYx hs, Measure.map_apply hX hs,
    cond_apply _ (hY (measurableSet_singleton _))]

lemma condEntropyKernel_comp (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) (f : S → U) :
    condEntropyKernel (f ∘ X) Y μ
      =ᵐ[μ.map Y] kernel.map (condEntropyKernel X Y μ) f (measurable_of_finite _) := by
  have hf : Measurable f := measurable_of_finite _
  rw [Filter.EventuallyEq, ae_iff_of_fintype]
  intro x hx
  rw [Measure.map_apply hY (measurableSet_singleton _)] at hx
  ext s hs
  rw [condEntropyKernel_apply' (hf.comp hX) hY _ _ hx hs, kernel.map_apply' _ _ _ hs,
    condEntropyKernel_apply' hX hY _ _ hx (hf hs), Set.preimage_comp]

lemma condEntropyKernel_fst_of_ne_zero
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) (u : U)
    (hu : μ (Z ⁻¹' {u}) ≠ 0) :
    kernel.fst (condEntropyKernel (fun a ↦ (X a, Y a)) Z μ) u
      = condEntropyKernel X Z μ u := by
  ext A hA
  rw [kernel.fst_apply' _ _ hA, condEntropyKernel_apply' (hX.prod_mk hY) hZ _ _ hu]
  swap; · exact measurable_fst hA
  rw [condEntropyKernel_apply' hX hZ _ _ hu hA]
  rfl

lemma condEntropyKernel_fst_ae_eq
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) :
    kernel.fst (condEntropyKernel (fun a ↦ (X a, Y a)) Z μ)
      =ᵐ[μ.map Z] condEntropyKernel X Z μ := by
  rw [Filter.EventuallyEq, ae_iff_of_fintype]
  intro x hx
  rw [condEntropyKernel_fst_of_ne_zero hX hY hZ]
  rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx

lemma condEntropyKernel_snd_of_ne_zero
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) (u : U)
    (hu : μ (Z ⁻¹' {u}) ≠ 0) :
    kernel.snd (condEntropyKernel (fun a ↦ (X a, Y a)) Z μ) u
      = condEntropyKernel Y Z μ u := by
  ext A hA
  rw [kernel.snd_apply' _ _ hA, condEntropyKernel_apply' (hX.prod_mk hY) hZ _ _ hu]
  swap; · exact measurable_snd hA
  rw [condEntropyKernel_apply' hY hZ _ _ hu hA]
  rfl

lemma condEntropyKernel_snd_ae_eq
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) :
    kernel.snd (condEntropyKernel (fun a ↦ (X a, Y a)) Z μ)
      =ᵐ[μ.map Z] condEntropyKernel Y Z μ := by
  rw [Filter.EventuallyEq, ae_iff_of_fintype]
  intro x hx
  rw [condEntropyKernel_snd_of_ne_zero hX hY hZ]
  rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx

lemma condKernel_condEntropyKernel_ae_eq
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
  kernel.condKernel (condEntropyKernel (fun a ↦ (X a, Y a)) Z μ) =ᵐ[μ.map (fun ω ↦ (Z ω, X ω))]
    condEntropyKernel Y (fun ω ↦ (Z ω, X ω)) μ := by
  rw [Filter.EventuallyEq, ae_iff_of_fintype]
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
  · rw [condEntropyKernel_apply' (hX.prod_mk hY) hZ _ _ hx1]
    swap
    · exact measurable_fst (measurableSet_singleton _)
    simp only [ne_eq, mul_eq_zero, ENNReal.inv_eq_zero, measure_ne_top μ, false_or]
    convert hx
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    conv_rhs => rw [← Prod.eta x]
    exact Prod.mk.inj_iff.symm
  rw [condEntropyKernel_apply' (hX.prod_mk hY) hZ _ _ hx1]
  swap
  · exact measurable_fst (measurableSet_singleton _)
  rw [condEntropyKernel_apply' (hX.prod_mk hY) hZ _ _ hx1]
  swap
  · exact (measurable_fst (measurableSet_singleton _)).inter (measurable_snd hA)
  rw [condEntropyKernel_apply' hY (hZ.prod_mk hX) _ _ hx hA]
  simp only [Set.preimage_inter]
  have : (fun a ↦ (X a, Y a)) ⁻¹' (Prod.fst ⁻¹' {x.2}) = X ⁻¹' {x.2} := by
    rfl
  simp_rw [this]
  have : (fun a ↦ (X a, Y a)) ⁻¹' (Prod.snd ⁻¹' A) = Y ⁻¹' A := rfl
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

lemma swap_condEntropyKernel_ae_eq
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) :
    kernel.comap (condEntropyKernel Y (fun a ↦ (X a, Z a)) μ) Prod.swap measurable_swap
      =ᵐ[μ.map (fun ω ↦ (Z ω, X ω))] condEntropyKernel Y (fun ω ↦ (Z ω, X ω)) μ := by
  rw [Filter.EventuallyEq, ae_iff_of_fintype]
  intro x hx
  ext A hA
  rw [kernel.comap_apply']
  have h_swap : (fun a ↦ (X a, Z a)) ⁻¹' {Prod.swap x} = (fun a ↦ (Z a, X a)) ⁻¹' {x} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Prod.eta x, Prod.swap_prod_mk, Prod.mk.inj_iff, Prod.mk.inj_iff, and_comm]
  rw [condEntropyKernel_apply' hY (hX.prod_mk hZ) _ _ _ hA]
  swap; · rwa [Measure.map_apply (hZ.prod_mk hX) (measurableSet_singleton _), ← h_swap] at hx
  rw [condEntropyKernel_apply' hY (hZ.prod_mk hX) _ _ _ hA]
  swap; · rwa [Measure.map_apply (hZ.prod_mk hX) (measurableSet_singleton _)] at hx
  rw [h_swap]

lemma condEntropyKernel_const_unit
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    kernel.condKernel (kernel.const Unit (μ.map (fun ω ↦ (X ω, Y ω))))
      =ᵐ[μ.map (fun ω ↦ ((), X ω))] kernel.prodMkLeft Unit (condEntropyKernel Y X μ) := by
  rw [Filter.EventuallyEq, ae_iff_of_fintype]
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
    Measure.map_apply (hX.prod_mk hY)
      ((measurable_fst (measurableSet_singleton _)).inter (measurable_snd hs))]
  rw [kernel.prodMkLeft_apply', condEntropyKernel_apply' hY hX _ _ hx hs]
  rfl

lemma map_compProd_condEntropyKernel
    (hX : Measurable X) (hZ : Measurable Z) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ.map Z ⊗ₘ condEntropyKernel X Z μ = μ.map (fun ω ↦ (Z ω, X ω)) := by
  have := isMarkovKernel_condEntropyKernel hX hZ μ
  ext A hA
  rw [Measure.map_apply (hZ.prod_mk hX) hA, Measure.compProd_apply _ _ hA, lintegral_eq_sum]
  have : ∑ x : U, μ.map Z {x} * condEntropyKernel X Z μ x (Prod.mk x ⁻¹' A)
      = ∑ x : U, μ (Z ⁻¹' {x} ∩ (fun ω ↦ (x, X ω)) ⁻¹' A) := by
    congr 1 with x
    rw [Measure.map_apply hZ (measurableSet_singleton _)]
    by_cases hx : μ (Z ⁻¹' {x}) = 0
    · simp only [hx, zero_mul, Set.mem_setOf_eq, Set.preimage_setOf_eq]
      exact (measure_mono_null (Set.inter_subset_left _ _) hx).symm
    rw [condEntropyKernel_apply' hX hZ _ _ hx]
    swap; · exact (measurable_prod_mk_left hA)
    rw [← mul_assoc, ENNReal.mul_inv_cancel hx (measure_ne_top _ _), one_mul]
    congr
  rw [this]
  have : (fun a ↦ (Z a, X a)) ⁻¹' A = ⋃ x, Z ⁻¹' {x} ∩ ((fun a ↦ (x, X a)) ⁻¹' A) := by
    ext ω
    simp
  rw [this, measure_iUnion]
  rotate_left
  · intro i j hij
    rw [Function.onFun]
    refine Disjoint.mono (Set.inter_subset_left _ _) (Set.inter_subset_left _ _) ?_
    rw [Set.disjoint_iff]
    intro z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      and_imp]
    exact fun hi hj ↦ hij (hi.symm.trans hj)
  · intro u
    exact (hZ (measurableSet_singleton _)).inter (measurable_const.prod_mk hX hA)
  rw [tsum_eq_sum]
  simp

end condEntropyKernel

end ProbabilityTheory
