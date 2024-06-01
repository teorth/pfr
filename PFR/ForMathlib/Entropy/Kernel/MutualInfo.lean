import PFR.Mathlib.MeasureTheory.MeasurableSpace.Basic
import PFR.Mathlib.Probability.Kernel.Composition
import PFR.ForMathlib.Entropy.Kernel.Basic

/-!
# Mutual Information of kernels

## Main definitions

* `mutualInfo`: Mutual information of a kernel `κ` into a product space with respect to a
  measure `μ`. This is denoted by `Ik[κ, μ]` and is equal to
  `Hk[fst κ, μ] + Hk[snd κ, μ] - Hk[κ, μ]`.

## Main statements

* `mutualInfo_nonneg`: `Ik[κ, μ]` is nonnegative
* `entropy_condKernel_le_entropy_fst` and `entropy_condKernel_le_entropy_snd`: conditioning
  reduces entropy.

## Notations

* `Ik[κ, μ] = kernel.entropy κ μ`

-/

open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

namespace ProbabilityTheory.kernel

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Nonempty S] [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Nonempty T] [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Nonempty U] [Countable U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Nonempty V] [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
  {κ : kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}

/-- Mutual information of a kernel into a product space with respect to a measure. -/
noncomputable
def mutualInfo (κ : kernel T (S × U)) (μ : Measure T) : ℝ :=
  Hk[fst κ, μ] + Hk[snd κ, μ] - Hk[κ, μ]

/-- Mutual information of a kernel into a product space with respect to a measure. -/
notation3:100 "Ik[" κ " , " μ "]" => kernel.mutualInfo κ μ

lemma mutualInfo_def (κ : kernel T (S × U)) (μ : Measure T) :
    Ik[κ, μ] = Hk[fst κ, μ] + Hk[snd κ, μ] - Hk[κ, μ] := rfl

@[simp]
lemma mutualInfo_zero_measure (κ : kernel T (S × U)) : Ik[κ, (0 : Measure T)] = 0 := by
  simp [mutualInfo]

@[simp]
lemma mutualInfo_zero_kernel (μ : Measure T) : Ik[(0 : kernel T (S × U)), μ] = 0 := by
  simp [mutualInfo]

lemma mutualInfo_congr {κ η : kernel T (S × U)} {μ : Measure T} (h : κ =ᵐ[μ] η) :
    Ik[κ, μ] = Ik[η, μ] := by
  rw [mutualInfo, mutualInfo]
  have h1 : fst κ =ᵐ[μ] fst η := by
    filter_upwards [h] with t ht
    rw [fst_apply, ht, fst_apply]
  have h2 : snd κ =ᵐ[μ] snd η := by
    filter_upwards [h] with t ht
    rw [snd_apply, ht, snd_apply]
  rw [entropy_congr h1, entropy_congr h2, entropy_congr h]

lemma mutualInfo_compProd {κ : kernel T S} [IsMarkovKernel κ]
    {η : kernel (T × S) U} [IsMarkovKernel η] {μ : Measure T} [IsProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η (μ ⊗ₘ κ)):
    Ik[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[snd (κ ⊗ₖ η), μ] - Hk[κ ⊗ₖ η, μ] := by
  rw [mutualInfo, entropy_compProd hκ hη, fst_compProd]

lemma mutualInfo_eq_snd_sub {κ : kernel T (S × U)} [IsMarkovKernel κ]
    {μ : Measure T} [IsProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Ik[κ, μ] = Hk[snd κ, μ] - Hk[condKernel κ, μ ⊗ₘ (fst κ)]  := by
  rw [mutualInfo, chain_rule hκ]
  ring

lemma mutualInfo_eq_fst_sub {κ : kernel T (S × U)} [IsMarkovKernel κ]
    {μ : Measure T} [IsProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Ik[κ, μ] = Hk[fst κ, μ] - Hk[condKernel (swapRight κ), μ ⊗ₘ (snd κ)] := by
  rw [mutualInfo, chain_rule' hκ]
  ring

@[simp]
lemma mutualInfo_prod {κ : kernel T S} {η : kernel T U} [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure T) [IsProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη: AEFiniteKernelSupport η μ) :
    Ik[κ ×ₖ η, μ] = 0 := by
  rw [mutualInfo, snd_prod, fst_prod, entropy_prod hκ hη, sub_self]

@[simp]
lemma mutualInfo_swapRight (κ : kernel T (S × U)) (μ : Measure T) :
    Ik[swapRight κ, μ] = Ik[κ, μ] := by
  rw [mutualInfo, fst_swapRight, snd_swapRight, entropy_swapRight, add_comm]
  rfl

lemma mutualInfo_nonneg' {κ : kernel T (S × U)} {μ : Measure T} [IsFiniteMeasure μ]
    [FiniteSupport μ] (hκ : FiniteKernelSupport κ) :
    0 ≤ Ik[κ, μ] := by
  simp_rw [mutualInfo, entropy, integral_eq_sum' _ (measure_compl_support μ),
    smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg (fun x _ ↦ ?_)
  by_cases hx : μ {x} = 0
  · simp [hx]
  rw [← mul_add, ← mul_sub]
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  rw [fst_apply, snd_apply]
  have : FiniteSupport (κ x) := ⟨hκ x⟩
  exact measureMutualInfo_nonneg

lemma mutualInfo_nonneg {κ : kernel T (S × U)} {μ : Measure T} [IsFiniteMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    0 ≤ Ik[κ, μ] := by
  rw [mutualInfo_congr hκ.ae_eq_mk]
  exact mutualInfo_nonneg' hκ.finiteKernelSupport_mk

lemma entropy_condKernel_le_entropy_fst (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[condKernel (swapRight κ), μ ⊗ₘ (snd κ)] ≤ Hk[fst κ, μ] := by
  rw [← sub_nonneg, ← mutualInfo_eq_fst_sub hκ]
  exact mutualInfo_nonneg hκ

lemma entropy_condKernel_le_entropy_snd {κ : kernel T (S × U)} [IsMarkovKernel κ]
    {μ : Measure T} [IsProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[condKernel κ, μ ⊗ₘ (fst κ)] ≤ Hk[snd κ, μ] := by
  rw [← sub_nonneg, ← mutualInfo_eq_snd_sub hκ]
  exact mutualInfo_nonneg hκ

-- TODO: extract lemma(s) from this:
lemma entropy_snd_sub_mutualInfo_le_entropy_map_of_injective {V : Type*} [Nonempty V] [Countable V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (κ : kernel T (S × U)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ]
    (f : S × U → V) (hfi : ∀ x, Injective (fun y ↦ f (x, y))) [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[snd κ, μ] - Ik[κ, μ] ≤ Hk[map κ f (measurable_of_countable f), μ] := by
  rw [mutualInfo_eq_snd_sub hκ]
  have hf : Measurable f := measurable_of_countable f
  ring_nf
  calc
    Hk[condKernel κ, μ ⊗ₘ fst κ] = Hk[snd ((condKernel κ) ⊗ₖ (deterministic (fun x : (T × S) × U ↦ f (x.1.2, x.2)) (measurable_of_countable _))), μ ⊗ₘ fst κ] := by
      symm
      apply entropy_snd_compProd_deterministic_of_injective
      simpa
    _ = Hk[condKernel (map κ (fun p ↦ (p.1, f p)) (measurable_fst.prod_mk hf)),
      μ ⊗ₘ fst κ] := entropy_congr (condKernel_map_prod_mk_left κ μ f).symm
    _ = Hk[condKernel (map κ (fun p ↦ (p.1, f p)) (measurable_fst.prod_mk hf)),
      μ ⊗ₘ fst (map κ (fun p ↦ (p.1, f p)) (measurable_fst.prod_mk hf))] := by
        congr 2 with x
        rw [fst_map_prod _ measurable_fst hf, fst_apply, map_apply]
    _ ≤ Hk[snd (map κ (fun p ↦ (p.1, f p)) (measurable_fst.prod_mk hf)), μ] :=
      entropy_condKernel_le_entropy_snd (hκ.map _)
    _ = Hk[map κ f hf, μ] := by rw [snd_map_prod _ measurable_fst]

lemma compProd_assoc (ξ : kernel T S) [IsMarkovKernel ξ]
    (κ : kernel (T × S) U) [IsMarkovKernel κ] (η : kernel (T × S × U) V) [IsMarkovKernel η] :
    map ((ξ ⊗ₖ κ) ⊗ₖ η) MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable
      = ξ ⊗ₖ (κ ⊗ₖ (comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable)) := by
  ext x s hs
  rw [map_apply' _ _ _ hs, compProd_apply _ _ _ (MeasurableEquiv.prodAssoc.measurable hs),
    compProd_apply _ _ _ hs, lintegral_compProd]
  swap; · exact measurable_kernel_prod_mk_left' (MeasurableEquiv.prodAssoc.measurable hs) _
  congr with a
  rw [compProd_apply]
  swap; · exact measurable_prod_mk_left hs
  congr

lemma Measure.compProd_compProd (μ : Measure T) [IsProbabilityMeasure μ]
    (ξ : kernel T S) [IsMarkovKernel ξ] (κ : kernel (T × S) U) [IsMarkovKernel κ] :
    μ ⊗ₘ (ξ ⊗ₖ κ) = (μ ⊗ₘ ξ ⊗ₘ κ).map MeasurableEquiv.prodAssoc := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply MeasurableEquiv.prodAssoc.measurable hs,
    Measure.compProd_apply (MeasurableEquiv.prodAssoc.measurable hs),
    Measure.lintegral_compProd]
  swap; · exact measurable_kernel_prod_mk_left (MeasurableEquiv.prodAssoc.measurable hs)
  congr with a
  rw [compProd_apply _ _ _ (measurable_prod_mk_left hs)]
  congr

lemma Measure.compProd_compProd' (μ : Measure T) [IsProbabilityMeasure μ]
    (ξ : kernel T S) [IsMarkovKernel ξ] (κ : kernel (T × S) U) [IsMarkovKernel κ] :
    μ ⊗ₘ (ξ ⊗ₖ κ) = (μ ⊗ₘ ξ ⊗ₘ κ).comap
      (MeasurableEquiv.prodAssoc.symm : T × S × U ≃ᵐ (T × S) × U) := by
  rw [MeasurableEquiv.comap_symm, Measure.compProd_compProd]

lemma Measure.compProd_compProd'' (μ : Measure T) [IsProbabilityMeasure μ]
    (ξ : kernel T S) [IsMarkovKernel ξ] (κ : kernel (T × S) U) [IsMarkovKernel κ] :
    μ ⊗ₘ ξ ⊗ₘ κ = Measure.comap MeasurableEquiv.prodAssoc (μ ⊗ₘ (ξ ⊗ₖ κ)) := by
  rw [Measure.compProd_compProd, ← MeasurableEquiv.map_symm, Measure.map_map]
  · simp
  · exact MeasurableEquiv.prodAssoc.symm.measurable
  · exact MeasurableEquiv.prodAssoc.measurable

-- from kernel (T × S × U) V ; Measure (T × S × U)
-- to kernel (T × S) V ; Measure (T × S)
lemma entropy_submodular_compProd {ξ : kernel T S} [IsMarkovKernel ξ]
    {κ : kernel (T × S) U} [IsMarkovKernel κ] {η : kernel (T × S × U) V} [IsMarkovKernel η]
    {μ : Measure T} [IsProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ (μ ⊗ₘ ξ))
    (hη : AEFiniteKernelSupport η (μ ⊗ₘ (ξ ⊗ₖ κ))) (hξ : AEFiniteKernelSupport ξ μ) :
    Hk[η, μ ⊗ₘ (ξ ⊗ₖ κ)]
      ≤ Hk[snd (κ ⊗ₖ (comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable)), μ ⊗ₘ ξ] := by
  have h_meas := (MeasurableEquiv.prodAssoc.symm : T × S × U ≃ᵐ (T × S) × U).symm.measurable
  have : FiniteSupport (μ ⊗ₘ ξ) := finiteSupport_of_compProd hξ
  have : FiniteSupport (μ ⊗ₘ (ξ ⊗ₖ κ)) := finiteSupport_of_compProd (hξ.compProd hκ)
  have h := entropy_condKernel_le_entropy_snd
    (κ := κ ⊗ₖ (comap η MeasurableEquiv.prodAssoc h_meas)) (μ := μ ⊗ₘ ξ) ?_
  simp only [fst_compProd] at h
  have : condKernel (κ ⊗ₖ comap η ↑MeasurableEquiv.prodAssoc h_meas)
      =ᵐ[μ ⊗ₘ ξ ⊗ₘ κ] comap η ↑MeasurableEquiv.prodAssoc h_meas := by
    exact condKernel_compProd_ae_eq κ (comap η ↑MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable)
      (μ ⊗ₘ ξ)
  rw [entropy_congr this, Measure.compProd_compProd'', entropy_comap_equiv] at h
  . exact h
  · refine (hκ.compProd ?_)
    convert hη.comap_equiv MeasurableEquiv.prodAssoc
    exact Measure.compProd_compProd'' _ _ _

lemma entropy_condKernel_compProd_triple (ξ : kernel T S) [IsMarkovKernel ξ]
    (κ : kernel (T × S) U) [IsMarkovKernel κ] (η : kernel (T × S × U) V) [IsMarkovKernel η]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[condKernel (ξ ⊗ₖ κ ⊗ₖ η) , μ ⊗ₘ (ξ ⊗ₖ κ)] = Hk[η, μ ⊗ₘ (ξ ⊗ₖ κ)] :=
  entropy_congr (condKernel_compProd_ae_eq (ξ ⊗ₖ κ) η μ)

/- $$ H[X,Y,Z] + H[X] \leq H[Z,X] + H[Y,X].$$ -/
lemma entropy_compProd_triple_add_entropy_le {ξ : kernel T S} [IsMarkovKernel ξ]
    {κ : kernel (T × S) U} [IsMarkovKernel κ] {η : kernel (T × S × U) V} [IsMarkovKernel η]
    {μ : Measure T} [IsProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ (μ ⊗ₘ ξ))
    (hη : AEFiniteKernelSupport η (μ ⊗ₘ (ξ ⊗ₖ κ))) (hξ : AEFiniteKernelSupport ξ μ) :
    Hk[(ξ ⊗ₖ κ) ⊗ₖ η, μ] + Hk[ξ, μ]
      ≤ Hk[ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable), μ]
       + Hk[ξ ⊗ₖ κ, μ] := by
  rw [chain_rule,
    chain_rule (κ := ξ ⊗ₖ snd (κ ⊗ₖ comap η ↑MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable))]
  simp only [fst_compProd, entropy_condKernel_compProd_triple, fst_deleteMiddle]
  . calc Hk[ξ ⊗ₖ κ , μ] + Hk[η , μ ⊗ₘ (ξ ⊗ₖ κ)] + Hk[ξ , μ]
      = Hk[ξ , μ] + Hk[ξ ⊗ₖ κ , μ] + Hk[η , μ ⊗ₘ (ξ ⊗ₖ κ)] := by abel
    _ ≤ Hk[ξ , μ] + Hk[ξ ⊗ₖ κ , μ]
      + Hk[condKernel (ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc _)) , μ ⊗ₘ ξ] := by
        refine add_le_add le_rfl ?_
        refine (entropy_submodular_compProd hκ hη hξ).trans_eq ?_
        refine entropy_congr ?_
        exact (condKernel_compProd_ae_eq _ _ _).symm
    _ = Hk[ξ , μ] + Hk[condKernel (ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc _)) , μ ⊗ₘ ξ] + Hk[ξ ⊗ₖ κ , μ] := by abel
  . refine hξ.compProd ?_
    refine AEFiniteKernelSupport.snd ?_
    refine hκ.compProd ?_
    convert hη.comap_equiv MeasurableEquiv.prodAssoc
    exact Measure.compProd_compProd'' _ _ _
  · exact (hξ.compProd hκ).compProd hη

/-- The submodularity inequality:
$$ H[X,Y,Z] + H[X] \leq H[X,Z] + H[X,Y].$$ -/
lemma entropy_triple_add_entropy_le' {κ : kernel T (S × U × V)} [IsMarkovKernel κ]
    {μ : Measure T} [IsProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[κ, μ] + Hk[fst κ, μ] ≤ Hk[deleteMiddle κ, μ] + Hk[deleteRight κ, μ] := by
  set κ' := map κ MeasurableEquiv.prodAssoc.symm MeasurableEquiv.prodAssoc.symm.measurable
    with hκ'_def
  let ξ := fst (fst κ')
  let κ'' := condKernel (fst κ')
  let η := condKernel κ'
  have hξ_eq : ξ = fst κ := by
    simp only [ξ, κ', fst, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      map_map]
    congr
  have h_compProd_eq : ξ ⊗ₖ κ'' = fst κ' := (disintegration (fst κ')).symm
  have h_compProd_triple_eq : (ξ ⊗ₖ κ'') ⊗ₖ η = κ' := by
    rw [h_compProd_eq]
    exact (disintegration κ').symm
  have h_compProd_triple_eq' : ξ ⊗ₖ (κ'' ⊗ₖ comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable)
      = κ := by
    rw [← compProd_assoc, h_compProd_triple_eq,hκ'_def, map_map]
    simp
  have h := entropy_compProd_triple_add_entropy_le (ξ := ξ) (κ := κ'') (η := η) (μ := μ) ?_ ?_ ?_
  rotate_left
  . exact aefiniteKernelSupport_of_cond _ (hκ.map _).fst
  . rw [h_compProd_eq]
    apply aefiniteKernelSupport_of_cond
    exact hκ.map _
  · exact (hκ.map _).fst.fst
  rw [← hξ_eq]
  have h_right : deleteRight κ = fst κ' := by
    simp only [κ', deleteRight, fst, map_map]
    congr
  have h_middle : deleteMiddle κ
      = ξ ⊗ₖ snd (κ'' ⊗ₖ comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable) := by
    rw [← deleteMiddle_compProd, h_compProd_triple_eq']
  have hκ : Hk[κ, μ] = Hk[κ', μ] := by
    rw [hκ'_def, entropy_map_of_injective]
    exact MeasurableEquiv.prodAssoc.symm.injective
  rw [h_right, h_middle, hκ, ← h_compProd_triple_eq, fst_compProd]
  . exact h

lemma entropy_reverse {κ : kernel T (S × U × V)} [IsMarkovKernel κ]
    {μ : Measure T} [IsProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[reverse κ, μ] = Hk[κ, μ] := by
  refine le_antisymm ?_ ?_
  · convert entropy_map_le (fun p ↦ (p.2.2, p.2.1, p.1)) hκ
  · conv_lhs => rw [← reverse_reverse κ]
    convert entropy_map_le (κ := reverse κ) (fun p ↦ (p.2.2, p.2.1, p.1)) hκ.reverse

/-- The submodularity inequality:
$$ H[X,Y,Z] + H[Z] \leq H[X,Z] + H[Y,Z].$$ -/
lemma entropy_triple_add_entropy_le (κ : kernel T (S × U × V)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[κ, μ] + Hk[snd (snd κ), μ] ≤ Hk[deleteMiddle κ, μ] + Hk[snd κ, μ] := by
  have h2 : fst (reverse κ) = snd (snd κ) := by
    simp only [fst, reverse, snd, map_map]
    congr
  rw [← entropy_reverse hκ, ← h2]
  refine (entropy_triple_add_entropy_le' (κ := reverse κ) (μ:= μ) hκ.reverse).trans ?_
  refine add_le_add ?_ ?_
  · rw [← entropy_swapRight]
    simp
  · rw [← entropy_swapRight]
    simp

end ProbabilityTheory.kernel
