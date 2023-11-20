import PFR.Entropy.Kernel

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

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators


namespace ProbabilityTheory.kernel

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Nonempty S] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Nonempty T] [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Nonempty U] [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  {κ : kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}

/-- Mutual information of a kernel into a product space with respect to a measure. -/
noncomputable
def mutualInfo (κ : kernel T (S × U)) (μ : Measure T) : ℝ :=
  Hk[fst κ, μ] + Hk[snd κ, μ] - Hk[κ, μ]

notation3:100 "Ik[" κ " , " μ "]" => kernel.mutualInfo κ μ

lemma mutualInfo_def (κ : kernel T (S × U)) (μ : Measure T) :
    Ik[κ, μ] = Hk[fst κ, μ] + Hk[snd κ, μ] - Hk[κ, μ] := rfl

@[simp]
lemma mutualInfo_zero_measure (κ : kernel T (S × U)) : Ik[κ, (0 : Measure T)] = 0 := by
  simp [mutualInfo]

@[simp]
lemma mutualInfo_zero_kernel (μ : Measure T) : Ik[(0 : kernel T (S × U)), μ] = 0 := by
  simp [mutualInfo]

lemma mutualInfo_compProd (κ : kernel T S) [IsMarkovKernel κ]
    (η : kernel (T × S) U) [IsMarkovKernel η] (μ : Measure T) [IsProbabilityMeasure μ] :
    Ik[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[snd (κ ⊗ₖ η), μ] - Hk[κ ⊗ₖ η, μ] := by
  rw [mutualInfo, entropy_compProd, fst_compProd]

lemma mutualInfo_eq_snd_sub (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Ik[κ, μ] = Hk[snd κ, μ] - Hk[condKernel κ, μ ⊗ₘ (fst κ)] := by
  rw [mutualInfo, chain_rule κ μ]
  ring

lemma mutualInfo_eq_fst_sub (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Ik[κ, μ] = Hk[fst κ, μ] - Hk[condKernel (swapRight κ), μ ⊗ₘ (snd κ)] := by
  rw [mutualInfo, chain_rule' κ μ]
  ring

@[simp]
lemma mutualInfo_prod (κ : kernel T S) (η : kernel T U) [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Ik[κ ×ₖ η, μ] = 0 := by
  rw [mutualInfo, snd_prod, fst_prod, entropy_prod, sub_self]

@[simp]
lemma mutualInfo_swapRight (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Ik[swapRight κ, μ] = Ik[κ, μ] := by
  rw [mutualInfo, fst_swapRight, snd_swapRight, entropy_swapRight, add_comm]
  rfl

lemma mutualInfo_nonneg (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    0 ≤ Ik[κ, μ] := by
  simp_rw [mutualInfo, entropy, integral_eq_sum,
    smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg (fun x _ ↦ ?_)
  by_cases hx : μ {x} = 0
  · simp [hx]
  rw [← mul_add, ← mul_sub]
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  rw [fst_apply, snd_apply]
  exact measureMutualInfo_nonneg _

lemma entropy_condKernel_le_entropy_fst (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[condKernel (swapRight κ), μ ⊗ₘ (snd κ)] ≤ Hk[fst κ, μ] := by
  rw [← sub_nonneg, ← mutualInfo_eq_fst_sub κ]
  exact mutualInfo_nonneg _ _

lemma entropy_condKernel_le_entropy_snd (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[condKernel κ, μ ⊗ₘ (fst κ)] ≤ Hk[snd κ, μ] := by
  rw [← sub_nonneg, ← mutualInfo_eq_snd_sub κ]
  exact mutualInfo_nonneg _ _

-- TODO: extract lemma(s) from this:
lemma entropy_snd_sub_mutualInfo_le_entropy_map_of_injective {V : Type*} [Fintype V] [Nonempty V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (κ : kernel T (S × U)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ]
    (f : S × U → V) (hfi : ∀ x, Function.Injective (fun y ↦ f (x, y))) :
    Hk[snd κ, μ] - Ik[κ, μ] ≤ Hk[map κ f (measurable_of_finite f), μ] := by
  rw [mutualInfo_eq_snd_sub]
  have hf : Measurable f := measurable_of_finite f
  ring_nf
  calc Hk[condKernel κ, μ ⊗ₘ fst κ]
    = Hk[snd ((condKernel κ) ⊗ₖ (deterministic (fun x : (T × S) × U ↦ f (x.1.2, x.2))
          (measurable_of_finite _))), μ ⊗ₘ fst κ] :=
        (entropy_snd_compProd_deterministic_of_injective _ _
          (fun x : (T × S) × U ↦ f (x.1.2, x.2)) (fun p x y hxy ↦ hfi p.2 hxy)).symm
  _ = Hk[condKernel (map κ (fun p ↦ (p.1, f p)) (measurable_fst.prod_mk hf)),
      μ ⊗ₘ fst κ] := entropy_congr (condKernel_map_prod_mk_left κ μ f).symm
  _ = Hk[condKernel (map κ (fun p ↦ (p.1, f p)) (measurable_fst.prod_mk hf)),
      μ ⊗ₘ fst (map κ (fun p ↦ (p.1, f p)) (measurable_fst.prod_mk hf))] := by
        congr 2 with x
        rw [fst_map_prod _ measurable_fst hf, fst_apply, map_apply]
  _ ≤ Hk[snd (map κ (fun p ↦ (p.1, f p)) (measurable_fst.prod_mk hf)), μ] :=
        entropy_condKernel_le_entropy_snd _ _
  _ = Hk[map κ f hf, μ] := by rw [snd_map_prod _ measurable_fst]

end ProbabilityTheory.kernel
