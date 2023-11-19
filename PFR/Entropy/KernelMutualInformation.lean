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

end ProbabilityTheory.kernel
