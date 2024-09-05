import PFR.ForMathlib.Entropy.Kernel.MutualInfo
import Mathlib.MeasureTheory.Group.Arithmetic
/-!
# Kernel entropy and mutual information in a commutative group

## Main definitions

## Main results

-/
open MeasureTheory ProbabilityTheory

variable {Ω Ω' Ω'' Ω''' G T : Type*}
  [MeasurableSpace T]
  [MeasurableSpace G] [MeasurableSingletonClass G] [Group G] [Countable G]
  {κ : Kernel T G} {μ : Measure T}

@[to_additive (attr := simp)]
lemma measureEntropy_inv (μ : Measure G) : Hm[μ.map (·⁻¹)] = Hm[μ] :=
  measureEntropy_map_of_injective μ _ measurable_inv inv_injective

@[to_additive]
lemma measureEntropy_div_comm (μ : Measure (G × G)) :
    Hm[μ.map fun p ↦ p.1 / p.2] = Hm[μ.map fun p ↦ p.2 / p.1] := by
  rw [← measureEntropy_inv, Measure.map_map measurable_inv measurable_div]
  congr with x
  simp

namespace ProbabilityTheory.Kernel

@[to_additive]
lemma entropy_inv (κ : Kernel T G) (μ : Measure T) : Hk[map κ (·⁻¹), μ] = Hk[κ, μ] :=
  entropy_map_of_injective κ μ inv_injective measurable_inv

@[to_additive]
lemma entropy_div_comm (κ : Kernel T (G × G)) (μ : Measure T) :
    Hk[map κ (fun p ↦ p.1 / p.2), μ]
      = Hk[map κ (fun p ↦ p.2 / p.1), μ] := by
  rw [← entropy_inv, Kernel.map_map _ (by fun_prop) (by fun_prop)]
  congr with x
  simp

variable [Countable T] [MeasurableSingletonClass T]

@[to_additive]
lemma entropy_snd_sub_mutualInfo_le_entropy_map_mul
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    Hk[snd κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.1 * p.2), μ] :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ mul_right_injective hκ

@[to_additive]
lemma entropy_snd_sub_mutualInfo_le_entropy_map_mul'
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    Hk[snd κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.2 * p.1), μ] :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ mul_left_injective hκ

@[to_additive]
lemma entropy_fst_sub_mutualInfo_le_entropy_map_mul
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    Hk[fst κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.1 * p.2), μ] := by
    have h := entropy_snd_sub_mutualInfo_le_entropy_map_mul' (swapRight κ) μ hκ.swapRight
    simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
    refine h.trans_eq ?_
    have : (fun p : G × G ↦ p.2 * p.1) ∘ Prod.swap = (fun p ↦ p.1 * p.2) := rfl
    simp_rw [this]

@[to_additive]
lemma entropy_fst_sub_mutualInfo_le_entropy_map_mul'
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ)  :
    Hk[fst κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.2 * p.1), μ] := by
    have h := entropy_snd_sub_mutualInfo_le_entropy_map_mul (swapRight κ) μ hκ.swapRight
    simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
    refine h.trans_eq ?_
    have : (fun p : G × G ↦ p.1 * p.2) ∘ Prod.swap = (fun p ↦ p.2 * p.1) := rfl
    simp_rw [this]

@[to_additive]
lemma entropy_snd_sub_mutualInfo_le_entropy_map_div
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ)  :
    Hk[snd κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.1 / p.2), μ] :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ (fun _ ↦ div_right_injective) hκ

@[to_additive]
lemma entropy_fst_sub_mutualInfo_le_entropy_map_div
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ)  :
    Hk[fst κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.1 / p.2), μ] := by
    have h := entropy_snd_sub_mutualInfo_le_entropy_map_div (swapRight κ) μ hκ.swapRight
    simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
    refine h.trans_eq ?_
    have : (fun p : G × G ↦ p.1 / p.2) ∘ Prod.swap = (fun p ↦ p.2 / p.1) := rfl
    simp_rw [this]
    rw [← entropy_div_comm]

@[to_additive]
lemma max_entropy_sub_mutualInfo_le_entropy_mul
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ)  :
    max (Hk[fst κ, μ]) (Hk[snd κ, μ]) - Ik[κ, μ]
      ≤ Hk[map κ (fun p ↦ p.1 * p.2), μ] := by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_fst_sub_mutualInfo_le_entropy_map_mul _ _ hκ,
    entropy_snd_sub_mutualInfo_le_entropy_map_mul _ _ hκ⟩

@[to_additive]
lemma max_entropy_sub_mutualInfo_le_entropy_mul'
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ)  :
    max (Hk[fst κ, μ]) (Hk[snd κ, μ]) - Ik[κ, μ]
      ≤ Hk[map κ (fun p ↦ p.2 * p.1), μ] := by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_fst_sub_mutualInfo_le_entropy_map_mul' _ _ hκ,
    entropy_snd_sub_mutualInfo_le_entropy_map_mul' _ _ hκ⟩

@[to_additive]
lemma max_entropy_sub_mutualInfo_le_entropy_div
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    max (Hk[fst κ, μ]) (Hk[snd κ, μ]) - Ik[κ, μ]
      ≤ Hk[map κ (fun p ↦ p.1 / p.2), μ] := by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_fst_sub_mutualInfo_le_entropy_map_div _ _ hκ,
    entropy_snd_sub_mutualInfo_le_entropy_map_div _ _ hκ⟩

@[to_additive]
lemma max_entropy_le_entropy_mul_prod
    (κ : Kernel T G) [IsMarkovKernel κ] (η : Kernel T G) [IsMarkovKernel η]
    (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    max (Hk[κ, μ]) (Hk[η, μ]) ≤ Hk[map (κ ×ₖ η) (fun p ↦ p.1 * p.2), μ] := by
  calc max (Hk[κ, μ]) (Hk[η, μ])
    = max (Hk[κ, μ]) (Hk[η, μ]) - Ik[κ ×ₖ η, μ] := by
        rw [mutualInfo_prod _ hκ hη, sub_zero]
  _ ≤ Hk[map (κ ×ₖ η) (fun p ↦ p.1 * p.2), μ] := by
        convert max_entropy_sub_mutualInfo_le_entropy_mul (κ ×ₖ η) μ (hκ.prod hη)
        · simp
        · simp

@[to_additive max_entropy_le_entropy_sub_prod]
lemma max_entropy_le_entropy_div_prod
    (κ : Kernel T G) [IsMarkovKernel κ] (η : Kernel T G) [IsMarkovKernel η]
    (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    max (Hk[κ, μ]) (Hk[η, μ]) ≤ Hk[map (κ ×ₖ η) (fun p ↦ p.1 / p.2), μ] := by
  calc max (Hk[κ, μ]) (Hk[η, μ])
    = max (Hk[κ, μ]) (Hk[η, μ]) - Ik[κ ×ₖ η, μ] := by
        rw [mutualInfo_prod _ hκ hη, sub_zero]
  _ ≤ Hk[map (κ ×ₖ η) (fun p ↦ p.1 / p.2), μ] := by
        convert max_entropy_sub_mutualInfo_le_entropy_div (κ ×ₖ η) μ (hκ.prod hη)
        · simp
        · simp

end ProbabilityTheory.Kernel
