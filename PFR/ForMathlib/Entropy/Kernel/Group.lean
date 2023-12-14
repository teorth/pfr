import PFR.ForMathlib.Entropy.Kernel.MutualInfo
import Mathlib.MeasureTheory.Group.Arithmetic
/-!
# Kernel entropy and mutual information in a commutative group

## Main definitions

## Main results

-/
open MeasureTheory ProbabilityTheory

variable {Ω Ω' Ω'' Ω''' G T : Type*}
  [Countable T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [MeasurableSpace G] [MeasurableSingletonClass G] [Group G]
  [MeasurableDiv₂ G] [MeasurableMul₂ G] [Countable G]
  {κ : kernel T G} {μ : Measure T}

@[to_additive (attr := simp)]
lemma measureEntropy_inv (μ : Measure G) : Hm[μ.map (·⁻¹)] = Hm[μ] := measureEntropy_map_of_injective μ _ measurable_inv inv_injective


@[to_additive]
lemma measureEntropy_div_comm (μ : Measure (G × G)) :
    Hm[μ.map fun p ↦ p.1 / p.2] = Hm[μ.map fun p ↦ p.2 / p.1] := by
  rw [←measureEntropy_inv, Measure.map_map measurable_inv measurable_div]
  congr with x
  simp

namespace ProbabilityTheory.kernel

@[to_additive]
lemma entropy_inv (κ : kernel T G) (μ : Measure T) : Hk[map κ (·⁻¹) measurable_inv, μ] = Hk[κ, μ] := entropy_map_of_injective κ μ inv_injective measurable_inv


@[to_additive]
lemma entropy_div_comm (κ : kernel T (G × G)) (μ : Measure T) :
    Hk[map κ (fun p ↦ p.1 / p.2) measurable_div, μ]
      = Hk[map κ (fun p ↦ p.2 / p.1) (measurable_snd.div measurable_fst), μ] := by
  rw [←entropy_inv, kernel.map_map]
  congr with x
  simp

@[to_additive]
lemma entropy_snd_sub_mutualInfo_le_entropy_map_mul
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] (hμ : FiniteSupport μ) (hκ: FiniteKernelSupport κ):
    Hk[snd κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.1 * p.2) measurable_mul, μ] :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ mul_right_injective hμ hκ

@[to_additive]
lemma entropy_snd_sub_mutualInfo_le_entropy_map_mul'
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ]  (hμ : FiniteSupport μ) (hκ: FiniteKernelSupport κ) :
    Hk[snd κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.2 * p.1) $ measurable_discrete _, μ] :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ mul_left_injective hμ hκ

@[to_additive]
lemma entropy_fst_sub_mutualInfo_le_entropy_map_mul
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ]  (hμ : FiniteSupport μ) (hκ: FiniteKernelSupport κ) :
    Hk[fst κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.1 * p.2) measurable_mul, μ] := by
    have h := entropy_snd_sub_mutualInfo_le_entropy_map_mul' (swapRight κ) μ hμ (kernel.finiteKernelSupport_of_swapRight hκ)
    simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
    refine h.trans_eq ?_
    have : (fun p : G × G ↦ p.2 * p.1) ∘ Prod.swap = (fun p ↦ p.1 * p.2) := rfl
    simp_rw [this]

@[to_additive]
lemma entropy_fst_sub_mutualInfo_le_entropy_map_mul'
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ]  (hμ : FiniteSupport μ) (hκ: FiniteKernelSupport κ)  :
    Hk[fst κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.2 * p.1) $ measurable_discrete _, μ] := by
    have h := entropy_snd_sub_mutualInfo_le_entropy_map_mul (swapRight κ) μ hμ (kernel.finiteKernelSupport_of_swapRight hκ)
    simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
    refine h.trans_eq ?_
    have : (fun p : G × G ↦ p.1 * p.2) ∘ Prod.swap = (fun p ↦ p.2 * p.1) := rfl
    simp_rw [this]

@[to_additive]
lemma entropy_snd_sub_mutualInfo_le_entropy_map_div
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] (hμ : FiniteSupport μ) (hκ: FiniteKernelSupport κ)  :
    Hk[snd κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.1 / p.2) measurable_div, μ] :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ (fun _ ↦ div_right_injective) hμ hκ

@[to_additive]
lemma entropy_fst_sub_mutualInfo_le_entropy_map_div
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] (hμ : FiniteSupport μ) (hκ: FiniteKernelSupport κ)  :
    Hk[fst κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.1 / p.2) measurable_div, μ] := by
    have h := entropy_snd_sub_mutualInfo_le_entropy_map_div (swapRight κ) μ hμ (kernel.finiteKernelSupport_of_swapRight hκ)
    simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
    refine h.trans_eq ?_
    have : (fun p : G × G ↦ p.1 / p.2) ∘ Prod.swap = (fun p ↦ p.2 / p.1) := rfl
    simp_rw [this]
    rw [← entropy_div_comm]

@[to_additive]
lemma max_entropy_sub_mutualInfo_le_entropy_mul
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] (hμ : FiniteSupport μ) (hκ: FiniteKernelSupport κ)  :
    max (Hk[fst κ, μ]) (Hk[snd κ, μ]) - Ik[κ, μ]
      ≤ Hk[map κ (fun p ↦ p.1 * p.2) measurable_mul, μ] := by
  rw [←max_sub_sub_right, max_le_iff]
  exact ⟨entropy_fst_sub_mutualInfo_le_entropy_map_mul _ _ hμ hκ,
    entropy_snd_sub_mutualInfo_le_entropy_map_mul _ _ hμ hκ⟩

@[to_additive]
lemma max_entropy_sub_mutualInfo_le_entropy_mul'
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] (hμ : FiniteSupport μ) (hκ: FiniteKernelSupport κ)  :
    max (Hk[fst κ, μ]) (Hk[snd κ, μ]) - Ik[κ, μ]
      ≤ Hk[map κ (fun p ↦ p.2 * p.1) $ measurable_discrete _, μ] := by
  rw [←max_sub_sub_right, max_le_iff]
  exact ⟨entropy_fst_sub_mutualInfo_le_entropy_map_mul' _ _ hμ hκ,
    entropy_snd_sub_mutualInfo_le_entropy_map_mul' _ _ hμ hκ⟩

@[to_additive]
lemma max_entropy_sub_mutualInfo_le_entropy_div
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] (hμ : FiniteSupport μ) (hκ: FiniteKernelSupport κ) :
    max (Hk[fst κ, μ]) (Hk[snd κ, μ]) - Ik[κ, μ]
      ≤ Hk[map κ (fun p ↦ p.1 / p.2) measurable_div, μ] := by
  rw [←max_sub_sub_right, max_le_iff]
  exact ⟨entropy_fst_sub_mutualInfo_le_entropy_map_div _ _ hμ hκ,
    entropy_snd_sub_mutualInfo_le_entropy_map_div _ _ hμ hκ⟩

end ProbabilityTheory.kernel
