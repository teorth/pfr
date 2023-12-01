import PFR.Entropy.KernelMutualInfo
/-!
# Kernel entropy and mutual information in a commutative group

## Main definitions

## Main results

-/
open MeasureTheory ProbabilityTheory

variable {Ω Ω' Ω'' Ω''' G T : Type*}
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [hG: MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G]
  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Fintype G]
  {κ : kernel T G} {μ : Measure T}

/-- For mathlib -/
instance : MeasurableNeg G := by
  constructor
  convert measurable_const (a := (0 : G)).sub measurable_id
  ext x
  simp

lemma measureEntropy_neg (μ : Measure G) :
    Hm[μ.map (fun x ↦ -x)] = Hm[μ] :=
  measureEntropy_map_of_injective μ (fun x ↦ -x) neg_injective

lemma measureEntropy_sub_comm (μ : Measure (G × G)) :
    Hm[μ.map (fun p ↦ p.2 - p.1)]
      = Hm[μ.map (fun p ↦ p.1 - p.2)] := by
  have : (fun p : G × G ↦ p.2 - p.1) = (fun x ↦ - x) ∘ (fun p ↦ p.1 - p.2) := by ext; simp
  simp_rw [this]
  rw [← Measure.map_map measurable_neg measurable_sub, measureEntropy_neg]

namespace ProbabilityTheory.kernel

lemma entropy_neg (κ : kernel T G) (μ : Measure T) :
    Hk[map κ (fun x ↦ -x) measurable_neg, μ] = Hk[κ, μ] :=
  entropy_map_of_injective κ μ (fun x ↦ -x) neg_injective

lemma entropy_sub_comm (κ : kernel T (G × G)) (μ : Measure T) :
    Hk[map κ (fun p ↦ p.1 - p.2) measurable_sub, μ]
      = Hk[map κ (fun p ↦ p.2 - p.1) (measurable_snd.sub measurable_fst), μ] := by
  have : (fun p : G × G ↦ p.2 - p.1) = (fun x ↦ - x) ∘ (fun p ↦ p.1 - p.2) := by ext; simp
  simp_rw [this]
  rw [← map_map, entropy_neg]

lemma entropy_snd_sub_mutualInfo_le_entropy_map_add
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[snd κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.1 + p.2) measurable_add, μ] :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ add_right_injective

lemma entropy_fst_sub_mutualInfo_le_entropy_map_add
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[fst κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.1 + p.2) measurable_add, μ] := by
    have h := entropy_snd_sub_mutualInfo_le_entropy_map_add (swapRight κ) μ
    simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
    refine h.trans_eq ?_
    have : (fun p : G × G ↦ p.1 + p.2) ∘ Prod.swap = (fun p ↦ p.1 + p.2) := by
      ext p; simp [add_comm p.1]
    simp_rw [this]

lemma entropy_snd_sub_mutualInfo_le_entropy_map_sub
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[snd κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.1 - p.2) measurable_sub, μ] :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ (fun _ ↦ sub_right_injective)

lemma entropy_fst_sub_mutualInfo_le_entropy_map_sub
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[fst κ, μ] - Ik[κ, μ] ≤ Hk[map κ (fun p ↦ p.1 - p.2) measurable_sub, μ] := by
    have h := entropy_snd_sub_mutualInfo_le_entropy_map_sub (swapRight κ) μ
    simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
    refine h.trans_eq ?_
    have : (fun p : G × G ↦ p.1 - p.2) ∘ Prod.swap = (fun p ↦ p.2 - p.1) := by
      ext p; simp
    simp_rw [this]
    rw [← entropy_sub_comm]

lemma ent_of_sum_lower
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] :
    (max (Hk[fst κ, μ]) (Hk[snd κ, μ])) - Ik[κ, μ]
      ≤ Hk[map κ (fun p ↦ p.1 + p.2) measurable_add, μ] := by
  rw [sub_le_iff_le_add']
  refine max_le ?_ ?_
  · rw [← sub_le_iff_le_add']
    exact entropy_fst_sub_mutualInfo_le_entropy_map_add _ _
  · rw [← sub_le_iff_le_add']
    exact entropy_snd_sub_mutualInfo_le_entropy_map_add _ _

lemma ent_of_diff_lower
    (κ : kernel T (G × G)) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] :
    (max (Hk[fst κ, μ]) (Hk[snd κ, μ])) - Ik[κ, μ]
      ≤ Hk[map κ (fun p ↦ p.1 - p.2) measurable_sub, μ] := by
  rw [sub_le_iff_le_add']
  refine max_le ?_ ?_
  · rw [← sub_le_iff_le_add']
    exact entropy_fst_sub_mutualInfo_le_entropy_map_sub _ _
  · rw [← sub_le_iff_le_add']
    exact entropy_snd_sub_mutualInfo_le_entropy_map_sub _ _

end ProbabilityTheory.kernel
