import PFR.Entropy.Group

/-!
# Ruzsa distance between kernels

## Main definitions

*

## Notations

* `dk[κ ; μ # η ; ν] = `

-/


open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators


namespace ProbabilityTheory.kernel

variable {T T' T'' G : Type*}
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype T'] [Nonempty T'] [MeasurableSpace T'] [MeasurableSingletonClass T']
  [Fintype T''] [Nonempty T''] [MeasurableSpace T''] [MeasurableSingletonClass T'']
  [Fintype G] [Nonempty G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G] [MeasurableSub₂ G] [MeasurableAdd₂ G]
  {κ : kernel T G} {η : kernel T' G} {μ : Measure T}  {ν : Measure T'}

noncomputable
def rdistm (μ : Measure G) (ν : Measure G) : ℝ :=
    Hm[(μ.prod ν).map (fun x ↦ x.1 - x.2)] - Hm[μ]/2 - Hm[ν]/2

noncomputable
def rdist (κ : kernel T G) (η : kernel T' G) (μ : Measure T) (ν : Measure T') : ℝ :=
  (μ.prod ν)[fun p ↦ rdistm (κ p.1) (η p.2)]

notation3:max "dk[" κ " ; " μ " # " η " ; " μ' "]" => rdist κ η μ μ'

lemma rdist_eq (κ : kernel T G) (η : kernel T' G) (μ : Measure T) (ν : Measure T')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    dk[κ ; μ # η ; ν] = (μ.prod ν)[fun p ↦ Hm[((κ p.1).prod (η p.2)).map (fun x ↦ x.1 - x.2)]]
      - Hk[κ, μ]/2 - Hk[η, ν]/2 := by
  simp_rw [rdist, rdistm, integral_eq_sum, smul_sub, Finset.sum_sub_distrib, smul_eq_mul]
  congr
  · simp_rw [Fintype.sum_prod_type, ← Finset.sum_mul,
      ← Set.singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul,
      ← Finset.mul_sum, Finset.sum_toReal_measure_singleton, Finset.coe_univ, measure_univ,
      ENNReal.one_toReal, mul_one, mul_div, ← Finset.sum_div, entropy, integral_eq_sum, smul_eq_mul]
  · simp_rw [Fintype.sum_prod_type_right, ← Finset.sum_mul, ← Set.singleton_prod_singleton,
      Measure.prod_prod, ENNReal.toReal_mul, ← Finset.sum_mul, Finset.sum_toReal_measure_singleton,
      Finset.coe_univ, measure_univ, ENNReal.one_toReal, one_mul,
      mul_div, ← Finset.sum_div, entropy, integral_eq_sum, smul_eq_mul]

lemma rdist_eq' (κ : kernel T G) (η : kernel T' G) [IsFiniteKernel κ] [IsFiniteKernel η]
    (μ : Measure T) (ν : Measure T') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    dk[κ ; μ # η ; ν] =
      Hk[map ((prodMkRight κ T') ×ₖ (prodMkLeft T η)) (fun x ↦ x.1 - x.2) measurable_sub, μ.prod ν]
      - Hk[κ, μ]/2 - Hk[η, ν]/2 := by
  rw [rdist_eq]
  congr with p
  simp only
  rw [map_apply, prod_apply'', prodMkLeft_apply, prodMkRight_apply]

lemma rdist_symm (κ : kernel T G) (η : kernel T' G) [IsFiniteKernel κ] [IsFiniteKernel η]
    (μ : Measure T) (ν : Measure T') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    dk[κ ; μ # η ; ν] = dk[η ; ν # κ ; μ] := by
  rw [rdist_eq', rdist_eq', sub_sub, sub_sub, add_comm]
  congr 1
  rw [← entropy_comap_swap, comap_map_comm, entropy_sub_comm, Measure.comap_swap, Measure.prod_swap,
    comap_prod_swap, map_map]
  congr

lemma ruzsa_triangle_aux1 (κ : kernel T (G × G)) (η : kernel T G)
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    map (κ ×ₖ η) (fun x ↦ x.1.1 - x.1.2) (measurable_of_finite _)
      = map κ (fun p ↦ p.1 - p.2) measurable_sub := by
  ext x s hs
  rw [map_apply' _ _ _ hs, map_apply' _ _ _ hs, prod_apply]
  swap; · exact measurable_of_finite _ hs
  simp only [Set.mem_preimage]
  classical
  have : ∀ b : G × G, η x {_c | b.1 - b.2 ∈ s}
      = ((fun p : G × G ↦ p.1 - p.2) ⁻¹' s).indicator (fun _ ↦ 1) b := by
    intro b
    simp only [Set.mem_preimage, Set.indicator_apply]
    split_ifs with h <;> simp [h]
  simp_rw [this]
  rw [lintegral_indicator_const, one_mul]
  exact measurable_of_finite _ hs

lemma ruzsa_triangle_aux2 (κ : kernel T (G × G)) (η : kernel T G)
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    map (κ ×ₖ η) (fun x ↦ (x.1.2, x.1.1 - x.1.2)) (measurable_of_finite _)
      = map κ (fun p ↦ (p.2, p.1 - p.2)) (measurable_of_finite _) := by
  ext x s hs
  rw [map_apply' _ _ _ hs, map_apply' _ _ _ hs, prod_apply]
  swap; · exact measurable_of_finite _ hs
  simp only [Set.mem_preimage]
  classical
  have : ∀ b : G × G, η x {_c | (b.2, b.1 - b.2) ∈ s}
      = ((fun p : G × G ↦ (p.2, p.1 - p.2)) ⁻¹' s).indicator (fun _ ↦ 1) b := by
    intro b
    simp only [Set.mem_preimage, Set.indicator_apply]
    split_ifs with h <;> simp [h]
  simp_rw [this]
  rw [lintegral_indicator_const, one_mul]
  exact measurable_of_finite _ hs

lemma ruzsa_triangle_aux3 (κ : kernel T (G × G)) (η : kernel T G)
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    map (κ ×ₖ η) (fun p ↦ p.2 - p.1.2) (measurable_of_finite _)
      = map (η ×ₖ snd κ) (fun p ↦ p.1 - p.2) (measurable_of_finite _) := by
  have : (fun p : G × G ↦ p.1 - p.2) = (fun p ↦ p.2 - p.1) ∘ Prod.swap := by ext1 p; simp
  rw [this, ← map_map]
  rotate_left
  · exact measurable_swap
  · exact measurable_of_finite _
  rw [map_prod_swap]
  ext x s hs
  rw [map_apply' _ _ _ hs, map_apply' _ _ _ hs, prod_apply, prod_apply]
  rotate_left
  · exact measurable_of_finite _ hs
  · exact measurable_of_finite _ hs
  rw [lintegral_snd]
  · congr
  · exact measurable_of_finite _

-- Kernel equivalent of `H[X - Y; μ] ≤ H[X - Z; μ] + H[Z - Y; μ] - H[Z; μ]`
-- `κ` is `⟨X,Y⟩`, `η` is `Z`. Independence is expressed through the product `×ₖ`.
/-- The **improved entropic Ruzsa triangle inequality**. -/
lemma ent_of_diff_le (κ : kernel T (G × G)) (η : kernel T G) [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[map κ (fun p : G × G ↦ p.1 - p.2) measurable_sub, μ]
      ≤ Hk[map ((fst κ) ×ₖ η) (fun p : G × G ↦ p.1 - p.2) measurable_sub, μ]
        + Hk[map (η ×ₖ (snd κ)) (fun p : G × G ↦ p.1 - p.2) measurable_sub, μ]
        - Hk[η, μ] := by
  have h1 : Hk[map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, (p.1.2, p.1.1 - p.1.2)))
        (measurable_of_finite _), μ] + Hk[map κ (fun p ↦ p.1 - p.2) measurable_sub, μ]
      ≤ Hk[map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.1 - p.1.2)) (measurable_of_finite _), μ]
        + Hk[map κ (fun p ↦ (p.2, p.1 - p.2)) (measurable_of_finite _), μ] := by
    have h := entropy_triple_add_entropy_le
      (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, (p.1.2, p.1.1 - p.1.2))) (measurable_of_finite _)) μ
    simp only [snd_map_prod _ (measurable_of_finite _) (measurable_of_finite _)] at h
    rw [deleteMiddle_map_prod _ (measurable_of_finite _) (measurable_of_finite _)
        (measurable_of_finite _)] at h
    have : map (κ ×ₖ η) (fun x ↦ x.1.1 - x.1.2) (measurable_of_finite _)
        = map κ (fun p ↦ p.1 - p.2) measurable_sub := ruzsa_triangle_aux1 κ η
    rw [this] at h
    refine h.trans_eq ?_
    congr 2
    exact ruzsa_triangle_aux2 κ η
  have h2 : Hk[map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.1 - p.1.2)) (measurable_of_finite _), μ]
      ≤ Hk[map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2) (measurable_of_finite _), μ]
        + Hk[map (κ ×ₖ η) (fun p ↦ p.1.2 - p.2) (measurable_of_finite _), μ] := by
    calc Hk[map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.1 - p.1.2)) (measurable_of_finite _), μ]
      ≤ Hk[map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.2 - p.2)) (measurable_of_finite _), μ] := by
          have : (fun p : (G × G) × G ↦ (p.1.1 - p.2, p.1.1 - p.1.2))
            = (fun p ↦ (p.1, p.1 - p.2)) ∘ (fun p ↦ (p.1.1 - p.2, p.1.2 - p.2)) := by ext1; simp
          rw [this, ← map_map]
          exact entropy_map_le _ _ _
    _ ≤ Hk[map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2) (measurable_of_finite _), μ]
        + Hk[map (κ ×ₖ η) (fun p ↦ p.1.2 - p.2) (measurable_of_finite _), μ] := by
          have h : 0 ≤ Hk[map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2) (measurable_of_finite _), μ]
              + Hk[map (κ ×ₖ η) (fun p ↦ p.1.2 - p.2) (measurable_of_finite _), μ]
              - Hk[map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.2 - p.2))
                (measurable_of_finite _), μ] := by
            have h' := mutualInfo_nonneg (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.2 - p.2))
                (measurable_of_finite _)) μ
            rwa [mutualInfo, fst_map_prod _ (measurable_of_finite _) (measurable_of_finite _),
              snd_map_prod _ (measurable_of_finite _) (measurable_of_finite _)] at h'
          linarith
  have h3 : Hk[map κ (fun p : G × G ↦ (p.2, p.1 - p.2)) (measurable_of_finite _), μ]
      ≤ Hk[κ, μ] := by
    exact entropy_map_le κ _ _
  have h4 : Hk[map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, (p.1.2, p.1.1 - p.1.2)))
      (measurable_of_finite _), μ] = Hk[κ ×ₖ η, μ] := by
    refine entropy_of_map_eq_of_map _ _ μ
      (fun p : G × G × G ↦ ((p.2.2 + p.2.1, p.2.1), -p.1 + p.2.2 + p.2.1))
      (fun p : (G × G) × G ↦ (p.1.1 - p.2, (p.1.2, p.1.1 - p.1.2))) ?_ ?_
    · rw [map_map]
      suffices ((fun p : G × G × G ↦ ((p.2.2 + p.2.1, p.2.1), -p.1 + p.2.2 + p.2.1))
          ∘ fun p ↦ (p.1.1 - p.2, p.1.2, p.1.1 - p.1.2)) = id by
        simp_rw [this, map_id]
      ext1 p
      simp
    · rfl
  have h5 : Hk[κ ×ₖ η, μ] = Hk[κ, μ] + Hk[η, μ] := by rw [entropy_prod]
  rw [h4, h5] at h1
  calc Hk[map κ (fun p : G × G ↦ p.1 - p.2) measurable_sub, μ]
    ≤ Hk[map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2) (measurable_of_finite _), μ]
      + Hk[map (κ ×ₖ η) (fun p ↦ p.1.2 - p.2) (measurable_of_finite _), μ] - Hk[η, μ] := by
        linarith
  _ = Hk[map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2) (measurable_of_finite _), μ]
      + Hk[map (κ ×ₖ η) (fun p ↦ p.2 - p.1.2) (measurable_of_finite _), μ] - Hk[η, μ] := by
        congr 2
        rw [← entropy_neg, map_map]
        congr with p
        simp
  _ = Hk[map ((fst κ) ×ₖ η) (fun p : G × G ↦ p.1 - p.2) measurable_sub, μ]
      + Hk[map (η ×ₖ (snd κ)) (fun p : G × G ↦ p.1 - p.2) measurable_sub, μ]
      - Hk[η, μ] := by
        congr 3
        · ext x s hs
          rw [map_apply' _ _ _ hs, map_apply' _ _ _ hs, prod_apply, prod_apply, lintegral_fst]
          · congr with x
          · exact measurable_of_finite _
          · exact measurable_sub hs
          · exact measurable_of_finite _ hs
        · exact ruzsa_triangle_aux3 κ η

lemma rdist_triangle (κ η ξ : kernel T G) (η : kernel T' G) (ξ : kernel T'' G)
    [IsMarkovKernel κ] [IsMarkovKernel η] [IsMarkovKernel ξ]
    (μ : Measure T) (μ' : Measure T') (μ'' : Measure T'')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsProbabilityMeasure μ''] :
    dk[κ ; μ # ξ ; μ''] ≤ dk[κ ; μ # η ; μ'] + dk[η ; μ' # ξ ; μ''] := by
  rw [rdist_eq', rdist_eq', rdist_eq']
  sorry

end ProbabilityTheory.kernel
