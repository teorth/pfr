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

variable {T T' G : Type*}
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype T'] [Nonempty T'] [MeasurableSpace T'] [MeasurableSingletonClass T']
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

section
variable {α β γ δ : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {_ : MeasurableSpace δ}

noncomputable
def deleteMiddle (κ : kernel α (β × γ × δ)) :
    kernel α (β × δ) :=
  map κ (fun p ↦ (p.1, p.2.2)) (measurable_fst.prod_mk (measurable_snd.comp measurable_snd))

instance (κ : kernel α (β × γ × δ)) [IsMarkovKernel κ] :
    IsMarkovKernel (deleteMiddle κ) := by
  rw [deleteMiddle]
  infer_instance

@[simp]
lemma fst_deleteMiddle (κ : kernel α (β × γ × δ)) : fst (deleteMiddle κ) = fst κ := by
  rw [deleteMiddle, fst_map_prod]
  rotate_left
  · exact measurable_fst
  · exact measurable_snd.comp measurable_snd
  · rfl

@[simp]
lemma snd_deleteMiddle (κ : kernel α (β × γ × δ)) : snd (deleteMiddle κ) = snd (snd κ) := by
  rw [deleteMiddle, snd_map_prod]
  rotate_left
  · exact measurable_fst
  · exact measurable_snd.comp measurable_snd
  · rw [snd, snd, map_map]
    rfl

noncomputable
def deleteRight (κ : kernel α (β × γ × δ)) :
    kernel α (β × γ) :=
  map κ (fun p ↦ (p.1, p.2.1)) (measurable_fst.prod_mk (measurable_fst.comp measurable_snd))

instance (κ : kernel α (β × γ × δ)) [IsMarkovKernel κ] :
    IsMarkovKernel (deleteRight κ) := by
  rw [deleteRight]
  infer_instance

@[simp]
lemma fst_deleteRight (κ : kernel α (β × γ × δ)) : fst (deleteRight κ) = fst κ := by
  rw [deleteRight, fst_map_prod]
  rotate_left
  · exact measurable_fst
  · exact measurable_fst.comp measurable_snd
  · rfl

@[simp]
lemma snd_deleteRight (κ : kernel α (β × γ × δ)) : snd (deleteRight κ) = fst (snd κ) := by
  rw [deleteRight, snd_map_prod]
  rotate_left
  · exact measurable_fst
  · exact measurable_fst.comp measurable_snd
  · rw [fst, snd, map_map]
    rfl

noncomputable
def assocRight (κ : kernel α ((β × γ) × δ)) :
    kernel α (β × γ × δ) :=
  map κ (fun p ↦ (p.1.1, (p.1.2, p.2)))
    ((measurable_fst.comp measurable_fst).prod_mk
      ((measurable_snd.comp measurable_fst).prod_mk measurable_snd))

noncomputable
def assocLeft (κ : kernel ((β × γ) × δ) α) :
    kernel (β × γ × δ) α :=
  comap κ (fun p  : β × γ × δ ↦ ((p.1, p.2.1), p.2.2))
    ((measurable_fst.prod_mk (measurable_fst.comp measurable_snd)).prod_mk
      (measurable_snd.comp measurable_snd))

noncomputable
def reverse (κ : kernel α (β × γ × δ)) :
    kernel α (δ × γ × β) :=
  map κ (fun p ↦ (p.2.2, (p.2.1, p.1)))
    ((measurable_snd.comp measurable_snd).prod_mk
      ((measurable_fst.comp measurable_snd).prod_mk measurable_fst))

end

lemma entropy_submodular {S U V : Type*}
    [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [Fintype V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (κ : kernel T (S × U × V)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[condKernel (swapRight κ), μ ⊗ₘ snd κ]
      ≤ Hk[condKernel (swapRight (deleteMiddle κ)), μ ⊗ₘ snd (snd κ)] := by
  let κ' : kernel (T × V) (U × S) := condKernel (reverse κ)
  have : IsMarkovKernel κ' := sorry
  have h_ae : condKernel (swapRight (deleteMiddle κ)) =ᵐ[μ ⊗ₘ snd (snd κ)] snd κ' := by
    sorry
  have h := entropy_condKernel_le_entropy_snd κ' (μ ⊗ₘ snd (snd κ))
  rw [entropy_congr h_ae.symm] at h
  refine le_trans (le_of_eq ?_) h
  sorry

/-- The submodularity inequality:
$$ H[X,Y,Z] + H[Z] \leq H[X,Z] + H[Y,Z].$$ -/
lemma entropy_triple_add_entropy_le {S U V : Type*}
    [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [Fintype V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (κ : kernel T (S × U × V)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[κ, μ] + Hk[snd (snd κ), μ] ≤ Hk[deleteMiddle κ, μ] + Hk[snd κ, μ] := by
  rw [chain_rule' κ, chain_rule' (deleteMiddle κ), chain_rule' (snd κ)]
  simp only [snd_deleteMiddle, fst_deleteMiddle, add_assoc]
  refine add_le_add le_rfl ?_
  rw [add_comm (Hk[snd (snd κ) , μ])]
  simp_rw [← add_assoc]
  refine add_le_add ?_ le_rfl
  rw [add_comm]
  refine add_le_add ?_ le_rfl
  exact entropy_submodular _ _

lemma entropy_reverse {S U V : Type*}
    [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [Fintype V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (κ : kernel T (S × U × V)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[reverse κ, μ] = Hk[κ, μ] := by
  sorry

/-- The submodularity inequality:
$$ H[X,Y,Z] + H[X] \leq H[X,Z] + H[X,Y].$$ -/
lemma entropy_triple_add_entropy_le' {S U V : Type*}
    [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [Fintype V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (κ : kernel T (S × U × V)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[κ, μ] + Hk[fst κ, μ] ≤ Hk[deleteMiddle κ, μ] + Hk[deleteRight κ, μ] := by
  have h2 : fst κ = snd (snd (reverse κ)) := sorry
  rw [← entropy_reverse κ μ, h2]
  have : IsMarkovKernel (reverse κ) := sorry
  refine (entropy_triple_add_entropy_le (reverse κ) μ).trans ?_
  refine add_le_add ?_ ?_
  · sorry -- use ← entropy_swapRight
  · sorry -- use ← entropy_swapRight

-- `κ` is `⟨X,Y⟩`, `η` is `Z`. Independence is expressed through the product `×ₖ`.
--lemma ent_of_diff_le (κ : T → G × G) (η : T → G) [IsMarkovKernel κ] [IsMarkovKernel η]
--    [IsProbabilityMeasure μ] :
--    Hk[map κ (fun p ↦ p.1 - p.2) measurable_sub, μ]
--      ≤ Hk[map ((fst κ) ×ₖ η) (fun p ↦ p.1 - p.2) measurable_sub, μ]
--        + Hk[map (η ×ₖ (snd κ)) (fun p ↦ p.1 - p.2) measurable_sub, μ] - Hk[η, μ] := by
--  sorry
  --have h1 : H[⟨X - Z, ⟨Y, X - Y⟩⟩; μ] + H[X - Y; μ] ≤ H[⟨X - Z, X - Y⟩; μ] + H[⟨Y, X - Y⟩; μ] :=
  --  entropy_triple_add_entropy_le μ (hX.sub hZ) hY (hX.sub hY)
  --have h2 : H[⟨X - Z, X - Y⟩ ; μ] ≤ H[X - Z ; μ] + H[Y - Z ; μ] := by
  --  calc H[⟨X - Z, X - Y⟩ ; μ] ≤ H[⟨X - Z, Y - Z⟩ ; μ] := by
  --        have : ⟨X - Z, X - Y⟩ = (fun p ↦ (p.1, p.1 - p.2)) ∘ ⟨X - Z, Y - Z⟩ := by ext1; simp
  --        rw [this]
  --        exact entropy_comp_le μ ((hX.sub hZ).prod_mk (hY.sub hZ)) _
  --  _ ≤ H[X - Z ; μ] + H[Y - Z ; μ] := by
  --        have h : 0 ≤ H[X - Z ; μ] + H[Y - Z ; μ] - H[⟨X - Z, Y - Z⟩ ; μ] :=
  --          mutualInformation_nonneg (hX.sub hZ) (hY.sub hZ) μ
  --        linarith
  --have h3 : H[⟨ Y, X - Y ⟩ ; μ] ≤ H[⟨ X, Y ⟩ ; μ] := by
  --  have : ⟨Y, X - Y⟩ = (fun p ↦ (p.2, p.1 - p.2)) ∘ ⟨X, Y⟩ := by ext1; simp
  --  rw [this]
  --  exact entropy_comp_le μ (hX.prod_mk hY) _
  --have h4 : H[⟨X - Z, ⟨Y, X - Y⟩⟩; μ] = H[⟨X, ⟨Y, Z⟩⟩ ; μ] := by
  --  refine entropy_of_comp_eq_of_comp μ ((hX.sub hZ).prod_mk (hY.prod_mk (hX.sub hY)))
  --    (hX.prod_mk (hY.prod_mk hZ))
  --    (fun p : G × (G × G) ↦ (p.2.2 + p.2.1, p.2.1, -p.1 + p.2.2 + p.2.1))
  --    (fun p : G × G × G ↦ (p.1 - p.2.2, p.2.1, p.1 - p.2.1)) ?_ ?_
  --  · ext1; simp
  --  · ext1; simp
  --have h5 : H[⟨X, ⟨Y, Z⟩⟩ ; μ] = H[⟨X, Y⟩ ; μ] + H[Z ; μ] := by
  --  rw [entropy_assoc hX hY hZ, entropy_pair_eq_add (hX.prod_mk hY) hZ]
  --  exact h
  --rw [h4, h5] at h1
  --calc H[X - Y; μ] ≤ H[X - Z; μ] + H[Y - Z; μ] - H[Z; μ] := by linarith
  --_ = H[X - Z; μ] + H[Z - Y; μ] - H[Z; μ] := by
  --  congr 2
  --  rw [entropy_sub_comm hY hZ]

end ProbabilityTheory.kernel
