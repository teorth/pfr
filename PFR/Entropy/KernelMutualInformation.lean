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
  [Fintype V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]
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

section measurableEquiv

variable {α β γ δ : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {_ : MeasurableSpace δ}

def assocEquiv : α × β × γ ≃ᵐ (α × β) × γ where
  toFun := fun p ↦ ((p.1, p.2.1), p.2.2)
  invFun := fun p ↦ (p.1.1, (p.1.2, p.2))
  left_inv := fun p ↦ by simp
  right_inv := fun p ↦ by simp
  measurable_toFun := (measurable_fst.prod_mk (measurable_fst.comp measurable_snd)).prod_mk
    (measurable_snd.comp measurable_snd)
  measurable_invFun := (measurable_fst.comp measurable_fst).prod_mk
    ((measurable_snd.comp measurable_fst).prod_mk measurable_snd)

end measurableEquiv

section
variable {α β γ δ ε : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {_ : MeasurableSpace ε}

lemma map_map (κ : kernel α β) {f : β → γ} (hf : Measurable f) {g : γ → δ} (hg : Measurable g) :
    map (map κ f hf) g hg = map κ (g ∘ f) (hg.comp hf) := by
  ext x s _
  rw [map_apply, map_apply, map_apply, Measure.map_map hg hf]

@[simp]
lemma map_id (κ : kernel α β) : map κ id measurable_id = κ := by
  ext x s _
  rw [map_apply]
  simp

lemma map_swapRight (κ : kernel α (β × γ)) {f : (γ × β) → δ} (hf : Measurable f) :
    map (swapRight κ) f hf = map κ (f ∘ Prod.swap) (hf.comp measurable_swap) := by
  rw [swapRight, map_map]

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
  · rfl
  · exact measurable_snd.comp measurable_snd

@[simp]
lemma snd_deleteMiddle (κ : kernel α (β × γ × δ)) : snd (deleteMiddle κ) = snd (snd κ) := by
  rw [deleteMiddle, snd_map_prod]
  · rw [snd, snd, map_map]
    rfl
  · exact measurable_fst

@[simp]
lemma deleteMiddle_map_prod (κ : kernel α β) {f : β → γ} {g : β → δ} {g' : β → ε}
    (hf : Measurable f) (hg : Measurable g) (hg' : Measurable g') :
    deleteMiddle (map κ (fun b ↦ (f b, g b, g' b)) (hf.prod_mk (hg.prod_mk hg')))
      = map κ (fun b ↦ (f b, g' b)) (hf.prod_mk hg') := by
  simp only [deleteMiddle, map_map]
  congr

@[simp]
lemma deleteMiddle_compProd (ξ : kernel α β) [IsSFiniteKernel ξ]
    (κ : kernel (α × β) (γ × δ)) [IsSFiniteKernel κ] :
    deleteMiddle (ξ ⊗ₖ κ) = ξ ⊗ₖ snd κ := by
  ext x s hs
  rw [deleteMiddle, map_apply' _ _ _ hs, compProd_apply _ _ _ hs, compProd_apply]
  swap; · exact measurable_fst.prod_mk measurable_snd.snd hs
  congr with b
  simp only [Set.mem_preimage]
  rw [snd_apply']
  swap; · exact measurable_prod_mk_left hs
  congr

noncomputable
def deleteRight (κ : kernel α (β × γ × δ)) :
    kernel α (β × γ) :=
  map κ (fun p ↦ (p.1, p.2.1)) (measurable_fst.prod_mk (measurable_fst.comp measurable_snd))

instance (κ : kernel α (β × γ × δ)) [IsMarkovKernel κ] :
    IsMarkovKernel (deleteRight κ) := by
  rw [deleteRight]; infer_instance

@[simp]
lemma fst_deleteRight (κ : kernel α (β × γ × δ)) : fst (deleteRight κ) = fst κ := by
  rw [deleteRight, fst_map_prod]
  · rfl
  · exact measurable_fst.comp measurable_snd

@[simp]
lemma snd_deleteRight (κ : kernel α (β × γ × δ)) : snd (deleteRight κ) = fst (snd κ) := by
  rw [deleteRight, snd_map_prod]
  · rw [fst, snd, map_map]
    rfl
  · exact measurable_fst

@[simp]
lemma deleteRight_map_prod (κ : kernel α β) {f : β → γ} {g : β → δ} {g' : β → ε}
    (hf : Measurable f) (hg : Measurable g) (hg' : Measurable g') :
    deleteRight (map κ (fun b ↦ (f b, g b, g' b)) (hf.prod_mk (hg.prod_mk hg')))
      = map κ (fun b ↦ (f b, g b)) (hf.prod_mk hg) := by
  simp only [deleteRight, map_map]
  congr

noncomputable
def reverse (κ : kernel α (β × γ × δ)) :
    kernel α (δ × γ × β) :=
  map κ (fun p ↦ (p.2.2, (p.2.1, p.1)))
    ((measurable_snd.comp measurable_snd).prod_mk
      ((measurable_fst.comp measurable_snd).prod_mk measurable_fst))

@[simp]
lemma reverse_reverse (κ : kernel α (β × γ × δ)) :
    reverse (reverse κ) = κ := by
  have : ((fun p : δ × γ × β ↦ (p.2.2, p.2.1, p.1)) ∘ fun p ↦ (p.2.2, p.2.1, p.1)) = id := by
    ext1; simp
  simp [reverse, map_map, this]

instance (κ : kernel α (β × γ × δ)) [IsMarkovKernel κ] :
    IsMarkovKernel (reverse κ) := by
  rw [reverse]
  infer_instance

@[simp]
lemma swapRight_deleteMiddle_reverse (κ : kernel α (β × γ × δ)) :
    swapRight (deleteMiddle (reverse κ)) = deleteMiddle κ := by
  simp only [swapRight, reverse, deleteMiddle, map_map]
  congr

@[simp]
lemma swapRight_snd_reverse (κ : kernel α (β × γ × δ)) :
    swapRight (snd (reverse κ)) = deleteRight κ := by
  simp only [swapRight, reverse, deleteMiddle, snd, map_map]
  congr

@[simp]
lemma swapRight_deleteRight_reverse (κ : kernel α (β × γ × δ)) :
    swapRight (deleteRight (reverse κ)) = snd κ := by
  simp only [swapRight, reverse, deleteRight, snd, map_map]
  congr

end

lemma compProd_assoc (ξ : kernel T S) [IsMarkovKernel ξ]
    (κ : kernel (T × S) U) [IsMarkovKernel κ] (η : kernel (T × S × U) V) [IsMarkovKernel η] :
    map ((ξ ⊗ₖ κ) ⊗ₖ η) assocEquiv.symm assocEquiv.symm.measurable
      = ξ ⊗ₖ (κ ⊗ₖ (comap η assocEquiv.symm assocEquiv.symm.measurable)) := by
  ext x s hs
  rw [map_apply' _ _ _ hs, compProd_apply _ _ _ (assocEquiv.symm.measurable hs),
    compProd_apply _ _ _ hs, lintegral_compProd]
  swap; · exact measurable_kernel_prod_mk_left' (assocEquiv.symm.measurable hs) _
  congr with a
  rw [compProd_apply]
  swap; · exact measurable_prod_mk_left hs
  congr

lemma Measure.compProd_compProd (μ : Measure T) [IsProbabilityMeasure μ]
    (ξ : kernel T S) [IsMarkovKernel ξ] (κ : kernel (T × S) U) [IsMarkovKernel κ] :
    μ ⊗ₘ (ξ ⊗ₖ κ) = (μ ⊗ₘ ξ ⊗ₘ κ).map assocEquiv.symm := by
  ext s hs
  rw [Measure.compProd_apply _ _ hs, Measure.map_apply assocEquiv.symm.measurable hs,
    Measure.compProd_apply _ _ (assocEquiv.symm.measurable hs),
    Measure.lintegral_compProd]
  swap; · exact measurable_kernel_prod_mk_left (assocEquiv.symm.measurable hs)
  congr with a
  rw [compProd_apply _ _ _ (measurable_prod_mk_left hs)]
  congr

lemma Measure.compProd_compProd' (μ : Measure T) [IsProbabilityMeasure μ]
    (ξ : kernel T S) [IsMarkovKernel ξ] (κ : kernel (T × S) U) [IsMarkovKernel κ] :
    μ ⊗ₘ (ξ ⊗ₖ κ) = Measure.comap (assocEquiv : T × S × U ≃ᵐ (T × S) × U) (μ ⊗ₘ ξ ⊗ₘ κ) := by
  rw [← MeasurableEquiv.map_symm, Measure.compProd_compProd]

lemma Measure.compProd_compProd'' (μ : Measure T) [IsProbabilityMeasure μ]
    (ξ : kernel T S) [IsMarkovKernel ξ] (κ : kernel (T × S) U) [IsMarkovKernel κ] :
    μ ⊗ₘ ξ ⊗ₘ κ = Measure.comap assocEquiv.symm (μ ⊗ₘ (ξ ⊗ₖ κ)) := by
  rw [Measure.compProd_compProd, MeasurableEquiv.comap_symm, Measure.map_map]
  · simp
  · exact assocEquiv.measurable
  · exact assocEquiv.symm.measurable

-- from kernel (T × S × U) V ; Measure (T × S × U)
-- to kernel (T × S) V ; Measure (T × S)
lemma entropy_submodular_compProd (ξ : kernel T S) [IsMarkovKernel ξ]
    (κ : kernel (T × S) U) [IsMarkovKernel κ] (η : kernel (T × S × U) V) [IsMarkovKernel η]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[η, μ ⊗ₘ (ξ ⊗ₖ κ)]
      ≤ Hk[snd (κ ⊗ₖ (comap η assocEquiv.symm assocEquiv.symm.measurable)), μ ⊗ₘ ξ] := by
  have h_meas := (assocEquiv : T × S × U ≃ᵐ (T × S) × U).symm.measurable
  have h := entropy_condKernel_le_entropy_snd
    (κ ⊗ₖ (comap η assocEquiv.symm h_meas)) (μ ⊗ₘ ξ)
  simp only [fst_compProd] at h
  have : condKernel (κ ⊗ₖ comap η ↑assocEquiv.symm h_meas)
      =ᵐ[μ ⊗ₘ ξ ⊗ₘ κ] comap η ↑assocEquiv.symm h_meas := by
    exact condKernel_compProd_ae_eq κ (comap η ↑assocEquiv.symm assocEquiv.symm.measurable)
      (μ ⊗ₘ ξ)
  rw [entropy_congr this, Measure.compProd_compProd''] at h
  have : IsFiniteMeasure (Measure.comap (↑assocEquiv.symm) (μ ⊗ₘ (ξ ⊗ₖ κ))) := by
    rw [MeasurableEquiv.comap_symm]
    infer_instance
  rw [entropy_comap_equiv] at h
  exact h

lemma entropy_condKernel_compProd_triple (ξ : kernel T S) [IsMarkovKernel ξ]
    (κ : kernel (T × S) U) [IsMarkovKernel κ] (η : kernel (T × S × U) V) [IsMarkovKernel η]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[condKernel (ξ ⊗ₖ κ ⊗ₖ η) , μ ⊗ₘ (ξ ⊗ₖ κ)] = Hk[η, μ ⊗ₘ (ξ ⊗ₖ κ)] :=
  entropy_congr (condKernel_compProd_ae_eq (ξ ⊗ₖ κ) η μ)

/- $$ H[X,Y,Z] + H[X] \leq H[Z,X] + H[Y,X].$$ -/
lemma entropy_compProd_triple_add_entropy_le (ξ : kernel T S) [IsMarkovKernel ξ]
    (κ : kernel (T × S) U) [IsMarkovKernel κ] (η : kernel (T × S × U) V) [IsMarkovKernel η]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[(ξ ⊗ₖ κ) ⊗ₖ η, μ] + Hk[ξ, μ]
      ≤ Hk[ξ ⊗ₖ snd (κ ⊗ₖ comap η assocEquiv.symm assocEquiv.symm.measurable), μ]
       + Hk[ξ ⊗ₖ κ, μ] := by
  rw [chain_rule,
    chain_rule (ξ ⊗ₖ snd (κ ⊗ₖ comap η ↑assocEquiv.symm assocEquiv.symm.measurable))]
  simp only [fst_compProd, entropy_condKernel_compProd_triple, fst_deleteMiddle]
  calc Hk[ξ ⊗ₖ κ , μ] + Hk[η , μ ⊗ₘ (ξ ⊗ₖ κ)] + Hk[ξ , μ]
    = Hk[ξ , μ] + Hk[ξ ⊗ₖ κ , μ] + Hk[η , μ ⊗ₘ (ξ ⊗ₖ κ)] := by abel
  _ ≤ Hk[ξ , μ] + Hk[ξ ⊗ₖ κ , μ]
    + Hk[condKernel (ξ ⊗ₖ snd (κ ⊗ₖ comap η assocEquiv.symm _)) , μ ⊗ₘ ξ] := by
        refine add_le_add le_rfl ?_
        refine (entropy_submodular_compProd ξ κ η μ).trans_eq ?_
        refine entropy_congr ?_
        exact (condKernel_compProd_ae_eq _ _ _).symm
  _ = Hk[ξ , μ] + Hk[condKernel (ξ ⊗ₖ snd (κ ⊗ₖ comap η assocEquiv.symm _)) , μ ⊗ₘ ξ]
    + Hk[ξ ⊗ₖ κ , μ] := by abel

/-- The submodularity inequality:
$$ H[X,Y,Z] + H[X] \leq H[X,Z] + H[X,Y].$$ -/
lemma entropy_triple_add_entropy_le' (κ : kernel T (S × U × V)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[κ, μ] + Hk[fst κ, μ] ≤ Hk[deleteMiddle κ, μ] + Hk[deleteRight κ, μ] := by
  set κ' := map κ assocEquiv assocEquiv.measurable with hκ'_def
  let ξ := fst (fst κ')
  let κ'' := condKernel (fst κ')
  let η := condKernel κ'
  have hξ_eq : ξ = fst κ := by
    simp only [fst._eq_1, assocEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, map_map]
    congr
  have h_compProd_eq : ξ ⊗ₖ κ'' = fst κ' := (disintegration (fst κ')).symm
  have h_compProd_triple_eq : (ξ ⊗ₖ κ'') ⊗ₖ η = κ' := by
    rw [h_compProd_eq]
    exact (disintegration κ').symm
  have h_compProd_triple_eq' : ξ ⊗ₖ (κ'' ⊗ₖ comap η assocEquiv.symm assocEquiv.symm.measurable)
      = κ := by
    rw [← compProd_assoc, h_compProd_triple_eq,hκ'_def, map_map]
    simp
  have h := entropy_compProd_triple_add_entropy_le ξ κ'' η μ
  rw [← hξ_eq]
  have h_right : deleteRight κ = fst κ' := by
    simp only [κ', deleteRight, fst, map_map]
    congr
  have h_middle : deleteMiddle κ
      = ξ ⊗ₖ snd (κ'' ⊗ₖ comap η assocEquiv.symm assocEquiv.symm.measurable) := by
    rw [← deleteMiddle_compProd, h_compProd_triple_eq']
  have hκ : Hk[κ, μ] = Hk[κ', μ] := by
    rw [hκ'_def, entropy_map_of_injective]
    exact assocEquiv.injective
  rw [h_right, h_middle, hκ, ← h_compProd_triple_eq, fst_compProd]
  exact h

lemma entropy_reverse (κ : kernel T (S × U × V)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[reverse κ, μ] = Hk[κ, μ] := by
  refine le_antisymm ?_ ?_
  · exact entropy_map_le κ μ (fun p ↦ (p.2.2, p.2.1, p.1))
  · conv_lhs => rw [← reverse_reverse κ]
    exact entropy_map_le (reverse κ) μ (fun p ↦ (p.2.2, p.2.1, p.1))

/-- The submodularity inequality:
$$ H[X,Y,Z] + H[Z] \leq H[X,Z] + H[Y,Z].$$ -/
lemma entropy_triple_add_entropy_le (κ : kernel T (S × U × V)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[κ, μ] + Hk[snd (snd κ), μ] ≤ Hk[deleteMiddle κ, μ] + Hk[snd κ, μ] := by
  have h2 : fst (reverse κ) = snd (snd κ) := by
    simp only [fst, reverse, snd, map_map]
    congr
  rw [← entropy_reverse κ μ, ← h2]
  refine (entropy_triple_add_entropy_le' (reverse κ) μ).trans ?_
  refine add_le_add ?_ ?_
  · rw [← entropy_swapRight]
    simp
  · rw [← entropy_swapRight]
    simp

end ProbabilityTheory.kernel
