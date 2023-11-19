import PFR.Entropy.Disintegration

/-!
# Entropy of a kernel with respect to a measure

## Main definitions

* `kernel.entropy`: entropy of a kernel `κ` with respect to a measure `μ`,
  `μ[fun t ↦ measureEntropy (κ t)]`. We use the notation `Hk[κ, μ]`.

## Main statements

* `chain_rule`: `Hk[κ, μ] = Hk[fst κ, μ] + Hk[condKernel κ, μ ⊗ₘ (fst κ)]`.
* `entropy_map_le`: data-processing inequality for the kernel entropy

## Notations

* `Hk[κ, μ] = kernel.entropy κ μ`

-/

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators


namespace ProbabilityTheory.kernel

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
  {κ : kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}

/-- Entropy of a kernel with respect to a measure. -/
noncomputable
def entropy (κ : kernel T S) (μ : Measure T) := μ[fun y ↦ Hm[κ y]]

notation3:100 "Hk[" κ " , " μ "]" => entropy κ μ

@[simp]
lemma entropy_zero_measure (κ : kernel T S) : Hk[κ, (0 : Measure T)] = 0 := by simp [entropy]

@[simp]
lemma entropy_zero_kernel (μ : Measure T) : Hk[(0 : kernel T S), μ] = 0 := by simp [entropy]

lemma entropy_congr {κ η : kernel T S} (h : κ =ᵐ[μ] η) : Hk[κ, μ] = Hk[η, μ] := by
  simp_rw [entropy]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

lemma entropy_nonneg (κ : kernel T S) (μ : Measure T) :
    0 ≤ Hk[κ, μ] := integral_nonneg (fun _ ↦ measureEntropy_nonneg _)

lemma entropy_le_log_card (κ : kernel T S) (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[κ, μ] ≤ log (Fintype.card S) := by
  refine (integral_mono_of_nonneg ?_ (integrable_const (log (Fintype.card S))) ?_).trans ?_
  · exact ae_of_all _ (fun _ ↦ measureEntropy_nonneg _)
  · exact ae_of_all _ (fun _ ↦ measureEntropy_le_log_card _)
  · simp

lemma entropy_eq_integral_sum (κ : kernel T S) [IsMarkovKernel κ] (μ : Measure T) :
    Hk[κ, μ] = μ[fun y ↦ ∑ x, negIdMulLog (κ y {x}).toReal] := by
  simp_rw [entropy, measureEntropy_of_isProbabilityMeasure]

-- entropy_map_of_injective is a special case of this (see def of map)
lemma entropy_snd_compProd_deterministic_of_injective (κ : kernel T S) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] (f : T × S → U)
    (hf : ∀ t, Function.Injective (fun x ↦ f (t, x))) :
    Hk[snd (κ ⊗ₖ deterministic f (measurable_of_finite f)), μ] = Hk[κ, μ] := by
  have : ∀ t, snd (κ ⊗ₖ deterministic f (measurable_of_finite f)) t
      = map κ (fun x ↦ f (t, x)) (measurable_of_finite _) t := by
    intro t
    ext s hs
    rw [snd_apply' _ _ hs, compProd_deterministic_apply, map_apply' _ _ _ hs]
    · congr
    · exact measurable_snd hs
  simp_rw [entropy, integral_eq_sum, smul_eq_mul]
  congr with y
  rw [this, map_apply, measureEntropy_map_of_injective _ _ (hf y)]

lemma entropy_map_of_injective
    (κ : kernel T S) (μ : Measure T) (f : S → U) (hf : Function.Injective f) :
    Hk[map κ f (measurable_of_finite f), μ] = Hk[κ, μ] := by
  simp_rw [entropy, map_apply, measureEntropy_map_of_injective _ _ hf]

lemma entropy_map_swap (κ : kernel T (S × U)) (μ : Measure T) :
    Hk[map κ Prod.swap measurable_swap, μ] = Hk[κ, μ] :=
  entropy_map_of_injective κ μ Prod.swap Prod.swap_injective

lemma entropy_swapRight (κ : kernel T (S × U)) (μ : Measure T) :
    Hk[swapRight κ, μ] = Hk[κ, μ] := by
  rw [swapRight, entropy_map_swap]

lemma entropy_comap {T' : Type*} [Fintype T'] [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : kernel T S) (μ : Measure T) (f : T' → T) (hf : MeasurableEmbedding f)
    (hf_range : Set.range f =ᵐ[μ] Set.univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure (μ.comap f)] :
    Hk[comap κ f hf.measurable, μ.comap f] = Hk[κ, μ] := by
  simp_rw [entropy, integral_eq_sum, Measure.comap_apply f hf.injective hf.measurableSet_image' _
    (measurableSet_singleton _)]
  simp only [Set.image_singleton, smul_eq_mul]
  simp_rw [comap_apply]
  classical
  rw [← Finset.sum_image (f := fun x ↦ (μ {x}).toReal * measureEntropy (κ x)) (g := f)]
  · rw [Finset.sum_subset]
    · exact Finset.subset_univ _
    · simp only [Finset.mem_univ, Finset.mem_image, true_and, not_exists, mul_eq_zero,
        forall_true_left]
      intro x hx
      simp only [ae_eq_univ] at hf_range
      have : {x} ⊆ (Set.range f)ᶜ := by simp [hx]
      rw [ENNReal.toReal_eq_zero_iff]
      exact Or.inl (Or.inl (measure_mono_null this hf_range))
  · simp only [Finset.mem_univ, forall_true_left]
    exact hf.injective

lemma entropy_comap_equiv {T' : Type*} [Fintype T'] [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : kernel T S) (μ : Measure T) (f : T' ≃ᵐ T)
    [IsFiniteMeasure μ] [IsFiniteMeasure (μ.comap f)] :
    Hk[comap κ f f.measurable, μ.comap f] = Hk[κ, μ] := by
  simp_rw [entropy, integral_eq_sum]
  simp_rw [Measure.comap_apply f f.injective f.measurableEmbedding.measurableSet_image' _
    (measurableSet_singleton _)]
  simp only [Set.image_singleton, smul_eq_mul]
  simp_rw [comap_apply]
  rw [Finset.sum_bij (fun x _ ↦ f x)]
  · simp
  · simp only [Finset.mem_univ, forall_true_left, implies_true]
  · simp
  · simp only [Finset.mem_univ, exists_const, forall_true_left]
    have h := f.surjective
    intro b
    exact ⟨(h b).choose, (h b).choose_spec.symm⟩

lemma entropy_comap_swap
    {T' : Type*} [Fintype T'] [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : kernel (T' × T) S) (μ : Measure (T' × T)) [IsFiniteMeasure μ] :
    Hk[comap κ Prod.swap measurable_swap, μ.comap Prod.swap] = Hk[κ, μ] := by
  have : IsFiniteMeasure (Measure.comap (↑MeasurableEquiv.prodComm) μ) := by
    constructor
    rw [Measure.comap_apply]
    · exact measure_lt_top _ _
    · exact MeasurableEquiv.prodComm.injective
    · intro s hs
      exact MeasurableEquiv.prodComm.measurableEmbedding.measurableSet_image' hs
    · exact MeasurableSet.univ
  exact entropy_comap_equiv κ μ MeasurableEquiv.prodComm

lemma entropy_prodMkLeft_unit (κ : kernel T S) (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[prodMkLeft Unit κ, μ.map (Prod.mk ())] = Hk[κ, μ] := by
  rw [entropy, integral_eq_sum, Fintype.sum_prod_type]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, smul_eq_mul, Finset.sum_singleton]
  simp_rw [Measure.map_apply measurable_prod_mk_left (measurableSet_singleton _)]
  have : ∀ x : T, Prod.mk () ⁻¹' {(PUnit.unit, x)} = {x} := fun x ↦ by ext; simp
  simp_rw [this, prodMkLeft_apply, entropy, integral_eq_sum, smul_eq_mul]

lemma entropy_compProd_aux [IsFiniteMeasure μ] (κ : kernel T S) [IsMarkovKernel κ]
    (η : kernel (T × S) U) [IsMarkovKernel η] :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ]
      + μ[fun t ↦ Hk[comap η (Prod.mk t) measurable_prod_mk_left, (κ t)]] := by
  simp_rw [entropy, measureEntropy_of_isProbabilityMeasure,
    compProd_apply κ η _ (measurableSet_singleton _), lintegral_eq_sum]
  have : ∀ (x : T) (su : S × U),
      ∑ s : S, κ x {s} * η (x, s) {c | (s, c) ∈ ({su} : Set (S × U))}
      = κ x {su.1} * η (x, su.1) {su.2} := by
    intro x su
    classical
    have : ∀ s, {c | (s, c) ∈ ({su} : Set (S × U))} = if s = su.1 then {su.2} else ∅ := by
      intro s
      ext u
      simp only [Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_ite_empty_right]
      rw [← Prod.eta su]
      exact Prod.mk.inj_iff
    simp_rw [this]
    rw [Finset.sum_eq_single su.1]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  simp_rw [this, ENNReal.toReal_mul, negIdMulLog_mul, Finset.sum_neg_distrib,
    Finset.sum_add_distrib]
  have h_left : ∀ x, -∑ su : S × U,
        (η (x, su.1) {su.2}).toReal * (κ x {su.1}).toReal * log (κ x {su.1}).toReal
      = ∑ s, negIdMulLog (κ x {s}).toReal := by
    intro hX
    simp_rw [mul_assoc, Fintype.sum_prod_type, ← Finset.sum_mul]
    simp [negIdMulLog]
  have h_right : ∀ x, -∑ su : S × U,
        (κ x {su.1}).toReal * (η (x, su.1) {su.2}).toReal * log (η (x, su.1) {su.2}).toReal
      = ∑ s, (κ x {s}).toReal * ∑ u, negIdMulLog (η (x, s) {u}).toReal := by
    intro x
    simp_rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    congr with s
    simp_rw [mul_assoc, neg_mul_eq_mul_neg (κ x {s}).toReal]
    simp only [mul_neg, Finset.sum_neg_distrib, negIdMulLog, neg_mul, neg_inj]
    rw [Finset.mul_sum]
  simp_rw [neg_add, h_left, h_right, integral_eq_sum, smul_add]
  rw [Finset.sum_add_distrib]
  congr

lemma entropy_compProd' [IsFiniteMeasure μ] (κ : kernel T S) [IsMarkovKernel κ]
    (η : kernel (T × S) U) [IsMarkovKernel η] :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[condKernel (κ ⊗ₖ η), μ ⊗ₘ κ] := by
  rw [entropy_compProd_aux]
  congr
  simp_rw [entropy, integral_eq_sum, measureEntropy_of_isProbabilityMeasure,
    Measure.compProd_apply _ _ (measurableSet_singleton _), lintegral_eq_sum]
  simp only [smul_eq_mul, Fintype.sum_prod_type]
  congr with x
  have : ∀ (b : S),
      (∑ t : T, μ {t} * κ t ((Prod.mk t ⁻¹' {(x, b)}))).toReal
      = (μ {x}).toReal * (κ x {b}).toReal := by
    intro b
    have h_prod_sing : ∀ b : S, {(x, b)} = {x} ×ˢ {b} := by
      simp only [Set.prod_singleton, Set.image_singleton, implies_true]
    classical
    simp_rw [h_prod_sing, Set.mk_preimage_prod_right_eq_if]
    rw [← ENNReal.toReal_mul, Finset.sum_eq_single x]
    · simp only [Set.mem_singleton_iff, ite_true, ENNReal.toReal_mul]
    · simp only [Finset.mem_univ, ne_eq, Set.mem_singleton_iff, mul_eq_zero, forall_true_left]
      intro y hyx
      simp [hyx]
    · simp
  simp_rw [this, mul_assoc]
  rw [← Finset.mul_sum]
  congr with y
  by_cases hy : κ x {y} = 0
  · simp [hy]
  · congr with z
    rw [condKernel_compProd_apply' _ _ _ hy (measurableSet_singleton _)]
    congr

lemma entropy_compProd [IsFiniteMeasure μ] (κ : kernel T S) [IsMarkovKernel κ]
    (η : kernel (T × S) U) [IsMarkovKernel η] :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[η, μ ⊗ₘ κ] := by
  rw [entropy_compProd', entropy_congr (condKernel_compProd_ae_eq κ η)]

@[simp]
lemma entropy_deterministic (f : T → S) (μ : Measure T) [IsFiniteMeasure μ] :
    Hk[deterministic f (measurable_of_finite f), μ] = 0 := by
  simp_rw [entropy, integral_eq_sum, smul_eq_mul, deterministic_apply, measureEntropy_dirac,
    mul_zero, Finset.sum_const_zero]

@[simp]
lemma entropy_compProd_deterministic
    (κ : kernel T S) [IsMarkovKernel κ] (μ : Measure T) [IsFiniteMeasure μ] (f : T × S → U) :
    Hk[κ ⊗ₖ (deterministic f (measurable_of_finite f)), μ] = Hk[κ, μ] := by
  simp [entropy_compProd]

lemma chain_rule (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[κ, μ] = Hk[fst κ, μ] + Hk[condKernel κ, μ ⊗ₘ (fst κ)] := by
  conv_lhs => rw [disintegration κ]
  rw [entropy_compProd', ← disintegration κ]

lemma chain_rule' (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[κ, μ] = Hk[snd κ, μ] + Hk[condKernel (swapRight κ), μ ⊗ₘ (snd κ)] := by
  rw [← entropy_swapRight, chain_rule]
  simp

lemma entropy_prodMkRight (κ : kernel T S) (η : kernel T U)
    [IsMarkovKernel κ] [IsMarkovKernel η] (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[prodMkRight η S, μ ⊗ₘ κ] = Hk[η, μ] := by
  simp_rw [entropy, prodMkRight_apply, integral_eq_sum,
    Measure.compProd_apply _ _ (measurableSet_singleton _), lintegral_eq_sum, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul]
  suffices ∀ x, (∑ a : S, (∑ b : T, μ {b} * κ b (Prod.mk b ⁻¹' {(x, a)})).toReal)
      = (μ {x}).toReal by
    simp_rw [this]
  intro x
  classical
  simp_rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod_right_eq_if]
  simp only [Set.mem_singleton_iff]
  have : ∀ a : S, (∑ b : T, μ {b} * κ b (if b = x then {a} else ∅)).toReal
      = (μ {x}).toReal * (κ x {a}).toReal := by
    intro a
    rw [Finset.sum_eq_single x]
    · simp only [ite_true, ENNReal.toReal_mul]
    · simp only [Finset.mem_univ, ne_eq, mul_eq_zero, forall_true_left]
      intro b hb
      simp [hb]
    · simp [measure_ne_top]
  simp_rw [this, ← Finset.mul_sum, sum_toReal_measure_singleton]
  simp

lemma entropy_swapLeft_prodMkLeft (κ : kernel T S) (η : kernel T U)
    [IsMarkovKernel κ] [IsMarkovKernel η] (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[swapLeft (prodMkLeft S η), μ ⊗ₘ κ] = Hk[η, μ] :=
  entropy_prodMkRight κ η μ

lemma entropy_prod (κ : kernel T S) (η : kernel T U) [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[κ ×ₖ η, μ] = Hk[κ, μ] + Hk[η, μ] := by
  rw [chain_rule, fst_prod, entropy_congr (condKernel_prod_ae_eq _ _), entropy_swapLeft_prodMkLeft]

/-- Data-processing inequality for the kernel entropy. -/
lemma entropy_map_le
    (κ : kernel T S) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] (f : S → U) :
    Hk[map κ f (measurable_of_finite f), μ] ≤ Hk[κ, μ] := by
  have : Hk[κ, μ] = Hk[map κ (fun x ↦ (x, f x)) (measurable_of_finite _), μ] := by
    refine (entropy_map_of_injective κ μ (fun x ↦ (x, f x)) ?_).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule', snd_map_prod _ measurable_id', le_add_iff_nonneg_right]
  exact entropy_nonneg _ _

lemma entropy_snd_le (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[snd κ, μ] ≤ Hk[κ, μ] :=
  entropy_map_le _ _ _

lemma entropy_fst_le (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[fst κ, μ] ≤ Hk[κ, μ] :=
  entropy_map_le _ _ _

end ProbabilityTheory.kernel
