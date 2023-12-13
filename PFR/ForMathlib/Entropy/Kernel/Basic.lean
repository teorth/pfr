import PFR.ForMathlib.Entropy.Measure
import PFR.Mathlib.MeasureTheory.Integral.Bochner
import PFR.Mathlib.Probability.Kernel.Disintegration

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
 [Countable S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
 [Countable T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
 [Countable U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
  {κ : kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}

/-- Entropy of a kernel with respect to a measure. -/
noncomputable
def entropy (κ : kernel T S) (μ : Measure T) := μ[fun y ↦ Hm[κ y]]

/-- Entropy of a kernel with respect to a measure. -/
notation3:100 "Hk[" κ " , " μ "]" => ProbabilityTheory.kernel.entropy κ μ

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

/-- The analogue of FiniteSupport for probability kernels.  For simplicity, we impose the hypothesis of a global set A which captures the mass of all possible values of the kernel-/
noncomputable def FiniteKernelSupport (κ : kernel T S) : Prop := ∃ A : Finset S, ∀ t : T, (κ t) Aᶜ  = 0

lemma entropy_le_log_card (κ : kernel T S) (μ : Measure T) [Fintype S] [IsProbabilityMeasure μ] :
    Hk[κ, μ] ≤ log (Fintype.card S) := by
  refine (integral_mono_of_nonneg ?_ (integrable_const (log (Fintype.card S))) ?_).trans ?_
  · exact ae_of_all _ (fun _ ↦ measureEntropy_nonneg _)
  · exact ae_of_all _ (fun _ ↦ measureEntropy_le_log_card _)
  · simp

lemma entropy_eq_integral_sum (κ : kernel T S) [IsMarkovKernel κ] (μ : Measure T) :
    Hk[κ, μ] = μ[fun y ↦ ∑' x, negMulLog (κ y {x}).toReal] := by
  simp_rw [entropy, measureEntropy_of_isProbabilityMeasure]

-- entropy_map_of_injective is a special case of this (see def of map)
lemma entropy_snd_compProd_deterministic_of_injective (κ : kernel T S) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] {f : T × S → U}
    (hf : ∀ t, Function.Injective (fun x ↦ f (t, x))) (hmes : Measurable f):
    Hk[snd (κ ⊗ₖ deterministic f hmes), μ] = Hk[κ, μ] := by
  have : ∀ t, snd (κ ⊗ₖ deterministic f hmes) t
      = map κ (fun x ↦ f (t, x)) (hmes.comp
        measurable_prod_mk_left) t := by
    intro t
    ext s hs
    rw [snd_apply' _ _ hs, compProd_deterministic_apply, map_apply' _ _ _ hs]
    · congr
    · exact measurable_snd hs
  simp_rw [entropy]
  congr with y
  convert measureEntropy_map_of_injective (κ y) _ (hmes.comp measurable_prod_mk_left) (hf y)
  rw [this y, map_apply]
  congr

lemma entropy_map_of_injective
    (κ : kernel T S) (μ : Measure T) {f : S → U} (hf : Function.Injective f) (hmes : Measurable f):
    Hk[map κ f hmes, μ] = Hk[κ, μ] := by
  simp_rw [entropy, map_apply, measureEntropy_map_of_injective _ _ hmes hf]

lemma entropy_map_swap (κ : kernel T (S × U)) (μ : Measure T) :
    Hk[map κ Prod.swap measurable_swap, μ] = Hk[κ, μ] := entropy_map_of_injective κ μ Prod.swap_injective _

lemma entropy_swapRight (κ : kernel T (S × U)) (μ : Measure T) :
    Hk[swapRight κ, μ] = Hk[κ, μ] := by
  rw [swapRight, entropy_map_swap]

lemma entropy_comap {T' : Type*}  [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : kernel T S) (μ : Measure T) (f : T' → T) (hf : MeasurableEmbedding f)
    (hf_range : Set.range f =ᵐ[μ] Set.univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure (μ.comap f)] (hfμ: FiniteSupport (μ.comap f)) :
    Hk[comap κ f hf.measurable, μ.comap f] = Hk[κ, μ] := by
  classical
  rcases hfμ with ⟨A, hA⟩
  have : μ (Finset.image f A: Set T)ᶜ = 0 := by
    rw [Finset.coe_image, Function.Injective.compl_image_eq hf.injective]
    simp
    constructor
    . rwa [<- Measure.comap_apply f hf.injective hf.measurableSet_image']
      exact MeasurableSet.compl (Finset.measurableSet A)
    exact ae_eq_univ.mp hf_range
  simp_rw [entropy]
  simp_rw [integral_eq_sum_finset' _ _ hA, integral_eq_sum_finset' _ _ this, Measure.comap_apply f hf.injective hf.measurableSet_image' _
    (measurableSet_singleton _)]
  simp only [Set.image_singleton, smul_eq_mul]
  simp_rw [comap_apply]
  rw [← Finset.sum_image (f := fun x ↦ (μ {x}).toReal * measureEntropy (κ x)) (g := f)]
  intro x _ y _ hxy
  exact hf.injective hxy

lemma entropy_comap_equiv {T' : Type*}  [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : kernel T S) {μ : Measure T} (f : T' ≃ᵐ T)
    [IsFiniteMeasure μ] (hμ: FiniteSupport μ) :
    Hk[comap κ f f.measurable, μ.comap f] = Hk[κ, μ] := by
  classical
  rcases hμ with ⟨A, hA⟩
  have : (μ.comap f) (Finset.image f.symm A: Set T')ᶜ = 0 := by
    rwa [Finset.coe_image, <-Set.image_compl_eq (MeasurableEquiv.bijective f.symm), Measure.comap_apply f (MeasurableEquiv.injective f),MeasurableEquiv.image_symm, MeasurableEquiv.image_preimage]
    . intro E
      exact (MeasurableEquiv.measurableSet_image f (s := E)).mpr
    simp
    exact Finset.measurableSet A
  have h : IsFiniteMeasure (μ.comap f) := by
    constructor
    rw [Measure.comap_apply f (MeasurableEquiv.injective f) _ μ MeasurableSet.univ]
    . exact measure_lt_top μ (⇑f '' Set.univ)
    intro E
    exact (MeasurableEquiv.measurableSet_image f (s := E)).mpr
  simp_rw [entropy, integral_eq_sum_finset' _ _ hA, integral_eq_sum_finset' _ _ this, Measure.comap_apply f f.injective f.measurableEmbedding.measurableSet_image' _
    (measurableSet_singleton _)]
  simp only [Set.image_singleton, smul_eq_mul]
  simp_rw [comap_apply]
  rw [Finset.sum_bij (fun x _ ↦ f x)]
  · simp
  · simp only [Finset.mem_univ, forall_true_left, implies_true]
  · simp
  intro b hb
  simp at hb
  use (f.symm b)
  have : f.symm b ∈ Finset.image (f.symm) A := by simp [hb]
  use this
  simp

lemma entropy_comap_swap
    {T' : Type*} [MeasurableSpace T'] [MeasurableSingletonClass T'] [Nonempty T']
    (κ : kernel (T' × T) S) {μ : Measure (T' × T)} [IsFiniteMeasure μ] (hμ: FiniteSupport μ) :
    Hk[comap κ Prod.swap measurable_swap, μ.comap Prod.swap] = Hk[κ, μ] := by
  have : IsFiniteMeasure (Measure.comap (↑MeasurableEquiv.prodComm) μ) := by
    constructor
    rw [Measure.comap_apply]
    · exact measure_lt_top _ _
    · exact MeasurableEquiv.prodComm.injective
    · intro s hs
      exact MeasurableEquiv.prodComm.measurableEmbedding.measurableSet_image' hs
    · exact MeasurableSet.univ
  exact entropy_comap_equiv κ MeasurableEquiv.prodComm hμ

def prodMKLeft_unit_equiv (T : Type*) [MeasurableSpace T] : (Unit × T) ≃ᵐ T where
  toFun := fun p ↦ p.2
  invFun:= Prod.mk ()
  left_inv := by intro p; simp
  right_inv := by intro t; simp
  measurable_toFun := by simp; exact measurable_snd
  measurable_invFun := by simp; exact measurable_prod_mk_left

lemma entropy_prodMkLeft_unit (κ : kernel T S) {μ : Measure T} [IsProbabilityMeasure μ] (hμ: FiniteSupport μ) :
    Hk[prodMkLeft Unit κ, μ.map (Prod.mk ())] = Hk[κ, μ] := by
    convert entropy_comap_equiv κ (prodMKLeft_unit_equiv T) hμ
    funext μ
    rw [<-MeasurableEquiv.map_symm]
    congr

lemma entropy_compProd_aux [IsFiniteMeasure μ] {κ : kernel T S} [IsMarkovKernel κ]
    {η : kernel (T × S) U} [IsMarkovKernel η] (hμ : FiniteSupport μ) (hκ : FiniteKernelSupport κ) (hη: FiniteKernelSupport η):
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ]
      + μ[fun t ↦ Hk[comap η (Prod.mk t) measurable_prod_mk_left, (κ t)]] := by
  rcases hμ with ⟨A, hA⟩
  have hsum (F : T → ℝ) : ∫ (t : T), F t ∂μ = ∑ t in A, (μ.real {t}) * (F t) := by
    rw [integral_eq_sum_finset' _ _ hA]
    congr with t ht
  simp_rw [entropy, hsum, <-Finset.sum_add_distrib]
  congr with t
  rw [<-mul_add]
  congr
  rcases hκ with ⟨B, hB⟩
  rcases hη with ⟨C, hC⟩
  rw [integral_eq_sum_finset' _ _ (hB t)]
  have hκη : ((κ ⊗ₖ η) t) (B ×ˢ C: Finset (S × U))ᶜ = 0 := by
    rw [ProbabilityTheory.kernel.compProd_apply, lintegral_eq_sum_finset' _ _ (hB t)]
    . apply Finset.sum_eq_zero
      intro s hs
      simp; left
      refine measure_mono_null ?_ (hC (t, s))
      intro u hu
      simp at hu ⊢
      exact hu hs
    exact MeasurableSet.compl (Finset.measurableSet _)
  rw [measureEntropy_def_finite' hκη, measureEntropy_def_finite' (hB t), <-Finset.sum_add_distrib, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s hs
  simp
  have hη': (comap η (Prod.mk t) measurable_prod_mk_left) s Cᶜ = 0 := by
    rw [kernel.comap_apply]
    exact hC (t, s)
  rw [measureEntropy_def_finite' hη']
  simp
  have : negMulLog ((κ t).real {s}) = ∑ u in C, negMulLog ((κ t).real {s}) * ((comap η (Prod.mk t) measurable_prod_mk_left) s).real {u} := by
    rw [<-Finset.mul_sum]
    simp
    rw [kernel.comap_apply]
    suffices : (η (t, s)).real ↑C = (η (t, s)).real Set.univ
    . simp [this]
    have := hC (t, s)
    rw [<- measureReal_eq_zero_iff] at this
    rw [<-measureReal_add_measureReal_compl (s := C) _, this, add_zero]
    exact Finset.measurableSet C
  rw [this, Finset.mul_sum, <-Finset.sum_add_distrib]
  congr with u
  have : ((κ ⊗ₖ η) t).real {(s, u)} = ((κ t).real {s}) * ((η (t, s)).real {u}) := by
    rw [measureReal_def, compProd_apply κ η _ (measurableSet_singleton _), lintegral_eq_sum_finset' _ _ (hB t), Finset.sum_eq_single_of_mem s hs]
    . simp [measureReal_def]; ring
    intro b _ hbs
    simp [hbs]
  rw [this, kernel.comap_apply, negMulLog_mul, negMulLog, negMulLog, <-measureReal_def]
  ring


lemma entropy_compProd' [IsFiniteMeasure μ] (κ : kernel T S) [IsMarkovKernel κ]
    (η : kernel (T × S) U) [IsMarkovKernel η] :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[condKernel (κ ⊗ₖ η), μ ⊗ₘ κ] := by
  rw [entropy_compProd_aux]
  congr
  simp_rw [entropy, integral_eq_sum, measureEntropy_of_isProbabilityMeasure,
    Measure.compProd_apply (measurableSet_singleton _), lintegral_eq_sum]
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
  rw [entropy_compProd', entropy_congr (condKernel_compProd_ae_eq κ η _)]

@[simp]
lemma entropy_deterministic (f : T → S) (μ : Measure T) [IsFiniteMeasure μ] :
    Hk[deterministic f (measurable_of_countable f), μ] = 0 := by
  simp_rw [entropy, integral_eq_sum, smul_eq_mul, deterministic_apply, measureEntropy_dirac,
    mul_zero, Finset.sum_const_zero]

@[simp]
lemma entropy_compProd_deterministic
    (κ : kernel T S) [IsMarkovKernel κ] (μ : Measure T) [IsFiniteMeasure μ] (f : T × S → U) :
    Hk[κ ⊗ₖ (deterministic f (measurable_of_countable f)), μ] = Hk[κ, μ] := by
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

@[simp]
lemma entropy_prodMkRight (κ : kernel T S) (η : kernel T U)
    [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[prodMkRight η S, μ ⊗ₘ κ] = Hk[η, μ] := by
  simp_rw [entropy, prodMkRight_apply, integral_eq_sum,
    Measure.compProd_apply (measurableSet_singleton _), lintegral_eq_sum, smul_eq_mul]
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

lemma entropy_prodMkRight' (η : kernel T U)
    (μ : Measure T) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν] :
    Hk[prodMkRight η S, μ.prod ν] = Hk[η, μ] := by
  rw [← entropy_prodMkRight (kernel.const T ν) η μ]
  congr
  ext s hs
  simp_rw [Measure.prod_apply hs, Measure.compProd_apply hs, kernel.const_apply]

lemma _root_.MeasureTheory.Measure.prod_apply_singleton {α β : Type*}
    {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν) {x} = μ {x.1} * ν {x.2} := by
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Measure.prod_prod]

@[simp]
lemma entropy_prodMkLeft (η : kernel T U)
    (ν : Measure S) [IsProbabilityMeasure ν] (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[prodMkLeft S η, ν.prod μ] = Hk[η, μ] := by
  simp_rw [entropy, prodMkLeft_apply, integral_eq_sum, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [Measure.prod_apply_singleton, ENNReal.toReal_mul, mul_assoc, ← Finset.mul_sum,
    ← Finset.sum_mul, sum_toReal_measure_singleton]
  simp

@[simp]
lemma entropy_prod (κ : kernel T S) (η : kernel T U) [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[κ ×ₖ η, μ] = Hk[κ, μ] + Hk[η, μ] := by
  rw [chain_rule, fst_prod, entropy_congr (condKernel_prod_ae_eq _ _), entropy_prodMkRight]

/-- Data-processing inequality for the kernel entropy. -/
lemma entropy_map_le
    (κ : kernel T S) [IsMarkovKernel κ] (μ : Measure T) [IsProbabilityMeasure μ] (f : S → U) :
    Hk[map κ f (measurable_of_countable f), μ] ≤ Hk[κ, μ] := by
  have : Hk[κ, μ] = Hk[map κ (fun x ↦ (x, f x)) (measurable_of_countable _), μ] := by
    refine (entropy_map_of_injective κ μ (fun x ↦ (x, f x)) ?_).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule', snd_map_prod _ measurable_id', le_add_iff_nonneg_right]
  exact entropy_nonneg _ _

lemma entropy_of_map_eq_of_map (κ : kernel T S) (η : kernel T U)
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure T) [IsProbabilityMeasure μ] (f : S → U) (g : U → S)
    (h1 : η = map κ f (measurable_of_countable _)) (h2 : κ = map η g (measurable_of_countable _)) :
    Hk[κ, μ] = Hk[η, μ] := by
  refine le_antisymm ?_ ?_
  · rw [h2]; exact entropy_map_le η μ g
  · rw [h1]; exact entropy_map_le κ μ f

lemma entropy_snd_le (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[snd κ, μ] ≤ Hk[κ, μ] :=
  entropy_map_le _ _ _

lemma entropy_fst_le (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] :
    Hk[fst κ, μ] ≤ Hk[κ, μ] :=
  entropy_map_le _ _ _

end ProbabilityTheory.kernel
