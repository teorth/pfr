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
 [Countable V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]

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

/-- The analogue of FiniteSupport for probability kernels. -/
noncomputable def FiniteKernelSupport (κ : kernel T S) : Prop :=
  ∀ t, ∃ A : Finset S, κ t Aᶜ = 0

noncomputable def AEFiniteKernelSupport (κ : kernel T S) (μ : Measure T) : Prop :=
  ∀ᵐ t ∂μ, ∃ A : Finset S, κ t Aᶜ = 0

lemma FiniteKernelSupport.aefiniteKernelSupport {κ : kernel T S} (hκ : FiniteKernelSupport κ)
    (μ : Measure T) :
    AEFiniteKernelSupport κ μ :=
  ae_of_all μ hκ

/-- Finite kernel support locally implies uniform finite kernel support. -/
lemma local_support_of_finiteKernelSupport {κ : kernel T S} (h : FiniteKernelSupport κ) (A : Finset T) :
    ∃ B : Finset S, ∀ t ∈ A, (κ t) Bᶜ = 0 := by
  classical
  use Finset.biUnion A (fun t ↦ (h t).choose)
  intro t ht
  set B := (h t).choose
  refine measure_mono_null ?_ (h t).choose_spec
  intro s; simp
  contrapose!; intro h
  use t

/-- Finite range implies finite kernel support. -/
lemma finiteKernelSupport_of_finite_range [Fintype S] (κ : kernel T S) : FiniteKernelSupport κ := by
  intro t
  use Finset.univ
  simp

/-- Deterministic kernels have finite kernel support.-/
lemma finiteKernelSupport_of_deterministic (f : T × S → U) :
    FiniteKernelSupport (deterministic f (measurable_of_countable f)) := by
  intro (t,s)
  use { f (t,s) }
  rw [kernel.deterministic_apply' (by measurability) _ (by measurability)]
  simp

/-- Projecting a kernel to first coordinate preserves finite kernel support. -/
lemma finiteKernelSupport_of_fst {κ : kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (fst κ) := by
  intro t
  rcases hκ t with ⟨A, hA⟩
  classical
  use Finset.image Prod.fst A
  rw [kernel.fst_apply' _ _ (by measurability)]
  refine measure_mono_null ?_ hA
  intro p; simp; contrapose!; intro hp; use p.2

/-- Projecting a kernel to second coordinate preserves finite kernel support. -/
lemma finiteKernelSupport_of_snd {κ : kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (snd κ) := by
  intro t
  rcases hκ t with ⟨A, hA⟩
  classical
  use Finset.image Prod.snd A
  rw [kernel.snd_apply' _ _ (by measurability)]
  refine measure_mono_null ?_ hA
  intro p; simp; contrapose!; intro hp; use p.1

lemma Measure.compProd_apply_singleton (μ : Measure T) [SFinite μ]
    (κ : kernel T S) [IsSFiniteKernel κ] (t : T) (s : S) :
    (μ ⊗ₘ κ) {(t, s)} = κ t {s} * μ {t} := by
  rw [Measure.compProd_apply (measurableSet_singleton _)]
  have : ∀ a, κ a (Prod.mk a ⁻¹' {(t, s)}) = ({t} : Set T).indicator (fun _ ↦ κ t {s}) a := by
    intro a
    by_cases ha : a = t
    · simp only [ha, Set.mem_singleton_iff, Set.indicator_of_mem]
      congr
      ext y
      simp
    · simp only [Set.mem_singleton_iff, ha, not_false_eq_true, Set.indicator_of_not_mem]
      suffices Prod.mk a ⁻¹' {(t, s)} = ∅ by simp [this]
      ext y
      simp [ha]
  simp_rw [this]
  rw [lintegral_indicator _ (measurableSet_singleton _)]
  simp

/-- Conditioning a kernel preserves finite kernel support. -/
lemma aefiniteKernelSupport_of_cond {κ : kernel T (S × U)} [hU: Nonempty U]
    (μ : Measure T) [IsFiniteMeasure μ] (hκ : AEFiniteKernelSupport κ μ) [IsFiniteKernel κ] :
    AEFiniteKernelSupport (condKernel κ) (μ ⊗ₘ (kernel.fst κ)) := by
  rw [AEFiniteKernelSupport, ae_iff_of_countable] at hκ ⊢
  intro (t, s) hts
  simp only [Measure.compProd_apply_singleton, ne_eq, mul_eq_zero] at hts
  push_neg at hts
  rcases hκ t hts.2 with ⟨A, hA⟩
  classical
  use Finset.image Prod.snd A
  rw [condKernel_apply']
  rotate_left
  · rw [kernel.fst_apply' _ _ (measurableSet_singleton _)] at hts
    exact hts.1
  · measurability
  simp only [Finset.coe_image, Set.singleton_prod, mul_eq_zero, ENNReal.inv_eq_zero]
  right
  refine measure_mono_null ?_ hA
  intro x
  simp only [Set.mem_image, Set.mem_compl_iff, Finset.mem_coe, Prod.exists, exists_eq_right,
    not_exists, forall_exists_index, and_imp]
  intro y h hsyx
  rw [← hsyx]
  exact h s

/-- Swapping a kernel right preserves finite kernel support. -/
lemma finiteKernelSupport_of_swapRight {κ : kernel T (S × U)} (hκ : FiniteKernelSupport κ) : FiniteKernelSupport (swapRight κ) := by
  intro t
  rcases hκ t with ⟨A, hA⟩
  classical
  use Finset.image Prod.swap A
  rw [kernel.swapRight_apply' _ _ (by measurability)]
  simp
  convert hA using 1

/-- Constant kernels with finite support, have finite kernel support. -/
lemma finiteKernelSupport_of_const {ν : Measure S} (hν  : FiniteSupport ν) : FiniteKernelSupport (kernel.const T ν) := by
  rcases hν with ⟨A, hA⟩
  intro t; use A
  simp [hA]


/-- Products preserve finite kernel support. -/
lemma finiteKernelSupport_of_prod {κ : kernel T S} {η : kernel T U} [IsMarkovKernel κ] [IsMarkovKernel η] (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) : FiniteKernelSupport (κ ×ₖ η) := by
  intro t
  rcases hκ t with ⟨A, hA⟩
  rcases hη t with ⟨B, hB⟩
  use A ×ˢ B
  rw [kernel.prod_apply _ _ _ (by measurability)]
  apply lintegral_eq_zero_of_ae_zero hA _ (by measurability)
  intro s hs
  refine measure_mono_null ?_ hB
  intro u; simp; tauto

/-- maps preserve finite kernel support. -/
lemma finiteKernelSupport_of_map {κ : kernel T S}  (hκ : FiniteKernelSupport κ) {f : S → U} (hf : Measurable f): FiniteKernelSupport (map κ f hf) := by
  intro t
  rcases hκ t with ⟨A, hA⟩
  classical
  use Finset.image f A
  rw [kernel.map_apply' _ _ _ (by measurability)]
  refine measure_mono_null ?_ hA
  intro s; simp; contrapose!; intro hs; use s

/-- comaps preserve finite kernel support. -/
lemma finiteKernelSupport_of_comap {κ : kernel T S}  (hκ : FiniteKernelSupport κ) {f : U → T} (hf : Measurable f): FiniteKernelSupport (comap κ f hf) := by
  intro u
  rcases hκ (f u) with ⟨A, hA⟩
  use A
  rwa [kernel.comap_apply]

/-- Composition-product preserves finite kernel support -/
lemma finiteKernelSupport_of_compProd {κ : kernel T S} [IsMarkovKernel κ] {η : kernel (T × S) U} [IsMarkovKernel η] (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) : FiniteKernelSupport (κ ⊗ₖ η) := by
  intro t
  rcases hκ t with ⟨A, hA⟩
  rcases (local_support_of_finiteKernelSupport hη ({t} ×ˢ A)) with ⟨B, hB⟩
  use (A ×ˢ B)
  rw [kernel.compProd_apply _ _ _ (by measurability), lintegral_eq_sum' _ hA]
  apply Finset.sum_eq_zero
  intro s hs
  simp; left
  refine measure_mono_null ?_ (hB (t, s) (by simp [hs]))
  intro u; simp; tauto

/-- prodMkRight preserves finite kernel support. -/
lemma finiteKernelSupport_of_prodMkRight {κ : kernel T S} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (prodMkRight κ U) :=
  finiteKernelSupport_of_comap hκ _

/-- prodMkLeft preserves finite kernel support. -/
lemma finiteKernelSupport_of_prodMkLeft {κ : kernel T S} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (prodMkLeft U κ) :=
  finiteKernelSupport_of_comap hκ _

/-- Composing a finitely supported measure with a finitely supported kernel gives a finitely supported kernel. -/
lemma finiteSupport_of_compProd {μ : Measure T} [IsProbabilityMeasure μ] {κ : kernel T S}
    [IsMarkovKernel κ] (hμ : FiniteSupport μ) (hκ: FiniteKernelSupport κ) :
    FiniteSupport (μ ⊗ₘ κ) := by
  rcases hμ with ⟨A, hA⟩
  rcases (local_support_of_finiteKernelSupport hκ A) with ⟨B, hB⟩
  use A ×ˢ B
  rw [Measure.compProd_apply (by measurability), lintegral_eq_sum' _ hA]
  apply Finset.sum_eq_zero
  intro t ht
  simp; left
  refine measure_mono_null ?_ (hB t ht)
  intro s
  simp; tauto

lemma aefiniteKernelSupport_condDistrib (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hX: Measurable X) (hY: Measurable Y) [FiniteRange X] [FiniteRange Y] :
    AEFiniteKernelSupport (condDistrib X Y μ) (μ.map Y) := by
  filter_upwards [condDistrib_ae_eq hX hY μ] with a ha
  rw [ha]
  exact finiteSupport_of_finiteRange hX

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
    (μ : Measure T) {f : T × S → U}
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
    . rwa [← Measure.comap_apply f hf.injective hf.measurableSet_image']
      exact MeasurableSet.compl (Finset.measurableSet A)
    exact ae_eq_univ.mp hf_range
  simp_rw [entropy]
  simp_rw [integral_eq_sum' _ hA, integral_eq_sum' _ this, Measure.comap_apply f hf.injective hf.measurableSet_image' _
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
    rwa [Finset.coe_image, ← Set.image_compl_eq (MeasurableEquiv.bijective f.symm), Measure.comap_apply f (MeasurableEquiv.injective f),MeasurableEquiv.image_symm, MeasurableEquiv.image_preimage]
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
  simp_rw [entropy, integral_eq_sum' _ hA, integral_eq_sum' _ this, Measure.comap_apply f f.injective f.measurableEmbedding.measurableSet_image' _
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
    Hk[comap κ Prod.swap measurable_swap, μ.comap Prod.swap] = Hk[κ, μ] :=
  entropy_comap_equiv κ MeasurableEquiv.prodComm hμ

/-- Measurable equivalence with the product with the one-point space `Unit`.-/
def prodMKLeft_unit_equiv (T : Type*) [MeasurableSpace T] : (Unit × T) ≃ᵐ T where
  toFun := fun p ↦ p.2
  invFun:= Prod.mk ()
  left_inv := by intro p; simp
  right_inv := by intro t; simp
  measurable_toFun := by simp; exact measurable_snd
  measurable_invFun := by simp; exact measurable_prod_mk_left

lemma entropy_prodMkLeft_unit (κ : kernel T S) {μ : Measure T} [IsProbabilityMeasure μ]
    (hμ : FiniteSupport μ) :
    Hk[prodMkLeft Unit κ, μ.map (Prod.mk ())] = Hk[κ, μ] := by
  convert entropy_comap_equiv κ (prodMKLeft_unit_equiv T) hμ
  funext μ
  rw [← MeasurableEquiv.map_symm]
  congr

lemma entropy_compProd_aux [IsFiniteMeasure μ] {κ : kernel T S} [IsMarkovKernel κ]
    {η : kernel (T × S) U} [IsMarkovKernel η] (hμ : FiniteSupport μ) (hκ : FiniteKernelSupport κ)
    (hη : FiniteKernelSupport η) :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ]
      + μ[fun t ↦ Hk[comap η (Prod.mk t) measurable_prod_mk_left, (κ t)]] := by
  rcases hμ with ⟨A, hA⟩
  have hsum (F : T → ℝ) : ∫ (t : T), F t ∂μ = ∑ t in A, (μ.real {t}) * (F t) := by
    rw [integral_eq_sum' _ hA]
    congr with t ht
  simp_rw [entropy, hsum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← mul_add]
  congr
  rcases (local_support_of_finiteKernelSupport hκ A) with ⟨B, hB⟩
  rcases (local_support_of_finiteKernelSupport hη (A ×ˢ B)) with ⟨C, hC⟩
  rw [integral_eq_sum' _ (hB t ht)]
  have hκη : ((κ ⊗ₖ η) t) (B ×ˢ C: Finset (S × U))ᶜ = 0 := by
    rw [ProbabilityTheory.kernel.compProd_apply, lintegral_eq_sum' _ (hB t ht)]
    . apply Finset.sum_eq_zero
      intro s hs
      simp; left
      have hts : (t, s) ∈ A ×ˢ B := by simp [ht, hs]
      refine measure_mono_null ?_ (hC (t, s) hts)
      intro u hu
      simp at hu ⊢
      exact hu hs
    exact MeasurableSet.compl (Finset.measurableSet _)
  rw [measureEntropy_def_finite' hκη, measureEntropy_def_finite' (hB t ht), ← Finset.sum_add_distrib, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s hs
  simp
  have hts : (t, s) ∈ A ×ˢ B := by simp [ht, hs]
  have hη': (comap η (Prod.mk t) measurable_prod_mk_left) s Cᶜ = 0 := by
    rw [kernel.comap_apply]
    exact hC (t, s) hts
  rw [measureEntropy_def_finite' hη']
  simp
  have : negMulLog ((κ t).real {s}) = ∑ u in C, negMulLog ((κ t).real {s}) * ((comap η (Prod.mk t) measurable_prod_mk_left) s).real {u} := by
    rw [← Finset.mul_sum]
    simp
    rw [kernel.comap_apply]
    suffices : (η (t, s)).real ↑C = (η (t, s)).real Set.univ
    . simp [this]
    have := hC (t, s) hts
    rw [← measureReal_eq_zero_iff] at this
    rw [← measureReal_add_measureReal_compl (s := C) _, this, add_zero]
    exact Finset.measurableSet C
  rw [this, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr with u
  have : ((κ ⊗ₖ η) t).real {(s, u)} = ((κ t).real {s}) * ((η (t, s)).real {u}) := by
    rw [measureReal_def, compProd_apply κ η _ (measurableSet_singleton _), lintegral_eq_sum' _ (hB t ht), Finset.sum_eq_single_of_mem s hs]
    . simp [measureReal_def]; ring
    intro b _ hbs
    simp [hbs]
  rw [this, kernel.comap_apply, negMulLog_mul, negMulLog, negMulLog, ← measureReal_def]
  ring

lemma entropy_compProd'' [IsFiniteMeasure μ] {κ : kernel T S} [IsMarkovKernel κ]
    {η : kernel (T × S) U} [IsMarkovKernel η] (hμ : FiniteSupport μ)
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[condKernel (κ ⊗ₖ η), μ ⊗ₘ κ] := by
  rw [entropy_compProd_aux hμ hκ hη]
  congr
  rcases hμ with ⟨A, hA⟩
  rcases (local_support_of_finiteKernelSupport hκ A) with ⟨B, hB⟩
  have hμκ : (μ ⊗ₘ κ) (A ×ˢ B : Finset (T × S))ᶜ = 0 := by
    rw [Measure.compProd_apply (by measurability), lintegral_eq_sum' _ hA]
    apply  Finset.sum_eq_zero
    intro x hx
    simp; left
    refine measure_mono_null ?_ (hB x hx)
    intro s hs
    contrapose! hs
    simp at hs ⊢
    exact ⟨hx, hs⟩
  simp_rw [entropy, integral_eq_sum' _ hA, integral_eq_sum' _ hμκ, Finset.sum_product, measureEntropy_of_isProbabilityMeasure]
  apply Finset.sum_congr rfl
  intro t ht
  simp_rw [
    Measure.compProd_apply (measurableSet_singleton _), lintegral_eq_sum' _ hA, integral_eq_sum' _ (hB t ht), smul_eq_mul, Finset.mul_sum, kernel.comap_apply]
  congr with s
  rw [Finset.sum_eq_single t]; rotate_left
  . intro b _ hbt
    simp; left; convert measure_empty
    ext c; simp [hbt]
  . intro ht; simp; right
    convert measure_mono_null ?_ hA
    simp [ht]
  have : {s} = Prod.mk t ⁻¹' {(t, s)} := by ext b; simp
  rw [ENNReal.toReal_mul, ← mul_assoc, mul_comm (μ {t}).toReal _, ← this]
  by_cases hκt : κ t {s} = 0
  . simp [hκt]
  congr with u
  congr 3
  rw [condKernel_compProd_apply]
  exact hκt

lemma entropy_compProd' [hU : Nonempty U] [IsFiniteMeasure μ] {κ : kernel T S} [IsMarkovKernel κ]
    {η : kernel (T × S) U} [IsMarkovKernel η] (hμ : FiniteSupport μ)
    (hκ : FiniteKernelSupport κ) (hη : AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[condKernel (κ ⊗ₖ η), μ ⊗ₘ κ] := by
  obtain ⟨η', hη', h_eq⟩ : ∃ η' : kernel (T × S) U, FiniteKernelSupport η' ∧ η' =ᵐ[μ ⊗ₘ κ] η := by
    classical
    let B := {t | ∃ A : Finset U, η t Aᶜ = 0}
    have hB : MeasurableSet B := by measurability
    let η'' := kernel.piecewise hB η (kernel.const _ (Measure.dirac hU.some))
    refine ⟨η'', ?_, ?_⟩
    · sorry
    · filter_upwards [hη] with t ht
      unfold_let η''
      have htB : t ∈ B := ht
      rw [kernel.piecewise_apply, if_pos htB]
  have : IsMarkovKernel η' := sorry
  have h_ent1 : Hk[κ ⊗ₖ η', μ] = Hk[κ ⊗ₖ η, μ] := by
    refine entropy_congr ?_
    sorry
  have h_ent2 : Hk[condKernel (κ ⊗ₖ η'), μ ⊗ₘ κ] = Hk[condKernel (κ ⊗ₖ η), μ ⊗ₘ κ] := by
    refine entropy_congr ?_
    sorry
  rw [← h_ent1, ← h_ent2, entropy_compProd'' hμ hκ hη']

lemma entropy_compProd [IsFiniteMeasure μ]
    {κ : kernel T S} [IsMarkovKernel κ] {η : kernel (T × S) U} [IsMarkovKernel η]
    (hμ : FiniteSupport μ) (hκ : FiniteKernelSupport κ) (hη: AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[η, μ ⊗ₘ κ] := by
  rw [entropy_compProd' hμ hκ hη, entropy_congr (condKernel_compProd_ae_eq κ η _)]

@[simp]
lemma entropy_deterministic (f : T → S) (μ : Measure T) :
    Hk[deterministic f (measurable_of_countable f), μ] = 0 := by
  simp_rw [entropy]
  convert integral_zero T ℝ
  apply measureEntropy_dirac

@[simp]
lemma entropy_compProd_deterministic
    (κ : kernel T S) [IsMarkovKernel κ] (μ : Measure T) [IsFiniteMeasure μ] (f : T × S → U)
    (hμ : FiniteSupport μ) (hκ : FiniteKernelSupport κ) :
    Hk[κ ⊗ₖ (deterministic f (measurable_of_countable f)), μ] = Hk[κ, μ] := by
  simp [entropy_compProd hμ hκ ((finiteKernelSupport_of_deterministic f).aefiniteKernelSupport _)]

lemma chain_rule {κ : kernel T (S × U)} [IsMarkovKernel κ] [hU: Nonempty U]
    {μ : Measure T} [IsProbabilityMeasure μ] (hμ : FiniteSupport μ)
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[κ, μ] = Hk[fst κ, μ] + Hk[condKernel κ, μ ⊗ₘ (fst κ)] := by
  conv_lhs => rw [disintegration κ]
  rw [entropy_compProd' hμ (finiteKernelSupport_of_fst hκ)
    (aefiniteKernelSupport_of_cond _ hκ)]
  congr
  rw [← disintegration κ]

lemma chain_rule' {κ : kernel T (S × U)} [IsMarkovKernel κ]
   {μ : Measure T} [IsProbabilityMeasure μ] (hμ : FiniteSupport μ) (hκ : FiniteKernelSupport κ) :
    Hk[κ, μ] = Hk[snd κ, μ] + Hk[condKernel (swapRight κ), μ ⊗ₘ (snd κ)] := by
  rw [← entropy_swapRight, chain_rule hμ (finiteKernelSupport_of_swapRight hκ)]
  simp

@[simp]
lemma entropy_prodMkRight {κ : kernel T S} {η : kernel T U}
    [IsMarkovKernel κ] {μ : Measure T} [IsProbabilityMeasure μ] (hμ : FiniteSupport μ)
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    Hk[prodMkRight η S, μ ⊗ₘ κ] = Hk[η, μ] := by
  rcases hμ with ⟨A, hA⟩
  rcases (local_support_of_finiteKernelSupport hκ A) with ⟨B, hB⟩
  rcases (local_support_of_finiteKernelSupport hη A) with ⟨C, hC⟩
  have hAB : (μ ⊗ₘ κ) (A ×ˢ B : Finset (T × S))ᶜ = 0 := by
    rw [Measure.compProd_apply (by measurability), lintegral_eq_sum' _ hA]
    apply Finset.sum_eq_zero
    intro t ht
    simp; left
    refine measure_mono_null ?_ (hB t ht)
    intro s hs
    contrapose! hs
    simp at hs ⊢
    exact ⟨ht, hs⟩
  rw [entropy, entropy, integral_eq_sum' _ hA, integral_eq_sum' _ hAB, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro t ht
  simp [← Finset.sum_mul]; left
  have : ∑ p in {t} ×ˢ B, ((μ ⊗ₘ κ) {p}).toReal = ∑ s in B, ((μ ⊗ₘ κ) {(t,s)}).toReal := by
    classical
    convert Finset.sum_image ?_
    . ext ⟨t', s⟩; simp; rw [Finset.mem_image]; simp
    intro x _ y _ hxy; simp at hxy; exact hxy
  rw [← this, Finset.sum_toReal_measure_singleton, Measure.compProd_apply (by measurability), lintegral_eq_single _ t _ _]
  . simp
    convert one_mul _
    replace hB := hB t ht
    rw [← measureReal_eq_zero_iff] at hB
    have := measureReal_compl (μ:=κ t) (s := B) (by measurability)
    simp [hB] at this
    have : (κ t B).toReal = 1 := by change (κ t).real B = 1; linarith
    convert this
    ext s; simp
  intro t' ht'
  convert measure_empty
  ext s
  simp
  intro _; exact ht'.symm

lemma entropy_prodMkRight' {η : kernel T U}
    {μ : Measure T} [IsProbabilityMeasure μ] {ν : Measure S} [IsProbabilityMeasure ν] (hμ : FiniteSupport μ) (hν  : FiniteSupport ν) (hη : FiniteKernelSupport η) :
    Hk[prodMkRight η S, μ.prod ν] = Hk[η, μ] := by
  rw [← entropy_prodMkRight hμ (finiteKernelSupport_of_const hν) hη]
  congr
  ext s hs
  simp_rw [Measure.prod_apply hs, Measure.compProd_apply hs, kernel.const_apply]

lemma _root_.MeasureTheory.Measure.prod_apply_singleton {α β : Type*}
    {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν) {x} = μ {x.1} * ν {x.2} := by
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Measure.prod_prod]

@[simp]
lemma entropy_prodMkLeft {η : kernel T U}
    {ν : Measure S} [IsProbabilityMeasure ν] {μ : Measure T} [IsProbabilityMeasure μ] (hμ : FiniteSupport μ) (hν  : FiniteSupport ν) (hη : FiniteKernelSupport η) :
    Hk[prodMkLeft S η, ν.prod μ] = Hk[η, μ] := by
  rcases hμ with ⟨A, hA⟩
  rcases hν with ⟨B, hB⟩
  rcases (local_support_of_finiteKernelSupport hη A) with ⟨C, hC⟩
  have hAB : (ν.prod μ) (B ×ˢ A: Finset (S×T))ᶜ = 0 := by
    have : ((B ×ˢ A: Finset (S×T)): Set (S × T))ᶜ = (B : Set S)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (A : Set T)ᶜ := by
      ext ⟨s, t⟩; simp; tauto
    rw [this]; simp
    exact ⟨hB, hA⟩
  simp_rw [entropy, prodMkLeft_apply, integral_eq_sum' _ hA, integral_eq_sum' _ hAB, smul_eq_mul, Finset.sum_product_right, Measure.prod_apply_singleton]
  apply Finset.sum_congr rfl
  intro t ht
  simp_rw [ENNReal.toReal_mul, mul_assoc, ← Finset.sum_mul]
  convert one_mul _
  simp
  have := measureReal_add_measureReal_compl (μ := ν) (s := B) (by measurability)
  rw [← measureReal_eq_zero_iff] at hB
  simp [hB] at this
  exact this

@[simp]
lemma entropy_prod {κ : kernel T S} {η : kernel T U} [IsMarkovKernel κ] [IsMarkovKernel η]
    {μ : Measure T} [IsProbabilityMeasure μ] (hμ : FiniteSupport μ)
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    Hk[κ ×ₖ η, μ] = Hk[κ, μ] + Hk[η, μ] := by
  rw [chain_rule hμ (finiteKernelSupport_of_prod hκ hη), fst_prod, entropy_congr (condKernel_prod_ae_eq _ _), entropy_prodMkRight hμ hκ hη]

/-- Data-processing inequality for the kernel entropy. -/
lemma entropy_map_le
    {κ : kernel T S} [IsMarkovKernel κ] {μ : Measure T} [IsProbabilityMeasure μ] (f : S → U) (hμ : FiniteSupport μ) (hκ : FiniteKernelSupport κ) :
    Hk[map κ f (measurable_of_countable f), μ] ≤ Hk[κ, μ] := by
  have : Hk[κ, μ] = Hk[map κ (fun x ↦ (x, f x)) (measurable_of_countable _), μ] := by
    refine (entropy_map_of_injective κ μ (f := fun x ↦ (x, f x)) ?_ ?_).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule' hμ (finiteKernelSupport_of_map hκ _), snd_map_prod _ measurable_id', le_add_iff_nonneg_right]
  exact entropy_nonneg _ _

lemma entropy_of_map_eq_of_map {κ : kernel T S} {η : kernel T U}
    [IsMarkovKernel κ] [IsMarkovKernel η]
    {μ : Measure T} [IsProbabilityMeasure μ] (f : S → U) (g : U → S)
    (h1 : η = map κ f (measurable_of_countable _)) (h2 : κ = map η g (measurable_of_countable _)) (hμ : FiniteSupport μ) (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    Hk[κ, μ] = Hk[η, μ] := by
  refine le_antisymm ?_ ?_
  · rw [h2]; exact entropy_map_le g hμ hη
  · rw [h1]; exact entropy_map_le f hμ hκ

lemma entropy_snd_le {κ : kernel T (S × U)} [IsMarkovKernel κ]
    {μ : Measure T} [IsProbabilityMeasure μ] (hμ : FiniteSupport μ) (hκ : FiniteKernelSupport κ) :
    Hk[snd κ, μ] ≤ Hk[κ, μ] :=
  entropy_map_le _ hμ hκ

lemma entropy_fst_le (κ : kernel T (S × U)) [IsMarkovKernel κ]
    (μ : Measure T) [IsProbabilityMeasure μ] (hμ : FiniteSupport μ) (hκ : FiniteKernelSupport κ) :
    Hk[fst κ, μ] ≤ Hk[κ, μ] :=
  entropy_map_le _ hμ hκ

end ProbabilityTheory.kernel
