
import Mathlib.Probability.Kernel.Composition

/-!
# Composition-Product of a measure and a kernel

This operation, denoted by `⊗ₘ`, takes `μ : Measure α` and `κ : kernel α β` and creates
`μ ⊗ₘ κ : Measure (α × β)`.

It is defined as `((kernel.const Unit μ) ⊗ₖ (kernel.prodMkLeft Unit κ)) ()`.

## Main definitions

* `Measure.compProd`: from `μ : Measure α` and `κ : kernel α β`, get a `Measure (α × β)`.

## Notations

* `μ ⊗ₘ κ = μ.compProd κ`
-/

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

section aux_kernel

namespace ProbabilityTheory.kernel

-- These are already PRed to mathlib

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

@[simp]
lemma const_zero : kernel.const α (0 : Measure β) = 0 := by ext x s _; simp [kernel.const_apply]

@[simp]
lemma prodMkLeft_zero : kernel.prodMkLeft α (0 : kernel β γ) = 0 := by
  ext x s _; simp [kernel.prodMkLeft_apply']

@[simp] lemma fst_zero : fst (0 : kernel α (β × γ)) = 0 := by simp [fst]
@[simp] lemma snd_zero : snd (0 : kernel α (β × γ)) = 0 := by simp [snd]

@[simp]
lemma fst_swapRight (κ : kernel α (β × γ)) : fst (swapRight κ) = snd κ := by
  ext a s hs
  rw [fst_apply' _ _ hs, swapRight_apply', snd_apply' _ _ hs]
  · rfl
  · exact measurable_fst hs

@[simp]
lemma snd_swapRight (κ : kernel α (β × γ)) : snd (swapRight κ) = fst κ := by
  ext a s hs
  rw [snd_apply' _ _ hs, swapRight_apply', fst_apply' _ _ hs]
  · rfl
  · exact measurable_snd hs

lemma fst_map_prod (κ : kernel α β) {f : β → γ} {g : β → δ}
    (hf : Measurable f) (hg : Measurable g) :
    fst (map κ (fun x ↦ (f x, g x)) (hf.prod_mk hg)) = map κ f hf := by
  ext x s hs
  rw [fst_apply' _ _ hs, map_apply', map_apply' _ _ _ hs]
  · rfl
  · exact measurable_fst hs

lemma snd_map_prod (κ : kernel α β) {f : β → γ} {g : β → δ}
    (hf : Measurable f) (hg : Measurable g) :
    snd (map κ (fun x ↦ (f x, g x)) (hf.prod_mk hg)) = map κ g hg := by
  ext x s hs
  rw [snd_apply' _ _ hs, map_apply', map_apply' _ _ _ hs]
  · rfl
  · exact measurable_snd hs

@[simp]
lemma fst_compProd (κ : kernel α β) (η : kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] :
    fst (κ ⊗ₖ η) = κ := by
  ext x s hs
  rw [fst_apply' _ _ hs, compProd_apply]
  swap; · exact measurable_fst hs
  simp only [Set.mem_setOf_eq]
  classical
  have : ∀ b : β, η (x, b) {_c | b ∈ s} = s.indicator (fun _ ↦ 1) b := by
    intro b
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator_const hs, one_mul]

@[simp]
lemma map_const (μ : Measure α) {f : α → β} (hf : Measurable f) :
    map (const γ μ) f hf = const γ (μ.map f) := by
  ext x s hs
  rw [map_apply' _ _ _ hs, const_apply, const_apply, Measure.map_apply hf hs]

-- the following are not PRed to mathlib yet

/- Todo: could `Measure.prod_apply` be generalized to s-finite measures?
It would allow replacing `IsFiniteKernel η` by `IsSFiniteKernel η`
Todo: this should be named `prod_apply` and the existing lemma with that name should be
`prod_apply'` -/
lemma prod_apply'' (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel α γ) [IsFiniteKernel η]
    (a : α) :
    (κ ×ₖ η) a = (κ a).prod (η a) := by
  ext s hs
  rw [prod_apply _ _ _ hs, Measure.prod_apply hs]
  rfl

lemma prod_const (μ : Measure β) [IsFiniteMeasure μ] (ν : Measure δ) [IsFiniteMeasure ν] :
    (const α μ) ×ₖ (const α ν) = const α (μ.prod ν) := by
  ext x s _
  rw [const_apply, prod_apply'', const_apply, const_apply]

lemma compProd_preimage_fst (κ : kernel α β) (η : kernel (α × β) γ) [IsSFiniteKernel κ]
    [IsMarkovKernel η] {x : α} {s : Set β} (hs : MeasurableSet s) :
    (κ ⊗ₖ η) x (Prod.fst ⁻¹' s) = κ x s := by
  rw [compProd_apply _ _ _ (measurable_fst hs)]
  simp only [Set.mem_preimage]
  classical
  have : ∀ b : β, η (x, b) {_c | b ∈ s} = s.indicator (fun _ ↦ 1) b := by
    intro b
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator_const hs, one_mul]

lemma compProd_deterministic_apply [MeasurableSingletonClass γ]
    (κ : kernel α β) [IsSFiniteKernel κ]
    {f : α × β → γ} (hf : Measurable f) (x : α) {s : Set (β × γ)} (hs : MeasurableSet s) :
    (κ ⊗ₖ deterministic f hf) x s = κ x {b | (b, f (x, b)) ∈ s} := by
  rw [compProd_apply _ _ _ hs]
  simp only [deterministic_apply, measurableSet_setOf, Set.mem_setOf_eq, Measure.dirac_apply]
  classical
  simp only [Set.mem_setOf_eq, Set.indicator_apply, Pi.one_apply]
  let t := {b | (b, f (x, b)) ∈ s}
  have ht : MeasurableSet t := (measurable_id.prod_mk (hf.comp measurable_prod_mk_left)) hs
  rw [← lintegral_add_compl _ ht]
  have h1 : ∫⁻ b in t, if (b, f (x, b)) ∈ s then 1 else 0 ∂(κ x) = κ x {b | (b, f (x, b)) ∈ s} := by
    suffices ∀ b ∈ t, (if (b, f (x, b)) ∈ s then (1 : ℝ≥0∞) else 0) = 1 by
      rw [set_lintegral_congr_fun ht (ae_of_all _ this), set_lintegral_one]
    intro b hb
    simp only [Set.mem_setOf_eq] at hb
    simp [hb]
  have h2 : ∫⁻ b in tᶜ, if (b, f (x, b)) ∈ s then 1 else 0 ∂(κ x) = 0 := by
    suffices ∀ b ∈ tᶜ, (if (b, f (x, b)) ∈ s then (1 : ℝ≥0∞) else 0) = 0 by
      rw [set_lintegral_congr_fun ht.compl (ae_of_all _ this), lintegral_zero]
    intro b hb
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hb
    simp [hb]
  rw [h1, h2, add_zero]

@[simp]
lemma fst_prod (κ : kernel α β) (η : kernel α γ) [IsSFiniteKernel κ] [IsMarkovKernel η] :
    fst (κ ×ₖ η) = κ := by
  ext x s hs
  rw [fst_apply' _ _ hs, prod_apply]
  swap; · exact measurable_fst hs
  simp only [Set.mem_setOf_eq]
  classical
  have : ∀ b : β, η x {_c | b ∈ s} = Set.indicator s (fun _ ↦ 1) b := by
    intro b
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator_const hs, one_mul]

@[simp]
lemma snd_prod (κ : kernel α β) (η : kernel α γ) [IsMarkovKernel κ] [IsSFiniteKernel η] :
    snd (κ ×ₖ η) = η := by
  ext x s hs
  rw [snd_apply' _ _ hs, prod_apply]
  swap; · exact measurable_snd hs
  simp

lemma comap_map_comm (κ : kernel β γ) {f : α → β} {g : γ → δ}
    (hf : Measurable f) (hg : Measurable g) :
    comap (map κ g hg) f hf = map (comap κ f hf) g hg := by
  ext x s _
  rw [comap_apply, map_apply, map_apply, comap_apply]

section ProdMkRight

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Define a `kernel (α × γ) β` from a `kernel α β` by taking the comap of the projection. -/
def prodMkRight (κ : kernel α β) (γ : Type*) [MeasurableSpace γ] : kernel (α × γ) β :=
  comap κ Prod.fst measurable_fst

variable {γ : Type*} {mγ : MeasurableSpace γ} {f : β → γ} {g : γ → α}

@[simp]
theorem prodMkRight_apply (κ : kernel α β) (ca : α × γ) : prodMkRight κ γ ca = κ ca.fst := rfl

theorem prodMkRight_apply' (κ : kernel α β) (ca : α × γ) (s : Set β) :
    prodMkRight κ γ ca s = κ ca.fst s := rfl

theorem lintegral_prodMkRight (κ : kernel α β) (ca : α × γ) (g : β → ℝ≥0∞) :
    ∫⁻ b, g b ∂prodMkRight κ γ ca = ∫⁻ b, g b ∂κ ca.fst := rfl

instance IsMarkovKernel.prodMkRight (κ : kernel α β) [IsMarkovKernel κ] :
    IsMarkovKernel (prodMkRight κ γ) := by rw [kernel.prodMkRight]; infer_instance

instance IsFiniteKernel.prodMkRight (κ : kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel (prodMkRight κ γ) := by rw [kernel.prodMkRight]; infer_instance

instance IsSFiniteKernel.prodMkRight (κ : kernel α β) [IsSFiniteKernel κ] :
    IsSFiniteKernel (prodMkRight κ γ) := by rw [kernel.prodMkRight]; infer_instance

@[simp]
lemma swapLeft_prodMkLeft (κ : kernel α β) (γ : Type*) [MeasurableSpace γ] :
    swapLeft (prodMkLeft γ κ) = prodMkRight κ γ := rfl

@[simp]
lemma swapLeft_prodMkRight (κ : kernel α β) (γ : Type*) [MeasurableSpace γ] :
    swapLeft (prodMkRight κ γ) = prodMkLeft γ κ := rfl

lemma map_prodMkRight (κ : kernel α β) (γ : Type*) [MeasurableSpace γ]
    {f : β → δ} (hf : Measurable f) :
    map (prodMkRight κ γ) f hf = prodMkRight (map κ f hf) γ := rfl

lemma fst_prodMkRight (κ : kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] :
    fst (prodMkRight κ δ) = prodMkRight (fst κ) δ := rfl

lemma snd_prodMkRight (κ : kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] :
    snd (prodMkRight κ δ) = prodMkRight (snd κ) δ := rfl

end ProdMkRight

lemma map_prodMkLeft (γ : Type*) [MeasurableSpace γ] (κ : kernel α β)
    {f : β → δ} (hf : Measurable f) :
    map (prodMkLeft γ κ) f hf = prodMkLeft γ (map κ f hf) := rfl

lemma fst_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : kernel α (β × γ)) :
    fst (prodMkLeft δ κ) = prodMkLeft δ (fst κ) := rfl

lemma snd_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : kernel α (β × γ)) :
    snd (prodMkLeft δ κ) = prodMkLeft δ (snd κ) := rfl

lemma _root_.MeasureTheory.Measure.comap_swap (μ : Measure (α × β)) :
    μ.comap Prod.swap = μ.map Prod.swap := by
  ext s hs
  rw [Measure.comap_apply _ Prod.swap_injective _ _ hs, Measure.map_apply measurable_swap hs,
    ← Set.image_swap_eq_preimage_swap]
  intro s hs
  rw [Set.image_swap_eq_preimage_swap]
  exact measurable_swap hs

lemma comap_prod_swap (κ : kernel α β) (η : kernel γ δ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    comap (prodMkRight η α ×ₖ prodMkLeft γ κ) Prod.swap measurable_swap
      = map (prodMkRight κ γ ×ₖ prodMkLeft α η) Prod.swap measurable_swap := by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_comap, lintegral_map _ _ _ hf, lintegral_prod _ _ _ hf,
    lintegral_prod]
  swap; · exact hf.comp measurable_swap
  simp only [prodMkRight_apply, Prod.fst_swap, Prod.swap_prod_mk, lintegral_prodMkLeft,
    Prod.snd_swap]
  refine (lintegral_lintegral_swap ?_).symm
  exact (hf.comp measurable_swap).aemeasurable

lemma map_prod_swap (κ : kernel α β) (η : kernel α γ) [IsMarkovKernel κ] [IsMarkovKernel η] :
    map (κ ×ₖ η) Prod.swap measurable_swap = η ×ₖ κ := by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_map _ _ _ hf, lintegral_prod, lintegral_prod _ _ _ hf]
  swap; · exact hf.comp measurable_swap
  refine (lintegral_lintegral_swap ?_).symm
  exact hf.aemeasurable

end ProbabilityTheory.kernel

end aux_kernel


section measure_compProd

namespace MeasureTheory.Measure

open ProbabilityTheory

attribute [local simp] kernel.const_apply kernel.prodMkLeft_apply kernel.prodMkLeft_apply'

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

/-- The composition product of a measure and a kernel. -/
noncomputable
def compProd (μ : Measure α) (κ : kernel α β) : Measure (α × β) :=
  (kernel.const Unit μ ⊗ₖ kernel.prodMkLeft Unit κ) ()

/-- The composition product of a measure and a kernel. -/
scoped[ProbabilityTheory] infixl:100 " ⊗ₘ " => MeasureTheory.Measure.compProd

@[simp] lemma compProd_zero_left (κ : kernel α β) : (0 : Measure α) ⊗ₘ κ = 0 := by simp [compProd]
@[simp] lemma compProd_zero_right (μ : Measure α) : μ ⊗ₘ (0 : kernel α β) = 0 := by simp [compProd]

lemma compProd_apply (μ : Measure α) [IsFiniteMeasure μ] (κ : kernel α β) [IsSFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ := by
  simp_rw [compProd, kernel.compProd_apply _ _ _ hs, kernel.const_apply, kernel.prodMkLeft_apply']
  rfl

lemma lintegral_compProd (μ : Measure α) [IsFiniteMeasure μ] (κ : kernel α β) [IsSFiniteKernel κ]
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd, kernel.lintegral_compProd _ _ _ hf]
  simp

lemma compProd_congr {κ η : kernel α β} [IsFiniteMeasure μ] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : κ =ᵐ[μ] η) : μ ⊗ₘ κ = μ ⊗ₘ η := by
  ext s hs
  have : (fun a ↦ κ a (Prod.mk a ⁻¹' s)) =ᵐ[μ] fun a ↦ η a (Prod.mk a ⁻¹' s) := by
    filter_upwards [h] with a ha using by rw [ha]
  rw [compProd_apply μ _ hs, lintegral_congr_ae this, compProd_apply μ _ hs]

lemma dirac_compProd_apply [MeasurableSingletonClass α] (a : α) (κ : kernel α β) [IsSFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    (Measure.dirac a ⊗ₘ κ) s = κ a (Prod.mk a ⁻¹' s) := by
  rw [compProd_apply _ _ hs, lintegral_dirac]

lemma dirac_unit_compProd (κ : kernel Unit β) [IsSFiniteKernel κ] :
    Measure.dirac () ⊗ₘ κ = (κ ()).map (Prod.mk ()) := by
  ext s hs; rw [dirac_compProd_apply _ _ hs, Measure.map_apply measurable_prod_mk_left hs]

lemma dirac_unit_compProd_const (μ : Measure β) [IsFiniteMeasure μ] :
    Measure.dirac () ⊗ₘ kernel.const Unit μ = μ.map (Prod.mk ()) := by
  rw [dirac_unit_compProd, kernel.const_apply]

instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (μ ⊗ₘ κ) := by
  rw [compProd]; infer_instance

instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (μ ⊗ₘ κ) := by
  rw [compProd]; infer_instance

end MeasureTheory.Measure
end measure_compProd
