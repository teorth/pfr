import Mathlib.Probability.Kernel.MeasureCompProd
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

namespace ProbabilityTheory.kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

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
