
import Mathlib.Probability.Kernel.Composition
import PFR.Entropy.Measure

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
lemma const_zero : kernel.const α (0 : Measure β) = 0 := by
  ext x s _; simp [kernel.const_apply]

@[simp]
lemma prodMkLeft_zero : kernel.prodMkLeft α (0 : kernel β γ) = 0 := by
  ext x s _; simp [kernel.prodMkLeft_apply']

@[simp]
lemma fst_zero : fst (0 : kernel α (β × γ)) = 0 := by simp [fst]

@[simp]
lemma snd_zero : snd (0 : kernel α (β × γ)) = 0 := by simp [snd]

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

end ProbabilityTheory.kernel

end aux_kernel


section measure_compProd

namespace MeasureTheory.Measure

open ProbabilityTheory

attribute [local simp] kernel.const_apply kernel.prodMkLeft_apply kernel.prodMkLeft_apply'

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

noncomputable
def compProd (μ : Measure α) (κ : kernel α β) :
    Measure (α × β) :=
  ((kernel.const Unit μ) ⊗ₖ (kernel.prodMkLeft Unit κ)) ()

scoped[ProbabilityTheory] infixl:100 " ⊗ₘ " => MeasureTheory.Measure.compProd

@[simp]
lemma compProd_zero_left (κ : kernel α β) :
    (0 : Measure α) ⊗ₘ κ = 0 := by simp [compProd]

@[simp]
lemma compProd_zero_right (μ : Measure α) :
    μ ⊗ₘ (0 : kernel α β) = 0 := by simp [compProd]

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
    ((Measure.dirac a) ⊗ₘ κ) s = κ a (Prod.mk a ⁻¹' s) := by
  rw [compProd_apply _ _ hs, lintegral_dirac]

lemma dirac_unit_compProd (κ : kernel Unit β) [IsSFiniteKernel κ] :
    (Measure.dirac ()) ⊗ₘ κ = (κ ()).map (Prod.mk ()) := by
  ext s hs; rw [dirac_compProd_apply _ _ hs, Measure.map_apply measurable_prod_mk_left hs]

lemma dirac_unit_compProd_const (μ : Measure β) [IsFiniteMeasure μ] :
    (Measure.dirac ()) ⊗ₘ (kernel.const Unit μ) = μ.map (Prod.mk ()) := by
  rw [dirac_unit_compProd, kernel.const_apply]

instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (μ ⊗ₘ κ) := by
  rw [compProd]; infer_instance

end MeasureTheory.Measure

end measure_compProd
