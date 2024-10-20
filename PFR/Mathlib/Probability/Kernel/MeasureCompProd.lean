import Mathlib.Probability.Kernel.Composition

open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

lemma compProd_preimage_fst (κ : Kernel α β) (η : Kernel (α × β) γ) [IsSFiniteKernel κ]
    [IsMarkovKernel η] {s : Set β} (hs : MeasurableSet s) (x : α) :
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
    (κ : Kernel α β) [IsSFiniteKernel κ]
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
      rw [setLIntegral_congr_fun ht (ae_of_all _ this), setLIntegral_one]
    intro b hb
    simp only [t, Set.mem_setOf_eq] at hb
    simp [hb]
  have h2 : ∫⁻ b in tᶜ, if (b, f (x, b)) ∈ s then 1 else 0 ∂(κ x) = 0 := by
    suffices ∀ b ∈ tᶜ, (if (b, f (x, b)) ∈ s then (1 : ℝ≥0∞) else 0) = 0 by
      rw [setLIntegral_congr_fun ht.compl (ae_of_all _ this), lintegral_zero]
    intro b hb
    simp only [t, Set.mem_compl_iff, Set.mem_setOf_eq] at hb
    simp [hb]
  rw [h1, h2, add_zero]

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {f : β → γ} {g : γ → α}

lemma comap_prod_swap (κ : Kernel α β) (η : Kernel γ δ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    comap (prodMkRight α η ×ₖ prodMkLeft γ κ) Prod.swap measurable_swap
      = map (prodMkRight γ κ ×ₖ prodMkLeft α η) Prod.swap := by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_comap, lintegral_map _ measurable_swap _ hf, lintegral_prod _ _ _ hf,
    lintegral_prod]
  swap; · exact hf.comp measurable_swap
  simp only [prodMkRight_apply, Prod.fst_swap, Prod.swap_prod_mk, lintegral_prodMkLeft,
    Prod.snd_swap]
  refine (lintegral_lintegral_swap ?_).symm
  exact (hf.comp measurable_swap).aemeasurable

lemma map_prod_swap (κ : Kernel α β) (η : Kernel α γ) [IsMarkovKernel κ] [IsMarkovKernel η] :
    map (κ ×ₖ η) Prod.swap = η ×ₖ κ := by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_map _ measurable_swap _ hf, lintegral_prod, lintegral_prod _ _ _ hf]
  swap; · exact hf.comp measurable_swap
  refine (lintegral_lintegral_swap ?_).symm
  exact hf.aemeasurable

end ProbabilityTheory.Kernel
