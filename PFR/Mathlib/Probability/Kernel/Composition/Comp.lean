import Mathlib.Probability.Kernel.Composition.Comp
import PFR.Mathlib.Probability.Kernel.Disintegration

open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

section
variable {α β γ δ ε : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {_ : MeasurableSpace ε}

variable {Ω S T : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace γ]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → β}

lemma map_map (κ : Kernel α β) {f : β → γ} (hf : Measurable f) {g : γ → δ} (hg : Measurable g) :
    map (map κ f) g = map κ (g ∘ f) := by
  ext x s _
  rw [map_apply _ hg, map_apply _ hf, map_apply _ (hg.comp hf), Measure.map_map hg hf]

lemma map_swapRight (κ : Kernel α (β × γ)) {f : (γ × β) → δ} :
    map (swapRight κ) f = map κ (f ∘ Prod.swap) := by
  by_cases hf : Measurable f
  · rw [swapRight_eq, map_map _ measurable_swap hf]
  · have : ¬ Measurable (f ∘ Prod.swap) := by
      contrapose! hf
      exact hf.comp measurable_swap
    simp [map_of_not_measurable _ hf, map_of_not_measurable _ this]

/-- Given a kernel taking values in a product of three spaces, forget the middle one. -/
noncomputable
def deleteMiddle (κ : Kernel α (β × γ × δ)) :
    Kernel α (β × δ) :=
  mapOfMeasurable κ (fun p ↦ (p.1, p.2.2))
    (measurable_fst.prod_mk (measurable_snd.comp measurable_snd))

lemma deleteMiddle_eq (κ : Kernel α (β × γ × δ)) :
    deleteMiddle κ = map κ (fun p ↦ (p.1, p.2.2)) := by
  simp [deleteMiddle]

instance (κ : Kernel α (β × γ × δ)) [IsMarkovKernel κ] : IsMarkovKernel (deleteMiddle κ) := by
  rw [deleteMiddle_eq]; apply IsMarkovKernel.map _ (by fun_prop)

instance (κ : Kernel α (β × γ × δ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (deleteMiddle κ) := by
  rw [deleteMiddle_eq]; infer_instance

@[simp]
lemma fst_deleteMiddle (κ : Kernel α (β × γ × δ)) : fst (deleteMiddle κ) = fst κ := by
  rw [deleteMiddle_eq, fst_map_prod, fst_eq]
  exact measurable_snd.comp measurable_snd

@[simp]
lemma snd_deleteMiddle (κ : Kernel α (β × γ × δ)) : snd (deleteMiddle κ) = snd (snd κ) := by
  rw [deleteMiddle_eq, snd_map_prod, snd_eq, snd_eq, map_map _ measurable_snd measurable_snd]
  · rfl
  · exact measurable_fst

@[simp] lemma deleteMiddle_zero : deleteMiddle (0 : Kernel α (β × γ × δ)) = 0 := by
  simp [deleteMiddle_eq]

@[simp, nolint simpNF]
lemma deleteMiddle_map_prod (κ : Kernel α β) {f : β → γ} {g : β → δ} {g' : β → ε}
    (hg : Measurable g) :
    deleteMiddle (map κ (fun b ↦ (f b, g b, g' b)))
      = map κ (fun b ↦ (f b, g' b)) := by
  by_cases hfg' : Measurable (fun b ↦ (f b, g' b))
  · have : Measurable f := hfg'.fst
    have : Measurable g' := hfg'.snd
    rw [deleteMiddle_eq, map_map _ (by fun_prop) (by fun_prop)]
    rfl
  · have : ¬ (Measurable (fun b ↦ (f b, g b, g' b))) := by
      contrapose! hfg'
      have T : Measurable g' := hfg'.snd.snd
      have U : Measurable f := hfg'.fst
      exact U.prod T
    simp [map_of_not_measurable _ hfg', map_of_not_measurable _ this]

@[simp]
lemma deleteMiddle_compProd (ξ : Kernel α β) [IsSFiniteKernel ξ]
    (κ : Kernel (α × β) (γ × δ)) [IsSFiniteKernel κ] :
    deleteMiddle (ξ ⊗ₖ κ) = ξ ⊗ₖ snd κ := by
  ext x s hs
  rw [deleteMiddle_eq, map_apply' _ (by fun_prop) _ hs, compProd_apply hs, compProd_apply]
  swap; · exact measurable_fst.prod_mk measurable_snd.snd hs
  congr with b
  rw [snd_apply']
  swap; · exact measurable_prod_mk_left hs
  congr

/-- Given a kernel taking values in a product of three spaces, forget the last variable. -/
noncomputable
def deleteRight (κ : Kernel α (β × γ × δ)) : Kernel α (β × γ) :=
  mapOfMeasurable κ (fun p ↦ (p.1, p.2.1))
    (measurable_fst.prod_mk (measurable_fst.comp measurable_snd))

lemma deleteRight_eq (κ : Kernel α (β × γ × δ)) :
    deleteRight κ = map κ (fun p ↦ (p.1, p.2.1)) := by simp [deleteRight]

@[simp] lemma deleteRight_zero : deleteRight (0 : Kernel α (β × γ × δ)) = 0 := by
  simp [deleteRight_eq]

instance (κ : Kernel α (β × γ × δ)) [IsMarkovKernel κ] : IsMarkovKernel (deleteRight κ) := by
  rw [deleteRight_eq]; apply IsMarkovKernel.map _ (by fun_prop)

instance (κ : Kernel α (β × γ × δ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (deleteRight κ) := by
  rw [deleteRight_eq]; infer_instance

@[simp]
lemma fst_deleteRight (κ : Kernel α (β × γ × δ)) : fst (deleteRight κ) = fst κ := by
  rw [deleteRight_eq, fst_map_prod, fst_eq]
  exact measurable_fst.comp measurable_snd

@[simp]
lemma snd_deleteRight (κ : Kernel α (β × γ × δ)) : snd (deleteRight κ) = fst (snd κ) := by
  rw [deleteRight_eq, snd_map_prod, snd_eq, fst_eq, map_map _ measurable_snd measurable_fst]
  · rfl
  · exact measurable_fst

@[simp, nolint simpNF]
lemma deleteRight_map_prod (κ : Kernel α β) {f : β → γ} {g : β → δ} {g' : β → ε}
    (hg' : Measurable g') :
    deleteRight (map κ (fun b ↦ (f b, g b, g' b)))
      = map κ (fun b ↦ (f b, g b)) := by
  by_cases hfg : Measurable (fun b ↦ (f b, g b))
  · have : Measurable f := hfg.fst
    have : Measurable g := hfg.snd
    rw [deleteRight_eq, map_map _ (by fun_prop) (by fun_prop)]
    rfl
  · have : ¬ (Measurable (fun b ↦ (f b, g b, g' b))) := by
      contrapose! hfg
      have T : Measurable g := hfg.snd.fst
      have U : Measurable f := hfg.fst
      exact U.prod T
    simp [map_of_not_measurable _ hfg, map_of_not_measurable _ this]

/-- Given a kernel taking values in a product of three spaces, reverse the order of the spaces. -/
noncomputable
def reverse (κ : Kernel α (β × γ × δ)) : Kernel α (δ × γ × β) :=
  mapOfMeasurable κ (fun p ↦ (p.2.2, p.2.1, p.1))
    ((measurable_snd.comp measurable_snd).prod_mk
      ((measurable_fst.comp measurable_snd).prod_mk measurable_fst))

lemma reverse_eq (κ : Kernel α (β × γ × δ)) : reverse κ = map κ (fun p ↦ (p.2.2, p.2.1, p.1)) := by
  simp [reverse]

lemma reverse_zero : reverse (0 : Kernel α (β × γ × δ)) = 0 := by simp [reverse_eq]

@[simp]
lemma reverse_reverse (κ : Kernel α (β × γ × δ)) :
    reverse (reverse κ) = κ := by
  have : ((fun p : δ × γ × β ↦ (p.2.2, p.2.1, p.1)) ∘ fun p ↦ (p.2.2, p.2.1, p.1)) = id := by
    ext1; simp
  rw [reverse_eq, reverse_eq, map_map _ (by fun_prop) (by fun_prop), this, map_id]

instance (κ : Kernel α (β × γ × δ)) [IsMarkovKernel κ] : IsMarkovKernel (reverse κ) := by
  rw [reverse_eq]; apply IsMarkovKernel.map _ (by fun_prop)

instance (κ : Kernel α (β × γ × δ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (reverse κ) := by
  rw [reverse_eq]; infer_instance

@[simp]
lemma swapRight_deleteMiddle_reverse (κ : Kernel α (β × γ × δ)) :
    swapRight (deleteMiddle (reverse κ)) = deleteMiddle κ := by
  rw [swapRight_eq, reverse_eq, deleteMiddle_eq, map_map _ (by fun_prop) (by fun_prop),
    map_map _ (by fun_prop) (by fun_prop), deleteMiddle_eq]
  rfl

@[simp]
lemma swapRight_snd_reverse (κ : Kernel α (β × γ × δ)) :
    swapRight (snd (reverse κ)) = deleteRight κ := by
  rw [swapRight_eq, reverse_eq, deleteRight_eq, snd_eq, map_map _ (by fun_prop) (by fun_prop),
    map_map _ (by fun_prop) (by fun_prop)]
  rfl

@[simp]
lemma swapRight_deleteRight_reverse (κ : Kernel α (β × γ × δ)) :
    swapRight (deleteRight (reverse κ)) = snd κ := by
  rw [swapRight_eq, reverse_eq, deleteRight_eq, snd_eq, map_map _ (by fun_prop) (by fun_prop),
    map_map _ (by fun_prop) (by fun_prop)]
  rfl

/-- Reversing preserves finite kernel support -/
lemma FiniteKernelSupport.reverse
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {κ : Kernel T (α × β × γ)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (reverse κ) := by
  rw [reverse_eq]
  apply hκ.map

lemma AEFiniteKernelSupport.reverse
    [MeasurableSingletonClass S] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {κ : Kernel T (S × β × γ)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (reverse κ) μ := by
  rw [reverse_eq]
  apply hκ.map

end
