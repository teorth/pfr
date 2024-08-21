import Mathlib.Probability.Kernel.Composition
import PFR.Mathlib.Probability.Kernel.Disintegration

open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

section
variable {α β γ δ ε : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {_ : MeasurableSpace ε}

variable {Ω S T β : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace β] [MeasurableSpace γ]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → β}

lemma map_map (κ : Kernel α β) {f : β → γ} (hf : Measurable f) {g : γ → δ} (hg : Measurable g) :
    map (map κ f hf) g hg = map κ (g ∘ f) (hg.comp hf) := by
  ext x s _
  rw [map_apply, map_apply, map_apply, Measure.map_map hg hf]

lemma map_swapRight (κ : Kernel α (β × γ)) {f : (γ × β) → δ} (hf : Measurable f) :
    map (swapRight κ) f hf = map κ (f ∘ Prod.swap) (hf.comp measurable_swap) := by
  rw [swapRight, map_map]

/-- Given a kernel taking values in a product of three spaces, forget the middle one. -/
noncomputable
def deleteMiddle (κ : Kernel α (β × γ × δ)) :
    Kernel α (β × δ) :=
  map κ (fun p ↦ (p.1, p.2.2)) (measurable_fst.prod_mk (measurable_snd.comp measurable_snd))

instance (κ : Kernel α (β × γ × δ)) [IsMarkovKernel κ] :
    IsMarkovKernel (deleteMiddle κ) := by
  rw [deleteMiddle]
  infer_instance

@[simp]
lemma fst_deleteMiddle (κ : Kernel α (β × γ × δ)) : fst (deleteMiddle κ) = fst κ := by
  rw [deleteMiddle, fst_map_prod]
  · rfl
  · exact measurable_snd.comp measurable_snd

@[simp]
lemma snd_deleteMiddle (κ : Kernel α (β × γ × δ)) : snd (deleteMiddle κ) = snd (snd κ) := by
  rw [deleteMiddle, snd_map_prod]
  · rw [snd, snd, map_map]
    rfl
  · exact measurable_fst

@[simp, nolint simpNF]
lemma deleteMiddle_map_prod (κ : Kernel α β) {f : β → γ} {g : β → δ} {g' : β → ε}
    (hf : Measurable f) (hg : Measurable g) (hg' : Measurable g') :
    deleteMiddle (map κ (fun b ↦ (f b, g b, g' b)) (hf.prod_mk (hg.prod_mk hg')))
      = map κ (fun b ↦ (f b, g' b)) (hf.prod_mk hg') := by
  simp only [deleteMiddle, map_map]
  congr

@[simp]
lemma deleteMiddle_compProd (ξ : Kernel α β) [IsSFiniteKernel ξ]
    (κ : Kernel (α × β) (γ × δ)) [IsSFiniteKernel κ] :
    deleteMiddle (ξ ⊗ₖ κ) = ξ ⊗ₖ snd κ := by
  ext x s hs
  rw [deleteMiddle, map_apply' _ _ _ hs, compProd_apply _ _ _ hs, compProd_apply]
  swap; · exact measurable_fst.prod_mk measurable_snd.snd hs
  congr with b
  simp only [Set.mem_preimage]
  rw [snd_apply']
  swap; · exact measurable_prod_mk_left hs
  congr

/-- Given a kernel taking values in a product of three spaces, forget the last variable. -/
noncomputable
def deleteRight (κ : Kernel α (β × γ × δ)) : Kernel α (β × γ) :=
  map κ (fun p ↦ (p.1, p.2.1)) (measurable_fst.prod_mk (measurable_fst.comp measurable_snd))

instance (κ : Kernel α (β × γ × δ)) [IsMarkovKernel κ] :
    IsMarkovKernel (deleteRight κ) := by
  rw [deleteRight]; infer_instance

@[simp]
lemma fst_deleteRight (κ : Kernel α (β × γ × δ)) : fst (deleteRight κ) = fst κ := by
  rw [deleteRight, fst_map_prod]
  · rfl
  · exact measurable_fst.comp measurable_snd

@[simp]
lemma snd_deleteRight (κ : Kernel α (β × γ × δ)) : snd (deleteRight κ) = fst (snd κ) := by
  rw [deleteRight, snd_map_prod]
  · rw [fst, snd, map_map]
    rfl
  · exact measurable_fst

@[simp, nolint simpNF]
lemma deleteRight_map_prod (κ : Kernel α β) {f : β → γ} {g : β → δ} {g' : β → ε}
    (hf : Measurable f) (hg : Measurable g) (hg' : Measurable g') :
    deleteRight (map κ (fun b ↦ (f b, g b, g' b)) (hf.prod_mk (hg.prod_mk hg')))
      = map κ (fun b ↦ (f b, g b)) (hf.prod_mk hg) := by
  simp only [deleteRight, map_map]
  congr

/-- Given a kernel taking values in a product of three spaces, reverse the order of the spaces. -/
noncomputable
def reverse (κ : Kernel α (β × γ × δ)) : Kernel α (δ × γ × β) :=
  map κ (fun p ↦ (p.2.2, p.2.1, p.1))
    ((measurable_snd.comp measurable_snd).prod_mk
      ((measurable_fst.comp measurable_snd).prod_mk measurable_fst))

@[simp]
lemma reverse_reverse (κ : Kernel α (β × γ × δ)) :
    reverse (reverse κ) = κ := by
  have : ((fun p : δ × γ × β ↦ (p.2.2, p.2.1, p.1)) ∘ fun p ↦ (p.2.2, p.2.1, p.1)) = id := by
    ext1; simp
  simp [reverse, map_map, this]

instance (κ : Kernel α (β × γ × δ)) [IsMarkovKernel κ] :
    IsMarkovKernel (reverse κ) := by
  rw [reverse]
  infer_instance

@[simp]
lemma swapRight_deleteMiddle_reverse (κ : Kernel α (β × γ × δ)) :
    swapRight (deleteMiddle (reverse κ)) = deleteMiddle κ := by
  simp only [swapRight, reverse, deleteMiddle, map_map]
  congr

@[simp]
lemma swapRight_snd_reverse (κ : Kernel α (β × γ × δ)) :
    swapRight (snd (reverse κ)) = deleteRight κ := by
  simp only [swapRight, reverse, deleteMiddle, snd, map_map]
  congr

@[simp]
lemma swapRight_deleteRight_reverse (κ : Kernel α (β × γ × δ)) :
    swapRight (deleteRight (reverse κ)) = snd κ := by
  simp only [swapRight, reverse, deleteRight, snd, map_map]
  congr

/-- Reversing preserves finite kernel support -/
lemma finiteKernelSupport_of_reverse
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {κ : Kernel T (α × β × γ)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (reverse κ) :=
  finiteKernelSupport_of_map hκ _

lemma AEFiniteKernelSupport.reverse
    [MeasurableSingletonClass S] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {κ : Kernel T (S × β × γ)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (reverse κ) μ :=
  hκ.map _

end
