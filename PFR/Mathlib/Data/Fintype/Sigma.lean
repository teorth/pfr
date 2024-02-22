import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Basic

variable {ι α : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]

lemma Set.biUnion_finsetSigma_univ (s : Finset ι) (f : Sigma κ → Set α) :
    ⋃ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij = ⋃ i ∈ s, ⋃ j, f ⟨i, j⟩ := by aesop

lemma Set.biUnion_finsetSigma_univ' (s : Finset ι) (f : ∀ i, κ i → Set α) :
    ⋃ i ∈ s, ⋃ j, f i j = ⋃ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij.1 ij.2 := by aesop

lemma Set.biInter_finsetSigma_univ (s : Finset ι) (f : Sigma κ → Set α) :
    ⋂ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij = ⋂ i ∈ s, ⋂ j, f ⟨i, j⟩ := by aesop

lemma Set.biInter_finsetSigma_univ' (s : Finset ι) (f : ∀ i, κ i → Set α) :
    ⋂ i ∈ s, ⋂ j, f i j = ⋂ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij.1 ij.2 := by aesop

