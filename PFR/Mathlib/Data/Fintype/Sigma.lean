import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Basic

namespace Fintype

variable {ι Ω: Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]

theorem iInter_sigma (S : Finset ι) (f : ∀ i, κ i → Set Ω) :
    ⋂ i ∈ S, ⋂ j : κ i, f i j = ⋂ ij ∈ (Finset.sigma S (fun i ↦ Finset.univ)), f ij.1 ij.2 := by
  ext
  simp_rw [Finset.mem_sigma, Finset.mem_univ, and_true, Set.mem_iInter, Sigma.forall]
  exact Iff.intro (fun _ _ _ _ ↦ by simp_all only) (fun _ _ _ _ ↦ by simp_all only)

end Fintype
