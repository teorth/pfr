import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Sigma

namespace Set

variable {ι β Ω: Type*} {κ : ι → Type*}

theorem iInter_sigma (S : Set ι) (T : ∀ i, Set (κ i)) (f : ∀ i, κ i → Set Ω) :
    ⋂ i ∈ S, ⋂ j : T i, f i j = ⋂ ij ∈ (Set.Sigma S T), f ij.1 ij.2 := by
  apply Set.ext
  intro x
  simp_rw [Set.mem_iInter]
  constructor
  . exact fun h ij hij ↦ h ij.fst hij.1 ({ val := ij.snd, property := hij.right } : T ij.fst)
  . exact fun h i hi j ↦ h (Sigma.mk i j) (Set.mk_mem_sigma hi j.property)

end Set
