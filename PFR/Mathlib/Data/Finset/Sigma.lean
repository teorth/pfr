import Mathlib.Data.Finset.Sigma

section Finset

variable {ι Ω: Type*} {κ : ι → Type*}

theorem Finset.iInter_sigma (S : Finset ι) (T : ∀ i, Finset (κ i)) (f : ∀ i, κ i → Set Ω) :
    ⋂ i ∈ S, ⋂ j : T i, f i j = ⋂ ij ∈ (Finset.sigma S T), f ij.1 ij.2 := by
  apply Set.ext
  intro x
  simp_rw [Set.mem_iInter]
  constructor
  . refine fun h ij hij ↦ h ij.fst ?_ ({ val := ij.snd, property := ?_ } : T ij.fst)
    all_goals { simp_all only [Finset.mem_sigma] }
  . refine fun h i hi j ↦ h (Sigma.mk i j) (Finset.mem_sigma.mpr (And.intro hi j.property ))

end Finset
