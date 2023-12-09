import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Basic

namespace Fintype

variable {ι Ω: Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]

theorem iInter_sigma (S : Finset ι) (f : ∀ i, κ i → Set Ω) :
    ⋂ i ∈ S, ⋂ j : κ i, f i j = ⋂ ij ∈ (Finset.sigma S (fun i ↦ Finset.univ)), f ij.1 ij.2 := by
  ext
  simp_rw [Finset.mem_sigma, Finset.mem_univ, and_true, Set.mem_iInter, Sigma.forall]
  exact Iff.intro (fun _ _ _ _ ↦ by simp_all only) (fun _ _ _ _ ↦ by simp_all only)

/-- $(j : \kappa\;i) \to (i, j)$ -/
def sigma_singleton (i : ι) (κ : ι → Type*) [∀ i, Fintype (κ i)] :=
  Finset.sigma {i} (fun i ↦ Finset.univ (α := κ i))

def sigma_singleton_apply (i : ι) (j : κ i) : sigma_singleton (κ := κ) i := by
  constructor ; swap
  . exact Sigma.mk i j
  . exact Finset.mem_sigma.mpr ⟨ Finset.mem_singleton_self i, Fintype.complete j ⟩

theorem sigma_singleton_surjective (i : ι) :
    Function.Surjective (sigma_singleton_apply (κ := κ) i) := by
  intro ij
  use ?_ ; swap
  · convert ij.val.snd
    exact (Finset.mem_singleton.mp (Finset.mem_sigma.mp ij.property).left).symm
  · show sigma_singleton_apply i (Eq.mpr _ ij.val.snd) = ij
    aesop_destruct_products
    simp_all only [sigma_singleton_apply, eq_mpr_eq_cast,
      Subtype.mk.injEq, Sigma.mk.inj_iff, cast_heq, and_true]
    simp_all only [sigma_singleton, Finset.mem_sigma, Finset.mem_singleton]

theorem sigma_singleton_injective (i : ι) : Function.Injective (sigma_singleton_apply (κ := κ) i) :=
  fun _ _ h ↦ sigma_mk_injective (Subtype.mk_eq_mk.mp h)

theorem sigma_singleton_bijective (i : ι) : Function.Bijective (sigma_singleton_apply (κ := κ) i) :=
  And.intro (sigma_singleton_injective i) (sigma_singleton_surjective i)

end Fintype
