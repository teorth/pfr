import PFR.Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Submodule

variable { B F R : Type* } [DivisionRing R] [AddCommGroup B] [AddCommGroup F]
  [Module R B] [Module R F]

open LinearMap

/-- Given a submodule $E$ of $B \times F$, there is an equivalence $f : E \to B' \times F'$
  where $B'$ and $F'$ are submodules of $B$ and $F$ respectively, and
  $f$ agrees with the projection $E \to B$.
  $\phi$ is the offset by which $F'$ can be unprojected from $B'$. -/
theorem equivProdSubmodule (E : Submodule R (B × F)) :
    ∃ (B' : Submodule R B) (F' : Submodule R F) (f : E ≃ₗ[R] B' × F') (φ : B →ₗ[R] F),
    (∀ x, (f x).1 = x.val.1 ∧ (f x).2 = x.val.2 - φ x.val.1) ∧
    (∀ x₁ x₂, f.symm (x₁, x₂) = (x₁.val, x₂.val + φ x₁.val)) := by
  let π₁ := LinearMap.fst R B F
  let f₁ := π₁.submoduleMap E
  have f₁_surj := range_eq_top.mpr (π₁.submoduleMap_surjective E)

  let ⟨ φ', hφ' ⟩ := f₁.exists_rightInverse_of_surjective f₁_surj
  let ⟨ φ, hφ ⟩ := φ'.exists_extend

  let p₂ := (LinearMap.snd R B F).domRestrict E
  let f₂'' := LinearMap.id - φ'.comp f₁
  let f₂' := p₂.comp f₂''
  let f₂ := f₂'.rangeRestrict

  have h_compl : IsCompl (ker f₁) (ker f₂) := by
    refine IsCompl.of_eq ?_ ?_
    · by_contra hc
      obtain ⟨ x, ⟨ h_ker, h_nezero ⟩ ⟩ := exists_mem_ne_zero_of_ne_bot hc
      simp_rw [mem_inf, mem_ker] at h_ker
      have h_zero₁ : x.val.1 = 0 := by rw [show x.val.1 = f₁ x from rfl, h_ker.left] ; rfl
      have h_zero₂: (f₂'' x).val.2 = 0 := (mk_eq_zero _ _).mp h_ker.right
      simp [show φ' (f₁ x) = 0 by simp_all only [LinearMap.map_zero]] at h_zero₂
      exact h_nezero (coe_eq_zero.mp (Prod.ext h_zero₁ h_zero₂))
    · simp_rw [eq_top_iff', mem_sup']
      intro x
      have : φ x.val.1 = φ' (f₁ x) := by subst hφ ; rfl
      have h_ker₁ : f₂'' x ∈ ker f₁ := by simp [hφ', ← f₁.comp_apply φ']
      have h_ker₂ : φ x.val.1 ∈ ker f₂ := by simp [this, hφ', ← f₁.comp_apply φ']
      use ⟨ f₂'' x, h_ker₁ ⟩, ⟨ φ x.val.1, h_ker₂ ⟩
      simp [add_comm_sub, sub_eq_zero, ← hφ] ; rfl

  let f := equivProdOfSurjectiveOfIsCompl f₁ f₂ f₁_surj f₂'.range_rangeRestrict h_compl
  use E.map π₁, range f₂', f, p₂.comp φ
  constructor
  · intro _
    rw [equivProdOfSurjectiveOfIsCompl_apply]
    constructor ; rfl ; subst hφ ; rfl
  · intro x₁ x₂
    let x := f.symm (x₁, x₂)
    have : (f₁ x, f₂ x) = (x₁, x₂) := f.apply_symm_apply (x₁, x₂)
    have : x.val.2 - p₂ (φ x.val.1) = p₂ (x - φ' (f₁ x)) := by subst hφ ; rfl
    have : (x₁.val, x₂.val + p₂ (φ x.val.1)) = (x.val.1, x.val.2)  := by
      rw [← add_zero x₁.val, ← Prod.mk_add_mk, ← eq_sub_iff_add_eq, Prod.mk_sub_mk, sub_zero, this]
      show (x₁.val, x₂.val) = ((f₁ x).val, (f₂ x).val)
      simp_all only [Prod.mk.injEq]
    subst hφ ; simp_all
