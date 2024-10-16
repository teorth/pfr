import Mathlib.Algebra.Module.Submodule.Range

open Submodule

variable {R R₂ M M₂ F : Type*} [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
  [Module R M] [Module R M₂] {τ₁₂ : R →+* R₂} [FunLike F M M₂]

lemma LinearMap.range_domRestrict (K : Submodule R M) (f : M →ₗ[R] M₂) :
    range (domRestrict f K) = K.map f := by ext; simp
