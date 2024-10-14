import Mathlib.Algebra.Module.Submodule.Map

open Function

variable {F R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
  [Module R M] [Module R₂ M₂] {σ₁₂ : R →+* R₂} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]
  [RingHomSurjective σ₁₂] {f : F}

lemma Submodule.comap_lt_comap_iff_of_surjective (hf : Surjective f) {p q : Submodule R₂ M₂} :
    p.comap f < q.comap f ↔ p < q :=
  lt_iff_lt_of_le_iff_le' (comap_le_comap_iff_of_surjective hf ..)
    (comap_le_comap_iff_of_surjective hf ..)
