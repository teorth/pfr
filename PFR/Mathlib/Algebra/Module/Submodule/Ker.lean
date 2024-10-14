import Mathlib.Algebra.Module.Submodule.Ker

lemma LinearMap.ker_domRestrict {R M M₁ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid M₁] [Module R M₁] (p : Submodule R M) (f : M →ₗ[R] M₁) :
    LinearMap.ker (f.domRestrict p) = (LinearMap.ker f).comap p.subtype := ker_comp ..
