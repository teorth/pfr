import Mathlib.Analysis.Convex.StdSimplex

namespace stdSimplex
variable {𝕜 ι : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]

@[simp, norm_cast] lemma coe_mk (f : ι → 𝕜) (hf) : (⟨f, hf⟩ : stdSimplex 𝕜 ι) = f := rfl

@[simp] lemma val_eq_coe (f : stdSimplex 𝕜 ι) : f.val = f := rfl

end stdSimplex
