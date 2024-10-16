import Mathlib.LinearAlgebra.Quotient

namespace Submodule.Quotient
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M}

nonrec lemma «forall» {P : M ⧸ p → Prop} : (∀ a, P a) ↔ ∀ a : M, P ⟦a⟧ := Quotient.forall

end Submodule.Quotient
