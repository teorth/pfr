import Mathlib.Data.Fintype.Lattice

namespace Finset

variable {α β : Type*} {u : α → Set β}

/-- Analogue of `Set.biInter_univ` -/
theorem set_biInter_univ [Fintype α] : ⋂ x, u x = ⋂ x : Finset.univ (α := α), u x := by ext; simp

end Finset
