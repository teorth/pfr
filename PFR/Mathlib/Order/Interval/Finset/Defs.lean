module

public import Mathlib.Order.Interval.Finset.Defs

public section

namespace Finset
variable {α : Type*} [One α] [Preorder α] [IsBotOneClass α] [LocallyFiniteOrderTop α] [Fintype α]

@[to_additive (attr := simp)] lemma Ici_one : Ici (1 : α) = univ := by ext; simp

end Finset
