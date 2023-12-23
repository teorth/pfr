import Mathlib.SetTheory.Cardinal.Finite

namespace Set
variable {α : Type*} {s : Set α}

lemma Nonempty.card_pos (hs : s.Nonempty) (hs' : s.Finite) : 0 < Nat.card s := by
  have := hs.to_subtype; have := hs'.to_subtype; exact Nat.card_pos

end Set
