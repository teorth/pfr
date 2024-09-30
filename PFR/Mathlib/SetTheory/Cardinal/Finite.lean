import Mathlib.SetTheory.Cardinal.Finite
import PFR.Mathlib.Data.Set.Function

namespace Set
variable {α β : Type*} {s : Set α}

lemma Nonempty.card_pos (hs : s.Nonempty) (hs' : s.Finite) : 0 < Nat.card s := by
  have := hs.to_subtype; have := hs'.to_subtype; exact Nat.card_pos

@[simp] lemma card_graphOn (s : Set α) (f : α → β) : Nat.card (s.graphOn f) = Nat.card s := by
  rw [← Nat.card_image_of_injOn fst_injOn_graph, image_fst_graphOn]

end Set
