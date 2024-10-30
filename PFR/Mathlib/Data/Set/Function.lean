import Mathlib.Data.Set.Function

variable {α β γ δ : Type*}

lemma graphOn_prod_graphOn (s : Set α) (t : Set β) (f : α → γ) (g : β → δ) :
    s.graphOn f ×ˢ t.graphOn g = Equiv.prodProdProdComm .. ⁻¹' (s ×ˢ t).graphOn (Prod.map f g) := by
  aesop
