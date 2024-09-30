import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Tactic.Abel
import PFR.Mathlib.Data.Set.Function

open Function

namespace Set
variable {α β γ : Type*} {f g : α → β} {x : α × β}

lemma graphOn_add [AddGroup α] [AddCommGroup β] {f : α →+ β} {c : α × β} :
    (c+·) '' univ.graphOn f = {(α, f α + (c.2 - f c.1)) | α : α} := by
  ext x
  simp only [Set.image_add_left, Set.mem_preimage, mem_graphOn,
    Prod.fst_add, Prod.snd_add, Set.mem_setOf_eq, Prod.fst_neg, Prod.snd_neg, AddMonoidHom.map_add,
    AddMonoidHom.map_neg]
  constructor
  · intro h
    use x.1
    rw [add_comm]
    simp [sub_eq_add_neg, add_assoc, h, add_neg_cancel_left]
  · rintro ⟨α, rfl⟩
    simp
    abel

end Set
