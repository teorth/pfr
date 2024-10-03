import Mathlib.Data.Set.Pointwise.Finite
import PFR.Mathlib.Data.Set.Function

open Function
open scoped Pointwise

namespace Set
variable {α β γ : Type*} {f g : α → β} {x : α × β}

variable {α β : Type*} [AddCommGroup α] [Fintype α] [AddCommGroup β] [Fintype β] [DecidableEq α]
  [DecidableEq β]

/-- The pairs of points in the graph of `f` satisyfing that their sum still belongs to the
graph correspond to the pairs `(x, y)` with `f (x + y) = f x + f y` (by considering the first
coordinates). -/
def equivFilterGraph (f : α → β) :
    let A := (univ.graphOn f).toFinite.toFinset
    (A ×ˢ A).filter (fun (a, a') ↦ a + a' ∈ A) ≃ {x : α × α | f (x.1 + x.2) = f x.1 + f x.2} where
  toFun := fun ⟨a, ha⟩ ↦ by
    let A := (univ.graphOn f).toFinite.toFinset
    use (a.1.1, a.2.1)
    apply Finset.mem_filter.mp at ha
    have h {a} (ha : a ∈ A) : f a.1 = a.2 := by simpa [A] using ha
    show f (a.1.1 + a.2.1) = (f a.1.1) + (f a.2.1)
    rw [h (Finset.mem_product.mp ha.1).1, h (Finset.mem_product.mp ha.1).2]
    exact h ha.2
  invFun := fun ⟨a, ha⟩ ↦ by
    use ((a.1, f a.1), (a.2, f a.2))
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    <;> apply (univ.graphOn f).toFinite.mem_toFinset.mpr
    · exact ⟨a.1, by simp⟩
    · exact ⟨a.2, by simp⟩
    · exact mem_graphOn.mpr (by simpa)
  left_inv := fun ⟨x, hx⟩ ↦ by
    apply Subtype.ext
    show ((x.1.1, f x.1.1), x.2.1, f x.2.1) = x
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
    rewrite [(univ.graphOn f).toFinite.mem_toFinset] at hx1 hx2
    rw [(mem_graphOn.mp hx1).2, (mem_graphOn.1 hx2).2]
  right_inv := fun _ ↦ rfl

end Set
