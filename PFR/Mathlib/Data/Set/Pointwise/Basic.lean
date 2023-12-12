import Mathlib.Data.Set.Pointwise.Basic

open Set Pointwise Function

@[to_additive]
lemma Set.mul_subset_range {F α β : Type*} [Mul α] [Mul β] [MulHomClass F α β]
    {f : F} {s t : Set β} (hs : s ⊆ range f) (ht : t ⊆ range f) : s * t ⊆ range f := by
  rintro _ ⟨x, y, hx, hy, rfl⟩
  rcases hs hx with ⟨z, rfl⟩
  rcases ht hy with ⟨w, rfl⟩
  exact ⟨z*w, map_mul _ _ _⟩

@[to_additive]
lemma Set.preimage_mul_preimage {F α β : Type*} [Mul α] [Mul β] [MulHomClass F α β]
    {m : F} (hm : Injective m) {s t : Set β} (hs : s ⊆ range m) (ht : t ⊆ range m) :
    m ⁻¹' s * m ⁻¹' t = m ⁻¹' (s * t) := by
  apply subset_antisymm (preimage_mul_preimage_subset m)
  rintro x ⟨y, z, hy, hz, hx : y * z = _⟩
  rcases hs hy with ⟨u, rfl⟩
  rcases ht hz with ⟨v, rfl⟩
  erw [← map_mul] at hx
  use u, v, hy, hz, hm hx
