import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.SetTheory.Cardinal.Finite

open scoped Pointwise

namespace Set
variable {α : Type*} [AddCommGroup α] {s t : Set α}

/-- **Ruzsa's covering lemma** for sets. See also `Finset.exists_subset_add_sub`. -/
lemma exists_subset_add_sub (hs : s.Finite) (ht' : t.Finite) (ht : t.Nonempty) :
    ∃ u : Set α, Nat.card u * Nat.card t ≤ Nat.card (s + t) ∧ s ⊆ u + t - t ∧ u.Finite := by
  lift s to Finset α using hs
  lift t to Finset α using ht'
  classical
  obtain ⟨u, hu, hsut⟩ := Finset.exists_subset_add_sub s ht
  refine ⟨u, ?_⟩
  norm_cast
  simp [*]

end Set

namespace Set
variable {α : Type*} [CommGroup α] {s t : Set α}

/-- **Ruzsa's covering lemma** for sets. See also `Finset.exists_subset_mul_div`. -/
@[to_additive existing "**Ruzsa's covering lemma**. Version for sets. For finsets,
see `Finset.exists_subset_add_sub`."]
lemma exists_subset_mul_div (hs : s.Finite) (ht' : t.Finite) (ht : t.Nonempty) :
    ∃ u : Set α, Nat.card u * Nat.card t ≤ Nat.card (s * t) ∧ s ⊆ u * t / t ∧ u.Finite := by
  lift s to Finset α using hs
  lift t to Finset α using ht'
  classical
  obtain ⟨u, hu, hsut⟩ := Finset.exists_subset_mul_div s ht
  refine ⟨u, ?_⟩
  norm_cast
  simp [*]
