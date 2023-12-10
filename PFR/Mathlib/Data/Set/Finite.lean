import Mathlib.Data.Set.Finite

namespace Set
section Image2
variable {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β}

lemma finite_image2 (hfs : ∀ b ∈ t, InjOn (f · b) s) (hft : ∀ a ∈ s, InjOn (f a) t) :
    (image2 f s t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ := by
  rw [← not_infinite, infinite_image2 hfs hft]
  simp [not_or, -not_and, not_and_or, not_nonempty_iff_eq_empty]
  aesop

end Image2

variable {s : Set β} {f : α → β}

protected lemma Infinite.preimage (hs : s.Infinite) (hf : s ⊆ range f) : (f ⁻¹' s).Infinite :=
  fun h ↦ hs $ finite_of_finite_preimage h hf

lemma Infinite.preimage' (hs : (s ∩ range f).Infinite) : (f ⁻¹' s).Infinite :=
  (hs.preimage $ inter_subset_right _ _).mono $ preimage_mono $ inter_subset_left _ _

end Set
