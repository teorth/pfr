module

public import Mathlib.Data.Finset.Basic

public section

namespace Finset
variable {α : Type*} {s : Finset α}

@[simp] lemma ne_empty_iff_nonempty : s ≠ ∅ ↔ s.Nonempty := nonempty_iff_ne_empty.symm

end Finset
