import Mathlib.Data.Finset.Basic

namespace Finset
variable {ι κ α : Type*}

lemma disjiUnion_filter_eq [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β) :
    t.disjiUnion (fun a ↦ s.filter fun c ↦ f c = a)
      (fun x' hx y' hy hne ↦ by
        simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl) =
      s.filter fun c ↦ f c ∈ t :=
  ext fun b => by simpa using and_comm

end Finset
