import Mathlib.Data.Set.Function

open Function

namespace Set
variable {α β γ : Type*} {s : Set α} {f g : α → β} {x : α × β}

@[simp] lemma mem_graphOn : x ∈ s.graphOn f ↔ x.1 ∈ s ∧ f x.1 = x.2 := by aesop (add simp graphOn)

lemma fst_injOn_graph : (s.graphOn f).InjOn Prod.fst := by aesop (add simp InjOn)

lemma graphOn_univ_eq_range : univ.graphOn f = range fun x ↦ (x, f x) := image_univ

lemma graphOn_univ_injective : Injective (univ.graphOn : (α → β) → Set (α × β)) := by
  aesop (add simp [Injective, Set.ext_iff])

@[simp]
lemma graphOn_univ_inj : univ.graphOn f = univ.graphOn g ↔ f = g := graphOn_univ_injective.eq_iff

@[simp] lemma image_snd_graphOn (f : α → β) : Prod.snd '' s.graphOn f = f '' s := by ext x; simp

lemma graphOn_comp (s : Set α) (f : α → β) (g : β → γ) :
    s.graphOn (g ∘ f) = (fun x ↦ (x.1, g x.2)) '' s.graphOn f := by aesop

@[simp]
lemma graphOn_nonempty : (s.graphOn f).Nonempty ↔ s.Nonempty := by aesop (add simp Set.Nonempty)

protected alias ⟨_, Nonempty.graphOn⟩ := graphOn_nonempty

end Set
