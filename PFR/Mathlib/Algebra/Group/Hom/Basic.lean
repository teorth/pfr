import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.Pi.Algebra

-- TODO: `pow`,`zpow`, `inv`

variable {ι α β : Type*}

section Group
variable [Group α] [Group β]

-- Move to be near `MonoidHom.map_div`
@[to_additive (attr := simp)]
lemma MonoidHom.comp_div (π : α →* β) (f g : ι → α) : π ∘ (f / g) = π ∘ f / π ∘ g := by ext; simp

end Group
