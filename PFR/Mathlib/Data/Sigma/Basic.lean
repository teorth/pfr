import Mathlib.Data.Sigma.Basic

namespace Sigma
variable {α γ : Type*} {β : α → Type*}

/-- Nondependent eliminator for `Sigma`. -/
def elim (f : ∀ a, β a → γ) (a : Sigma β) : γ := Sigma.casesOn a f

end Sigma
