import Mathlib.Util.Notation3
import Mathlib.Tactic.Basic

/-- The pair of two random variables -/
abbrev prod {Ω S T : Type*} (X : Ω → S) (Y : Ω → T) (ω : Ω) : S × T := (X ω, Y ω)

@[inherit_doc prod] notation3:100 "⟨" X ", " Y "⟩" => prod X Y

@[simp]
lemma prod_eq {Ω S T : Type*} {X : Ω → S} {Y : Ω → T} {ω : Ω} : (⟨ X, Y ⟩ : Ω → S × T) ω = (X ω, Y ω) := rfl
