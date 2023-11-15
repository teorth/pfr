import PFR.probability_space


/-! This file sets out some basic tools for manipulating random variables.  -/



/-- Some notation for pairing together two random variables that share a common sample space.  This
will be convenient when manipulating Shannon entropy functionals involving two or more variables. -/
def pair {Ω S T : Type*} ( X : Ω → S ) ( Y : Ω → T ) (ω : Ω) : S × T := (X ω, Y ω)

notation:100 "⟨ " X " , " Y " ⟩" => pair X Y

-- note: ⟨ X , ⟨ Y , Z ⟩ ⟩ and ⟨ ⟨ X , Y ⟩ , Z ⟩ are not definitionally equivalent, but there is a
-- canonical bijection relating the two random variables that we may need at some point.  Similarly
-- for ⟨ X , Y ⟩ and ⟨ Y , X ⟩

example {Ω S T : Type*} ( X : Ω → S ) ( Y : Ω → T ) ( Z : Ω → S × T )
    (h : Z = ⟨ X, Y ⟩ ) (ω : Ω) : Z ω = (X ω, Y ω) := by
  rw [h]
  rfl
