import Mathlib.LinearAlgebra.Dimension.Finrank

/-- The dimension of a submodule -/
noncomputable abbrev Submodule.finrank {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) : ℕ := Module.finrank R S
