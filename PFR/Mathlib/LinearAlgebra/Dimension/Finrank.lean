import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable abbrev Submodule.finrank {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) : ℕ := Module.finrank R S
