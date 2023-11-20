import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.OrderOfElement
import PFR.f2_vec
import PFR.entropy_pfr

/-!
# Polynomial Freiman-Ruzsa conjecture

Here we prove the polynomial Freiman-Ruzsa conjecture.

-/

open Pointwise Nat

/-- The polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of an elementary abelian 2-group of doubling constant at most $K$, then $A$ can be covered by at most $2K^{12}$ cosets of a subgroup of cardinality at most $|A|$. -/
theorem PFR_conjecture {G : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G]
    [DecidableEq G] {A : Set G} {K : ℝ} (h₀A : A.Nonempty)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) : ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  sorry
