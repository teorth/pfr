import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.OrderOfElement
import PFR.f2_vec
import PFR.ruzsa_covering
import PFR.entropy_pfr

/-!
# Polynomial Freiman-Ruzsa conjecture

Here we prove the polynomial Freiman-Ruzsa conjecture.

-/

open Pointwise Nat

theorem PFR_conjecture {G : Type*} [AddCommGroup G] [ElementaryAddGroup G 2] [Fintype G]
    [DecidableEq G] {A : Set G} {K : ℝ} (h₀A : A.Nonempty)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) : ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  sorry
