import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.OrderOfElement


/-! The objective of this project is to prove the PFR conjecture, see PFR_conjecture below.
-/

open Pointwise Nat

class ElementaryAddGroup (G : Type*) [AddGroup G] (p : outParam ℕ) where
  orderOf_of_ne {x : G} (hx : x ≠ 0) : addOrderOf x = p
-- may want to change this to p . x = 0 for all x; may also want to enforce finiteness.

theorem PFR_conjecture {G : Type*} [AddCommGroup G] [ElementaryAddGroup G 2] [Fintype G]
    [DecidableEq G] {A : Set G} {K : ℝ} (h₀A : A.Nonempty)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) : ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  sorry
