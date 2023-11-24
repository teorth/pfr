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

open Pointwise ProbabilityTheory MeasureTheory Real
universe u

namespace ProbabilityTheory

/-- The polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of an elementary abelian
2-group of doubling constant at most $K$, then $A$ can be covered by at most $2K^{12}$ cosets of
a subgroup of cardinality at most $|A|$. -/
theorem PFR_conjecture {G : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G]
    {A : Set G} {K : ℝ} (h₀A : A.Nonempty)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) : ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  have card_AA_pos : (0 : ℝ) < Nat.card (A + A) := by
    have : Nonempty (A + A) := Set.nonempty_coe_sort.mpr (Set.Nonempty.add h₀A h₀A)
    have : Finite (A + A) := by exact Subtype.finite
    simp [Nat.cast_pos, Nat.card_pos_iff]
  have KA_pos : 0 < K ∧ (0 : ℝ) < Nat.card A := by
    have I : ¬ ((Nat.card A : ℝ) < 0) := by simp
    simpa [Nat.cast_pos, I, and_false, or_false] using mul_pos_iff.1 (card_AA_pos.trans_le hA)
  have : MeasurableAdd₂ G := ⟨measurable_of_finite _⟩
  have : MeasurableSub₂ G := ⟨measurable_of_finite _⟩
  rcases exists_isUniform_measureSpace A h₀A with ⟨Ω₀, mΩ₀, U₀, hP₀, U₀meas, U₀unif, U₀mem⟩
  rcases independent_copies_two U₀meas U₀meas with ⟨Ω, mΩ, U, U', hP, hU, hU', UU'_indep, idU, idU'⟩
  have Uunif : IsUniform A U := U₀unif.of_identDistrib idU.symm trivial
  have U'unif : IsUniform A U' := U₀unif.of_identDistrib idU'.symm trivial
  have : d[U # U'] ≤ log K := by
    have I : H[U + U'] ≤ log (Nat.card (A + A)) := by
      apply entropy_le_log_card_of_mem (hU.add hU')
      filter_upwards [Uunif.ae_mem, U'unif.ae_mem] with ω h1 h2
      exact Set.add_mem_add h1 h2
    have J : log (Nat.card (A + A)) ≤ log K + log (Nat.card A) := by
      apply (log_le_log' card_AA_pos hA).trans (le_of_eq _)
      rw [log_mul KA_pos.1.ne' KA_pos.2.ne']
    have : H[U + U'] = H[U - U'] := by congr; simp
    rw [UU'_indep.rdist_eq hU hU', Uunif.entropy_eq, U'unif.entropy_eq, ← this]
    linarith
  sorry
