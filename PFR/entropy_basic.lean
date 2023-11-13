import Mathlib
import Pfr.probability_space
import Pfr.neg_xlogx


/-- The purpose of this file is to develop the basic theory of Shannon entropy. -/

/- In this file, inversion will always mean inversion of real numbers. -/
local macro_rules | `($x ⁻¹)   => `(Inv.inv ($x : ℝ))

open Real
open BigOperators

/-- The entropy of a random variable. -/
noncomputable def entropy {Ω : Type*} [ProbSpace Ω] [Fintype S] (X : Ω → S) := ∑ s : S, h ( P[ X ⁻¹' {s} ] )

notation:100 "H[ " X " ]" => entropy X

/-- Entropy is non-negative --/
lemma entropy_nonneg [ProbSpace Ω] [Fintype S] (X : Ω → S) : 0 ≤ H[ X ] := by
  unfold entropy
  apply Finset.sum_nonneg
  intro s _
  apply h_nonneg
  . simp
  apply prob_le_one

/-- The Jensen bound --/
lemma entropy_le_log [ProbSpace Ω] [Fintype S] {X : Ω → S} (hX : Measurable X): H[ X ] ≤ log (Fintype.card S) := by
  set N := Fintype.card S
  have : 0 < N := range_nonempty' hX
  unfold entropy
  have hN : log N = N * h (∑ s : S, N⁻¹ * P[ X ⁻¹' {s} ]) := by
    rw [<-Finset.mul_sum]
    norm_cast
    rw [totalProb hX]
    simp
    unfold h
    rw [log_inv]
    field_simp; ring
  rw [hN, <- inv_mul_le_iff, Finset.mul_sum]
  set w := fun _ : S ↦ N⁻¹
  set p := fun s : S ↦ (P[ X ⁻¹' {s} ] : ℝ)

  conv =>
    congr
    . congr; rfl
      ext s
      rw [(show N⁻¹ = w s by simp), (show P[ X ⁻¹' {s} ] = p s by simp)]
    congr; congr; rfl
    ext s
    rw [(show N⁻¹ = w s by simp), (show P[ X ⁻¹' {s} ] = p s by simp)]
  have hf := h_concave
  have h0 : ∀ s ∈ Finset.univ, 0 ≤ w s := by intros; simp
  have h1 : ∑ s in Finset.univ, w s = 1 := by
    simp
    apply mul_inv_cancel
    positivity
  have hmem : ∀ s ∈ Finset.univ, p s ∈ (Set.Icc 0 1) := by
    intro s _
    simp
    norm_cast
    exact prob_le_one (X ⁻¹' {s})
  convert (ConcaveOn.le_map_sum hf h0 h1 hmem)
  positivity

/-- Equality in Jensen is attained when X is uniform.  TODO: also establish converse -/
lemma entropy_of_uniform [ProbSpace Ω] [Fintype S] {X : Ω → S} (hX : isUniform X) : H[ X ] = log (Fintype.card S) := by
  rcases hX with ⟨ hX1, hX2 ⟩
  unfold entropy
  conv =>
    lhs; congr; rfl; ext s
    rw [hX2 s]
  simp [h]
  have := range_nonempty' hX1
  field_simp
  rw [mul_comm]
  congr
