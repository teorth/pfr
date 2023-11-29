import Mathlib.Probability.Notation
import PFR.main


section PFR

open Pointwise

/-- A self-contained version of the PFR conjecture using only Mathlib definitions. -/
example {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]
    {A : Set G} {K : ℝ} (h₀A : A.Nonempty) (Afin : A.Finite)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  convert PFR_conjecture' h₀A Afin hA
  norm_cast

end PFR



section RealMeasure
-- some examples to showcase real-valued measures in a self-contained fashion?

end RealMeasure

section Kernels
-- some examples to showcase the probability kernel stuff in a self-contained fashion?

end Kernels


section Entropy
-- some examples to showcase Shannon entropy in a self-contained fashion

open MeasureTheory ProbabilityTheory BigOperators

variable {Ω : Type*} [MeasureSpace Ω] [hΩ : IsProbabilityMeasure (ℙ : Measure Ω)]

variable {S : Type*} [Fintype S] [Nonempty S][MeasurableSpace S] [MeasurableSingletonClass S]

variable {T : Type*} [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]

variable {U : Type*} [Fintype U] [Nonempty U][MeasurableSpace U] [MeasurableSingletonClass U]

variable (X : Ω → S) (hX: Measurable X) (Y : Ω → T) (hY: Measurable Y) (Z : Ω → U) (hZ: Measurable Z)

/-- $H[X]$ is the Shannon entropy of $X$. -/
example : H[X] = - ∑ x, ((ℙ: Measure Ω).map X {x}).toReal * Real.log ((ℙ: Measure Ω).map X {x}).toReal := by
  rw [entropy_eq_sum hX ℙ, <-Finset.sum_neg_distrib]
  congr with x
  unfold Real.negIdMulLog
  ring

/-- $\langle X,Y \rangle$ is the random variable formed by pairing $X$ and $Y$. -/

example (ω : Ω) : (⟨X, Y⟩) ω = (X ω, Y ω) := rfl

/-- $H[X|Y]$ is the conditional entropy of $X$ relative to $Y$. -/
example : H[X|Y] = H[⟨ X,Y ⟩] - H[Y] := chain_rule'' ℙ hX hY

/-- $I[X:Y]$ is the mutual information between $X$ and $Y$. -/
example : I[X:Y] = H[X] + H[Y] - H[⟨ X,Y ⟩] := rfl

/-- $I[X:Y|Z]$ is the conditional mutual information between $X$ and $Y$ relative to $Z$. -/
example : I[X:Y|Z] = H[X|Z] + H[Y|Z] - H[⟨ X,Y ⟩|Z] := condMutualInformation_eq hX hY hZ ℙ

/-- Submodularity: conditional information is nonnegative. -/
example : 0 ≤ I[X : Y | Z] := condMutualInformation_nonneg hX hY Z ℙ

/-- Relation between conditional mutual information and conditional independence. -/
example : I[X : Y | Z]  = 0  ↔ condIndepFun X Y Z ℙ := condMutualInformation_eq_zero hX hY hZ


end Entropy


section RuzsaDistance
-- some examples to showcase Ruzsa distance in a self-contained fashion?

end RuzsaDistance


section Finiteness
-- some examples to showcase the Finiteness tactic?

end Finiteness
