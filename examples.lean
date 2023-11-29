import Mathlib.Probability.Notation
import PFR.main
import PFR.homomorphism


section PFR

open Pointwise

variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Fintype G]

variable {G' : Type*} [AddCommGroup G'] [Module (ZMod 2) G'] [Fintype G']

/-- A self-contained version of the PFR conjecture using only Mathlib definitions. -/
example {A : Set G} {K : ℝ} (h₀A : A.Nonempty)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  convert PFR_conjecture h₀A hA
  norm_cast

/-- The homomorphism version of PFR. -/
example (f : G → G') (S : Set G') (hS: ∀ x y : G, f (x+y) - (f x) - (f y) ∈ S): ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ 4 * (Nat.card S)^24 ∧ ∀ x : G, (f x) - (φ x) ∈ T := homomorphism_pfr f S hS

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

variable {Ω : Type*} [MeasureSpace Ω] [ IsProbabilityMeasure (ℙ : Measure Ω)]

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
example : I[X : Y | Z]  = 0  ↔ condIndepFun X Y Z := condMutualInformation_eq_zero hX hY hZ


end Entropy


section RuzsaDistance
-- some examples to showcase Ruzsa distance in a self-contained fashion

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [ IsProbabilityMeasure (ℙ : Measure Ω)]

variable {G : Type*} [hG: MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G]
  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Fintype G]

variable (X : Ω → G) (hX: Measurable X) (Y : Ω → G) (hY: Measurable Y) (Z : Ω → G) (hZ: Measurable Z) (X' : Ω → G) (Y' : Ω → G)

/-- `d[X # Y]` is the Ruzsa distance when `X`, `Y` are independent. -/
example (h : IndepFun X Y) : d[X # Y] = H[X-Y] - H[X]/2 - H[Y]/2 := ProbabilityTheory.IndepFun.rdist_eq h hX hY

/-- `d[X # Y]` depends only on the distribution of `X` and `Y`.-/
example (h1: IdentDistrib X X') (h2: IdentDistrib Y Y') : d[X # Y] = d[X' # Y'] := ProbabilityTheory.IdentDistrib.rdist_eq h1 h2

/-- The Ruzsa triangle inequality. -/
example : d[X # Z] ≤ d[X # Y] + d[Y # Z] := rdist_triangle hX hY hZ

/-- The Kaimanovich-Vershik-Madiman inequality -/
example (h : iIndepFun (fun _ ↦ hG) ![X, Y, Z]) : H[X + Y + Z] - H[X + Y] ≤ H[Y + Z] - H[Y] := kaimanovich_vershik h hX hY hZ

/-- The entropic Balog--Szemeredi--Gowers inequality -/
example (h: Z = X+Y) : ((ℙ:Measure Ω).map Z)[fun z ↦ d[ X; ℙ[|Z⁻¹' {z}] # Y ; ℙ[|Z⁻¹' {z}] ]] ≤ 3 * I[ X : Y] + 2 * H[Z] - H[X] - H[Y] := ent_bsg  hX hY h

end RuzsaDistance

section Finiteness
-- some examples to showcase the Finiteness tactic

open ENNReal

example : (1:ℝ≥0∞) < ∞ := by finiteness

example : (3:ℝ≥0∞) ≠ ∞ := by finiteness

example (a : ℝ) (b : ℕ) : ENNReal.ofReal a + b < ∞ := by finiteness

example {a : ℝ≥0∞} (ha : a ≠ ∞) : a + 3 < ∞ := by finiteness
example {a : ℝ≥0∞} (ha : a < ∞) : a + 3 < ∞ := by finiteness

example (a : ℝ) : (ENNReal.ofReal (1 + a ^ 2))⁻¹ < ∞ := by finiteness

example (f : α → ℕ) : ∀ i, (f i : ℝ≥0∞) ≠ ∞ := by finiteness

open MeasureTheory

example {Ω Ω': Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] [MeasurableSpace Ω'] (μ' : Measure Ω') [IsFiniteMeasure μ']  (E: Set (Ω × Ω')): (μ.prod μ') E < ∞ := by finiteness


end Finiteness
