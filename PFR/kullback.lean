import PFR.Mathlib.Analysis.SpecialFunctions.NegMulLog
import PFR.ForMathlib.FiniteRange
import Mathlib.Probability.IdentDistrib

/-!
# Kullback-Leibler divergence

Definition of Kullback-Leibler divergence and basic facts

## Main definitions:


## Main results

-/

open MeasureTheory ProbabilityTheory Real

variable {Ω Ω' Ω'' Ω''' G: Type*}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G] [MeasurableSingletonClass G]

variable {X : Ω → G} {Y : Ω' → G} [FiniteRange X] [FiniteRange Y]

/--  If `X, Y` are two `G`-valued random variables, the Kullback--Leibler divergence is defined as
  `KL(X ‖ Y) := ∑ₓ 𝐏(X = x) log(𝐏(X = x) / 𝐏(Y = x))`. -/
noncomputable def KL_div (X : Ω → G) (Y: Ω' → G) (μ: Measure Ω) (μ' : Measure Ω') : ℝ := ∑' x, (μ.map X {x}).toReal * log ((μ.map X {x}).toReal / (μ'.map Y {x}).toReal)

@[inherit_doc KL_div] notation3:max "KL[" X " ; " μ " # " Y " ; " μ' "]" => KL_div X Y μ μ'

/-- If `X'` is a copy of `X`, and `Y'` is a copy of `Y`, then `KL(X' ‖ Y') = KL(X ‖ Y)`. -/
lemma KL_div_eq_of_equiv (X' : Ω'' → G) (Y' : Ω''' → G) (hX : IdentDistrib X X' μ μ'') (hY : IdentDistrib Y Y' μ' μ''') :
  KL[X ; μ # Y ; μ'] = KL[X' ; μ'' # Y' ; μ'''] := sorry

/-- `KL(X ‖ Y) ≥ 0`.-/
lemma KL_div_nonneg : KL[X ; μ # Y ; μ'] ≥ 0 := sorry

/-- `KL(X ‖ Y) = 0` if and only if `Y` is a copy of `X`. -/
lemma KL_div_eq_zero_iff_identDistrib : KL[X ; μ # Y ; μ'] = 0 ↔ IdentDistrib X Y μ μ' := sorry
