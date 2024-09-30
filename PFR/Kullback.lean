import PFR.ForMathlib.FiniteRange
import Mathlib.Probability.IdentDistrib
import PFR.ForMathlib.Entropy.Basic

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

-- one should add somewhere the hypotheses that μ, μ', and μ'' are all probability measures

/-- If `X, Y` are two `G`-valued random variables, the Kullback--Leibler divergence is defined as
  `KL(X ‖ Y) := ∑ₓ 𝐏(X = x) log(𝐏(X = x) / 𝐏(Y = x))`. -/
noncomputable def KL_div (X : Ω → G) (Y: Ω' → G) (μ: Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac) : ℝ := ∑' x, (μ.map X {x}).toReal * log ((μ.map X {x}).toReal / (μ'.map Y {x}).toReal)

@[inherit_doc KL_div] notation3:max "KL[" X " ; " μ " # " Y " ; " μ' "]" => KL_div X Y μ μ'

@[inherit_doc KL_div] notation3:max "KL[" X " # " Y "]" => KL_div X Y volume volume

/-- If `X'` is a copy of `X`, and `Y'` is a copy of `Y`, then `KL(X' ‖ Y') = KL(X ‖ Y)`. -/
lemma KL_div_eq_of_equiv (X' : Ω'' → G) (Y' : Ω''' → G) (hX : IdentDistrib X X' μ μ'') (hY : IdentDistrib Y Y' μ' μ''') :
  KL[X ; μ # Y ; μ'] = KL[X' ; μ'' # Y' ; μ'''] := sorry

/-- `KL(X ‖ Y) ≥ 0`.-/
lemma KL_div_nonneg : KL[X ; μ # Y ; μ'] ≥ 0 := sorry

/-- `KL(X ‖ Y) = 0` if and only if `Y` is a copy of `X`. -/
lemma KL_div_eq_zero_iff_identDistrib : KL[X ; μ # Y ; μ'] = 0 ↔ IdentDistrib X Y μ μ' := sorry

/-- If $S$ is a finite set, $\sum_{s \in S} w_s = 1$ for some non-negative $w_s$, and ${\bf P}(X=x) = \sum_{s\in S} w_s {\bf P}(X_s=x)$, ${\bf P}(Y=x) = \sum_{s\in S} w_s {\bf P}(Y_s=x)$ for all $x$, then
$$D_{KL}(X\Vert Y) \le \sum_{s\in S} w_s D_{KL}(X_s\Vert Y_s).$$ -/
lemma KL_div_of_convex {I : Type*} {S : Finset I} {w : I → ℝ} (hw: ∀ s, w s ≥ 0) (hsum: ∑ s in S, w s = 1) (X': I → Ω'' → G) (hconvex: ∀ x : G, (μ.map X {x}).toReal = ∑ s in S, (w s) * (μ''.map (X' s) {x}).toReal) : KL[X ; μ # Y ; μ'] ≤ ∑ s in S, w s * KL[X' s ; μ'' # Y ; μ'] := sorry

/-- If $f:G \to H$ is an injection, then $D_{KL}(f(X)\Vert f(Y)) = D_{KL}(X\Vert Y)$. -/
lemma KL_div_of_comp_inj {H : Type*} [MeasurableSpace H] [MeasurableSingletonClass H] {f : G → H} (hf : Function.Injective f) : KL[X ; μ # Y ; μ'] = KL[f ∘ X ; μ # f ∘ Y ; μ'] := sorry

/-- If $X, Y, Z$ are independent $G$-valued random variables, then
  $$D_{KL}(X+Z\Vert Y+Z) \leq D_{KL}(X\Vert Y).$$ -/
lemma KL_div_add_le_KL_div_of_indep [AddCommGroup G] [MeasurableSub₂ G] [MeasurableAdd₂ G] {X Y Z : Ω → G} [FiniteRange X] [FiniteRange Y] [FiniteRange Z] (hindep : iIndepFun (fun _ ↦ hG) ![X, Y, Z] μ) : KL[X + Z ; μ # Y + Z ; μ] ≤ KL[X ; μ # Y ; μ] := sorry

/-- If $X,Y,Z$ are random variables, with $X,Z$ defined on the same sample space, we define
$$ D_{KL}(X|Z \Vert Y) := \sum_z \mathbf{P}(Z=z) D_{KL}( (X|Z=z) \Vert Y).$$ -/
noncomputable def condKL_div {S: Type*} (X: Ω → G) (Y: Ω' → G) (Z: Ω → S) (μ: Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac) : ℝ := ∑' z, (μ (Z⁻¹' {z})).toReal * KL[X ; (ProbabilityTheory.cond μ (Z⁻¹' {z})) # Y ; μ']


@[inherit_doc condKL_div] notation3:max "KL[" X " | " Z " ; " μ " # " Y " ; " μ' "]" => condKL_div X Y Z μ μ'

@[inherit_doc condKL_div] notation3:max "KL[" X " | " Z " # " Y "]" => condKL_div X Y Z volume volume

/-- If $X, Y$ are independent $G$-valued random variables, and $Z$ is another random variable defined on the same sample space as $X$, then
  $$D_{KL}((X|Z)\Vert Y) = D_{KL}(X\Vert Y) + \bbH[X] - \bbH[X|Z].$$ -/
lemma condKL_div_eq {S: Type*} [MeasurableSpace S] (X: Ω → G) (Y: Ω' → G) (Z: Ω → S) (μ: Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac) : KL[ X | Z; μ # Y ; μ'] = KL[X ; μ # Y ; μ'] + H[X ; μ] - H[ X | Z ; μ] := sorry


/-- `KL(X|Z ‖ Y) ≥ 0`.-/
lemma condKL_div_nonneg {S: Type*} (X: Ω → G) (Y: Ω' → G) (Z: Ω → S) (μ: Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac) : KL[X | Z; μ # Y ; μ'] ≥ 0 := sorry
