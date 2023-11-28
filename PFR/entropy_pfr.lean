import PFR.Entropy.Basic
import PFR.f2_vec
import PFR.ruzsa_distance
import PFR.tau_functional
import PFR.HundredPercent

/-!
# Entropic version of polynomial Freiman-Ruzsa conjecture

Here we prove the entropic version of the polynomial Freiman-Ruzsa conjecture.

## Main results

* `entropic_PFR_conjecture`: For two $G$-valued random variables $X^0_1, X^0_2$, there is some
  subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 11 d[X^0_1;X^0_2]$.

-/

open MeasureTheory ProbabilityTheory
universe u

variable {Ω₀₁ Ω₀₂ : Type u} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]

variable {Ω Ω' : Type u} [mΩ : MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable {G : Type u} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G]

variable (p : refPackage Ω₀₁ Ω₀₂ G) {X₁ : Ω → G} {X₂ : Ω → G}

/-- If $d[X_1;X_2] > 0$ then  there are $G$-valued random variables $X'_1, X'_2$ such that $\tau[X'_1;X'_2] < \tau[X_1;X_2]$.
Phrased in the contrapositive form for convenience of proof. -/
theorem tau_strictly_decreases (h : tau_minimizes p X₁ X₂) : d[X₁ # X₂] = 0 := sorry

/-- `entropic_PFR_conjecture`: For two $G$-valued random variables $X^0_1, X^0_2$, there is some
    subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 11 d[X^0_1;X^0_2]$. -/
theorem entropic_PFR_conjecture :
    ∃ H : AddSubgroup G, ∃ Ω : Type u, ∃ mΩ : MeasureSpace Ω, ∃ U : Ω → G,
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧
    IsUniform H U ∧ d[p.X₀₁ # U] + d[p.X₀₂ # U] ≤ 11 * d[p.X₀₁ # p.X₀₂] := by
  obtain ⟨Ω', mΩ', X₁, X₂, hX₁, hX₂, _, htau_min⟩ := tau_minimizer_exists p
  have hdist : d[X₁ # X₂] = 0 := tau_strictly_decreases p htau_min
  obtain ⟨H, U, hU, hH_unif, hdistX₁, hdistX₂⟩ := exists_isUniform_of_rdist_eq_zero hX₁ hX₂ hdist
  refine ⟨H, Ω', inferInstance, U, inferInstance, hU, hH_unif , ?_⟩
  have h : τ[X₁ # X₂ | p] ≤ τ[p.X₀₂ # p.X₀₁ | p] := is_tau_min p htau_min p.hmeas2 p.hmeas1
  rw [tau, tau, η] at h
  norm_num at h
  have : d[U # X₁] = d[X₁ # U] := rdist_symm
  have : d[U # X₂] = d[X₂ # U] := rdist_symm
  have : d[p.X₀₁ # p.X₀₂ ] = d[p.X₀₂ # p.X₀₁] := rdist_symm
  have : d[p.X₀₁ # U] ≤ d[p.X₀₁ # X₁] + d[X₁ # U] := rdist_triangle _ _ _ p.hmeas1 hX₁ hU
  have : d[p.X₀₂ # U] ≤ d[p.X₀₂ # X₂] + d[X₂ # U] := rdist_triangle _ _ _ p.hmeas2 hX₂ hU
  linarith

theorem entropic_PFR_conjecture' :
    ∃ H : AddSubgroup G, ∃ Ω : Type u, ∃ mΩ : MeasureSpace Ω, ∃ U : Ω → G,
    IsUniform H U ∧ d[p.X₀₁ # U] ≤ 6 * d[p.X₀₁ # p.X₀₂] ∧
      d[p.X₀₂ # U] ≤ 6 * d[p.X₀₁ # p.X₀₂] := by
  have : d[p.X₀₁ # p.X₀₂ ] = d[p.X₀₂ # p.X₀₁] := rdist_symm
  obtain ⟨H, Ω, mΩ, U, H', hU, hUnif, h'⟩ := entropic_PFR_conjecture p
  refine ⟨H, Ω, mΩ, U, hUnif, ?_⟩
  have : d[p.X₀₁ # U] ≤ d[p.X₀₁ # p.X₀₂] + d[p.X₀₂ # U] := rdist_triangle ℙ ℙ ℙ p.hmeas1 p.hmeas2 hU
  have : d[p.X₀₂ # U] ≤ d[p.X₀₂ # p.X₀₁] + d[p.X₀₁ # U] := rdist_triangle ℙ ℙ ℙ p.hmeas2 p.hmeas1 hU
  constructor
  · linarith
  · linarith
