import PFR.entropy_basic
import PFR.f2_vec
import PFR.ruzsa_distance
import PFR.tau_functional

/-!
# Entropic version of polynomial Freiman-Ruzsa conjecture

Here we prove the entropic version of the polynomial Freiman-Ruzsa conjecture.

## Main results

* `entropic_PFR_conjecture`: For two $G$-valued random variables $X^0_1, X^0_2$, there is some subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 11 d[X^0_1;X^0_2]$.

-/

open MeasureTheory ProbabilityTheory

variable (Ω₀₁ Ω₀₂ : Type*) [MeasurableSpace Ω₀₁] [MeasurableSpace Ω₀₂]

variable {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [mΩ' : MeasurableSpace Ω'] (μ' : Measure Ω')

variable [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G]

variable (p : ref_package Ω₀₁ Ω₀₂ G)

/-- If $d[X_1;X_2] > 0$ then  there are $G$-valued random variables $X'_1, X'_2$ such that
$$ \tau[X'_1;X'_2] < \tau[X_1;X_2].$$
Phrased in the contrapositive form for convenience of proof. -/
theorem tau_strictly_decreases (μ₁ μ₂ : Measure G) (h: tau_minimizes p μ₁ μ₂) : d[id ; μ₁ # id ; μ₂]  = 0 := sorry

/-- `entropic_PFR_conjecture`: For two $G$-valued random variables $X^0_1, X^0_2$, there is some subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 11 d[X^0_1;X^0_2]$. -/
theorem entropic_PFR_conjecture :  ∃ H : AddSubgroup G, ∃ Ω : Type*, ∃ mΩ : MeasurableSpace Ω, ∃ U : Ω → G, ∃ μ: Measure Ω, isUniform H U μ ∧ d[p.X₀₁ ; p.μ₀₁ # U ; μ] + d[p.X₀₂ ; p.μ₀₂ # U ; μ] ≤ 11 * d[p.X₀₁ ; p.μ₀₁ # p.X₀₂ ; p.μ₀₂] := by sorry

theorem entropic_PFR_conjecture' :  ∃ H : AddSubgroup G, ∃ Ω : Type*, ∃ mΩ : MeasurableSpace Ω, ∃ U : Ω → G, ∃ μ: Measure Ω, isUniform H U μ ∧ d[p.X₀₁ ; p.μ₀₁ # U ; μ] ≤ 6 * d[p.X₀₁ ; p.μ₀₁ # p.X₀₂ ; p.μ₀₂] ∧ d[p.X₀₂ ; p.μ₀₂ # U ; μ] ≤ 6 * d[p.X₀₁ ; p.μ₀₁ # p.X₀₂ ; p.μ₀₂]   := by sorry
