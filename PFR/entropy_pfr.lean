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
universe u

variable (Ω₀₁ Ω₀₂ : Type*) [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]

variable {Ω Ω' : Type*} [mΩ : MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable {G : Type u} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G]

variable (p : refPackage Ω₀₁ Ω₀₂ G) {X₁ : Ω → G} {X₂ : Ω → G}

/-- If $d[X_1;X_2] > 0$ then  there are $G$-valued random variables $X'_1, X'_2$ such that
Phrased in the contrapositive form for convenience of proof. -/
theorem tau_strictly_decreases (h : tau_minimizes p X₁ X₂) : d[X₁ # X₂] = 0 := sorry

/-- `entropic_PFR_conjecture`: For two $G$-valued random variables $X^0_1, X^0_2$, there is some subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 11 d[X^0_1;X^0_2]$. -/
theorem entropic_PFR_conjecture :
    ∃ H : AddSubgroup G, ∃ Ω : Type u, ∃ mΩ : MeasureSpace Ω, ∃ U : Ω → G,
    isUniform H U ∧ d[p.X₀₁ # U] + d[p.X₀₂ # U] ≤ 11 * d[p.X₀₁ # p.X₀₂] := by sorry

theorem entropic_PFR_conjecture' :
    ∃ H : AddSubgroup G, ∃ Ω : Type u, ∃ mΩ : MeasureSpace Ω, ∃ U : Ω → G,
    isUniform H U ∧ d[p.X₀₁ # U] ≤ 6 * d[p.X₀₁ # p.X₀₂] ∧
      d[p.X₀₂ # U] ≤ 6 * d[p.X₀₁ # p.X₀₂] := by sorry
