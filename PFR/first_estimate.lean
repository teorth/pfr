import PFR.entropy_basic
import PFR.tau_functional
import PFR.f2_vec

/-!
# First estimate

The first estimate on tau-minimizers.

Assumptions:

* $X_1, X_2$ are tau-minimizers
* $X_1, X_2, \tilde X_1, \tilde X_2$ are independent random variables, with $X_1,\tilde X_1$ copies of $X_1$ and $X_2,\tilde X_2$ copies of $X_2$.
* $k := d[X_1;X_2]$
* $I_1 :=  I [ X_1+X_2 : \tilde X_1 + X_2 | X_1+X_2+\tilde X_1+\tilde X_2 ]$

## Main results

* `first_estimate` : $I_1 ≤ 2 η k$
* `ent_ofsum_le` : $H[X_1+X_2+\tilde X_1+\tilde X_2] \le \tfrac{1}{2} H[X_1]+\tfrac{1}{2} H[X_2] + (2 + \eta) k - I_1.$
-/

open MeasureTheory ProbabilityTheory

variable {G : Type*} [AddCommGroup G] [Fintype G] [hG : MeasurableSpace G] [ElementaryAddCommGroup G 2]

variable {Ω₀₁ Ω₀₂ : Type*} [MeasurableSpace Ω₀₁] [MeasurableSpace Ω₀₂]

variable (p : ref_package Ω₀₁ Ω₀₂ G)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

variable (X₁ X₂ X₁' X₂' : Ω → G)

variable (h₁ : IdentDistrib X₁ X₁' μ μ) (h2 : IdentDistrib X₂ X₂' μ μ)

variable (h_indep : iIndepFun ![hG, hG, hG, hG] ![X₁, X₂, X₁', X₂'] μ)

variable (h_min: tau_minimizes p (μ.map X₁) (μ.map X₂))

local notation3 "k" => d[ X₁; μ # X₂; μ ]

local notation3 "I₁" => I[ X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂' ; μ ]

/--  We have $I_1 \leq 2 \eta k$ -/
lemma first_estimate : I₁ ≤ 2 * η * k := by sorry


/--
$$H[X_1+X_2+\tilde X_1+\tilde X_2] \le \tfrac{1}{2} H[X_1]+\tfrac{1}{2} H[X_2] + (2 + \eta) k - I_1.$$
-/
lemma ent_ofsum_le : H[X₁ + X₂ + X₁' + X₂' ; μ] ≤ H[X₁; μ]/2 + H[X₂; μ]/2 + (2+η)*k - I₁ := by sorry
