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

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]

variable (p : refPackage Ω₀₁ Ω₀₂ G)

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (X₁ X₂ X₁' X₂' : Ω → G)

variable (h₁ : IdentDistrib X₁ X₁') (h2 : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun ![hG, hG, hG, hG] ![X₁, X₂, X₁', X₂'])

variable (h_min: tau_minimizes p X₁ X₂)

local notation3 "k" => d[X₁ # X₂]

local notation3 "I₁" => I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']

/-- The sum of
$$ d[X_1+\tilde X_2;X_2+\tilde X_1] + d[X_1|X_1+\tilde X_2; X_2|X_2+\tilde X_1] $$
and
$$ I[ X_1+ X_2 : \tilde X_1 + X_2 \,|\, X_1 + X_2 + \tilde X_1 + \tilde X_2 ] $$
is equal to $2k$. -/
lemma rdist_add_rdist_add_condMutual_eq : d[X₁ + X₂' # X₂ + X₁'] + d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁' ] + I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂'] = 2 * k := by sorry

/-- The distance $d[X_1+\tilde X_2; X_2+\tilde X_1]$ is at least
$$ k - \eta (d[X^0_1; X_1+\tilde X_2] - d[X^0_1; X_1]) \\& \qquad- \eta (d[X^0_2; X_2+\tilde X_1] - d[X^0_2; X_2]).$$ -/
lemma rdist_of_sums_ge : d[X₁ + X₂' # X₂ + X₁'] ≥ k - η * (d[p.X₀₁ # X₁ + X₂'] - d[p.X₀₁ # X₁]) - η * (d[p.X₀₂ # X₂ + X₁'] - d[p.X₀₂ # X₂]) := by sorry

/-- The distance $d[X_1|X_1+\tilde X_2; X_2|X_2+\tilde X_1]$ is at least
$$ k - \eta (d[X^0_1; X_1 | X_1 + \tilde X_2] - d[X^0_1; X_1]) - \eta(d[X^0_2; X_2 | X_2 + \tilde X_1] - d[X^0_2; X_2]).$$
--/
lemma cond_rdist_of_sums_ge : d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁'] ≥ k - η * (d[p.X₀₁ # X₁ | X₁ + X₂'] - d[p.X₀₁ # X₁]) - η * (d[p.X₀₂ # X₂ | X₂ + X₁'] - d[p.X₀₂ # X₂]) := by sorry

/-- $$d[X^0_1; X_1+\tilde X_2] - d[X^0_1; X_1] \leq \tfrac{1}{2} k + \tfrac{1}{4} \bbH[X_2] - \tfrac{1}{4} \bbH[X_1].$$ -/
lemma diff_rdist_le_1 : d[p.X₀₁ # X₁ + X₂'] - d[p.X₀₁ # X₁] ≤ k/2 + H[X₂]/4 - H[X₁]/4 := by sorry

/-- $$ d[X^0_2;X_2+\tilde X_1] - d[X^0_2; X_2] \leq \tfrac{1}{2} k + \tfrac{1}{4} \bbH[X_1] - \tfrac{1}{4} \bbH[X_2].$$ -/
lemma diff_rdist_le_2 : d[p.X₀₂ # X₂ + X₁'] - d[p.X₀₂ # X₂] ≤ k/2 + H[X₁]/4 - H[X₂]/4 := by sorry

/-- $$ d[X_1^0;X_1|X_1+\tilde X_2] - d[X_1^0;X_1] \leq \tfrac{1}{2} k + \tfrac{1}{4} \bbH[X_1] - \tfrac{1}{4} \bbH[X_2].$$ -/
lemma diff_rdist_le_3 : d[p.X₀₁ # X₁ | X₁ + X₂'] - d[p.X₀₁ # X₁] ≤ k/2 + H[X₁]/4 - H[X₂]/4 := by sorry

/-- $$ d[X_2^0; X_2|X_2+\tilde X_1] - d[X_2^0; X_2] &\leq \tfrac{1}{2}k + \tfrac{1}{4} \bbH[X_2] - \tfrac{1}{4} \bbH[X_1].$$ -/
lemma diff_rdist_le_4 : d[p.X₀₂ # X₂ | X₂ + X₁'] - d[p.X₀₂ # X₂] ≤ k/2 + H[X₂]/4 - H[X₁]/4 := by sorry

/--  We have $I_1 \leq 2 \eta k$ -/
lemma first_estimate : I₁ ≤ 2 * η * k := by sorry


/--
$$H[X_1+X_2+\tilde X_1+\tilde X_2] \le \tfrac{1}{2} H[X_1]+\tfrac{1}{2} H[X_2] + (2 + \eta) k - I_1.$$
-/
lemma ent_ofsum_le : H[X₁ + X₂ + X₁' + X₂'] ≤ H[X₁]/2 + H[X₂]/2 + (2+η)*k - I₁ := by sorry
