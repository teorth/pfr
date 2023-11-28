import PFR.Entropy.Basic
import PFR.tau_functional
import PFR.f2_vec
import PFR.fibring
import Mathlib.Tactic

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

variable {G : Type u} [addgroup: AddCommGroup G] [Fintype G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [elem: ElementaryAddCommGroup G 2] [MeasurableAdd₂ G]

variable {Ω₀₁ Ω₀₂ : Type u} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable (p : refPackage Ω₀₁ Ω₀₂ G)

variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (X₁ X₂ X₁' X₂' : Ω → G)
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun (fun _i => hG) ![X₁, X₂, X₂', X₁'])

variable (h_min: tau_minimizes p X₁ X₂)

/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => d[X₁ # X₂]

/-- `I₁ := I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']`, the conditional mutual information
of `X₁ + X₂` and `X₁' + X₂` given the quadruple sum `X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₁" => I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']

/-- The sum of
$$ d[X_1+\tilde X_2;X_2+\tilde X_1] + d[X_1|X_1+\tilde X_2; X_2|X_2+\tilde X_1] $$
and
$$ I[ X_1+ X_2 : \tilde X_1 + X_2 \,|\, X_1 + X_2 + \tilde X_1 + \tilde X_2 ] $$
is equal to $2k$. -/
lemma rdist_add_rdist_add_condMutual_eq : d[X₁ + X₂' # X₂ + X₁'] + d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁']
    + I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂'] = 2 * k := by
  have h0 : ![X₁, X₂, X₂', X₁'] 0 = X₁ := rfl
  have h1 : ![X₁, X₂, X₂', X₁'] 1 = X₂ := rfl
  have h2 : ![X₁, X₂, X₂', X₁'] 2 = X₂' := rfl
  have h3 : ![X₁, X₂, X₂', X₁'] 3 = X₁' := rfl
  have h := sum_of_rdist_eq_char_2 ![X₁, X₂, X₂', X₁'] h_indep (fun i => by fin_cases i <;> assumption)
  rw [h0, h1, h2, h3] at h
  have heq : d[X₂' # X₁'] = k
  · rw [rdist_symm]
    apply ProbabilityTheory.IdentDistrib.rdist_eq h₁.symm h₂.symm
  rw[heq] at h
  convert h.symm using 1
  · congr 2 <;> abel
  · ring

/-- The distance $d[X_1+\tilde X_2; X_2+\tilde X_1]$ is at least
$$ k - \eta (d[X^0_1; X_1+\tilde X_2] - d[X^0_1; X_1]) - \eta (d[X^0_2; X_2+\tilde X_1] - d[X^0_2; X_2]).$$ -/
lemma rdist_of_sums_ge :
    d[X₁ + X₂' # X₂ + X₁'] ≥
      k - η * (d[p.X₀₁ # X₁ + X₂'] - d[p.X₀₁ # X₁])
        - η * (d[p.X₀₂ # X₂ + X₁'] - d[p.X₀₂ # X₂]) :=
  distance_ge_of_min _ h_min (hX₁.add hX₂') (hX₂.add hX₁')

/-- The distance $d[X_1|X_1+\tilde X_2; X_2|X_2+\tilde X_1]$ is at least
$$ k - \eta (d[X^0_1; X_1 | X_1 + \tilde X_2] - d[X^0_1; X_1]) - \eta(d[X^0_2; X_2 | X_2 + \tilde X_1] - d[X^0_2; X_2]).$$
-/
lemma cond_rdist_of_sums_ge :
    d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁'] ≥
      k - η * (d[p.X₀₁ # X₁ | X₁ + X₂'] - d[p.X₀₁ # X₁])
        - η * (d[p.X₀₂ # X₂ | X₂ + X₁'] - d[p.X₀₂ # X₂]) :=
  condDistance_ge_of_min _ h_min hX₁ hX₂ _ _ (by measurability) (by measurability)

/-- $$d[X^0_1; X_1+\tilde X_2] - d[X^0_1; X_1] \leq \tfrac{1}{2} k + \tfrac{1}{4} \bbH[X_2] - \tfrac{1}{4} \bbH[X_1].$$ -/
lemma diff_rdist_le_1 : d[p.X₀₁ # X₁ + X₂'] - d[p.X₀₁ # X₁] ≤ k/2 + H[X₂]/4 - H[X₁]/4 := by
  have h : IndepFun X₁ X₂'
  · simpa using h_indep.indepFun (show (0:Fin 4) ≠ 2 by decide)
  convert condDist_diff_le' ℙ p.hmeas1 hX₁ hX₂' h using 4
  · exact ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₂
  · exact h₂.entropy_eq

/-- $$ d[X^0_2;X_2+\tilde X_1] - d[X^0_2; X_2] \leq \tfrac{1}{2} k + \tfrac{1}{4} \mathbb{H}[X_1] - \tfrac{1}{4} \mathbb{H}[X_2].$$ -/
lemma diff_rdist_le_2 : d[p.X₀₂ # X₂ + X₁'] - d[p.X₀₂ # X₂] ≤ k/2 + H[X₁]/4 - H[X₂]/4 := by
  have h : IndepFun X₂ X₁'
  · simpa using h_indep.indepFun (show (1:Fin 4) ≠ 3 by decide)
  convert condDist_diff_le' ℙ p.hmeas2 hX₂ hX₁' h using 4
  · rw [rdist_symm]
    exact ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₂.aemeasurable) h₁
  · exact h₁.entropy_eq

/-- $$ d[X_1^0;X_1|X_1+\tilde X_2] - d[X_1^0;X_1] \leq \tfrac{1}{2} k + \tfrac{1}{4} \mathbb{H}[X_1] - \tfrac{1}{4} \mathbb{H}[X_2].$$ -/
lemma diff_rdist_le_3 : d[p.X₀₁ # X₁ | X₁ + X₂'] - d[p.X₀₁ # X₁] ≤ k/2 + H[X₁]/4 - H[X₂]/4 := by
  have h : IndepFun X₁ X₂'
  · simpa using h_indep.indepFun (show (0:Fin 4) ≠ 2 by decide)
  convert condDist_diff_le''' ℙ p.hmeas1 hX₁ hX₂' h using 3
  · rw[ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₂]
  · apply h₂.entropy_eq

/-- $$ d[X_2^0; X_2|X_2+\tilde X_1] - d[X_2^0; X_2] \leq \tfrac{1}{2}k + \tfrac{1}{4} \mathbb{H}[X_2] - \tfrac{1}{4} \mathbb{H}[X_1].$$ -/
lemma diff_rdist_le_4 : d[p.X₀₂ # X₂ | X₂ + X₁'] - d[p.X₀₂ # X₂] ≤ k/2 + H[X₂]/4 - H[X₁]/4 := by
  have h : IndepFun X₂ X₁'
  · simpa using h_indep.indepFun (show (1:Fin 4) ≠ 3 by decide)
  convert condDist_diff_le''' ℙ p.hmeas2 hX₂ hX₁' h using 3
  · rw[rdist_symm, ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₂.aemeasurable) h₁]
  · apply h₁.entropy_eq

/--  We have $I_1 \leq 2 \eta k$ -/
lemma first_estimate : I₁ ≤ 2 * η * k := by
  have v1 := rdist_add_rdist_add_condMutual_eq X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  have v2 := rdist_of_sums_ge p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_› ‹_›
  have v3 := cond_rdist_of_sums_ge p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› (by measurability) (by measurability)
  have v4 := diff_rdist_le_1 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›
  have v5 := diff_rdist_le_2 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›
  have v6 := diff_rdist_le_3 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›
  have v7 := diff_rdist_le_4 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›
  simp only [η, inv_eq_one_div] at *
  linarith [v1, v2, v3, v4, v5, v6, v7]

/--
$$\mathbb{H}[X_1+X_2+\tilde X_1+\tilde X_2] \le \tfrac{1}{2} \mathbb{H}[X_1]+\tfrac{1}{2} \mathbb{H}[X_2] + (2 + \eta) k - I_1.$$
-/
lemma ent_ofsum_le : H[X₁ + X₂ + X₁' + X₂'] ≤ H[X₁]/2 + H[X₂]/2 + (2+η)*k - I₁ := by
  let D := d[X₁ + X₂' # X₂ + X₁']
  let Dcc := d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁' ]
  let D1 := d[p.X₀₁ # X₁]
  let Dc1 := d[p.X₀₁ # X₁ | X₁ + X₂']
  let D2 := d[p.X₀₂ # X₂]
  let Dc2 := d[p.X₀₂ # X₂ | X₂ + X₁']
  have lem68 : D + Dcc + I₁ = 2 * k :=
    rdist_add_rdist_add_condMutual_eq _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep
  have lem610 : Dcc ≥ k - η * (Dc1 - D1) - η * (Dc2 - D2) :=
    cond_rdist_of_sums_ge p X₁ X₂ X₁' X₂' hX₁ hX₂ (by measurability) (by measurability) h_min
  have lem611c : Dc1 - D1 ≤ k / 2 + H[X₁] / 4 - H[X₂] / 4 :=
    diff_rdist_le_3 p X₁ X₂ X₁' X₂' hX₁ hX₂' h₂ h_indep
  have lem611d : Dc2 - D2 ≤ k / 2 + H[X₂] / 4 - H[X₁] / 4 :=
    diff_rdist_le_4 p X₁ X₂ X₁' X₂' hX₂ hX₁' h₁ h_indep
  have aux : D + I₁ ≤ (1 + η) * k := by
    calc D + I₁
       ≤ k + η * (Dc1 - D1) + η * (Dc2 - D2)                                            := ?_
     _ ≤ k + η * (k / 2 + H[X₁] / 4 - H[X₂] / 4) + η * (k / 2 + H[X₂] / 4 - H[X₁] / 4)  := ?_
     _ = (1 + η) * k                                                                    := by ring
    · convert add_le_add lem68.le (neg_le_neg lem610) using 1 <;> ring
    · refine add_le_add (add_le_add (le_refl _) ?_) ?_
      · apply (mul_le_mul_left (by norm_num [η])).mpr lem611c
      · apply (mul_le_mul_left (by norm_num [η])).mpr lem611d
  have ent_sub_eq_ent_add : H[X₁ + X₂' - (X₂ + X₁')] = H[X₁ + X₂' + (X₂ + X₁')] := by simp
  have rw₁ : X₁ + X₂' + (X₂ + X₁') = X₁ + X₂ + X₁' + X₂' := by abel
  have ind_aux : IndepFun (X₁ + X₂') (X₂ + X₁') := by
    have pairs_indep := iIndepFun.indepFun_prod_prod h_indep
          (fun i ↦ by fin_cases i <;> assumption)
          0 2 1 3 (by decide) (by decide) (by decide) (by decide)
    exact IndepFun.comp (φ := fun gg ↦ gg.1 + gg.2) (ψ := fun gg ↦ gg.1 + gg.2) pairs_indep
              measurable_add measurable_add
  have ind : D = H[X₁ + X₂' - (X₂ + X₁')] - H[X₁ + X₂'] / 2 - H[X₂ + X₁'] / 2 :=
    @IndepFun.rdist_eq Ω G _ ℙ _ _ _ _ (X₁ + X₂') _ (X₂ + X₁') ind_aux (by measurability) (by measurability)
  rw [ind, ent_sub_eq_ent_add, rw₁] at aux
  have obs : H[X₁ + X₂ + X₁' + X₂'] ≤ H[X₁ + X₂'] / 2 + H[X₂ + X₁'] / 2 + (1 + η) * k - I₁ := by
    linarith
  have rw₂ : H[X₁ + X₂'] = k + H[X₁]/2 + H[X₂]/2 := by
    have HX₂_eq : H[X₂] = H[X₂'] :=
      congr_arg (fun (μ : Measure G) ↦ measureEntropy (μ := μ)) h₂.map_eq
    have k_eq : k = H[X₁ - X₂'] - H[X₁] / 2 - H[X₂'] / 2 := by
      have k_eq_aux : k = d[X₁ # X₂'] :=
        IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₂
      rw [k_eq_aux]
      exact IndepFun.rdist_eq (h_indep.indepFun (show (0 : Fin 4) ≠ 2 by decide)) hX₁ hX₂'
    rw [k_eq, ←ElementaryAddCommGroup.sub_eq_add, ←HX₂_eq]
    ring
  have rw₃ : H[X₂ + X₁'] = k + H[X₁]/2 + H[X₂]/2 := by
    have HX₁_eq : H[X₁] = H[X₁'] :=
      congr_arg (fun (μ : Measure G) ↦ measureEntropy (μ := μ)) h₁.map_eq
    have k_eq' : k = H[X₁' - X₂] - H[X₁'] / 2 - H[X₂] / 2 := by
      have k_eq_aux : k = d[X₁' # X₂] :=
        IdentDistrib.rdist_eq h₁ (IdentDistrib.refl hX₂.aemeasurable)
      rw [k_eq_aux]
      exact IndepFun.rdist_eq (h_indep.indepFun (show (3 : Fin 4) ≠ 1 by decide)) hX₁' hX₂
    rw [add_comm X₂ X₁', k_eq', ←ElementaryAddCommGroup.sub_eq_add, ←HX₁_eq]
    ring
  calc H[X₁ + X₂ + X₁' + X₂']
      ≤ H[X₁ + X₂'] / 2 + H[X₂ + X₁'] / 2 + (1 + η) * k - I₁    := obs
    _ = (k + H[X₁] / 2 + H[X₂] / 2) / 2
        + (k + H[X₁] / 2 + H[X₂] / 2) / 2 + (1 + η) * k - I₁    := by rw [rw₂, rw₃]
    _ = H[X₁] / 2 + H[X₂] / 2 + (2 + η) * k - I₁                := by ring
