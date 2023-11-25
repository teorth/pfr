import PFR.Entropy.Basic
import PFR.tau_functional
import PFR.f2_vec
import PFR.fibring

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

local notation3 "k" => d[X₁ # X₂]

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
$$ k - \eta (d[X^0_1; X_1+\tilde X_2] - d[X^0_1; X_1]) \\& \qquad- \eta (d[X^0_2; X_2+\tilde X_1] - d[X^0_2; X_2]).$$ -/
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
  condDistance_ge_of_min _ h_min hX₁ hX₂ _ _

/-- $$d[X^0_1; X_1+\tilde X_2] - d[X^0_1; X_1] \leq \tfrac{1}{2} k + \tfrac{1}{4} \bbH[X_2] - \tfrac{1}{4} \bbH[X_1].$$ -/
lemma diff_rdist_le_1 : d[p.X₀₁ # X₁ + X₂'] - d[p.X₀₁ # X₁] ≤ k/2 + H[X₂]/4 - H[X₁]/4 := by
  have h : IndepFun X₁ X₂'
  · simpa using h_indep.indepFun (show (0:Fin 4) ≠ 2 by decide)
  convert condDist_diff_le' ℙ p.hmeas1 hX₁ hX₂' h using 4
  · exact ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₂
  · exact h₂.entropy_eq

/-- $$ d[X^0_2;X_2+\tilde X_1] - d[X^0_2; X_2] \leq \tfrac{1}{2} k + \tfrac{1}{4} \bbH[X_1] - \tfrac{1}{4} \bbH[X_2].$$ -/
lemma diff_rdist_le_2 : d[p.X₀₂ # X₂ + X₁'] - d[p.X₀₂ # X₂] ≤ k/2 + H[X₁]/4 - H[X₂]/4 := by
  have h : IndepFun X₂ X₁'
  · simpa using h_indep.indepFun (show (1:Fin 4) ≠ 3 by decide)
  convert condDist_diff_le' ℙ p.hmeas2 hX₂ hX₁' h using 4
  · rw [rdist_symm]
    exact ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₂.aemeasurable) h₁
  · exact h₁.entropy_eq

/-- $$ d[X_1^0;X_1|X_1+\tilde X_2] - d[X_1^0;X_1] \leq \tfrac{1}{2} k + \tfrac{1}{4} \bbH[X_1] - \tfrac{1}{4} \bbH[X_2].$$ -/
lemma diff_rdist_le_3 : d[p.X₀₁ # X₁ | X₁ + X₂'] - d[p.X₀₁ # X₁] ≤ k/2 + H[X₁]/4 - H[X₂]/4 := by
  have h : IndepFun X₁ X₂'
  · simpa using h_indep.indepFun (show (0:Fin 4) ≠ 2 by decide)
  convert condDist_diff_le''' ℙ p.hmeas1 hX₁ hX₂' h using 3
  · rw[ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₂]
  · apply h₂.entropy_eq

/-- $$ d[X_2^0; X_2|X_2+\tilde X_1] - d[X_2^0; X_2] &\leq \tfrac{1}{2}k + \tfrac{1}{4} \bbH[X_2] - \tfrac{1}{4} \bbH[X_1].$$ -/
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
  have v3 := cond_rdist_of_sums_ge p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_›
  have v4 := diff_rdist_le_1 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›
  have v5 := diff_rdist_le_2 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›
  have v6 := diff_rdist_le_3 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›
  have v7 := diff_rdist_le_4 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›
  simp only [η, inv_eq_one_div] at *
  linarith [v1, v2, v3, v4, v5, v6, v7]

lemma identDistrib_prod_of_eq (hindep₁ : IndepFun X₁ X₂) (hindep₂ : IndepFun X₁ X₂') :
IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁,X₂⟩) :=
  { aemeasurable_fst := by measurability
    aemeasurable_snd := by measurability
    map_eq := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map hX₁ hX₂').mp
      (hindep₂), (indepFun_iff_map_prod_eq_prod_map_map hX₁ hX₂).mp (hindep₁), h₂.map_eq] }

/--
$$H[X_1+X_2+\tilde X_1+\tilde X_2] \le \tfrac{1}{2} H[X_1]+\tfrac{1}{2} H[X_2] + (2 + \eta) k - I_1.$$
-/
lemma ent_ofsum_le : H[X₁ + X₂ + X₁' + X₂'] ≤ H[X₁]/2 + H[X₂]/2 + (2+η)*k - I₁ := by
  have hmeas : ∀ (i : Fin 4), Measurable (![X₁, X₂, X₂', X₁'] i)
  | 0 => hX₁
  | 1 => hX₂
  | 2 => hX₂'
  | 3 => hX₁'
  have hφ : Measurable (fun x ↦ (X₁ x, x)) := by exact Measurable.prod hX₁ (measurable_id)
  have := sub_le_sub (cond_rdist_of_sums_ge _ _ _ X₁' X₂' hX₁ hX₂ h_min)
    (le_of_eq $ rdist_add_rdist_add_condMutual_eq _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep)
  have hk : k = H[X₁ - X₂] - H[X₁] / 2 - H[X₂] / 2 :=
  by exact IndepFun.rdist_eq (h_indep.indepFun (show (0 : Fin 4) ≠ 1 by decide)) hX₁ hX₂
  suffices h₃ : d[X₁ + X₂' # X₂ + X₁'] ≤ (1 + η) * k - I₁
  · rw [IndepFun.rdist_eq] at h₃
    simp at h₃
    suffices h₄ : (1 + η) * k - I₁ + H[X₂ + X₁'] / 2 + H[X₁ + X₂'] / 2 = H[X₁] / 2 + H[X₂] / 2 + (2 + η) * k - I₁
    · convert (le_of_le_of_eq h₃ h₄) using 2
      abel
    have hident_sum₁ : IdentDistrib (X₁ + X₂') (X₁ + X₂) := by
      exact (identDistrib_prod_of_eq _ _ _ hX₁ hX₂ hX₂' h₂
      (h_indep.indepFun (show (0:Fin 4) ≠ 1 by decide))
      (h_indep.indepFun (show (0:Fin 4) ≠ 2 by decide))).comp measurable_add
    have hident_sum₂ : IdentDistrib (X₂ + X₁') (X₁ + X₂) := by
      apply ((identDistrib_prod_of_eq _ _ _ hX₂ hX₁' hX₁ h₁.symm
      (h_indep.indepFun (show (1:Fin 4) ≠ 3 by decide))
      (h_indep.indepFun (show (1:Fin 4) ≠ 0 by decide))).comp measurable_add).symm.trans
      apply ProbabilityTheory.IdentDistrib.of_ae_eq (by measurability)
      rw [add_comm]
      rfl
    simp [IdentDistrib.entropy_eq hident_sum₁, IdentDistrib.entropy_eq hident_sum₂, add_mul, add_mul,
      two_mul, one_mul]
    suffices h₅ : H[X₁ + X₂] / 2 + H[X₁ + X₂] / 2 = H[X₁] / 2 + H[X₂] / 2 + k
    · linarith[h₅]
    norm_num [add_halves, hk]
    · exact ((h_indep.indepFun_prod_prod hmeas 0 2 1 3
      (by decide) (by decide) (by decide) (by decide)).comp measurable_add measurable_add)
    · exact (Measurable.add (hmeas 0) (hmeas 2))
    · exact (Measurable.add (hmeas 1) (hmeas 3))
  linarith [this, diff_rdist_le_3 p _ _ _ X₂' hX₂ hX₁' h₁ h_indep]
