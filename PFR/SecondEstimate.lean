module

public import PFR.ForMathlib.FourVariables
public import PFR.FirstEstimate

/-!
# Second estimate

The second estimate on tau-minimizers.

Assumptions:

* $X_1, X_2$ are tau-minimizers
* $X_1, X_2, \tilde X_1, \tilde X_2$ be independent random variables, with $X_1,\tilde X_1$ copies
  of $X_1$ and $X_2,\tilde X_2$ copies of $X_2$.
* $d[X_1;X_2] = k$
* $I_1 := I_1 [X_1+X_2 : \tilde X_1 + X_2 | X_1+X_2+\tilde X_1+\tilde X_2]$
* $I_2 := I[X_1+X_2 : X_1 + \tilde X_1 | X_1+X_2+\tilde X_1+\tilde X_2]$

## Main results

* `second_estimate` : $$ I_2 \leq 2 \eta k + \frac{2 \eta (2 \eta k - I_1)}{1 - \eta}.$$
-/

public section

open MeasureTheory Module ProbabilityTheory

variable {G : Type*} [AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [Module (ZMod 2) G] [MeasurableAdd₂ G]

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable (p : refPackage Ω₀₁ Ω₀₂ G)

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (X₁ X₂ X₁' X₂' : Ω → G)
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun ![X₁, X₂, X₁', X₂'])

variable (h_min : tau_minimizes p X₁ X₂)

/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => d[X₁ # X₂]

/-- `I₁ := I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']`, the conditional mutual information
of `X₁ + X₂` and `X₁' + X₂` given the quadruple sum `X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₁" => I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']

/-- `I₂ := I[X₁ + X₂ : X₁' + X₁ | X₁ + X₂ + X₁' + X₂']`, the conditional mutual information
of `X₁ + X₂` and `X₁' + X₁` given the quadruple sum `X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₂" => I[X₁ + X₂ : X₁' + X₁ | X₁ + X₂ + X₁' + X₂']

include h_min hX₁ hX₁' hX₂ hX₂' h_indep h₁ h₂ in
/-- $$ d[X_1+\tilde X_1; X_2+\tilde X_2] \geq k - \frac{\eta}{2} ( d[X_1; X_1] + d[X_2;X_2] ).$$
-/
lemma rdist_of_sums_ge' : d[X₁ + X₁' # X₂ + X₂'] ≥ k - p.η * (d[X₁ # X₁] + d[X₂ # X₂]) / 2 := by
  refine LE.le.ge (LE.le.trans ?_ (distance_ge_of_min p h_min (hX₁.add hX₁') (hX₂.add hX₂')))
  rw [sub_sub, sub_le_sub_iff_left k, ← mul_add,mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith [p.hη])
  have h₁' := condRuzsaDist_diff_le' ℙ p.hmeas1 hX₁ hX₁' (h_indep.indepFun (show 0 ≠ 2 by decide))
  have h₂' := condRuzsaDist_diff_le' ℙ p.hmeas2 hX₂ hX₂' (h_indep.indepFun (show 1 ≠ 3 by decide))
  rw [h₁.entropy_congr, add_sub_cancel_right,
    ← (IdentDistrib.refl hX₁.aemeasurable).rdist_congr h₁] at h₁'
  rw [h₂.entropy_congr, add_sub_cancel_right,
    ← (IdentDistrib.refl hX₂.aemeasurable).rdist_congr h₂] at h₂'
  linarith

include h_min hX₁ hX₁' hX₂ hX₂' h_indep h₁ h₂ in
lemma second_estimate_aux :
    d[X₁ # X₁] + d[X₂ # X₂] ≤ 2 * (k + (2 * p.η * k - I₁) / (1 - p.η)) := by
  have hX₁_indep : IndepFun X₁ X₁' (μ := ℙ) := h_indep.indepFun (show 0 ≠ 2 by decide)
  have hX₂_indep : IndepFun X₂ X₂' (μ := ℙ) := h_indep.indepFun (show 1 ≠ 3 by decide)
  have hX_indep : IndepFun (X₁ + X₁') (X₂ + X₂') := by
    exact h_indep.indepFun_add_add (ι := Fin 4) (by intro i; fin_cases i <;> assumption) 0 2 1 3
      (by decide) (by decide) (by decide) (by decide)
  have h : d[X₁ + X₁' # X₂+ X₂'] ≤ (2 + p.η) * k - (d[X₁# X₁] + d[X₂ # X₂]) / 2 - I₁ := by
    have h := hX_indep.rdist_eq (hX₁.add hX₁') (hX₂.add hX₂')
    rw [ZModModule.sub_eq_add (X₁ + X₁') (X₂ + X₂'), ← ZModModule.sub_eq_add X₁ X₁',
      ← ZModModule.sub_eq_add X₂ X₂',
      sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp (hX₁_indep.rdist_eq hX₁ hX₁').symm),
      sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp (hX₂_indep.rdist_eq hX₂ hX₂').symm),
      ← h₁.entropy_congr, ← h₂.entropy_congr, add_assoc, add_assoc, add_halves, add_halves,
      ← (IdentDistrib.refl hX₁.aemeasurable).rdist_congr h₁,
      ← (IdentDistrib.refl hX₂.aemeasurable).rdist_congr h₂,
      ZModModule.sub_eq_add X₁ X₁', ZModModule.sub_eq_add X₂ X₂', ← add_assoc, add_right_comm _ X₁']
        at h
    have h_indep' : iIndepFun ![X₁, X₂, X₂', X₁'] :=
      by exact h_indep.reindex_four_abdc
    have h' := ent_ofsum_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep' h_min
    convert (h.symm ▸ (sub_le_sub_right (sub_le_sub_right h' _) _)) using 1; ring
  have h' := (rdist_of_sums_ge' p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min).le.trans h
  rw [← div_le_iff₀' two_pos, ← sub_le_iff_le_add', le_div_iff₀ (by linarith [p.hη'])]
  linarith

include h_min hX₁ hX₁' hX₂ hX₂' h_indep h₁ h₂ in
/-- $$ I_2 \leq 2 \eta k + \frac{2 \eta (2 \eta k - I_1)}{1 - \eta}.$$ -/
lemma second_estimate : I₂ ≤ 2 * p.η * k + (2 * p.η * (2 * p.η * k - I₁)) / (1 - p.η) := by
  have hX₁_indep : IndepFun X₁ X₁' (μ := ℙ) := h_indep.indepFun (show 0 ≠ 2 by decide)
  have hX₂_indep : IndepFun X₂ X₂' (μ := ℙ) := h_indep.indepFun (show 1 ≠ 3 by decide)
  let Y : Fin 4 → Ω → G := ![X₂, X₁, X₂', X₁']
  have hY : ∀ i, Measurable (Y i) := fun i => by fin_cases i <;> assumption
  have hY_indep : iIndepFun Y := by exact h_indep.reindex_four_badc
  have h := sum_of_rdist_eq_char_2 Y hY_indep hY
  rw [show Y 0 = X₂ by rfl, show Y 1 = X₁ by rfl, show Y 2 = X₂' by rfl, show Y 3 = X₁' by rfl] at h
  rw [← h₂.rdist_congr h₁, rdist_symm, rdist_symm (X := X₂ + X₂'),
    condRuzsaDist_symm (Z := X₂ + X₂') (W := X₁ + X₁') (hX₂.add hX₂') (hX₁.add hX₁'),
    ← two_mul] at h
  replace h : 2 * k = d[X₁ + X₁' # X₂ + X₂'] + d[X₁ | X₁ + X₁' # X₂ | X₂ + X₂']
      + I[X₁ + X₂ : X₁ + X₁'|X₁ + X₂ + X₁' + X₂'] := by
    convert h using 3 <;> abel
  have h' := condRuzsaDistance_ge_of_min p h_min hX₁ hX₂ (X₁ + X₁') (X₂ + X₂') (hX₁.add hX₁')
    (hX₂.add hX₂')
  have h₁' := condRuzsaDist_diff_le''' ℙ p.hmeas1 hX₁ hX₁' hX₁_indep
  have h₂' := condRuzsaDist_diff_le''' ℙ p.hmeas2 hX₂ hX₂' hX₂_indep
  rw [h₁.entropy_congr, add_sub_cancel_right,
    ← (IdentDistrib.refl hX₁.aemeasurable).rdist_congr h₁] at h₁'
  rw [h₂.entropy_congr, add_sub_cancel_right,
    ← (IdentDistrib.refl hX₂.aemeasurable).rdist_congr h₂] at h₂'
  have h'' : I₂ ≤ p.η * (d[X₁ # X₁] + d[X₂ # X₂]) := by
    simp_rw [← add_comm X₁ X₁']
    have h₁'' := mul_le_mul_of_nonneg_left h₁' (show 0 ≤ p.η by linarith [p.hη])
    have h₂'' := mul_le_mul_of_nonneg_left h₂' (show 0 ≤ p.η by linarith [p.hη])
    have := rdist_of_sums_ge' p _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
    linarith
  nth_rewrite 1 [mul_div_assoc, ← mul_add, mul_assoc, mul_left_comm]
  refine h''.trans (mul_le_mul_of_nonneg_left ?_ (show 0 ≤ p.η by linarith [p.hη]))
  exact second_estimate_aux p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
