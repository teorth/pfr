import PFR.first_estimate

/-!
# Second estimate

The second estimate on tau-minimizers.

Assumptions:

* $X_1, X_2$ are tau-minimizers
* $X_1, X_2, \tilde X_1, \tilde X_2$ be independent random variables, with $X_1,\tilde X_1$ copies of $X_1$ and $X_2,\tilde X_2$ copies of $X_2$.
* $d[X_1;X_2] = k$
* $I_1 :=  I_1 [ X_1+X_2 : \tilde X_1 + X_2 | X_1+X_2+\tilde X_1+\tilde X_2 ]$
* $I_2 := I[ X_1+X_2 : X_1 + \tilde X_1 | X_1+X_2+\tilde X_1+\tilde X_2 ]$

## Main results

* `second_estimate` : $$ I_2 \leq 2 \eta k + \frac{2 \eta (2 \eta k - I_1)}{1 - \eta}.$$
-/

open MeasureTheory ProbabilityTheory ElementaryAddCommGroup

variable {G : Type*} [addgroup: AddCommGroup G] [Fintype G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [elem: ElementaryAddCommGroup G 2] [MeasurableAdd₂ G]

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable (p : refPackage Ω₀₁ Ω₀₂ G)

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (X₁ X₂ X₁' X₂' : Ω → G)
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun (fun _i => hG) ![X₁, X₂, X₁', X₂'])

variable (h_min: tau_minimizes p X₁ X₂)

/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => d[X₁ # X₂]

/-- `I₁ := I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']`, the conditional mutual information
of `X₁ + X₂` and `X₁' + X₂` given the quadruple sum `X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₁" => I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']

/-- `I₂ := I[X₁ + X₂ : X₁' + X₁ | X₁ + X₂ + X₁' + X₂']`, the conditional mutual information
of `X₁ + X₂` and `X₁' + X₁` given the quadruple sum `X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₂" => I[X₁ + X₂ : X₁' + X₁ | X₁ + X₂ + X₁' + X₂']

/-- $$ d[X_1+\tilde X_1; X_2+\tilde X_2] \geq k - \frac{\eta}{2} ( d[X_1; X_1] + d[X_2;X_2] ).$$
-/
lemma rdist_of_sums_ge' : d[X₁ + X₁' # X₂ + X₂'] ≥ k - η * (d[X₁ # X₁] + d[X₂ # X₂]) / 2 := by
  refine' LE.le.ge (LE.le.trans _ (distance_ge_of_min p h_min (hX₁.add hX₁') (hX₂.add hX₂')))
  rw [sub_sub, sub_le_sub_iff_left k, ← mul_add,mul_div_assoc]
  refine' mul_le_mul_of_nonneg_left _ (by rw [η]; positivity)
  have h₁' := condDist_diff_le' ℙ p.hmeas1 hX₁ hX₁' (h_indep.indepFun (show 0 ≠ 2 by decide))
  have h₂' := condDist_diff_le' ℙ p.hmeas2 hX₂ hX₂' (h_indep.indepFun (show 1 ≠ 3 by decide))
  rw [h₁.entropy_eq, add_sub_cancel, ← (IdentDistrib.refl hX₁.aemeasurable).rdist_eq h₁] at h₁'
  rw [h₂.entropy_eq, add_sub_cancel, ← (IdentDistrib.refl hX₂.aemeasurable).rdist_eq h₂] at h₂'
  linarith

/--  $$ I_2 \leq 2 \eta k + \frac{2 \eta (2 \eta k - I_1)}{1 - \eta}.$$ -/
lemma second_estimate : I₂ ≤ 2 * η * k + (2 * η * (2 * η * k - I₁)) / (1 - η) := by
  have hX₁_indep : IndepFun X₁ X₁' (μ := ℙ) := h_indep.indepFun (show 0 ≠ 2 by decide)
  have hX₂_indep : IndepFun X₂ X₂' (μ := ℙ) := h_indep.indepFun (show 1 ≠ 3 by decide)
  have hX_indep : IndepFun (X₁ + X₁') (X₂ + X₂') := by
    exact h_indep.indepFun_add_add (ι := Fin 4) (by intro i; fin_cases i <;> assumption) 0 2 1 3
      (by decide) (by decide) (by decide) (by decide)
  let Y : Fin 4 → Ω → G := ![X₂, X₁, X₂', X₁']
  have hY : ∀ i, Measurable (Y i) := fun i => by fin_cases i <;> assumption
  have hY_indep : iIndepFun (fun _ => hG) Y := by
    let σ : Fin 4 ≃ Fin 4 := { toFun := ![1, 0, 3, 2], invFun := ![1, 0, 3, 2], left_inv := by intro i; fin_cases i <;> rfl, right_inv := by intro i; fin_cases i <;> rfl }
    refine' iIndepFun.reindex σ _; convert h_indep using 1; ext i; fin_cases i <;> rfl
  have h := sum_of_rdist_eq_char_2 Y hY_indep hY
  rw [show Y 0 = X₂ by rfl, show Y 1 = X₁ by rfl, show Y 2 = X₂' by rfl, show Y 3 = X₁' by rfl] at h
  rw [← h₂.rdist_eq h₁, rdist_symm, rdist_symm (X:= X₂ + X₂'),
    cond_rdist_symm (Z := X₂ + X₂') (W := X₁ + X₁') hX₂ (hX₂.add hX₂') hX₁ (hX₁.add hX₁'),
    add_comm X₂ X₁, add_right_comm _ X₂', ← two_mul] at h
  have h' := condDistance_ge_of_min p h_min hX₁ hX₂ (X₁ + X₁') (X₂ + X₂') (hX₁.add hX₁') (hX₂.add hX₂')
  have h₁' := condDist_diff_le''' ℙ p.hmeas1 hX₁ hX₁' hX₁_indep
  have h₂' := condDist_diff_le''' ℙ p.hmeas2 hX₂ hX₂' hX₂_indep
  rw [h₁.entropy_eq, add_sub_cancel, ← (IdentDistrib.refl hX₁.aemeasurable).rdist_eq h₁] at h₁'
  rw [h₂.entropy_eq, add_sub_cancel, ← (IdentDistrib.refl hX₂.aemeasurable).rdist_eq h₂] at h₂'
  have h'' : I₂ ≤ η * (d[X₁ # X₁] + d[X₂ # X₂]) := by
    rw [← add_comm X₁ X₁']
    have h₁'' := mul_le_mul_of_nonneg_left h₁' (show 0 ≤ η by rw [η]; positivity)
    have h₂'' := mul_le_mul_of_nonneg_left h₂' (show 0 ≤ η by rw [η]; positivity)
    have := rdist_of_sums_ge' p _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
    linarith
  nth_rewrite 1 [mul_div_assoc, ← mul_add, mul_assoc, mul_left_comm]
  refine' h''.trans (mul_le_mul_of_nonneg_left _ (show 0 ≤ η by rw [η]; positivity))
  have h : d[X₁ + X₁' # X₂+ X₂'] ≤ (2 + η) * k - (d[X₁# X₁] + d[X₂ # X₂]) / 2 - I₁ := by
    have h := hX_indep.rdist_eq (hX₁.add hX₁') (hX₂.add hX₂')
    rw [sub_eq_add (X₁ + X₁') (X₂ + X₂'), ← sub_eq_add X₁ X₁', ← sub_eq_add X₂ X₂',
      sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp (hX₁_indep.rdist_eq hX₁ hX₁').symm),
      sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp (hX₂_indep.rdist_eq hX₂ hX₂').symm),
      ← h₁.entropy_eq, ← h₂.entropy_eq, add_assoc, add_assoc, add_halves', add_halves',
      ← (IdentDistrib.refl hX₁.aemeasurable).rdist_eq h₁,
      ← (IdentDistrib.refl hX₂.aemeasurable).rdist_eq h₂,
      sub_eq_add X₁ X₁', sub_eq_add X₂ X₂', ← add_assoc, add_right_comm _ X₁'] at h
    have h_indep' : iIndepFun (fun _i => hG) ![X₁, X₂, X₂', X₁'] := by
      let σ : Fin 4 ≃ Fin 4 := { toFun := ![0, 1, 3, 2], invFun := ![0, 1, 3, 2], left_inv := by intro i; fin_cases i <;> rfl, right_inv := by intro i; fin_cases i <;> rfl }
      refine' iIndepFun.reindex σ.symm _; convert h_indep using 1; ext i; fin_cases i <;> rfl
    have h' := ent_ofsum_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep' h_min
    convert (h.symm ▸ (sub_le_sub_right (sub_le_sub_right h' _) _)) using 1; ring
  have h' := (rdist_of_sums_ge' p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min).le.trans h
  rw [← div_le_iff' two_pos, ← sub_le_iff_le_add', le_div_iff (by rw [η]; positivity)]
  linarith
