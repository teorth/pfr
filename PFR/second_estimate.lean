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

It may make sense to merge this file with first_estimate.lean
-/

open MeasureTheory ProbabilityTheory

variable {G : Type u} [addgroup: AddCommGroup G] [Fintype G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [elem: ElementaryAddCommGroup G 2] [MeasurableAdd₂ G]

-- declared in the same universe because `condDist_diff_le'` currently requires that
variable {Ω₀₁ Ω₀₂ : Type u} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable (p : refPackage Ω₀₁ Ω₀₂ G)

-- declared in the same universe as `Ω₀₁` and `Ω₀₂` for the same reason
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (X₁ X₂ X₁' X₂' : Ω → G)
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun ![hG, hG, hG, hG] ![X₁, X₂, X₁', X₂'])

variable (h_min: tau_minimizes p X₁ X₂)

local notation3 "k" => d[X₁ # X₂]

local notation3 "I₁" => I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']

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
lemma second_estimate : I₂ ≤ 2 * η * k + (2 * η * (2 * η * k - I₁)) / (1 - η) := by sorry
