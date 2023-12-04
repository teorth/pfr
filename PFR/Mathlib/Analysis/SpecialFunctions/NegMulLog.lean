import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PFR.Mathlib.Analysis.Convex.Jensen

/-!
# Entropy function

The purpose of this file is to record basic analytic properties of the function
$$h(x) = - x * \log x$$ on the unit interval, for use in the theory of Shannon entropy.

## Main definitions

* `negMulLog`: the function `x ↦ - x log x`

## Main results

* `sum_negMulLog_le`: a Jensen inequality for `negMulLog`
* `sum_negMulLog_eq`: the equality case of this inequality

-/

open scoped ENNReal NNReal Topology BigOperators

namespace Real

lemma tendsto_log_mul_nhds_zero_left :
    Filter.Tendsto (fun x ↦ log x * x) (𝓝[<] 0) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhds_zero zero_lt_one
  simp only [rpow_one] at h
  have h_eq : ∀ x ∈ Set.Iio 0, (- (fun x ↦ log x * x) ∘ (fun x ↦ |x|)) x = log x * x := by
    intro x hx
    simp only [Set.mem_Iio] at hx
    simp only [Pi.neg_apply, Function.comp_apply, log_abs]
    rw [abs_of_nonpos hx.le]
    simp only [mul_neg, neg_neg]
  refine tendsto_nhdsWithin_congr h_eq ?_
  rw [← neg_zero]
  refine Filter.Tendsto.neg ?_
  simp only [neg_zero]
  refine h.comp ?_
  refine tendsto_abs_nhdsWithin_zero.mono_left ?_
  refine nhdsWithin_mono 0 (fun x hx ↦ ?_)
  simp only [Set.mem_Iio] at hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hx.ne, not_false_eq_true]

lemma continuous_mul_log : Continuous fun x ↦ x * log x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  swap; · exact (continuous_id'.continuousAt).mul (continuousAt_log hx)
  rw [hx]
  have h := tendsto_log_mul_rpow_nhds_zero zero_lt_one
  simp only [rpow_one] at h
  have h' : Filter.Tendsto (fun x ↦ log x * x) (𝓝[<] 0) (𝓝 0) := tendsto_log_mul_nhds_zero_left
  rw [ContinuousAt, zero_mul]
  suffices Filter.Tendsto (fun x ↦ log x * x) (𝓝 0) (𝓝 0) by
    exact this.congr (fun x ↦ by rw [mul_comm])
  nth_rewrite 1 [← nhdsWithin_univ]
  have : (Set.univ : Set ℝ) = Set.Iio 0 ∪ Set.Ioi 0 ∪ {0} := by
    ext x
    simp only [Set.mem_univ, Set.Iio_union_Ioi, Set.union_singleton, Set.mem_compl_iff,
      Set.mem_singleton_iff, not_true, Set.mem_insert_iff, true_iff]
    exact em _
  rw [this, nhdsWithin_union, nhdsWithin_union]
  simp only [ge_iff_le, nhdsWithin_singleton, sup_le_iff, Filter.nonpos_iff, Filter.tendsto_sup]
  refine ⟨⟨h', h⟩, ?_⟩
  rw [Filter.tendsto_pure_left, mul_zero]
  intro s hs
  obtain ⟨t, hts, _, h_zero_mem⟩ := mem_nhds_iff.mp hs
  exact hts h_zero_mem

lemma differentiableOn_id_mul_log : DifferentiableOn ℝ (fun x ↦ x * log x) {0}ᶜ :=
  differentiable_id'.differentiableOn.mul differentiableOn_log

lemma deriv_id_mul_log {x : ℝ} (hx : x ≠ 0) : deriv (fun x ↦ x * log x) x = log x + 1 := by
  rw [deriv_mul differentiableAt_id' (differentiableAt_log hx)]
  simp only [deriv_id'', one_mul, deriv_log', ne_eq, add_right_inj]
  exact mul_inv_cancel hx

lemma deriv2_id_mul_log {x : ℝ} (hx : x ≠ 0) : deriv^[2] (fun x ↦ x * log x) x = x⁻¹ := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp.left_id,
    Function.comp_apply]
  suffices ∀ᶠ y in (𝓝 x), deriv (fun x ↦ x * log x) y = log y + 1 by
    refine (Filter.EventuallyEq.deriv_eq this).trans ?_
    rw [deriv_add_const, deriv_log x]
  suffices ∀ᶠ y in (𝓝 x), y ≠ 0 by
    filter_upwards [this] with y hy
    exact deriv_id_mul_log hy
  exact eventually_ne_nhds hx

lemma strictConvexOn_id_mul_log : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) := by
  refine strictConvexOn_of_deriv2_pos (convex_Ici 0) (continuous_mul_log.continuousOn) ?_
  intro x hx
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
  rw [deriv2_id_mul_log hx.ne']
  positivity

lemma convexOn_id_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) :=
  strictConvexOn_id_mul_log.convexOn

lemma id_mul_log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x * log x :=
  mul_nonneg (zero_le_one.trans hx) (log_nonneg hx)


section negMulLog

/-- The function `x ↦ - x * log x` from `ℝ` to `ℝ`. -/
noncomputable
def negMulLog (x : ℝ) : ℝ := - x * log x

@[simp]
lemma negMulLog_zero : negMulLog (0 : ℝ) = 0 := by simp [negMulLog]

@[simp]
lemma negMulLog_one : negMulLog (1 : ℝ) = 0 := by simp [negMulLog]

lemma negMulLog_eq_neg : negMulLog = fun x ↦ - (x * log x) := by
  funext
  simp [negMulLog]

lemma negMulLog_nonneg {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ negMulLog x := by
  rw [negMulLog, neg_mul_comm]
  apply mul_nonneg h1
  simp only [Left.nonneg_neg_iff]
  exact log_nonpos h1 h2

lemma negMulLog_mul (x y : ℝ) : negMulLog (x * y) = - (y * x * log x + x * y * log y) := by
  simp only [negMulLog, neg_mul, neg_add_rev]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [log_mul hx hy]
  ring

lemma negMulLog_mul' (x y : ℝ) : negMulLog (x * y) = y * negMulLog x + x * negMulLog y := by
  simp_rw [negMulLog_mul, negMulLog]
  ring

lemma concaveOn_negMulLog : ConcaveOn ℝ (Set.Ici (0 : ℝ)) negMulLog := by
  rw [negMulLog_eq_neg]
  exact convexOn_id_mul_log.neg

lemma strictConcaveOn_negMulLog : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) negMulLog := by
  rw [negMulLog_eq_neg]
  exact strictConvexOn_id_mul_log.neg

lemma sum_negMulLog_finset_le {S : Type*} {A : Finset S} {w : S → ℝ} {p : S → ℝ}
    (h0 : ∀ s ∈ A, 0 ≤ w s) (h1 : ∑ s in A, w s = 1) (hmem : ∀ s ∈ A, 0 ≤ p s) :
    ∑ s in A, w s * negMulLog (p s) ≤ negMulLog (∑ s in A, w s * p s) :=
  ConcaveOn.le_map_sum concaveOn_negMulLog h0 h1 hmem

lemma sum_negMulLog_le {S : Type*} [Fintype S] {w : S → ℝ} {p : S → ℝ} (h0 : ∀ s, 0 ≤ w s)
    (h1 : ∑ s, w s = 1) (hmem : ∀ s, 0 ≤ p s) :
    ∑ s, w s * negMulLog (p s) ≤ negMulLog (∑ s, w s * p s) :=
  sum_negMulLog_finset_le (fun s _hs ↦ h0 s) h1 (fun s _hs ↦ hmem s)

-- a form of equality case of Jensen
lemma sum_negMulLog_eq_aux {w : S → ℝ} {p : S → ℝ} {U : Finset S}
    (h0 : ∀ s ∈ U, 0 < w s) (h₁ : ∑ s in U, w s = 1) (hmem : ∀ s ∈ U, 0 ≤ p s) :
    negMulLog (∑ s in U, w s • p s) = ∑ s in U, w s • negMulLog (p s)
    ↔ ∀ j ∈ U, p j = ∑ s in U, w s * p s :=
  strictConcaveOn_negMulLog.map_sum_eq_iff h0 h₁ hmem

-- a form of equality case of Jensen
lemma sum_negMulLog_eq_aux2 {w : S → ℝ} {p : S → ℝ} {U : Finset S}
    (h0 : ∀ s ∈ U, 0 < w s) (h1 : ∑ s in U, w s = 1) (hmem : ∀ s ∈ U, 0 ≤ p s) :
    ∑ s in U, w s * negMulLog (p s) = negMulLog (∑ s in U, w s * p s)
    ↔ ∀ j ∈ U, p j = ∑ s in U, w s * p s := by
  rw [eq_comm]
  exact strictConcaveOn_negMulLog.map_sum_eq_iff h0 h1 hmem

-- a form of equality case of Jensen
lemma sum_negMulLog_eq_aux3 {S : Type*} [Fintype S] {w : S → ℝ} {p : S → ℝ} (h0 : ∀ s, 0 ≤ w s)
    (h1 : ∑ s, w s = 1) (hmem : ∀ s, 0 ≤ p s) :
    ∑ s, w s * negMulLog (p s) = negMulLog (∑ s, w s * p s)
      ↔ ∀ s, w s = 0 ∨ p s = ∑ s', w s' * p s' := by
  rw [eq_comm]
  exact strictConcaveOn_negMulLog.map_sum_eq_iff' h0 h1 hmem

/-- The equality case of Jensen's inequality -/
lemma sum_negMulLog_eq {S : Type*} [Fintype S] {w : S → ℝ} {p : S → ℝ} (h0 : ∀ s, 0 ≤ w s)
    (h1 : ∑ s, w s = 1) (hmem : ∀ s, 0 ≤ p s)
    (heq : ∑ s, w s * negMulLog (p s) = negMulLog (∑ s, w s * p s))
    (s : S) (hs : 0 < w s) : p s = ∑ s', (w s') * (p s') :=
  ((sum_negMulLog_eq_aux3 h0 h1 hmem).1 heq s).resolve_left hs.ne'

lemma continuous_negMulLog : Continuous negMulLog := by
  change Continuous fun x ↦ - x * Real.log x
  simp_rw [neg_mul]
  exact continuous_mul_log.neg

end negMulLog
end Real
