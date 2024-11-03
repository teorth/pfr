import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Entropy function

The purpose of this file is to record basic analytic properties of the function
$$h(x) = - x * \log x$$ on the unit interval, for use in the theory of Shannon entropy.

## Main results

* `sum_negMulLog_le`: a Jensen inequality for `negMulLog`
* `sum_negMulLog_eq`: the equality case of this inequality

-/

open scoped ENNReal NNReal Topology

namespace Real
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {p : ι → ℝ}

/-- If $S$ is a finite set, and $a_s$, $b_s$ are non-negative for $s\in S$, then
  $$\sum_{s\in S} a_s \log\frac{a_s}{b_s}\ge
    \left(\sum_{s\in S}a_s\right)\log\frac{\sum_{s\in S} a_s}{\sum_{s\in S} b_s}$$.
  We require additionally that, if $b_s=0$, then $s_s=0$ as otherwise the right hand side should
  morally be infinite, which it can't be in the formalization using real numbers. -/
lemma sum_mul_log_div_leq {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (habs : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤ ∑ i ∈ s, a i * log (a i / b i) := by
  by_cases h : ∀ i ∈ s, b i = 0
  · have A : ∑ i ∈ s, b i = ∑ i ∈ s, 0 := Finset.sum_congr rfl (fun i hi ↦ h i hi)
    have B : ∑ i ∈ s, a i * log (a i / b i) = ∑ i ∈ s, a i * log (a i / 0) := by
      apply Finset.sum_congr rfl (fun i hi ↦ by simp [h i hi])
    simp [A, B]
  let B := ∑ i ∈ s, b i
  have B_pos : 0 < B := by
    apply Finset.sum_pos' hb
    simp only [not_forall, Classical.not_imp] at h
    rcases h with ⟨i, hi, h'i⟩
    exact ⟨i, hi, lt_of_le_of_ne (hb i hi) (Ne.symm h'i)⟩
  suffices - (∑ i ∈ s, a i * log (a i / b i)) / B ≤
        - ((∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))) / B by
    rwa [div_le_div_right B_pos, neg_le_neg_iff] at this
  have A : ∑ i ∈ s, b i / B = 1 := by
    simpa [← Finset.sum_div] using div_self B_pos.ne'
  have A' : ∀ i ∈ s, 0 ≤ b i / B := fun i hi ↦ div_nonneg (hb i hi) B_pos.le
  have A'' : ∀ i ∈ s, 0 ≤ a i / b i := fun i hi ↦ div_nonneg (ha i hi) (hb i hi)
  convert ConcaveOn.le_map_sum Real.concaveOn_negMulLog A' A (p := fun i ↦ a i / b i) A'' using 1
  · simp only [negMulLog, neg_mul, smul_eq_mul, mul_neg, Finset.sum_neg_distrib]
    rw [neg_div, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl (fun i hi ↦ ?_)
    rcases eq_or_lt_of_le (hb i hi) with h'i | h'i
    · simp [← h'i, habs i hi h'i.symm]
    · field_simp
      ring
  · have : ∑ x ∈ s, b x / B * (a x / b x) = (∑ x ∈ s, a x) / B := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl (fun i hi ↦ ?_)
      rcases eq_or_lt_of_le (hb i hi) with h'i | h'i
      · simp [← h'i, habs i hi h'i.symm]
      · field_simp
        ring
    simp only [negMulLog, smul_eq_mul, neg_mul, this]
    ring

/-- If equality holds in the previous bound, then $a_s=r\cdot b_s$ for every $s\in S$, for some
constant $r\in \mathbb{R}$. Auxiliary version assuming the `b i` are positive. -/
lemma sum_mul_log_div_eq_iff_aux {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i)
    (heq : ∑ i ∈ s, a i * log (a i / b i) = (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))) :
    ∃ r, ∀ i ∈ s, a i = r * (b i) := by
  rcases Finset.eq_empty_or_nonempty s with rfl | h's
  · simp
  let B := ∑ i ∈ s, b i
  have B_pos : 0 < B := Finset.sum_pos hb h's
  suffices ∀ j ∈ s, a j / b j = ∑ i ∈ s, (b i / B) * (a i / b i) by
    refine ⟨∑ i ∈ s, (b i / B) * (a i / b i), fun j hj ↦ ?_⟩
    specialize this j hj
    rwa [div_eq_iff (hb j hj).ne'] at this
  have A : ∑ i ∈ s, b i / B = 1 := by
    simpa [← Finset.sum_div] using div_self B_pos.ne'
  have A' : ∀ i ∈ s, 0 < b i / B := fun i hi ↦ div_pos (hb i hi) B_pos
  have A'' : ∀ i ∈ s, 0 ≤ a i / b i := fun i hi ↦ div_nonneg (ha i hi) (hb i hi).le
  apply (StrictConcaveOn.map_sum_eq_iff Real.strictConcaveOn_negMulLog A' A A'').1
  have : ∑ x ∈ s, b x / B * (a x / b x) = (∑ x ∈ s, a x) / B := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl (fun i hi ↦ ?_)
    have : 0 < b i := hb i hi
    field_simp
    ring
  simp only [negMulLog, smul_eq_mul, this, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_inj]
  rw [← mul_div_right_comm, ← heq, Finset.sum_div]
  apply Finset.sum_congr rfl (fun i hi ↦ ?_)
  have : 0 < b i := hb i hi
  field_simp
  ring

/-- If equality holds in the previous bound, then $a_s=r\cdot b_s$ for every $s\in S$, for some
constant $r\in \mathbb{R}$. -/
lemma sum_mul_log_div_eq_iff {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (habs : ∀ i ∈ s, b i = 0 → a i = 0)
    (heq : ∑ i ∈ s, a i * log (a i / b i)
      = (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))) :
    ∃ r, ∀ i ∈ s, a i = r * (b i) := by
  let s' : Finset ι := s.filter (fun i ↦ 0 < b i)
  have A : ∑ i ∈ s', a i = ∑ i ∈ s, a i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi h'i
    simp only [Finset.mem_filter, hi, true_and, not_lt] at h'i
    exact habs i hi (le_antisymm h'i (hb i hi))
  have B : ∑ i ∈ s', b i = ∑ i ∈ s, b i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi h'i
    simp only [Finset.mem_filter, hi, true_and, not_lt] at h'i
    exact le_antisymm h'i (hb i hi)
  have C : ∑ i ∈ s', a i * log (a i / b i) =
      (∑ i ∈ s', a i) * log ((∑ i ∈ s', a i) / (∑ i ∈ s', b i)) := by
    convert heq using 1
    · apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi h'i
      simp only [Finset.mem_filter, hi, true_and, not_lt] at h'i
      have : b i = 0 := le_antisymm h'i (hb i hi)
      simp [this]
    · simp [A, B]
  obtain ⟨r, hr⟩ : ∃ r, ∀ i ∈ s', a i = r * (b i) := by
    apply sum_mul_log_div_eq_iff_aux (fun i hi ↦ ha i ?_) (fun i hi ↦ ?_) C
    · simp only [Finset.mem_filter, s'] at hi
      exact hi.1
    · simp only [Finset.mem_filter, s'] at hi
      exact hi.2
  refine ⟨r, fun i hi ↦ ?_⟩
  rcases eq_or_lt_of_le (hb i hi) with h'i | h'i
  · simp [← h'i, habs i hi h'i.symm]
  · apply hr
    simp [s', hi, h'i]

end Real
