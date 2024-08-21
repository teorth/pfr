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

/-- Jensen's inequality for the entropy function. -/
lemma sum_negMulLog_le (h₀ : ∀ i ∈ s, 0 ≤ w i) (h₁ : ∑ i in s, w i = 1) (hmem : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i in s, w i * negMulLog (p i) ≤ negMulLog (∑ i in s, w i * p i) :=
  concaveOn_negMulLog.le_map_sum h₀ h₁ hmem

/-- The strict Jensen inequality for the entropy function. -/
lemma sum_negMulLog_lt (h₀ : ∀ i ∈ s, 0 < w i) (h₁ : ∑ i in s, w i = 1) (hmem : ∀ i ∈ s, 0 ≤ p i)
    (hp : ∃ j ∈ s, ∃ k ∈ s, p j ≠ p k) :
    ∑ i in s, w i * negMulLog (p i) < negMulLog (∑ i in s, w i * p i) :=
  strictConcaveOn_negMulLog.lt_map_sum h₀ h₁ hmem hp

/-- The equality case of Jensen's inequality for the entropy function. -/
lemma sum_negMulLog_eq_iff (h₀ : ∀ i ∈ s, 0 < w i) (h₁ : ∑ i in s, w i = 1)
    (hmem : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i in s, w i * negMulLog (p i) = negMulLog (∑ i in s, w i * p i) ↔
      ∀ j ∈ s, p j = ∑ i in s, w i * p i :=
  eq_comm.trans $ strictConcaveOn_negMulLog.map_sum_eq_iff h₀ h₁ hmem

/-- The equality case of Jensen's inequality for the entropy function. -/
lemma sum_negMulLog_eq_iff' (h₀ : ∀ i ∈ s, 0 ≤ w i) (h₁ : ∑ i in s, w i = 1)
    (hmem : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i in s, w i * negMulLog (p i) = negMulLog (∑ i in s, w i * p i) ↔
      ∀ j ∈ s, w j ≠ 0 → p j = ∑ i in s, w i * p i :=
  eq_comm.trans $ strictConcaveOn_negMulLog.map_sum_eq_iff' h₀ h₁ hmem

/-- If $S$ is a finite set, and $a_s,b_s$ are non-negative for $s\in S$, then
  $$\sum_{s\in S} a_s \log\frac{a_s}{b_s}\ge \left(\sum_{s\in S}a_s\right)\log\frac{\sum_{s\in S} a_s}{\sum_{s\in S} b_s},$$
  with the convention $0\log\frac{0}{b}=0$ for any $b\ge 0$ and $0\log\frac{a}{0}=\infty$ for any $a>0$. -/
lemma sum_mul_log_div_leq {a b : s → ℝ} (ha: ∀ i, 0 ≤ a i) (hb: ∀ i, 0 ≤ b i) :
    ∑ i, (a i) * log (a i / b i) ≤ (∑ i, a i) * log ((∑ i, a i) / (∑ i, b i)) := sorry
-- Note: the conventions mentioned above may not be automatic in the Lean implementation of division and logarithm.

/-- If equality holds in the previous bound, then $a_s=r\cdot b_s$ for every $s\in S$, for some constant $r\in \mathbb{R}$. -/
lemma sum_mul_log_div_eq_iff {a b : s → ℝ} (ha: ∀ i, 0 ≤ a i) (hb: ∀ i, 0 ≤ b i)
    (heq: ∑ i, (a i) * log (a i / b i) = (∑ i, a i) * log ((∑ i, a i) / (∑ i, b i))) :
    ∃ r:ℝ, ∀ i, a i = r * (b i) := sorry
-- Note: there may be degenerate cases to consider

end Real
