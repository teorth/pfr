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
