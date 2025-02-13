import PFR.Mathlib.Probability.UniformOn
import PFR.ForMathlib.Entropy.Measure
import PFR.ForMathlib.MeasureReal.Defs

open MeasureTheory Measure Real

namespace ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {s t : Set Ω} {x : Ω}

lemma uniformOn_apply' (hs : s.Finite) (t : Set Ω) :
    (uniformOn s).real t = (Nat.card ↑(s ∩ t)) / Nat.card s := by
  simp [measureReal_def, uniformOn_apply hs]

end ProbabilityTheory

namespace ProbabilityTheory

variable {S : Type*} [MeasurableSpace S] (H : Set S) [MeasurableSingletonClass S] [Finite H]

/-- The entropy of a uniform measure is the log of the cardinality of its support. -/
lemma entropy_of_uniformOn [Nonempty H] : measureEntropy (uniformOn H) = log (Nat.card H) := by
  simp only [measureEntropy_def', IsProbabilityMeasure.measureReal_univ, inv_one, Pi.smul_apply,
    uniformOn_apply', Set.toFinite, smul_eq_mul, one_mul]
  classical
  calc ∑' s, negMulLog ((Nat.card (H ∩ {s} : Set S)) / (Nat.card H))
    _ = ∑' s, if s ∈ H then negMulLog (1 / (Nat.card H)) else 0 := by
      congr with s
      by_cases h : s ∈ H <;> simp [h, Finset.filter_true_of_mem, Finset.filter_false_of_mem]
    _ = ∑ s ∈ H.toFinite.toFinset, negMulLog (1 / (Nat.card H)) := by
      convert tsum_eq_sum (s := H.toFinite.toFinset) ?_ using 2 with s hs
      · simp at hs; simp [hs]
      intro s hs
      simp only [Set.Finite.mem_toFinset] at hs; simp [hs]
    _ = (Nat.card H) * negMulLog (1 / (Nat.card H)) := by
      simp [← Set.ncard_coe_Finset, Set.Nat.card_coe_set_eq]
    _ = log (Nat.card H) := by
      simp only [negMulLog, one_div, log_inv, mul_neg, neg_mul, neg_neg, ← mul_assoc]
      rw [mul_inv_cancel₀, one_mul]
      simp only [ne_eq, Nat.cast_eq_zero, Nat.card_ne_zero]
      exact ⟨ ‹_›, ‹_› ⟩
