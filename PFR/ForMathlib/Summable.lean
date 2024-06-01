import Mathlib.Topology.Instances.ENNReal

/-- Currently not needed. -/
lemma tsum_eq_toReal_tsum_ofReal {S : Type*} {f : S → ℝ} (hf : ∀ s : S, 0 ≤ f s) : ∑' s, f s = ENNReal.toReal (∑' s, ENNReal.ofReal (f s)) := by
  rw [ENNReal.tsum_toReal_eq]
  . congr with s
    simp [hf s]
  intro s; simp

/-- Currently not needed. -/
lemma tsum_of_not_summable {S : Type*} {f : S → ℝ} (hf : ∀ s : S, 0 ≤ f s) (hsum : ¬ Summable f) : ∑' s, ENNReal.ofReal (f s) = ⊤ := by
  show ∑' s, (Real.toNNReal (f s) : ENNReal) = ⊤
  refine ENNReal.tsum_coe_eq_top_iff_not_summable_coe.mpr ?_
  contrapose! hsum
  convert hsum with s
  simp [hf s]
