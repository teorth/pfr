import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[simp] lemma Real.log_div_self (x : ℝ) : log (x / x) = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [hx]
