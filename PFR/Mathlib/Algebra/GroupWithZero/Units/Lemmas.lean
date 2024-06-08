import Mathlib.Algebra.GroupWithZero.Units.Lemmas

variable {G₀ : Type u_3} [GroupWithZero G₀] {a b c: G₀}

/-- A variant of `eq_mul_inv _iff_mul_eq₀` that moves the nonvanishing hypothesis to another variable. --/
lemma eq_mul_inv_cancel₀' (ha : a ≠ 0) (h:a = b * c⁻¹) : a * c = b := by
  have : c ≠ 0 := by contrapose! h; simp [h, ha]
  rw [eq_mul_inv_iff_mul_eq₀ this] at h; exact h

/-- A variant of `eq_inv_mul_iff_mul_eq₀` that moves the nonvanishing hypothesis to another variable. --/
lemma eq_inv_mul_cancel₀'  (ha : a ≠ 0) (h: a = b⁻¹ * c) : b * a = c := by
  have : b ≠ 0 := by contrapose! h; simp [h, ha]
  rw [eq_inv_mul_iff_mul_eq₀ this] at h; exact h

/-- A variant of `inv_mul_eq_iff_eq_mul₀` that moves the nonvanishing hypothesis to another variable. --/
theorem inv_mul_eq_cancel₀' (hc : c ≠ 0) (h: a⁻¹ * b = c) : b = a * c := by
  have : a ≠ 0 := by contrapose! h; simp [h, hc.symm]
  rw [inv_mul_eq_iff_eq_mul₀ this] at h; exact h

/-- A variant of `mul_inv_eq_iff_eq_mul₀` that moves the nonvanishing hypothesis to another variable. --/
theorem mul_inv__eq_cancel₀' (hc : c ≠ 0) (h: a * b⁻¹ = c) : a = c * b := by
  have : b ≠ 0 := by contrapose! h; simp [h, hc.symm]
  rw [mul_inv_eq_iff_eq_mul₀ this] at h; exact h

/-- A variant of `inv_mul_eq_one₀` that does not require a nonvanishing hypothesis. --/
lemma inv_mul_eq_one₀' {G₀ : Type u_3} [GroupWithZero G₀] {a : G₀} {b : G₀}
(h: a⁻¹ * b = 1) : a = b := by
  have : a ≠ 0 := by contrapose! h; simp [h]
  rw [inv_mul_eq_one₀ this] at h; exact h

/-- A variant of `mul_inv_eq_one₀` that does not require a nonvanishing hypothesis. --/
lemma mul_inv_eq_one₀' {G₀ : Type u_3} [GroupWithZero G₀] {a : G₀} {b : G₀}
(h: a * b⁻¹ = 1) : a = b := by
  have : b ≠ 0 := by contrapose! h; simp [h]
  rw [mul_inv_eq_one₀ this] at h; exact h

/-- A variant of `mul_eq_one_iff_eq_inv₀` that does not require a nonvanishing hypothesis. -/
lemma mul_eq_one_cancel_right (h: a * b = 1) : a = b⁻¹ := by
  have : b ≠ 0 := by contrapose! h; simp [h]
  rw [mul_eq_one_iff_eq_inv₀ this] at h; exact h

/-- A variant of `mul_eq_one_iff_inv_eq₀` that does not require a nonvanishing hypothesis. -/
lemma mul_eq_one_cancel_left (h: a * b = 1) : a⁻¹ = b := by
  have : a ≠ 0 := by contrapose! h; simp [h]
  rw [mul_eq_one_iff_inv_eq₀ this] at h; exact h
