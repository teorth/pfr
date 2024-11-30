import Mathlib.SetTheory.Cardinal.Arithmetic

universe u

open Function Set Cardinal Equiv Order Ordinal


/- Put just after `power_nat_eq` -/
theorem power_le_aleph0 {a b : Cardinal.{u}} (ha : a ≤ ℵ₀) (hb : b < ℵ₀) : a ^ b ≤ ℵ₀ := by
  rcases lt_aleph0.1 hb with ⟨n, rfl⟩
  have : a ^ (n : Cardinal.{u}) ≤ ℵ₀ ^ (n : Cardinal.{u}) := power_le_power_right ha
  apply this.trans
  simp only [power_natCast]
  exact power_nat_le le_rfl
