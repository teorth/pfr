import Mathlib.Algebra.Order.Archimedean

section

/-- Replace `pow_unbounded_of_one_lt` by this one, which has strictly weaker assumptions (notably,
it applies to `ℕ`). -/
theorem pow_unbounded_of_one_lt' {α : Type*}
   [StrictOrderedSemiring α] [Archimedean α] [ExistsAddOfLE α]
    (x : α) {y : α} (hy1 : 1 < y) : ∃ n : ℕ, x < y ^ n := by
  obtain ⟨c, c_pos, rfl⟩ : ∃ c > 0, 1 + c = y := exists_pos_add_of_lt' hy1
  rw [add_comm]
  exact add_one_pow_unbounded_of_pos _ c_pos

/-- Replace `exists_nat_pow_near` by this one, which has strictly weaker assumptions (notably,
it applies to `ℕ`). -/
theorem exists_nat_pow_near' {α : Type*} [LinearOrderedSemiring α] [Archimedean α] [ExistsAddOfLE α]
    {x : α} {y : α} (hx : 1 ≤ x) (hy : 1 < y) :
    ∃ n : ℕ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
  have h : ∃ n : ℕ, x < y ^ n := pow_unbounded_of_one_lt' _ hy
  classical exact
      let n := Nat.find h
      have hn : x < y ^ n := Nat.find_spec h
      have hnp : 0 < n :=
        pos_iff_ne_zero.2 fun hn0 => by rw [hn0, pow_zero] at hn; exact not_le_of_gt hn hx
      have hnsp : Nat.pred n + 1 = n := Nat.succ_pred_eq_of_pos hnp
      have hltn : Nat.pred n < n := Nat.pred_lt (ne_of_gt hnp)
      ⟨Nat.pred n, le_of_not_lt (Nat.find_min h hltn), by rwa [hnsp]⟩

end
