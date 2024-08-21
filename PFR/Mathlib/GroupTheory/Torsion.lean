import Mathlib.GroupTheory.Torsion

lemma AddMonoid.IsTorsionFree.noZeroNsmulDivisors {M : Type*} [AddMonoid M]
    (hM : AddMonoid.IsTorsionFree M) : NoZeroSMulDivisors ℕ M where
  eq_zero_or_eq_zero_of_smul_eq_zero := by
    intro n x h
    by_contra hc
    obtain ⟨h_n0, h_x0⟩ := not_or.mp hc
    exact hM x h_x0 <| isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, Nat.pos_of_ne_zero h_n0, h⟩
