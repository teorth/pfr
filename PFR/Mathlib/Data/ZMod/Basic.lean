import Mathlib.Data.ZMod.Basic

open Function ZMod

namespace Module
variable {p n : ℕ} {G : Type*} [AddCommGroup G]

section general
variable (n) [Module (ZMod n) G] {x : G}

@[simp]
lemma char_smul_eq_zero_of_zmod (x : G) : n • x = 0 := by simp [← Nat.cast_smul_eq_nsmul (ZMod n)]

@[simp] lemma char_mul_smul_eq_zero_zmod (x : G) (a : ℤ) : (a * n) • x = 0 := by simp [mul_smul]

variable (G)

lemma char_ne_one_of_nontrivial_of_zmod [Nontrivial G] : n ≠ 1 := by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : G)
  exact hx <| by simpa using char_smul_eq_zero_of_zmod 1 x

lemma two_le_char_of_ne_zero [NeZero n] [Nontrivial G] : 2 ≤ n := by
  have := NeZero.ne n
  have := char_ne_one_of_nontrivial_of_zmod n G
  omega

@[simp] lemma periodicPts_add_left_of_zmod [NeZero n] (x : G) : periodicPts (x + ·) = .univ :=
  Set.eq_univ_of_forall fun y ↦ ⟨n, NeZero.pos n, by simpa [IsPeriodicPt] using isFixedPt_id _⟩

instance subgroup [Module (ZMod n) G] (H : AddSubgroup G) : Module (ZMod n) H where
  zero_smul _ := by ext; simp
  add_smul _ _ _ := by ext; simp [add_smul]

end general

section two
variable [Module (ZMod 2) G]

@[simp] lemma add_self (x : G) : x + x = 0 := by
  simpa [-char_smul_eq_zero_of_zmod, two_nsmul] using char_smul_eq_zero_of_zmod 2 x

@[simp] lemma neg_eq_self (x : G) : -x = x := by simp [eq_comm, ← sub_eq_zero]

@[simp] lemma sub_eq_add (x y : G) : x - y = x + y := by simp [sub_eq_add_neg]

lemma add_add_add_cancel (x y z : G) : (x + y) + (y + z) = x + z := by
  simpa using sub_add_sub_cancel x y z

end two
end Module
