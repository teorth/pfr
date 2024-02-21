import Mathlib.Algebra.Group.Basic

variable {G : Type*} [DivisionMonoid G] {a b : G}

lemma eq_of_inv_mul_eq_one (h : a⁻¹ * b = 1) : a = b := by
  simpa using eq_inv_of_mul_eq_one_left h

lemma eq_of_mul_inv_eq_one {G : Type*} [DivisionMonoid G] {a b : G} (h : a * b⁻¹ = 1) : a = b := by
  simpa using eq_inv_of_mul_eq_one_left h
