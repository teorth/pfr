import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin

open Finset

variable {M : Type*} [AddCommMonoid M] {n : ℕ}

-- TODO: Rename `Fin.sum_univ_castSucc` to `Fin.sum_univ_eq_castSucc`
lemma Fin.sum_univ_castSucc' (f : Fin (n + 1) → M) :
    ∑ i : Fin n, f i.castSucc = ∑ i ∈ .Iio (.last _), f i := by
  convert (sum_image (castSucc_injective _).injOn).symm
  refine coe_injective ?_
  ext
  simp [← Fin.lt_last_iff_ne_last, ← Fin.val_fin_lt]
