import Mathlib.Order.Interval.Finset.Fin

lemma Iio_of_succ_eq_Iic_of_castSucc {N : ℕ} (n: Fin N) : Finset.Iio n.succ = Finset.Iic n.castSucc := rfl
