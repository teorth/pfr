module

public import Mathlib.Order.Interval.Finset.Fin

public section

open Finset

namespace Fin

lemma Iio_succ_eq_Iic_castSucc {n : ℕ} (k : Fin n) : Iio k.succ = Iic k.castSucc := rfl

end Fin
