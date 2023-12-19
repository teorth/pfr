import Mathlib.Data.Fin.VecNotation

namespace Matrix

variable {α : Type*}

variable {m:ℕ}

@[simp]
theorem cons_val_three (x : α) (u : Fin m.succ.succ.succ → α) : vecCons x u 3 = vecHead (vecTail (vecTail u)) :=
  rfl
