import Mathlib.Data.Fin.Basic

/-- This is neither `Fin.elim0` nor `Fin.elim0'` -/
def Fin.rec0 {α : Fin 0 → Sort*} (i : Fin 0) : α i := absurd i.2 (Nat.not_lt_zero _)
