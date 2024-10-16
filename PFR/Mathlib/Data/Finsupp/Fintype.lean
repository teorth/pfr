import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Fintype.BigOperators

variable {ι π : Type*} [DecidableEq ι] [Zero π] [Fintype ι] [Fintype π]

variable (ι π) in
@[simp] lemma Fintype.card_finsupp : card (ι →₀ π) = card π ^ card ι := by
  simp [card_congr Finsupp.equivFunOnFinite]
