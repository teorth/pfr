module

public import Mathlib.Data.ZMod.Basic

open scoped Pointwise

public section

variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]

namespace Set

lemma sub_eq_add (A : Set G) : A - A = A + A := by
  simp [← Set.image2_add, ← Set.image2_sub, ZModModule.sub_eq_add]

end Set
