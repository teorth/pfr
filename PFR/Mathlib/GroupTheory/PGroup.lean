import Mathlib.GroupTheory.PGroup

namespace ZModModule
variable {n : ℕ} {G : Type*} [AddCommGroup G] [Module (ZMod n) G]

lemma isPGroup_multiplicative : IsPGroup n (Multiplicative G) := by
  simpa [IsPGroup, Multiplicative.forall] using
    fun _ ↦ ⟨1, by simp [← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero]⟩

end ZModModule
