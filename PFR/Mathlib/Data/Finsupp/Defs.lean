import Mathlib.Data.Finsupp.Defs

open Function

namespace Finsupp

/-- `Finsupp.mapRange` of a surjective function is surjective. -/
lemma mapRange_surjective {α M N : Type*} [Zero M] [Zero N] (f : M → N) (hf : f 0 = 0)
    (hs : Surjective f) : Surjective (Finsupp.mapRange (α := α) f hf) := by
  classical
  let g (n : N) : M := if n = 0 then 0 else surjInv hs n
  have : RightInverse g f := by
    intro n
    by_cases h : n = 0
    · simp [g, h, hf]
    · simp [g, h, surjInv_eq hs n]
  have hg : g 0 = 0 := by simp [g]
  have hfg : (f ∘ g) 0 = 0 := by simp [hf, hg]
  intro F
  use Finsupp.mapRange g hg F
  rw [← Finsupp.mapRange_comp (h := hfg)]
  convert Finsupp.mapRange_id F
  convert this.id

end Finsupp
