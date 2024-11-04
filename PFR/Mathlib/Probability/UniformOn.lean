import Mathlib.Probability.UniformOn


open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

lemma uniformOn_apply_singleton_of_mem [MeasurableSingletonClass Ω]
    {A : Set Ω} {x : Ω} (hx : x ∈ A) (h'A : A.Finite) :
    uniformOn A {x} = 1 / Nat.card A := by
  have : {x} ∩ A = {x} := by ext y; simp (config := {contextual := true}) [hx]
  simp only [uniformOn, cond, Measure.smul_apply, MeasurableSet.singleton, Measure.restrict_apply,
    this, Measure.count_singleton', smul_eq_mul, mul_one, one_div, inv_inj]
  rw [Measure.count_apply_finite _ h'A, Nat.card_eq_card_finite_toFinset h'A]

lemma uniformOn_apply_singleton_of_nmem [MeasurableSingletonClass Ω]
    {A : Set Ω} {x : Ω} (hx : x ∉ A) :
    uniformOn A {x} = 0 := by
  simp [uniformOn, cond, hx]

theorem uniformOn_apply_eq_zero [MeasurableSingletonClass Ω]
    {s t : Set Ω} (hst : s ∩ t = ∅) : uniformOn s t = 0 := by
  rcases Set.finite_or_infinite s with hs | hs
  · exact (uniformOn_eq_zero_iff hs).mpr hst
  · simp [uniformOn, cond, Measure.count_apply_infinite hs]

end ProbabilityTheory
