import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.Real

open Function MeasureTheory Measure

namespace ProbabilityTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Ω'] [MeasurableSingletonClass Ω'] {s t : Set Ω} {x : Ω}

lemma uniformOn_apply_singleton_of_mem (hx : x ∈ s) (hs : s.Finite) :
    uniformOn s {x} = 1 / Nat.card s := by
  have : {x} ∩ s = {x} := by ext y; simp (config := {contextual := true}) [hx]
  simp only [uniformOn, cond, Measure.smul_apply, MeasurableSet.singleton, Measure.restrict_apply,
    this, Measure.count_singleton', smul_eq_mul, mul_one, one_div, inv_inj]
  rw [Measure.count_apply_finite _ hs, Nat.card_eq_card_finite_toFinset hs]

lemma real_uniformOn_apply_singleton_of_mem (hx : x ∈ s) (hs : s.Finite) :
    (uniformOn s).real {x} = 1 / Nat.card s := by
  simp [measureReal_def, uniformOn_apply_singleton_of_mem hx hs]

lemma uniformOn_apply_singleton_of_not_mem (hx : x ∉ s) : uniformOn s {x} = 0 := by
  simp [uniformOn, cond, hx]

lemma real_uniformOn_apply_singleton_of_not_mem (hx : x ∉ s) :
    (uniformOn s).real {x} = 0 := by
  simp [measureReal_def, uniformOn_apply_singleton_of_not_mem hx]

theorem uniformOn_apply_eq_zero (hst : s ∩ t = ∅) : uniformOn s t = 0 := by
  rcases Set.finite_or_infinite s with hs | hs
  · exact (uniformOn_eq_zero_iff hs).mpr hst
  · simp [uniformOn, cond, Measure.count_apply_infinite hs]

lemma uniformOn_of_infinite (hs : s.Infinite) : uniformOn s = 0 := by simp [hs]

lemma uniformOn_apply (hs : s.Finite) (t : Set Ω) :
    uniformOn s t = (Nat.card ↑(s ∩ t)) / Nat.card s := by
  rw [uniformOn, cond_apply hs.measurableSet, count_apply_finite _ hs,
    count_apply_finite _ (hs.inter_of_left _), ← Nat.card_eq_card_finite_toFinset,
    ← Nat.card_eq_card_finite_toFinset, ENNReal.div_eq_inv_mul]

instance uniformOn.instIsProbabilityMeasure [Nonempty s] [Finite s] :
    IsProbabilityMeasure (uniformOn s) := uniformOn_isProbabilityMeasure ‹_› .of_subtype

lemma map_uniformOn_apply {f : Ω → Ω'} (hmes : Measurable f) (hf : Injective f) {t : Set Ω'}
    (ht : MeasurableSet t) :
    (uniformOn s).map f t = uniformOn (f '' s) t := by
  obtain hs | hs := s.infinite_or_finite
  · simp [uniformOn_of_infinite, hs, hs.image hf.injOn]
  · rw [map_apply hmes ht, uniformOn_apply hs, uniformOn_apply (hs.image _),
      Nat.card_image_of_injective hf, ← Nat.card_image_of_injective hf, Set.image_inter_preimage]

lemma map_uniformOn {f : Ω → Ω'} (hmes : Measurable f) (hf : Injective f) :
    (uniformOn s).map f = uniformOn (f '' s) := by
  ext t ht
  exact map_uniformOn_apply hmes hf ht

end ProbabilityTheory
