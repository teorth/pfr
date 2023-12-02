import Mathlib.MeasureTheory.Measure.Typeclasses

open Function MeasureTheory Measure

namespace MeasureTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : β → α} {p : α → Prop}
  {μ : Measure α} [IsProbabilityMeasure μ] {s : Set α}

attribute [mk_iff] IsProbabilityMeasure

lemma mem_ae_iff_apply_eq_one (hs : MeasurableSet s) : s ∈ μ.ae ↔ μ s = 1 :=
  mem_ae_iff.trans $ prob_compl_eq_zero_iff hs

lemma ae_iff_apply_eq_one (hp : Measurable p) : (∀ᵐ a ∂μ, p a) ↔ μ {a | p a} = 1 :=
  mem_ae_iff_apply_eq_one hp.setOf

lemma isProbabilityMeasure_comap (hf : Injective f) (hf' : ∀ᵐ a ∂μ, ∃ b, f b = a)
    (hf'' : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) :
    IsProbabilityMeasure (μ.comap f) where
  measure_univ := by
    rw [comap_apply _ hf hf'' _ MeasurableSet.univ,
      ←mem_ae_iff_apply_eq_one (hf'' _ MeasurableSet.univ)]
    simpa
