import Mathlib.MeasureTheory.Measure.Typeclasses

open Function MeasureTheory Measure Set

namespace MeasureTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : β → α} {p : α → Prop}
  {μ : Measure α} [IsProbabilityMeasure μ] {s : Set α}

attribute [mk_iff] IsProbabilityMeasure

lemma mem_ae_iff_apply_eq_one (hs : MeasurableSet s) : s ∈ μ.ae ↔ μ s = 1 :=
  mem_ae_iff.trans $ prob_compl_eq_zero_iff hs

lemma ae_iff_apply_eq_one (hp : Measurable p) : (∀ᵐ a ∂μ, p a) ↔ μ {a | p a} = 1 :=
  mem_ae_iff_apply_eq_one hp.setOf

instance isProbabilityMeasure_map_up [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (μ.map ULift.up) := isProbabilityMeasure_map measurable_up.aemeasurable

instance isProbabilityMeasure_comap_down [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (μ.comap ULift.down) := by
  refine isProbabilityMeasure_comap ?_ ?_ $ by
    rintro s hs
    change MeasurableSet (ULift.down ⁻¹' (ULift.down '' s))
    rwa [Set.preimage_image_eq _ ULift.down_injective]
  all_goals simp [ULift.down_injective]
