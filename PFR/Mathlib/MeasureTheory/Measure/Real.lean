import Mathlib.MeasureTheory.Measure.Real
import PFR.Mathlib.MeasureTheory.Measure.Prod

open Function Set
open scoped ENNReal NNReal

namespace MeasureTheory
variable {α β R Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
  {_ : MeasurableSpace α} {_ : MeasurableSpace β}

lemma Measure.ennreal_smul_real_apply (c : ℝ≥0∞) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c.toReal • μ.real s := by simp

lemma Measure.nnreal_smul_real_apply (c : ℝ≥0) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c • μ.real s := by simp [Measure.real, NNReal.smul_def]

lemma Measure.comap_real_apply {s : Set α} {f : α → β} (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    (comap f μ).real s = μ.real (f '' s) := by simp [Measure.real, comap_apply _ hfi hf μ hs]

lemma Measure.prod_real_singleton (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by
  simp [Measure.real, Measure.prod_apply_singleton]

variable [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ω']

lemma measureReal_preimage_fst_singleton_eq_sum [Fintype Ω'] (μ : Measure (Ω × Ω'))
    [IsFiniteMeasure μ] (x : Ω) :
    μ.real (Prod.fst ⁻¹' {x}) = ∑ y : Ω', μ.real {(x, y)} := by
  rw [measureReal_def, measure_preimage_fst_singleton_eq_sum, ENNReal.toReal_sum]
  · rfl
  intros
  finiteness

lemma measureReal_preimage_snd_singleton_eq_sum [Fintype Ω] (μ : Measure (Ω × Ω'))
    [IsFiniteMeasure μ] (y : Ω') :
    μ.real (Prod.snd ⁻¹' {y}) = ∑ x : Ω, μ.real {(x, y)} := by
  rw [measureReal_def, measure_preimage_snd_singleton_eq_sum, ENNReal.toReal_sum]
  · rfl
  intros
  finiteness

end MeasureTheory
