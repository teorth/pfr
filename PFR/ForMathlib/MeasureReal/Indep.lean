import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real

open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal

namespace ProbabilityTheory
variable {Ω ι β β' γ : Type*} {κ : ι → Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β}
  {g : Ω → β'}

lemma IndepFun.measureReal_inter_preimage_eq_mul {_mβ : MeasurableSpace β}
    {_mβ' : MeasurableSpace β'} (h : IndepFun f g μ) {s : Set β} {t : Set β'}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ.real (f ⁻¹' s ∩ g ⁻¹' t) = μ.real (f ⁻¹' s) * μ.real (g ⁻¹' t) := by
  rw [measureReal_def, h.measure_inter_preimage_eq_mul _ _ hs ht, ENNReal.toReal_mul]; rfl

end ProbabilityTheory
