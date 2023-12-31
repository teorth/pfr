import PFR.ForMathlib.Entropy.RuzsaDist
import PFR.ForMathlib.MeasureReal



section UniformMeasure

/- Here we set up the foundational theory of discrete uniform measures on finite non-empty sets. -/

open BigOperators

namespace MeasureTheory

variable {S : Type*} [MeasurableSpace S] (H : Set S)

/-- In practice one would also impose the conditions `MeasurableSingletonClass S`, `Finite H` and `Nonempty H` before attempting to use this definition. -/
noncomputable def Measure.discreteUniform : Measure S := (Nat.card H:ENNReal)⁻¹ • (Measure.restrict Measure.count H)

variable [MeasurableSingletonClass S] [Nonempty H] [Finite H]

lemma Measure.discreteUniform_apply (A : Set S) :
  Measure.discreteUniform H A = (Nat.card (A ∩ H : Set S)) / Nat.card H := by sorry

lemma Measure.discreteUniform_apply' (A : Set S) :
  (Measure.discreteUniform H).real A = (Nat.card (A ∩ H : Set S)) / Nat.card H := by sorry

instance Measure.discreteUniform.isProbabilityMeasure  : IsProbabilityMeasure (Measure.discreteUniform H) := by sorry

-- injective map of discrete uniform is discrete uniform

-- relate to IsUniform

end MeasureTheory

end UniformMeasure
