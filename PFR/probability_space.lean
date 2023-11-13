import Mathlib

/-! Basic theory of probability spaces. -/

open MeasureTheory

/-- In this project, a ProbabilitySpace is modeled by a MeasureSpace with a finite volume measure that can potentially vanish.  The probability measure is then the normalization of this probability measure, bearing in mind that it may be zero. Thus we also consider a measure space with the zero measure to be a (degenerate) example of a ProbabilitySpace-/
class ProbabilitySpace (Ω : Type*) extends MeasureSpace Ω, IsFiniteMeasure volume

/-- The raw, unnormalized measure.  Would only be directly used in foundational lemmas typically. --/
def ProbabilitySpace.rawMeasure (Ω : Type*) [ProbabilitySpace Ω] : Measure Ω := volume

/-- The raw measure interpreted as a finite measure. Again, only used in foundational lemmas. --/
@[simps (config := .lemmasOnly)]
def ProbabilitySpace.rawFiniteMeasure (Ω : Type*) [ProbabilitySpace Ω] : FiniteMeasure Ω := ⟨volume, inferInstance⟩

/-- The total mass of the raw measure. -/
def ProbabilitySpace.rawMass (Ω : Type*) [ProbabilitySpace Ω] : NNReal := (ProbabilitySpace.rawFiniteMeasure Ω) Set.univ

/-- The assertion that a probability space is nondegenerate. --/
def ProbabilitySpace.isNondeg (Ω : Type*) [ProbabilitySpace Ω] : Prop := 0 < ProbabilitySpace.rawMass Ω

/-- The normalized measure associated to a probability space -/
noncomputable def ProbabilitySpace.measure (Ω : Type*) [ProbabilitySpace Ω] : Measure Ω := (ProbabilitySpace.rawMass Ω)⁻¹ • volume

/-- The normalized finite measure associated to a probability space -/
noncomputable def ProbabilitySpace.finiteMeasure (Ω : Type*) [ProbabilitySpace Ω] : FiniteMeasure Ω := (ProbabilitySpace.rawMass Ω)⁻¹ •(ProbabilitySpace.rawFiniteMeasure Ω)

/-- prob Ω E is the probability of E in Ω. -/
noncomputable def ProbabilitySpace.prob {Ω : Type*} [ProbabilitySpace Ω] (E : Set Ω) := (ProbabilitySpace.finiteMeasure Ω) E

notation:100 "P[ " E " ]" => ProbabilitySpace.prob E
