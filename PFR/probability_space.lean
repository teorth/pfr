import Mathlib

/-! Basic theory of probability spaces. -/

open MeasureTheory

/-- In this project, a ProbabilitySpace is modeled by a MeasureSpace with a finite volume measure that can potentially vanish.  The probability measure is then the normalization of this probability measure, bearing in mind that it may be zero. Thus we also consider a measure space with the zero measure to be a (degenerate) example of a ProbabilitySpace.  This will be convenient when we wish to condition the probability space to an event, because the event may potentially have zero measure. --/
class ProbabilitySpace (Ω : Type*) extends MeasureSpace Ω, IsFiniteMeasure volume

/-- The raw, unnormalized measure.  Would only be directly used in foundational lemmas typically. --/
def ProbabilitySpace.rawMeasure (Ω : Type*) [ProbabilitySpace Ω] : Measure Ω := volume

/-- The raw measure interpreted as a finite measure. Again, only used in foundational lemmas. --/
@[simps (config := .lemmasOnly)]
def ProbabilitySpace.rawFiniteMeasure (Ω : Type*) [ProbabilitySpace Ω] : FiniteMeasure Ω := ⟨volume, inferInstance⟩

/-- The total mass of the raw measure. Can vanish! -/
def ProbabilitySpace.rawMass (Ω : Type*) [ProbabilitySpace Ω] : NNReal := (ProbabilitySpace.rawFiniteMeasure Ω) Set.univ

/-- The assertion that a probability space is nondegenerate (non-zero raw mass). --/
def ProbabilitySpace.isNondeg (Ω : Type*) [ProbabilitySpace Ω] : Prop := 0 < ProbabilitySpace.rawMass Ω

/-- The normalized measure associated to a probability space -/
noncomputable def ProbabilitySpace.measure (Ω : Type*) [ProbabilitySpace Ω] : Measure Ω := (ProbabilitySpace.rawMass Ω)⁻¹ • volume

/-- The normalized finite measure associated to a probability space -/
noncomputable def ProbabilitySpace.finiteMeasure (Ω : Type*) [ProbabilitySpace Ω] : FiniteMeasure Ω := (ProbabilitySpace.rawMass Ω)⁻¹ •(ProbabilitySpace.rawFiniteMeasure Ω)

/-- prob Ω E is the probability of E in Ω. -/
noncomputable def ProbabilitySpace.prob {Ω : Type*} [ProbabilitySpace Ω] (E : Set Ω) := (ProbabilitySpace.finiteMeasure Ω) E

notation:100 "P[ " E " ]" => ProbabilitySpace.prob E

/-- Probability can be computed using ProbabilitySpace.finiteMeasure. --/
lemma ProbabilitySpace.prob_eq [ProbabilitySpace Ω] (E : Set Ω) : P[ E ] = (ProbabilitySpace.finiteMeasure Ω) E := rfl

/-- Probability can also be computed using ProbabilitySpace.measure. --/
lemma ProbabilitySpace.prob_eq' [ProbabilitySpace Ω] (E : Set Ω) : P[ E ] = (ProbabilitySpace.measure Ω) E := by
  unfold ProbabilitySpace.prob ProbabilitySpace.measure ProbabilitySpace.finiteMeasure
  simp
  congr

/-- A silly little lemma on how to cancel in ENNReal - should have a better proof -/
lemma ENNReal_cancel {a : NNReal} (h : a ≠ 0) : 1 / (ENNReal.ofNNReal a) * (ENNReal.ofNNReal a) = 1 := by
  rw [<- inv_eq_one_div, <- ENNReal.div_eq_inv_mul]
  have : ENNReal.toNNReal ((ENNReal.ofNNReal a) / (ENNReal.ofNNReal a)) = ENNReal.toNNReal 1 := by
    rw [ENNReal.toNNReal_div]
    simp
    exact div_self h
  exact (ENNReal.toNNReal_eq_one_iff (↑a / ↑a)).mp this


/-- If nondegenerate, we have a full measure.  Proof is unnecessarily convoluted - would like a slicker proof -/
lemma prob_univ (Ω : Type*) [ProbabilitySpace Ω] (h: ProbabilitySpace.isNondeg Ω) : P[(⊤ : Set Ω)] = 1 := by
  unfold ProbabilitySpace.prob ProbabilitySpace.finiteMeasure ProbabilitySpace.rawMass
  generalize hμ : ProbabilitySpace.rawFiniteMeasure Ω = μ
  dsimp
  push_cast
  rw [show 1 = ENNReal.toNNReal 1 by norm_cast]
  congr
  dsimp [HMul]
  rw [<- MeasureTheory.FiniteMeasure.ennreal_mass]
  unfold ProbabilitySpace.isNondeg at h
  have : FiniteMeasure.mass μ = ProbabilitySpace.rawMass Ω := by
    rw [<- hμ]
    rfl
  rw [this]
  have h' : ProbabilitySpace.rawMass Ω ≠ 0 := by norm_cast; contrapose! h; rw [h]
  field_simp
  apply ENNReal_cancel h'

/-- Degenerate probability measures are zero -/
lemma prob_zero [ProbabilitySpace Ω] (h: ¬ ProbabilitySpace.isNondeg Ω) (E : Set Ω): P[E] = 0 := by
  -- may need to assume E measurable
  sorry
