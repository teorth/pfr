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

/-- another silly lemma -/
lemma ENNReal_zero {a: NNReal} (h: ENNReal.toNNReal a = 0) : a = 0 := by
  exact h

/-- If nondegenerate, we have a full measure.  Proof is unnecessarily convoluted - would like a slicker proof -/
@[simp]
lemma ProbabilitySpace.prob_univ (Ω : Type*) [ProbabilitySpace Ω] (h: ProbabilitySpace.isNondeg Ω) : P[(⊤ : Set Ω)] = 1 := by
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
  exact ENNReal_cancel h'

/-- Degenerate probability measures are zero.  Again, a ridiculously convoluted proof; I have a lot of trouble working with ENNReals. -/
@[simp]
lemma ProbabilitySpace.prob_zero [ProbabilitySpace Ω] (h: ¬ ProbabilitySpace.isNondeg Ω) (E : Set Ω): P[E] = 0 := by
  unfold ProbabilitySpace.prob ProbabilitySpace.finiteMeasure ProbabilitySpace.rawMass
  generalize hμ : ProbabilitySpace.rawFiniteMeasure Ω = μ
  dsimp
  push_cast
  rw [show 0 = ENNReal.toNNReal 0 by norm_cast]
  congr
  dsimp [HMul]
  simp; left
  rw [show 0 = ENNReal.toNNReal 0 by norm_cast]
  congr
  unfold ProbabilitySpace.isNondeg at h
  have : ProbabilitySpace.rawMass Ω = 0 := by contrapose! h; exact zero_lt_iff.mpr h
  have h' : ProbabilitySpace.rawMass Ω = FiniteMeasure.mass μ := by
    rw [<- hμ]
    rfl
  rw [h'] at this
  apply_fun ENNReal.ofNNReal at this
  convert this
  unfold FiniteMeasure.mass
  dsimp
  exact (FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure μ Set.univ).symm

/-- Larger events have larger probability. -/
lemma ProbabilitySpace.prob_mono {Ω : Type*} [ProbabilitySpace Ω] {A B : Set Ω} (h : A ≤ B) : P[A] ≤ P[B] := by
  rw [ProbabilitySpace.prob_eq A,ProbabilitySpace.prob_eq B]
  exact FiniteMeasure.apply_mono (ProbabilitySpace.finiteMeasure Ω) h

/-- All events occur with probability at most 1. -/
lemma ProbabilitySpace.prob_le_one [ProbabilitySpace Ω] (E : Set Ω) : P[ E ] ≤ 1 := by
  by_cases h: ProbabilitySpace.isNondeg Ω
  . rw [← ProbabilitySpace.prob_univ Ω h]
    simp [ProbabilitySpace.prob_mono]
  rw [ProbabilitySpace.prob_zero h E]
  norm_num

/-- Give all finite types the discrete sigma-algebra by default. -/
instance Fintype.instMeasurableSpace [Fintype S] : MeasurableSpace S := ⊤

/-- Every finite measure creates a ProbabilitySpace. -/
def ProbabilitySpace.ofFiniteMeasure [MeasurableSpace Ω] (μ : FiniteMeasure Ω) : ProbabilitySpace Ω where
  volume := μ
  measure_univ_lt_top := by
    simp
    exact IsFiniteMeasure.measure_univ_lt_top

open BigOperators

/-- The law of total probability: in a non-degenerate space, the probability densities of a discrete random variable sum to 1. Proof is way too long.  TODO: connect this with Mathlib.Probability.ProbabilityMassFunction.Basic -/
lemma ProbabilitySpace.totalProb {Ω : Type*} [ProbabilitySpace Ω] [Fintype S] (h: ProbabilitySpace.isNondeg Ω) {X : Ω → S} (hX: Measurable X): ∑ s : S, P[ X ⁻¹' {s} ] = 1 := by
  rw [<-ENNReal.coe_eq_coe]
  push_cast
  conv =>
    lhs; congr; rfl; intro s
    rw [ProbabilitySpace.prob_eq']
  rw [<- MeasureTheory.measure_biUnion_finset]
  . rw [<-ProbabilitySpace.prob_eq']
    norm_cast
    convert ProbabilitySpace.prob_univ Ω h
    ext _
    simp
  . dsimp [Set.PairwiseDisjoint, Set.Pairwise,Function.onFun]
    intro x _ y _ hxy
    rw [disjoint_iff]
    contrapose! hxy
    simp at hxy
    have : (X ⁻¹' {x} ∩ X ⁻¹' {y} ).Nonempty := by
      exact Set.nmem_singleton_empty.mp hxy
    rcases this with ⟨ a, ha ⟩
    simp at ha
    rw [<-ha.1, <-ha.2]
  intro s _
  exact hX trivial

/-- In a non-degenerate space, random variables always take values in non-empty sets. -/
lemma ProbabilitySpace.range_nonempty {Ω : Type*} [ProbabilitySpace Ω] (h: ProbabilitySpace.isNondeg Ω) [Fintype S] {X : Ω → S} (hX: Measurable X) : Nonempty S := by
  rcases isEmpty_or_nonempty S with hS | hS
  . have := ProbabilitySpace.totalProb h hX
    simp [hS] at this
  assumption

lemma ProbabilitySpace.range_nonempty' {Ω : Type*} [ProbabilitySpace Ω] (h: ProbabilitySpace.isNondeg Ω) [Fintype S] {X : Ω → S} (hX: Measurable X) : 0 < Fintype.card S := by
  suffices : Fintype.card S ≠ 0
  . contrapose! this; linarith
  have := ProbabilitySpace.range_nonempty h hX
  apply Fintype.card_ne_zero

/-- Definition of a uniform random variable on a set S -/
def ProbabilitySpace.isUniform {Ω : Type*} [ProbabilitySpace Ω] [Fintype S] (X : Ω → S) := (Measurable X) ∧ (∀ s : S, P[ X ⁻¹' {s} ] = ((Fintype.card S) : ℝ)⁻¹)
