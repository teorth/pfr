import Mathlib
-- to do: be more specific on which part of Mathlib is being imported

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
def ProbabilitySpace.rawMass (Ω : Type*) [ProbabilitySpace Ω] : NNReal := rawFiniteMeasure Ω Set.univ

lemma ProbabilitySpace.rawMeasure_eq (Ω : Type*) [ProbabilitySpace Ω] (E : Set Ω) : rawFiniteMeasure Ω E = rawMeasure Ω E := by
  unfold rawMeasure rawFiniteMeasure
  simp; congr

lemma ProbabilitySpace.rawMass_eq (Ω : Type*) [ProbabilitySpace Ω] : rawMass Ω = rawMeasure Ω Set.univ := by
  apply rawMeasure_eq

/-- The assertion that a probability space is nondegenerate (non-zero raw mass). --/
def ProbabilitySpace.isNondeg (Ω : Type*) [ProbabilitySpace Ω] : Prop := 0 < rawMass Ω

/-- The normalized measure associated to a probability space -/
noncomputable def ProbabilitySpace.measure (Ω : Type*) [ProbabilitySpace Ω] : Measure Ω := (rawMass Ω)⁻¹ • volume

/-- The normalized finite measure associated to a probability space -/
noncomputable def ProbabilitySpace.finiteMeasure (Ω : Type*) [ProbabilitySpace Ω] : FiniteMeasure Ω := (rawMass Ω)⁻¹ • rawFiniteMeasure Ω

/-- P[ E ] is the probability of E. -/
notation:100 "P[ " E " ]" => (ProbabilitySpace.finiteMeasure _) E

/-- An alternate notation where one makes the Probability space X = ‹ ProbabilitySpace Ω › explicit.  -/
notation:100 "P[ " E " ; " X " ]" => (@ProbabilitySpace.finiteMeasure _ X) E

/-- Probability can be computed using ProbabilitySpace.finiteMeasure. --/
lemma ProbabilitySpace.prob_eq [ProbabilitySpace Ω] (E : Set Ω) : P[ E ] = finiteMeasure Ω E := rfl

/-- Probability can also be computed using ProbabilitySpace.measure. --/
lemma ProbabilitySpace.prob_eq' [ProbabilitySpace Ω] (E : Set Ω) : P[ E ] = measure Ω E := by
  unfold measure finiteMeasure
  simp
  congr

lemma ProbabilitySpace.prob_eq'' [ProbabilitySpace Ω] (E : Set Ω) : P[ E ; ‹ ProbabilitySpace Ω› ] = P[ E ] := by rfl

lemma ProbabilitySpace.prob_raw [ProbabilitySpace Ω] (E : Set Ω) : P[ E ] = (rawMass Ω)⁻¹ * rawMeasure Ω E := by
  rw [prob_eq' E]
  unfold measure
  rw [Measure.smul_apply]
  congr

lemma ProbabilitySpace.prob_raw' [ProbabilitySpace Ω] (E : Set Ω) : P[ E ] = (rawMass Ω)⁻¹ * rawFiniteMeasure Ω E := by
  rw [<-ENNReal.coe_eq_coe, prob_raw E]
  push_cast
  congr
  rw [<-rawMeasure_eq Ω E]

/-- If nondegenerate, we have a full measure.  -/
@[simp]
lemma ProbabilitySpace.prob_univ (Ω : Type*) [ProbabilitySpace Ω] (h: isNondeg Ω) : P[(⊤ : Set Ω)] = 1 := by
  rw [prob_raw' (⊤ : Set Ω)]
  unfold isNondeg at h
  field_simp [h]
  rfl


/-- Degenerate probability measures are zero.  -/
@[simp]
lemma ProbabilitySpace.prob_zero [ProbabilitySpace Ω] (h: ¬ isNondeg Ω) (E : Set Ω): P[E] = 0 := by
  rw [prob_raw' E]
  field_simp; right
  unfold isNondeg at h
  contrapose! h
  exact zero_lt_iff.mpr h

/-- Larger events have larger probability. -/
lemma ProbabilitySpace.prob_mono {Ω : Type*} [ProbabilitySpace Ω] {A B : Set Ω} (h : A ≤ B) : P[A] ≤ P[B] := by
  rw [prob_eq A, prob_eq B]
  exact FiniteMeasure.apply_mono (finiteMeasure Ω) h

/-- All events occur with probability at most 1. -/
lemma ProbabilitySpace.prob_le_one [ProbabilitySpace Ω] (E : Set Ω) : P[ E ] ≤ 1 := by
  by_cases h: isNondeg Ω
  . rw [← prob_univ Ω h]
    simp [prob_mono]
  rw [prob_zero h E]
  norm_num

/-- Give all finite types the discrete sigma-algebra by default. -/
instance Fintype.instMeasurableSpace [Fintype S] : MeasurableSpace S := ⊤

/-- Every finite measure creates a ProbabilitySpace. -/
def ProbabilitySpace.ofFiniteMeasure [MeasurableSpace Ω] (μ : FiniteMeasure Ω) : ProbabilitySpace Ω where
  volume := μ
  measure_univ_lt_top := by
    simp
    exact IsFiniteMeasure.measure_univ_lt_top

/-- The formula for probability in ProbabilitySpace.ofFiniteMeasure in terms of the original measure -/
lemma ProbabilitySpace.ofFiniteMeasure.prob_eq [MeasurableSpace Ω] (μ : FiniteMeasure Ω) (E : Set Ω) : P[ E ; ofFiniteMeasure μ ] = (μ Set.univ)⁻¹ * μ E := by
  unfold finiteMeasure
  rw [FiniteMeasure.coeFn_smul]
  dsimp
  congr

-- Force subsets of measurable spaces to themselves be measurable spaces
attribute [instance] MeasureTheory.Measure.Subtype.measureSpace

/-- Every measurable subset of a probability space is also a probability space (even when the set has measure zero!).  May want to register this as an instance somehow. -/
noncomputable def Subtype.probabilitySpace {Ω : Type*} [ProbabilitySpace Ω] {E : Set Ω} (hE: MeasurableSet E): ProbabilitySpace E where
  measure_univ_lt_top := by
    rw [Measure.Subtype.volume_univ (MeasurableSet.nullMeasurableSet hE)]
    set μ := @volume Ω ProbabilitySpace.toMeasureSpace
    have : μ E ≤ μ Set.univ := by
      apply measure_mono
      simp
    exact lt_of_le_of_lt this (IsFiniteMeasure.measure_univ_lt_top)

lemma ProbabilitySpace.condRaw_eq [ProbabilitySpace Ω] {E : Set Ω} (hE: MeasurableSet E) {F : Set E} (hF : MeasurableSet F) : @rawFiniteMeasure E (Subtype.probabilitySpace hE) F = rawFiniteMeasure Ω (F : Set Ω) := by
  rw [<-ENNReal.coe_eq_coe, rawMeasure_eq Ω (F : Set Ω), @rawMeasure_eq E (Subtype.probabilitySpace hE) F]
  unfold rawMeasure
  rw [Measure.Subtype.volume_def]
  sorry

lemma ProbabilitySpace.condProb_eq [ProbabilitySpace Ω] {E : Set Ω} (hE: MeasurableSet E) {F : Set E} (hF : MeasurableSet F): P[ F ; Subtype.probabilitySpace hE ] = (P[ E ])⁻¹ * P[ (F : Set Ω) ]  := by
  rw [prob_raw' E, prob_raw' (F : Set Ω), @prob_raw' E (Subtype.probabilitySpace hE)]
  rw [condRaw_eq hE hF]
  sorry




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
