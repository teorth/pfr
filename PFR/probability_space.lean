import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Basic theory of probability spaces
-/

/-- Give all finite types the discrete sigma-algebra by default. -/
instance Fintype.instMeasurableSpace [Fintype S] : MeasurableSpace S := ⊤

open MeasureTheory Set

/-- In this project, a ProbabilitySpace is modeled by a MeasureSpace with a finite volume measure
that can potentially vanish.  The probability measure is then the normalization of this probability
measure, bearing in mind that it may be zero. Thus we also consider a measure space with the zero
measure to be a (degenerate) example of a   This will be convenient when we wish to
condition the probability space to an event, because the event may potentially have zero measure. -/
class ProbabilitySpace (Ω : Type*) extends MeasureSpace Ω, IsFiniteMeasure volume

namespace ProbabilitySpace
variable (Ω : Type*) [ProbabilitySpace Ω] [Fintype S] {X : Ω → S} {E : Set Ω}

/-- The raw, unnormalized measure.  Would only be directly used in foundational lemmas typically. -/
def rawMeasure : Measure Ω := volume

/-- The raw measure interpreted as a finite measure. Again, only used in foundational lemmas. -/
@[simps (config := .lemmasOnly)]
def rawFiniteMeasure : FiniteMeasure Ω := ⟨volume, inferInstance⟩

/-- The total mass of the raw measure. Can vanish! -/
def rawMass : NNReal := rawFiniteMeasure Ω univ

/-- The assertion that a probability space is nondegenerate (non-zero raw mass). -/
def isNondeg : Prop := 0 < rawMass Ω

/-- The normalized measure associated to a probability space -/
noncomputable def measure : Measure Ω := (rawMass Ω)⁻¹ • volume

/-- The normalized finite measure associated to a probability space -/
noncomputable def finiteMeasure : FiniteMeasure Ω := (rawMass Ω)⁻¹ • rawFiniteMeasure Ω

variable {Ω}

/-- The raw finite measure and the raw measure agree. -/
lemma rawFiniteMeasure_eq (E : Set Ω) : rawFiniteMeasure Ω E = rawMeasure Ω E := by
  simp [rawMeasure, rawFiniteMeasure]; congr

/-- The raw mass is the mass of the raw measure. -/
lemma rawMass_eq : rawMass Ω = rawMeasure Ω univ := rawFiniteMeasure_eq _

/-- The raw mass is the mass of the raw finite measure. -/
lemma rawMass_eq' : rawMass Ω = rawFiniteMeasure Ω univ := rfl

/-- P[ E ] is the probability of E. -/
notation:100 "P[ " E " ]" => (finiteMeasure _) E

/-- An alternate notation where one makes the probability space `X = ‹ProbabilitySpace Ω›`
explicit. -/
notation:100 "P[ " E " ; " X " ]" => @finiteMeasure _ X E

/-- Probability can be computed using finiteMeasure. -/
lemma prob_eq (E : Set Ω) : P[ E ] = finiteMeasure Ω E := rfl

/-- Probability can also be computed using measure. -/
lemma prob_eq' (E : Set Ω) : P[ E ] = measure Ω E := by
  unfold measure finiteMeasure
  simp
  congr

lemma prob_eq'' (E : Set Ω) : P[ E ; ‹ ProbabilitySpace Ω› ] = P[ E ] := by rfl

/-- Probability can be computed using raw measure. -/
lemma prob_raw (E : Set Ω) : P[ E ] = (rawMass Ω)⁻¹ * rawMeasure Ω E := by
  rw [prob_eq' E]
  unfold measure
  rw [Measure.smul_apply]
  congr

/-- Probability can be computed using raw finite measure. -/
lemma prob_raw' (E : Set Ω) : P[ E ] = (rawMass Ω)⁻¹ * rawFiniteMeasure Ω E := by
  rw [<-ENNReal.coe_eq_coe, prob_raw E]
  push_cast
  congr
  rw [←rawFiniteMeasure_eq E]

variable (Ω) in
/-- If nondegenerate, we have a full measure.  -/
@[simp]
lemma prob_univ (h : isNondeg Ω) : P[(⊤ : Set Ω)] = 1 := by
  rw [prob_raw' (⊤ : Set Ω)]
  unfold isNondeg at h
  field_simp [h]
  rfl


/-- Degenerate probability measures are zero.  -/
@[simp]
lemma prob_zero (h : ¬ isNondeg Ω) (E : Set Ω): P[E] = 0 := by
  rw [prob_raw' E]
  field_simp; right
  unfold isNondeg at h
  contrapose! h
  exact zero_lt_iff.mpr h

/-- Larger events have larger probability. -/
lemma prob_mono {A B : Set Ω} (h : A ⊆ B) : P[A] ≤ P[B] := by
  rw [prob_eq A, prob_eq B]
  exact FiniteMeasure.apply_mono (finiteMeasure Ω) h

/-- All events occur with probability at most 1. -/
lemma prob_le_one (E : Set Ω) : P[ E ] ≤ 1 := by
  by_cases h: isNondeg Ω
  . rw [← prob_univ Ω h]
    simp [prob_mono]
  rw [prob_zero h E]
  norm_num

/-- Every finite measure creates a `ProbabilitySpace`. -/
def ofFiniteMeasure [MeasurableSpace Ω] (μ : FiniteMeasure Ω) : ProbabilitySpace Ω where
  volume := μ
  measure_univ_lt_top := by
    simp
    exact IsFiniteMeasure.measure_univ_lt_top

/-- The formula for probability in `ProbabilitySpace.ofFiniteMeasure` in terms of the original
measure -/
lemma ofFiniteMeasure.prob_eq [MeasurableSpace Ω] (μ : FiniteMeasure Ω) (E : Set Ω) :
    P[ E ; ofFiniteMeasure μ ] = (μ Set.univ)⁻¹ * μ E := by
  unfold finiteMeasure
  rw [FiniteMeasure.coeFn_smul]
  dsimp
  congr

/-- Every measurable subset of a probability space is also a probability space (even when the set has measure zero!).  May want to register this as an instance somehow. -/
noncomputable def Subset.probabilitySpace {Ω : Type*} [ProbabilitySpace Ω] (E : Set Ω) : ProbabilitySpace Ω where
  volume := volume.restrict E
  measure_univ_lt_top := by
    unfold volume
    rw [Measure.restrict_apply_univ]
    show rawMeasure Ω E < ⊤
    have : rawMeasure Ω E ≤ rawMeasure Ω Set.univ := by
      apply MeasureTheory.measure_mono
      simp
    have h : rawMeasure Ω Set.univ < ⊤ := by
      unfold rawMeasure
      apply IsFiniteMeasure.measure_univ_lt_top
    exact lt_of_le_of_lt this h

-- Force subsets of measurable spaces to themselves be measurable spaces
attribute [instance] MeasureTheory.Measure.Subtype.measureSpace

/-- The raw finite measure after conditioning. -/
lemma condRaw_eq [hΩ: ProbabilitySpace Ω] {E F : Set Ω} (hF : MeasurableSet F) : @rawFiniteMeasure Ω (Subset.probabilitySpace E) F = rawFiniteMeasure Ω (F ∩ E) := by
  rw [<-ENNReal.coe_eq_coe, @rawFiniteMeasure_eq Ω hΩ (F ∩ E), @rawFiniteMeasure_eq Ω (Subset.probabilitySpace E) F]
  unfold rawMeasure
  show (volume.restrict E) F = volume (F ∩ E)
  exact Measure.restrict_apply hF

/-- The raw finite mass after conditioning. -/
lemma condRawMass_eq [hΩ: ProbabilitySpace Ω] {E : Set Ω} : @rawMass Ω (Subset.probabilitySpace E) = rawFiniteMeasure Ω E := by
  rw [@rawMass_eq' Ω (Subset.probabilitySpace E), condRaw_eq]
  simp
  exact MeasurableSet.univ

notation:100 "P[ " F " | " E " ]" => P[ F ; Subset.probabilitySpace E ]

/-- The conditional probability formula. -/
lemma condProb_eq [hΩ : ProbabilitySpace Ω] {E F : Set Ω} (hF : MeasurableSet F) :
    P[ F | E ] = (P[ E ])⁻¹ * P[ F ∩ E ]  := by
  rw [@prob_raw' Ω (Subset.probabilitySpace E) F, @prob_raw' Ω hΩ (F ∩ E), @prob_raw' Ω hΩ E, condRaw_eq hF, condRawMass_eq]
  generalize a_def : rawMass Ω = a
  generalize b_def : rawFiniteMeasure Ω E = b
  rcases eq_or_ne a 0 with ha | ha
  . simp [ha]; left
    suffices : b ≤ a
    . rw [ha] at this; exact le_zero_iff.mp this
    rw [<- a_def, <- b_def, rawMass_eq']
    apply FiniteMeasure.apply_mono
    simp
  rcases eq_or_ne b 0 with hb | hb
  . simp [hb]
  . field_simp; ring

/-- Larger events have larger conditional probability.  A simple example of how an unconditional lemma can instantly imply a conditional counterpart. -/
lemma prob_mono_cond {A B E : Set Ω} (h : A ⊆ B) : P[A | E] ≤ P[B | E] :=
  @prob_mono Ω (Subset.probabilitySpace E) _ _ h

/-- Conditioning to a positive probability event gives a non-degenerate probability space. -/
lemma posprob_isnondeg [hΩ : ProbabilitySpace Ω] {E : Set Ω} (hE : 0 < P[E]) : @isNondeg Ω (Subset.probabilitySpace E) := by
  unfold isNondeg
  rw [prob_raw'] at hE
  contrapose! hE
  simp at hE ⊢
  left

open BigOperators


/-- The law of total probability: in a non-degenerate space, the probability densities of a discrete
random variable sum to 1. Proof is way too long.

TODO: connect this with `Mathlib.Probability.ProbabilityMassFunction.Basic`. -/
lemma totalProb (h : isNondeg Ω) {X : Ω → S} (hX : Measurable X) : ∑ s, P[X ⁻¹' {s}] = 1 := by
  rw [<-ENNReal.coe_eq_coe]
  push_cast
  conv =>
    lhs; congr; rfl; intro s
    rw [prob_eq']
  rw [<- MeasureTheory.measure_biUnion_finset]
  . rw [<-prob_eq']
    norm_cast
    convert prob_univ Ω h
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
lemma range_nonempty (h : isNondeg Ω) (hX : Measurable X) : Nonempty S := by
  rcases isEmpty_or_nonempty S with hS | hS
  . have := totalProb h hX
    simp [hS] at this
  assumption

lemma range_nonempty' (h : isNondeg Ω) (hX : Measurable X) : 0 < Fintype.card S := by
  suffices : Fintype.card S ≠ 0
  . contrapose! this; linarith
  have := range_nonempty h hX
  apply Fintype.card_ne_zero

/-- Definition of a uniform random variable on a set S -/
def isUniform (X : Ω → S) := (Measurable X) ∧ (∀ s : S, P[ X ⁻¹' {s} ] = ((Fintype.card S) : ℝ)⁻¹)

end ProbabilitySpace
