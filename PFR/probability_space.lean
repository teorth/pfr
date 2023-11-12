import Mathlib

/-! Basic theory of probability spaces. -/

open MeasureTheory

/-- A ProbSpace is a MeasureSpace in which the canonical volumen measure is also a probability measure. -/
class ProbSpace (Ω : Type*) extends
  MeasureSpace Ω,
  IsProbabilityMeasure volume

/-- This method to extract the probability measure automatically creates an IsProbabilityMeasure instance. --/
abbrev probMeasure (Ω : Type*) [ProbSpace Ω] : Measure Ω := volume

def prob {Ω : Type*} [ProbSpace Ω] (E : Set Ω) := MeasureSpace.volume E

notation:100 "P[ " E " ]" => prob E

lemma prob_univ (Ω : Type*) [ProbSpace Ω] : P[(⊤ : Set Ω)] = 1 :=
  IsProbabilityMeasure.measure_univ

lemma prob_mono {Ω : Type*} [ProbSpace Ω] {A B : Set Ω} (h : A ≤ B) : P[A] ≤ P[B] :=
  OuterMeasure.mono _ h

lemma prob_le_one [ProbSpace Ω] (E : Set Ω) : P[ E ] ≤ 1 := by
  rw [← prob_univ Ω]
  simp [prob_mono]

lemma prob_le_one' [ProbSpace Ω] (E : Set Ω) : P[ E ] ≤ 1 := by
  unfold prob
  exact MeasureTheory.prob_le_one

lemma prob_eq [ProbSpace Ω] (E : Set Ω) : P[ E ] = probMeasure Ω E := by
  rfl
