import Mathlib

/-! Basic theory of probability spaces. -/

open MeasureTheory

/-- A ProbSpace is a MeasureSpace in which the canonical volume measure is also a probability measure. -/
class ProbSpace (Ω : Type*) extends MeasureSpace Ω, IsProbabilityMeasure volume


/-- The probability measure associated to a ProbSpace --/
@[simps (config := .lemmasOnly)]
def probMeasure (Ω : Type*) [ProbSpace Ω] : ProbabilityMeasure Ω := ⟨volume, inferInstance⟩

/-- prob Ω E is the probability of E in Ω. -/
def prob {Ω : Type*} [ProbSpace Ω] (E : Set Ω) := probMeasure Ω E

/-- The customary notation for probability.  Todo: integrate this with https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Notation.html -/
notation:100 "P[ " E " ]" => prob E

/-- Total event has probability one. -/
lemma prob_univ (Ω : Type*) [ProbSpace Ω] : P[(⊤ : Set Ω)] = 1 := (probMeasure Ω).coeFn_univ

/-- Larger events have larger probability. -/
lemma prob_mono {Ω : Type*} [ProbSpace Ω] {A B : Set Ω} (h : A ≤ B) : P[A] ≤ P[B] :=
  (probMeasure Ω).apply_mono h

/-- All events have probability at most 1.  Measurability not required! -/
lemma prob_le_one [ProbSpace Ω] (E : Set Ω) : P[ E ] ≤ 1 := (probMeasure Ω).apply_le_one E

/- an alternate proof:

lemma prob_le_one' [ProbSpace Ω] (E : Set Ω) : P[ E ] ≤ 1 := by
  rw [← prob_univ Ω]
  simp [prob_mono]

-/

/-- Probability can also be computed using probMeasure. --/
lemma prob_eq [ProbSpace Ω] (E : Set Ω) : P[ E ] = probMeasure Ω E := rfl
