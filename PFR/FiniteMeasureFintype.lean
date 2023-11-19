import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic
import PFR.ForMathlib.FiniteMeasureComponent
import PFR.entropy_basic

open MeasureTheory Topology Metric Filter Set ENNReal NNReal Real

open scoped Topology ENNReal NNReal BoundedContinuousFunction

section count
/-! ### Counting measure as a finite measure and discrete uniform measure as a probability measure

-/

variable (Ω : Type*) [MeasurableSpace Ω] [Fintype Ω]

noncomputable def finCount : FiniteMeasure Ω :=
  ⟨Measure.count, Measure.count.isFiniteMeasure⟩

noncomputable def finUniformProba [Nonempty Ω] : ProbabilityMeasure Ω :=
  (finCount Ω).normalize

end count -- section

variable {ι : Type _} {Ω : Type _}
variable [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

section pmf
/-! ### Point mass function of a finite measures

-/

/-- The point mass function of a finite measure. -/
def FiniteMeasure.pmf (μ : FiniteMeasure Ω) (ω : Ω) : ℝ := (μ : Measure Ω).real {ω}

/-
Q: Why doesn't the spelling `μ.pmf` work?

invalid field 'pmf', the environment does not contain 'Subtype.pmf'
  μ
has type
  { μ // IsFiniteMeasure μ }
-/
/-- The point masses of a finite measure on a discrete topological space depend continuously on the
finite measure. -/
lemma continuous_pmf_apply [DiscreteTopology Ω] (ω : Ω) :
    Continuous (fun (μ : FiniteMeasure Ω) ↦ FiniteMeasure.pmf μ ω) :=
  continuous_finiteMeasure_apply_of_isOpen_of_isClosed ⟨isOpen_discrete _, T1Space.t1 _⟩

end pmf --section

section entropy
/-! ### Continuity of entropy-like quantitites for finite measures / probability measures

-/

open ProbabilityTheory

-- TODO: Use notation `Hm[μ]` (figure out how).
lemma continuous_measureEntropy_probabilityMeasure [Fintype Ω] [DiscreteTopology Ω] :
    Continuous (fun (μ : ProbabilityMeasure Ω) ↦ measureEntropy (S := Ω) μ) := by
  apply continuous_finset_sum
  intro ω _
  apply continuous_negIdMulLog.comp
  simp only [measure_univ, inv_one, one_smul]
  exact continuous_probabilityMeasure_apply_of_isOpen_of_isClosed
    (s := {ω}) ⟨isOpen_discrete _, T1Space.t1 _⟩

end entropy -- section
