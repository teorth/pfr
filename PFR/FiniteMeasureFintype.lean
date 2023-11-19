import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic
import PFR.ForMathlib.FiniteMeasureComponent
import PFR.entropy_basic
import Mathlib

open MeasureTheory Topology Metric Filter Set ENNReal NNReal Real

open scoped Topology ENNReal NNReal BoundedContinuousFunction

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
  continuous_finiteMeasure_apply_of_isClopen ⟨isOpen_discrete _, T1Space.t1 _⟩

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
  exact continuous_probabilityMeasure_apply_of_isClopen (s := {ω}) ⟨isOpen_discrete _, T1Space.t1 _⟩

end entropy -- section

section count
/-! ### Counting measure as a finite measure and discrete uniform measure as a probability measure

-/

variable (Ω : Type*) [MeasurableSpace Ω] [Fintype Ω]

/-- The counting measure on a finite type as a `FiniteMeasure`. -/
noncomputable def finCount : FiniteMeasure Ω :=
  ⟨Measure.count, Measure.count.isFiniteMeasure⟩

/-- The discrete uniform probability measure on a nonempty finite type as a `ProbabilityMeasure`. -/
noncomputable def finUniformProba [Nonempty Ω] : ProbabilityMeasure Ω :=
  (finCount Ω).normalize

/-- The counting measure on a finite set as a `FiniteMeasure`. -/
noncomputable def finCountOn {X : Type*} [MeasurableSpace X] {s : Set X}
    (s_finite : s.Finite) (s_mble : MeasurableSet s) : FiniteMeasure X :=
  ⟨Measure.count.restrict s, by
    refine ⟨?_⟩
    simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter,
               Measure.count_apply_finite' s_finite s_mble]
    exact coe_lt_top⟩

/-- The discrete uniform probability measure on a nonempty finite type as a `ProbabilityMeasure`. -/
noncomputable def finUniformProbaOn {X : Type*} [MeasurableSpace X] {s : Set X}
    (s_nonemp : s.Nonempty) (s_finite : s.Finite) (s_mble : MeasurableSet s) :
    ProbabilityMeasure X :=
  @FiniteMeasure.normalize X (Exists.nonempty s_nonemp) _ (finCountOn s_finite s_mble)

-- to Mathlib
lemma Measure.count_apply_pos (X : Type*) [MeasurableSpace X] {s : Set X}
    (s_nonemp : s.Nonempty) (s_mble : MeasurableSet s) :
    0 < Measure.count s := by
  by_contra maybe_zero
  have maybe_zero' : Measure.count s = 0 := by aesop
  rw [Measure.count_eq_zero_iff'] at maybe_zero'
  · aesop
  · exact s_mble

-- to Mathlib
lemma Measure.count_univ_pos (X : Type*) [MeasurableSpace X] [Nonempty X] :
    0 < Measure.count (univ : Set X) :=
  Measure.count_apply_pos _ univ_nonempty MeasurableSet.univ

lemma finCount_mass_pos [Nonempty Ω] : 0 < (finCount Ω).mass := by
  apply ENNReal.toNNReal_pos _ (measure_ne_top _ univ)
  have obs : 0 < Measure.count (univ : Set Ω) := Measure.count_univ_pos Ω
  aesop

lemma finCount_mass_nonzero [Nonempty Ω] : (finCount Ω).mass ≠ 0 := (finCount_mass_pos Ω).ne.symm

variable [MeasurableSingletonClass Ω]

@[simp] lemma finCount_apply_eq_card (s : Set Ω) :
    (finCount Ω : Measure Ω).real s = Finset.card (toFinite s).toFinset :=
  congrArg ENNReal.toReal (Measure.count_apply_finite s (toFinite s))

@[simp] lemma finUniformProba_apply_eq_inv_mul_card [Nonempty Ω] (s : Set Ω) :
    (finUniformProba Ω : Measure Ω).real s
      = (Fintype.card Ω : ℝ)⁻¹ * Finset.card (toFinite s).toFinset := by
  simp [finUniformProba, FiniteMeasure.normalize, finCount_mass_nonzero Ω]
  -- Why doesn't `ite_false` kick in? Also `rw [ite_false]` fails.
  -- On the other hand `FiniteMeasure.mass` should probably be refactored, so the coercion
  -- fight might not be worth it now.
  sorry

@[simp] lemma finUniformProba_apply_eq_inv_mul_card' [Nonempty Ω] (s : Set Ω) :
    (finUniformProba Ω : Measure Ω) s
      = (Fintype.card Ω : ℝ≥0∞)⁻¹ * Finset.card (toFinite s).toFinset := by
  simp [finUniformProba, FiniteMeasure.normalize, finCount_mass_nonzero Ω]
  -- Why doesn't `ite_false` kick in?
  -- Also `rw [ite_false]` fails.
  sorry

lemma pmf_finUniformProba_eq_uniformOfFintype [Nonempty Ω] :
    (finUniformProba Ω : Measure Ω).toPMF = PMF.uniformOfFintype Ω := by
  ext ω
  rw [Measure.toPMF]
  simp only [finUniformProba_apply_eq_inv_mul_card', toFinite_toFinset,
    toFinset_singleton, Finset.card_singleton, Nat.cast_one, mul_one, PMF.uniformOfFintype_apply]
  rfl

#check Measure.toPMF -- Mathlib: Why is `Countable` an assumption in `toPMF`?

-- By this experiment, I'm not sure `(X.map μ).toPMF = PMF.uniformOfFinset _ _` would be a
-- nice enough spelling for `IsUniform`.
lemma pmf_finUniformProbaOn_eq_uniformOfFintype {X : Type*} [Countable X] -- why necessary?
    [MeasurableSpace X] [MeasurableSingletonClass X] {s : Set X}
    (s_nonemp : s.Nonempty) (s_finite : s.Finite) (s_mble : MeasurableSet s) :
    (finUniformProbaOn s_nonemp s_finite s_mble : Measure X).toPMF
      = PMF.uniformOfFinset s_finite.toFinset
        ((Finite.toFinset_nonempty s_finite).mpr s_nonemp) := by
  ext ω
  rw [Measure.toPMF]
  sorry

-- Unnecessary, just for Kalle to practice with existing PMF API.
lemma pmf_probabilityMeasure_apply_eq [MeasurableSingletonClass Ω] (μ : ProbabilityMeasure Ω) (ω : Ω) :
    (μ : Measure Ω).toPMF ω = (μ : Measure Ω) {ω} := rfl

-- Unnecessary, just for Kalle to practice with existing PMF API.
lemma pmf_probabilityMeasure_apply_eq' [MeasurableSingletonClass Ω] (μ : ProbabilityMeasure Ω) (ω : Ω) :
    (μ : Measure Ω).toPMF ω = ENNReal.ofReal ((μ : Measure Ω).real {ω}) := by
  simp only [Measure.toPMF, Measure.real, ne_eq]
  rw [ofReal_toReal]
  · rfl
  · exact measure_ne_top ↑μ {ω}

-- For Kalle to practice the existing `pdf.IsUniform` and `PMF.uniformOfFinset` APIs.
lemma isUniform_uniformOfFinset (s : Finset Ω) (hs : Finset.Nonempty s) :
    pdf.IsUniform (id : Ω → Ω) s (PMF.uniformOfFinset s hs).toMeasure Measure.count := by
  -- Apparently no results exist yet to connect densities w.r.t. counting measure to PMFs?
  sorry

end count -- section

section density_count

end density_count -- section
