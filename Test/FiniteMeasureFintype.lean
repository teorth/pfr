import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic
import Mathlib.Probability.ProbabilityMassFunction.Uniform
import Mathlib.Probability.Density
import PFR.Entropy.Basic
import PFR.ForMathlib.FiniteMeasureComponent

open MeasureTheory Topology Metric Filter Set ENNReal NNReal Real

open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {ι : Type _} {Ω : Type _}
variable [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

-- Mathlib: Why is `Countable` an assumption in `Measure.toPMF`?

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

section count
/-! ### Counting measure as a finite measure and discrete uniform measure as a probability measure

These are mainly a test for what is a good spelling of uniformity of the distribution in `IsUniform`
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

end count -- section

section density_count
/-! ### Radon-Nikodym density w.r.t. counting measure and its relation to PMF

These are mainly a test for what is a good spelling of uniformity of the distribution in `IsUniform`
-/

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

-- to Mathlib? (after golf and minimization of hypotheses)
lemma PMF.toMeasure_eq_withDensity_count (p : PMF X) :
    p.toMeasure = Measure.count.withDensity p := by
  ext s s_mble
  simp only [s_mble, withDensity_apply, ← lintegral_indicator _ s_mble, lintegral_count,
             p.toMeasure_apply s s_mble]

-- to Mathlib? (after golf and minimization of hypotheses)
lemma sigmaFinite_count_of_countable [Countable X] : SigmaFinite (Measure.count : Measure X) := by
  apply @Measure.sigmaFinite_of_countable X _ Measure.count (Set.range fun x ↦ {x})
      (countable_range _) ?_ ?_
  · intro s hs
    simp only [mem_range] at hs
    obtain ⟨x, hx⟩ := hs
    simp only [← hx, MeasurableSet.singleton, Measure.count_singleton', one_lt_top]
  · apply subset_antisymm (subset_univ _)
    intro x _
    simp only [sUnion_range, mem_iUnion, mem_singleton_iff, exists_eq']

-- to Mathlib? (after golf and minimization of hypotheses)
lemma PMF.rnDeriv_toMeasure_count [Countable X] (p : PMF X) :
    Measure.rnDeriv p.toMeasure Measure.count = p := by
  have key := @Measure.rnDeriv_withDensity X _ Measure.count sigmaFinite_count_of_countable p
              (measurable_of_countable p)
  rw [← p.toMeasure_eq_withDensity_count] at key
  ext x
  have key' : Set.indicator {x} (Measure.rnDeriv (toMeasure p) Measure.count)
              =ᵐ[Measure.count] Set.indicator {x} p := by
    filter_upwards [key] with y hy
    by_cases hyx : y ∈ ({x} : Set X)
    · simpa only [mem_singleton_iff, indicator_of_mem hyx] using hy
    · simp only [mem_singleton_iff, indicator_of_not_mem hyx]
  have obs := lintegral_congr_ae key'
  simp_rw [lintegral_count] at obs
  have rw₁ := @sum_eq_tsum_indicator ℝ≥0∞ X _ _ (Measure.rnDeriv (toMeasure p) Measure.count) {x}
  have rw₂ := @sum_eq_tsum_indicator ℝ≥0∞ X _ _ p {x}
  simp only [Finset.sum_singleton, Finset.coe_singleton, mem_singleton_iff] at rw₁ rw₂
  rwa [← rw₁, ← rw₂] at obs

-- to Mathlib? (after golf and minimization of hypotheses)
lemma hasPDF_id_uniformOfFinset [MeasurableSingletonClass Ω] [Countable Ω]
    (s : Finset Ω) (hs : Finset.Nonempty s) :
    HasPDF id (PMF.uniformOfFinset s hs).toMeasure Measure.count := by
  refine ⟨measurable_id, ⟨PMF.uniformOfFinset s hs, ⟨measurable_of_countable _, ?_⟩⟩⟩
  simpa only [Measure.map_id] using PMF.toMeasure_eq_withDensity_count _

-- to Mathlib? (after golf and minimization of hypotheses)
-- This seems to indicate that the `pdf.IsUniform id s ℙ Measure.count` might be a
-- reasonable spelling of `IsUniform`.
lemma isUniform_uniformOfFinset [MeasurableSingletonClass Ω] [Countable Ω]
    (s : Finset Ω) (hs : Finset.Nonempty s) :
    pdf.IsUniform (id : Ω → Ω) s (PMF.uniformOfFinset s hs).toMeasure Measure.count := by
  simp [pdf.IsUniform]
  have obs := (@pdf.unique' Ω Ω _ _ (PMF.uniformOfFinset s hs).toMeasure Measure.count
          sigmaFinite_count_of_countable id (by apply hasPDF_id_uniformOfFinset)
          (PMF.uniformOfFinset s hs) (measurable_of_countable _).aemeasurable).mp ?_
  · simp only at obs
    convert obs
    ext ω
    simp only [Finset.mem_coe, PMF.uniformOfFinset_apply]
    by_cases hω : ω ∈ s <;> simp [hω]
  · simpa only [Measure.map_id] using PMF.toMeasure_eq_withDensity_count _

end density_count -- section
