import PFR.ForMathlib.FiniteMeasureComponent

/-!
# Compactness of the space of probability measures

We define the canonical bijection between the space of probability measures on a finite space `X`
and the standard simplex, and show that it is a homeomorphism.

We deduce that the space of probability measures is compact in this situation. This is an easy case
of a result that holds in a general compact metrizable space, but requires Riesz representation
theorem which we don't have currently in mathlib.

-/

open MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X]

section

variable [TopologicalSpace X] [DiscreteTopology X] [BorelSpace X]

lemma continuous_pmf_apply' (i : X) :
    Continuous fun μ : ProbabilityMeasure X ↦ (μ : Measure X).real {i} :=
  continuous_probabilityMeasure_apply_of_isClopen (s := {i}) $ isClopen_discrete _

lemma continuous_pmf_apply (i : X) :  Continuous fun μ : ProbabilityMeasure X ↦ μ {i} := by
  -- KK: The coercion fight here is one reason why I now prefer ℝ-valued and not ℝ≥0-valued probas.
  convert continuous_real_toNNReal.comp (continuous_pmf_apply' i)
  ext
  simp only [Measure.real, Function.comp_apply, Real.coe_toNNReal', ge_iff_le,
             ENNReal.toReal_nonneg, max_eq_left]
  rfl

-- KK: I will reuse this, so could be used in `probabilityMeasureHomeoStdSimplex`, too.
open Filter in
lemma tendsto_lintegral_of_forall_of_finite [Finite X] {ι : Type*} {L : Filter ι}
    (μs : ι → Measure X) (μ : Measure X)
    (f : X →ᵇ ℝ≥0) (h : ∀ (x : X), Tendsto (fun i ↦ μs i {x}) L (𝓝 (μ {x}))) :
    Tendsto (fun i ↦ ∫⁻ x, f x ∂(μs i)) L (𝓝 (∫⁻ x, f x ∂μ)) := by
  cases nonempty_fintype X
  simp only [lintegral_fintype]
  refine tendsto_finset_sum Finset.univ ?_
  exact fun x _ ↦ ENNReal.Tendsto.const_mul (h x) (Or.inr ENNReal.coe_ne_top)

end

section Fintype
variable [Fintype X]

/-- The canonical bijection between the set of probability measures on a fintype and the set of
nonnegative functions on the points adding up to one. -/
noncomputable def probabilityMeasureEquivStdSimplex [Fintype X] [MeasurableSingletonClass X] :
    ProbabilityMeasure X ≃ stdSimplex ℝ X where
  toFun := by
    intro μ
    refine ⟨fun i ↦ (μ {i}).toReal, by simp, ?_⟩
    simp only
    rw [← NNReal.coe_sum, ProbabilityMeasure.coeFn_def,
      ← ENNReal.toNNReal_sum (fun a _ha ↦ by finiteness)]
    simp
  invFun := by
    intro p
    refine ⟨∑ i, ENNReal.ofReal ((p : X → ℝ) i) • Measure.dirac i, ⟨?_⟩⟩
    simp only [Measure.coe_finset_sum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.toReal_eq_toReal (by simp [ENNReal.sum_eq_top]) ENNReal.one_ne_top,
        ENNReal.toReal_sum (by simp)]
    simp_rw [ENNReal.toReal_ofReal (p.2.1 _), p.2.2, ENNReal.one_toReal]
  left_inv := by
    intro μ
    ext s _hs
    conv_rhs => rw [← Measure.sum_smul_dirac (μ := (μ : Measure X))]
    simp
  right_inv := by
    rintro ⟨p, p_pos, hp⟩
    ext i
    simp only [ProbabilityMeasure.mk_apply, Measure.coe_finset_sum, Measure.coe_smul,
      Finset.sum_apply, Pi.smul_apply, MeasurableSet.singleton, Measure.dirac_apply', smul_eq_mul]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp only [Measure.smul_apply, MeasurableSet.singleton, Measure.dirac_apply',
        Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
      exact ENNReal.toReal_ofReal (p_pos i)
    · intro b _ bi
      simp [bi]

@[simp] lemma probabilityMeasureEquivStdSimplex_symm_coe_apply [MeasurableSingletonClass X]
    (p : stdSimplex ℝ X) :
    (probabilityMeasureEquivStdSimplex.symm p : Measure X) =
       ∑ i, ENNReal.ofReal ((p : X → ℝ) i) • Measure.dirac i := rfl

@[simp] lemma probabilityMeasureEquivStdSimplex_coe_apply [MeasurableSingletonClass X]
    (μ : ProbabilityMeasure X) (i : X) :
    (probabilityMeasureEquivStdSimplex μ : X → ℝ) i = (μ {i}).toReal := rfl

variable [TopologicalSpace X] [DiscreteTopology X] [BorelSpace X]

/-- The canonical homeomorphism between the space of probability measures on a finite space and the
standard simplex. -/
noncomputable def probabilityMeasureHomeoStdSimplex : ProbabilityMeasure X ≃ₜ stdSimplex ℝ X where
  __ := probabilityMeasureEquivStdSimplex
  continuous_toFun := by
    apply continuous_iff_continuousAt.2 (fun μ ↦ ?_)
    rw [ContinuousAt, tendsto_subtype_rng, tendsto_pi_nhds]
    intro i
    simpa using ((continuous_pmf_apply i).continuousAt (x := μ)).tendsto
  continuous_invFun := by
    apply continuous_iff_continuousAt.2 (fun p ↦ ?_)
    rw [ContinuousAt, ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]
    intro f
    simp only [Equiv.invFun_as_coe, probabilityMeasureEquivStdSimplex_symm_coe_apply,
      lintegral_finset_sum_measure, lintegral_smul_measure, lintegral_dirac]
    apply tendsto_finset_sum _ (fun i _hi ↦ ?_)
    apply ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal _) (by simp)
    exact ((continuous_apply i).tendsto _).comp (continuous_subtype_val.tendsto _)

end Fintype

variable [TopologicalSpace X] [OpensMeasurableSpace X] [Finite X] [DiscreteTopology X]
  [BorelSpace X]

/-- This is still true when `X` is a metrizable compact space, but the proof requires Riesz
representation theorem.
TODO: remove once the general version is proved. -/
instance : CompactSpace (ProbabilityMeasure X) := by
  cases nonempty_fintype X; exact probabilityMeasureHomeoStdSimplex.symm.compactSpace

instance : SecondCountableTopology (ProbabilityMeasure X) := by
  cases nonempty_fintype X
  exact (probabilityMeasureHomeoStdSimplex (X := X)).secondCountableTopology
