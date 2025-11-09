import PFR.Mathlib.Analysis.Convex.StdSimplex
import PFR.Mathlib.MeasureTheory.Measure.ProbabilityMeasure

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
    refine ⟨∑ i, ENNReal.ofReal (p i) • Measure.dirac i, ⟨?_⟩⟩
    simp only [Measure.coe_finset_sum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.toReal_eq_toReal (by simp [ENNReal.sum_eq_top]) ENNReal.one_ne_top,
        ENNReal.toReal_sum (by simp)]
    have (x : X) : (ENNReal.ofReal (p x)).toReal = p x := ENNReal.toReal_ofReal (p.2.1 x)
    have that : ∑ i, p i = 1 := p.2.2
    simp_rw [this, that, ENNReal.toReal_one]
  left_inv := by
    intro μ
    ext s _hs
    conv_rhs => rw [← Measure.sum_smul_dirac (μ := (μ : Measure X))]
    simp
  right_inv := by
    rintro ⟨p, p_pos, hp⟩
    ext i
    simp only [stdSimplex.coe_mk, ProbabilityMeasure.mk_apply, Measure.coe_finset_sum,
      Measure.coe_smul, Finset.sum_apply, Pi.smul_apply, MeasurableSet.singleton,
      Measure.dirac_apply', smul_eq_mul]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp only [Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply, mul_one]
      exact ENNReal.toReal_ofReal (p_pos i)
    · intro b _ bi
      simp [bi]

@[simp] lemma probabilityMeasureEquivStdSimplex_symm_coe_apply [MeasurableSingletonClass X]
    (p : stdSimplex ℝ X) :
    (probabilityMeasureEquivStdSimplex.symm p : Measure X) =
       ∑ i, ENNReal.ofReal (p i) • Measure.dirac i := rfl

@[simp] lemma probabilityMeasureEquivStdSimplex_coe_apply [MeasurableSingletonClass X]
    (μ : ProbabilityMeasure X) (i : X) :
    probabilityMeasureEquivStdSimplex μ i = (μ {i}).toReal := rfl

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
