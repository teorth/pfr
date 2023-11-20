import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import PFR.MeasureReal
import PFR.ForMathlib.Finiteness
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

attribute [simp] lintegral_dirac

open scoped BigOperators Topology

open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable (X : Type*) [Fintype X] [MeasurableSpace X]

@[simp] lemma ProbabilityMeasure.coe_mk (μ : Measure X) (hμ : IsProbabilityMeasure μ) :
  ((↑) : ProbabilityMeasure X → Measure X) (⟨μ, hμ⟩ : ProbabilityMeasure X) = μ := rfl

instance {X : Type*} [Fintype X] : CompactSpace (stdSimplex ℝ X) :=
  isCompact_iff_compactSpace.mp (isCompact_stdSimplex X)

/-- The canonical bijection between the set of probability measures on a fintype and the set of
nonnegative functions on the points adding up to one. -/
noncomputable def equiv_probabilityMeasure_stdSimplex [MeasurableSingletonClass X] :
    ProbabilityMeasure X ≃ stdSimplex ℝ X where
  toFun := by
    intro μ
    refine ⟨fun i ↦ (μ {i}).toReal, by simp, ?_⟩
    simp only
    rw [← NNReal.coe_sum, ← ENNReal.toNNReal_sum (fun a _ha ↦ by finiteness)]
    simp
  invFun := by
    intro p
    refine ⟨∑ i, ENNReal.ofReal ((p : X → ℝ) i) • Measure.dirac i, ⟨?_⟩⟩
    simp only [Measure.coe_finset_sum, Measure.smul_toOuterMeasure, OuterMeasure.coe_smul,
      Finset.sum_apply, Pi.smul_apply, MeasurableSet.univ, Measure.dirac_apply', Set.mem_univ,
      Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
    rw [← ENNReal.toReal_eq_toReal (by simp [ENNReal.sum_eq_top_iff]) ENNReal.one_ne_top,
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
    simp only [ProbabilityMeasure.coe_mk , Measure.coe_finset_sum, Measure.smul_toOuterMeasure,
      OuterMeasure.coe_smul, Finset.sum_apply, Pi.smul_apply, MeasurableSet.singleton,
      Measure.dirac_apply', Set.mem_singleton_iff, smul_eq_mul]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp only [Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply, mul_one]
      exact ENNReal.toReal_ofReal (p_pos i)
    · intro b _ bi
      simp [bi]

@[simp] lemma equiv_probabilityMeasure_stdSimplex_symm_coe_apply [MeasurableSingletonClass X]
    (p : stdSimplex ℝ X) :
    ((equiv_probabilityMeasure_stdSimplex X).symm p : Measure X) =
       ∑ i, ENNReal.ofReal ((p : X → ℝ) i) • Measure.dirac i := rfl

@[simp] lemma equiv_probabilityMeasure_stdSimplex_coe_apply [MeasurableSingletonClass X]
    (μ : ProbabilityMeasure X) (i : X) :
    ((equiv_probabilityMeasure_stdSimplex X) μ : X → ℝ) i = (μ {i}).toReal := rfl

variable [TopologicalSpace X] [DiscreteTopology X] [BorelSpace X]

variable {X}

lemma continuous_pmf_apply' (i : X) :
    Continuous (fun (μ : ProbabilityMeasure X) ↦ (μ : Measure X).real {i}) :=
  continuous_probabilityMeasure_apply_of_isClopen (s := {i})
    ⟨isOpen_discrete _, T1Space.t1 _⟩

lemma continuous_pmf_apply (i : X) :
    Continuous (fun (μ : ProbabilityMeasure X) ↦ μ {i}) :=  by
  -- KK: The coercion fight here is one reason why I now prefer ℝ-valued and not ℝ≥0-valued probas.
  convert continuous_real_toNNReal.comp (continuous_pmf_apply' i)
  ext
  simp only [Measure.real, Function.comp_apply, Real.coe_toNNReal', ge_iff_le,
             ENNReal.toReal_nonneg, max_eq_left]
  rfl

variable (X)

noncomputable def homeomorph_probabilityMeasure_stdSimplex
    [TopologicalSpace X] [DiscreteTopology X] [BorelSpace X] :
    ProbabilityMeasure X ≃ₜ stdSimplex ℝ X where
  __ := equiv_probabilityMeasure_stdSimplex X
  continuous_toFun := by
    apply continuous_iff_continuousAt.2 (fun μ ↦ ?_)
    rw [ContinuousAt, tendsto_subtype_rng, tendsto_pi_nhds]
    intro i
    simpa using ((continuous_pmf_apply i).continuousAt (x := μ)).tendsto
  continuous_invFun := by
    apply continuous_iff_continuousAt.2 (fun p ↦ ?_)
    rw [ContinuousAt, ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]
    intro f
    simp only [Equiv.invFun_as_coe, equiv_probabilityMeasure_stdSimplex_symm_coe_apply,
      lintegral_finset_sum_measure, lintegral_smul_measure, lintegral_dirac]
    apply tendsto_finset_sum _ (fun i _hi ↦ ?_)
    apply ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal _) (by simp)
    exact ((continuous_apply i).tendsto _).comp (continuous_subtype_val.tendsto _)

/-- This is still true when `X` is a metrizable compact space, but the proof requires Riesz
representation theorem.
TODO: remove once the general version is proved. -/
instance : CompactSpace (ProbabilityMeasure X) :=
  (homeomorph_probabilityMeasure_stdSimplex X).symm.compactSpace
