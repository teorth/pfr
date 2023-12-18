import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import PFR.Tactic.Finiteness

open ENNReal MeasureTheory MeasurableSpace Measure Set
open scoped BigOperators

variable {Ω Ω' α β γ : Type*} {m : MeasurableSpace Ω} [MeasurableSpace Ω'] {μ : Measure Ω}
  {s t : Set Ω} {i : Ω' → Ω}

namespace ProbabilityTheory

@[inherit_doc cond] -- TODO: Also tag the two existing notations
scoped notation:60 μ "[|" T " ← " t "]" => μ[|T ⁻¹' {t}]

lemma cond_absolutelyContinuous : μ[|s] ≪ μ :=
  smul_absolutelyContinuous.trans restrict_le_self.absolutelyContinuous

/-- `μ[|s]` is always a finite measure. -/
instance cond_isFiniteMeasure : IsFiniteMeasure (μ[|s]) := by
  constructor
  simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, MeasurableSet.univ,
    Measure.restrict_apply, Set.univ_inter, smul_eq_mul, ProbabilityTheory.cond,
    ← ENNReal.div_eq_inv_mul]
  exact ENNReal.div_self_le_one.trans_lt ENNReal.one_lt_top

lemma cond_eq_zero_of_measure_eq_zero (hμs : μ s = 0) : μ[|s] = 0 := by
  simp [cond, restrict_eq_zero.2 hμs]

@[simp] lemma cond_eq_zero (hμs : μ s ≠ ⊤) : μ[|s] = 0 ↔ μ s = 0 := by simp [cond, hμs]

lemma comap_cond (hi : MeasurableEmbedding i) (hi' : ∀ᵐ ω ∂μ, ω ∈ range i) (hs : MeasurableSet s) :
    comap i (μ[|s]) = (comap i μ)[|i ⁻¹' s] := by
  ext t ht
  change μ (range i)ᶜ = 0 at hi'
  rw [cond_apply, comap_apply, cond_apply, comap_apply, comap_apply, image_inter,
    image_preimage_eq_inter_range, inter_right_comm, measure_inter_conull hi',
    measure_inter_conull hi']
  all_goals first
  | exact hi.injective
  | exact hi.measurableSet_image'
  | exact hs
  | exact ht
  | exact hi.measurable hs
  | exact (hi.measurable hs).inter ht

variable [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

/-- The law of total probability : a measure $\mu$ can be expressed as a mixture of its conditional
measures $\mu[|Y^{-1}\{y\}]$ from a finitely valued random variable $Y$.-/
lemma law_of_total_probability {Y : Ω → T} (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] :
    μ = ∑ y, μ (Y ⁻¹' {y}) • (μ[|Y ← y]) := by
  apply Measure.ext
  intro E hE
  simp only [Measure.coe_finset_sum, smul_toOuterMeasure, OuterMeasure.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  have : μ E = ∑ y : T, μ (Y ⁻¹' {y} ∩ E) := by
    have : E = ⋃ y ∈ Set.univ, Y ⁻¹' {y} ∩ E := by
      simp; ext _; simp
    nth_rewrite 1 [this]
    convert measure_biUnion_finset _ _
    . simp
    · intro _ _ _ _ hyz
      apply Disjoint.inf_left
      apply Disjoint.inf_right
      apply Disjoint.preimage
      simp [hyz]
    intro b _
    exact MeasurableSet.inter (hY (MeasurableSet.singleton b)) hE
  rw [this]
  congr with y
  rcases eq_or_ne (μ (Y ⁻¹' {y})) 0 with hy | hy
  . simp [hy]
    exact measure_inter_null_of_null_left E hy
  symm
  rw [mul_comm, cond_mul_eq_inter _ (hY (MeasurableSet.singleton y)) hy]

/-- Replace `cond_cond_eq_cond_inter'` in mathlib with this version, which removes a nonzero measure
assumption-/
theorem cond_cond_eq_cond_inter'' (hms : MeasurableSet s) (hmt : MeasurableSet t)
    (hcs : μ s ≠ ∞ := by finiteness) :
    μ[|s][|t] = μ[|s ∩ t] := by
  ext u
  rw [cond_apply _ hmt, cond_apply _ hms, cond_apply _ hms, cond_apply _ (hms.inter hmt)]
  rcases eq_or_ne (μ (s ∩ t)) 0 with hst|hst
  · have : μ (s ∩ t ∩ u) = 0 :=
      le_antisymm (le_trans (measure_mono (Set.inter_subset_left _ _)) hst.le) bot_le
    simp [this, ← Set.inter_assoc]
  · have hcs' : μ s ≠ 0 :=
      (μ.toOuterMeasure.pos_of_subset_ne_zero (Set.inter_subset_left _ _) hst).ne'
    simp [*, hms.inter hmt, cond_apply, ← mul_assoc, ← Set.inter_assoc, ENNReal.mul_inv, mul_comm, ←
      mul_assoc, ENNReal.mul_inv_cancel]

end ProbabilityTheory
