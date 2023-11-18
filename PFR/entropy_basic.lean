import Mathlib.Data.Prod.TProd
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.IdentDistrib
import PFR.ForMathlib.Positivity
import PFR.neg_xlogx
import PFR.MeasureReal

/-!
# Entropy and conditional entropy

## Main definitions

* `measureEntropy`: entropy of a measure
* `entropy`: entropy of a random variable, defined as `measureEntropy (volume.map X)`
* `condEntropy`: conditional entropy of a random variable `X` w.r.t. another one `Y`
* `mutualInformation`: mutual information of two random variables

## Main statements

* `chain_rule`: `H[⟨ X, Y ⟩] = H[Y] + H[ X Y`

## Notations

* `Hm[μ] = measureEntropy μ`
* `H[X] = entropy X`
* `H[X | Y ← y] = Hm[(ℙ[| Y ⁻¹' {y}]).map X]`
* `H[X | Y] = condEntropy X Y`, such that `H[X | Y] = (volume.map Y)[fun y ↦ H[X | Y ← y]]`
* `I[X : Y] = mutualInformation X Y`

All notations except for `Hm[]` have variants where we can specify the measure (which is otherwise
supposed to be `volume`). For example `H[X ; μ]` and `I[X : Y ; μ]` instead of `H[X]` and
`I[X : Y]` respectively.

-/

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

section aux_lemmas

-- seems reasonable for Mathlib?
attribute [pp_dot] Measure.map

-- todo: is this somewhere?
lemma integral_eq_sum {S E : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
     (μ : Measure S) [IsFiniteMeasure μ] (f : S → E) :
    ∫ x, f x ∂μ = ∑ x, (μ {x}).toReal • (f x) := by
  conv_lhs => rw [← Measure.sum_smul_dirac μ]
  have hf : Integrable f μ := integrable_of_fintype _ _
  have hf' : Integrable f (Measure.sum fun a ↦ μ {a} • Measure.dirac a) := by
    rwa [Measure.sum_smul_dirac μ]
  rw [integral_sum_measure hf']
  simp_rw [integral_smul_measure, integral_dirac]
  rw [tsum_fintype]

/-- `μ[|s]` is always a finite measure. -/
instance cond_isFiniteMeasure {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    (s : Set α) : IsFiniteMeasure (μ[|s]) := by
  constructor
  simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, MeasurableSet.univ,
    Measure.restrict_apply, Set.univ_inter, smul_eq_mul, ProbabilityTheory.cond,
    ← ENNReal.div_eq_inv_mul]
  exact ENNReal.div_self_le_one.trans_lt ENNReal.one_lt_top

lemma cond_eq_zero_of_measure_zero {α : Type*} {_ : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hμs : μ s = 0) :
    μ[|s] = 0 := by
  have : μ.restrict s = 0 := by simp [hμs]
  simp [ProbabilityTheory.cond, this]

lemma measure_preimage_fst_singleton_eq_sum {S T : Type*} {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] [Fintype T] {_ : MeasurableSpace T}
    [MeasurableSingletonClass T] (μ : Measure (S × T)) (x : S) :
    μ (Prod.fst ⁻¹' {x}) = ∑ y : T, μ {(x, y)} := by
  have : Prod.fst ⁻¹' {x} = ⋃ y : T, {(x, y)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.iUnion_singleton_eq_range,
      Set.mem_range]
    exact ⟨fun h ↦ ⟨y.2, by rw [← h]⟩, fun ⟨b, h⟩ ↦ by rw [← h]⟩
  rw [this, measure_iUnion, tsum_eq_sum]
  · simp
  · intro a a' haa'
    rw [Function.onFun, Set.disjoint_iff]
    intro su
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, and_imp]
    intro h1 h2
    rw [h2] at h1
    simp only [Prod.mk.injEq, true_and] at h1
    exact haa' h1.symm
  · simp

lemma measure_preimage_snd_singleton_eq_sum {S T : Type*} [Fintype S] {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] {_ : MeasurableSpace T}
    [MeasurableSingletonClass T] (μ : Measure (S × T)) (y : T) :
    μ (Prod.snd ⁻¹' {y}) = ∑ x : S, μ {(x, y)} := by
  have : Prod.snd ⁻¹' {y} = ⋃ x : S, {(x, y)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.iUnion_singleton_eq_range,
      Set.mem_range]
    exact ⟨fun h ↦ ⟨y.1, by rw [← h]⟩, fun ⟨b, h⟩ ↦ by rw [← h]⟩
  rw [this, measure_iUnion, tsum_eq_sum]
  · simp
  · intro a a' haa'
    rw [Function.onFun, Set.disjoint_iff]
    intro su
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, and_imp]
    intro h1 h2
    rw [h2] at h1
    simp only [Prod.mk.injEq, and_true] at h1
    exact haa' h1.symm
  · simp

end aux_lemmas


/-- Give all finite types the discrete sigma-algebra by default. -/
instance Fintype.instMeasurableSpace [Fintype S] : MeasurableSpace S := ⊤

namespace ProbabilityTheory

variable {Ω S T U: Type*} [mΩ : MeasurableSpace Ω]
  [Fintype S] [Fintype T] [Fintype U] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]

section measureEntropy

variable {μ : Measure S}

/-- Entropy of a measure on a finite measurable space.

We normalize the measure by `(μ Set.univ)⁻¹` to extend the entropy definition to finite measures.
What we really want to do is deal with `μ=0` or `IsProbabilityMeasure μ`, but we don't have
a typeclass for that (we could create one though).
The added complexity in the expression is not an issue because if `μ` is a probability measure,
a call to `simp` will simplify `(μ Set.univ)⁻¹ • μ` to `μ`. -/
noncomputable
def measureEntropy (μ : Measure S := by volume_tac) : ℝ :=
  ∑ s, negIdMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal

lemma measureEntropy_def (μ : Measure S) :
    measureEntropy μ = ∑ s, negIdMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal := rfl

lemma measureEntropy_def' (μ : Measure S) :
    measureEntropy μ = ∑ s, negIdMulLog (((μ.real Set.univ) ⁻¹ • μ.real) {s}) := by
  rw [measureEntropy_def]
  congr! with s
  simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, measureReal_def, ENNReal.toReal_inv]

notation:max "Hm[" μ "]" => measureEntropy μ

@[simp]
lemma measureEntropy_zero : Hm[(0 : Measure S)] = 0 := by
  simp [measureEntropy]

lemma measureEntropy_of_not_isFiniteMeasure (h : ¬ IsFiniteMeasure μ) :
    Hm[μ] = 0 := by
  simp [measureEntropy, not_isFiniteMeasure_iff.mp h]

lemma measureEntropy_of_isProbabilityMeasure (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = ∑ s, negIdMulLog (μ {s}).toReal := by
  simp [measureEntropy]

lemma measureEntropy_univ_smul : Hm[(μ Set.univ)⁻¹ • μ] = Hm[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap
  · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ =>
    rw [measureEntropy_def]
    simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul,
      ENNReal.toReal_mul]
    rw [ENNReal.inv_mul_cancel]
    · simp only [inv_one, ENNReal.one_toReal, one_mul]
      simp [measureEntropy]
    · simp [hμ.out]
    · exact measure_ne_top _ _

lemma measureEntropy_nonneg (μ : Measure S) : 0 ≤ Hm[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap; · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
  refine Finset.sum_nonneg (fun s _ ↦ negIdMulLog_nonneg ENNReal.toReal_nonneg ?_)
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => exact prob_le_one

lemma measureEntropy_le_card_aux [MeasurableSingletonClass S]
    (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] ≤ log (Fintype.card S) := by
  cases isEmpty_or_nonempty S with
  | inl h =>
    have : μ = 0 := Subsingleton.elim _ _
    simp [Fintype.card_eq_zero, this]
  | inr h =>
    set N := Fintype.card S
    rw [measureEntropy_def']
    simp only [IsProbabilityMeasure.measureReal_univ, inv_one, one_smul]
    calc ∑ x, negIdMulLog (μ.real {x})
      = ∑ x, negIdMulLog (μ.real {x}) := rfl
    _ = N * ∑ x, (N : ℝ)⁻¹ * negIdMulLog (μ.real {x}) := by
        rw [Finset.mul_sum]
        congr with x
        rw [← mul_assoc, mul_inv_cancel, one_mul]
        simp
    _ ≤ N * negIdMulLog (∑ x : S, (N : ℝ)⁻¹ * μ.real {x}) := by
        gcongr
        refine sum_negIdMulLog_le (by simp) ?_ (fun _ ↦ ENNReal.toReal_nonneg)
        simp [Finset.card_univ]
    _ = N * negIdMulLog ((N : ℝ)⁻¹) := by
        congr
        rw [← Finset.mul_sum]
        simp
    _ = - log ((N : ℝ)⁻¹) := by
        simp [negIdMulLog]
    _ = log (Fintype.card S) := by simp [Finset.card_univ]

lemma measureEntropy_eq_card_iff_measureReal_eq_aux [MeasurableSingletonClass S]
    (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = log (Fintype.card S) ↔ (∀ s : S, μ.real {s} = (Fintype.card S : ℝ)⁻¹) := by
  cases isEmpty_or_nonempty S with
  | inl h =>
    have : μ = 0 := Subsingleton.elim _ _
    simp [Fintype.card_eq_zero, this]
  | inr h =>
    -- multiply LHS equation through by `N⁻¹`
    set N := Fintype.card S
    have hN : (N:ℝ)⁻¹ ≠ 0 := by positivity
    rw [← mul_right_inj' hN]
    -- setup to use equality case of Jensen
    let w (_ : S) := (N:ℝ)⁻¹
    have hw1 : ∀ s ∈ Finset.univ, 0 < w s := by intros; positivity
    have hw2 : ∑ s : S, w s = 1 := by simp [Finset.card_univ]
    let p (s : S) := μ.real {s}
    have hp : ∀ s ∈ Finset.univ, 0 ≤ p s := by intros; positivity
    -- use equality case of Jensen
    convert sum_negIdMulLog_eq_aux2 hw1 hw2 hp using 2
    · simp [measureEntropy_def', Finset.mul_sum]
    · simp [negIdMulLog, ←Finset.mul_sum]
    · rw [← Finset.smul_sum]
      simp

lemma measureEntropy_eq_card_iff_measure_eq_aux [MeasurableSingletonClass S]
    (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = log (Fintype.card S) ↔ (∀ s : S, μ {s} = (Fintype.card S : ℝ≥0)⁻¹) := by
  rw [measureEntropy_eq_card_iff_measureReal_eq_aux]
  congr! with s
  rw [measureReal_def, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ {s})]
  congr!
  simp

lemma measureEntropy_le_log_card [MeasurableSingletonClass S] (μ : Measure S) :
    Hm[μ] ≤ log (Fintype.card S) := by
  have h_log_card_nonneg : 0 ≤ log (Fintype.card S) := by
    cases isEmpty_or_nonempty S with
    | inl h =>
      rw [Fintype.card_eq_zero]
      simp
    | inr h =>
      refine log_nonneg ?_
      simp only [Nat.one_le_cast]
      exact Fintype.card_pos
  cases eq_zero_or_neZero μ with
  | inl hμ =>
    simp only [hμ, measureEntropy_zero]
    exact h_log_card_nonneg
  | inr hμ =>
    by_cases hμ_fin : IsFiniteMeasure μ
    swap;
    · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
      exact h_log_card_nonneg
    rw [← measureEntropy_univ_smul]
    exact measureEntropy_le_card_aux _

lemma measureEntropy_eq_card_iff_measureReal_eq [MeasurableSingletonClass S] [IsFiniteMeasure μ]
    [NeZero μ] :
    Hm[μ] = log (Fintype.card S) ↔
    (∀ s : S, μ.real {s} = μ.real Set.univ / Fintype.card S) := by
  rw [← measureEntropy_univ_smul]
  convert measureEntropy_eq_card_iff_measureReal_eq_aux ((μ Set.univ)⁻¹ • μ) using 2 with s
  simp only [measureReal_smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_inv, inv_mul_eq_iff_eq_mul₀ (by exact measureReal_univ_ne_zero),
    div_eq_mul_inv]
  rfl

lemma measureEntropy_eq_card_iff_measure_eq [MeasurableSingletonClass S] [IsFiniteMeasure μ]
    [NeZero μ] :
    Hm[μ] = log (Fintype.card S) ↔
    (∀ s : S, μ {s} = μ Set.univ / Fintype.card S) := by
  obtain h | h := isEmpty_or_nonempty S
  · have : μ = 0 := Subsingleton.elim _ _
    simp [Fintype.card_eq_zero, this]
  rw [div_eq_mul_inv, measureEntropy_eq_card_iff_measureReal_eq]
  congr! with s
  rw [measureReal_def, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ {s})]
  · rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
    rfl
  · finiteness

lemma measureEntropy_map_of_injective [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (μ : Measure S) (f : S → T) (hf : Function.Injective f)  :
    Hm[μ.map f] = Hm[μ] := by
  have hf_m : Measurable f := measurable_of_finite f
  have : μ.map f Set.univ = μ Set.univ := by
      rw [Measure.map_apply hf_m MeasurableSet.univ]
      simp
  simp_rw [measureEntropy_def, Measure.smul_apply,
    Measure.map_apply hf_m (measurableSet_singleton _)]
  rw [this]
  classical
  have : ∑ x : T, negIdMulLog (ENNReal.toReal ((μ Set.univ)⁻¹ • μ (f ⁻¹' {x})))
      = ∑ x in Finset.univ.image f,
        negIdMulLog (ENNReal.toReal ((μ Set.univ)⁻¹ • μ (f ⁻¹' {x}))) := by
    rw [← Finset.sum_subset]
    · exact Finset.subset_univ _
    · intro y _ hy
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hy
      suffices f ⁻¹' {y} = ∅ by simp [this]
      rw [Set.preimage_eq_empty_iff]
      simp [hy]
  rw [this, Finset.sum_image]
  · simp only [smul_eq_mul, ENNReal.toReal_mul]
    congr with x
    congr with x'
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ hf h, fun h ↦ by rw [h]⟩
  · simp only [Finset.mem_univ, forall_true_left]
    exact hf

end measureEntropy

section measureMutualInfo

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]

noncomputable
def measureMutualInfo (μ : Measure (S × T) := by volume_tac) : ℝ :=
  Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ]

notation:100 "Im[" μ "]" => measureMutualInfo μ

lemma measureMutualInfo_def (μ : Measure (S × T)) :
    Im[μ] = Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ] := rfl

--todo: do this in mathlib? Others: Measure.withDensity, Measure.map
attribute [pp_dot] ENNReal.toReal

@[simp]
lemma measureMutualInfo_zero_measure : Im[(0 : Measure (S × T))] = 0 := by
  simp [measureMutualInfo]

lemma measureMutualInfo_swap (μ : Measure (S × T)) :
    Im[μ.map Prod.swap] = Im[μ] := by
  rw [measureMutualInfo_def, add_comm, Measure.map_map measurable_snd measurable_swap,
    Measure.map_map measurable_fst measurable_swap]
  congr 1
  simp_rw [measureEntropy_def, Measure.map_apply measurable_swap MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply,
    smul_eq_mul, ENNReal.toReal_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  congr with x
  congr with y
  congr 2
  rw [Measure.map_apply measurable_swap (measurableSet_singleton _),
    ← Set.singleton_prod_singleton, Set.preimage_swap_prod, Set.singleton_prod_singleton]

lemma measureMutualInfo_nonneg (μ : Measure (S × U)) [IsProbabilityMeasure μ] :
    0 ≤ Im[μ] := by
  have : IsProbabilityMeasure (μ.map Prod.fst) :=
    isProbabilityMeasure_map measurable_fst.aemeasurable
  have : IsProbabilityMeasure (μ.map Prod.snd) :=
    isProbabilityMeasure_map measurable_snd.aemeasurable
  simp_rw [measureMutualInfo_def, measureEntropy_of_isProbabilityMeasure, negIdMulLog]
  have h1 : ∀ y, (μ.map Prod.fst {y}).toReal = ∑ z : U, (μ {(y, z)}).toReal := by
    intro y
    rw [Measure.map_apply measurable_fst (measurableSet_singleton _), ← ENNReal.toReal_sum]
    swap; · simp [measure_ne_top]
    rw [← measure_preimage_fst_singleton_eq_sum]
  have h2 : ∀ z, (μ.map Prod.snd {z}).toReal = ∑ y : S, (μ {(y, z)}).toReal := by
    intro z
    rw [Measure.map_apply measurable_snd (measurableSet_singleton _), ← ENNReal.toReal_sum]
    swap; · simp [measure_ne_top]
    rw [← measure_preimage_snd_singleton_eq_sum]
  simp_rw [h1, h2]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (γ := U)]
  simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← mul_add, ← mul_sub, neg_mul,
    Finset.sum_neg_distrib, ← h1, ← h2]
  have h_fst_ne_zero : ∀ p, μ {p} ≠ 0 → (μ.map Prod.fst {p.1}).toReal ≠ 0 := by
    intro p hp
    rw [Measure.map_apply measurable_fst (measurableSet_singleton _)]
    simp only [Set.mem_singleton_iff, ne_eq, ENNReal.toReal_eq_zero_iff, measure_ne_top μ,
      or_false]
    refine fun h_eq_zero ↦ hp ?_
    refine measure_mono_null ?_ h_eq_zero
    simp
  have h_snd_ne_zero : ∀ p, μ {p} ≠ 0 → (μ.map Prod.snd {p.2}).toReal ≠ 0 := by
    intro p hp
    rw [Measure.map_apply measurable_snd (measurableSet_singleton _)]
    simp only [Set.mem_singleton_iff, ne_eq, ENNReal.toReal_eq_zero_iff, measure_ne_top μ,
      or_false]
    refine fun h_eq_zero ↦ hp ?_
    refine measure_mono_null ?_ h_eq_zero
    simp
  have : ∀ a b, (μ {(a, b)}).toReal
        * (log (μ.map Prod.fst {a}).toReal
          + log (μ.map Prod.snd {b}).toReal - log (μ {(a, b)}).toReal)
      = -(μ {(a, b)}).toReal * (log (((μ.map Prod.fst {a}).toReal
        * (μ.map Prod.snd {b}).toReal)⁻¹ * (μ {(a, b)}).toReal)) := by
    intro a b
    by_cases h_zero : μ {(a, b)} = 0
    · simp only [h_zero, ENNReal.zero_toReal, log_zero, sub_zero, zero_mul, div_zero, mul_zero]
    rw [log_mul]
    rotate_left
    · refine inv_ne_zero ?_
      exact mul_ne_zero (h_fst_ne_zero _ h_zero) (h_snd_ne_zero _ h_zero)
    · simp [ENNReal.toReal_eq_zero_iff, h_zero, measure_ne_top μ]
    rw [log_inv]
    rw [neg_mul_comm, neg_add, neg_neg, sub_eq_add_neg, log_mul]
    · exact h_fst_ne_zero (a, b) h_zero
    · exact h_snd_ne_zero (a, b) h_zero
  simp_rw [this]
  rw [neg_nonneg]
  calc ∑ a : S, ∑ b : U, -(μ {(a, b)}).toReal *
      log (((μ.map Prod.fst {a}).toReal * (μ.map Prod.snd {b}).toReal)⁻¹ * (μ {(a, b)}).toReal)
    = ∑ p : S × U, -(μ {p}).toReal *
      log (((μ.map Prod.fst {p.1}).toReal * (μ.map Prod.snd {p.2}).toReal)⁻¹ * (μ {p}).toReal) := by
        rw [Fintype.sum_prod_type]
  _ = ∑ p : S × U, ((μ.map Prod.fst {p.1}).toReal * (μ.map Prod.snd {p.2}).toReal)
      * negIdMulLog (((μ.map Prod.fst {p.1}).toReal
      * (μ.map Prod.snd {p.2}).toReal)⁻¹ * (μ {p}).toReal) := by
        congr with p
        by_cases hp : μ {p} = 0
        · simp [hp]
        rw [negIdMulLog, neg_mul, neg_mul, ← neg_mul_comm, ← mul_assoc, ← mul_assoc, neg_mul,
          mul_inv_cancel, neg_mul, one_mul, neg_mul]
        exact mul_ne_zero (h_fst_ne_zero p hp) (h_snd_ne_zero p hp)
  _ ≤ negIdMulLog (∑ p : S × U, ((μ.map Prod.fst {p.1}).toReal * (μ.map Prod.snd {p.2}).toReal)
      * (((μ.map Prod.fst {p.1}).toReal * (μ.map Prod.snd {p.2}).toReal)⁻¹ * (μ {p}).toReal)) := by
        refine sum_negIdMulLog_le ?_ ?_ ?_
        · exact fun _ ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        · rw [Fintype.sum_prod_type]
          simp only
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
          simp
        · refine fun _ ↦ mul_nonneg (inv_nonneg.mpr ?_) ENNReal.toReal_nonneg
          exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  _ = negIdMulLog (∑ p : S × U, (μ {p}).toReal) := by
        congr with p
        by_cases hp : (μ {p}).toReal = 0
        · simp only [mul_inv_rev, hp, mul_zero]
        rw [ENNReal.toReal_eq_zero_iff] at hp
        push_neg at hp
        rw [← mul_assoc, mul_inv_cancel, one_mul]
        exact mul_ne_zero (h_fst_ne_zero p hp.1) (h_snd_ne_zero p hp.1)
  _ = negIdMulLog 1 := by rw [sum_toReal_measure_singleton, measure_univ, ENNReal.one_toReal]
  _ = 0 := negIdMulLog_one

end measureMutualInfo

section entropy

variable {μ : Measure Ω} {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

/-- Entropy of a random variable with values in a finite measurable space. -/
noncomputable
def entropy (X : Ω → S) (μ : Measure Ω := by volume_tac) := Hm[μ.map X]

notation3:max "H[" X "; " μ "]" => entropy X μ
notation3:max "H[" X "]" => entropy X volume
notation3:max "H[" X "|" Y "←" y "; " μ "]" => entropy X (μ[|Y ⁻¹' {y}])
notation3:max "H[" X "|" Y "←" y "]" => entropy X (ℙ[|Y ⁻¹' {y}])

lemma entropy_def (X : Ω → S) (μ : Measure Ω) : entropy X μ = Hm[μ.map X] := rfl

@[simp]
lemma entropy_zero_measure (X : Ω → S) : H[X ; (0 : Measure Ω)] = 0 := by simp [entropy]

lemma entropy_congr {X X' : Ω → S} (h : X =ᵐ[μ] X') : H[X ; μ] = H[X' ; μ] := by
  rw [entropy_def, Measure.map_congr h, entropy_def]

lemma entropy_nonneg (X : Ω → S) (μ : Measure Ω) : 0 ≤ entropy X μ := measureEntropy_nonneg _

lemma IdentDistrib.entropy_eq {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} {X' : Ω' → S}
    (h : IdentDistrib X X' μ μ') : entropy X μ = entropy X' μ' := by
  simp [entropy_def, h.map_eq]

lemma entropy_le_log_card [MeasurableSingletonClass S]
    (X : Ω → S) (μ : Measure Ω) : entropy X μ ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card _

lemma entropy_eq_sum (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    entropy X μ = ∑ x, negIdMulLog (μ.map X {x}).toReal := by
  have : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  rw [entropy_def, measureEntropy_of_isProbabilityMeasure]

lemma entropy_cond_eq_sum (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] (y : T) :
    H[X | Y ← y ; μ] = ∑ x, negIdMulLog ((μ[|Y ⁻¹' {y}]).map X {x}).toReal := by
  by_cases hy : μ (Y ⁻¹' {y}) = 0
  · rw [entropy_def, cond_eq_zero_of_measure_zero hy]
    simp
  · have : IsProbabilityMeasure (μ[|Y ⁻¹' {y}]) := cond_isProbabilityMeasure _ hy
    rw [entropy_eq_sum hX]

/-- If $X$, $Y$ are $S$-valued and $T$-valued random variables, and $Y = f(X)$ almost surely for
some injection $f: S \to T$, then $H[X] = H[Y]$. -/
lemma entropy_comp_of_injective [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (μ : Measure Ω) (hX : Measurable X) (f : S → T) (hf : Function.Injective f) :
    H[f ∘ X ; μ] = H[X ; μ] := by
  have hf_m : Measurable f := measurable_of_finite f
  rw [entropy_def, ← Measure.map_map hf_m hX, measureEntropy_map_of_injective _ _ hf,
    entropy_def]

/-- The assertion that the law of $X$ is the uniform probability measure on a finite set $H$.  While in applications $H$ will be non-empty finite set, $X$ measurable, and and $μ$ a probability measure, it could be technically convenient to have a definition that works even without these hypotheses.  (For instance, isUniform would be well-defined, but false, for infinite H)   -/
def isUniform (H: Set S) (X : Ω → S) (μ : Measure Ω) : Prop := sorry

/-- Uniform distributions exist -/
lemma exists_uniform (H : Finset S) [h: Nonempty H] : ∃ X : S → S, ∃ μ: Measure S, IsProbabilityMeasure μ ∧ Measurable X ∧ isUniform H X μ ∧ ∀ ω : S, X ω ∈ H := by sorry

/-- If $X$ is uniformly distributed on $H$, then $H[X] = \log |H|$.  May need some non-degeneracy and measurability conditions. -/
lemma entropy_of_uniform (H: Finset S) (X : Ω → S) (μ : Measure Ω) (hX : isUniform H X μ) :
    H[X ; μ] = log (Fintype.card H) := sorry

/-- If $X$ is $S$-valued random variable, then $H[X] = \log |S|$ if and only if $X$ is uniformly
distributed. -/
lemma entropy_eq_log_card (X : Ω → S) (μ : Measure Ω) : (entropy X μ = log (Fintype.card S)) ↔ (∀ s : S, μ.map X {s} = (μ Set.univ) / (Fintype.card S)) := by
  -- TODO: which of these side conditions are actually needed?
  have : MeasurableSingletonClass S := sorry
  have : IsFiniteMeasure (μ.map X) := sorry
  have : NeZero (μ.map X) := sorry
  have hX : Measurable X := sorry
  rw [entropy_def, measureEntropy_eq_card_iff_measure_eq, Measure.map_apply hX MeasurableSet.univ]
  simp

/-- If $X$ is an $S$-valued random variable, then there exists $s \in S$ such that
$P[X=s] \geq \exp(-H[X])$. -/
lemma prob_ge_exp_neg_entropy (X : Ω → S) (μ : Measure Ω) : ∃ s : S, μ.map X {s} ≥ (μ Set.univ) * (rexp (- entropy X μ )).toNNReal := by sorry

abbrev prod {Ω S T : Type*} ( X : Ω → S ) ( Y : Ω → T ) (ω : Ω) : S × T := (X ω, Y ω)

notation3:100 "⟨" X ", " Y "⟩" => prod X Y

lemma entropy_comm [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨ X, Y ⟩; μ] = H[⟨ Y, X ⟩ ; μ] := by
  change H[⟨ X, Y ⟩ ; μ] = H[Prod.swap ∘ ⟨ X, Y ⟩ ; μ]
  exact (entropy_comp_of_injective μ (hX.prod_mk hY) Prod.swap Prod.swap_injective).symm

lemma entropy_assoc [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) :
    H[⟨ X, ⟨ Y, Z ⟩ ⟩; μ] = H[⟨ ⟨X, Y⟩ , Z ⟩ ; μ] := by sorry

end entropy

section condEntropy

variable {X : Ω → S} {Y : Ω → T}

/-- Conditional entropy of a random variable w.r.t. another.
This is the expectation under the law of `Y` of the entropy of the law of `X` conditioned on the
event `Y = y`. -/
noncomputable
def condEntropy (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  (μ.map Y)[fun y ↦ H[X | Y ← y ; μ]]

lemma condEntropy_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    condEntropy X Y μ = (μ.map Y)[fun y ↦ H[X | Y ← y ; μ]] := rfl

notation3:max "H[" X "|" Y "; " μ "]" => condEntropy X Y μ
notation3:max "H[" X "|" Y "]" => condEntropy X Y volume

@[simp]
lemma condEntropy_zero_measure (X : Ω → S) (Y : Ω → T) : H[X | Y ; (0 : Measure Ω)] = 0 :=
  by simp [condEntropy]

lemma condEntropy_nonneg (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : 0 ≤ H[X | Y ; μ] :=
  integral_nonneg (fun _ ↦ measureEntropy_nonneg _)

lemma condEntropy_le_log_card [MeasurableSingletonClass S]
    (X : Ω → S) (Y : Ω → T) (hY : Measurable Y) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    H[X | Y ; μ] ≤ log (Fintype.card S) := by
  refine (integral_mono_of_nonneg ?_ (integrable_const (log (Fintype.card S))) ?_).trans ?_
  · exact ae_of_all _ (fun _ ↦ entropy_nonneg _ _)
  · exact ae_of_all _ (fun _ ↦ entropy_le_log_card _ _)
  · have : IsProbabilityMeasure (μ.map Y) := isProbabilityMeasure_map hY.aemeasurable
    simp

lemma condEntropy_eq_sum [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω → T) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
    H[X | Y ; μ] = ∑ y, (μ.map Y {y}).toReal * H[X | Y ← y ; μ] := by
  rw [condEntropy_def, integral_eq_sum]
  simp_rw [smul_eq_mul]

lemma condEntropy_eq_sum_sum [MeasurableSingletonClass T] (hX : Measurable X) (Y : Ω → T)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    H[X | Y ; μ]
      = ∑ y, ∑ x, (μ.map Y {y}).toReal * negIdMulLog ((μ[|Y ⁻¹' {y}]).map X {x}).toReal := by
  rw [condEntropy_eq_sum]
  congr with y
  rw [entropy_cond_eq_sum hX, Finset.mul_sum]

lemma condEntropy_eq_sum_prod [MeasurableSingletonClass T] (hX : Measurable X) (Y : Ω → T)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    H[X | Y ; μ] = ∑ p : S × T,
      (μ.map Y {p.2}).toReal * negIdMulLog ((μ[|Y ⁻¹' {p.2}]).map X {p.1}).toReal := by
  have h_prod : (Finset.univ : Finset (S × T)) = (Finset.univ : Finset S) ×ˢ Finset.univ := rfl
  rw [condEntropy_eq_sum_sum hX Y, h_prod, Finset.sum_product_right]

/-- If $X: \Omega \to S$, $Y: \Omega \to T$ are random variables, and $f: T \times S → U$ is injective for each fixed $t \in T$, then $H[f(Y,X)|Y] = H[X|Y]$.  Thus for instance $H[X-Y|Y]=H[X|Y]$.-/
lemma condEntropy_of_inj_map [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (f : T → S → U) (hf : ∀ t : T, Function.Injective (f t)) :
    H[(fun ω ↦ f (Y ω) (X ω)) | Y ; μ] = H[X | Y ; μ] := by
  rw [condEntropy_eq_sum, condEntropy_eq_sum]
  have : ∀ y, H[fun ω ↦ f (Y ω) (X ω)|Y←y; μ] = H[(f y ∘ X) | Y ← y ; μ] := by
    intro y
    refine entropy_congr ?_
    have : ∀ᵐ ω ∂μ[|Y ⁻¹' {y}], Y ω = y := by
      rw [ae_iff, cond_apply _ (hY (measurableSet_singleton _))]
      have : {a | ¬Y a = y} = (Y ⁻¹' {y})ᶜ := by ext; simp
      rw [this, Set.inter_compl_self, measure_empty, mul_zero]
    filter_upwards [this] with ω hω
    rw [hω]
    simp
  simp_rw [this]
  congr with y
  rw [entropy_comp_of_injective _ hX (f y) (hf y)]

/- The following is a weaker version of the above lemma in which f is independent of Y. -/

lemma condEntropy_comp_of_injective [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (μ : Measure Ω) (hX : Measurable X) (f : S → U) (hf : Function.Injective f) :
    H[f ∘ X | Y ; μ] = H[X | Y ; μ] :=
  integral_congr_ae (ae_of_all _ (fun _ ↦ entropy_comp_of_injective _ hX f hf))

/-- If $X: \Omega \to S$ and $Y: \Omega \to T$ are random variables, and $f: T \to U$ is an injection then $H[X|f(Y)] = H[X|Y]$.
 -/
lemma condEntropy_of_inj_map' [MeasurableSingletonClass S] (μ : Measure Ω) (hX : Measurable X) (hY : Measurable Y) (f : T → U) (hf : Function.Injective f) :
    H[X | f ∘ Y ; μ] = H[X | Y ; μ] := sorry

lemma condEntropy_comm {Z : Ω → U} [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨ X, Y ⟩ | Z ; μ] = H[⟨ Y, X ⟩ | Z; μ] := by
  change H[⟨ X, Y ⟩ | Z ; μ] = H[Prod.swap ∘ ⟨ X, Y ⟩ | Z; μ]
  exact (condEntropy_comp_of_injective μ (hX.prod_mk hY) Prod.swap Prod.swap_injective).symm

end condEntropy

section pair
variable {U : Type*} {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
  [Fintype U] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  {μ : Measure Ω}

lemma measure_prod_singleton_eq_mul [IsFiniteMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) {p : S × T} :
    (μ.map (⟨ X, Y ⟩) {p}).toReal
      = (μ.map Y {p.2}).toReal * ((μ[|Y ⁻¹' {p.2}]).map X {p.1}).toReal := by
  have hp_prod : {p} = {p.1} ×ˢ {p.2} := by simp
  rw [Measure.map_apply (hX.prod_mk hY) (measurableSet_singleton p)]
  by_cases hpY : μ (Y ⁻¹' {p.2}) = 0
  · rw [cond_eq_zero_of_measure_zero hpY]
    simp only [aemeasurable_zero_measure, not_true, Measure.map_zero, Measure.zero_toOuterMeasure,
      OuterMeasure.coe_zero, Pi.zero_apply, ENNReal.zero_toReal, mul_zero]
    suffices (μ (⟨ X, Y ⟩⁻¹' ({p.1} ×ˢ {p.2}))).toReal = 0 by convert this
    rw [Set.mk_preimage_prod, ENNReal.toReal_eq_zero_iff]
    exact Or.inl (measure_mono_null (Set.inter_subset_right _ _) hpY)
  rw [Measure.map_apply hY (measurableSet_singleton p.2)]
  simp_rw [Measure.map_apply hX (measurableSet_singleton _)]
  simp_rw [cond_apply _ (hY (measurableSet_singleton _))]
  rw [ENNReal.toReal_mul, ← mul_assoc, ENNReal.toReal_inv, mul_inv_cancel, one_mul, hp_prod,
    Set.mk_preimage_prod, Set.inter_comm]
  rw [ENNReal.toReal_ne_zero]; exact ⟨hpY, measure_ne_top _ _⟩

lemma negIdMulLog_measure_prod_singleton [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y)
   {p : S × T} :
    negIdMulLog ((μ.map (⟨ X, Y ⟩)) {p}).toReal
      = - ((μ[|Y ⁻¹' {p.2}]).map X {p.1}).toReal
          * (μ.map Y {p.2}).toReal* log (μ.map Y {p.2}).toReal
        - (μ.map Y {p.2}).toReal * ((μ[|Y ⁻¹' {p.2}]).map X {p.1}).toReal
          * log ((μ[|Y ⁻¹' {p.2}]).map X {p.1}).toReal := by
  rw [measure_prod_singleton_eq_mul hX hY]
  by_cases hpY : μ (Y ⁻¹' {p.2}) = 0
  · rw [cond_eq_zero_of_measure_zero hpY]
    simp
  by_cases hpX : (μ[|Y ⁻¹' {p.2}]).map X {p.1} = 0
  · simp [hpX]
  rw [negIdMulLog, log_mul]
  · ring
  · rw [ENNReal.toReal_ne_zero]
    refine ⟨?_, measure_ne_top _ _⟩
    rwa [Measure.map_apply hY (measurableSet_singleton _)]
  · rw [ENNReal.toReal_ne_zero]
    refine ⟨hpX, measure_ne_top _ _⟩

lemma chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) :
    H[⟨ X, Y ⟩; μ] = H[Y ; μ] + H[X | Y ; μ] := by
  have : IsProbabilityMeasure (μ.map Y) := isProbabilityMeasure_map hY.aemeasurable
  have : IsProbabilityMeasure (μ.map (⟨ X, Y ⟩)) :=
    isProbabilityMeasure_map (hX.prod_mk hY).aemeasurable
  rw [entropy_def, measureEntropy_of_isProbabilityMeasure]
  simp_rw [negIdMulLog_measure_prod_singleton hX hY, sub_eq_add_neg, Finset.sum_add_distrib]
  congr
  · have h_prod : (Finset.univ : Finset (S × T)) = (Finset.univ : Finset S) ×ˢ Finset.univ := rfl
    rw [h_prod, Finset.sum_product_right, entropy_def, measureEntropy_of_isProbabilityMeasure]
    congr with y
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    by_cases hy : μ (Y ⁻¹' {y}) = 0
    · simp [cond_eq_zero_of_measure_zero hy, Measure.map_apply hY, hy]
    have : IsProbabilityMeasure (μ[|Y ⁻¹' {y}]) := cond_isProbabilityMeasure _ hy
    suffices ∑ x : S, ((μ[|Y ⁻¹' {y}]).map X {x}).toReal = 1 by
      rw [this, one_mul, ← neg_mul, negIdMulLog]
    simp [Measure.map_apply hX MeasurableSet.univ]
  · rw [condEntropy_eq_sum_prod hX]
    congr with p
    rw [negIdMulLog]
    ring

lemma chain_rule' (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) :
    H[⟨ X, Y ⟩; μ] = H[X ; μ] + H[Y  | X ; μ] := by
  rw [entropy_comm hX hY, chain_rule μ hY hX]

lemma cond_chain_rule_aux (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U) (z : U) :
    H[⟨ X, Y ⟩ | Z ← z ; μ] = H[Y | Z ← z ; μ] + H[X | Y ; μ[|Z ⁻¹' {z}]] := by
  by_cases hz : μ (Z ⁻¹' {z}) = 0
  · have : μ[|Z ⁻¹' {z}] = 0 := by exact cond_eq_zero_of_measure_zero hz
    simp [this]
  · have : IsProbabilityMeasure (μ[|Z ⁻¹' {z}]) := cond_isProbabilityMeasure _ hz
    exact chain_rule (μ[|Z ⁻¹' {z}]) hX hY

/--   If $X: \Omega \to S$, $Y: \Omega \to T$, $Z: \Omega \to U$ are random variables, then
$$ H[  X,Y | Z ] = H[Y | Z] + H[X|Y, Z].$$ -/
lemma cond_chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[⟨ X, Y ⟩ | Z ; μ] = H[Y | Z ; μ] + H[X | ⟨ Y, Z ⟩ ; μ] := by
  rw [condEntropy_def]
  simp_rw [cond_chain_rule_aux μ hX hY Z]
  rw [integral_add]
  rotate_left
  · sorry
  · sorry
  congr
  -- goal is `∫ z, H[X|Y; μ[|Z ⁻¹' {z}]] ∂(μ.map Z) = H[X|⟨ Y, Z ⟩; μ]`
  rw [condEntropy_def, integral_map hZ.aemeasurable, integral_map (hY.prod_mk hZ).aemeasurable]
  rotate_left
  · exact (measurable_of_countable _).stronglyMeasurable.aestronglyMeasurable
  · exact (measurable_of_countable _).stronglyMeasurable.aestronglyMeasurable
  simp_rw [condEntropy_def, integral_map hY.aemeasurable
    (measurable_of_countable _).stronglyMeasurable.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ (fun ω ↦ ?_))
  simp only
  sorry

lemma cond_chain_rule' (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[⟨ X, Y ⟩ | Z ; μ] = H[X | Z ; μ] + H[Y | ⟨ X, Z ⟩ ; μ] := by
    rw [condEntropy_comm hX hY, cond_chain_rule _ hY hX hZ]

/-- Data-processing inequality for the entropy. -/
lemma entropy_comp_le {U : Type*} [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) {f : S → U} (hf : Measurable f) :
    H[f ∘ X ; μ] ≤ H[X ; μ] := by
  have : H[X ; μ] = H[⟨ X, f ∘ X ⟩ ; μ] := by
    refine (entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) ?_).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule _ hX (hf.comp hX)]
  simp only [le_add_iff_nonneg_right]
  exact condEntropy_nonneg X (f ∘ X) μ

end pair

section mutualInformation

variable {U : Type*} [Fintype U] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

/-- Mutual information (TODO docstring). -/
noncomputable
def mutualInformation (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[⟨ X, Y ⟩ ; μ]

lemma mutualInformation_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
  mutualInformation X Y μ = H[X ; μ] + H[Y ; μ] - H[⟨ X, Y ⟩ ; μ] := rfl

notation3:max "I[" X ":" Y ";" μ "]" => mutualInformation X Y μ
notation3:max "I[" X ":" Y "]" => mutualInformation X Y volume

lemma mutualInformation_eq_entropy_sub_condEntropy [MeasurableSingletonClass S]
    [MeasurableSingletonClass T] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  rw [mutualInformation_def, chain_rule μ hX hY]
  abel

lemma mutualInformation_comm [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    I[X : Y ; μ] = I[Y : X ; μ] := by simp_rw [mutualInformation, add_comm, entropy_comm hX hY]

lemma mutualInformation_nonneg [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    0 ≤ I[X : Y ; μ] := by
  have : IsProbabilityMeasure (μ.map (⟨ X, Y ⟩)) :=
    isProbabilityMeasure_map (hX.prod_mk hY).aemeasurable
  simp_rw [mutualInformation_def, entropy_def]
  have h_fst : μ.map X = (μ.map (⟨ X, Y ⟩)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prod_mk hY)]
    congr
  have h_snd : μ.map Y = (μ.map (⟨ X, Y ⟩)).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prod_mk hY)]
    congr
  rw [h_fst, h_snd]
  exact measureMutualInfo_nonneg _

/-- Subadditivity of entropy. -/
lemma entropy_pair_le_add [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    H[⟨ X, Y ⟩ ; μ] ≤ H[X ; μ] + H[Y ; μ] :=
  sub_nonneg.1 $ mutualInformation_nonneg hX hY _

noncomputable
def condMutualInformation (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω := by volume_tac) :
    ℝ := (μ.map Z)[fun z ↦ H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[⟨ X, Y ⟩ | Z ← z ; μ]]

lemma condMutualInformation_def (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) :
    condMutualInformation X Y Z μ = (μ.map Z)[fun z ↦
      H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[⟨ X, Y ⟩ | Z ← z ; μ]] := rfl

notation3:max "I[" X ":" Y "|" Z ";" μ "]" => condMutualInformation X Y Z μ
notation3:max "I[" X ":" Y "|" Z "]" => condMutualInformation X Y Z volume

lemma condMutualInformation_eq_integral_mutualInformation :
    I[X : Y | Z ; μ] = (μ.map Z)[fun z ↦ I[X : Y ; μ[|Z ⁻¹' {z}]]] := rfl

lemma condMutualInformation_comm [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U) (μ : Measure Ω) :
    I[X : Y | Z ; μ] = I[Y : X | Z ; μ] := by
  simp_rw [condMutualInformation_def, add_comm, entropy_comm hX hY]

lemma condMutualInformation_nonneg [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    0 ≤ I[X : Y | Z ; μ] := by
  refine integral_nonneg (fun z ↦ ?_)
  by_cases hz : μ (Z ⁻¹' {z}) = 0
  · have : μ[|Z ⁻¹' {z}] = 0 := cond_eq_zero_of_measure_zero hz
    simp [this]
  have : IsProbabilityMeasure (μ[|Z ⁻¹' {z}]) := cond_isProbabilityMeasure μ hz
  exact mutualInformation_nonneg hX hY _

/-- $$ I[X:Y|Z] := H[X|Z] + H[Y|Z] - H[X,Y|Z].$$ -/
lemma condMutualInformation_eq :
    I[X : Y | Z ; μ] = H[X | Z ; μ] - H[⟨X, Y⟩ | Z ; μ] := by sorry

section IsProbabilityMeasure
variable (μ : Measure Ω) [IsProbabilityMeasure μ] [MeasurableSingletonClass S]
  [MeasurableSingletonClass T]

lemma entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) :
    H[X ; μ] - H[X | Y ; μ] = I[X : Y ; μ] := by
  rw [mutualInformation_def, chain_rule _ hX hY, add_comm, add_sub_add_left_eq_sub]

lemma condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ] :
    H[X | Y ; μ] ≤ H[X ; μ] :=
  sub_nonneg.1 $ by rw [entropy_sub_condEntropy _ hX hY]; exact mutualInformation_nonneg hX hY _

/-- $H[X|Y,Z] \leq H[X|Z]$ -/
lemma entropy_submodular (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z): H[X | ⟨ Y, Z ⟩ ; μ] ≤ H[X | Z ; μ] := sorry

/-- $$ H[X,Y,Z] + H[Z] \leq H[X,Z] + H[Y,Z].$$ -/
lemma entropy_triple_add_entropy_le :
    H[⟨X, ⟨ Y, Z ⟩ ⟩ ; μ] + H[Z ; μ] ≤
      H[⟨ X, Z ⟩ ; μ] + H[⟨ Y, Z ⟩ ; μ] := sorry

variable {μ : Measure Ω}

lemma entropy_pair_eq_add : H[⟨ X, Y ⟩ ; μ] = H[X ; μ] + H[Y ; μ] ↔ IndepFun X Y μ :=
  sorry

/-- $I[X:Y]=0$ iff $X,Y$ are independent. -/
lemma mutualInformation_eq_zero : I[X : Y ; μ] = 0 ↔ IndepFun X Y μ :=
  sub_eq_zero.trans $ eq_comm.trans entropy_pair_eq_add

/-- The assertion that X and Y are conditionally independent relative to Z.  -/
def condIndepFun (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) : Prop := sorry

/-- $I[X:Y|Z]=0$ iff $X,Y$ are conditionally independent over $Z$. -/
lemma condMutualInformation_eq_zero (X : Ω → S) (Y : Ω → T) (Z : Ω → U) : I[X : Y | Z ; μ] = 0 ↔ condIndepFun X Y Z μ := sorry

/-- If $X, Y$ are conditionally independent over $Z$, then $H[X,Y,Z] = H[X,Z] + H[Y,Z] - H[Z]$. -/
lemma ent_of_cond_indep (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (h : condIndepFun X Y Z μ): H[ ⟨ X, ⟨ Y, Z ⟩ ⟩ ; μ ] = H[ ⟨ X, Z ⟩; μ ] + H[ ⟨ X, Z ⟩; μ ] - H[Z; μ] := by sorry


end IsProbabilityMeasure
end mutualInformation

section copy

variable {mΩ' : MeasurableSpace Ω'}

/-- For $X,Y$ random variables, one can find independent copies $X',Y'$ of $X,Y$. -/
lemma independent_copies {X : Ω → S} {Y : Ω' → T} (hX: Measurable X) (hY: Measurable Y) (μ: Measure Ω) (μ': Measure Ω'): ∃ ν : Measure (S × T), ∃ X' : S × T → S, ∃ Y' : S × T → T, IsProbabilityMeasure ν ∧ Measurable X' ∧ Measurable Y' ∧ (IndepFun X' Y' ν) ∧ IdentDistrib X' X ν μ ∧ IdentDistrib Y' Y ν μ' := by sorry

universe u v

/-- Let $X_i : \Omega_i \to S_i$ be random variables for $i=1,\dots,k$.  Then there exist jointly independent random variables $X'_i: \Omega' \to S_i$ for $i=1,\dots,k$ such that each $X'_i$ is a copy of $X_i$.  May need some hypotheses of measurability and non-degeneracy -/
lemma independent_copies' {I: Type*} [Fintype I] {S : I → Type u}
    [mS : ∀ i : I, MeasurableSpace (S i)] {Ω : I → Type v}
    [mΩ : ∀ i : I, MeasurableSpace (Ω i)] (X : ∀ i : I, Ω i → S i) (hX : ∀ i : I, Measurable (X i))
    (μ : ∀ i : I, Measure (Ω i)) :
    ∃ (A : Type (max u v)) (mA : MeasurableSpace A) (μA : Measure A) (X' : ∀ i, A → S i),
    IsProbabilityMeasure μA ∧
    (iIndepFun mS X' μA) ∧
    ∀ i : I, Measurable (X' i) ∧ IdentDistrib (X' i) (X i) μA (μ i) := by sorry


/-- For $X,Y$ random variables, there is a canonical choice of conditionally independent trials $X_1,X_2,Y'$.-/
lemma condIndependent_copies (X : Ω → S) (Y : Ω → T) (μ: Measure Ω): ∃ ν : Measure (S × S × T), ∃ X_1 X_2 : S × S × T → S, ∃ Y' : S × S × T → T, IsProbabilityMeasure ν ∧ Measurable X_1 ∧ Measurable X_2 ∧ Measurable Y' ∧ (condIndepFun X_1 X_2 Y' ν) ∧ IdentDistrib (⟨ X_1, Y' ⟩) (⟨ X, Y ⟩) ν μ ∧ IdentDistrib (⟨ X_2, Y' ⟩) (⟨ X, Y ⟩) ν μ := by sorry


end copy


end ProbabilityTheory



section MeasureSpace_example

open ProbabilityTheory

variable {Ω S T : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T}

example (hX : Measurable X) (hY : Measurable Y) :
  H[⟨ X, Y ⟩] = H[Y] + H[X | Y] := chain_rule _ hX hY

end MeasureSpace_example
