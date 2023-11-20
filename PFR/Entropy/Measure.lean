import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import PFR.ForMathlib.Positivity
import PFR.neg_xlogx
import PFR.MeasureReal

/-!
# Entropy of a measure

## Main definitions

* `measureEntropy`: entropy of a measure `μ`, denoted by `Hm[μ]`
* `measureMutualInfo`: mutual information of a measure over a product space, denoted by `Im[μ]`,
  equal to `Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ]`

## Notations

* `Hm[μ] = measureEntropy μ`
* `Im[μ] = measureMutualInfo μ`

-/

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

section aux_lemmas

-- seems reasonable for Mathlib?
attribute [pp_dot] Measure.map

lemma integral_eq_sum {S E : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
     (μ : Measure S) [IsFiniteMeasure μ] (f : S → E) :
    ∫ x, f x ∂μ = ∑ x, (μ {x}).toReal • f x :=
  integral_fintype _ $ integrable_of_fintype _ _

lemma ae_iff_of_fintype {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (μ : Measure S) (p : S → Prop) :
    (∀ᵐ x ∂μ, p x) ↔ ∀ x, μ {x} ≠ 0 → p x := by
  rw [ae_iff]
  conv_lhs => rw [← Measure.sum_smul_dirac μ]
  simp only [Measure.sum_fintype, Measure.coe_finset_sum, Measure.smul_toOuterMeasure,
    OuterMeasure.coe_smul, Finset.sum_apply, Pi.smul_apply, measurableSet_setOf, Set.mem_setOf_eq,
    Measure.dirac_apply, not_not, smul_eq_mul, Finset.sum_eq_zero_iff, Finset.mem_univ, mul_eq_zero,
    Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, forall_true_left, ne_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro x
    cases h x with
    | inl h => exact fun h_not ↦ absurd h h_not
    | inr h =>
      intro _
      by_contra hpx
      exact h hpx
  · intro x
    by_cases hμx : μ {x} = 0
    · exact Or.inl hμx
    · exact Or.inr (fun hpx ↦ hpx (h x hμx))

-- TODO: Change RHS of `lintegral_fintype`
lemma lintegral_eq_sum {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
     (μ : Measure S) (f : S → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑ x, (μ {x}) * (f x) := by simp_rw [lintegral_fintype, mul_comm]

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

lemma measure_preimage_fst_singleton_eq_sum {S T : Type*} [Fintype S] {_ : MeasurableSpace S}
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
    [MeasurableSingletonClass S] [Fintype T] {_ : MeasurableSpace T}
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


namespace ProbabilityTheory

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]

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

notation:100 "Hm[" μ "]" => measureEntropy μ

@[simp]
lemma measureEntropy_zero : Hm[(0 : Measure S)] = 0 := by
  simp [measureEntropy]

@[simp]
lemma measureEntropy_dirac (x : S) : Hm[Measure.dirac x] = 0 := by
  rw [measureEntropy_def]
  simp only [MeasurableSet.univ, Measure.dirac_apply', Set.mem_univ, Set.indicator_of_mem,
    Pi.one_apply, inv_one, one_smul, MeasurableSet.singleton, Set.mem_singleton_iff]
  rw [Finset.sum_eq_single x]
  · simp
  · simp only [Finset.mem_univ, ne_eq, Set.mem_singleton_iff, forall_true_left]
    intro b hb
    simp [Ne.symm hb]
  · simp

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

lemma measureEntropy_le_card_aux (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] ≤ log (Fintype.card S) := by
  cases isEmpty_or_nonempty S with
  | inl h =>
    have : μ = 0 := Subsingleton.elim _ _
    simp [Fintype.card_eq_zero, this]
  | inr h =>
    set N := Fintype.card S
    have hN : 0 < N := Fintype.card_pos
    rw [measureEntropy_def]
    simp only [measure_univ, inv_one, one_smul]
    calc ∑ x, negIdMulLog (μ {x}).toReal
      = ∑ x, negIdMulLog (μ {x}).toReal := rfl
    _ = N * ∑ x, (N : ℝ)⁻¹ * negIdMulLog (μ {x}).toReal := by
        rw [Finset.mul_sum]
        congr with x
        rw [← mul_assoc, mul_inv_cancel, one_mul]
        simp [hN.ne']
    _ ≤ N * negIdMulLog (∑ x : S, (N : ℝ)⁻¹ * (μ {x}).toReal) := by
        refine mul_le_mul le_rfl ?_ ?_ ?_
        · refine sum_negIdMulLog_le (by simp) ?_ (fun _ ↦ ENNReal.toReal_nonneg)
          simp [Finset.card_univ]
        · refine Finset.sum_nonneg (fun x _ ↦ ?_)
          refine mul_nonneg ?_ ?_
          · simp [hN]
          · refine negIdMulLog_nonneg (by simp) ?_
            refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
            rw [ENNReal.ofReal_one]
            exact prob_le_one
        · positivity
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

lemma measureEntropy_le_log_card (μ : Measure S) :
    Hm[μ] ≤ log (Fintype.card S) := by
  have h_log_card_nonneg : 0 ≤ log (Fintype.card S) := by
    cases isEmpty_or_nonempty S with
    | inl h => rw [Fintype.card_eq_zero]; simp
    | inr h =>
      refine log_nonneg ?_
      simp only [Nat.one_le_cast]
      exact Fintype.card_pos
  cases eq_zero_or_neZero μ with
  | inl hμ => simp only [hμ, measureEntropy_zero]; exact h_log_card_nonneg
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

lemma measureEntropy_map_of_injective
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
  have : ∑ x : T, negIdMulLog ((μ Set.univ)⁻¹ • μ (f ⁻¹' {x})).toReal
      = ∑ x in Finset.univ.image f,
        negIdMulLog ((μ Set.univ)⁻¹ • μ (f ⁻¹' {x})).toReal := by
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

lemma measureEntropy_comap (μ : Measure S) (f : T → S) (hf : MeasurableEmbedding f)
    (hf_range : Set.range f =ᵐ[μ] Set.univ) :
    Hm[μ.comap f] = Hm[μ] := by
  simp_rw [measureEntropy_def, Measure.smul_apply,
    Measure.comap_apply f hf.injective hf.measurableSet_image' _ (measurableSet_singleton _),
    Measure.comap_apply f hf.injective hf.measurableSet_image' _ MeasurableSet.univ]
  simp only [Set.image_univ, Set.image_singleton, smul_eq_mul, ENNReal.toReal_mul]
  classical
  rw [← Finset.sum_image
    (f := fun x ↦ negIdMulLog (((μ (Set.range f))⁻¹).toReal * (μ {x}).toReal)) (g := f)]
  rw [measure_congr hf_range]
  rw [Finset.sum_subset]
  · exact Finset.subset_univ _
  · intro y _ hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hy
    simp only [ae_eq_univ] at hf_range
    suffices μ {y} = 0 by simp [this]
    refine measure_mono_null ?_ hf_range
    intro y'
    simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_range, not_exists]
    intro h
    rwa [h]
  · simp only [Finset.mem_univ, forall_true_left]
    exact hf.injective

lemma measureEntropy_comap_equiv (μ : Measure S) (f : T ≃ᵐ S) :
    Hm[μ.comap f] = Hm[μ] := by
  refine measureEntropy_comap μ f f.measurableEmbedding ?_
  simp only [ae_eq_univ]
  have : Set.range f = Set.univ := Equiv.range_eq_univ _
  simp [this]

lemma measureEntropy_prod (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Hm[μ.prod ν] = Hm[μ] + Hm[ν] := by
  simp_rw [measureEntropy_of_isProbabilityMeasure, Fintype.sum_prod_type,
    ← Set.singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul, negIdMulLog_mul',
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sum_toReal_measure_singleton]
  simp only [measure_univ, ENNReal.one_toReal, one_mul]

end measureEntropy

section measureMutualInfo

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
  simp_rw [Measure.map_apply measurable_swap (measurableSet_singleton _)]
  rw [Finset.sum_comm]
  congr with x
  congr with y
  congr
  rw [← Set.singleton_prod_singleton, Set.preimage_swap_prod, Set.singleton_prod_singleton]

lemma measureMutualInfo_prod (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Im[μ.prod ν] = 0 := by
  rw [measureMutualInfo_def, measureEntropy_prod]
  simp

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

end ProbabilityTheory
