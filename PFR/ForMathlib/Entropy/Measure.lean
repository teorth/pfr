import PFR.ForMathlib.MeasureReal
import PFR.Mathlib.Analysis.SpecialFunctions.NegMulLog
import PFR.Mathlib.Data.Fintype.Card

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
open scoped ENNReal NNReal Topology BigOperators

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
  ∑ s, negMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal

lemma measureEntropy_def (μ : Measure S) :
    measureEntropy μ = ∑ s, negMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal := rfl

lemma measureEntropy_def' (μ : Measure S) :
    measureEntropy μ = ∑ s, negMulLog (((μ.real Set.univ) ⁻¹ • μ.real) {s}) := by
  rw [measureEntropy_def]
  congr! with s
  simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, measureReal_def, ENNReal.toReal_inv]

@[inherit_doc measureEntropy] notation:100 "Hm[" μ "]" => measureEntropy μ

@[simp]
lemma measureEntropy_zero : Hm[(0 : Measure S)] = 0 := by simp [measureEntropy]

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

lemma measureEntropy_of_not_isFiniteMeasure (h : ¬ IsFiniteMeasure μ) : Hm[μ] = 0 := by
  simp [measureEntropy, not_isFiniteMeasure_iff.mp h]

lemma measureEntropy_of_isProbabilityMeasure (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = ∑ s, negMulLog (μ {s}).toReal := by
  simp [measureEntropy]

lemma measureEntropy_of_isProbabilityMeasure' (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = ∑ s, negMulLog (μ.real {s}) :=
  measureEntropy_of_isProbabilityMeasure μ

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
  refine Finset.sum_nonneg (fun s _ ↦ negMulLog_nonneg ENNReal.toReal_nonneg ?_)
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => exact prob_le_one

lemma measureEntropy_le_card_aux {μ : Measure S} [IsProbabilityMeasure μ]
    (A : Finset S) (hμ : μ Aᶜ = 0) :
    Hm[μ] ≤ log A.card := by
  have μA : μ A = 1 := by
    rw [← compl_compl (A : Set S), measure_compl A.measurableSet.compl (measure_ne_top _ _), hμ]
    simp
  let N := A.card
  have N_pos : (0 : ℝ) < N := by
    rcases Finset.eq_empty_or_nonempty A with rfl|hA
    · simp at μA
    · simpa using Finset.card_pos.mpr hA
  simp only [measureEntropy_def, measure_univ, inv_one, one_smul]
  calc
  ∑ x, negMulLog (μ {x}).toReal
    = ∑ x in A, negMulLog (μ {x}).toReal := by
      apply (Finset.sum_subset A.subset_univ _).symm
      intro i _ hi
      have : μ {i} = 0 :=
        le_antisymm ((measure_mono (by simpa using hi)).trans (le_of_eq hμ)) bot_le
      simp [this]
  _ = N * ∑ x in A, (N : ℝ)⁻¹ * negMulLog (μ {x}).toReal := by
      rw [Finset.mul_sum]
      congr with x
      rw [← mul_assoc, mul_inv_cancel, one_mul]
      exact N_pos.ne'
  _ ≤ N * negMulLog (∑ x in A, (N : ℝ)⁻¹ * (μ {x}).toReal) :=
       mul_le_mul_of_nonneg_left
         (sum_negMulLog_le (by simp) (by simp [mul_inv_cancel N_pos.ne']) (by simp)) (by positivity)
  _ = N * negMulLog ((N : ℝ)⁻¹) := by simp [← Finset.mul_sum, μA]
  _ = log A.card := by simp [negMulLog, ← mul_assoc, mul_inv_cancel N_pos.ne']

lemma measureEntropy_eq_card_iff_measureReal_eq_aux [MeasurableSingletonClass S]
    (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = log (Fintype.card S) ↔∀ s : S, μ.real {s} = (Fintype.card S : ℝ)⁻¹ := by
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
    convert sum_negMulLog_eq_iff hw1 hw2 hp using 2
    · simp [measureEntropy_def', Finset.mul_sum]
    · simp [negMulLog, ← Finset.mul_sum]
    · rw [← Finset.mul_sum]
      simp

lemma measureEntropy_eq_card_iff_measure_eq_aux
    (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = log (Fintype.card S) ↔ (∀ s : S, μ {s} = (Fintype.card S : ℝ≥0)⁻¹) := by
  rw [measureEntropy_eq_card_iff_measureReal_eq_aux]
  congr! with s
  rw [measureReal_def, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ {s})]
  congr!
  simp

lemma measureEntropy_le_log_card_of_mem {A : Set S} (μ : Measure S) (hμA : μ Aᶜ = 0) :
    Hm[μ] ≤ log (Nat.card A) := by
  have h_log_card_nonneg : 0 ≤ log (Nat.card A) := log_nat_cast_nonneg (Nat.card ↑A)
  rcases eq_zero_or_neZero μ with rfl|hμ
  · simp [h_log_card_nonneg]
  · by_cases hμ_fin : IsFiniteMeasure μ
    swap;
    · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
      exact h_log_card_nonneg
    rw [← measureEntropy_univ_smul]
    let A' := A.toFinite.toFinset
    have AA' : A = (A' : Set S) := by simp
    have : ((μ Set.univ) ⁻¹ • μ) (A'ᶜ) = 0 := by simp [hμA]
    convert measureEntropy_le_card_aux A' this using 3
    rw [AA', Nat.card_eq_fintype_card]
    exact Fintype.card_coe A'

lemma measureEntropy_le_log_card (μ : Measure S) : Hm[μ] ≤ log (Fintype.card S) := by
  convert measureEntropy_le_log_card_of_mem (A := (Set.univ : Set S)) μ (by simp)
  simpa only [Nat.card_eq_fintype_card] using
    ((set_fintype_card_eq_univ_iff (Set.univ : Set S)).2 rfl).symm

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
    (μ : Measure S) (f : S → T) (hf : Function.Injective f) :
    Hm[μ.map f] = Hm[μ] := by
  have hf_m : Measurable f := measurable_of_finite f
  have : μ.map f Set.univ = μ Set.univ := by
      rw [Measure.map_apply hf_m MeasurableSet.univ]
      simp
  simp_rw [measureEntropy_def, Measure.smul_apply,
    Measure.map_apply hf_m (measurableSet_singleton _)]
  rw [this]
  classical
  have : ∑ x : T, negMulLog ((μ Set.univ)⁻¹ • μ (f ⁻¹' {x})).toReal
      = ∑ x in Finset.univ.image f,
        negMulLog ((μ Set.univ)⁻¹ • μ (f ⁻¹' {x})).toReal := by
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
    (f := fun x ↦ negMulLog (((μ (Set.range f))⁻¹).toReal * (μ {x}).toReal)) (g := f)]
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

@[simp]
lemma measureEntropy_prod (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Hm[μ.prod ν] = Hm[μ] + Hm[ν] := by
  simp_rw [measureEntropy_of_isProbabilityMeasure, Fintype.sum_prod_type,
    ← Set.singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul, negMulLog_mul',
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sum_toReal_measure_singleton]
  simp only [measure_univ, ENNReal.one_toReal, one_mul]

end measureEntropy

section measureMutualInfo

/-- The mutual information between the marginals of a measure on a product space. -/
noncomputable
def measureMutualInfo (μ : Measure (S × T) := by volume_tac) : ℝ :=
  Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ]

/-- The mutual information between the marginals of a measure on a product space. -/
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

@[simp]
lemma measureMutualInfo_prod (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Im[μ.prod ν] = 0 := by
  rw [measureMutualInfo_def, measureEntropy_prod]
  simp

lemma measureMutualInfo_nonneg_aux (μ : Measure (S × U)) [IsProbabilityMeasure μ] :
    0 ≤ Im[μ] ∧
    (Im[μ] = 0 ↔ ∀ p, μ.real {p} = (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2}) := by
  have : IsProbabilityMeasure (μ.map Prod.fst) :=
    isProbabilityMeasure_map measurable_fst.aemeasurable
  have : IsProbabilityMeasure (μ.map Prod.snd) :=
    isProbabilityMeasure_map measurable_snd.aemeasurable
  have h_fst_ne_zero : ∀ p, μ.real {p} ≠ 0 → (μ.map Prod.fst).real {p.1} ≠ 0 := by
    intro p hp
    rw [map_measureReal_apply measurable_fst (measurableSet_singleton _)]
    simp only [Set.mem_singleton_iff, ne_eq, ENNReal.toReal_eq_zero_iff, measure_ne_top μ,
      or_false]
    refine fun h_eq_zero ↦ hp ?_
    refine measureReal_mono_null ?_ h_eq_zero
    simp
  have h_snd_ne_zero : ∀ p, μ.real {p} ≠ 0 → (μ.map Prod.snd).real {p.2} ≠ 0 := by
    intro p hp
    rw [map_measureReal_apply measurable_snd (measurableSet_singleton _)]
    simp only [Set.mem_singleton_iff, ne_eq, ENNReal.toReal_eq_zero_iff, measure_ne_top μ,
      or_false]
    refine fun h_eq_zero ↦ hp ?_
    refine measureReal_mono_null ?_ h_eq_zero
    simp
  have h1 y : (μ.map Prod.fst).real {y} = ∑ z : U, μ.real {(y, z)} := by
    rw [map_measureReal_apply measurable_fst (measurableSet_singleton _),
      measureReal_preimage_fst_singleton_eq_sum]
  have h2 z : (μ.map Prod.snd).real {z} = ∑ y : S, μ.real {(y, z)} := by
    rw [map_measureReal_apply measurable_snd (measurableSet_singleton _),
      measureReal_preimage_snd_singleton_eq_sum]
  let w (p : S × U) := (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2}
  let f (p : S × U) := ((μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2})⁻¹ * μ.real {p}
  have hw1 : ∀ p, 0 ≤ w p := fun _ ↦ by positivity
  have hw2 : ∑ p, w p = 1 := by
    rw [Fintype.sum_prod_type]
    simp [← Finset.mul_sum, ← Finset.sum_mul]
  have hf : ∀ p, 0 ≤ f p := fun _ ↦ by positivity
  have H :=
  calc
    ∑ p : S × U, w p * f p
        = ∑ p : S × U, μ.real {p} := by
          congr with p
          by_cases hp : μ.real {p} = 0
          · simp [hp]
          field_simp [h_fst_ne_zero p hp, h_snd_ne_zero p hp]
          ring
      _ = 1 := by simp [-Fintype.sum_prod_type]
  have H1 : -measureMutualInfo (μ := μ) = ∑ p : S × U, w p * negMulLog (f p) :=
  calc
    _ = ∑ p : S × U,
          (-(μ.real {p} * log (μ.real {p}))
          + (μ.real {p} * log ((μ.map Prod.snd).real {p.2})
            + μ.real {p} * log ((μ.map Prod.fst).real {p.1}))) := by
        simp_rw [measureMutualInfo_def, measureEntropy_of_isProbabilityMeasure', negMulLog]
        simp [Finset.sum_add_distrib, Finset.sum_comm (γ := U), Finset.sum_mul, h1, h2]
    _ = ∑ p : S × U, w p * negMulLog (f p) := by
        congr! 1 with p
        by_cases hp : μ.real {p} = 0
        · simp [hp]
        have := h_fst_ne_zero p hp
        have := h_snd_ne_zero p hp
        rw [negMulLog, log_mul, log_inv, log_mul]
        · field_simp
          ring
        all_goals positivity
  have H2 : 0 = negMulLog (∑ s : S × U, w s * f s) := by simpa using congr_arg negMulLog H.symm
  rw [← neg_eq_zero, ← neg_nonpos, H1, H2]
  refine ⟨sum_negMulLog_le (fun _ _ ↦ hw1 ‹_›) hw2 fun _ _ ↦ hf ‹_›, ?_⟩
  refine (sum_negMulLog_eq_iff' (fun _ _ ↦ hw1 ‹_›) hw2 fun _ _ ↦ hf ‹_›).trans $
    forall_congr' fun p ↦ ?_
  · have hp1 := h_fst_ne_zero p
    have hp2 := h_snd_ne_zero p
    rw [not_imp_not] at hp1 hp2
    by_cases hp1' : (μ.map Prod.fst).real {p.1} = 0
    · simp [hp1', hp1 hp1']
    by_cases hp2' : (μ.map Prod.snd).real {p.2} = 0
    · simp [hp2', hp2 hp2']
    have hw : (w p)⁻¹ ≠ 0 := by positivity
    rw [← mul_right_inj' hw]
    simp (config := {zeta := false}) [H, -mul_eq_mul_left_iff, -Fintype.sum_prod_type]
    congr!
    field_simp

lemma measureMutualInfo_of_not_isFiniteMeasure {μ : Measure (S × U)} (h : ¬ IsFiniteMeasure μ) :
    Im[μ] = 0 := by
  rw [measureMutualInfo_def]
  have h1 : ¬ IsFiniteMeasure (μ.map Prod.fst) := by
    rw [not_isFiniteMeasure_iff] at h ⊢
    rw [← h]
    convert Measure.map_apply measurable_fst MeasurableSet.univ
  have h2 : ¬ IsFiniteMeasure (μ.map Prod.snd) := by
    rw [not_isFiniteMeasure_iff] at h ⊢
    rw [← h]
    convert Measure.map_apply measurable_snd MeasurableSet.univ
  rw [measureEntropy_of_not_isFiniteMeasure h, measureEntropy_of_not_isFiniteMeasure h1,
    measureEntropy_of_not_isFiniteMeasure h2]
  simp

lemma measureMutualInfo_univ_smul (μ : Measure (S × U)) : Im[(μ Set.univ)⁻¹ • μ] = Im[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap
  · rw [measureMutualInfo_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]
  rcases eq_zero_or_neZero μ with hμ | _
  . simp [hμ]
  rw [measureMutualInfo_def, measureMutualInfo_def]
  congr 1; congr 1
  . convert measureEntropy_univ_smul
    simp; congr; symm
    convert Measure.map_apply measurable_fst MeasurableSet.univ
  . convert measureEntropy_univ_smul
    simp; congr; symm
    convert Measure.map_apply measurable_snd MeasurableSet.univ
  convert measureEntropy_univ_smul

lemma measureMutualInfo_nonneg (μ : Measure (S × U)):
    0 ≤ Im[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  . rcases eq_zero_or_neZero μ with hμ|hμ
    . simp [hμ]
    rw [← measureMutualInfo_univ_smul μ]
    exact (measureMutualInfo_nonneg_aux ((μ Set.univ)⁻¹ • μ)).1
  rw [measureMutualInfo_of_not_isFiniteMeasure hμ_fin]

lemma measureMutualInfo_eq_zero_iff (μ : Measure (S × U)) [IsProbabilityMeasure μ] :
    Im[μ] = 0 ↔ ∀ p, μ.real {p} = (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2} :=
  (measureMutualInfo_nonneg_aux μ).2

end measureMutualInfo

end ProbabilityTheory
