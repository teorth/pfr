import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import PFR.ForMathlib.FiniteRange.Defs
import PFR.Mathlib.MeasureTheory.Measure.Dirac
import PFR.Mathlib.MeasureTheory.Measure.Real
import PFR.Mathlib.Probability.UniformOn

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

open MeasureTheory Real Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] --[MeasurableSingletonClass S]
  [MeasurableSpace T] --[MeasurableSingletonClass T]
  [MeasurableSpace U] --[MeasurableSingletonClass U]

section measureEntropy
variable {μ : Measure S}

/-- Entropy of a measure on a measurable space.

We normalize the measure by `(μ Set.univ)⁻¹` to extend the entropy definition to finite measures.
What we really want to do is deal with `μ=0` or `IsProbabilityMeasure μ`, but we don't have
a typeclass for that (we could create one though).
The added complexity ∈ the expression is not an issue because if `μ` is a probability measure,
a call to `simp` will simplify `(μ Set.univ)⁻¹ • μ` to `μ`. -/
noncomputable
def measureEntropy (μ : Measure S := by volume_tac) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ).real {s})

@[inherit_doc measureEntropy] notation:100 "Hm[" μ "]" => measureEntropy μ

/-- A measure has finite support if there exists a finite set whose complement has zero measure. -/
class FiniteSupport (μ : Measure S := by volume_tac) : Prop where
  finite : ∃ A : Finset S, μ Aᶜ = 0

/-- A set on which a measure with finite support is supported. -/
noncomputable
def _root_.MeasureTheory.Measure.support (μ : Measure S) [hμ : FiniteSupport μ] : Finset S :=
  hμ.finite.choose.filter (μ {·} ≠ 0)

lemma measure_compl_support (μ : Measure S) [hμ : FiniteSupport μ] : μ μ.supportᶜ = 0 := by
  let A := hμ.finite.choose
  have : (μ.support : Set S)ᶜ ⊆ (A : Set S)ᶜ ∪ ⋃ x ∈ A.filter (μ {·} = 0), {x} := by
    intro z hz
    simp only [Measure.support, ne_eq, Finset.coe_filter, mem_compl_iff, mem_setOf_eq, not_and,
      Decidable.not_not] at hz
    by_cases h'z : z ∈ A
    · simp [hz h'z, h'z]
    · simp [h'z]
  apply le_antisymm ?_ bot_le
  calc μ (μ.support : Set S)ᶜ ≤ μ ((A : Set S)ᶜ ∪ ⋃ x ∈ A.filter (μ {·} = 0), {x}) :=
    measure_mono this
  _ ≤ μ (Aᶜ) + ∑ x ∈ A.filter (μ {·} = 0), μ {x} := by
    apply (measure_union_le _ _).trans
    gcongr
    apply measure_biUnion_finset_le
  _ ≤ 0 + ∑ x ∈ A.filter (μ {·} = 0), 0 := by
    gcongr with x hx
    · exact hμ.finite.choose_spec.le
    · simp only [Finset.mem_filter] at hx
      exact hx.2.le
  _ = 0 := by simp

@[simp] lemma mem_support {μ : Measure S} [hμ : FiniteSupport μ] {x : S} :
    x ∈ μ.support ↔ μ {x} ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [Measure.support, ne_eq, Finset.mem_filter] at h
    exact h.2
  · contrapose! h
    exact measure_mono_null (by simpa using h) (measure_compl_support μ)

instance finiteSupport_zero : FiniteSupport (0 : Measure S) where
  finite := ⟨(∅ : Finset S), by simp⟩

/-- TODO: replace FiniteSupport hypotheses ∈ these files with FiniteEntropy hypotheses. -/
noncomputable def FiniteEntropy (μ : Measure S := by volume_tac) : Prop :=
  Summable (fun s ↦ negMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal) ∧
  ∃ A : Set S, Countable A ∧ μ Aᶜ = 0

instance finiteSupport_of_fintype {μ : Measure S} [Fintype S] : FiniteSupport μ := by
  use Finset.univ
  simp

instance finiteSupport_of_mul {μ : Measure S} [FiniteSupport μ] (c : ℝ≥0∞) :
    FiniteSupport (c • μ) := by
  use μ.support
  simp [measure_compl_support]

section

variable [MeasurableSingletonClass S]

lemma finiteSupport_of_comp
    {μ : Measure Ω} [FiniteSupport μ] {X : Ω → S} (hX : Measurable X) :
    FiniteSupport (μ.map X) := by
  classical
  use Finset.image X μ.support
  rw [Measure.map_apply hX (MeasurableSet.compl (Finset.measurableSet _))]
  refine measure_mono_null ?_ (measure_compl_support μ)
  intro x; contrapose!; simp; intro hx; use x

instance finiteSupport_of_dirac (x : S) : FiniteSupport (Measure.dirac x) := by
  use {x}
  simp [Measure.dirac_apply', Set.mem_singleton_iff, MeasurableSet.singleton]

/-- duplicate of `FiniteRange.null_of_compl` -/
lemma full_measure_of_finiteRange {μ : Measure Ω} {X : Ω → S}
    (hX : Measurable X) [hX' : FiniteRange X] :
    (μ.map X) hX'.toFinsetᶜ = 0 := by
  rw [Measure.map_apply hX (MeasurableSet.compl (Finset.measurableSet _))]
  convert measure_empty (μ := μ)
  ext x
  simp [FiniteRange.toFinset]

instance finiteSupport_of_finiteRange {μ : Measure Ω} {X : Ω → S} [hX' : FiniteRange X] :
    FiniteSupport (μ.map X) := by
  use hX'.toFinset
  exact FiniteRange.null_of_compl μ X

instance finiteSupport_of_prod {μ : Measure S} [FiniteSupport μ] {ν : Measure T} [SigmaFinite ν]
    [FiniteSupport ν] :
    FiniteSupport (μ.prod ν) := by
  use μ.support ×ˢ ν.support
  exact Measure.prod_of_full_measure_finset (measure_compl_support μ) (measure_compl_support ν)

/-- The countability hypothesis can probably be dropped here. Proof is unwieldy and can probably
be golfed. -/
lemma integrable_of_finiteSupport (μ : Measure S) [FiniteSupport μ]
    {β : Type*} [NormedAddCommGroup β] [IsFiniteMeasure μ] [Countable S]
    {f : S → β} :
    Integrable f μ := by
  let A := μ.support
  have hA : μ Aᶜ = 0 := measure_compl_support μ
  by_cases hA' : A = ∅
  · simp [hA'] at hA
    rw [hA]
    exact integrable_zero_measure
  have : ∃ s₀, s₀ ∈ A := by
    contrapose! hA'
    ext s
    simp
    exact hA' s
  rcases this with ⟨s₀, hs₀⟩
  let f' : A → β := fun a ↦ f a
  classical
  let g : S → A := fun s ↦ if h : s ∈ A then ⟨s, h⟩ else ⟨s₀, hs₀⟩
  have : (f' ∘ g) =ᵐ[μ] f := by
    apply Filter.eventuallyEq_of_mem (s := A) hA
    intro a ha
    simp at ha
    simp [f', g, ha]
  apply Integrable.congr _ this
  apply Integrable.comp_measurable .of_finite
  fun_prop

lemma integral_congr_finiteSupport {μ : Measure Ω} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f g : Ω → G} [FiniteSupport μ]
    (hfg : ∀ x, μ {x} ≠ 0 → f x = g x) : ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
  refine integral_congr_ae <| measure_mono_null ?_ <| measure_compl_support μ
  exact fun x hx hx' ↦ hx <| hfg _ <| mem_support.1 hx'

/-- This generalizes Measure.ext_iff_singleton ∈ MeasureReal -/
theorem Measure.ext_iff_singleton_finiteSupport
    {μ1 μ2 : Measure S} [FiniteSupport μ1] [FiniteSupport μ2] :
    μ1 = μ2 ↔ ∀ x, μ1 {x} = μ2 {x} := by
  classical
  constructor
  · rintro rfl
    simp
  · let A1 := μ1.support
    have hA1 := measure_compl_support μ1
    let A2 := μ2.support
    have hA2 := measure_compl_support μ2
    intro h
    ext s
    have h1 : μ1 s = μ1 (s ∩ (A1 ∪ A2)) := by
      apply (measure_eq_measure_of_null_diff _ _).symm
      · simp
      refine measure_mono_null ?_ hA1
      intro x
      simp (config := { contextual := true }) [A1]
    have h2 : μ2 s = μ2 (s ∩ (A1 ∪ A2)) := by
      apply (measure_eq_measure_of_null_diff _ _).symm
      · simp
      exact measure_mono_null (fun x ↦ by simp (config := { contextual := true }) [A2]) hA2
    rw [h1, h2]
    have hs : Set.Finite (s ∩ (A1 ∪ A2)) := Set.toFinite (s ∩ (↑A1 ∪ ↑A2))
    rw [← hs.coe_toFinset, ← sum_measure_singleton (μ := μ1), ← sum_measure_singleton (μ := μ2)]
    simp_rw [h]

theorem Measure.ext_iff_measureReal_singleton_finiteSupport {μ1 μ2 : Measure S}
    [FiniteSupport μ1] [FiniteSupport μ2] [IsFiniteMeasure μ1] [IsFiniteMeasure μ2] :
    μ1 = μ2 ↔ ∀ x, μ1.real {x} = μ2.real {x} := by
  rw [Measure.ext_iff_singleton_finiteSupport]
  congr! with x
  have h1 : μ1 {x} ≠ ⊤ := by finiteness
  have h2 : μ2 {x} ≠ ⊤ := by finiteness
  rw [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff]
  simp [h1, h2]

end

lemma measureEntropy_eq_sum {μ : Measure S} {A : Finset S} (hA : μ Aᶜ = 0) :
   Hm[μ] = ∑ s ∈ A, negMulLog (((μ Set.univ)⁻¹ • μ).real {s}) := by
  unfold measureEntropy
  rw [tsum_eq_sum]
  intro s hs
  suffices μ.real {s} = 0 by simp [this]
  rw [Measure.real, measure_mono_null (by simpa) hA]
  simp

@[simp]
lemma measureEntropy_zero : Hm[(0 : Measure S)] = 0 := by simp [measureEntropy]

@[simp]
lemma measureEntropy_dirac [MeasurableSingletonClass S] (x : S) : Hm[Measure.dirac x] = 0 := by
  rw [measureEntropy]
  simp only [MeasurableSet.univ, Measure.dirac_apply', mem_univ, indicator_of_mem, Pi.one_apply,
    inv_one, one_smul]
  rw [tsum_eq_single x]
  · simp only [Measure.real, MeasurableSet.singleton, Measure.dirac_apply', mem_singleton_iff,
    indicator_of_mem, Pi.one_apply, ENNReal.toReal_one, negMulLog_one]
  · simp +contextual [eq_comm]

lemma measureEntropy_of_not_isFiniteMeasure (h : ¬ IsFiniteMeasure μ) : Hm[μ] = 0 := by
  simp [measureEntropy, not_isFiniteMeasure_iff.mp h]

lemma measureEntropy_of_isProbabilityMeasure (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑' s, negMulLog (μ.real {s}) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [measureEntropy]
  · simp [measureEntropy]

lemma measureEntropy_of_isProbabilityMeasure' (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑' s, negMulLog (μ.real {s}) :=
  measureEntropy_of_isProbabilityMeasure μ

lemma measureEntropy_of_isProbabilityMeasure_finite {μ : Measure S} {A : Finset S} (hA : μ Aᶜ = 0)
    [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑ s ∈ A, negMulLog (μ.real {s}) := by
  rw [measureEntropy_eq_sum hA]
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ <;> simp

lemma measureEntropy_of_isProbabilityMeasure_finite' {μ : Measure S} {A : Finset S} (hA : μ Aᶜ = 0)
    [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑ s ∈ A, negMulLog (μ.real {s}) :=
  measureEntropy_of_isProbabilityMeasure_finite hA

lemma measureEntropy_univ_smul : Hm[(μ Set.univ)⁻¹ • μ] = Hm[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap
  · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => simp [measureEntropy]

lemma measureEntropy_nonneg (μ : Measure S) : 0 ≤ Hm[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap; · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
  apply tsum_nonneg
  intro s
  apply negMulLog_nonneg (by positivity)
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => exact prob_le_one

variable [MeasurableSingletonClass S]

/-- Auxiliary lemma for `measureEntropy_le_log_card_of_mem`, which removes the probability
measure assumption. -/
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
    · simpa [N] using Finset.card_pos.mpr hA
  simp only [measureEntropy, measure_univ, inv_one, one_smul]
  calc
  ∑' x, negMulLog (μ.real {x})
    = ∑ x ∈ A, negMulLog (μ.real {x}) := by
      apply tsum_eq_sum
      intro i hi
      have : μ {i} = 0 :=
        le_antisymm ((measure_mono (by simpa using hi)).trans (le_of_eq hμ)) bot_le
      simp [Measure.real, this]
  _ = N * ∑ x ∈ A, (N : ℝ)⁻¹ * negMulLog (μ.real {x}) := by
      rw [Finset.mul_sum]
      congr with x
      rw [← mul_assoc, mul_inv_cancel₀, one_mul]
      exact N_pos.ne'
  _ ≤ N * negMulLog (∑ x ∈ A, (N : ℝ)⁻¹ * (μ.real {x})) := by
      gcongr
      exact concaveOn_negMulLog.le_map_sum (by simp) (by simp [mul_inv_cancel₀ N_pos.ne', N])
        (by simp)
  _ = N * negMulLog ((N : ℝ)⁻¹) := by simp [← Finset.mul_sum]; simp [μA, Measure.real]
  _ = log A.card := by simp [negMulLog, ← mul_assoc, mul_inv_cancel₀ N_pos.ne', N]

lemma measureEntropy_eq_card_iff_measureReal_eq_aux [Fintype S]
    (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = log (Fintype.card S) ↔ ∀ s, μ.real {s} = (Fintype.card S : ℝ)⁻¹ := by
  cases isEmpty_or_nonempty S
  · simp [Fintype.card_eq_zero, Subsingleton.elim μ 0]
  -- multiply LHS equation through by `N⁻¹`
  set N := Fintype.card S
  have hN : (N:ℝ)⁻¹ ≠ 0 := by positivity
  rw [← mul_right_inj' hN]
  -- setup to use equality case of Jensen
  let w (_ : S) := (N:ℝ)⁻¹
  have hw1 : ∀ s ∈ Finset.univ, 0 < w s := by intros; positivity
  have hw2 : ∑ s : S, w s = 1 := by simp [w, Finset.card_univ, N]
  let p (s : S) := μ.real {s}
  have hp : ∀ s ∈ Finset.univ, 0 ≤ p s := by intros; positivity
  rw [measureEntropy, tsum_fintype, eq_comm]
  convert strictConcaveOn_negMulLog.map_sum_eq_iff hw1 hw2 hp using 2
  · simp [w, p, negMulLog, ← Finset.mul_sum]
  · simp [Finset.mul_sum, w, p]
  · simp [p, ← Finset.mul_sum, w, p]

lemma measureEntropy_eq_card_iff_measure_eq_aux
    (μ : Measure S) [Fintype S] [IsProbabilityMeasure μ] :
    Hm[μ] = log (Fintype.card S) ↔ (∀ s : S, μ {s} = (Fintype.card S : ℝ≥0)⁻¹) := by
  rw [measureEntropy_eq_card_iff_measureReal_eq_aux]
  congr! with s
  rw [measureReal_def, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ {s})]
  congr!
  simp

lemma measureEntropy_le_log_card_of_mem
    {A : Finset S} (μ : Measure S) (hμA : μ Aᶜ = 0) :
    Hm[μ] ≤ log A.card := by
  have h_log_card_nonneg : 0 ≤ log (Nat.card A) := log_natCast_nonneg (Nat.card ↑A)
  rcases eq_zero_or_neZero μ with rfl|hμ
  · simp
    positivity
  by_cases hμ_fin : IsFiniteMeasure μ
  · rw [← measureEntropy_univ_smul]
    exact measureEntropy_le_card_aux A <| by simp [hμA]
  · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
    exact log_natCast_nonneg _

lemma measureEntropy_le_log_card [Fintype S] (μ : Measure S) : Hm[μ] ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card_of_mem (A := (Finset.univ : Finset S)) μ (by simp)

lemma measureEntropy_eq_card_iff_measureReal_eq [Fintype S] [IsFiniteMeasure μ] [NeZero μ] :
    Hm[μ] = log (Fintype.card S) ↔ ∀ s : S, μ.real {s} = μ.real Set.univ / Fintype.card S := by
  rw [← measureEntropy_univ_smul]
  convert measureEntropy_eq_card_iff_measureReal_eq_aux ((μ Set.univ)⁻¹ • μ) using 2 with s
  simp only [measureReal_ennreal_smul_apply]
  rw [ENNReal.toReal_inv, inv_mul_eq_iff_eq_mul₀ (by exact measureReal_univ_ne_zero),
    div_eq_mul_inv]
  rfl

/-- The entropy of a uniform measure is the log of the cardinality of its support. -/
lemma entropy_of_uniformOn (H : Set S) [Nonempty H] [Finite H] :
    measureEntropy (uniformOn H) = log (Nat.card H) := by
  simp only [measureEntropy, measure_univ, inv_one, one_smul, Set.toFinite, uniformOn_real]
  classical
  calc ∑' s, negMulLog ((Nat.card (H ∩ {s} : Set S)) / Nat.card H)
    _ = ∑' s, if s ∈ H then negMulLog (1 / Nat.card H) else 0 := by
      congr with s; by_cases h : s ∈ H <;> simp [h]
    _ = ∑ s ∈ H.toFinite.toFinset, negMulLog (1 / Nat.card H) := by
      convert tsum_eq_sum (s := H.toFinite.toFinset) ?_ using 2 with s hs
      · simp at hs; simp [hs]
      · constructor
        simp
      intro s hs
      simp only [Set.Finite.mem_toFinset] at hs; simp [hs]
    _ = (Nat.card H) * negMulLog (1 / Nat.card H) := by simp [← Set.ncard_coe_finset]
    _ = log (Nat.card H) := by
      simp only [negMulLog, one_div, log_inv, mul_neg, neg_mul, neg_neg, ← mul_assoc]
      rw [mul_inv_cancel₀, one_mul]
      simp only [ne_eq, Nat.cast_eq_zero, Nat.card_ne_zero]
      exact ⟨‹_›, ‹_›⟩

lemma measureEntropy_eq_card_iff_measure_eq [Fintype S] [IsFiniteMeasure μ] [NeZero μ] :
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
    (μ : Measure T) (f : T → S) (hf_m : Measurable f) (hf : Function.Injective f) :
    Hm[μ.map f] = Hm[μ] := by
  have : μ.map f Set.univ = μ Set.univ := by
      rw [Measure.map_apply hf_m MeasurableSet.univ]
      simp
  simp_rw [measureEntropy, Measure.ennreal_smul_real_apply,
    map_measureReal_apply hf_m (.singleton _)]
  rw [this]
  classical
  let F (x : S) : ℝ := negMulLog ((μ Set.univ)⁻¹.toReal • μ.real (f ⁻¹' {x}))
  have : ∑' x : S, F x
      = ∑' x : (f '' Set.univ), F x := by
    apply (tsum_subtype_eq_of_support_subset _).symm
    intro x hx
    contrapose hx
    suffices f ⁻¹' {x} = ∅ by simp [F, this]
    contrapose! hx
    rw [Set.image_univ]
    exact hx
  rw [this, tsum_image _ hf.injOn, tsum_univ fun x ↦ F (f x)]
  congr! with s
  ext s'; simp
  exact hf.eq_iff

lemma measureEntropy_comap (μ : Measure T) (f : S → T) (hf : MeasurableEmbedding f)
    (hf_range : Set.range f =ᵐ[μ] Set.univ) :
    Hm[μ.comap f] = Hm[μ] := by
  simp_rw [measureEntropy, Measure.ennreal_smul_real_apply,
    Measure.comap_real_apply hf.injective hf.measurableSet_image' _ (.singleton _),
    Measure.comap_apply f hf.injective hf.measurableSet_image' _ MeasurableSet.univ]
  simp only [Set.image_univ, Set.image_singleton, smul_eq_mul]
  classical
  rw [← tsum_range (f := fun x ↦ negMulLog ((μ (Set.range f))⁻¹.toReal * μ.real {x})) (g := f),
    measure_congr hf_range]
  let F : T → ℝ := fun x ↦ negMulLog ((μ .univ)⁻¹.toReal * μ.real {x})
  show ∑' x : (Set.range f), F x = ∑' x : T, F x
  apply tsum_subtype_eq_of_support_subset
  · intro x hx
    contrapose hx
    suffices μ {x} = 0 by simp [F, Measure.real, this]
    simp only [ae_eq_univ] at hf_range
    exact measure_mono_null (by simp [*]) hf_range
  exact hf.injective

lemma measureEntropy_comap_equiv (μ : Measure T) (f : S ≃ᵐ T) : Hm[μ.comap f] = Hm[μ] := by
  refine measureEntropy_comap μ f f.measurableEmbedding ?_
  simp only [ae_eq_univ]
  have : Set.range f = Set.univ := Equiv.range_eq_univ _
  simp [this]

/-- An ambitious goal would be to replace FiniteSupport with finite entropy. -/
@[simp]
lemma measureEntropy_prod {μ : Measure S} {ν : Measure T} [FiniteSupport μ] [FiniteSupport ν]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [MeasurableSingletonClass T] :
    Hm[μ.prod ν] = Hm[μ] + Hm[ν] := by
  let A := μ.support
  have hA := measure_compl_support μ
  let B := ν.support
  have hB := measure_compl_support ν
  have hC : (μ.prod ν) (A ×ˢ B : Finset (S × T))ᶜ = 0 := by
    have : ((A ×ˢ B : Finset (S × T)) : Set (S × T))ᶜ
      = ((A : Set S)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (B : Set T)ᶜ) := by ext ⟨a, b⟩; simp; tauto
    rw [this]
    simp [hA, hB, A, B]
  have h1 : Hm[μ] = ∑ p ∈ (A ×ˢ B), (negMulLog (μ.real {p.1})) * (ν.real {p.2}) := by
    rw [measureEntropy_of_isProbabilityMeasure_finite' hA, Finset.sum_product]
    congr with s
    simp; rw [← Finset.mul_sum]; simp
    suffices ν.real B = ν.real Set.univ by simp at this; simp [this]
    apply measureReal_congr
    simp [hB, B]
  have h2 : Hm[ν] = ∑ p ∈ (A ×ˢ B), (negMulLog (ν.real {p.2})) * (μ.real {p.1}) := by
    rw [measureEntropy_of_isProbabilityMeasure_finite' hB, Finset.sum_product_right]
    congr with t
    simp; rw [← Finset.mul_sum]; simp
    suffices μ.real A = μ.real Set.univ by simp at this; simp [this]
    apply measureReal_congr
    simp [hA, A]
  rw [measureEntropy_of_isProbabilityMeasure_finite' hC, h1, h2, ← Finset.sum_add_distrib]
  congr with ⟨s, t⟩
  simp_rw [← Set.singleton_prod_singleton, measureReal_prod_prod, negMulLog_mul]
  ring

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

@[simp]
lemma measureMutualInfo_zero_measure : Im[(0 : Measure (S × T))] = 0 := by
  simp [measureMutualInfo]

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
  · simp [hμ]
  rw [measureMutualInfo_def, measureMutualInfo_def]
  congr 1; congr 1
  · convert measureEntropy_univ_smul
    simp; congr; symm
    convert Measure.map_apply measurable_fst MeasurableSet.univ
  · convert measureEntropy_univ_smul
    simp; congr; symm
    convert Measure.map_apply measurable_snd MeasurableSet.univ
  convert measureEntropy_univ_smul

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]

lemma measureMutualInfo_swap (μ : Measure (S × T)) :
    Im[μ.map Prod.swap] = Im[μ] := by
  rw [measureMutualInfo_def, add_comm, Measure.map_map measurable_snd measurable_swap,
    Measure.map_map measurable_fst measurable_swap]
  congr 1
  simp_rw [measureEntropy, Measure.map_apply measurable_swap MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.ennreal_smul_real_apply, smul_eq_mul]
  simp_rw [map_measureReal_apply measurable_swap (.singleton _)]
  have : Set.range (Prod.swap : S × T → T × S) = Set.univ := Set.range_eq_univ.mpr Prod.swap_surjective
  rw [← tsum_univ, ← this,
    tsum_range fun x ↦ negMulLog <| (μ Set.univ)⁻¹.toReal * μ.real (Prod.swap⁻¹' {x})]
  congr! with ⟨s, t⟩
  simp
  convert Function.Injective.preimage_image _ _
  simp
  all_goals exact Prod.swap_injective

@[simp]
lemma measureMutualInfo_prod {μ : Measure S} {ν : Measure T} [FiniteSupport μ] [FiniteSupport ν]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Im[μ.prod ν] = 0 := by
  rw [measureMutualInfo_def, measureEntropy_prod]
  simp

/-- An ambitious goal would be to replace FiniteSupport with finite entropy. Proof is long and slow; needs to be optimized -/
lemma measureMutualInfo_nonneg_aux {μ : Measure (S × U)} [FiniteSupport μ]
    [IsZeroOrProbabilityMeasure μ] :
    0 ≤ Im[μ] ∧
    (Im[μ] = 0 ↔ ∀ p, μ.real {p} = (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2}) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : IsProbabilityMeasure (μ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have : IsProbabilityMeasure (μ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let E := μ.support
  have hE := measure_compl_support μ
  classical
  set E1 : Finset S := Finset.image Prod.fst E
  set E2 : Finset U := Finset.image Prod.snd E
  have hE' : μ (E1 ×ˢ E2 : Finset (S × U))ᶜ = 0 := by
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    contrapose!
    intro h
    simp at h ⊢
    simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, E1, E, E2,
      mem_support]
    constructor; use u; use s
  have hE1 : (μ.map Prod.fst) E1ᶜ = 0 := by
    rw [Measure.map_apply measurable_fst (MeasurableSet.compl (Finset.measurableSet E1))]
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    simp
    contrapose!
    simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, E1, E,
      mem_support]
    intro h; use u
  have hE1' : (μ.map Prod.fst).real E1 = 1 := by
    rw [prob_compl_eq_zero_iff E1.measurableSet] at hE1
    unfold Measure.real
    rw [hE1]
    norm_num
  have hE2 : (μ.map Prod.snd) E2ᶜ = 0 := by
    rw [Measure.map_apply measurable_snd (MeasurableSet.compl (Finset.measurableSet E2))]
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    simp
    contrapose!
    simp only [Finset.mem_image, Prod.exists, exists_eq_right, E2, E, mem_support]
    intro h; use s
  have hE2' : (μ.map Prod.snd).real E2 = 1 := by
    rw [prob_compl_eq_zero_iff E2.measurableSet] at hE2
    unfold Measure.real
    rw [hE2]
    norm_num
  have h_fst_ne_zero : ∀ p, μ.real {p} ≠ 0 → (μ.map Prod.fst).real {p.1} ≠ 0 := by
    intro p hp
    rw [map_measureReal_apply measurable_fst (.singleton _)]
    refine fun h_eq_zero ↦ hp <| measureReal_mono_null (by simp) h_eq_zero

  have h_snd_ne_zero : ∀ p, μ.real {p} ≠ 0 → (μ.map Prod.snd).real {p.2} ≠ 0 := by
    intro p hp
    rw [map_measureReal_apply measurable_snd (.singleton _)]
    exact fun h_eq_zero ↦ hp <| measureReal_mono_null (by simp) h_eq_zero
  have h1 y : (μ.map Prod.fst).real {y} = ∑ z ∈ E2, μ.real {(y, z)} := by
    rw [map_measureReal_apply measurable_fst (.singleton _), ← measureReal_biUnion_finset]
    · apply measureReal_congr
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null ?_ hE
        intro ⟨s, u⟩ ⟨h1, h2⟩
        contrapose! h2
        simp at h1 h2 ⊢
        simp only [Finset.mem_image, Prod.exists, exists_eq_right, E2, E, mem_support]
        constructor; exact h1; use s
      · convert measure_empty (μ := μ)
        rw [Set.diff_eq_empty]
        intro ⟨s, u⟩ h
        simp at h ⊢
        exact h.1
    · intro s1 _ s2 _ h; simp [h]
    intros; exact .singleton _

  have h2 z : (μ.map Prod.snd).real {z} = ∑ y ∈ E1, μ.real {(y, z)} := by
    rw [map_measureReal_apply measurable_snd (.singleton _), ← measureReal_biUnion_finset]
    · apply measureReal_congr
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null ?_ hE
        intro ⟨s, u⟩ ⟨h1, h2⟩
        contrapose! h2
        simp at h1 h2 ⊢
        simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, E1, E,
          mem_support]
        constructor; use u; exact h1
      · convert measure_empty (μ := μ)
        rw [Set.diff_eq_empty]
        intro ⟨s, u⟩ h
        simp at h ⊢
        exact h.2
    · intro s1 _ s2 _ h; simp [h]
    intros; exact .singleton _
  let w (p : S × U) := (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2}
  let f (p : S × U) := ((μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2})⁻¹ * μ.real {p}
  have hw1 : ∀ p ∈ (E1 ×ˢ E2), 0 ≤ w p := by intros; positivity
  have hw2 : ∑ p ∈ E1 ×ˢ E2, w p = 1 := by
    rw [Finset.sum_product]
    simp [w, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
    rw [show (1 : ℝ) = 1 * 1 by norm_num]
    congr
    convert hE1'
    simp
  have hf : ∀ p ∈ E1 ×ˢ E2, 0 ≤ f p := by intros; positivity
  have H :=
  calc
    ∑ p ∈ E1 ×ˢ E2, w p * f p
        = ∑ p ∈ E1 ×ˢ E2, μ.real {p} := by
          congr with p
          by_cases hp : μ.real {p} = 0
          · simp [f, hp]
          · simp [w, f]
            field_simp [h_fst_ne_zero p hp, h_snd_ne_zero p hp]
      _ = 1 := by
        simp
        rw [show 1 = μ.real Set.univ by simp]
        apply measureReal_congr
        simp
        convert hE'
        simp
  have H1 : -measureMutualInfo (μ := μ) = ∑ p ∈ E1 ×ˢ E2, w p * negMulLog (f p) := calc
    _ = ∑ p ∈ E1 ×ˢ E2,
          (-(μ.real {p} * log (μ.real {p}))
          + (μ.real {p} * log ((μ.map Prod.snd).real {p.2})
            + μ.real {p} * log ((μ.map Prod.fst).real {p.1}))) := by
        have H0 : Hm[μ] = -∑ p ∈ E1 ×ˢ E2, μ.real {p} * log (μ.real {p}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE', negMulLog, neg_mul, Finset.sum_neg_distrib]
        have H1 : Hm[μ.map Prod.fst] = -∑ p ∈ E1 ×ˢ E2,
            μ.real {p} * log ((μ.map Prod.fst).real {p.1}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE1, negMulLog, neg_mul,
            Finset.sum_neg_distrib, Finset.sum_product, ← Finset.sum_mul]
          congr! with s _
          exact h1 s
        have H2 : Hm[μ.map Prod.snd] = -∑ p ∈ E1 ×ˢ E2, μ.real {p} * log ((μ.map Prod.snd).real {p.2}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE2, negMulLog, neg_mul, Finset.sum_neg_distrib, Finset.sum_product_right, ← Finset.sum_mul]
          congr! with s _
          exact h2 s
        simp_rw [measureMutualInfo_def, H0, H1, H2]
        simp [Finset.sum_add_distrib]
    _ = ∑ p ∈ E1 ×ˢ E2, w p * negMulLog (f p) := by
        congr! 1 with p _
        by_cases hp : μ.real {p} = 0
        · simp [f, hp]
        have := h_fst_ne_zero p hp
        have := h_snd_ne_zero p hp
        simp [negMulLog, log_mul, log_inv, h_fst_ne_zero p hp, h_snd_ne_zero p hp, hp, w, f]
        field_simp
        ring
  have H2 : 0 = negMulLog (∑ s ∈ (E1 ×ˢ E2), w s * f s) := by
    rw [H, negMulLog_one]
  constructor
  · rw [← neg_nonpos, H1]
    convert concaveOn_negMulLog.le_map_sum hw1 hw2 hf
  rw [← neg_eq_zero, H1, H2, eq_comm]
  refine (strictConcaveOn_negMulLog.map_sum_eq_iff' hw1 hw2 hf).trans ?_
  have w0 (p : S × U) (hp: w p = 0) : μ.real {p} = 0 := by
    simp only [mul_eq_zero, w] at hp
    rcases hp with hp | hp
    · contrapose! hp; exact (h_fst_ne_zero p) hp
    · contrapose! hp; exact (h_snd_ne_zero p) hp
  constructor
  · intro hyp p
    by_cases hp1 : p.1 ∈ E1
    · by_cases hp2 : p.2 ∈ E2
      · have hp : p ∈ E1 ×ˢ E2 := Finset.mem_product.mpr ⟨hp1, hp2⟩
        by_cases hw : w p = 0
        · rw [w0 p hw]
          exact hw.symm
        replace hyp := hyp p hp hw
        simp_rw [smul_eq_mul, H] at hyp
        have := eq_of_inv_mul_eq_one hyp
        convert this.symm
      have : {p.2} ⊆ (E2 : Set U)ᶜ := by
        simp only [Set.singleton_subset_iff, Set.mem_compl_iff, Finset.mem_coe]; convert hp2
      replace : (Measure.map Prod.snd μ).real {p.2} = 0 := by
        rw [measureReal_eq_zero_iff]; exact measure_mono_null this hE2
      have hp : μ.real {p} = 0 := by contrapose! this; exact (h_snd_ne_zero p) this
      simp [hp, this]
    have : {p.1} ⊆ (E1 : Set S)ᶜ := by
      simp only [Set.singleton_subset_iff, Set.mem_compl_iff, Finset.mem_coe]; convert hp1
    replace : (Measure.map Prod.fst μ).real {p.1} = 0 := by
      rw [measureReal_eq_zero_iff]; exact measure_mono_null this hE1
    have hp : μ.real {p} = 0 := by contrapose! this; exact (h_fst_ne_zero p) this
    simp [hp, this]
  intro hyp ⟨s, u⟩ _ hw
  simp_rw [smul_eq_mul, H]
  show (w (s,u))⁻¹ * (μ.real {(s,u)}) = 1
  have : w (s,u) ≠ 0 := by exact hw
  field_simp [this]
  rw [hyp (s,u)]

lemma measureMutualInfo_nonneg {μ : Measure (S × U)} [FiniteSupport μ] :
    0 ≤ Im[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  · rw [← measureMutualInfo_univ_smul μ]
    apply measureMutualInfo_nonneg_aux.1
  rw [measureMutualInfo_of_not_isFiniteMeasure hμ_fin]

lemma measureMutualInfo_eq_zero_iff {μ : Measure (S × U)} [FiniteSupport μ]
    [IsZeroOrProbabilityMeasure μ] :
    Im[μ] = 0 ↔ ∀ p, μ.real {p} = (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2} :=
  measureMutualInfo_nonneg_aux.2

end measureMutualInfo

end ProbabilityTheory

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function ProbabilityTheory

/-- Extension for `measureMutualInfo`. -/
@[positivity measureMutualInfo _]
def evalMeasureMutualInfo : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@measureMutualInfo $S $T $measS $measT $μ) =>
    assertInstancesCommute
    let _ ← synthInstanceQ q(MeasurableSingletonClass $S)
    let _ ← synthInstanceQ q(MeasurableSingletonClass $T)
    let _ ← synthInstanceQ q(FiniteSupport $μ)
    pure <| .nonnegative q(measureMutualInfo_nonneg)
  | _, _, _ => throwError "failed to match ProbabilityTheory.measureMutualInfo"

example {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSingletonClass S]
    [MeasurableSingletonClass T] {μ : Measure (S × T)} [FiniteSupport μ] : 0 ≤ Im[μ] := by
  positivity

end Mathlib.Meta.Positivity
