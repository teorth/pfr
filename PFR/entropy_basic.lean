import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import PFR.neg_xlogx

/-!
# Entropy and conditional entropy

## Main definitions

* `measureEntropy`: entropy of a measure
* `entropy`: entropy of a random variable, defined as `measureEntropy (volume.map X)`
* `condEntropy`: conditional entropy of a random variable `X` w.r.t. another one `Y`
* `mutualInformation`: mutual information of two random variables

## Main statements

* `chain_rule`: `entropy (fun ω ↦ (X ω, Y ω)) = entropy Y + condEntropy X Y`

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

@[simp]
lemma sum_measure_singleton {S : Type*} [Fintype S] {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] (μ : Measure S) :
    ∑ x, μ {x} = μ Set.univ := by
  change ∑ x, μ (id ⁻¹' {x}) = μ Set.univ
  rw [sum_measure_preimage_singleton]
  · simp
  · simp

@[simp]
lemma sum_toReal_measure_singleton {S : Type*} [Fintype S] {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] (μ : Measure S) [IsFiniteMeasure μ] :
    ∑ x : S, (μ {x}).toReal = (μ Set.univ).toReal := by
  rw [← ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)]
  simp

end aux_lemmas




namespace ProbabilityTheory

variable {Ω S T : Type*} [mΩ : MeasurableSpace Ω]
  [Fintype S] [Fintype T] [MeasurableSpace S] [MeasurableSpace T]

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

notation:100 "Hm[" μ "]" => measureEntropy μ

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

lemma measureEntropy_map_of_injective [MeasurableSingletonClass T]
    (μ : Measure S) (f : S → T) (hf : Function.Injective f) (hf_m : Measurable f) :
    Hm[μ.map f] = Hm[μ] := by
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

section entropy

variable {μ : Measure Ω} {X : Ω → S} {Y : Ω → T}

/-- Entropy of a random variable with values in a finite measurable space. -/
noncomputable
def entropy (X : Ω → S) (μ : Measure Ω := by volume_tac) := Hm[μ.map X]

notation3:100 "H[" X "; " μ "]" => entropy X μ
notation3:100 "H[" X "]" => entropy X volume
notation3:100 "H[" X "|" Y "←" y "; " μ "]" => entropy X (μ[|Y ⁻¹' {y}])
notation3:100 "H[" X "|" Y "←" y "]" => entropy X (ℙ[|Y ⁻¹' {y}])

lemma entropy_def (X : Ω → S) (μ : Measure Ω) : entropy X μ = Hm[μ.map X] := rfl

lemma entropy_nonneg (X : Ω → S) (μ : Measure Ω) : 0 ≤ entropy X μ := measureEntropy_nonneg _

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
lemma entropy_comp_of_injective [MeasurableSingletonClass T]
    (μ : Measure Ω) (hX : Measurable X)
    (f : S → T) (hf : Function.Injective f) (hf_m : Measurable f) :
    H[f ∘ X ; μ] = H[X ; μ] := by
  rw [entropy_def, ← Measure.map_map hf_m hX, measureEntropy_map_of_injective _ _ hf hf_m,
    entropy_def]

/-- If $X$ is $S$-valued random variable, then $H[X] = \log |S|$ if and only if $X$ is uniformly
distributed. -/
lemma entropy_eq_log_card : 0 = 1 := sorry

/-- If $X$ is an $S$-valued random variable, then there exists $s \in S$ such that
$P[X=s] \geq \exp(-H[X])$. -/
lemma prob_ge_exp_neg_entropy : 0 = 1 := sorry

lemma entropy_comm (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    entropy (fun ω ↦ (X ω, Y ω)) μ = entropy (fun ω ↦ (Y ω, X ω)) μ := sorry

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

notation3:100 "H[" X "|" Y "; " μ "]" => condEntropy X Y μ
notation3:100 "H[" X "|" Y "]" => condEntropy X Y volume

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

/-- If $X: \Omega \to S$, $Y: \Omega \to T$, and $Z: \Omega \to U$ are random variables, and $Y = f(X,Z)$ almost surely for some map $f: S \times U \to T$ that is injective for each fixed $U$, then $H[X|Z] = H[Y|Z]$.-/
lemma condEntropy_of_inj_map : 0 = 1 := sorry


end condEntropy

section pair
variable {X : Ω → S} {Y : Ω → T} [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  {μ : Measure Ω}

lemma measure_prod_singleton_eq_mul [IsFiniteMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) {p : S × T} :
    (μ.map (fun ω ↦ (X ω, Y ω)) {p}).toReal
      = (μ.map Y {p.2}).toReal * ((μ[|Y ⁻¹' {p.2}]).map X {p.1}).toReal := by
  have hp_prod : {p} = {p.1} ×ˢ {p.2} := by simp
  rw [Measure.map_apply (hX.prod_mk hY) (measurableSet_singleton p)]
  by_cases hpY : μ (Y ⁻¹' {p.2}) = 0
  · rw [cond_eq_zero_of_measure_zero hpY]
    simp only [aemeasurable_zero_measure, not_true, Measure.map_zero, Measure.zero_toOuterMeasure,
      OuterMeasure.coe_zero, Pi.zero_apply, ENNReal.zero_toReal, mul_zero]
    suffices (μ ((fun a ↦ (X a, Y a)) ⁻¹' ({p.1} ×ˢ {p.2}))).toReal = 0 by convert this
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
    negIdMulLog (μ.map (fun ω ↦ (X ω, Y ω)) {p}).toReal
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
    H[fun ω ↦ (X ω, Y ω) ; μ] = H[Y ; μ] + H[X | Y ; μ] := by
  have : IsProbabilityMeasure (μ.map Y) := isProbabilityMeasure_map hY.aemeasurable
  have : IsProbabilityMeasure (μ.map (fun ω ↦ (X ω, Y ω))) :=
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

/-- Data-processing inequality for the entropy. -/
lemma entropy_comp_le {U : Type*} [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) {f : S → U} (hf : Measurable f) :
    H[f ∘ X ; μ] ≤ H[X ; μ] := by
  have : H[X ; μ] = H[fun ω ↦ (X ω, (f ∘ X) ω) ; μ] := by
    refine (entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) ?_ ?_).symm
    · intro x y hxy
      simp only [Prod.mk.injEq] at hxy
      exact hxy.1
    · exact measurable_id.prod_mk hf
  rw [this, chain_rule _ hX (hf.comp hX)]
  simp only [le_add_iff_nonneg_right]
  exact condEntropy_nonneg X (f ∘ X) μ

/--   If $X: \Omega \to S$, $Y: \Omega \to T$, $Z: \Omega \to U$ are random variables, then
$$ H[  X,Y | Z ] = H[Y | Z] + H[X|Y, Z].$$ -/
lemma cond_chain_rule : 0 = 1 := sorry

end pair

section mutualInformation

variable {U : Type*} [Fintype U] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

/-- Mutual information (TODO docstring). -/
noncomputable
def mutualInformation (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[fun ω ↦ (X ω, Y ω) ; μ]

lemma mutualInformation_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
  mutualInformation X Y μ = H[X ; μ] + H[Y ; μ] - H[fun ω ↦ (X ω, Y ω) ; μ] := rfl

notation3:100 "I[" X ":" Y ";" μ "]" => mutualInformation X Y μ
notation3:100 "I[" X ":" Y "]" => mutualInformation X Y volume

lemma mutualInformation_eq_entropy_sub_condEntropy [MeasurableSingletonClass S]
    [MeasurableSingletonClass T] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  rw [mutualInformation_def, chain_rule μ hX hY]
  abel

lemma mutualInformation_comm (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    I[X : Y ; μ] = I[Y : X ; μ] := by simp_rw [mutualInformation, add_comm, entropy_comm X Y]

lemma mutualInformation_nonneg (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    0 ≤ I[X : Y ; μ] := sorry

/-- Subadditivity of entropy. -/
lemma entropy_pair_le_add (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    H[fun ω ↦ (X ω, Y ω) ; μ] ≤ H[X ; μ] + H[Y ; μ] :=
  sub_nonneg.1 $ mutualInformation_nonneg _ _ _

noncomputable
def condMutualInformation (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω := by volume_tac) :
    ℝ := (μ.map Z)[fun z ↦ H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[fun ω ↦ (X ω, Y ω) | Z ← z ; μ]]

lemma condMutualInformation_def (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) :
    condMutualInformation X Y Z μ = (μ.map Z)[fun z ↦
      H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[fun ω ↦ (X ω, Y ω) | Z ← z ; μ]] := rfl

lemma condMutualInformation_eq_integral_mutualInformation :
    condMutualInformation X Y Z μ = (μ.map Z)[fun z ↦ I[X : Y ; μ[|Z ⁻¹' {z}]]] := rfl

lemma condMutualInformation_comm (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) :
    condMutualInformation X Y Z μ = condMutualInformation Y X Z μ := by
  simp_rw [condMutualInformation_def, add_comm, entropy_comm X]

lemma condMutualInformation_nonneg (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) :
    0 ≤ condMutualInformation X Y Z μ :=
  integral_nonneg fun _x ↦ mutualInformation_nonneg _ _ _

/-- $$ I[X:Y|Z] := H[X|Z] + H[Y|Z] - H[X,Y|Z].$$ -/
lemma condMutualInformation_eq : 0 = 1 := by sorry

section IsProbabilityMeasure
variable (μ : Measure Ω) [IsProbabilityMeasure μ] [MeasurableSingletonClass S]
  [MeasurableSingletonClass T]

lemma entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) :
    H[X ; μ] - H[X | Y ; μ] = I[X : Y ; μ] := by
  rw [mutualInformation_def, chain_rule _ hX hY, add_comm, add_sub_add_left_eq_sub]

lemma condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y) : H[X | Y ; μ] ≤ H[X ; μ] :=
  sub_nonneg.1 $ by rw [entropy_sub_condEntropy _ hX hY]; exact mutualInformation_nonneg _ _ _

/-- $H[X|Y,Z] \leq H[X|Z]$ -/
lemma entropy_submodular : 0 = 1 := sorry

/-- $$ H[X,Y,Z] + H[Z] \leq H[X,Z] + H[Y,Z].$$ -/
lemma entropy_triple_add_entropy_le :
    H[fun ω ↦ (X ω, Y ω, Z ω) ; μ] + H[Z ; μ] ≤
      H[fun ω ↦ (X ω, Z ω) ; μ] + H[fun ω ↦ (Y ω, Z ω) ; μ] := sorry

variable {μ : Measure Ω}

lemma entropy_pair_eq_add : H[fun ω ↦ (X ω, Y ω) ; μ] = H[X ; μ] + H[Y ; μ] ↔ IndepFun X Y μ :=
  sorry

/-- $I[X:Y]=0$ iff $X,Y$ are independent. -/
lemma mutualInformation_eq_zero : I[X : Y ; μ] = 0 ↔ IndepFun X Y μ :=
  sub_eq_zero.trans $ eq_comm.trans entropy_pair_eq_add

/-- $I[X:Y|Z]=0$ iff $X,Y$ are conditionally independent over $Z$. -/
lemma condMutualInformation_eq_zero : 0 = 1 := sorry

end IsProbabilityMeasure
end mutualInformation

section copy

/-- X' is a copy of X if they have the same distribution -/
def isCopy [Fintype S] (X : Ω → S) (X' : Ω' → S) : Prop := sorry

/-- If $X'$ is a copy of $X$ then $H[X'] = H[X]$. --/
lemma entropy_of_copy : 0 = 1 := by sorry

/-- Let $X_i : \Omega_i \to S_i$ be random variables for $i=1,\dots,k$.  Then there exist jointly independent random variables $X'_i: \Omega' \to S_i$ for $i=1,\dots,k$ such that each $X'_i$ is a copy of $X_i$.  May need to be a constructive method rather than a function -/
def independent_copies : 0 = 1 := by sorry

/-- For $X,Y$ random variables, there is a canonical choice of conditionally independent trials $X_1,X_2,Y'$.-/
def condIndependent_copies : 0=1 := by sorry


end copy


end ProbabilityTheory



section MeasureSpace_example

open ProbabilityTheory

variable {Ω S T : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T}

example (hX : Measurable X) (hY : Measurable Y) :
  H[fun ω ↦ (X ω, Y ω)] = H[Y] + H[X | Y] := chain_rule _ hX hY

end MeasureSpace_example
