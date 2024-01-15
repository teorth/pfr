import PFR.ForMathlib.Entropy.Kernel.MutualInfo
import PFR.ForMathlib.Entropy.Kernel.Basic
import PFR.ForMathlib.Uniform
import PFR.Mathlib.Probability.Independence.Conditional

/-!
# Entropy and conditional entropy

## Main definitions

* `entropy`: entropy of a random variable, defined as `measureEntropy (volume.map X)`
* `condEntropy`: conditional entropy of a random variable `X` w.r.t. another one `Y`
* `mutualInfo`: mutual information of two random variables

## Main statements

* `chain_rule`: $H[⟨X, Y⟩] = H[Y] + H[X | Y]$
* `entropy_cond_le_entropy`: $H[X | Y] ≤ H[X]$. (Chain rule another way.)
* `entropy_triple_add_entropy_le`: $H[X, Y, Z] + H[Z] ≤ H[X, Z] + H[Y, Z]$. (Submodularity of entropy.)

## Notations

* `H[X] = entropy X`
* `H[X | Y ← y] = Hm[(ℙ[|Y ← y]).map X]`
* `H[X | Y] = condEntropy X Y`, such that `H[X | Y] = (volume.map Y)[fun y ↦ H[X | Y ← y]]`
* `I[X : Y] = mutualInfo X Y`

All notations have variants where we can specify the measure (which is otherwise
supposed to be `volume`). For example `H[X ; μ]` and `I[X : Y ; μ]` instead of `H[X]` and
`I[X : Y]` respectively.

-/

open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

namespace ProbabilityTheory

universe uΩ uS uT uU

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU} [mΩ : MeasurableSpace Ω]
  [Countable S] [Countable T] [Countable U]
  [Nonempty S] [Nonempty T] [Nonempty U]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
  {μ : Measure Ω}

section entropy

/-- Entropy of a random variable with values in a finite measurable space. -/
noncomputable
def entropy (X : Ω → S) (μ : Measure Ω := by volume_tac) := Hm[μ.map X]

@[inherit_doc entropy] notation3:max "H[" X " ; " μ "]" => entropy X μ
@[inherit_doc entropy] notation3:max "H[" X "]" => entropy X volume
@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y " ; " μ "]" => entropy X (μ[|Y ← y])
@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "]" => entropy X (ℙ[|Y ← y])

/-- Entropy of a random variable agrees with entropy of its distribution. -/
lemma entropy_def (X : Ω → S) (μ : Measure Ω) : entropy X μ = Hm[μ.map X] := rfl

/-- Entropy of a random variable is also the kernel entropy of the distribution over a Dirac mass. -/
lemma entropy_eq_kernel_entropy (X : Ω → S) (μ : Measure Ω) :
    H[X ; μ] = Hk[kernel.const Unit (μ.map X), Measure.dirac ()] := by
  simp only [kernel.entropy, kernel.const_apply, integral_const, MeasurableSpace.measurableSet_top,
    Measure.dirac_apply', Set.mem_univ, Set.indicator_of_mem, Pi.one_apply, ENNReal.one_toReal,
    smul_eq_mul, one_mul]
  rfl

/-- Any variable on a zero measure space has zero entropy. -/
@[simp]
lemma entropy_zero_measure (X : Ω → S) : H[X ; (0 : Measure Ω)] = 0 := by simp [entropy]

/-- Two variables that agree almost everywhere, have the same entropy. -/
lemma entropy_congr {X X' : Ω → S} (h : X =ᵐ[μ] X') : H[X ; μ] = H[X' ; μ] := by
  rw [entropy_def, Measure.map_congr h, entropy_def]

/-- Entropy is always non-negative. -/
lemma entropy_nonneg (X : Ω → S) (μ : Measure Ω) : 0 ≤ entropy X μ := measureEntropy_nonneg _

/-- Two variables that have the same distribution, have the same entropy. -/
lemma IdentDistrib.entropy_eq {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} {X' : Ω' → S}
    (h : IdentDistrib X X' μ μ') : H[X ; μ] = H[X' ; μ'] := by
  simp [entropy_def, h.map_eq]

/-- Entropy is at most the logarithm of the cardinality of the range. -/
lemma entropy_le_log_card [Fintype S] (X : Ω → S) (μ : Measure Ω) : H[X ; μ] ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card _

/-- Entropy is at most the logarithm of the cardinality of a set in which X almost surely takes values in. -/
lemma entropy_le_log_card_of_mem {A : Finset S} {μ : Measure Ω} {X : Ω → S}
    (hX : Measurable X) (h : ∀ᵐ ω ∂μ, X ω ∈ A) :
    H[X ; μ] ≤ log (Nat.card A) := by
  apply measureEntropy_le_log_card_of_mem
  rwa [Measure.map_apply hX (measurableSet_discrete _)]

/-- $H[X] = \sum_s P[X=s] \log \frac{1}{P[X=s]}$. -/
lemma entropy_eq_sum (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    entropy X μ = ∑' x, negMulLog (μ.map X {x}).toReal := by
  have : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  rw [entropy_def, measureEntropy_of_isProbabilityMeasure]

lemma entropy_eq_sum' (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    entropy X μ = ∑' x, negMulLog ((μ.map X).real {x}) := by
  have : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  simp only [entropy_def, measureEntropy_of_isProbabilityMeasure, Measure.real]

lemma entropy_eq_sum_finset (hX : Measurable X) {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Finset S} (hA : (μ.map X) Aᶜ = 0):
    entropy X μ = ∑ x in A, negMulLog (μ.map X {x}).toReal := by
  rw [entropy_eq_sum hX]
  convert tsum_eq_sum ?_
  intro s hs
  convert negMulLog_zero
  convert ENNReal.zero_toReal
  convert measure_mono_null ?_ hA
  simp [hs]

lemma entropy_eq_sum_finset' (hX : Measurable X) {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Finset S} (hA : (μ.map X) Aᶜ = 0):
    entropy X μ = ∑ x in A, negMulLog ((μ.map X).real {x}) := entropy_eq_sum_finset hX hA

lemma entropy_eq_sum_finiteRange (hX : Measurable X) {μ : Measure Ω} [IsProbabilityMeasure μ] [FiniteRange X]:
    entropy X μ = ∑ x in FiniteRange.toFinset X, negMulLog (μ.map X {x}).toReal :=  entropy_eq_sum_finset hX (A := FiniteRange.toFinset X) (full_measure_of_finiteRange hX)

lemma entropy_eq_sum_finiteRange' (hX : Measurable X) {μ : Measure Ω} [IsProbabilityMeasure μ] [FiniteRange X]:
    entropy X μ = ∑ x in FiniteRange.toFinset X, negMulLog ((μ.map X).real {x}) :=  entropy_eq_sum_finiteRange hX

/-- $H[X|Y=y] = \sum_s P[X=s|Y=y] \log \frac{1}{P[X=s|Y=y]}$. -/
lemma entropy_cond_eq_sum (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] (y : T) :
    H[X | Y ← y ; μ] = ∑' x, negMulLog ((μ[|Y ← y]).map X {x}).toReal := by
  by_cases hy : μ (Y ⁻¹' {y}) = 0
  · rw [entropy_def, cond_eq_zero_of_measure_eq_zero hy]
    simp
  · have : IsProbabilityMeasure (μ[|Y ← y]) := cond_isProbabilityMeasure _ hy
    rw [entropy_eq_sum hX]

lemma entropy_cond_eq_sum_finiteRange (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] (y : T) [FiniteRange X]:
    H[X | Y ← y ; μ] = ∑ x in FiniteRange.toFinset X, negMulLog ((μ[|Y ← y]).map X {x}).toReal := by
  by_cases hy : μ (Y ⁻¹' {y}) = 0
  · rw [entropy_def, cond_eq_zero_of_measure_eq_zero hy]
    simp
  · have : IsProbabilityMeasure (μ[|Y ← y]) := cond_isProbabilityMeasure _ hy
    rw [entropy_eq_sum_finiteRange hX]

/-- If $X$, $Y$ are $S$-valued and $T$-valued random variables, and $Y = f(X)$ for
some injection $f : S \to T$, then $H[Y] = H[X]$. One can also use `entropy_of_comp_eq_of_comp` as an alternative if verifying injectivity is fiddly. For the upper bound only, see `entropy_comp_le`. -/
lemma entropy_comp_of_injective
    (μ : Measure Ω) (hX : Measurable X) (f : S → T) (hf : Function.Injective f) :
    H[f ∘ X ; μ] = H[X ; μ] := by
  have hf_m : Measurable f := measurable_of_countable f
  rw [entropy_def, ← Measure.map_map hf_m hX, measureEntropy_map_of_injective _ _ hf_m hf,
    entropy_def]


/-- The entropy of any constant is zero. -/
@[simp] lemma entropy_const [IsProbabilityMeasure μ] (c : S) : H[fun _ ↦ c ; μ] = 0 := by
  simp [entropy, Measure.map_const]

open Set

open Function

/-- If $X$ is uniformly distributed on $H$, then $H[X] = \log |H|$.
-/
lemma IsUniform.entropy_eq (H : Finset S) (X : Ω → S) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsUniform H X μ) (hX' : Measurable X) : H[X ; μ] = log (Nat.card H) := by
  haveI : IsProbabilityMeasure (μ.map X) := isProbabilityMeasure_map hX'.aemeasurable
  have : ∀ (t : S), negMulLog ((μ.map X).real {t}) = ((μ.map X).real {t}) * log (Nat.card H)
  · intro t
    by_cases ht : t ∈ H
    · simp only [negMulLog, neg_mul, neg_mul_eq_mul_neg, IsUniform.measureReal_preimage_of_mem'
        hX hX' ht, one_div, log_inv, neg_neg]
    · simp only [negMulLog, map_measureReal_apply hX' (MeasurableSet.singleton t),
      IsUniform.measureReal_preimage_of_nmem hX ht, neg_zero, log_zero, mul_zero, zero_mul]
  rw [entropy_eq_sum_finset' (A := H) hX', Finset.sum_congr rfl (fun t _ ↦ this t), ← Finset.sum_mul,
    Finset.sum_realMeasure_singleton]
  . convert one_mul _
    have := IsUniform.full_measure hX hX'
    simp at this
    rw [Measure.real, this]
    simp
  rw [Measure.map_apply hX' (by measurability)]
  exact hX.measure_preimage_compl


/-- Variant of `IsUniform.entropy_eq` where `H` is a finite `Set` rather than `Finset`. -/
lemma IsUniform.entropy_eq' {H : Set S} [Finite H] {X : Ω → S} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsUniform H X μ) (hX' : Measurable X) : H[X ; μ] = log (Nat.card H) := by
  convert IsUniform.entropy_eq H.toFinite.toFinset X ?_ hX' with x
  . simp; exact Iff.rfl
  . infer_instance
  convert hX
  simp

/-- If $X$ is $S$-valued random variable, then $H[X] = \log |S|$ if and only if $X$ is uniformly
distributed. -/
lemma entropy_eq_log_card {X : Ω → S} [Fintype S] (hX : Measurable X) (μ : Measure Ω) [hμ : NeZero μ]
    [IsFiniteMeasure μ] :
    entropy X μ = log (Fintype.card S) ↔ ∀ s, μ.map X {s} = μ Set.univ / Fintype.card S := by
  rcases eq_zero_or_neZero (μ.map X) with h | h
  . have := Measure.le_map_apply (@Measurable.aemeasurable Ω S _ _ X μ hX) Set.univ
    simp [h] at this; simp [this] at hμ
  have : IsFiniteMeasure (μ.map X) := by
    apply Measure.isFiniteMeasure_map
  rw [entropy_def, measureEntropy_eq_card_iff_measure_eq, Measure.map_apply hX MeasurableSet.univ]
  simp

/-- If $X$ is an $S$-valued random variable, then there exists $s \in S$ such that
$P[X=s] \geq \exp(-H[X])$.  TODO: remove the probability measure hypothesis, which is unncessary here. -/
lemma prob_ge_exp_neg_entropy (X : Ω → S) (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) [hX': FiniteRange X] :
    ∃ s : S, μ.map X {s} ≥ (μ Set.univ) * (rexp (- H[X ; μ])).toNNReal := by
  let μS := μ.map X
  let μs s := μS {s}
  rcases finiteSupport_of_finiteRange (X := X) with ⟨A, hA⟩

  let S_nonzero := A.filter (fun s ↦ μs s ≠ 0)

  set norm := μS A with rw_norm
  have h_norm : norm = μ Set.univ := by
    have := measure_add_measure_compl (μ := μS) (s := A) (Finset.measurableSet _)
    rw [hA, add_zero] at this
    simp [this, Measure.map_apply hX MeasurableSet.univ]

  let pdf_nn s := norm⁻¹ * μs s
  let pdf s := (pdf_nn s).toReal
  let neg_log_pdf s := -log (pdf s)

  rcases Finset.eq_empty_or_nonempty S_nonzero with h_empty | h_nonempty
  . have h_norm_zero : μ Set.univ = 0 := by
      have h : ∀ s ∈ A, μs s ≠ 0 → μs s ≠ 0 := fun _ _ h ↦ h
      rw [← h_norm, rw_norm, ← Finset.sum_measure_singleton, ← Finset.sum_filter_of_ne h,
        show Finset.filter _ _ = S_nonzero from rfl, h_empty, show Finset.sum ∅ μs = 0 from rfl]
    use Classical.arbitrary (α := S)
    rw [h_norm_zero, zero_mul]
    exact le_of_not_gt ENNReal.not_lt_zero

  rcases exists_or_forall_not (fun s ↦ μ.map X {s} = ∞) with h_infty | h_finite
  . obtain ⟨s, h_s⟩ := h_infty
    use s; rw [h_s] ; exact le_top

  rcases eq_zero_or_neZero μ with h_zero_measure | _
  . use Classical.arbitrary (α := S)
    rw [h_zero_measure, show (0 : Measure Ω) _ = 0 from rfl, zero_mul]
    exact zero_le _

  have h_norm_pos : 0 < norm := by
    rw [h_norm, Measure.measure_univ_pos]
    exact NeZero.ne μ
  have h_norm_finite : norm < ∞ := by
    rw [rw_norm, ← Finset.sum_measure_singleton]
    exact ENNReal.sum_lt_top (fun s _ ↦ h_finite s)
  have h_invinvnorm_finite : norm⁻¹⁻¹ ≠ ∞ := by
    rw [inv_inv]
    exact LT.lt.ne_top h_norm_finite
  have h_invnorm_ne_zero : norm⁻¹ ≠ 0 := ENNReal.inv_ne_top.mp h_invinvnorm_finite
  have h_invnorm_finite : norm⁻¹ ≠ ∞ := by
    rw [← ENNReal.inv_ne_zero, inv_inv]
    exact ne_zero_of_lt h_norm_pos
  have h_pdf_finite : ∀ s, pdf_nn s ≠ ∞ := fun s ↦ ENNReal.mul_ne_top h_invnorm_finite (h_finite s)

  have h_norm_cancel : norm * norm⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ne_zero_of_lt h_norm_pos) (LT.lt.ne_top h_norm_finite)
  have h_pdf1 : (∑ s in A, pdf s) = 1 := by
    rw [← ENNReal.toReal_sum (fun s _ ↦ h_pdf_finite s), ← Finset.mul_sum,
      Finset.sum_measure_singleton, mul_comm, h_norm_cancel, ENNReal.one_toReal]

  let ⟨s_max, hs, h_min⟩ := Finset.exists_min_image S_nonzero neg_log_pdf h_nonempty
  have h_pdf_s_max_pos : 0 < pdf s_max := by
    rw [Finset.mem_filter] at hs
    have h_nonzero : pdf s_max ≠ 0 := ENNReal.toReal_ne_zero.mpr
      ⟨mul_ne_zero h_invnorm_ne_zero hs.2, ENNReal.mul_ne_top h_invnorm_finite (h_finite s_max)⟩
    exact LE.le.lt_of_ne ENNReal.toReal_nonneg h_nonzero.symm

  use s_max
  rw [← h_norm, ← one_mul (μ.map X _), ← h_norm_cancel, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt h_norm_pos)
  show ENNReal.ofReal (rexp (-H[X ; μ])) ≤ pdf_nn s_max
  rw [ENNReal.ofReal_le_iff_le_toReal (h_pdf_finite _),
    show (pdf_nn _).toReal = pdf _ from rfl, ← Real.exp_log h_pdf_s_max_pos]
  apply exp_monotone
  rw [neg_le, ← one_mul (-log _), ← h_pdf1, Finset.sum_mul]
  let g_lhs s := pdf s * neg_log_pdf s_max
  let g_rhs s := -pdf s * log (pdf s)
  suffices : ∑ s in A, g_lhs s ≤ ∑ s in A, g_rhs s
  . convert this
    rw [entropy_eq_sum_finset hX hA]
    congr with s
    simp [negMulLog, g_rhs]
    simp at h_norm
    rw [h_norm]
    simp
  have h_lhs : ∀ s, μs s = 0 → g_lhs s = 0 := by {intros _ h; simp [h]}
  have h_rhs : ∀ s, μs s = 0 → g_rhs s = 0 := by {intros _ h; simp [h]}
  rw [← Finset.sum_filter_of_ne (fun s _ ↦ (h_lhs s).mt),
    ← Finset.sum_filter_of_ne (fun s _ ↦ (h_rhs s).mt)]
  apply Finset.sum_le_sum
  intros s h_s
  rw [show g_lhs s = _ * _ from rfl, show g_rhs s = _ * _ from rfl, neg_mul_comm]
  exact mul_le_mul_of_nonneg_left (h_min s h_s) ENNReal.toReal_nonneg

/-- If $X$ is an $S$-valued random variable, then there exists $s \in S$ such that
$P[X=s] \geq \exp(-H[X])$. -/
lemma prob_ge_exp_neg_entropy' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → S) (hX : Measurable X) [FiniteRange X] :
    ∃ s : S, rexp (- H[X ; μ]) ≤ μ.real (X ⁻¹' {s}) := by
  obtain ⟨s, hs⟩ := prob_ge_exp_neg_entropy X μ hX
  use s
  rwa [IsProbabilityMeasure.measure_univ, one_mul, ge_iff_le,
    (show ENNReal.ofNNReal _ = ENNReal.ofReal _ from rfl),
    ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _), ← Measure.real,
    map_measureReal_apply hX (MeasurableSet.singleton s)] at hs

/-- If $X$ is an $S$-valued random variable of non-positive entropy, then $X$ is almost surely constant. -/
lemma const_of_nonpos_entropy {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → S} (hX : Measurable X) [FiniteRange X] (hent: H[X; μ] ≤ 0):
    ∃ s : S, μ.real (X ⁻¹' {s}) = 1 := by
    rcases prob_ge_exp_neg_entropy' (μ := μ) X hX with ⟨ s, hs ⟩
    use s
    apply LE.le.antisymm
    . rw [← IsProbabilityMeasure.measureReal_univ (μ := μ)]
      exact measureReal_mono (subset_univ _) (by finiteness)
    refine le_trans ?_ hs
    simp [hent]


/-- $H[X, Y] = H[Y, X]$. -/
lemma entropy_comm (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X, Y⟩; μ] = H[⟨Y, X⟩ ; μ] := by
  change H[Prod.swap ∘ ⟨Y, X⟩ ; μ] = H[⟨Y, X⟩ ; μ]
  exact entropy_comp_of_injective μ (hY.prod_mk hX) Prod.swap Prod.swap_injective

/-- $H[(X, Y), Z] = H[X, (Y, Z)]$. -/
lemma entropy_assoc (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) :
    H[⟨X, ⟨Y, Z⟩⟩ ; μ] = H[⟨⟨X, Y⟩, Z⟩ ; μ] := by
  change H[Equiv.prodAssoc _ _ _ ∘ ⟨⟨X, Y⟩, Z⟩ ; μ] = H[⟨⟨X, Y⟩, Z⟩ ; μ]
  exact entropy_comp_of_injective μ ((hX.prod_mk hY).prod_mk hZ) _ $ Equiv.injective _

/-- $H[X, f(X)] = H[X]$.-/
@[simp] lemma entropy_prod_comp (hX : Measurable X) (μ : Measure Ω) (f : S → T) :
    H[⟨X, f ∘ X⟩; μ] = H[X ; μ] :=
  entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) fun _ _ ab ↦ (Prod.ext_iff.1 ab).1

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

@[inherit_doc condEntropy] notation3:max "H[" X " | " Y " ; " μ "]" => condEntropy X Y μ
@[inherit_doc condEntropy] notation3:max "H[" X " | " Y "]" => condEntropy X Y volume

lemma condEntropy_eq_zero
    (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] (t : T) (ht : (μ.map Y {t}).toReal = 0) : H[X | Y ← t ; μ] = 0 := by
  convert entropy_zero_measure X
  apply cond_eq_zero_of_measure_eq_zero
  rw [Measure.map_apply hY (MeasurableSet.singleton t)] at ht
  rw [← measureReal_eq_zero_iff]
  exact ht

/-- Conditional entropy of a random variable is equal to the entropy of its conditional kernel. -/
lemma condEntropy_eq_kernel_entropy
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] [FiniteRange Y] :
    H[X | Y ; μ] = Hk[condDistrib X Y μ, μ.map Y] := by
  rw [condEntropy_def, kernel.entropy]
  apply integral_congr_finiteSupport
  intro t ht
  simp only [ENNReal.toReal_eq_zero_iff, measure_ne_top (μ.map Y), or_false] at ht
  rw [Measure.map_apply hY (measurableSet_singleton _)] at ht
  simp only [entropy_def]
  congr
  ext S hS
  rw [condDistrib_apply' hX hY _ _ ht hS, Measure.map_apply hX hS,
      cond_apply _ (hY (measurableSet_singleton _))]

/-- The law of $(X, Z)$ is the image of the law of $(Z, X)$.-/
lemma map_prod_comap_swap (hX : Measurable X) (hZ : Measurable Z) (μ : Measure Ω) :
    (μ.map (fun ω ↦ (X ω, Z ω))).comap Prod.swap = μ.map (fun ω ↦ (Z ω, X ω)) := by
  ext s hs
  rw [Measure.map_apply (hZ.prod_mk hX) hs, Measure.comap_apply _ Prod.swap_injective _ _ hs]
  · rw [Measure.map_apply (hX.prod_mk hZ)]
    · congr with ω
      simp only [Set.image_swap_eq_preimage_swap, Set.mem_preimage, Prod.swap_prod_mk]
    · exact MeasurableEquiv.prodComm.measurableEmbedding.measurableSet_image' hs
  · exact fun t ht ↦ MeasurableEquiv.prodComm.measurableEmbedding.measurableSet_image' ht

lemma condEntropy_two_eq_kernel_entropy (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteRange Y] [FiniteRange Z] :
    H[X | ⟨Y, Z⟩ ; μ] =
      Hk[kernel.condKernel (condDistrib (fun a ↦ (Y a, X a)) Z μ),
        Measure.map Z μ ⊗ₘ kernel.fst (condDistrib (fun a ↦ (Y a, X a)) Z μ)] := by
  rw [Measure.compProd_congr (condDistrib_fst_ae_eq hY hX hZ μ),
      map_compProd_condDistrib hY hZ,
      kernel.entropy_congr (condKernel_condDistrib_ae_eq hY hX hZ μ),
      ← kernel.entropy_congr (swap_condDistrib_ae_eq hY hX hZ μ)]
  have : μ.map (fun ω ↦ (Z ω, Y ω)) = (μ.map (fun ω ↦ (Y ω, Z ω))).comap Prod.swap := by
    rw [map_prod_comap_swap hY hZ]
  rw [this, condEntropy_eq_kernel_entropy hX (hY.prod_mk hZ), kernel.entropy_comap_swap]

/-- Any random variable on a zero measure space has zero conditional entropy. -/
@[simp]
lemma condEntropy_zero_measure (X : Ω → S) (Y : Ω → T) : H[X | Y ; (0 : Measure Ω)] = 0 :=
  by simp [condEntropy]

/-- Conditional entropy is non-negative. -/
lemma condEntropy_nonneg (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : 0 ≤ H[X | Y ; μ] :=
  integral_nonneg (fun _ ↦ measureEntropy_nonneg _)

/-- Conditional entropy is at most the logarithm of the cardinality of the range. -/
lemma condEntropy_le_log_card [MeasurableSingletonClass S] [Fintype S]
    (X : Ω → S) (Y : Ω → T) (hY : Measurable Y) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    H[X | Y ; μ] ≤ log (Fintype.card S) := by
  refine (integral_mono_of_nonneg ?_ (integrable_const (log (Fintype.card S))) ?_).trans ?_
  · exact ae_of_all _ (fun _ ↦ entropy_nonneg _ _)
  · exact ae_of_all _ (fun _ ↦ entropy_le_log_card _ _)
  · have : IsProbabilityMeasure (μ.map Y) := isProbabilityMeasure_map hY.aemeasurable
    simp

/-- $H[X|Y] = \sum_y P[Y=y] H[X|Y=y]$.-/
lemma condEntropy_eq_sum [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω → T) (μ : Measure Ω)
    [IsFiniteMeasure μ] (hY: Measurable Y) [FiniteRange Y]:
    H[X | Y ; μ] = ∑ y in FiniteRange.toFinset Y, (μ.map Y {y}).toReal * H[X | Y ← y ; μ] := by
  rw [condEntropy_def, integral_eq_sum' (s := FiniteRange.toFinset Y) _ _]
  simp_rw [smul_eq_mul]
  exact full_measure_of_finiteRange hY

/-- $H[X|Y] = \sum_y P[Y=y] H[X|Y=y]$.-/
lemma condEntropy_eq_sum_fintype
    [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω → T) (μ : Measure Ω)
    [IsFiniteMeasure μ] (hY : Measurable Y) [Fintype T] :
    H[X | Y ; μ] = ∑ y, (μ (Y ⁻¹' {y})).toReal * H[X | Y ← y ; μ] := by
  rw [condEntropy_def, integral_eq_sum]
  simp_rw [smul_eq_mul, Measure.map_apply hY (measurableSet_singleton _)]

lemma condEntropy_prod_eq_sum {X : Ω → S} {Y : Ω → T} {Z : Ω → T'} [MeasurableSpace T']
    [MeasurableSingletonClass T']
    (μ : Measure Ω) (hY : Measurable Y) (hZ : Measurable Z)
    [IsFiniteMeasure μ] [Fintype T] [Fintype T'] :
    H[X | ⟨Y, Z⟩ ; μ]
      = ∑ z, (μ (Z ⁻¹' {z})).toReal * H[X | Y ; μ[|Z ⁻¹' {z}]] := by
  simp_rw [condEntropy_eq_sum_fintype _ _ _ (hY.prod_mk hZ), condEntropy_eq_sum_fintype _ _ _ hY,
    Fintype.sum_prod_type_right, Finset.mul_sum, ← mul_assoc, ← ENNReal.toReal_mul]
  congr with y
  congr with x
  have A : (fun a ↦ (Y a, Z a)) ⁻¹' {(x, y)} = Z ⁻¹' {y} ∩ Y ⁻¹' {x} := by
    ext p; simp [and_comm]
  congr 2
  · rw [cond_apply _ (hZ (measurableSet_singleton y)), ← mul_assoc, A]
    rcases eq_or_ne (μ (Z ⁻¹' {y})) 0 with hy|hy
    · have : μ (Z ⁻¹' {y} ∩ Y ⁻¹' {x}) = 0 :=
        le_antisymm ((measure_mono (Set.inter_subset_left _ _)).trans hy.le) bot_le
      simp [this, hy]
    · rw [ENNReal.mul_inv_cancel hy (by finiteness), one_mul]
  · rw [A, cond_cond_eq_cond_inter'' (hZ (measurableSet_singleton y))
      (hY (measurableSet_singleton x))]

/-- $H[X|Y] = \sum_y \sum_x P[Y=y] P[X=x|Y=y] log \frac{1}{P[X=x|Y=y]}$.-/
lemma condEntropy_eq_sum_sum [MeasurableSingletonClass T] (hX : Measurable X) {Y : Ω → T} (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    H[X | Y ; μ]
      = ∑ y in FiniteRange.toFinset Y, ∑ x in FiniteRange.toFinset X, (μ.map Y {y}).toReal * negMulLog ((μ[|Y ← y]).map X {x}).toReal := by
  rw [condEntropy_eq_sum _ _ _ hY]
  congr with y
  rw [entropy_cond_eq_sum_finiteRange hX, Finset.mul_sum]

/-- Same as previous lemma, but with a sum over a product space rather than a double sum. -/
lemma condEntropy_eq_sum_prod [MeasurableSingletonClass T] (hX : Measurable X) {Y : Ω → T}
    (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]:
    H[X | Y ; μ] = ∑ p in (FiniteRange.toFinset X) ×ˢ (FiniteRange.toFinset Y),
      (μ.map Y {p.2}).toReal * negMulLog ((μ[|Y ⁻¹' {p.2}]).map X {p.1}).toReal := by
  rw [condEntropy_eq_sum_sum hX hY, Finset.sum_product_right]

/-- If $X : \Omega \to S$, $Y : \Omega \to T$ are random variables, and $f : T \times S → U$ is
  injective for each fixed $t \in T$, then $H[f(Y, X)|Y] = H[X|Y]$.
  Thus for instance $H[X-Y|Y] = H[X|Y]$. -/
lemma condEntropy_of_injective
    [MeasurableSingletonClass U] (μ : Measure Ω) [IsFiniteMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : T → S → U) (hf : ∀ t, Injective (f t)) [FiniteRange Y] :
    H[(fun ω ↦ f (Y ω) (X ω)) | Y ; μ] = H[X | Y ; μ] := by
  rw [condEntropy_eq_sum _ _ _ hY, condEntropy_eq_sum _ _ _ hY]
  have : ∀ y, H[fun ω ↦ f (Y ω) (X ω)|Y← y; μ] = H[(f y ∘ X) | Y ← y ; μ] := by
    intro y
    refine entropy_congr ?_
    have : ∀ᵐ ω ∂μ[|Y ← y], Y ω = y := by
      rw [ae_iff, cond_apply _ (hY (measurableSet_singleton _))]
      have : {a | ¬Y a = y} = (Y ⁻¹' {y})ᶜ := by ext; simp
      rw [this, Set.inter_compl_self, measure_empty, mul_zero]
    filter_upwards [this] with ω hω
    rw [hω]
    simp
  simp_rw [this]
  congr with y
  rw [entropy_comp_of_injective _ hX (f y) (hf y)]

/-- A weaker version of the above lemma in which f is independent of Y. -/
lemma condEntropy_comp_of_injective [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (μ : Measure Ω) (hX : Measurable X) (f : S → U) (hf : Injective f) :
    H[f ∘ X | Y ; μ] = H[X | Y ; μ] :=
  integral_congr_ae (ae_of_all _ (fun _ ↦ entropy_comp_of_injective _ hX f hf))

/-- $H[X, Y| Z] = H[Y, X| Z]$. -/
lemma condEntropy_comm {Z : Ω → U}
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X, Y⟩ | Z ; μ] = H[⟨Y, X⟩ | Z; μ] := by
  change H[⟨X, Y⟩ | Z ; μ] = H[Prod.swap ∘ ⟨X, Y⟩ | Z; μ]
  exact (condEntropy_comp_of_injective μ (hX.prod_mk hY) Prod.swap Prod.swap_injective).symm

end condEntropy

section pair

/-- One form of the chain rule : $H[X, Y] = H[X] + H[Y|X]. -/
lemma chain_rule' (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y]:
    H[⟨X, Y⟩ ; μ] = H[X ; μ] + H[Y | X ; μ] := by
  have : IsProbabilityMeasure (μ.map X) := isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure (μ.map (⟨X, Y⟩)) :=
    isProbabilityMeasure_map (hX.prod_mk hY).aemeasurable
  rw [entropy_eq_kernel_entropy, kernel.chain_rule]
  simp_rw [← kernel.map_const _ (hX.prod_mk hY), kernel.fst_map_prod _ hX hY, kernel.map_const _ hX,
    kernel.map_const _ (hX.prod_mk hY)]
  . congr 1
    · rw [kernel.entropy, integral_dirac]
      rfl
    · simp_rw [condEntropy_eq_kernel_entropy hY hX]
      have : Measure.dirac () ⊗ₘ kernel.const Unit (μ.map X) = μ.map (fun ω ↦ ((), X ω)) := by
        ext s _
        rw [Measure.dirac_unit_compProd_const, Measure.map_map measurable_prod_mk_left hX]
        congr
      rw [this, kernel.entropy_congr (condDistrib_const_unit hX hY μ)]
      have : μ.map (fun ω ↦ ((), X ω)) = (μ.map X).map (Prod.mk ()) := by
        ext s _
        rw [Measure.map_map measurable_prod_mk_left hX]
        rfl
      rw [this, kernel.entropy_prodMkLeft_unit]
  · apply kernel.FiniteKernelSupport.aefiniteKernelSupport
    exact kernel.finiteKernelSupport_of_const _

/-- Another form of the chain rule : $H[X, Y] = H[Y] + H[X|Y]$. -/
lemma chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
   [FiniteRange X] [FiniteRange Y] :
    H[⟨X, Y⟩ ; μ] = H[Y ; μ] + H[X | Y ; μ] := by
  rw [entropy_comm hX hY, chain_rule' μ hY hX]

/-- Another form of the chain rule : $H[X|Y] = H[X, Y] - H[Y]$. -/
lemma chain_rule'' (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    H[X | Y ; μ] = H[⟨X, Y⟩ ; μ] - H[Y ; μ] := by
  rw [chain_rule μ hX hY, add_sub_cancel']

/-- Two pairs of variables that have the same joint distribution, have the same
conditional entropy. -/
lemma IdentDistrib.condEntropy_eq {Ω' : Type*} [MeasurableSpace Ω'] {X : Ω → S} {Y : Ω → T}
    {μ' : Measure Ω'} {X' : Ω' → S} {Y' : Ω' → T} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X') (hY' : Measurable Y')
    (h : IdentDistrib (⟨X, Y⟩) (⟨X', Y'⟩) μ μ') [FiniteRange X] [FiniteRange Y] [FiniteRange X']
    [FiniteRange Y'] :
    H[X | Y ; μ] = H[X' | Y' ; μ'] := by
  have : IdentDistrib Y Y' μ μ' := h.comp measurable_snd
  rw [chain_rule'' _ hX hY, chain_rule'' _ hX' hY', h.entropy_eq, this.entropy_eq]

/-- If $X : \Omega \to S$ and $Y : \Omega \to T$ are random variables, and $f : T \to U$ is an
injection then $H[X|f(Y)] = H[X|Y]$.
 -/
lemma condEntropy_of_injective' [MeasurableSingletonClass S] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) (f : T → U) (hf : Injective f)
    (hfY : Measurable (f ∘ Y)) [FiniteRange X] [FiniteRange Y] :
    H[X | f ∘ Y ; μ] = H[X | Y ; μ] := by
  rw [chain_rule'' μ hX hY, chain_rule'' μ hX hfY, chain_rule' μ hX hY, chain_rule' μ hX hfY]
  congr 1
  . congr 1
    exact condEntropy_comp_of_injective μ hY f hf
  exact entropy_comp_of_injective μ hY f hf

/-- $H[X|f(X)] = H[X] - H[f(X)]$. -/
lemma condEntropy_comp_self [IsProbabilityMeasure μ] (hX : Measurable X) {f : S → U}
    (hf : Measurable f) [FiniteRange X] : H[X | f ∘ X ; μ] = H[X ; μ] - H[f ∘ X ; μ] := by
  rw [chain_rule'' μ hX (hf.comp hX), entropy_prod_comp hX _ f]

/-- If $X : \Omega \to S$, $Y : \Omega \to T$,$Z : \Omega \to U$ are random variables, then
$$H[X, Y | Z] = H[X | Z] + H[Y|X, Z]$$. -/
lemma cond_chain_rule' (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X] [FiniteRange Y] [FiniteRange Z]:
    H[⟨X, Y⟩ | Z ; μ] = H[X | Z ; μ] + H[Y | ⟨X, Z⟩ ; μ] := by
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  rw [condEntropy_eq_kernel_entropy (hX.prod_mk hY) hZ, kernel.chain_rule]
  . congr 1
    . rw [condEntropy_eq_kernel_entropy hX hZ]
      refine kernel.entropy_congr ?_
      exact condDistrib_fst_ae_eq hX hY hZ μ
    · rw [condEntropy_two_eq_kernel_entropy hY hX hZ]
  exact kernel.aefiniteKernelSupport_condDistrib _ _ μ (by measurability) (by measurability)

/-- $$ H[X, Y | Z] = H[Y | Z] + H[X|Y, Z].$$ -/
lemma cond_chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X] [FiniteRange Y] [FiniteRange Z]:
    H[⟨X, Y⟩ | Z ; μ] = H[Y | Z ; μ] + H[X | ⟨Y, Z⟩ ; μ] := by
    rw [condEntropy_comm hX hY, cond_chain_rule' _ hY hX hZ]

/-- Data-processing inequality for the entropy :
$$ H[f(X)] \leq H[X].$$
To upgrade this to equality, see `entropy_of_comp_eq_of_comp` or `entropy_comp_of_injective`. -/
lemma entropy_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (f : S → U) [FiniteRange X]:
    H[f ∘ X ; μ] ≤ H[X ; μ] := by
  have hfX : Measurable (f ∘ X) := (measurable_of_countable _).comp hX
  have : H[X ; μ] = H[⟨X, f ∘ X⟩ ; μ] := by
    refine (entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) ?_).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule _ hX hfX]
  simp only [le_add_iff_nonneg_right]
  exact condEntropy_nonneg X (f ∘ X) μ

/-- A Schroder-Bernstein type theorem for entropy : if two random variables are functions of each
  other, then they have the same entropy. Can be used as a substitute for
  `entropy_comp_of_injective` if one doesn't want to establish the injectivity. -/
lemma entropy_of_comp_eq_of_comp
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (f : S → T) (g : T → S) (h1 : Y = f ∘ X) (h2 : X = g ∘ Y) [FiniteRange X] [FiniteRange Y]:
    H[X ; μ] = H[Y ; μ] := by
  have h3 : H[X ; μ] ≤ H[Y ; μ] := by
    rw [h2]; exact entropy_comp_le μ hY _
  have h4 : H[Y ; μ] ≤ H[X ; μ] := by
    rw [h1]; exact entropy_comp_le μ hX _
  linarith

end pair

section mutualInfo

/-- The mutual information $I[X : Y]$ of two random variables is defined to be $H[X] + H[Y] - H[X ; Y]$. -/
noncomputable
def mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[⟨X, Y⟩ ; μ]

@[inherit_doc mutualInfo] notation3:max "I[" X " : " Y " ; " μ "]" => mutualInfo X Y μ
@[inherit_doc mutualInfo] notation3:max "I[" X " : " Y "]" => mutualInfo X Y volume

lemma mutualInfo_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
  I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[⟨X, Y⟩ ; μ] := rfl

/-- $I[X : Y] = I[Y : X]$. -/
lemma mutualInfo_comm (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    I[X : Y ; μ] = I[Y : X ; μ] := by simp_rw [mutualInfo, add_comm, entropy_comm hX hY]

lemma entropy_add_entropy_sub_mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    H[X ; μ] + H[Y ; μ] - I[X : Y ; μ] = H[⟨X, Y⟩ ; μ] := sub_sub_self _ _

/-- $I[X : Y] = H[X] - H[X|Y]$. -/
lemma mutualInfo_eq_entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]:
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  rw [mutualInfo_def, chain_rule μ hX hY]
  abel

/-- $I[X : Y] = H[Y] - H[Y | X]$. -/
lemma mutualInfo_eq_entropy_sub_condEntropy' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]:
    I[X : Y ; μ] = H[Y ; μ] - H[Y | X ; μ] := by
  rw [mutualInfo_comm hX hY, mutualInfo_eq_entropy_sub_condEntropy hY hX]

/-- $H[X] - I[X : Y] = H[X | Y]$. -/
lemma entropy_sub_mutualInfo_eq_condEntropy (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]:
    H[X ; μ] - I[X : Y ; μ] = H[X | Y ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY, sub_sub_self]

/-- $H[Y] - I[X : Y] = H[Y | X]$. -/
lemma entropy_sub_mutualInfo_eq_condEntropy' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]:
    H[Y ; μ] - I[X : Y ; μ] = H[Y | X ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy' hX hY, sub_sub_self]

/-- Mutual information is non-negative. -/
lemma mutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [FiniteRange X] [FiniteRange Y] :
    0 ≤ I[X : Y ; μ] := by
  simp_rw [mutualInfo_def, entropy_def]
  have h_fst : μ.map X = (μ.map (⟨X, Y⟩)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prod_mk hY)]
    congr
  have h_snd : μ.map Y = (μ.map (⟨X, Y⟩)).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prod_mk hY)]
    congr
  rw [h_fst, h_snd]
  exact measureMutualInfo_nonneg

/-- Substituting variables for ones with the same distributions doesn't change the mutual information. -/
lemma IdentDistrib.mutualInfo_eq {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X' : Ω' → S} {Y' : Ω' → T} (hXY : IdentDistrib (⟨X, Y⟩) (⟨X', Y'⟩) μ μ') :
      I[X : Y ; μ] = I[X' : Y' ; μ'] := by
  have hX : IdentDistrib X X' μ μ' := hXY.comp measurable_fst
  have hY : IdentDistrib Y Y' μ μ' := hXY.comp measurable_snd
  simp_rw [mutualInfo_def,hX.entropy_eq,hY.entropy_eq,hXY.entropy_eq]

/-- Subadditivity of entropy. -/
lemma entropy_pair_le_add (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [FiniteRange X] [FiniteRange Y] :
    H[⟨X, Y⟩ ; μ] ≤ H[X ; μ] + H[Y ; μ] :=
  sub_nonneg.1 $ mutualInfo_nonneg hX hY _

/-- $I[X : Y] = 0$ iff $X, Y$ are independent. -/
lemma mutualInfo_eq_zero (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y ; μ] = 0 ↔ IndepFun X Y μ := by
  have : IsProbabilityMeasure (μ.map (⟨X, Y⟩)) :=
    isProbabilityMeasure_map (hX.prod_mk hY).aemeasurable
  simp_rw [mutualInfo_def, entropy_def]
  have h_fst : μ.map X = (μ.map (⟨X, Y⟩)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prod_mk hY)]
    congr
  have h_snd : μ.map Y = (μ.map (⟨X, Y⟩)).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prod_mk hY)]
    congr
  rw [h_fst, h_snd]
  convert measureMutualInfo_eq_zero_iff (μ := μ.map (⟨X, Y⟩))
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    Measure.ext_iff_measureReal_singleton_finiteSupport]
  congr! with p
  convert measureReal_prod_prod (μ := μ.map X) (ν := μ.map Y) {p.1} {p.2}
  · simp
  · exact Measure.map_map measurable_fst (hX.prod_mk hY)
  · exact Measure.map_map measurable_snd (hX.prod_mk hY)

protected alias ⟨_, IndepFun.mutualInfo_eq_zero⟩ := mutualInfo_eq_zero

/-- The mutual information with a constant is always zero. -/
lemma mutualInfo_const (hX : Measurable X) (c : T) {μ : Measure Ω} [IsProbabilityMeasure μ] [FiniteRange X] :
    I[X : fun _ ↦ c ; μ] = 0 := (indepFun_const c).mutualInfo_eq_zero hX measurable_const

lemma IndepFun.condEntropy_eq_entropy {μ : Measure Ω} (h : IndepFun X Y μ)
    (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    H[X | Y ; μ] = H[X ; μ] := by
  have := h.mutualInfo_eq_zero hX hY
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY] at this
  linarith

/-- $H[X, Y] = H[X] + H[Y]$ if and only if $X, Y$ are independent. -/
lemma entropy_pair_eq_add (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    H[⟨X, Y⟩ ; μ] = H[X ; μ] + H[Y ; μ] ↔ IndepFun X Y μ := by
  rw [eq_comm, ← sub_eq_zero, ← mutualInfo_eq_zero hX hY]; rfl

/-- If $X, Y$ are independent, then $H[X, Y] = H[X] + H[Y]$. -/
protected alias ⟨_, IndepFun.entropy_pair_eq_add⟩ := entropy_pair_eq_add

/-- The conditional mutual information $I[X : Y| Z]$ is the mutual information of $X| Z=z$ and
$Y| Z=z$, integrated over $z$. -/
noncomputable
def condMutualInfo (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω := by volume_tac) :
    ℝ := (μ.map Z)[fun z ↦ H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[⟨X, Y⟩ | Z ← z ; μ]]

lemma condMutualInfo_def (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) :
    condMutualInfo X Y Z μ = (μ.map Z)[fun z ↦
      H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[⟨X, Y⟩ | Z ← z ; μ]] := rfl

@[inherit_doc condMutualInfo]
notation3:max "I[" X " : " Y "|" Z ";" μ "]" => condMutualInfo X Y Z μ
@[inherit_doc condMutualInfo]
notation3:max "I[" X " : " Y "|" Z "]" => condMutualInfo X Y Z volume

/-- The conditional mutual information agrees with the information of the conditional kernel.
-/
lemma condMutualInfo_eq_kernel_mutualInfo
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteRange Z] :
    I[X : Y | Z ; μ] = Ik[condDistrib (⟨X, Y⟩) Z μ, μ.map Z] := by
  rcases finiteSupport_of_finiteRange (μ := μ) (X := Z) with ⟨A, hA⟩
  simp_rw [condMutualInfo_def, entropy_def, kernel.mutualInfo, kernel.entropy,
    integral_eq_sum' _ hA, smul_eq_mul, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr with x
  · have h := condDistrib_fst_ae_eq hX hY hZ μ
    rw [Filter.EventuallyEq, ae_iff_of_countable] at h
    specialize h x
    by_cases hx : (μ.map Z) {x} = 0
    · simp [hx]
    rw [h hx, condDistrib_apply hX hZ]
    rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx
  · have h := condDistrib_snd_ae_eq hX hY hZ μ
    rw [Filter.EventuallyEq, ae_iff_of_countable] at h
    specialize h x
    by_cases hx : (μ.map Z) {x} = 0
    · simp [hx]
    rw [h hx, condDistrib_apply hY hZ]
    rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx
  · by_cases hx : (μ.map Z) {x} = 0
    · simp [hx]
    rw [condDistrib_apply (hX.prod_mk hY) hZ]
    rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx

lemma condMutualInfo_eq_integral_mutualInfo :
    I[X : Y | Z ; μ] = (μ.map Z)[fun z ↦ I[X : Y ; μ[| Z ⁻¹' {z}]]] := rfl

lemma condMutualInfo_eq_sum [IsFiniteMeasure μ] (hZ : Measurable Z) [FiniteRange Z] :
    I[X : Y | Z ; μ] = ∑ z in FiniteRange.toFinset Z, (μ (Z ⁻¹' {z})).toReal * I[X : Y ; (μ[|Z ← z])] := by
  rw [condMutualInfo_eq_integral_mutualInfo, integral_eq_sum' _ (FiniteRange.null_of_compl _ Z)]
  congr 1 with z
  rw [map_apply hZ (MeasurableSet.singleton z)]
  rfl

/-- A variant of `condMutualInfo_eq_sum` when `Z` has finite codomain. -/
lemma condMutualInfo_eq_sum' [IsFiniteMeasure μ] (hZ : Measurable Z) [Fintype U] :
    I[X : Y | Z ; μ] = ∑ z, (μ (Z ⁻¹' {z})).toReal * I[X : Y ; (μ[|Z ← z])] := by
  rw [condMutualInfo_eq_sum hZ]
  apply Finset.sum_subset
  . simp
  intro z _ hz
  have : Z ⁻¹' {z} = ∅ := by
    ext ω
    simp at hz
    simp [hz]
  simp [this]

/-- $I[X : Y | Z] = I[Y : X | Z]$. -/
lemma condMutualInfo_comm
    (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U) (μ : Measure Ω) :
    I[X : Y | Z ; μ] = I[Y : X | Z ; μ] := by
  simp_rw [condMutualInfo_def, add_comm, entropy_comm hX hY]

/-- Conditional information is non-nonegative. -/
lemma condMutualInfo_nonneg
    (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U) (μ : Measure Ω)
    [FiniteRange X] [FiniteRange Y] :
    0 ≤ I[X : Y | Z ; μ] := by
  refine integral_nonneg (fun z ↦ ?_)
  exact mutualInfo_nonneg hX hY _

/-- $$ I[X : Y| Z] = H[X| Z] + H[Y| Z] - H[X, Y| Z].$$ -/
lemma condMutualInfo_eq (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteRange Z] :
    I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z; μ] - H[⟨X, Y⟩ | Z ; μ] := by
  rw [condMutualInfo_eq_kernel_mutualInfo hX hY hZ, kernel.mutualInfo,
    kernel.entropy_congr (condDistrib_fst_ae_eq hX hY hZ _),
    kernel.entropy_congr (condDistrib_snd_ae_eq hX hY hZ _),
    condEntropy_eq_kernel_entropy hX hZ, condEntropy_eq_kernel_entropy hY hZ,
    condEntropy_eq_kernel_entropy (hX.prod_mk hY) hZ]

/-- $$ I[X : Y| Z] = H[X| Z] - H[X|Y, Z].$$ -/
lemma condMutualInfo_eq' (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] = H[X | Z ; μ] - H[X | ⟨Y, Z⟩ ; μ] := by
  rw [condMutualInfo_eq hX hY hZ, cond_chain_rule _ hX hY hZ]
  ring

/-- If $f(Z, X)$ is injective for each fixed $Z$, then $I[f(Z, X) : Y| Z] = I[X : Y| Z]$.-/
lemma condMutualInfo_of_inj_map [IsProbabilityMeasure μ]
  (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
  {V : Type*} [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  (f : U → S → V) (hf : ∀ t, Function.Injective (f t)) [FiniteRange Z] :
    I[fun ω ↦ f (Z ω) (X ω) : Y | Z ; μ] =
    I[X : Y | Z ; μ] := by
  have hM : Measurable (Function.uncurry f ∘ ⟨Z, X⟩) :=
    (measurable_of_countable _).comp (hZ.prod_mk hX)
  have hM : Measurable fun ω ↦ f (Z ω) (X ω) := hM
  rw [condMutualInfo_eq hM hY hZ, condMutualInfo_eq hX hY hZ]
  let g : U → (S × T) → (V × T) := fun z (x, y) ↦ (f z x, y)
  have hg : ∀ t, Function.Injective (g t) :=
    fun _ _ _ h ↦ Prod.ext_iff.2 ⟨hf _ (Prod.ext_iff.1 h).1, (Prod.ext_iff.1 h).2⟩
  rw [← condEntropy_of_injective μ (hX.prod_mk hY) hZ g hg, ← condEntropy_of_injective μ hX hZ _ hf]

lemma condEntropy_prod_eq_of_indepFun [Fintype T] [Fintype U] [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X]
    (h : IndepFun (⟨X, Y⟩) Z μ) :
    H[X | ⟨Y, Z⟩ ; μ] = H[X | Y ; μ] := by
  rw [condEntropy_prod_eq_sum _ hY hZ]
  have : H[X | Y ; μ] = ∑ z, (μ (Z ⁻¹' {z})).toReal * H[X | Y ; μ] := by
    rw [← Finset.sum_mul, sum_measure_preimage_singleton' μ hZ, one_mul]
  rw [this]
  congr with w
  rcases eq_or_ne (μ (Z ⁻¹' {w})) 0 with hw|hw
  · simp [hw]
  congr 1
  have : IsProbabilityMeasure (μ[|Z ⁻¹' {w}]) := cond_isProbabilityMeasure μ hw
  apply IdentDistrib.condEntropy_eq hX hY hX hY
  exact (h.identDistrib_cond (MeasurableSet.singleton w) (hX.prod_mk hY) hZ hw).symm

section IsProbabilityMeasure
variable (μ : Measure Ω) [IsProbabilityMeasure μ] [MeasurableSingletonClass S]
  [MeasurableSingletonClass T]

/-- $$ H[X] - H[X|Y] = I[X : Y] $$ -/
lemma entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    H[X ; μ] - H[X | Y ; μ] = I[X : Y ; μ] := by
  rw [mutualInfo_def, chain_rule _ hX hY, add_comm, add_sub_add_left_eq_sub]

/-- $$ H[X|Y] ≤ H[X] $$ -/
lemma condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    H[X | Y ; μ] ≤ H[X ; μ] :=
  sub_nonneg.1 $ by rw [entropy_sub_condEntropy _ hX hY]; exact mutualInfo_nonneg hX hY _

/-- $H[X | Y, Z] \leq H[X | Z]$ -/
lemma entropy_submodular (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    H[X | ⟨Y, Z⟩ ; μ] ≤ H[X | Z ; μ] := by
  rw [condEntropy_eq_kernel_entropy hX hZ, condEntropy_two_eq_kernel_entropy hX hY hZ]
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  refine (kernel.entropy_condKernel_le_entropy_snd ?_).trans_eq ?_
  . apply kernel.aefiniteKernelSupport_condDistrib
    all_goals measurability
  exact kernel.entropy_congr (condDistrib_snd_ae_eq hY hX hZ _)

/-- Data-processing inequality for the conditional entropy:
$$ H[Y|f(X)] \geq H[Y|X]$$
To upgrade this to equality, see `condEntropy_of_injective'` -/
lemma condEntropy_comp_ge [FiniteRange X] [FiniteRange Y] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (f : S → U) : H[Y | f ∘ X ; μ] ≥ H[Y | X; μ] := by
  have h_joint : H[⟨Y, ⟨X, f ∘ X⟩⟩ ; μ] = H[⟨Y, X⟩ ; μ] := by
    let g : T × S → T × S × U := fun (y, x) ↦ (y, (x, f x))
    show H[g ∘ ⟨Y, X⟩ ; μ] = H[⟨Y, X⟩ ; μ]
    refine entropy_comp_of_injective μ (by exact Measurable.prod hY hX) g (fun _ _ h => ?_)
    repeat rewrite [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  have hZ : Measurable (f ∘ X) := (measurable_of_countable _).comp hX
  rewrite [chain_rule'' μ hY hX, ← entropy_prod_comp hX μ f, ← h_joint,
    ← chain_rule'' μ hY (Measurable.prod (by exact hX) (by exact hZ))]
  exact entropy_submodular μ hY hX hZ

/-- The submodularity inequality:
$$ H[X, Y, Z] + H[Z] \leq H[X, Z] + H[Y, Z].$$ -/
lemma entropy_triple_add_entropy_le (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    H[⟨X, ⟨Y, Z⟩⟩ ; μ] + H[Z ; μ] ≤ H[⟨X, Z⟩ ; μ] + H[⟨Y, Z⟩ ; μ] := by
  rw [chain_rule _ hX (hY.prod_mk hZ), chain_rule _ hX hZ, chain_rule _ hY hZ]
  ring_nf
  exact add_le_add le_rfl (entropy_submodular _ hX hY hZ)

variable {μ : Measure Ω}

/-- $I[X : Y| Z]=0$ iff $X, Y$ are conditionally independent over $Z$. -/
lemma condMutualInfo_eq_zero (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] = 0 ↔ CondIndepFun X Y Z μ := by
  rw [condIndepFun_iff, condMutualInfo_eq_integral_mutualInfo, integral_eq_zero_iff_of_nonneg]
  . dsimp
    have : (fun x ↦ I[X : Y;μ[| Z ⁻¹' {x}]]) =ᵐ[μ.map Z] 0 ↔ ∀ᵐ z ∂(μ.map Z), I[X : Y ; μ[| Z ⁻¹' {z}]] = 0 := by rfl
    rw [this]
    apply Filter.eventually_congr
    rw [ae_iff_of_countable]
    intro z hz
    rw [Measure.map_apply hZ (measurableSet_singleton z)] at hz
    have : IsProbabilityMeasure (μ[| Z ⁻¹' {z}]) := cond_isProbabilityMeasure μ hz
    exact mutualInfo_eq_zero hX hY
  . dsimp
    rw [Pi.le_def]
    intro z; simp
    by_cases hz : μ (Z ⁻¹' {z}) = 0
    · have : μ[| Z ⁻¹' {z}] = 0 := cond_eq_zero_of_measure_eq_zero hz
      simp [this]
      rw [mutualInfo_def]
      simp
    exact mutualInfo_nonneg hX hY _
  simp
  exact integrable_of_finiteSupport _

/-- If $X, Y$ are conditionally independent over $Z$, then $H[X, Y, Z] = H[X, Z] + H[Y, Z] - H[Z]$. -/
lemma ent_of_cond_indep (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
     (h : CondIndepFun X Y Z μ) [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
     H[⟨X, ⟨Y, Z⟩⟩ ; μ] = H[⟨X, Z⟩; μ] + H[⟨Y, Z⟩; μ] - H[Z; μ] := by
  have hI : I[X : Y | Z ; μ] = 0 := (condMutualInfo_eq_zero hX hY hZ).mpr h
  rw [condMutualInfo_eq hX hY hZ] at hI
  rw [entropy_assoc hX hY hZ, chain_rule _ (hX.prod_mk hY) hZ, chain_rule _ hX hZ, chain_rule _ hY hZ]
  linarith [hI]

end IsProbabilityMeasure
end mutualInfo
end ProbabilityTheory

section MeasureSpace_example

open ProbabilityTheory

variable {Ω S T : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T}

/-- An example to illustrate how `MeasureSpace` can be used to suppress the ambient measure. -/
example (hX : Measurable X) (hY : Measurable Y) :
  H[⟨X, Y⟩] = H[Y] + H[X | Y] := chain_rule _ hX hY

end MeasureSpace_example
