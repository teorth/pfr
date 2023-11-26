import Mathlib.Data.Prod.TProd
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.IdentDistrib
import PFR.Entropy.KernelMutualInformation
import PFR.ForMathlib.Independence
import PFR.ForMathlib.Miscellaneous

/-!
# Entropy and conditional entropy

## Main definitions

* `entropy`: entropy of a random variable, defined as `measureEntropy (volume.map X)`
* `condEntropy`: conditional entropy of a random variable `X` w.r.t. another one `Y`
* `mutualInformation`: mutual information of two random variables

## Main statements

* `chain_rule`: $H[⟨ X, Y ⟩] = H[Y] + H[X | Y]$
* `entropy_cond_le_entropy`: $H[X | Y] ≤ H[X]$. (Chain rule another way.)
* `entropy_triple_add_entropy_le`: $H[X, Y, Z] + H[Z] ≤ H[X,Z] + H[Y,Z]$. (Submodularity of entropy.)

## Notations

* `H[X] = entropy X`
* `H[X | Y ← y] = Hm[(ℙ[| Y ⁻¹' {y}]).map X]`
* `H[X | Y] = condEntropy X Y`, such that `H[X | Y] = (volume.map Y)[fun y ↦ H[X | Y ← y]]`
* `I[X : Y] = mutualInformation X Y`

All notations have variants where we can specify the measure (which is otherwise
supposed to be `volume`). For example `H[X ; μ]` and `I[X : Y ; μ]` instead of `H[X]` and
`I[X : Y]` respectively.

-/

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

/-- Give all finite types the discrete sigma-algebra by default. -/
@[nolint unusedArguments]
instance Fintype.instMeasurableSpace [Fintype S] : MeasurableSpace S := ⊤

/-- Give all finite types the MeasurableSingletonClass instance. -/
@[nolint unusedArguments]
instance Fintype.instMeasurableSingletonClass [Fintype S] : MeasurableSingletonClass S := {
  measurableSet_singleton := by intros; simp
}


namespace ProbabilityTheory

universe uΩ uS uT uU

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU} [mΩ : MeasurableSpace Ω]
  [Fintype S] [Fintype T] [Fintype U]
  [Nonempty S] [Nonempty T] [Nonempty U]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
  {μ : Measure Ω}

section entropy

/-- Entropy of a random variable with values in a finite measurable space. -/
noncomputable
def entropy (X : Ω → S) (μ : Measure Ω := by volume_tac) := Hm[μ.map X]

@[inherit_doc entropy] notation3:max "H[" X "; " μ "]" => entropy X μ
@[inherit_doc entropy] notation3:max "H[" X "]" => entropy X volume
@[inherit_doc entropy] notation3:max "H[" X "|" Y "←" y "; " μ "]" => entropy X (μ[|Y ⁻¹' {y}])
@[inherit_doc entropy] notation3:max "H[" X "|" Y "←" y "]" => entropy X (ℙ[|Y ⁻¹' {y}])

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
lemma entropy_le_log_card
    (X : Ω → S) (μ : Measure Ω) : H[X ; μ] ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card _

lemma entropy_le_log_card_of_mem {A : Set S} {μ : Measure Ω} {X : Ω → S}
    (hX : Measurable X) (h : ∀ᵐ ω ∂μ, X ω ∈ A) :
    H[X ; μ] ≤ log (Nat.card A) := by
  apply measureEntropy_le_log_card_of_mem
  rwa [Measure.map_apply hX (measurableSet_of_countable _)]

/-- $H[X] = \sum_s P[X=s] \log \frac{1}{P[X=s]}$. -/
lemma entropy_eq_sum (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    entropy X μ = ∑ x, negIdMulLog (μ.map X {x}).toReal := by
  have : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  rw [entropy_def, measureEntropy_of_isProbabilityMeasure]

/-- $H[X|Y=y] = \sum_s P[X=s|Y=y] \log \frac{1}{P[X=s|Y=y]}$. -/
lemma entropy_cond_eq_sum (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] (y : T) :
    H[X | Y ← y ; μ] = ∑ x, negIdMulLog ((μ[|Y ⁻¹' {y}]).map X {x}).toReal := by
  by_cases hy : μ (Y ⁻¹' {y}) = 0
  · rw [entropy_def, cond_eq_zero_of_measure_zero hy]
    simp
  · have : IsProbabilityMeasure (μ[|Y ⁻¹' {y}]) := cond_isProbabilityMeasure _ hy
    rw [entropy_eq_sum hX]

/-- If $X$, $Y$ are $S$-valued and $T$-valued random variables, and $Y = f(X)$ for
some injection $f: S \to T$, then $H[Y] = H[X]$. One can also use `entropy_of_comp_eq_of_comp` as an alternative if verifying injectivity is fiddly.  For the upper bound only, see `entropy_comp_le`. -/
lemma entropy_comp_of_injective
    (μ : Measure Ω) (hX : Measurable X) (f : S → T) (hf : Function.Injective f) :
    H[f ∘ X ; μ] = H[X ; μ] := by
  have hf_m : Measurable f := measurable_of_finite f
  rw [entropy_def, ← Measure.map_map hf_m hX, measureEntropy_map_of_injective _ _ hf,
    entropy_def]

/-- The entropy of any constant is zero. -/
@[simp] lemma entropy_const [IsProbabilityMeasure μ] (c : S) : H[(fun _ => c) ; μ] = 0 := by
  simp [entropy,MeasureTheory.Measure.map_const]

attribute [-instance] Fintype.instMeasurableSpace in
@[simp] lemma entropy_add_const {G : Type*} [AddGroup G] [Fintype G] [MeasurableSpace G]
    [MeasurableSingletonClass G]
    (μ : Measure Ω) (X : Ω → G)
    (hX : Measurable X) (c : G) :
    H[(fun ω ↦ X ω + c) ; μ] = H[X ; μ] := by
  apply entropy_comp_of_injective μ hX _ (add_left_injective c)

/-- The assertion that the law of $X$ is the uniform probability measure on a finite set $H$.
While in applications $H$ will be non-empty finite set, $X$ measurable, and and $μ$ a probability
measure, it could be technically convenient to have a definition that works even without these
hypotheses.  (For instance, `isUniform` would be well-defined, but false, for infinite `H`)   -/
structure IsUniform (H : Set S) (X : Ω → S) (μ : Measure Ω := by volume_tac) : Prop :=
  eq_of_mem : ∀ x y, x ∈ H → y ∈ H → μ (X ⁻¹' {x}) = μ (X ⁻¹' {y})
  measure_preimage_compl : μ (X ⁻¹' Hᶜ) = 0

open Set

attribute [-instance] Fintype.instMeasurableSpace in
/-- Uniform distributions exist.   -/
lemma exists_isUniform (H : Finset S) (h : H.Nonempty) :
    ∃ (Ω : Type uS) (mΩ : MeasurableSpace Ω) (X : Ω → S) (μ : Measure Ω),
    IsProbabilityMeasure μ ∧ Measurable X ∧ IsUniform H X μ ∧ ∀ ω : Ω, X ω ∈ H := by
  refine ⟨H, Subtype.instMeasurableSpace, (fun x ↦ x),
      (Finset.card H : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac i, ?_, measurable_subtype_coe, ?_, fun x ↦ x.2⟩
  · constructor
    simp only [Finset.univ_eq_attach, Measure.smul_toOuterMeasure, OuterMeasure.coe_smul,
      Measure.coe_finset_sum, Pi.smul_apply, Finset.sum_apply, MeasurableSet.univ,
      Measure.dirac_apply', mem_univ, indicator_of_mem, Pi.one_apply, Finset.sum_const,
      Finset.card_attach, nsmul_eq_mul, mul_one, smul_eq_mul]
    rw [ENNReal.inv_mul_cancel]
    · simpa using h.ne_empty
    · simp
  · constructor
    · intro x y hx hy
      simp only [Finset.univ_eq_attach, Measure.smul_toOuterMeasure, OuterMeasure.coe_smul,
        Measure.coe_finset_sum, Pi.smul_apply, Finset.sum_apply, mem_preimage, mem_singleton_iff,
        Measure.dirac_apply, smul_eq_mul]
      rw [Finset.sum_eq_single ⟨x, hx⟩, Finset.sum_eq_single ⟨y, hy⟩]
      · simp
      · rintro ⟨b, bH⟩ _hb h'b
        simp only [ne_eq, Subtype.mk.injEq] at h'b
        simp [h'b]
      · simp
      · rintro ⟨b, bH⟩ _hb h'b
        simp only [ne_eq, Subtype.mk.injEq] at h'b
        simp [h'b]
      · simp
    · simp

open Function

/-- The image of a uniform random variable under an injective map is uniform on the image. -/
lemma IsUniform.comp
    {H : Set S} {X : Ω → S} {μ : Measure Ω} (h : IsUniform H X μ) {f : S → T} (hf : Injective f) :
    IsUniform (f '' H) (f ∘ X) μ where
  eq_of_mem := by
    rintro - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    have A z : f ⁻¹' {f z} = {z} := by ext; simp [hf.eq_iff]
    simp [preimage_comp, A, h.eq_of_mem x y hx hy]
  measure_preimage_compl := by simpa [preimage_comp, hf] using h.measure_preimage_compl

/-- Uniform distributions exist, version within a fintype and giving a measure space  -/
lemma exists_isUniform_measureSpace
    {S : Type u} [Fintype S] (H : Set S) (h : H.Nonempty) :
    ∃ (Ω : Type u) (mΩ : MeasureSpace Ω) (U : Ω → S),
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧ IsUniform H U ∧ ∀ ω : Ω, U ω ∈ H := by
  let H' : Finset S := H.toFinite.toFinset
  rcases exists_isUniform H' (by simpa using h) with ⟨Ω, mΩ, X, μ, hμ, Xmeas, Xunif, Xmem⟩
  simp only [Finite.coe_toFinset, Finite.mem_toFinset] at Xunif Xmem
  exact ⟨Ω, ⟨μ⟩, X, hμ, Xmeas, Xunif, Xmem⟩

lemma IsUniform.ae_mem {H : Set S} {X : Ω → S} {μ : Measure Ω} (h : IsUniform H X μ) :
    ∀ᵐ ω ∂μ, X ω ∈ H := h.measure_preimage_compl

lemma IsUniform.nonempty {H : Set S} {X : Ω → S} {μ : Measure Ω} (h : IsUniform H X μ)
    [hμ : NeZero μ] : H.Nonempty := by
  rcases eq_empty_or_nonempty H with rfl|h'
  · have : μ univ = 0 := by convert h.measure_preimage_compl; simp
    simp at this
    exact (hμ.out this).elim
  · exact h'

/-- A "unit test" for the definition of uniform distribution. -/
lemma IsUniform.measure_preimage_of_mem
    {H : Set S} {X : Ω → S} {μ : Measure Ω} (h : IsUniform H X μ) (hX : Measurable X)
    {s : S} (hs : s ∈ H) :
    μ (X ⁻¹' {s}) = μ univ / Nat.card H := by
  let H' := H.toFinite.toFinset
  have B : μ univ = (Nat.card H) * μ (X ⁻¹' {s}) := calc
    μ univ = μ (X ⁻¹' Hᶜ) + μ (X ⁻¹' H) := by
      rw [← measure_union (disjoint_compl_left.preimage _) (hX (measurableSet_of_countable _))]
      simp
    _ = μ (X ⁻¹' H) := by rw [h.measure_preimage_compl, zero_add]
    _ = ∑ x in H', μ (X ⁻¹' {x}) := by
      have : X ⁻¹' H = ⋃ x ∈ H', X ⁻¹' ({x} : Set S) := by simp
      rw [this, measure_biUnion_finset]
      · intro y _hy z _hz hyz
        apply Disjoint.preimage
        simp [hyz]
      · intro y _hy
        exact hX (measurableSet_of_countable _)
    _ = ∑ _x in H', μ (X ⁻¹' {s}) :=
      Finset.sum_congr rfl (fun x hx ↦ h.eq_of_mem x s (by simpa using hx) hs)
    _ = H'.card * μ (X ⁻¹' {s}) := by simp
    _ = (Nat.card H) * μ (X ⁻¹' {s}) := by
      congr; exact (Nat.card_eq_toFinset_card (toFinite H)).symm
  rcases Nat.eq_zero_or_pos (Nat.card H) with hH|hH
  · simp only [hH, CharP.cast_eq_zero, zero_mul, Measure.measure_univ_eq_zero] at B
    simp [B]
  · rwa [eq_comm, ← ENNReal.eq_div_iff] at B
    · simpa using Nat.pos_iff_ne_zero.mp hH
    · simp

/-- A "unit test" for the definition of uniform distribution. -/
lemma IsUniform.measureReal_preimage_of_mem
    {H : Set S} {X : Ω → S} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsUniform H X μ) (hX : Measurable X) {s : S} (hs : s ∈ H) :
    μ.real (X ⁻¹' {s}) = 1 / Nat.card H := by
  rw [measureReal_def, h.measure_preimage_of_mem hX hs]
  simp [ENNReal.toReal_inv]

/-- Another "unit test" for the definition of uniform distribution. -/
lemma IsUniform.measure_preimage_of_nmem
    {H : Set S} {X : Ω → S} {μ : Measure Ω} (h : IsUniform H X μ) {s : S} (hs : s ∉ H) :
    μ (X ⁻¹' {s}) = 0 := by
  apply le_antisymm ((measure_mono _).trans h.measure_preimage_compl.le) (zero_le _)
  apply preimage_mono
  simpa using hs

/-- Another "unit test" for the definition of uniform distribution. -/
lemma IsUniform.measureReal_preimage_of_nmem
    {H : Set S} {X : Ω → S} {μ : Measure Ω} (h : IsUniform H X μ) {s : S} (hs : s ∉ H) :
    μ.real (X ⁻¹' {s}) = 0 := by
  rw [measureReal_def, h.measure_preimage_of_nmem hs, ENNReal.zero_toReal]

lemma IsUniform.of_identDistrib {Ω' : Type*} [MeasurableSpace Ω']
    {H : Set S} {X : Ω → S} {μ : Measure Ω} (h : IsUniform H X μ)
    {X' : Ω' → S} {μ' : Measure Ω'} (h' : IdentDistrib X X' μ μ') (hH : MeasurableSet H) :
    IsUniform H X' μ' := by
  constructor
  · intro x y hx hy
    rw [← h'.measure_mem_eq (MeasurableSet.singleton x),
      ← h'.measure_mem_eq (MeasurableSet.singleton y)]
    apply h.eq_of_mem x y hx hy
  · rw [← h'.measure_mem_eq hH.compl]
    exact h.measure_preimage_compl

/-- If $X$ is uniformly distributed on $H$, then $H[X] = \log |H|$.
May need some non-degeneracy and measurability conditions. -/
lemma IsUniform.entropy_eq (H : Set S) (X : Ω → S) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsUniform H X μ) : H[X ; μ] = log (Nat.card H) := sorry

/-- If $X$ is $S$-valued random variable, then $H[X] = \log |S|$ if and only if $X$ is uniformly
distributed. -/
lemma entropy_eq_log_card {X : Ω → S} (hX : Measurable X) (μ : Measure Ω) (hμ : NeZero μ)
    (hμ' : IsFiniteMeasure μ) :
    (entropy X μ = log (Fintype.card S)) ↔
      (∀ s : S, μ.map X {s} = (μ Set.univ) / (Fintype.card S)) := by
  rcases eq_zero_or_neZero (μ.map X) with h | h
  . have := Measure.le_map_apply  (@Measurable.aemeasurable Ω S _ _ X μ hX) Set.univ
    simp [h] at this; simp [this] at hμ
  have : IsFiniteMeasure (μ.map X) := by
    apply Measure.isFiniteMeasure_map
  rw [entropy_def, measureEntropy_eq_card_iff_measure_eq, Measure.map_apply hX MeasurableSet.univ]
  simp

lemma Finset.Nonempty_image {α β : Type*} [DecidableEq β]
{s : Finset α} (hs : s.Nonempty) (f : α → β) : (s.image f).Nonempty := by
  rw [Finset.Nonempty] at hs ⊢
  obtain ⟨x, hx⟩ := hs
  use (f x)
  exact Finset.mem_image_of_mem f hx

lemma Finset.image_min'_le_sum {α β : Type*} [DecidableEq β] [LinearOrder β] [AddCommMonoid β]
{s : Finset α} (hs : s.Nonempty) (f : α → β) (hf : ∀ a, 0 ≤ f a ):
  (s.image f).min' (Finset.Nonempty_image hs f) ≤ s.sum f := sorry

lemma Measure.eq_zero_of_map_eq_zero (X : Ω → S) (μ : Measure Ω) (hX : AEMeasurable X μ)
  (hμ : μ.map X = 0) : μ = 0 := by
  have := Measure.preimage_null_of_map_null hX (Measure.measure_univ_eq_zero.mpr hμ)
  rwa [preimage_univ, Measure.measure_univ_eq_zero] at this

def Measure.NeZero_map_NeZero {X : Ω → S} (μ : Measure Ω) (hX : AEMeasurable X μ)
  [NeZero μ] : NeZero (μ.map X) := sorry

lemma IsFiniteMeasure_sum_measure_singleton [Nonempty S] (μ : Measure S)
  (hμ' : IsFiniteMeasure μ) [NeZero μ] : ∑ s : S, μ {s} = μ Set.univ :=
  sorry

lemma IsFiniteMeasure_sum_measureReal_singleton [Nonempty S] (μ : Measure S)
  [IsFiniteMeasure μ] [NeZero μ] : ∑ s : S, μ.real {s} = μ.real Set.univ := sorry

lemma IsFiniteMeasure_sum_measure_univ_inv_mul_measure_singleton [Nonempty S] (μ : Measure S)
  [IsFiniteMeasure μ] [NeZero μ] : ∑ s : S, ((μ Set.univ)⁻¹ * μ {s}) = 1:= sorry

lemma IsFiniteMeasure_sum_measureReal_univ_inv_mul_measureReal_singleton [Nonempty S] (μ : Measure S)
  [IsFiniteMeasure μ] [NeZero μ] : ∑ s : S, ((μ.real Set.univ)⁻¹ * μ.real {s}) = 1:= sorry

/-- If $X$ is an $S$-valued random variable, then there exists $s \in S$ such that
$P[X=s] \geq \exp(-H[X])$. -/
lemma prob_ge_exp_neg_entropy [Nonempty S] (X : Ω → S) (hX : Measurable X) (μ : Measure Ω)
  [hμ' : IsFiniteMeasure μ] [NeZero μ] (hbd : ∀ (s : S), μ.map X {s} ≠ 0) :
  ∃ s : S, μ.map X {s} ≥ (μ.map X Set.univ) * (rexp (- H[X ; μ])).toNNReal := by
  -- A few helper lemmas for later
  have nonempty : (Finset.univ.image (fun (x : S) =>
    (-log ((μ.map X Set.univ)⁻¹ * (μ.map X) {x}).toReal))).Nonempty
  · apply Finset.Nonempty_image (Finset.univ_nonempty) _
  haveI := (Measure.isFiniteMeasure_map μ X)
  have pos' : (μ.map X Set.univ) ≠ 0
  · intro h
    have := Measure.preimage_null_of_map_null hX.aemeasurable h
    rw [preimage_univ, Measure.measure_univ_eq_zero] at this
    apply (NeZero.ne μ) this
  have mul_pos : ∀ (s : S), 0 < ((μ.map X Set.univ)⁻¹ * (μ.map X {s})).toReal
  · intro s
    simp only [ENNReal.toReal_mul, gt_iff_lt]
    apply mul_pos (ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
      (ENNReal.inv_ne_top.mpr pos')) (ENNReal.toReal_pos (hbd s) (measure_ne_top _ _))
  -- First notice that H[X] = ∑ s, - ℙ[X = s] log ℙ[X = s] ≥ min - log ℙ[X = s]
  have ineq : H[X ; μ] ≥ (Finset.univ.image (fun (x : S) =>
    (- log ((μ.map X Set.univ)⁻¹ * (μ.map X) {x}).toReal))).min' nonempty
  · calc H[X ; μ] = ∑ x : S, (negIdMulLog (((μ.map X Set.univ)⁻¹ * ((μ.map X) {x})).toReal)) := by
          simp only [entropy_def, measureEntropy_def, Measure.smul_toOuterMeasure,
            OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
      _ ≥ ∑ x : S, ((((μ.map X Set.univ)⁻¹ * ((μ.map X) {x})).toReal) * ((Finset.univ.image (fun (x : S) =>
            (- log ((μ.map X Set.univ)⁻¹ * (μ.map X) {x}).toReal))).min' nonempty)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [negIdMulLog]
        suffices : ((Finset.univ.image (fun (x : S) =>
            (- log ((μ.map X Set.univ)⁻¹ * (μ.map X) {x}).toReal))).min' nonempty) ≤
            (- log (((μ.map X Set.univ)⁻¹ * ((μ.map X) {i})).toReal))
        { rw [neg_mul, neg_mul_eq_mul_neg]
          apply mul_le_mul_of_nonneg_left this (le_of_lt (mul_pos i)) }
        apply Finset.min'_le
        apply Finset.mem_image_of_mem _ (Finset.mem_univ i)
      _ = ((Finset.univ.image (fun (x : S) =>
            (- log ((μ.map X Set.univ)⁻¹ * (μ.map X) {x}).toReal))).min' nonempty) *
          (∑ x : S, ((((μ.map X Set.univ)⁻¹ * ((μ.map X) {x})).toReal))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl (fun x hx => mul_comm _ _)
      _ =  ((Finset.univ.image (fun (x : S) =>
            (- log ((μ.map X Set.univ)⁻¹ * (μ.map X) {x}).toReal))).min' nonempty) := by
        suffices : (∑ x : S, ((((μ.map X Set.univ)⁻¹ * ((μ.map X) {x})).toReal))) = 1
        · rw [this, mul_one]
        simp only [ENNReal.toReal_mul]
        haveI : NeZero (μ.map X) := Measure.NeZero_map_NeZero μ hX.aemeasurable
        rw [←IsFiniteMeasure_sum_measureReal_univ_inv_mul_measureReal_singleton (μ.map X)]
        apply Finset.sum_congr rfl
        intro x _
        rw [MeasureTheory.Measure.real, MeasureTheory.Measure.real, ENNReal.toReal_inv]
  -- Take s that attains the minimum. This is the element we are after
  obtain ⟨s, _, hs⟩ := (Finset.mem_image.mp (Finset.min'_mem (Finset.univ.image
    (fun (x : S) => (- log ((μ.map X Set.univ)⁻¹ * (μ.map X) {x}).toReal))) nonempty))
  use s
  -- Apply x ↦ exp(- x) on both sides
  rw [←hs, ge_iff_le, ←neg_le_neg_iff, neg_neg] at ineq
  replace ineq := exp_monotone ineq
  -- Rewrite the inequality in terms of ENNReal
  rw [Real.exp_log (mul_pos s), ENNReal.toReal_mul] at ineq
  rw [ge_iff_le, ENNReal.mul_le_iff_le_inv pos' (measure_ne_top _ _), ENNReal.ofNNReal,
    ←ENNReal.toReal_le_toReal _ (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr pos') (measure_ne_top _ _)),
    ENNReal.some_eq_coe', ENNReal.coe_toReal, coe_toNNReal',
    ENNReal.toReal_mul, max_le_iff]
  · refine ⟨ineq, by rw [←ENNReal.toReal_mul] ; apply ENNReal.toReal_nonneg⟩
  · apply ENNReal.coe_ne_top

/-- If $X$ is an $S$-valued random variable, then there exists $s \in S$ such that
$P[X=s] \geq \exp(-H[X])$. -/
lemma prob_ge_exp_neg_entropy' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype S] (X : Ω → S) (hX : Measurable X)
    [NeZero μ] (hbd : ∀ (s : S), μ.map X {s} ≠ 0) :
    ∃ s : S, rexp (- H[X ; μ]) ≤ μ.real (X ⁻¹' {s}) := by
  obtain ⟨s, hs⟩ := prob_ge_exp_neg_entropy X hX μ hbd
  use s
  haveI : IsProbabilityMeasure (μ.map X) := isProbabilityMeasure_map hX.aemeasurable
  rwa [IsProbabilityMeasure.measure_univ, one_mul, ge_iff_le,
    (show ENNReal.ofNNReal (toNNReal (rexp (-H[X; μ]))) = ENNReal.ofReal (rexp (-H[X; μ])) from rfl),
    ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _), ←MeasureTheory.Measure.real,
    map_measureReal_apply hX (MeasurableSet.singleton s)] at hs

/-- The pair of two random variables -/
abbrev prod {Ω S T : Type*} ( X : Ω → S ) ( Y : Ω → T ) (ω : Ω) : S × T := (X ω, Y ω)

@[inherit_doc prod] notation3:100 "⟨" X ", " Y "⟩" => prod X Y

/-- $H[X,Y] = H[Y,X]$. -/
lemma entropy_comm
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨ X, Y ⟩; μ] = H[⟨ Y, X ⟩ ; μ] := by
  change H[⟨ X, Y ⟩ ; μ] = H[Prod.swap ∘ ⟨ X, Y ⟩ ; μ]
  exact (entropy_comp_of_injective μ (hX.prod_mk hY) Prod.swap Prod.swap_injective).symm

/-- $H[(X,Y),Z] = H[X,(Y,Z)]$. -/
lemma entropy_assoc [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  [MeasurableSingletonClass U] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
  (μ : Measure Ω) : H[⟨ X, ⟨ Y, Z ⟩ ⟩; μ] = H[⟨ ⟨X, Y⟩ , Z ⟩ ; μ] := by
  change H[⟨ X, ⟨ Y, Z ⟩ ⟩ ; μ] = H[(Equiv.prodAssoc _ _ _).symm ∘ ⟨ X, ⟨ Y, Z ⟩ ⟩ ; μ]
  exact entropy_comp_of_injective μ (hX.prod_mk (hY.prod_mk hZ)) _
    (Equiv.prodAssoc S T U).symm.injective |>.symm

variable [AddGroup S] in
/-- $H[X,X+Y] = H[X,Y]$. -/
lemma entropy_add_right {Y : Ω → S}
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨ X, X + Y ⟩; μ] = H[⟨ X, Y ⟩ ; μ] := by
  change H[(Equiv.refl _).prodShear Equiv.addLeft ∘ ⟨ X, Y ⟩ ; μ] = H[⟨ X, Y ⟩ ; μ]
  exact entropy_comp_of_injective μ (hX.prod_mk hY) _ (Equiv.injective _)

@[simp] lemma entropy_prod_comp (hX : Measurable X) (μ : Measure Ω) (f : S → T) :
    H[⟨ X, f ∘ X ⟩; μ] = H[X ; μ] :=
  entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) (fun _ _ ab ↦ (Prod.ext_iff.1 ab).1)

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

@[inherit_doc condEntropy] notation3:max "H[" X "|" Y "; " μ "]" => condEntropy X Y μ
@[inherit_doc condEntropy] notation3:max "H[" X "|" Y "]" => condEntropy X Y volume

/-- Conditional entropy of a random variable is equal to the entropy of its conditional kernel. -/
lemma condEntropy_eq_kernel_entropy
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] :
    H[X | Y ; μ] = Hk[condEntropyKernel X Y μ, μ.map Y] := by
  rw [condEntropy_def, kernel.entropy]
  simp_rw [integral_eq_sum]
  congr with t
  by_cases ht : (μ.map Y {t}).toReal = 0
  · simp [ht]
  simp only [ENNReal.toReal_eq_zero_iff, measure_ne_top (μ.map Y), or_false] at ht
  rw [Measure.map_apply hY (measurableSet_singleton _)] at ht
  simp only [entropy_def]
  congr
  ext S hS
  rw [condEntropyKernel_apply' hX hY _ _ ht hS, Measure.map_apply hX hS,
      cond_apply _ (hY (measurableSet_singleton _))]

lemma map_prod_comap_swap (hX : Measurable X) (hZ : Measurable Z) (μ : Measure Ω) :
    (μ.map (fun ω ↦ (X ω, Z ω))).comap Prod.swap = μ.map (fun ω ↦ (Z ω, X ω)) := by
  ext s hs
  rw [Measure.map_apply (hZ.prod_mk hX) hs, Measure.comap_apply _ Prod.swap_injective _ _ hs]
  · rw [Measure.map_apply (hX.prod_mk hZ)]
    · congr with ω
      simp only [Set.image_swap_eq_preimage_swap, Set.mem_preimage, Prod.swap_prod_mk]
    · exact MeasurableEquiv.prodComm.measurableEmbedding.measurableSet_image' hs
  · exact fun t ht ↦ MeasurableEquiv.prodComm.measurableEmbedding.measurableSet_image' ht

lemma condEntropy_two_eq_kernel_entropy
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    H[X | ⟨ Y, Z ⟩ ; μ] =
      Hk[kernel.condKernel (condEntropyKernel (fun a ↦ (Y a, X a)) Z μ) ,
        Measure.map Z μ ⊗ₘ kernel.fst (condEntropyKernel (fun a ↦ (Y a, X a)) Z μ)] := by
  have := isMarkovKernel_condEntropyKernel (hY.prod_mk hX) hZ μ
  have := isMarkovKernel_condEntropyKernel hY hZ μ
  rw [Measure.compProd_congr (condEntropyKernel_fst_ae_eq hY hX hZ μ),
      map_compProd_condEntropyKernel hY hZ,
      kernel.entropy_congr (condKernel_condEntropyKernel_ae_eq hY hX hZ μ),
      ← kernel.entropy_congr (swap_condEntropyKernel_ae_eq hY hX hZ μ)]
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
lemma condEntropy_le_log_card [MeasurableSingletonClass S]
    (X : Ω → S) (Y : Ω → T) (hY : Measurable Y) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    H[X | Y ; μ] ≤ log (Fintype.card S) := by
  refine (integral_mono_of_nonneg ?_ (integrable_const (log (Fintype.card S))) ?_).trans ?_
  · exact ae_of_all _ (fun _ ↦ entropy_nonneg _ _)
  · exact ae_of_all _ (fun _ ↦ entropy_le_log_card _ _)
  · have : IsProbabilityMeasure (μ.map Y) := isProbabilityMeasure_map hY.aemeasurable
    simp

/-- $H[X|Y] = \sum_y P[Y=y] H[X|Y=y]$.-/
lemma condEntropy_eq_sum [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω → T) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
    H[X | Y ; μ] = ∑ y, (μ.map Y {y}).toReal * H[X | Y ← y ; μ] := by
  rw [condEntropy_def, integral_eq_sum]
  simp_rw [smul_eq_mul]

/-- $H[X|Y] = \sum_y \sum_x P[Y=y] P[X=x|Y=y] log \frac{1}{P[X=x|Y=y]$}.-/
lemma condEntropy_eq_sum_sum [MeasurableSingletonClass T] (hX : Measurable X) (Y : Ω → T)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    H[X | Y ; μ]
      = ∑ y, ∑ x, (μ.map Y {y}).toReal * negIdMulLog ((μ[|Y ⁻¹' {y}]).map X {x}).toReal := by
  rw [condEntropy_eq_sum]
  congr with y
  rw [entropy_cond_eq_sum hX, Finset.mul_sum]

/-- Same as previous lemma, but with a sum over a product space rather than a double sum. -/
lemma condEntropy_eq_sum_prod [MeasurableSingletonClass T] (hX : Measurable X) (Y : Ω → T)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    H[X | Y ; μ] = ∑ p : S × T,
      (μ.map Y {p.2}).toReal * negIdMulLog ((μ[|Y ⁻¹' {p.2}]).map X {p.1}).toReal := by
  have h_prod : (Finset.univ : Finset (S × T)) = (Finset.univ : Finset S) ×ˢ Finset.univ := rfl
  rw [condEntropy_eq_sum_sum hX Y, h_prod, Finset.sum_product_right]

/-- If $X: \Omega \to S$, $Y: \Omega \to T$ are random variables, and $f: T \times S → U$ is injective
  for each fixed $t \in T$, then $H[f(Y,X)|Y] = H[X|Y]$.  Thus for instance $H[X-Y|Y]=H[X|Y]$.-/
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

/-- A weaker version of the above lemma in which f is independent of Y. -/
lemma condEntropy_comp_of_injective [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (μ : Measure Ω) (hX : Measurable X) (f : S → U) (hf : Function.Injective f) :
    H[f ∘ X | Y ; μ] = H[X | Y ; μ] :=
  integral_congr_ae (ae_of_all _ (fun _ ↦ entropy_comp_of_injective _ hX f hf))

lemma condEntropy_comm {Z : Ω → U} [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨ X, Y ⟩ | Z ; μ] = H[⟨ Y, X ⟩ | Z; μ] := by
  change H[⟨ X, Y ⟩ | Z ; μ] = H[Prod.swap ∘ ⟨ X, Y ⟩ | Z; μ]
  exact (condEntropy_comp_of_injective μ (hX.prod_mk hY) Prod.swap Prod.swap_injective).symm

end condEntropy

section pair

/-- One form of the chain rule: $H[X,Y] = H[X] + H[Y|X]. -/
lemma chain_rule'
  (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) :
    H[⟨ X, Y ⟩; μ] = H[X ; μ] + H[Y | X ; μ] := by
  have : IsProbabilityMeasure (μ.map X) := isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure (μ.map (⟨ X, Y ⟩)) :=
    isProbabilityMeasure_map (hX.prod_mk hY).aemeasurable
  rw [entropy_eq_kernel_entropy, kernel.chain_rule,
    ← kernel.map_const _ (hX.prod_mk hY), kernel.fst_map_prod _ hX hY, kernel.map_const _ hX,
    kernel.map_const _ (hX.prod_mk hY)]
  congr 1
  · rw [kernel.entropy, integral_dirac]
    rfl
  · simp_rw [condEntropy_eq_kernel_entropy hY hX]
    have : Measure.dirac () ⊗ₘ kernel.const Unit (μ.map X) = μ.map (fun ω ↦ ((), X ω)) := by
      ext s _
      rw [Measure.dirac_unit_compProd_const, Measure.map_map measurable_prod_mk_left hX]
      congr
    rw [this, kernel.entropy_congr (condEntropyKernel_const_unit hX hY μ)]
    have : μ.map (fun ω ↦ ((), X ω)) = (μ.map X).map (Prod.mk ()) := by
      ext s _
      rw [Measure.map_map measurable_prod_mk_left hX]
      rfl
    rw [this, kernel.entropy_prodMkLeft_unit]

/-- Another form of the chain rule: $H[X,Y] = H[Y] + H[X|Y]. -/
lemma chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) :
    H[⟨ X, Y ⟩; μ] = H[Y ; μ] + H[X  | Y ; μ] := by
  rw [entropy_comm hX hY, chain_rule' μ hY hX]

/-- Another form of the chain rule: $H[X|Y] = H[X,Y] - H[Y]. -/
lemma chain_rule'' (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) :
  H[X|Y;μ] = H[⟨ X, Y ⟩; μ] - H[Y ; μ] := by
  rw [chain_rule μ hX hY, add_sub_cancel']

/-- If $X: \Omega \to S$ and $Y: \Omega \to T$ are random variables, and $f: T \to U$ is an injection then $H[X|f(Y)] = H[X|Y]$.
 -/
lemma condEntropy_of_inj_map' [MeasurableSingletonClass S] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (hX : Measurable X) (hY : Measurable Y) (f : T → U) (hf : Function.Injective f)
  (hfY : Measurable (f ∘ Y)):
    H[X | f ∘ Y ; μ] = H[X | Y ; μ] := by
    rw [chain_rule'' μ hX hY, chain_rule'' μ hX hfY, chain_rule' μ hX hY, chain_rule' μ hX hfY]
    congr 1
    . congr 1
      exact condEntropy_comp_of_injective μ hY f hf
    exact entropy_comp_of_injective μ hY f hf

lemma condEntropy_comp_self [IsProbabilityMeasure μ]
  (hX : Measurable X) {f : S → U} (hf : Measurable f) :
    H[X| f ∘ X; μ] = H[X; μ] - H[f ∘ X; μ] := by
  rw [chain_rule'' μ hX (hf.comp hX), entropy_prod_comp hX _ f]

/--   If $X: \Omega \to S$, $Y: \Omega \to T$,$Z: \Omega \to U$ are random variables, then
$$ H[  X,Y | Z ] = H[X | Z] + H[Y|X, Z].$$ -/
lemma cond_chain_rule' (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[⟨ X, Y ⟩ | Z ; μ] = H[X | Z ; μ] + H[Y | ⟨ X, Z ⟩ ; μ] := by
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  have := isMarkovKernel_condEntropyKernel (hX.prod_mk hY) hZ μ
  rw [condEntropy_eq_kernel_entropy (hX.prod_mk hY) hZ, kernel.chain_rule]
  congr 1
  . rw [condEntropy_eq_kernel_entropy hX hZ]
    refine kernel.entropy_congr ?_
    exact condEntropyKernel_fst_ae_eq hX hY hZ μ
  · rw [condEntropy_two_eq_kernel_entropy hY hX hZ]

/-- $$ H[  X,Y | Z ] = H[Y | Z] + H[X|Y, Z].$$ -/
lemma cond_chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[⟨ X, Y ⟩ | Z ; μ] = H[Y | Z ; μ] + H[X | ⟨ Y, Z ⟩ ; μ] := by
    rw [condEntropy_comm hX hY, cond_chain_rule' _ hY hX hZ]

/-- Data-processing inequality for the entropy:
$$ H[f(X)] \leq H[X].$$
To upgrade this to equality, see `entropy_of_comp_eq_of_comp` or `entropy_comp_of_injective`. -/
lemma entropy_comp_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (f : S → U) :
    H[f ∘ X ; μ] ≤ H[X ; μ] := by
  have hfX : Measurable (f ∘ X) := (measurable_of_finite _).comp hX
  have : H[X ; μ] = H[⟨ X, f ∘ X ⟩ ; μ] := by
    refine (entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) ?_).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule _ hX hfX]
  simp only [le_add_iff_nonneg_right]
  exact condEntropy_nonneg X (f ∘ X) μ

/-- A Schroder-Bernstein type theorem for entropy: if two random variables are functions of each
  other, then they have the same entropy.  Can be used as a substitute for
  `entropy_comp_of_injective` if one doesn't want to establish the injectivity. -/
lemma entropy_of_comp_eq_of_comp
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (f : S → T) (g : T → S) (h1 : Y = f ∘ X) (h2 : X = g ∘ Y) :
    H[X ; μ] = H[Y ; μ] := by
  have h3 : H[X ; μ] ≤ H[Y ; μ]  := by
    rw [h2]; exact entropy_comp_le μ hY _
  have h4 : H[Y ; μ] ≤ H[X ; μ]  := by
    rw [h1]; exact entropy_comp_le μ hX _
  linarith



end pair

section mutualInformation

/-- The mutual information $I[X:Y]$ of two random variables is defined to be $H[X] + H[Y] - H[X;Y]$. -/
noncomputable
def mutualInformation (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[⟨ X, Y ⟩ ; μ]

lemma mutualInformation_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
  mutualInformation X Y μ = H[X ; μ] + H[Y ; μ] - H[⟨ X, Y ⟩ ; μ] := rfl

@[inherit_doc mutualInformation] notation3:max "I[" X ":" Y ";" μ "]" => mutualInformation X Y μ
@[inherit_doc mutualInformation] notation3:max "I[" X ":" Y "]" => mutualInformation X Y volume

/-- $I[X:Y] = H[X] - H[X|Y]$. -/
lemma mutualInformation_eq_entropy_sub_condEntropy [MeasurableSingletonClass S]
    [MeasurableSingletonClass T] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  rw [mutualInformation_def, chain_rule μ hX hY]
  abel

/-- $I[X:Y] = I[Y:X]$. -/
lemma mutualInformation_comm [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    I[X : Y ; μ] = I[Y : X ; μ] := by simp_rw [mutualInformation, add_comm, entropy_comm hX hY]

/-- Mutual information is non-negative. -/
lemma mutualInformation_nonneg [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
    0 ≤ I[X : Y ; μ] := by
  have : IsFiniteMeasure (μ.map (⟨ X, Y ⟩)) :=
    Measure.isFiniteMeasure_map _ _
  simp_rw [mutualInformation_def, entropy_def]
  have h_fst : μ.map X = (μ.map (⟨ X, Y ⟩)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prod_mk hY)]
    congr
  have h_snd : μ.map Y = (μ.map (⟨ X, Y ⟩)).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prod_mk hY)]
    congr
  rw [h_fst, h_snd]
  exact measureMutualInfo_nonneg _

/-- Substituting variables for ones with the same distributions doesn't change the mutual information. -/
lemma IdentDistrib.mutualInformation_eq {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X' : Ω' → S} {Y' : Ω' → T} (hXY : IdentDistrib (⟨X,Y⟩) (⟨X',Y'⟩) μ μ') :
      I[X : Y ; μ] = I[X' : Y' ; μ'] := by
  have hX : IdentDistrib X X' μ μ' := hXY.comp measurable_fst
  have hY : IdentDistrib Y Y' μ μ' := hXY.comp measurable_snd
  simp_rw [mutualInformation_def,hX.entropy_eq,hY.entropy_eq,hXY.entropy_eq]

/-- Subadditivity of entropy. -/
lemma entropy_pair_le_add [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
    H[⟨ X, Y ⟩ ; μ] ≤ H[X ; μ] + H[Y ; μ] :=
  sub_nonneg.1 $ mutualInformation_nonneg hX hY _

/-- $I[X:Y]=0$ iff $X,Y$ are independent. -/
lemma mutualInformation_eq_zero (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    I[X : Y ; μ] = 0 ↔ IndepFun X Y μ := by
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
  convert measureMutualInfo_eq_zero_iff (μ.map (⟨ X, Y ⟩))
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ext_iff_measureReal_singleton]
  congr! with p
  convert measureReal_prod_prod (μ:=  μ.map X) (ν := μ.map Y) {p.1} {p.2}
  · simp
  · exact Measure.map_map measurable_fst (hX.prod_mk hY)
  · exact Measure.map_map measurable_snd (hX.prod_mk hY)

/-- Random variables are always independent of constants. -/
lemma indepFun_const [IsProbabilityMeasure μ] (c : T) :
    IndepFun X (fun _ => c) μ := by
  rw [IndepFun_iff,MeasurableSpace.comap_const]
  intro t₁ t₂ _ ht₂
  rcases MeasurableSpace.measurableSet_bot_iff.mp ht₂ with h | h
  all_goals simp [h]

/-- The mutual information with a constant is always zero. -/
lemma mutualInformation_const (hX : Measurable X) (c : T) {μ : Measure Ω} [IsProbabilityMeasure μ] :
    I[X : (fun _ => c) ; μ] = 0 := by
  exact (mutualInformation_eq_zero hX measurable_const).mpr (indepFun_const c)

lemma IndepFun.condEntropy_eq_entropy {μ : Measure Ω} (h : IndepFun X Y μ)
    (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ]  :
    H[X | Y ; μ] = H[X ; μ] := by
  have := (mutualInformation_eq_zero hX hY).2 h
  rw [mutualInformation_eq_entropy_sub_condEntropy hX hY] at this
  linarith

/-- $H[X,Y] = H[X] + H[Y]$ if and only if $X,Y$ are independent. -/
lemma entropy_pair_eq_add (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    H[⟨ X, Y ⟩ ; μ] = H[X ; μ] + H[Y ; μ] ↔ IndepFun X Y μ := by
  rw [eq_comm, ←sub_eq_zero]
  exact mutualInformation_eq_zero hX hY

/-- If $X,Y$ are independent, then $H[X,Y] = H[X] + H[Y]$. -/
lemma entropy_pair_eq_add' (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h: IndepFun X Y μ) :
    H[⟨ X, Y ⟩ ; μ] = H[X ; μ] + H[Y ; μ] :=
  (entropy_pair_eq_add hX hY).2 h

variable [AddGroup S] in
/-- $I[X : X + Y] = H[X + Y] - H[Y]$ iff $X, Y$ are independent. -/
lemma mutualInformation_add_right {Y : Ω → S} (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h: IndepFun X Y μ) :
    I[X : X + Y ; μ] = H[X + Y; μ] - H[Y; μ] := by
  rw [mutualInformation_def, entropy_add_right hX hY, entropy_pair_eq_add' hX hY h]
  abel


/-- The conditional mutual information $I[X:Y|Z]$ is the mutual information of $X|Z=z$ and $Y|Z=z$,
integrated over $z$. -/
noncomputable
def condMutualInformation (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω := by volume_tac) :
    ℝ := (μ.map Z)[fun z ↦ H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[⟨ X, Y ⟩ | Z ← z ; μ]]

lemma condMutualInformation_def (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) :
    condMutualInformation X Y Z μ = (μ.map Z)[fun z ↦
      H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[⟨ X, Y ⟩ | Z ← z ; μ]] := rfl

@[inherit_doc condMutualInformation]
notation3:max "I[" X ":" Y "|" Z ";" μ "]" => condMutualInformation X Y Z μ
@[inherit_doc condMutualInformation]
notation3:max "I[" X ":" Y "|" Z "]" => condMutualInformation X Y Z volume

/-- The conditional mutual information agrees with the information of the conditional kernel.
-/
lemma condMutualInformation_eq_kernel_mutualInfo
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    I[X : Y | Z ; μ] = Ik[condEntropyKernel (⟨ X, Y ⟩) Z μ, μ.map Z] := by
  simp_rw [condMutualInformation_def, entropy_def, kernel.mutualInfo, kernel.entropy,
    integral_eq_sum, smul_eq_mul, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr with x
  · have h := condEntropyKernel_fst_ae_eq hX hY hZ μ
    rw [Filter.EventuallyEq, ae_iff_of_fintype] at h
    specialize h x
    by_cases hx : (μ.map Z) {x} = 0
    · simp [hx]
    rw [h hx, condEntropyKernel_apply hX hZ]
    rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx
  · have h := condEntropyKernel_snd_ae_eq hX hY hZ μ
    rw [Filter.EventuallyEq, ae_iff_of_fintype] at h
    specialize h x
    by_cases hx : (μ.map Z) {x} = 0
    · simp [hx]
    rw [h hx, condEntropyKernel_apply hY hZ]
    rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx
  · by_cases hx : (μ.map Z) {x} = 0
    · simp [hx]
    rw [condEntropyKernel_apply (hX.prod_mk hY) hZ]
    rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx

lemma condMutualInformation_eq_integral_mutualInformation :
    I[X : Y | Z ; μ] = (μ.map Z)[fun z ↦ I[X : Y ; μ[|Z ⁻¹' {z}]]] := rfl

/-- $I[X:Y|Z] = I[Y:X|Z]$. -/
lemma condMutualInformation_comm [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U) (μ : Measure Ω) :
    I[X : Y | Z ; μ] = I[Y : X | Z ; μ] := by
  simp_rw [condMutualInformation_def, add_comm, entropy_comm hX hY]

/-- Conditional information is non-nonegative. -/
lemma condMutualInformation_nonneg [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U) (μ : Measure Ω) [IsFiniteMeasure μ] :
    0 ≤ I[X : Y | Z ; μ] := by
  refine integral_nonneg (fun z ↦ ?_)
  exact mutualInformation_nonneg hX hY _

/-- $$ I[X:Y|Z] = H[X|Z] + H[Y|Z] - H[X,Y|Z].$$ -/
lemma condMutualInformation_eq (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z; μ] - H[⟨X, Y⟩ | Z ; μ] := by
  rw [condMutualInformation_eq_kernel_mutualInfo hX hY hZ, kernel.mutualInfo,
    kernel.entropy_congr (condEntropyKernel_fst_ae_eq hX hY hZ _),
    kernel.entropy_congr (condEntropyKernel_snd_ae_eq hX hY hZ _),
    condEntropy_eq_kernel_entropy hX hZ, condEntropy_eq_kernel_entropy hY hZ,
    condEntropy_eq_kernel_entropy (hX.prod_mk hY) hZ]

/-- $$ I[X:Y|Z] = H[X|Z] - H[X|Y,Z].$$ -/
lemma condMutualInformation_eq' (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    I[X : Y | Z ; μ] = H[X | Z ; μ] - H[X | ⟨Y, Z⟩  ; μ] := by
  rw [condMutualInformation_eq hX hY hZ, cond_chain_rule _ hX hY hZ]
  ring

lemma condMutualInformation_of_inj_map [IsProbabilityMeasure μ]
  (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
  {V : Type*} [Nonempty V] [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  (f : U → S → V) (hf : ∀ t, Function.Injective (f t)) :
    I[fun ω ↦ f (Z ω) (X ω) : Y | Z ; μ] =
    I[X : Y | Z ; μ] := by
  have hM : Measurable (Function.uncurry f ∘ ⟨Z, X⟩) :=
    (measurable_of_countable _).comp (hZ.prod_mk hX)
  have hM : Measurable fun ω ↦ f (Z ω) (X ω) := hM
  rw [condMutualInformation_eq hM hY hZ, condMutualInformation_eq hX hY hZ]
  let g : U → (S × T) → (V × T) := fun z (x,y) ↦ (f z x, y)
  have hg : ∀ t, Function.Injective (g t) :=
    fun _ _ _ h ↦ Prod.ext_iff.2 ⟨hf _ (Prod.ext_iff.1 h).1, (Prod.ext_iff.1 h).2⟩
  rw [← condEntropy_of_inj_map μ (hX.prod_mk hY) hZ g hg, ← condEntropy_of_inj_map μ hX hZ _ hf]

section IsProbabilityMeasure
variable (μ : Measure Ω) [IsProbabilityMeasure μ] [MeasurableSingletonClass S]
  [MeasurableSingletonClass T]

/-- $$ H[X] - H[X|Y] = I[X:Y] $$ -/
lemma entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) :
    H[X ; μ] - H[X | Y ; μ] = I[X : Y ; μ] := by
  rw [mutualInformation_def, chain_rule _ hX hY, add_comm, add_sub_add_left_eq_sub]

/-- $$ H[X|Y] ≤ H[X] $$ -/
lemma condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ] :
    H[X | Y ; μ] ≤ H[X ; μ] :=
  sub_nonneg.1 $ by rw [entropy_sub_condEntropy _ hX hY]; exact mutualInformation_nonneg hX hY _

/-- $H[X|Y,Z] \leq H[X|Z]$ -/
lemma entropy_submodular (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[X | ⟨ Y, Z ⟩ ; μ] ≤ H[X | Z ; μ] := by
  rw [condEntropy_eq_kernel_entropy hX hZ, condEntropy_two_eq_kernel_entropy hX hY hZ]
  have : IsMarkovKernel (condEntropyKernel (fun a ↦ (Y a, X a)) Z μ) :=
    isMarkovKernel_condEntropyKernel (hY.prod_mk hX) hZ μ
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  refine (kernel.entropy_condKernel_le_entropy_snd _ _).trans_eq ?_
  exact kernel.entropy_congr (condEntropyKernel_snd_ae_eq hY hX hZ _)

/-- The submodularity inequality:
$$ H[X,Y,Z] + H[Z] \leq H[X,Z] + H[Y,Z].$$ -/
lemma entropy_triple_add_entropy_le
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[⟨ X, ⟨ Y, Z ⟩ ⟩; μ] + H[Z ; μ] ≤
      H[⟨ X, Z ⟩ ; μ] + H[⟨ Y, Z ⟩ ; μ] := by
  rw [chain_rule _ hX (hY.prod_mk hZ), chain_rule _ hX hZ, chain_rule _ hY hZ]
  ring_nf
  exact add_le_add le_rfl (entropy_submodular _ hX hY hZ)

variable {μ : Measure Ω}

/-- The assertion that X and Y are conditionally independent relative to Z.  -/
def condIndepFun (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) : Prop := ∀ᵐ z ∂ (μ.map Z),  IndepFun X Y (μ[|Z ⁻¹' {z}])

lemma condIndepFun_iff (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω): condIndepFun X Y Z μ ↔ ∀ᵐ z ∂ (μ.map Z),  IndepFun X Y (μ[|Z ⁻¹' {z}]) := by rfl


/-- $I[X:Y|Z]=0$ iff $X,Y$ are conditionally independent over $Z$. -/
lemma condMutualInformation_eq_zero (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [IsProbabilityMeasure μ]  [Fintype U]:
     I[X : Y | Z ; μ] = 0 ↔ condIndepFun X Y Z μ := by
  rw [condIndepFun_iff, condMutualInformation_eq_integral_mutualInformation, integral_eq_zero_iff_of_nonneg ]
  . dsimp
    have : (fun x ↦ I[X:Y;μ[|Z ⁻¹' {x}]]) =ᵐ[μ.map Z] 0 ↔ ∀ᵐ z ∂(μ.map Z), I[X : Y ; μ[|Z ⁻¹' {z}]] = 0 := by rfl
    rw [this]
    apply Filter.eventually_congr
    rw [ae_iff_of_fintype]
    intro z hz
    rw [Measure.map_apply hZ (measurableSet_singleton z)] at hz
    have : IsProbabilityMeasure (μ[|Z ⁻¹' {z}]) := cond_isProbabilityMeasure μ hz
    exact mutualInformation_eq_zero hX hY
  . dsimp
    rw [Pi.le_def]
    intro z; simp
    by_cases hz : μ (Z ⁻¹' {z}) = 0
    · have : μ[|Z ⁻¹' {z}] = 0 := cond_eq_zero_of_measure_zero hz
      simp [this]
      rw [mutualInformation_def]
      simp
    have : IsProbabilityMeasure (μ[|Z ⁻¹' {z}]) := cond_isProbabilityMeasure μ hz
    apply mutualInformation_nonneg hX hY
  simp

/-- If $X, Y$ are conditionally independent over $Z$, then $H[X,Y,Z] = H[X,Z] + H[Y,Z] - H[Z]$. -/
lemma ent_of_cond_indep (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
     (h : condIndepFun X Y Z μ) [IsProbabilityMeasure μ] :
     H[ ⟨ X, ⟨ Y, Z ⟩ ⟩ ; μ ] = H[ ⟨ X, Z ⟩; μ ] + H[ ⟨ Y, Z ⟩; μ ] - H[Z; μ] := by
  have hI : I[X : Y | Z ; μ] = 0 := (condMutualInformation_eq_zero hX hY hZ).mpr h
  rw [condMutualInformation_eq hX hY hZ] at hI
  rw [entropy_assoc hX hY hZ, chain_rule _ (hX.prod_mk hY) hZ, chain_rule _ hX hZ, chain_rule _ hY hZ]
  linarith [hI]

end IsProbabilityMeasure
end mutualInformation

section copy

variable {mΩ' : MeasurableSpace Ω'}

/-- The following three lemmas should probably be in Mathlib. -/
lemma _root_.MeasurableSet_comap_fst {s : Set (S × T)}
  (h : MeasurableSet[MeasurableSpace.comap Prod.fst inferInstance] s) :
    ∃ s' : Set S, s' ×ˢ Set.univ = s := by
  simp_rw [Set.prod_univ]
  obtain ⟨s', _, hs'⟩ := h
  exact ⟨s', hs'⟩

lemma _root_.MeasurableSet_comap_snd {t : Set (S × T)}
    (h : MeasurableSet[MeasurableSpace.comap Prod.snd inferInstance] t) :
    ∃ t' : Set T, Set.univ ×ˢ t' = t := by
  simp_rw [Set.univ_prod]
  obtain ⟨t', _, ht'⟩ := h
  exact ⟨t', ht'⟩

lemma _root_.IndepFun.fst_snd [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
  IndepFun (Prod.fst : Ω × Ω' → Ω) (Prod.snd : Ω × Ω' → Ω') (μ.prod μ') := by
  rw [@IndepFun_iff]
  intro t1 t2 ht1 ht2
  obtain ⟨t1', ht1'⟩ := MeasurableSet_comap_fst ht1
  obtain ⟨t2', ht2'⟩ := MeasurableSet_comap_snd ht2
  simp [← ht1',← ht2', Set.top_eq_univ, Set.prod_inter_prod, Set.inter_univ, Set.univ_inter,
    Measure.prod_prod, measure_univ, mul_one, one_mul]

/-- For $X,Y$ random variables, one can find independent copies $X',Y'$ of $X,Y$. -/
lemma independent_copies {X : Ω → S} {Y : Ω' → T} (hX: Measurable X) (hY: Measurable Y)
    (μ : Measure Ω) (μ' : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    ∃ ν : Measure (S × T), ∃ X' : S × T → S, ∃ Y' : S × T → T, IsProbabilityMeasure ν
      ∧ Measurable X' ∧ Measurable Y' ∧ (IndepFun X' Y' ν)
      ∧ IdentDistrib X' X ν μ ∧ IdentDistrib Y' Y ν μ' := by
  use (μ.map X).prod (μ'.map Y)
  have := MeasureTheory.isProbabilityMeasure_map hX.aemeasurable (μ:=μ)
  have := MeasureTheory.isProbabilityMeasure_map hY.aemeasurable (μ:=μ')
  use Prod.fst
  use Prod.snd
  refine ⟨inferInstance, measurable_fst, measurable_snd, IndepFun.fst_snd, ?_, ?_⟩
  · refine ⟨measurable_fst.aemeasurable, hX.aemeasurable, ?_⟩
    simp? says simp only [Measure.map_fst_prod, measure_univ, one_smul]
  · refine ⟨measurable_snd.aemeasurable, hY.aemeasurable, ?_⟩
    simp? says simp only [Measure.map_snd_prod, measure_univ, one_smul]

/-- For $X,Y$ random variables, one can find independent copies $X',Y'$ of $X,Y$. Version
formulated in spaces with a canonical measures. -/
lemma independent_copies_two {Ω : Type u} {Ω' : Type v} [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω)] [IsProbabilityMeasure (ℙ : Measure Ω')]
    {X : Ω → S} {Y : Ω' → T} (hX : Measurable X) (hY : Measurable Y) :
    ∃ (Ω'' : Type (max u v)) (m'' : MeasureSpace Ω'') (X' : Ω'' → S) (Y' : Ω'' → T),
    IsProbabilityMeasure (ℙ : Measure Ω'') ∧ Measurable X' ∧ Measurable Y' ∧
      (IndepFun X' Y') ∧ IdentDistrib X' X ∧ IdentDistrib Y' Y := by
  refine ⟨Ω × Ω', by infer_instance, X ∘ Prod.fst, Y ∘ Prod.snd, by infer_instance,
    hX.comp measurable_fst, hY.comp measurable_snd, ?_, ?_, ?_⟩
  · exact IndepFun.fst_snd.comp hX hY
  · refine ⟨(hX.comp measurable_fst).aemeasurable, hX.aemeasurable, ?_⟩
    have : (ℙ : Measure (Ω × Ω')) = (ℙ : Measure Ω).prod (ℙ : Measure Ω') := rfl
    simp [← Measure.map_map hX measurable_fst, this]
  · refine ⟨(hY.comp measurable_snd).aemeasurable, hY.aemeasurable, ?_⟩
    have : (ℙ : Measure (Ω × Ω')) = (ℙ : Measure Ω).prod (ℙ : Measure Ω') := rfl
    simp [← Measure.map_map hY measurable_snd, this]

universe u v
open Function Set Measure

instance {I} [Fintype I] {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i : I, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (.pi μ) :=
  ⟨by simp_rw [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩

@[simp]
lemma pi_pi_set
    {I} [Fintype I] {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i : I, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (t : Set I) [DecidablePred (· ∈ t)] (s : (i : I) → Set (Ω i)) :
    Measure.pi μ (pi t s) = ∏ i in Finset.univ.filter (· ∈ t), μ i (s i) := by
  classical
  simp (config := {singlePass := true}) only [← pi_univ_ite]
  simp_rw [pi_pi, apply_ite, measure_univ,
    Finset.prod_ite, Finset.prod_const_one, mul_one]

@[simp]
lemma pi_pi_finset
    {I} [Fintype I] {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i : I, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (t : Finset I) (s : (i : I) → Set (Ω i)) :
    Measure.pi μ (pi t s) = ∏ i in t, μ i (s i) := by
  classical
  rw [pi_pi_set]
  congr; ext x; simp

@[simp]
lemma pi_eval_preimage
    {I} [Fintype I] {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i : I, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] {i : I} (s : Set (Ω i)) :
    Measure.pi μ (eval i ⁻¹' s) = μ i s := by
  classical
  simp_rw [eval_preimage, pi_pi, apply_update (fun i ↦ μ i), measure_univ,
    Finset.prod_update_of_mem (Finset.mem_univ _), Finset.prod_const_one, mul_one]

lemma map_eval_pi {I} [Fintype I] {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i : I, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] {i : I} :
    Measure.map (eval i) (Measure.pi μ) = μ i := by
  ext s hs
  simp_rw [Measure.map_apply (measurable_pi_apply i) hs, pi_eval_preimage]

/-- Let $X_i : \Omega_i \to S_i$ be random variables for $i=1,\dots,k$.
Then there exist jointly independent random variables $X'_i: \Omega' \to S_i$ for $i=1,\dots,k$
such that each $X'_i$ is a copy of $X_i$. -/
lemma independent_copies' {I: Type u} [Fintype I] {S : I → Type u'}
    [mS : ∀ i : I, MeasurableSpace (S i)] {Ω : I → Type v}
    [mΩ : ∀ i : I, MeasurableSpace (Ω i)] (X : ∀ i : I, Ω i → S i) (hX : ∀ i : I, Measurable (X i))
    (μ : ∀ i : I, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] :
    ∃ (A : Type (max u v)) (mA : MeasurableSpace A) (μA : Measure A) (X' : ∀ i, A → S i),
    IsProbabilityMeasure μA ∧
    iIndepFun mS X' μA ∧
    ∀ i : I, Measurable (X' i) ∧ IdentDistrib (X' i) (X i) μA (μ i) := by
  refine ⟨Π i, Ω i, inferInstance, .pi μ, fun i ↦ X i ∘ eval i, inferInstance, ?_, fun i ↦ ⟨?_, ?_⟩⟩
  · rw [iIndepFun_iff]
    intro t s hs
    choose! u _ hus using hs
    simp (config := {contextual := true}) [← hus, preimage_comp]
    simp_rw [← Finset.mem_coe, ← Set.pi_def, pi_pi_finset]
  · exact (hX i).comp (measurable_pi_apply i)
  · refine ⟨(hX i).comp (measurable_pi_apply i) |>.aemeasurable, (hX i).aemeasurable, ?_⟩
    rw [← Measure.map_map (hX i) (measurable_pi_apply i), map_eval_pi]

/- This is neither `Fin.elim0` nor `Fin.elim0'` -/
def Fin.rec0 {α : Fin 0 → Sort*} (i : Fin 0) : α i := absurd i.2 (Nat.not_lt_zero _)

instance _root_.ULift.measurableSpace [m : MeasurableSpace Ω] : MeasurableSpace (ULift Ω) :=
  m.comap ULift.down

def _root_.ULift.isProbabilityMeasure (m : IsProbabilityMeasure μ) :
    IsProbabilityMeasure (μ.comap ULift.down) := by
  refine' ⟨_⟩
  rw [Measure.comap_apply _ ULift.down_injective _ _ MeasurableSet.univ]
  simp [ULift.down_surjective.range_eq]
  intro s ⟨s',hs',hs⟩
  rw [←hs, Set.image_preimage_eq _ ULift.down_surjective]
  exact hs'

lemma identDistrib_ulift_self {X : Ω → S} (hX : Measurable X) :
    IdentDistrib X (X ∘ ULift.down) μ (μ.comap ULift.down) := by
  have hX' : Measurable (X ∘ ULift.down : ULift.{u_1,uΩ} Ω → S) := hX.comp (comap_measurable _)
  refine' ⟨hX.aemeasurable, hX'.aemeasurable, _⟩
  ext s hs
  rw [Measure.map_apply (μ := (μ.comap ULift.down)) hX' hs,
    Measure.comap_apply _ ULift.down_injective _ _ (hX' hs), Set.preimage_comp,
    Set.image_preimage_eq _ ULift.down_surjective, Measure.map_apply hX hs]
  intro s ⟨s',hs',hs⟩
  rw [←hs, Set.image_preimage_eq _ ULift.down_surjective]
  exact hs'

/-- A version with exactly 3 random variables that have the same codomain.
It's unfortunately incredibly painful to prove this from the general case. -/
lemma independent_copies3_nondep {S : Type u}
    [mS : MeasurableSpace S]
    {Ω₁ : Type u_1} {Ω₂ : Type u_2} {Ω₃ : Type u_3}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {X₁ : Ω₁ → S} {X₂ : Ω₂ → S} {X₃ : Ω₃ → S}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃)
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃)
    [hμ₁ : IsProbabilityMeasure μ₁] [hμ₂ : IsProbabilityMeasure μ₂] [hμ₃ : IsProbabilityMeasure μ₃] :
    ∃ (A : Type (max u_1 u_2 u_3)) (mA : MeasurableSpace A) (μA : Measure A)
      (X₁' X₂' X₃' : A → S),
    IsProbabilityMeasure μA ∧
    iIndepFun (fun _ ↦ mS) ![X₁', X₂', X₃'] μA ∧
      Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧
      IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂ ∧ IdentDistrib X₃' X₃ μA μ₃ := by
  let Ω₁' : Type (max u_1 u_2 u_3) := ULift.{max u_2 u_3} Ω₁
  let Ω₂' : Type (max u_1 u_2 u_3) := ULift.{max u_1 u_3} Ω₂
  let Ω₃' : Type (max u_1 u_2 u_3) := ULift.{max u_1 u_2} Ω₃
  let Ω : Fin 3 → Type (max u_1 u_2 u_3) := ![Ω₁', Ω₂', Ω₃']
  let mΩ : (i : Fin 3) → MeasurableSpace (Ω i) :=
    Fin.cases (inferInstance : MeasurableSpace Ω₁') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₂') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₃') Fin.rec0
  let X : (i : Fin 3) → Ω i → S :=
    Fin.cases (X₁ ∘ ULift.down) <| Fin.cases (X₂ ∘ ULift.down) <| Fin.cases (X₃ ∘ ULift.down) Fin.rec0
  have hX : ∀ (i : Fin 3), @Measurable _ _ (mΩ i) mS (X i) :=
    Fin.cases (hX₁.comp (comap_measurable _)) <|
    Fin.cases (hX₂.comp (comap_measurable _)) <|
    Fin.cases (hX₃.comp (comap_measurable _)) Fin.rec0
  let μ : (i : Fin 3) → @Measure (Ω i) (mΩ i) :=
    Fin.cases (μ₁.comap ULift.down) <|
    Fin.cases (μ₂.comap ULift.down) <|
    Fin.cases (μ₃.comap ULift.down) Fin.rec0
  let hμ : (i : Fin 3) → IsProbabilityMeasure (μ i) :=
    Fin.cases (ULift.isProbabilityMeasure hμ₁) <|
    Fin.cases (ULift.isProbabilityMeasure hμ₂) <|
    Fin.cases (ULift.isProbabilityMeasure hμ₃) Fin.rec0
  obtain ⟨A, mA, μA, X', hμ, hi, hX'⟩ := independent_copies' X hX μ
  refine ⟨A, mA, μA, X' 0, X' 1, X' 2, hμ, ?_,
    (hX' 0).1, (hX' 1).1, (hX' 2).1,
    (hX' 0).2.trans ((identDistrib_ulift_self hX₁).symm),
    (hX' 1).2.trans (identDistrib_ulift_self hX₂).symm,
    (hX' 2).2.trans (identDistrib_ulift_self hX₃).symm⟩
  convert hi; ext i; fin_cases i <;> rfl

/-- A version with exactly 4 random variables that have the same codomain.
It's unfortunately incredibly painful to prove this from the general case. -/
lemma independent_copies4_nondep {S : Type u}
    [mS : MeasurableSpace S]
    {Ω₁ Ω₂ Ω₃ Ω₄ : Type v}
    [mΩ₁ : MeasurableSpace Ω₁] [mΩ₂ : MeasurableSpace Ω₂]
    [mΩ₃ : MeasurableSpace Ω₃] [mΩ₄ : MeasurableSpace Ω₄]
    {X₁ : Ω₁ → S} {X₂ : Ω₂ → S} {X₃ : Ω₃ → S} {X₄ : Ω₄ → S}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃) (hX₄ : Measurable X₄)
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃) (μ₄ : Measure Ω₄)
    [hμ₁ : IsProbabilityMeasure μ₁] [hμ₂ : IsProbabilityMeasure μ₂]
    [hμ₃ : IsProbabilityMeasure μ₃] [hμ₄ : IsProbabilityMeasure μ₄] :
    ∃ (A : Type v) (mA : MeasurableSpace A) (μA : Measure A)
      (X₁' X₂' X₃' X₄' : A → S),
    IsProbabilityMeasure μA ∧
    iIndepFun (fun _ ↦ mS) ![X₁', X₂', X₃', X₄'] μA ∧
    Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧ Measurable X₄' ∧
    IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂ ∧
    IdentDistrib X₃' X₃ μA μ₃ ∧ IdentDistrib X₄' X₄ μA μ₄ := by
  let Ω : Fin 4 → Type v := ![Ω₁, Ω₂, Ω₃, Ω₄]
  let mΩ : (i : Fin 4) → MeasurableSpace (Ω i) :=
    Fin.cases mΩ₁ <| Fin.cases mΩ₂ <| Fin.cases mΩ₃ <| Fin.cases mΩ₄ Fin.rec0
  let X : (i : Fin 4) → Ω i → S :=
    Fin.cases X₁ <| Fin.cases X₂ <| Fin.cases X₃ <| Fin.cases X₄ Fin.rec0
  have hX : ∀ (i : Fin 4), @Measurable _ _ (mΩ i) mS (X i) :=
    Fin.cases hX₁ <| Fin.cases hX₂ <| Fin.cases hX₃ <| Fin.cases hX₄ Fin.rec0
  let μ : (i : Fin 4) → @Measure (Ω i) (mΩ i) :=
    Fin.cases μ₁ <| Fin.cases μ₂ <| Fin.cases μ₃ <| Fin.cases μ₄ Fin.rec0
  let hμ : (i : Fin 4) → IsProbabilityMeasure (μ i) :=
    Fin.cases hμ₁ <| Fin.cases hμ₂ <| Fin.cases hμ₃ <| Fin.cases hμ₄ Fin.rec0
  obtain ⟨A, mA, μA, X', hμ, hi, hX'⟩ := independent_copies' X hX μ
  refine ⟨A, mA, μA, X' 0, X' 1, X' 2, X' 3, hμ, ?_,
    (hX' 0).1, (hX' 1).1, (hX' 2).1, (hX' 3).1,
    (hX' 0).2, (hX' 1).2, (hX' 2).2, (hX' 3).2⟩
  convert hi; ext i; fin_cases i <;> rfl

/-- The law of total probability: a measure $\mu$ can be expressed as a mixture of its conditional measures $\mu[|Y^{-1}\{y\}]$ from a finitely valued random variable $Y$.-/
lemma law_of_total_probability [Fintype T] [MeasurableSingletonClass T] {Y: Ω → T} (hY: Measurable Y) (μ: Measure Ω) [IsFiniteMeasure μ]: μ = ∑ y : T, (μ (Y⁻¹' {y})) • (μ[|Y ⁻¹' {y}]) := by
  apply Measure.ext
  intro E hE
  simp
  have : μ E = ∑ y : T, μ (Y⁻¹' {y} ∩ E) := by
    have : E = ⋃ y ∈ Set.univ, Y⁻¹' {y} ∩ E := by
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
  rcases eq_or_ne (μ (Y⁻¹' {y})) 0 with hy | hy
  . simp [hy]
    exact measure_inter_null_of_null_left E hy
  symm
  rw [mul_comm, cond_mul_eq_inter _ (hY (MeasurableSet.singleton y)) hy]

/-- To show identical distribution of two random variables on a mixture of probability measures, it suffices to do so on each non-trivial component. --/
-- in fact this is an if and only if
lemma identDistrib_of_sum {X : Ω → S} {Y : Ω' → S} [Fintype T] {μ : T → Measure Ω} {μ' : T → Measure Ω'} {w : T → ENNReal} (hX: Measurable X) (hY: Measurable Y) (h_ident : ∀ y : T, (w y ≠ 0) → IdentDistrib X Y (μ y) (μ' y)) : IdentDistrib X Y (∑ y : T, (w y) • (μ y)) (∑ y : T, (w y) • (μ' y)) := {
  aemeasurable_fst := hX.aemeasurable,
  aemeasurable_snd := hY.aemeasurable,
  map_eq := by
    rw [<-Measure.mapₗ_apply_of_measurable hX, <-Measure.mapₗ_apply_of_measurable hY]
    simp
    congr with y E _
    rcases eq_or_ne (w y) 0 with hy | hy
    . simp [hy]
    congr 3
    rw [Measure.mapₗ_apply_of_measurable hX, Measure.mapₗ_apply_of_measurable hY]
    exact (h_ident y hy).map_eq
}

/-- A random variable is identically distributed to its lift to a product space (in the first factor). -/
lemma identDistrib_comp_fst {X : Ω → S} (hX: Measurable X) (μ : Measure Ω) (μ' : Measure Ω') [IsProbabilityMeasure μ']: IdentDistrib (X ∘ Prod.fst) X (μ.prod μ') μ := {
  aemeasurable_fst := (hX.comp measurable_fst).aemeasurable
  aemeasurable_snd := hX.aemeasurable
  map_eq := by
    rw [<- Measure.map_map hX measurable_fst, Measure.map_fst_prod]
    congr
    simp
}

/-- A random variable is identically distributed to its lift to a product space (in the second factor). -/
lemma identDistrib_comp_snd {X : Ω → S} (hX: Measurable X) (μ : Measure Ω) (μ' : Measure Ω') [MeasureTheory.SigmaFinite μ][IsProbabilityMeasure μ']: IdentDistrib (X ∘ Prod.snd) X (μ'.prod μ) μ := {
  aemeasurable_fst := (hX.comp measurable_snd).aemeasurable
  aemeasurable_snd := hX.aemeasurable
  map_eq := by
    rw [<- Measure.map_map hX measurable_snd, Measure.map_snd_prod]
    congr
    simp
}

/-- A random variable is identically distributed to its pullbacks. -/
lemma identDistrib_map {X : Ω → S} (hX: Measurable X) {f: S → T} (hf: Measurable f) (μ : Measure Ω) : IdentDistrib f (f ∘ X) (μ.map X) μ := {
  aemeasurable_fst := hf.aemeasurable
  aemeasurable_snd := (hf.comp hX).aemeasurable
  map_eq := map_map hf hX
}


/-- For $X,Y$ random variables, there exist conditionally independent trials
$X_1, X_2, Y'$.-/
lemma condIndependent_copies {S T : Type u} [MeasurableSpace S] [Fintype T] [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω → T) (hX: Measurable X) (hY: Measurable Y) (μ: Measure Ω) [IsProbabilityMeasure μ]:
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (X_1 X_2 : Ω' → S) (Y' : Ω' → T) (ν : Measure Ω'),
    IsProbabilityMeasure ν ∧ Measurable X_1 ∧ Measurable X_2 ∧ Measurable Y' ∧
    (condIndepFun X_1 X_2 Y' ν) ∧ IdentDistrib (⟨ X_1, Y' ⟩)
    (⟨ X, Y ⟩) ν μ ∧ IdentDistrib (⟨ X_2, Y' ⟩) (⟨ X, Y ⟩) ν μ := by
  let m' := fun (y : T) ↦ ((μ[|Y ⁻¹' {y}]).map X)
  let m := fun (y : T) ↦ ((m' y).prod (m' y)).prod (Measure.dirac y)
  let ν : Measure ((S × S) × T) := ∑ y : T, ((μ (Y⁻¹' {y})) • (m y))

  have h3' (y : T) : { ω : Ω | Y ω = y } ∈ ae (μ[|Y⁻¹' {y}]) := by
    rw [mem_ae_iff, <-cond_inter_self]
    . have : (Y⁻¹' {y}) ∩ { ω : Ω | Y ω = y }ᶜ = ∅ := by
        ext _; simp
      simp [this]
    exact hY trivial

  have h3 (y : T) : IdentDistrib (fun ω ↦ (X ω, y)) (⟨ X, Y ⟩) (μ[|Y⁻¹' {y}]) (μ[|Y⁻¹' {y}]) := by
    apply IdentDistrib.of_ae_eq (hX.prod_mk measurable_const).aemeasurable
    apply Filter.eventuallyEq_of_mem (h3' y)
    intro ω; simp; exact fun a ↦ id a.symm

  have h4 (y : T): { ω : (S × S) × T| ω.2 = y } ∈ ae ( m y ) := by
    rw [mem_ae_iff]
    have : { ω : (S × S) × T | ω.2 = y}ᶜ = Prod.snd⁻¹' {t : T | t ≠ y} := by simp; rfl
    rw [this, <-Measure.map_apply measurable_snd]
    all_goals {simp}

  have h5 {y : T} (hy: μ (Y⁻¹' {y}) ≠ 0): IsProbabilityMeasure (m' y) := by
    have : IsProbabilityMeasure (μ[|Y ⁻¹' {y}]) := cond_isProbabilityMeasure μ hy
    exact isProbabilityMeasure_map (Measurable.aemeasurable hX)

  refine ⟨ (S × S) × T, by infer_instance, fun ω ↦ ω.1.1, fun ω ↦ ω.1.2, fun ω ↦ ω.2, ν, ?_, measurable_fst.comp measurable_fst, measurable_snd.comp measurable_fst, measurable_snd, ?_, ?_, ?_ ⟩
  . constructor
    simp
    have : ∑ y : T, μ (Y⁻¹' {y})*1 = 1 := by
      simp
      rw [show 1 = μ Set.univ by simp]
      symm
      convert measure_biUnion_finset _ _
      . simp; ext _; simp
      . intro _ _ _ _ hyz
        apply Disjoint.preimage
        simp [hyz]
      intros
      exact hY trivial
    rw [<-this]
    congr with y
    rcases eq_or_ne (μ (Y⁻¹' {y})) 0 with hy | hy
    . simp [hy]
    congr 1
    have : IsProbabilityMeasure (m' y) := h5 hy
    simp
  . rw [condIndepFun_iff, ae_iff_of_fintype]
    have h1 : ν.map Prod.snd = μ.map Y := by
      rw [law_of_total_probability hY μ, <-Measure.mapₗ_apply_of_measurable measurable_snd, <-Measure.mapₗ_apply_of_measurable hY]
      simp
      congr with y
      rcases eq_or_ne (μ (Y⁻¹' {y})) 0 with hy | hy
      . simp [hy]
      have h6 : IsProbabilityMeasure (m' y) := h5 hy
      have h7 : IsProbabilityMeasure (μ[|Y⁻¹' {y}]) := cond_isProbabilityMeasure μ hy
      congr 3
      rw [Measure.mapₗ_apply_of_measurable measurable_snd, Measure.mapₗ_apply_of_measurable hY]
      simp
      have := Measure.map_const (μ[|Y⁻¹' {y}]) y
      simp at this; rw [<-this]
      apply Measure.map_congr
      apply Filter.eventuallyEq_of_mem (h3' y)
      intro ω; simp; exact fun a ↦ id a.symm
    intro y hy
    have hy' : ν (Prod.snd⁻¹' {y}) = μ (Y⁻¹' {y}) := by
      rw [<- map_apply measurable_snd (by simp), <-map_apply hY trivial, h1]
    rw [h1] at hy
    have hy'' : μ (Y⁻¹' {y}) ≠ 0 := by
      convert hy
      exact (map_apply hY trivial).symm

    have h2 : ν[| Prod.snd⁻¹' {y} ] = m y := by
      rw [Measure.ext_iff]
      intro E _
      rw [cond_apply ν (measurable_snd (by simp)) E, hy']
      simp
      have h3 : (m y) ((Prod.snd⁻¹' {y}) ∩ E) = (m y) E := by
        apply measure_congr
        apply inter_ae_eq_right_of_ae_eq_univ
        simp
        rw [(show (Prod.snd⁻¹' {y})ᶜ = Prod.snd⁻¹' ({y}ᶜ) by rfl), <- map_apply measurable_snd (by simp)]
        simp
      have h3' {x : T} (hx: x ≠ y): (m x) ((Prod.snd⁻¹' {y}) ∩ E) = 0 := by
        apply measure_inter_null_of_null_left E
        rw [<- Measure.map_apply measurable_snd (by simp), MeasureTheory.Measure.map_snd_prod]
        simp; right; exact hx
      rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
      . rw [h3, <-mul_assoc, ENNReal.inv_mul_cancel hy'', one_mul]
        finiteness
      intro x _ hx
      rw [h3' hx]
      simp
    rw [h2, indepFun_iff_map_prod_eq_prod_map_map]
    . let f : (S × S) × T → (S × S) := Prod.fst
      show ((m y).map f) = ((m y).map (Prod.fst ∘ f)).prod ((m y).map (Prod.snd ∘ f))
      have : IsProbabilityMeasure (m' y) := h5 hy''
      have : (m y).map f = (m' y).prod (m' y) := by simp
      rw [<-map_map measurable_fst measurable_fst, <-map_map measurable_snd measurable_fst, this]
      simp
    . exact measurable_fst.comp measurable_fst
    exact measurable_snd.comp measurable_fst
  . rw [law_of_total_probability hY μ]
    apply identDistrib_of_sum ((measurable_fst.comp measurable_fst).prod_mk measurable_snd) (hX.prod_mk hY)
    intro y hy
    have h1 : IdentDistrib (fun ω ↦ (ω.1.1, ω.2)) (fun ω ↦ (ω.1.1, y)) (m y) (m y) := by
      apply IdentDistrib.of_ae_eq ((measurable_fst.comp measurable_fst).prod_mk measurable_snd).aemeasurable
      apply Filter.eventuallyEq_of_mem (h4 y)
      intro _;  simp
    have h2 : IdentDistrib (fun ω ↦ (ω.1.1, y)) (fun ω ↦ (X ω, y)) (m y) (μ[|Y⁻¹' {y}]) := by
      let f := fun (x : S) ↦ (x, y)
      show IdentDistrib (f ∘ (Prod.fst ∘ Prod.fst)) (f ∘ X) (m y) (μ[|Y⁻¹' {y}])
      apply IdentDistrib.comp _ measurable_prod_mk_right
      apply (identDistrib_comp_fst measurable_fst _ _).trans
      have : IsProbabilityMeasure ((μ[|Y ⁻¹' {y}]).map X) := h5 hy
      apply (identDistrib_comp_fst measurable_id _ _).trans
      apply identDistrib_map hX measurable_id
    exact (h1.trans h2).trans (h3 y)
  rw [law_of_total_probability hY μ]
  apply identDistrib_of_sum ((measurable_snd.comp measurable_fst).prod_mk measurable_snd) (hX.prod_mk hY)
  intro y hy
  have h1 : IdentDistrib (fun ω ↦ (ω.1.2, ω.2)) (fun ω ↦ (ω.1.2, y)) (m y) (m y) := by
    apply IdentDistrib.of_ae_eq ((measurable_snd.comp measurable_fst).prod_mk measurable_snd).aemeasurable
    apply Filter.eventuallyEq_of_mem (h4 y)
    intro _;  simp
  have h2 : IdentDistrib (fun ω ↦ (ω.1.2, y)) (fun ω ↦ (X ω, y)) (m y) (μ[|Y⁻¹' {y}]) := by
    let f := fun (x : S) ↦ (x, y)
    show IdentDistrib (f ∘ (Prod.snd ∘ Prod.fst)) (f ∘ X) (m y) (μ[|Y⁻¹' {y}])
    apply IdentDistrib.comp _ measurable_prod_mk_right
    apply (identDistrib_comp_fst measurable_snd _ _).trans
    have : IsProbabilityMeasure ((μ[|Y ⁻¹' {y}]).map X) := h5 hy
    apply (identDistrib_comp_snd measurable_id _ _).trans
    apply identDistrib_map hX measurable_id
  exact (h1.trans h2).trans (h3 y)


end copy


end ProbabilityTheory



section MeasureSpace_example

open ProbabilityTheory

variable {Ω S T : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T}

/-- An example to illustrate how `MeasureSpace` can be used to suppress the ambient measure. -/
example (hX : Measurable X) (hY : Measurable Y) :
  H[⟨ X, Y ⟩] = H[Y] + H[X | Y] := chain_rule _ hX hY

end MeasureSpace_example
