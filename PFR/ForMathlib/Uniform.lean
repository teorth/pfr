import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ConditionalProbability
import PFR.ForMathlib.MeasureReal
import PFR.ForMathlib.FiniteRange

open Function MeasureTheory Set
open scoped BigOperators ENNReal

namespace ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  [Countable S] [Countable T] [Nonempty T] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] {X : Ω → S} {Y : Ω → T} {μ : Measure Ω}
  {H : Set S}

/-- The assertion that the law of $X$ is the uniform probability measure on a finite set $H$.
While in applications $H$ will be non-empty finite set, $X$ measurable, and and $μ$ a probability
measure, it could be technically convenient to have a definition that works even without these
hypotheses.  (For instance, `isUniform` would be well-defined, but false, for infinite `H`) -/
structure IsUniform (H : Set S) (X : Ω → S) (μ : Measure Ω := by volume_tac) : Prop :=
  eq_of_mem : ∀ x y, x ∈ H → y ∈ H → μ (X ⁻¹' {x}) = μ (X ⁻¹' {y})
  measure_preimage_compl : μ (X ⁻¹' Hᶜ) = 0

/-- Uniform distributions exist. -/
lemma exists_isUniform (H : Finset S) (h : H.Nonempty) :
    ∃ (Ω : Type uS) (mΩ : MeasurableSpace Ω) (X : Ω → S) (μ : Measure Ω),
    IsProbabilityMeasure μ ∧ Measurable X ∧ IsUniform H X μ ∧ (∀ ω : Ω, X ω ∈ H) ∧ FiniteRange X := by
  refine ⟨H, Subtype.instMeasurableSpace, (fun x ↦ x),
      (Finset.card H : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac i, ?_, measurable_subtype_coe, ?_, fun x ↦ x.2, ?_⟩
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
  apply finiteRange_of_finset _ H _
  simp

/-- The image of a uniform random variable under an injective map is uniform on the image. -/
lemma IsUniform.comp [DecidableEq T] {H: Finset S} (h : IsUniform H X μ) {f : S → T} (hf : Injective f) :
    IsUniform (Finset.image f H) (f ∘ X) μ where
  eq_of_mem := by
    intro x y hx hy
    simp at hx hy
    rcases hx with ⟨x, hx, rfl⟩
    rcases hy with ⟨y, hy, rfl⟩
    have A z : f ⁻¹' {f z} = {z} := by ext; simp [hf.eq_iff]
    simp [preimage_comp, A, h.eq_of_mem x y hx hy]
  measure_preimage_compl := by simpa [preimage_comp, hf] using h.measure_preimage_compl

/-- Uniform distributions exist, version giving a measure space -/
lemma exists_isUniform_measureSpace {S : Type u}  [MeasurableSpace S]
    [MeasurableSingletonClass S] (H : Finset S) (h : H.Nonempty) :
    ∃ (Ω : Type u) (mΩ : MeasureSpace Ω) (U : Ω → S),
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧ IsUniform H U ∧ (∀ ω : Ω, U ω ∈ H) ∧ FiniteRange U := by
  rcases exists_isUniform H h with ⟨Ω, mΩ, X, μ, hμ, Xmeas, Xunif, Xmem, Xfin⟩
  exact ⟨Ω, ⟨μ⟩, X, hμ, Xmeas, Xunif, Xmem, Xfin⟩

/-- Uniform distributions exist, version with a Finite set rather than a Finset and giving a measure space -/
lemma exists_isUniform_measureSpace' {S : Type u}  [MeasurableSpace S]
    [MeasurableSingletonClass S] (H : Set S) [Finite H] [Nonempty H] :
    ∃ (Ω : Type u) (mΩ : MeasureSpace Ω) (U : Ω → S),
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧ IsUniform H U ∧ (∀ ω, U ω ∈ H) ∧ FiniteRange U := by
  set Hf := H.toFinite.toFinset
  have hHf : Hf.Nonempty := by
    rwa [<-Hf.coe_nonempty, H.toFinite.coe_toFinset, <-H.nonempty_coe_sort]
  obtain ⟨ Ω, mΩ, U, hμ, hmes, hunif, hrange, hfin ⟩ := exists_isUniform_measureSpace Hf hHf
  rw [ H.toFinite.coe_toFinset] at hunif
  replace hrange : ∀ ω, U ω ∈ H := by convert hrange with ω; simp_rw [Finite.mem_toFinset]
  exact ⟨Ω, mΩ, U, hμ, hmes, hunif, hrange, hfin⟩


/-- A uniform random variable on H almost surely takes values in H. -/
lemma IsUniform.ae_mem (h : IsUniform H X μ) : ∀ᵐ ω ∂μ, X ω ∈ H := h.measure_preimage_compl

/-- Uniform random variables only exist for non-empty sets H. -/
lemma IsUniform.nonempty {H: Finset S} (h : IsUniform H X μ) [hμ : NeZero μ] : H.Nonempty := by
  rcases Finset.eq_empty_or_nonempty H with rfl|h'
  · have : μ univ = 0 := by convert h.measure_preimage_compl; simp
    simp at this
    exact (hμ.out this).elim
  · exact h'

/-- A "unit test" for the definition of uniform distribution. -/
lemma IsUniform.measure_preimage_of_mem {H: Finset S} (h : IsUniform H X μ) (hX : Measurable X)
    {s : S} (hs : s ∈ H) :
    μ (X ⁻¹' {s}) = μ univ / Nat.card H := by
  have B : μ univ = (Nat.card H) * μ (X ⁻¹' {s}) := calc
    μ univ = μ (X ⁻¹' Hᶜ) + μ (X ⁻¹' H) := by
      rw [← measure_union (disjoint_compl_left.preimage _) (hX (measurableSet_discrete _))]
      simp
    _ = μ (X ⁻¹' H) := by rw [h.measure_preimage_compl, zero_add]
    _ = ∑ x in H, μ (X ⁻¹' {x}) := by
      have : X ⁻¹' H = ⋃ x ∈ H, X ⁻¹' ({x} : Set S) := by simp
      rw [this, measure_biUnion_finset]
      · intro y _hy z _hz hyz
        apply Disjoint.preimage
        simp [hyz]
      · intro y _hy
        exact hX (measurableSet_discrete _)
    _ = ∑ _x in H, μ (X ⁻¹' {s}) :=
      Finset.sum_congr rfl (fun x hx ↦ h.eq_of_mem x s (by simpa using hx) hs)
    _ = H.card * μ (X ⁻¹' {s}) := by simp
    _ = (Nat.card H) * μ (X ⁻¹' {s}) := by
      congr; simp
  rcases Nat.eq_zero_or_pos (Nat.card H) with hH|hH
  · simp only [hH, CharP.cast_eq_zero, zero_mul, Measure.measure_univ_eq_zero] at B
    simp [B]
  · rwa [eq_comm, ← ENNReal.eq_div_iff] at B
    · simpa using Nat.pos_iff_ne_zero.mp hH
    · simp

/-- A "unit test" for the definition of uniform distribution. -/
lemma IsUniform.measureReal_preimage_of_mem {H: Finset S} [IsProbabilityMeasure μ]
    (h : IsUniform H X μ) (hX : Measurable X) {s : S} (hs : s ∈ H) :
    μ.real (X ⁻¹' {s}) = 1 / Nat.card H := by
  rw [measureReal_def, h.measure_preimage_of_mem hX hs]
  simp [ENNReal.toReal_inv]

lemma IsUniform.measureReal_preimage_of_mem' {H: Finset S} [IsProbabilityMeasure μ]
    (h : IsUniform H X μ) (hX : Measurable X) {s : S} (hs : s ∈ H) :
    (μ.map X).real {s} = 1 / Nat.card H := by
  rw [map_measureReal_apply hX (MeasurableSet.singleton s),
    IsUniform.measureReal_preimage_of_mem h hX hs]

/-- Another "unit test" for the definition of uniform distribution. -/
lemma IsUniform.measure_preimage_of_nmem (h : IsUniform H X μ) {s : S} (hs : s ∉ H) :
    μ (X ⁻¹' {s}) = 0 := by
  apply le_antisymm ((measure_mono _).trans h.measure_preimage_compl.le) (zero_le _)
  apply preimage_mono
  simpa using hs

/-- Another "unit test" for the definition of uniform distribution. -/
lemma IsUniform.measureReal_preimage_of_nmem (h : IsUniform H X μ) {s : S} (hs : s ∉ H) :
    μ.real (X ⁻¹' {s}) = 0 := by
  rw [measureReal_def, h.measure_preimage_of_nmem hs, ENNReal.zero_toReal]

/-- $\mathbb{P}(U_H \in H') = \dfrac{|H' \cap H|}{|H|}$ -/
lemma IsUniform.measure_preimage {H : Finset S} (h : IsUniform H X μ) (hX : Measurable X)
    (H' : Set S) : μ (X ⁻¹' H') = (μ univ) * (Nat.card (H' ∩ H.toSet).Elem) / Nat.card H := calc
  _ = μ (X ⁻¹' (H' ∩ H.toSet) ∪ X ⁻¹' (H' \ H.toSet)) := by simp
  _ = μ (X ⁻¹' (H' ∩ H.toSet)) + μ (X ⁻¹' (H' \ H.toSet)) :=
    measure_union (Disjoint.preimage X disjoint_inf_sdiff) (by measurability)
  _ = μ (X ⁻¹' (H' ∩ H.toSet)) + 0 := congrArg _ <| by
    rewrite [Set.diff_eq_compl_inter, ← le_zero_iff, ← h.measure_preimage_compl]
    exact measure_mono (inter_subset_left _ _)
  _ = μ (X ⁻¹' (H' ∩ H.toSet).toFinite.toFinset) := by simp
  _ = (μ univ) * ∑ __ in (H' ∩ H.toSet).toFinite.toFinset, (1 : ENNReal) / Nat.card H := by
    rewrite [← sum_measure_preimage_singleton _ (by measurability), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun _ hx ↦ ?_)
    rw [mul_one_div, h.measure_preimage_of_mem hX ((Finite.mem_toFinset _).mp hx).2]
  _ = (μ univ) * (Nat.card (H' ∩ H.toSet).Elem) / Nat.card H := by
    rw [Finset.sum_const, Nat.card_eq_card_finite_toFinset, nsmul_eq_mul, ← mul_assoc, mul_one_div]

/-- $\mathbb{P}(U_H \in H') = \dfrac{|H' \cap H|}{|H|}$ -/
lemma IsUniform.measureReal_preimage {H : Finset S} (h : IsUniform H X μ) (hX : Measurable X)
    (H' : Set S) :
    μ.real (X ⁻¹' H') = (μ.real univ) * (Nat.card (H' ∩ H.toSet).Elem) / Nat.card H := by
  simp [measureReal_def, h.measure_preimage hX H', ENNReal.toReal_div]

lemma IsUniform.nonempty_preimage_of_mem [NeZero μ] {H: Finset S} (h : IsUniform H X μ)
    (hX : Measurable X) {s : S} (hs : s ∈ H) : Set.Nonempty (X ⁻¹' {s}) := by
  apply MeasureTheory.nonempty_of_measure_ne_zero
  rewrite [h.measure_preimage_of_mem hX hs]
  simp [NeZero.ne]

lemma IsUniform.full_measure (h : IsUniform H X μ) (hX: Measurable X) :
    (μ.map X) H = μ Set.univ := by
    rw [Measure.map_apply hX (by measurability)]
    refine measure_eq_measure_of_null_diff (subset_univ _) ?h_nulldiff
    convert h.measure_preimage_compl
    ext ω; simp

/-- A copy of a uniform random variable is also uniform.-/
lemma IsUniform.of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] (h : IsUniform H X μ)
    {X' : Ω' → S} {μ' : Measure Ω'} (h' : IdentDistrib X X' μ μ') (hH : MeasurableSet (H : Set S)) :
    IsUniform H X' μ' := by
  constructor
  · intro x y hx hy
    rw [← h'.measure_mem_eq (MeasurableSet.singleton x),
      ← h'.measure_mem_eq (MeasurableSet.singleton y)]
    apply h.eq_of_mem x y hx hy
  · rw [← h'.measure_mem_eq hH.compl]
    exact h.measure_preimage_compl

/-- $\mathbb{P}(U_H \in H') \neq 0$ if $H'$ intersects $H$ and the measure is non-zero. -/
lemma IsUniform.measure_preimage_ne_zero {H : Finset S} [NeZero μ] (h : IsUniform H X μ)
    (hX : Measurable X) (H' : Set S) [Nonempty (H' ∩ H.toSet).Elem] : μ (X ⁻¹' H') ≠ 0 := by
  simp_rw [h.measure_preimage hX H', ne_eq, ENNReal.div_eq_zero_iff, ENNReal.nat_ne_top, or_false,
    mul_eq_zero, NeZero.ne, false_or, Nat.cast_eq_zero, ← Nat.pos_iff_ne_zero, Nat.card_pos]

/-- If $X$ is uniform w.r.t. $\mu$ on $H$, then $X$ is uniform w.r.t. $\mu$ conditioned by
$H'$ on $H' \cap H$. -/
lemma IsUniform.restrict {H : Set S} (h : IsUniform H X μ) (hX : Measurable X) (H' : Set S) :
    IsUniform (H' ∩ H) X (μ[|X ⁻¹' H']) where
  eq_of_mem := fun x y hx hy ↦ by
    show _ * _ = _ * _
    rw [μ.restrict_eq_self (preimage_mono (singleton_subset_iff.mpr hx.1)),
      μ.restrict_eq_self (preimage_mono (singleton_subset_iff.mpr hy.1)), h.eq_of_mem x y hx.2 hy.2]
  measure_preimage_compl := le_zero_iff.mp <| by
    rewrite [Set.compl_inter, Set.preimage_union]
    calc
      _ ≤ (μ[|X ⁻¹' H']) (X ⁻¹' H'ᶜ) + (μ[|X ⁻¹' H']) (X ⁻¹' Hᶜ) := measure_union_le _ _
      _ = (μ[|X ⁻¹' H']) (X ⁻¹' H'ᶜ) + 0 := congrArg _ <| by
        show _ * _ = _
        rw [le_zero_iff.mp <| h.measure_preimage_compl.trans_ge <| Measure.restrict_apply_le _ _,
          mul_zero]
      _ = 0 := by
        show _ * _ + 0 = 0
        rw [add_zero, Set.preimage_compl, Measure.restrict_apply <|
          MeasurableSet.compl (measurableSet_preimage hX (measurableSet_discrete H')),
          compl_inter_self, measure_empty, mul_zero]

lemma IdentDistrib.of_isUniform {Ω' : Type*}  [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Finite H] {X: Ω → S} {X': Ω' → S} (hX: Measurable X) (hX': Measurable X') (hX_unif : IsUniform H X μ) (hX'_unif : IsUniform H X' μ') : IdentDistrib X X' μ μ' := by
  constructor
  . exact Measurable.aemeasurable hX
  . exact Measurable.aemeasurable hX'
  ext E hE
  rw [← MeasureTheory.Measure.tsum_indicator_apply_singleton _ _ hE, ← MeasureTheory.Measure.tsum_indicator_apply_singleton _ _ hE]
  congr! 4 with _ x
  rw [Measure.map_apply hX (MeasurableSet.singleton x), Measure.map_apply hX' (MeasurableSet.singleton x)]
  set Hf := H.toFinite.toFinset
  have hX_unif' : IsUniform Hf X μ := by convert hX_unif; simp
  have hX'_unif' : IsUniform Hf X' μ' := by convert hX'_unif; simp

  by_cases h : x ∈ Hf
  . rw [IsUniform.measure_preimage_of_mem hX_unif' hX h,IsUniform.measure_preimage_of_mem hX'_unif' hX' h]
    simp
  rw [IsUniform.measure_preimage_of_nmem hX_unif' h,IsUniform.measure_preimage_of_nmem hX'_unif' h]
