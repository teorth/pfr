import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Notation
import PFR.ForMathlib.MeasureReal
import PFR.Mathlib.MeasureTheory.MeasurableSpace.Defs
import PFR.Mathlib.SetTheory.Cardinal.Finite

open Function MeasureTheory Set
open scoped BigOperators ENNReal

namespace ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  [Fintype S] [Fintype T] [Nonempty S] [Nonempty T] [MeasurableSpace S] [MeasurableSpace T]
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

/-- The image of a uniform random variable under an injective map is uniform on the image. -/
lemma IsUniform.comp (h : IsUniform H X μ) {f : S → T} (hf : Injective f) :
    IsUniform (f '' H) (f ∘ X) μ where
  eq_of_mem := by
    rintro - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    have A z : f ⁻¹' {f z} = {z} := by ext; simp [hf.eq_iff]
    simp [preimage_comp, A, h.eq_of_mem x y hx hy]
  measure_preimage_compl := by simpa [preimage_comp, hf] using h.measure_preimage_compl

/-- Uniform distributions exist, version within a fintype and giving a measure space -/
lemma exists_isUniform_measureSpace {S : Type u} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (H : Set S) (h : H.Nonempty) :
    ∃ (Ω : Type u) (mΩ : MeasureSpace Ω) (U : Ω → S),
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧ IsUniform H U ∧ ∀ ω : Ω, U ω ∈ H := by
  let H' : Finset S := H.toFinite.toFinset
  rcases exists_isUniform H' (by simpa using h) with ⟨Ω, mΩ, X, μ, hμ, Xmeas, Xunif, Xmem⟩
  simp only [Finite.coe_toFinset, Finite.mem_toFinset] at Xunif Xmem
  exact ⟨Ω, ⟨μ⟩, X, hμ, Xmeas, Xunif, Xmem⟩

/-- A uniform random variable on H almost surely takes values in H. -/
lemma IsUniform.ae_mem (h : IsUniform H X μ) : ∀ᵐ ω ∂μ, X ω ∈ H := h.measure_preimage_compl

/-- Uniform random variables only exist for non-empty sets H. -/
lemma IsUniform.nonempty (h : IsUniform H X μ) [hμ : NeZero μ] : H.Nonempty := by
  rcases eq_empty_or_nonempty H with rfl|h'
  · have : μ univ = 0 := by convert h.measure_preimage_compl; simp
    simp at this
    exact (hμ.out this).elim
  · exact h'

/-- A "unit test" for the definition of uniform distribution. -/
lemma IsUniform.measure_preimage_of_mem (h : IsUniform H X μ) (hX : Measurable X)
    {s : S} (hs : s ∈ H) :
    μ (X ⁻¹' {s}) = μ univ / Nat.card H := by
  let H' := H.toFinite.toFinset
  have B : μ univ = (Nat.card H) * μ (X ⁻¹' {s}) := calc
    μ univ = μ (X ⁻¹' Hᶜ) + μ (X ⁻¹' H) := by
      rw [←measure_union (disjoint_compl_left.preimage _) (hX (measurableSet_discrete _))]
      simp
    _ = μ (X ⁻¹' H) := by rw [h.measure_preimage_compl, zero_add]
    _ = ∑ x in H', μ (X ⁻¹' {x}) := by
      have : X ⁻¹' H = ⋃ x ∈ H', X ⁻¹' ({x} : Set S) := by simp
      rw [this, measure_biUnion_finset]
      · intro y _hy z _hz hyz
        apply Disjoint.preimage
        simp [hyz]
      · intro y _hy
        exact hX (measurableSet_discrete _)
    _ = ∑ _x in H', μ (X ⁻¹' {s}) :=
      Finset.sum_congr rfl (fun x hx ↦ h.eq_of_mem x s (by simpa using hx) hs)
    _ = H'.card * μ (X ⁻¹' {s}) := by simp
    _ = (Nat.card H) * μ (X ⁻¹' {s}) := by
      congr; exact (Nat.card_eq_toFinset_card (toFinite H)).symm
  rcases Nat.eq_zero_or_pos (Nat.card H) with hH|hH
  · simp only [hH, CharP.cast_eq_zero, zero_mul, Measure.measure_univ_eq_zero] at B
    simp [B]
  · rwa [eq_comm, ←ENNReal.eq_div_iff] at B
    · simpa using Nat.pos_iff_ne_zero.mp hH
    · simp

/-- A "unit test" for the definition of uniform distribution. -/
lemma IsUniform.measureReal_preimage_of_mem [IsProbabilityMeasure μ]
    (h : IsUniform H X μ) (hX : Measurable X) {s : S} (hs : s ∈ H) :
    μ.real (X ⁻¹' {s}) = 1 / Nat.card H := by
  rw [measureReal_def, h.measure_preimage_of_mem hX hs]
  simp [ENNReal.toReal_inv]

lemma IsUniform.measureReal_preimage_of_mem' [IsProbabilityMeasure μ]
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

/-- A copy of a uniform random variable is also uniform.-/
lemma IsUniform.of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] (h : IsUniform H X μ)
    {X' : Ω' → S} {μ' : Measure Ω'} (h' : IdentDistrib X X' μ μ') (hH : MeasurableSet H) :
    IsUniform H X' μ' := by
  constructor
  · intro x y hx hy
    rw [←h'.measure_mem_eq (MeasurableSet.singleton x),
      ←h'.measure_mem_eq (MeasurableSet.singleton y)]
    apply h.eq_of_mem x y hx hy
  · rw [←h'.measure_mem_eq hH.compl]
    exact h.measure_preimage_compl
