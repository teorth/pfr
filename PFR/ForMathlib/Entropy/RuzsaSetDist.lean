import PFR.ForMathlib.Entropy.RuzsaDist
import PFR.ForMathlib.MeasureReal
import PFR.ForMathlib.Uniform
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.ENat.Basic


section UniformMeasure

/- Here we set up the foundational theory of discrete uniform measures on finite non-empty sets. -/

open BigOperators

namespace MeasureTheory.Measure

variable {S : Type*} [MeasurableSpace S] (H : Set S)

/-- In practice one would also impose the conditions `MeasurableSingletonClass S`, `Finite H` and `Nonempty H` before attempting to use this definition. -/
noncomputable def discreteUniform : Measure S := ((Set.encard H).toENNReal)⁻¹ • (restrict count H)

lemma discreteUniform_of_infinite (h: Set.Infinite H) : discreteUniform H = 0 := by
  simp [discreteUniform, Set.Infinite.encard_eq h]

variable [MeasurableSingletonClass S] [Finite H]

lemma discreteUniform_apply (A : Set S) :
  discreteUniform H A = (Nat.card (A ∩ H : Set S)) / Nat.card H := by
    have : Fintype (A ∩ H : Set S) := Fintype.ofFinite (A ∩ H : Set S)

    rw [discreteUniform, smul_apply, restrict_apply' (Set.Finite.measurableSet H.toFinite), count_apply (Set.Finite.measurableSet (A ∩ H).toFinite), tsum_eq_sum (s := Finset.univ)]
    . simp [Finset.card_univ, ENNReal.div_eq_inv_mul, Set.Nat.card_coe_set_eq, Set.ncard_def]
      congr
      rw [<-ENat.coe_toNat (n := Set.encard H) _]
      . rfl
      simp [H.toFinite]
    simp

lemma discreteUniform_apply' (A : Set S) :
  (discreteUniform H).real A = (Nat.card (A ∩ H : Set S)) / Nat.card H := by
  rw [measureReal_def, discreteUniform_apply, ENNReal.toReal_div]
  congr

variable [Nonempty H]

instance discreteUniform.isProbabilityMeasure  : IsProbabilityMeasure (discreteUniform H) := by
  rw [isProbabilityMeasure_iff, discreteUniform_apply, Set.univ_inter, ENNReal.div_self]
  . simp [Nat.pos_iff_ne_zero.mp Nat.card_pos]
  simp

/--  injective map of discrete uniform is discrete uniform -/
lemma map_discreteUniform_of_inj {T: Type*} [MeasurableSpace T] [MeasurableSingletonClass T] {f : S → T} (hmes : Measurable f) (hf : Function.Injective f) : (discreteUniform H).map f = discreteUniform (f '' H) := by
  ext A hA
  simp_rw [map_apply hmes hA, discreteUniform_apply, Nat.card_image_of_injective hf, Set.Nat.card_coe_set_eq, <-Set.ncard_image_of_injective (f⁻¹' A ∩ H) hf]
  congr; ext t; simp
  constructor
  . rintro ⟨ s, ⟨ hs, hs' ⟩, hs'' ⟩
    exact ⟨ hs'' ▸ hs, ⟨ s, hs', hs'' ⟩ ⟩
  rintro ⟨ ht, s, ⟨ hs, hs'⟩ ⟩
  exact ⟨ s, ⟨ hs' ▸ ht, hs ⟩, hs' ⟩

lemma isUniform_iff_uniform_dist {Ω : Type uΩ} [mΩ : MeasurableSpace Ω] {μ: Measure Ω} [Countable S] (hμ: IsProbabilityMeasure μ) (U: Ω → S) (hU: Measurable U) :
  ProbabilityTheory.IsUniform H U μ ↔ μ.map U = discreteUniform H := by
  constructor
  . intro h_unif
    ext A hA
    let Hf := H.toFinite.toFinset
    have h_unif': ProbabilityTheory.IsUniform Hf U μ := (Set.Finite.coe_toFinset H.toFinite).symm ▸ h_unif
    let AHf := (A ∩ H).toFinite.toFinset

    rw [discreteUniform_apply, <-MeasureTheory.Measure.tsum_indicator_apply_singleton _ _ hA]
    classical
    calc ∑' x, Set.indicator A (fun x => (μ.map U) {x}) x
      _ = ∑' x, (if x ∈ (A ∩ H) then (1:ENNReal) / (Nat.card H) else 0) := by
        congr with x
        by_cases h : x ∈ A
        . by_cases h' : x ∈ H
          . simp [h, h', map_apply hU (MeasurableSet.singleton x), ProbabilityTheory.IsUniform.measure_preimage_of_mem h_unif' hU ((Set.Finite.coe_toFinset H.toFinite).symm ▸ h')]
          simp [h, h', map_apply hU (MeasurableSet.singleton x), ProbabilityTheory.IsUniform.measure_preimage_of_nmem h_unif' ((Set.Finite.coe_toFinset H.toFinite).symm ▸ h')]
        simp [h]
      _ = Finset.sum AHf (fun _ ↦ (1:ENNReal) / (Nat.card H)) := by
        rw [tsum_eq_sum (s := (A ∩ H).toFinite.toFinset)]
        . apply Finset.sum_congr (by rfl)
          intro x hx
          simp at hx
          simp [hx]
        intro x hx
        simp at hx
        simpa
      _ = (Nat.card (A ∩ H:Set S)) / (Nat.card H) := by
        simp [Finset.sum_const, <-Set.ncard_eq_toFinset_card (A ∩ H), Set.Nat.card_coe_set_eq]
        rfl
  intro this
  constructor
  . intro x y hx hy
    replace hx : {x} ∩ H = {x} := by simp [hx]
    replace hy : {y} ∩ H = {y} := by simp [hy]
    simp [<-map_apply hU (MeasurableSet.singleton _), this, discreteUniform_apply, hx, hy]
  rw [<-map_apply hU (by measurability), this, discreteUniform_apply]
  simp




end MeasureTheory.Measure

end UniformMeasure
