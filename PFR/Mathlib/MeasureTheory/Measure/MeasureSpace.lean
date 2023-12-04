import Mathlib.MeasureTheory.Measure.MeasureSpace

noncomputable section

open Function MeasurableSpace Set
open scoped Classical Topology BigOperators Filter ENNReal NNReal Interval MeasureTheory

variable {α β γ δ ι R R' : Type*}

namespace MeasureTheory
namespace Measure

-- Seems reasonable for mathlib?
-- TODO: This is currently broken.
-- It prints with dot notation on the function argument, not the measure
attribute [pp_dot] Measure.map

alias absolutelyContinuous_refl := AbsolutelyContinuous.refl
alias absolutelyContinuous_rfl := AbsolutelyContinuous.rfl

variable [MeasurableSpace α] {μ : Measure α} {c : ℝ≥0∞}

lemma smul_absolutelyContinuous : c • μ ≪ μ := absolutelyContinuous_of_le_smul le_rfl

instance instNoZeroSMulDivisors : NoZeroSMulDivisors ℝ≥0∞ (Measure α) where
  eq_zero_or_eq_zero_of_smul_eq_zero h := by simpa [Ne.def, @ext_iff', forall_or_left] using h

end Measure

variable [MeasurableSpace α] {μ : Measure α} {s t : Set α}

lemma measure_inter_conull' (ht : μ (s \ t) = 0) : μ (s ∩ t) = μ s := by
  rw [←diff_compl, measure_diff_null']; rwa [←diff_eq]

lemma measure_inter_conull (ht : μ tᶜ = 0) : μ (s ∩ t) = μ s := by
  rw [←diff_compl, measure_diff_null ht]

lemma measure_preimage_eq_zero_iff_of_countable {Ω α : Type*} [MeasurableSpace Ω]
    {H : Set α} {X : Ω → α} {μ : Measure Ω} (hs : H.Countable) :
    μ (X ⁻¹' H) = 0 ↔ ∀ x ∈ H, μ (X ⁻¹' {x}) = 0 := by
  have : Countable H := hs.to_subtype
  refine ⟨fun h x hx ↦ measure_mono_null (preimage_mono $ singleton_subset_iff.2 hx) h,
    fun h ↦ (zero_le _).antisymm' ?_⟩
  calc
    μ (X ⁻¹' H)
      = μ (⋃ x : H, X ⁻¹' {(x : α)}) := by simp
    _ ≤ ∑' x : H, μ (X ⁻¹' {(x : α)}) := measure_iUnion_le _
    _ = ∑' x : H, 0 := by congr with x; exact h x x.2
    _ = 0 := tsum_zero

/- not sure where to move this. Presumably there are some other lemmas that state
that a measure on a countable type is determined by its values on singletons?
Also simplify proof -/
open MeasureTheory in
theorem Countable.ae_of_singleton {Ω} [MeasurableSpace Ω] [Countable Ω] {μ : Measure Ω} {p : Ω → Prop}
    (h : ∀ x, μ {x} ≠ 0 → p x) : ∀ᵐ x ∂μ, p x := by
  have : {x | ¬ p x} ⊆ {x | μ {x} = 0} := by
    simp (config := {singlePass := true}) only [← not_imp_not] at h
    simpa using h
  apply measure_mono_null this
  rw [← Set.biUnion_of_singleton {x | μ {x} = 0}]
  rw [measure_biUnion_null_iff (Set.to_countable _)]
  exact fun i hi ↦ hi
