import Mathlib.Probability.IdentDistrib
import PFR.Mathlib.Probability.ConditionalProbability

-- TODO: Change `ae_snd` to assume `Measurable p`

noncomputable section

open MeasureTheory Measure Filter Set
open scoped Topology BigOperators MeasureTheory ENNReal NNReal

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

namespace ProbabilityTheory
variable {μ : Measure α} {ν : Measure β} {f f' : α → γ} {g g' : β → γ} {s : Set γ}

attribute [mk_iff] IdentDistrib

lemma identDistrib_id_left {X : α → β} (hX : AEMeasurable X μ) :
    IdentDistrib id X (μ.map X) μ where
  aemeasurable_fst := aemeasurable_id
  aemeasurable_snd := hX
  map_eq := by simp

lemma identDistrib_id_right {X : α → β} (hX : AEMeasurable X μ) : IdentDistrib X id μ (μ.map X) :=
  (identDistrib_id_left hX).symm

@[simp] lemma identDistrib_id {μ ν : Measure α} : IdentDistrib id id μ ν ↔ μ = ν := by
  simp [IdentDistrib_iff id id μ ν, aemeasurable_id]

protected lemma IdentDistrib.cond (hs : MeasurableSet s) (hf' : Measurable f') (hg' : Measurable g')
    (hfg : IdentDistrib (fun a ↦ (f a, f' a)) (fun b ↦ (g b, g' b)) μ ν) :
    IdentDistrib f g (μ[|f' ⁻¹' s]) (ν[|g' ⁻¹' s]) where
  aemeasurable_fst := (measurable_fst.aemeasurable.comp_aemeasurable hfg.aemeasurable_fst).mono_ac
    cond_absolutelyContinuous
  aemeasurable_snd := (measurable_fst.aemeasurable.comp_aemeasurable hfg.aemeasurable_snd).mono_ac
    cond_absolutelyContinuous
  map_eq := by
    ext t ht
    rw [map_apply₀ _ ht.nullMeasurableSet, map_apply₀ _ ht.nullMeasurableSet,
      cond_apply _ (hg' hs), cond_apply _ (hf' hs)]
    congr
    · simpa only [map_apply₀ (hfg.comp measurable_snd).aemeasurable_fst hs.nullMeasurableSet,
        map_apply₀ (hfg.comp measurable_snd).aemeasurable_snd hs.nullMeasurableSet]
        using congr_fun (congr_arg (⇑) (hfg.comp measurable_snd).map_eq) s
    · rw [inter_comm, inter_comm (g' ⁻¹' _)]
      simpa only [map_apply₀ hfg.aemeasurable_fst (ht.prod hs).nullMeasurableSet,
        map_apply₀ hfg.aemeasurable_snd (ht.prod hs).nullMeasurableSet]
        using congr_fun (congr_arg (⇑) hfg.map_eq) (t ×ˢ s)
    · exact (hfg.comp measurable_fst).aemeasurable_snd.mono_ac cond_absolutelyContinuous
    · exact (hfg.comp measurable_fst).aemeasurable_fst.mono_ac cond_absolutelyContinuous

end ProbabilityTheory

open MeasureTheory ProbabilityTheory Function Set BigOperators

namespace ProbabilityTheory

section IdentDistrib
variable {Ω Ω' α ι β β' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mβ : MeasurableSpace β}
  {μ : Measure Ω} {ν : Measure Ω'}
  {f g : Ω → β} {f' g' : Ω' → β}

-- todo: replace mathlib version with this lemma (this lemma uses `AEMeasurable`)
theorem indepFun_iff_map_prod_eq_prod_map_map' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f : Ω → β} {g : Ω → β'}
    [IsFiniteMeasure μ] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    IndepFun f g μ ↔ μ.map (fun ω ↦ (f ω, g ω)) = (μ.map f).prod (μ.map g) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {s : Set β} {t : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      μ (f ⁻¹' s) * μ (g ⁻¹' t) = μ.map f s * μ.map g t ∧
      μ (f ⁻¹' s ∩ g ⁻¹' t) = μ.map (fun ω ↦ (f ω, g ω)) (s ×ˢ t) :=
    ⟨by rw [Measure.map_apply_of_aemeasurable hf hs, Measure.map_apply_of_aemeasurable hg ht],
      (Measure.map_apply_of_aemeasurable (hf.prod_mk hg) (hs.prod ht)).symm⟩
  constructor
  · refine fun h ↦ (Measure.prod_eq fun s t hs ht ↦ ?_).symm
    rw [← (h₀ hs ht).1, ← (h₀ hs ht).2, h s t hs ht]
  · intro h s t hs ht
    rw [(h₀ hs ht).1, (h₀ hs ht).2, h, Measure.prod_prod]

-- todo: (Mantas) add this to mathlib & upgrade to work for `AEMeasurable` (currently lemmas missing)
theorem iIndepFun_iff_map_prod_eq_prod_map_map
    {ι : Type*} {β : ι → Type*} [Fintype ι] (f : ∀ x : ι, Ω → β x) (m: ∀ x : ι, MeasurableSpace (β x))
    [IsProbabilityMeasure μ] (hf : ∀ (x : ι), Measurable (f x)) :
    iIndepFun m f μ ↔ μ.map (fun ω i ↦ f i ω) = (Measure.pi (fun i => μ.map (f i))) := by
  classical -- might be able to get rid of this
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {h : ∀ i, Set (β i)} (hm : ∀ (i : ι), MeasurableSet (h i)) :
      ∏ i : ι, μ ((f i)⁻¹' (h i)) = ∏ i : ι, μ.map (f i) (h i) ∧
      μ (⋂ i : ι, ((f i)⁻¹' (h i))) = μ.map (fun ω i ↦ f i ω) (Set.pi univ h) := by
      constructor
      · rw [Finset.prod_congr (show Finset.univ = Finset.univ by rfl) (fun x _ => Measure.map_apply_of_aemeasurable (hf x).aemeasurable (hm x))]
      · rw [Measure.map_apply_of_aemeasurable _ (MeasurableSet.univ_pi hm)]
        · congr
          aesop
        measurability
  constructor
  · refine fun hS ↦ (Measure.pi_eq fun h hm ↦ ?_).symm
    rw [← (h₀ hm).1, ← (h₀ hm).2]
    convert hS Finset.univ (sets := h)
    simp [hm]
  · intro h S s hs
    set l : ∀ i, Set (β i) := fun i ↦ if i ∈ S then s i else univ with hldef
    have hl : (∀ (i : ι), MeasurableSet (l i)) := by
      intro i
      by_cases hiS : i ∈ S
      · simp[hldef, hiS, hs i]
      · simp[hldef, hiS]
    specialize h₀ hl
    rw [h] at h₀
    convert h₀.2 using 1
    · congr
      aesop
    · convert h₀.1 using 1
      · rw [hldef, ← Finset.prod_compl_mul_prod S]
        suffices : ∀ i ∈ Sᶜ, μ (f i ⁻¹' (fun i ↦ if i ∈ S then s i else univ) i) = 1
        · rw [Finset.prod_congr (show Sᶜ = Sᶜ by rfl) this]; aesop
        aesop
      . aesop

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem IdentDistrib.prod_mk (hff' : IdentDistrib f f' μ ν) (hgg' : IdentDistrib g g' μ ν)
    (h : IndepFun f g μ) (h' : IndepFun f' g' ν) :
    IdentDistrib (fun x ↦ (f x, g x)) (fun x ↦ (f' x, g' x)) μ ν where
  aemeasurable_fst := hff'.aemeasurable_fst.prod_mk hgg'.aemeasurable_fst
  aemeasurable_snd := hff'.aemeasurable_snd.prod_mk hgg'.aemeasurable_snd
  map_eq := by
    rw [indepFun_iff_map_prod_eq_prod_map_map' hff'.aemeasurable_fst hgg'.aemeasurable_fst] at h
    rw [indepFun_iff_map_prod_eq_prod_map_map' hff'.aemeasurable_snd hgg'.aemeasurable_snd] at h'
    rw [h, h', hff'.map_eq, hgg'.map_eq]

variable [Mul β] [MeasurableMul₂ β] [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
@[to_additive]
theorem IdentDistrib.mul
    (hff' : IdentDistrib f f' μ ν) (hgg' : IdentDistrib g g' μ ν)
    (h : IndepFun f g μ) (h' : IndepFun f' g' ν) :
    IdentDistrib (f * g) (f' * g') μ ν :=
  hff'.prod_mk hgg' h h' |>.comp_of_aemeasurable measurable_mul.aemeasurable

end IdentDistrib
end ProbabilityTheory
