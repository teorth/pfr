import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Function Set

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


variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem IdentDistrib.prod_mk
    (hff' : IdentDistrib f f' μ ν) (hgg' : IdentDistrib g g' μ ν)
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

section iIndepFun

variable {Ω ι ι' : Type*} [MeasurableSpace Ω] {α β : ι → Type*}
  {n : (i : ι) → MeasurableSpace (α i)}
  {m : (i : ι) → MeasurableSpace (β i)} {f : (i : ι) → Ω → α i}
  {μ : Measure Ω}

variable (g : ι' ≃ ι)
lemma iIndepFun.reindex (h : iIndepFun (n ∘' g) (f ∘' g) μ) :
    iIndepFun n f μ := by
  rw [iIndepFun_iff] at h ⊢
  intro t s hs
  have : ⋂ i, ⋂ (_ : g i ∈ t), s (g i) = ⋂ i ∈ t, s i
  · ext x; simp [g.forall_congr_left']
  specialize h (t.map g.symm.toEmbedding) (f' := s ∘ g)
  simp [this, g.forall_congr_left'] at h
  apply h
  convert hs <;> simp

lemma iIndepFun.comp (h : iIndepFun n f μ) (g : (i : ι) → α i → β i) (hg : ∀ i, Measurable (g i)) :
    iIndepFun m (fun i ↦ g i ∘ f i) μ := by
  rw [iIndepFun_iff] at h ⊢
  refine fun t s hs ↦ h t (fun i hi ↦ ?_)
  simp_rw [measurable_iff_comap_le] at hg
  simp_rw [← MeasurableSpace.comap_comp] at hs
  exact MeasurableSpace.comap_mono (hg i) (s i) (hs i hi)

variable (i : ι) [Neg (α i)] [MeasurableNeg (α i)] [DecidableEq ι] in
lemma iIndepFun.neg (h : iIndepFun n f μ) : iIndepFun n (update f i (-f i)) μ := by
  convert h.comp (update (fun _ ↦ id) i (-·)) _ with j
  · by_cases hj : j = i
    · subst hj; ext x; simp
    · simp [hj]
  intro j
  by_cases hj : j = i
  · subst hj; simp [measurable_neg]
  · simp [hj, measurable_id]

end iIndepFun

end ProbabilityTheory
