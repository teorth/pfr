import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import PFR.ForMathlib.MeasureReal

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
  have h₀  {h: (i : ι) → Set (β i)} (hm : ∀ (i : ι), MeasurableSet (h i)) :
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
    set l : (i : ι) → Set (β i) := fun i ↦ if i ∈ S then s i else univ with hldef
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

variable [IsProbabilityMeasure μ]

lemma iIndepFun.indepFun_prod_prod (h_indep: iIndepFun n f μ) (hf: ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun a => (f i a, f j a)) (fun a => (f k a, f l a)) μ := by
  classical
  have hd : Disjoint ({i, j} : Finset ι) ({k,l} : Finset ι) := by
    simp only [Finset.mem_singleton, Finset.disjoint_insert_right, Finset.mem_insert,
      Finset.disjoint_singleton_right]
    tauto
  have h := h_indep.indepFun_finset ({i, j} : Finset ι) ({k,l} : Finset ι) hd hf
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), α x) : (α i) × (α j) :=
    ⟨v ⟨i, Finset.mem_insert_self i {j}⟩, v ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self j)⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by measurability
  exact h.comp (hg i j) (hg k l)

@[to_additive]
lemma iIndepFun.indepFun_mul_mul {β : Type*} {m : MeasurableSpace β} {f : ι → Ω → β} [Mul β]
    [hβ : MeasurableMul₂ β] (h_indep: iIndepFun (fun _ => m) f μ) (hf: ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i * f j) (f k * f l) μ :=
  (h_indep.indepFun_prod_prod hf i j k l hik hil hjk hjl).comp hβ.measurable_mul hβ.measurable_mul

variable {ST : ι' → Finset ι} (hS : Pairwise (Disjoint on ST)) in
lemma iIndepFun.prod (h : iIndepFun n f μ) :
    let β := fun k ↦ Π i : ST k, α i
    iIndepFun (β := β) (fun k ↦ MeasurableSpace.pi)
      (fun (k : ι') (x : Ω) (i : ST k) ↦ f i x) μ := by
  sorry

end iIndepFun


section

variable {β β' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

theorem IndepFun.measure_inter_preimage_eq_mul {_mβ : MeasurableSpace β}
    {_mβ' : MeasurableSpace β'} (h : IndepFun f g μ) {s : Set β} {t : Set β'}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) :=
  indepFun_iff_measure_inter_preimage_eq_mul.1 h _ _ hs ht

theorem IndepFun.measureReal_inter_preimage_eq_mul {_mβ : MeasurableSpace β}
    {_mβ' : MeasurableSpace β'} (h : IndepFun f g μ) {s : Set β} {t : Set β'}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ.real (f ⁻¹' s ∩ g ⁻¹' t) = μ.real (f ⁻¹' s) * μ.real (g ⁻¹' t) := by
  rw [measureReal_def, h.measure_inter_preimage_eq_mul hs ht, ENNReal.toReal_mul]; rfl

end

end ProbabilityTheory
