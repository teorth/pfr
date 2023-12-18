import Mathlib.Probability.Independence.Basic
import PFR.ForMathlib.MeasureReal
import PFR.Mathlib.Data.Fintype.Lattice
import PFR.Mathlib.Data.Finset.Sigma
import PFR.Mathlib.Data.Fintype.Sigma
import PFR.Mathlib.Probability.Independence.Kernel

open Function MeasureTheory MeasurableSpace Measure Set
open scoped BigOperators MeasureTheory ENNReal

namespace Sigma
variable {α γ : Type*} {β : α → Type*}

/-- Nondependent eliminator for `Sigma`. -/
def elim (f : ∀ a, β a → γ) (a : Sigma β) : γ := Sigma.casesOn a f

end Sigma

namespace ProbabilityTheory
variable {Ω ι β γ : Type*} {κ : ι → Type*}

section IndepFun
variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

@[to_additive]
lemma iIndepFun.mul_left [IsProbabilityMeasure μ] {ι : Type*} {β : Type*} {m : MeasurableSpace β}
    [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β} (hf_Indep : iIndepFun (fun _ => m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) μ :=
  kernel.iIndepFun.mul_left hf_Indep hf_meas i j k hik hjk

@[to_additive]
lemma iIndepFun.mul_right [IsProbabilityMeasure μ] {ι : Type*} {β : Type*} {m : MeasurableSpace β}
    [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β} (hf_Indep : iIndepFun (fun _ => m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j * f k) μ :=
  kernel.iIndepFun.mul_right hf_Indep hf_meas i j k hij hik

section iIndepFun

variable {Ω ι ι' : Type*} [MeasurableSpace Ω] {α β : ι → Type*}
  [n : ∀ i, MeasurableSpace (α i)]
  [m : ∀ i, MeasurableSpace (β i)] {f : ∀ i, Ω → α i}
  {μ : Measure Ω}

@[nontriviality]
lemma iIndepFun.of_subsingleton [IsProbabilityMeasure μ] [Subsingleton ι] : iIndepFun n f μ := by
  simp [iIndepFun_iff]
  intro s f' hf'
  rcases Finset.eq_empty_or_nonempty s with rfl|hs
  · simp
  · rcases hs with ⟨x, hx⟩
    have : s = {x} := by ext y; simp [Subsingleton.elim y x, hx]
    simp [this]

lemma iIndepFun.isProbabilityMeasure (h : iIndepFun n f μ) : IsProbabilityMeasure μ :=
  ⟨by simpa using h.meas_biInter (S := ∅) (s := fun _ ↦ univ)⟩

lemma iIndepFun.reindex_of_injective (h : iIndepFun n f μ) (g : ι' → ι) (hg : Injective g) :
    iIndepFun (n ∘' g) (f ∘' g) μ := by
  have : IsProbabilityMeasure μ := h.isProbabilityMeasure
  nontriviality ι'
  have A : ∀ x, invFun g (g x) = x := leftInverse_invFun hg
  rw [iIndepFun_iff] at h ⊢
  intro t s' hs'
  specialize h (t.map ⟨g, hg⟩ ) (f' := fun i ↦ s' (invFun g i)) (by simpa [A ] using hs')
  simpa [A] using h

lemma iIndepFun.reindex (g : ι' ≃ ι) (h : iIndepFun (n ∘' g) (f ∘' g) μ) : iIndepFun n f μ := by
  rw [iIndepFun_iff] at h ⊢
  intro t s hs
  have : ⋂ i, ⋂ (_ : g i ∈ t), s (g i) = ⋂ i ∈ t, s i
  · ext x; simp [g.forall_congr_left']
  specialize h (t.map g.symm.toEmbedding) (f' := s ∘ g)
  simp [this, g.forall_congr_left'] at h
  apply h
  convert hs <;> simp

lemma iIndepFun.reindex_symm (g : ι' ≃ ι) (h : iIndepFun n f μ) : iIndepFun (n ∘' g) (f ∘' g) μ := by
  apply h.reindex_of_injective _ (Equiv.injective g)

lemma iIndepFun_reindex_iff (g : ι' ≃ ι) : iIndepFun (n ∘' g) (f ∘' g) μ ↔ iIndepFun n f μ :=
  ⟨fun h ↦ h.reindex g, fun h ↦ h.reindex_symm g⟩

lemma iIndepFun.comp (h : iIndepFun n f μ) (g : ∀ i, α i → β i) (hg : ∀ i, Measurable (g i)) :
    iIndepFun m (fun i ↦ g i ∘ f i) μ := by
  rw [iIndepFun_iff] at h ⊢
  refine fun t s hs ↦ h t (fun i hi ↦ ?_)
  simp_rw [measurable_iff_comap_le] at hg
  simp_rw [← MeasurableSpace.comap_comp] at hs
  exact MeasurableSpace.comap_mono (hg i) (s i) (hs i hi)

variable (i : ι) [Inv (α i)] [MeasurableInv (α i)] [DecidableEq ι] in
@[to_additive]
lemma iIndepFun.inv (h : iIndepFun n f μ) : iIndepFun n (update f i (f i)⁻¹) μ := by
  convert h.comp (update (fun _ ↦ id) i (·⁻¹)) _ with j
  · by_cases hj : j = i
    · subst hj; ext x; simp
    · simp [hj]
  intro j
  by_cases hj : j = i
  · subst hj; simp [measurable_inv]
  · simp [hj, measurable_id]

variable [IsProbabilityMeasure μ]

open Finset in
lemma iIndepFun.indepFun_prod_prod (h_indep: iIndepFun n f μ) (hf : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun a => (f i a, f j a)) (fun a => (f k a, f l a)) μ := by
  classical
  have hd : Disjoint ({i, j} : Finset ι) ({k,l} : Finset ι)
  · simp only [Finset.mem_singleton, Finset.disjoint_insert_right, Finset.mem_insert,
      Finset.disjoint_singleton_right]
    tauto
  have h := h_indep.indepFun_finset ({i, j} : Finset ι) ({k,l} : Finset ι) hd hf
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), α x) : α i × α j :=
    ⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem $ mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by measurability
  exact h.comp (hg i j) (hg k l)

@[to_additive]
lemma iIndepFun.indepFun_mul_mul {β : Type*} {m : MeasurableSpace β} {f : ι → Ω → β} [Mul β]
    [hβ : MeasurableMul₂ β] (h_indep: iIndepFun (fun _ => m) f μ) (hf: ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i * f j) (f k * f l) μ :=
  (h_indep.indepFun_prod_prod hf i j k l hik hil hjk hjl).comp hβ.measurable_mul hβ.measurable_mul

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

variable {Ω' : Type*} [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]

/-- Random variables are always independent of constants. -/
lemma indepFun_const [IsProbabilityMeasure μ] (c : α) : IndepFun f (fun _ => c) μ := by
  rw [IndepFun_iff, MeasurableSpace.comap_const]
  intro t₁ t₂ _ ht₂
  rcases MeasurableSpace.measurableSet_bot_iff.mp ht₂ with h | h
  all_goals simp [h]

lemma indepFun_fst_snd [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    IndepFun (Prod.fst : Ω × Ω' → Ω) (Prod.snd : Ω × Ω' → Ω') (μ.prod μ') := by
  rw [IndepFun_iff]
  rintro _ _ ⟨s, _, rfl⟩ ⟨t, _, rfl⟩
  simp [←Set.prod_univ, ←Set.univ_prod, Set.top_eq_univ, Set.prod_inter_prod, Set.inter_univ,
    Set.univ_inter, Measure.prod_prod, measure_univ, mul_one, one_mul]

variable {f : Ω → α} {g : Ω → β}

/-- Composing independent functions with a measurable embedding of conull range gives independent
functions. -/
lemma IndepFun.comp_right {i : Ω' → Ω} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ, a ∈ range i)
    (hf : Measurable f) (hg : Measurable g) (hfg : IndepFun f g μ) :
    IndepFun (f ∘ i) (g ∘ i) (μ.comap i) := by
  change μ (range i)ᶜ = 0 at hi'
  rw [IndepFun_iff] at hfg ⊢
  rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  rw [preimage_comp, preimage_comp, ←preimage_inter, comap_apply, comap_apply, comap_apply,
    image_preimage_eq_inter_range, image_preimage_eq_inter_range, image_preimage_eq_inter_range,
    measure_inter_conull hi', measure_inter_conull hi', measure_inter_conull hi',
    hfg _ _ ⟨_, hs, rfl⟩ ⟨_, ht, rfl⟩]
  all_goals first
  | exact hi.injective
  | exact hi.measurableSet_image'
  | exact hi.measurable $ hf hs
  | exact hi.measurable $ hg ht
  | exact hi.measurable $ (hf hs).inter $ hg ht

-- Same as `iIndepFun_iff` except that the function `f'` returns measurable sets even on junk values
lemma iIndepFun_iff' [MeasurableSpace Ω] {β : ι → Type*}
    (m : ∀ i, MeasurableSpace (β i)) (f : ∀ i, Ω → β i) (μ : Measure Ω) :
    iIndepFun m f μ ↔ ∀ (s : Finset ι) ⦃f' : ι → Set Ω⦄
      (_hf' : ∀ i, MeasurableSet[(m i).comap (f i)] (f' i)),
      μ (⋂ i ∈ s, f' i) = ∏ i in s, μ (f' i) := by
  classical
  rw [iIndepFun_iff]
  refine forall_congr' fun s ↦ ⟨fun h f hf ↦ h fun i _ ↦ hf _, fun h f hf ↦ ?_⟩
  let g (i : ι) : Set Ω := if i ∈ s then f i else univ
  have (i : ι) (hi : i ∈ s) : f i = g i := (if_pos hi).symm
  convert @h g _ using 2
  · exact iInter₂_congr this
  · rw [this _ ‹_›]
  · rintro i
    by_cases hi : i ∈ s <;> simp [hi, hf]

-- TODO: Replace mathlib version with this lemma (this lemma uses `AEMeasurable`)
theorem indepFun_iff_map_prod_eq_prod_map_map' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f : Ω → β} {g : Ω → β'} [IsFiniteMeasure μ] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
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

-- TODO(Mantas): Add this to mathlib & upgrade to work for `AEMeasurable` (currently lemmas missing)
theorem iIndepFun_iff_pi_map_eq_map {ι : Type*} {β : ι → Type*} [Fintype ι]
    (f : ∀ x : ι, Ω → β x) [m : ∀ x : ι, MeasurableSpace (β x)]
    [IsProbabilityMeasure μ] (hf : ∀ (x : ι), Measurable (f x)) :
    iIndepFun m f μ ↔ Measure.pi (fun i ↦ μ.map (f i)) = μ.map (fun ω i ↦ f i ω) := by
  classical -- might be able to get rid of this
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {h : ∀ i, Set (β i)} (hm : ∀ (i : ι), MeasurableSet (h i)) :
      ∏ i : ι, μ (f i ⁻¹' h i) = ∏ i : ι, μ.map (f i) (h i) ∧
      μ (⋂ i : ι, (f i ⁻¹' h i)) = μ.map (fun ω i ↦ f i ω) (Set.pi univ h)
  · constructor
    · rw [Finset.prod_congr (show Finset.univ = Finset.univ by rfl)
      (fun x _ => Measure.map_apply_of_aemeasurable (hf x).aemeasurable (hm x))]
    rw [Measure.map_apply_of_aemeasurable _ (MeasurableSet.univ_pi hm)]
    · congr
      aesop
    measurability
  refine ⟨fun hS ↦ Measure.pi_eq fun h hm ↦ ?_, fun h S s hs ↦ ?_⟩
  · rw [← (h₀ hm).1, ← (h₀ hm).2]
    convert hS Finset.univ (sets := h)
    simp [hm]
  set l : ∀ i, Set (β i) := fun i ↦ if i ∈ S then s i else univ with hldef
  have hl (i : ι) : MeasurableSet (l i) := by by_cases hiS : i ∈ S <;> simp [hldef, hiS, hs]
  specialize h₀ hl
  rw [←h] at h₀
  convert h₀.2 using 1
  · congr with x
    simp (config := { contextual := true })
  convert h₀.1 using 1
  · rw [hldef, ← Finset.prod_compl_mul_prod S]
    suffices : ∀ i ∈ Sᶜ, μ (f i ⁻¹' (fun i ↦ if i ∈ S then s i else univ) i) = 1
    · rw [Finset.prod_congr (show Sᶜ = Sᶜ by rfl) this]; aesop
    aesop
  . simp

end IndepFun
end ProbabilityTheory

namespace ProbabilityTheory
variable {ι Ω : Type*} {κ : ι → Type*} {α : ∀ i, κ i → Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [m : ∀ i j, MeasurableSpace (α i j)] {f : ∀ i j, Ω → α i j}
  [Fintype ι] [∀ i, Fintype (κ i)]

lemma measurable_sigmaCurry :
    Measurable (Sigma.curry : (∀ ij : Σ i, κ i, α ij.1 ij.2) → ∀ i j, α i j) := by
  measurability

@[to_additive]
lemma _root_.Finset.prod_univ_prod {β : Type*} [CommMonoid β] (f : ∀ i, κ i → β) :
    (∏ ij : (i : ι) × κ i, f ij.1 ij.2) = (∏ i : ι, ∏ j : κ i, f i j) := by
  rw [← Finset.univ_sigma_univ, Finset.prod_sigma]

@[to_additive]
lemma _root_.Finset.prod_univ_prod' {β : Type*} [CommMonoid β] (f : ((i : ι) × κ i) → β) :
    (∏ ij : (i : ι) × κ i, f ij) = (∏ i : ι, ∏ j : κ i, f ⟨i, j⟩) := by
  rw [← Finset.univ_sigma_univ, Finset.prod_sigma]

variable {ι : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]
  {α : ∀ i, κ i → Type*} {f : ∀ i j, Ω → α i j} [m : ∀ i j, MeasurableSpace (α i j)]

/-- If a family of functions `(i, j) ↦ f i j` is independent, then the family of function tuples
`i ↦ (f i j)ⱼ` is independent. -/
lemma iIndepFun.pi
    (f_meas : ∀ i j, Measurable (f i j))
    (hf : iIndepFun (fun ij : Σ i, κ i ↦ m ij.1 ij.2) (fun ij : Σ i, κ i ↦ f ij.1 ij.2) μ) :
    iIndepFun (fun i ↦ MeasurableSpace.pi) (fun i ω ↦ (fun j ↦ f i j ω)) μ := by
  let F i ω j := f i j ω
  let M (i : ι):= MeasurableSpace.pi (m := m i)
  let πβ (i : ι) := Set.pi Set.univ '' Set.pi Set.univ fun j => { s | MeasurableSet[m i j] s }
  apply iIndepSets.iIndep
  · exact fun i ↦ measurable_iff_comap_le.mp (measurable_pi_iff.mpr (f_meas i))
  · exact fun i ↦ IsPiSystem.comap isPiSystem_pi (F i)
  · intro k
    show MeasurableSpace.comap _ (M k) = _
    have : M k = MeasurableSpace.generateFrom (πβ k) := generateFrom_pi.symm
    rewrite [this, MeasurableSpace.comap_generateFrom] ; rfl

  rw [iIndepSets_iff]
  intro s E hE
  simp? at hE
    says simp only [mem_image, mem_pi, mem_univ, mem_setOf_eq, forall_true_left,
      exists_exists_and_eq_and] at hE
  have hE' (k : s) := hE k (Finset.coe_mem k)
  classical
  obtain ⟨sets, h_sets⟩ := Classical.axiomOfChoice hE'
  let sets' (i : ι) (j : κ i) : Set (α i j) := if h : i ∈ s then sets ⟨i, h⟩ j else Set.univ
  have box (i : ι) (hi : i ∈ s) : E i = ⋂ j : κ i, (f i j)⁻¹' (sets' i j) := by
    rw [← (h_sets ⟨i, hi⟩).right]
    simp_rw [hi]
    ext : 1
    rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    exact ⟨fun hj j ↦ mem_preimage.mpr (hj j), fun hj j ↦ mem_preimage.mp (hj j)⟩

  let set (i : ι) (j : κ i) := f i j ⁻¹' sets' i j
  set set_σ := fun (ij : (i : ι) × κ i) ↦ set ij.fst ij.snd with set_σ_def
  let meas i j := μ (set i j)
  let meas_σ ij := μ (set_σ ij)
  suffices : μ (⋂ i ∈ s, ⋂ j : κ i, set i j) = ∏ i in s, μ (⋂ j : κ i, set i j)
  · convert this with k hk k hk ; all_goals { exact box k hk }

  let κ_σ (i : ι) := Finset.sigma {i} fun i ↦ Finset.univ (α := κ i)
  have reindex_prod (i : ι) : ∏ j : κ i, meas i j = ∏ ij : κ_σ i, meas_σ ij := by
    rw [Finset.prod_coe_sort, Finset.prod_sigma, Finset.prod_singleton]
  have reindex_inter (i : ι) : ⋂ j : κ i, set i j = ⋂ ij : κ_σ i, set_σ ij := by
    rw [iInter_subtype, set_σ_def, ← Finset.iInter_sigma, Finset.set_biInter_singleton]
    exact Finset.set_biInter_univ

  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf
  rw [Fintype.iInter_sigma, hf, Finset.prod_sigma]
  · apply Finset.prod_congr rfl
    intro i hi
    symm
    rw [reindex_prod, reindex_inter, Finset.prod_coe_sort, iInter_subtype]
    apply hf (κ_σ i) (sets := fun ij ↦ sets' ij.fst ij.snd)
    intro ij hij
    rw [← Finset.mem_singleton.mp (Finset.mem_sigma.mp hij).left] at hi
    convert (h_sets ⟨ij.fst, hi⟩).left ij.snd
    simp? [hi] says simp only [hi, dite_true]
  intros ij hij
  obtain ⟨hi, _⟩ := Finset.mem_sigma.mp hij
  simp_rw [hi]
  exact (h_sets ⟨ij.fst, hi⟩).1 ij.snd


/-- If a family of functions `(i, j) ↦ f i j` is independent, then the family of function tuples
`i ↦ (f i j)ⱼ` is independent. -/
lemma iIndepFun.pi' {f : ∀ ij : (Σ i, κ i), Ω → α ij.1 ij.2 }
    (f_meas : ∀ i, Measurable (f i))
    (hf : iIndepFun (fun ij : Σ i, κ i ↦ m ij.1 ij.2) f μ) :
    iIndepFun (fun _i ↦ MeasurableSpace.pi) (fun i ω ↦ (fun j ↦ f ⟨i, j⟩ ω)) μ :=
  iIndepFun.pi (fun _ _ ↦ f_meas _) hf

variable {ι ι' : Type*} {α : ι → Type*}
    {n : (i : ι) → MeasurableSpace (α i)} {f : (i : ι) → Ω → α i}
    {hf : ∀ (i : ι), Measurable (f i)} {ST : ι' → Finset ι} (hS : Pairwise (Disjoint on ST))
lemma iIndepFun.prod (h : iIndepFun n f μ) :
    let β := fun k ↦ Π i : ST k, α i
    iIndepFun (β := β) (fun k ↦ MeasurableSpace.pi) (fun (k : ι') (x : Ω) (i : ST k) ↦ f i x) μ := by
  let g : (i : ι') × ST i → ι := Subtype.val ∘' (Sigma.snd (α := ι'))
  have hg : Injective g := by
    intro x y hxy
    have : ¬(Disjoint on ST) x.fst y.fst := by
      refine not_forall.mpr ⟨{g y}, ?_⟩
      rewrite [not_imp, not_imp]
      repeat' apply And.intro
      · exact Finset.singleton_subset_iff.mpr (by rewrite [← hxy] ; exact Finset.coe_mem x.snd)
      · exact Finset.singleton_subset_iff.mpr (Finset.coe_mem y.snd)
      · rewrite [le_bot_iff] ; exact Finset.singleton_ne_empty (g y)
    exact Sigma.subtype_ext (not_ne_iff.mp ((@hS x.fst y.fst).mt this)) hxy
  let m (i : ι') (j : ST i) : MeasurableSpace (α j) := n j
  exact iIndepFun.pi' (m := m) (hf ∘' g) (h.reindex_of_injective g hg)


variable {β β' Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Improved version of `IndepFun.ae_eq` in which the ranges are allowed to be distinct.
TODO: replace `IndepFun.ae_eq` with this one. -/
theorem IndepFun.ae_eq' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} {f f' : Ω → β}
    {g g' : Ω → β'} (hfg : IndepFun f g μ)
    (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') : IndepFun f' g' μ := by
  refine kernel.IndepFun.ae_eq' hfg ?_ ?_ <;>
    simp only [ae_dirac_eq, Filter.eventually_pure, kernel.const_apply]
  exacts [hf, hg]

/-- Improved version of `kernel.IndepFun.symm` in which the ranges are allowed to be distinct.
TODO: replace `kernel.IndepFun.symm` with this one. -/
theorem kernel.IndepFun.symm' {Ω α β γ : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace α}
    {_ : MeasurableSpace β} {_ : MeasurableSpace γ} {κ : kernel α Ω} {f : Ω → β} {g : Ω → γ}
    {μ : Measure α}
    (hfg : kernel.IndepFun f g κ μ) : kernel.IndepFun g f κ μ :=
  kernel.Indep.symm hfg

/-- Improved version of `IndepFun.symm` in which the ranges are allowed to be distinct.
TODO: replace `IndepFun.symm` with this one. -/
theorem IndepFun.symm' {γ β Ω : Type*} {_ : MeasurableSpace γ}
    {_ : MeasurableSpace β} {_ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → γ}
    (hfg : IndepFun f g μ) :
    IndepFun g f μ := kernel.IndepFun.symm' hfg

/-- The new Mathlib tool `Finset.eventuallyEq_iInter` will supersede this result. -/
theorem EventuallyEq.finite_iInter {ι : Type*} {α : Type u_2} {l : Filter α} (s: Finset ι)
    {E : ι → Set α} {F : ι → Set α}
    (h : ∀ i ∈ s, E i =ᶠ[l] F i) :
    ⋂ i ∈ s, E i =ᶠ[l] ⋂ i ∈ s, F i := by
  unfold Filter.EventuallyEq Filter.Eventually at h ⊢
  simp at h ⊢
  rw [← Filter.biInter_finset_mem] at h
  apply Filter.mem_of_superset h
  intro a ha
  simp at ha ⊢
  change a ∈ ⋂ i ∈ s, E i ↔ a ∈ ⋂ i ∈ s, F i
  simp
  change ∀ i ∈ s, a ∈ E i ↔ a ∈ F i at ha
  exact ball_congr ha

/-- TODO: a kernel version of this theorem-/
theorem iIndepFun.ae_eq {ι : Type*} {β : ι → Type*}
    {m : ∀ i, MeasurableSpace (β i)} {f g : ∀ i, Ω → β i}
    (hf_Indep : iIndepFun m f μ) (hfg : ∀ i, f i =ᵐ[μ] g i) : iIndepFun m g μ := by
  rw [iIndepFun_iff_iIndep, iIndep_iff] at hf_Indep ⊢
  intro s E H
  have (i : ι) : ∃ E' : Set Ω, i ∈ s → MeasurableSet[MeasurableSpace.comap (f i) (m i)] E' ∧ E' =ᵐ[μ] E i := by
    by_cases hi: i ∈ s
    . rcases H i hi with ⟨F, mF, hFE⟩
      use (f i)⁻¹' F
      simp [hi]
      constructor
      . use F
      rw [← hFE]
      exact Filter.EventuallyEq.preimage (hfg i) F
    use ∅
    tauto
  classical
  rcases Classical.axiomOfChoice this with ⟨E', hE'⟩
  have hE'' : ∀ i ∈ s, MeasurableSet[MeasurableSpace.comap (f i) (m i)] (E' i) := by
    intro i hi; exact (hE' i hi).1
  have hE''' : ∀ i ∈ s, E' i =ᵐ[μ] E i := by
    intro i hi; exact (hE' i hi).2
  convert hf_Indep s hE'' using 1 with i
  . apply measure_congr
    apply EventuallyEq.finite_iInter
    intro i hi
    exact (hE''' i hi).symm
  apply Finset.prod_congr rfl
  intro i hi
  exact measure_congr (hE''' i hi).symm
