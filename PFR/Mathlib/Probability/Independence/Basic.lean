import Mathlib.Probability.Independence.Basic
import PFR.ForMathlib.MeasureReal
import PFR.Mathlib.MeasureTheory.Measure.MeasureSpace
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
  {n : ∀ i, MeasurableSpace (α i)}
  {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → α i}
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
lemma iIndepFun.indepFun_prod_prod (h_indep: iIndepFun n f μ) (hf: ∀ i, Measurable (f i))
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
    (hf : Measurable f) (hg : Measurable g) (hfg : IndepFun f g μ) : IndepFun (f ∘ i) (g ∘ i) (μ.comap i) := by
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
    (f : ∀ x : ι, Ω → β x) (m : ∀ x : ι, MeasurableSpace (β x))
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

/-- If a family of functions `(i, j) ↦ f i j` is independent, then the family of function tuples
`i ↦ (f i j)ⱼ` is independent. -/
lemma iIndepFun.pi
    (f_meas : ∀ i j, Measurable (f i j))
    (hf : iIndepFun (fun ij : Σ i, κ i ↦ m ij.1 ij.2) (fun ij : Σ i, κ i ↦ f ij.1 ij.2) μ) :
    iIndepFun (fun i ↦ MeasurableSpace.pi) (fun i ω ↦ (fun j ↦ f i j ω)) μ := by
  have I : ∀ i, iIndepFun (fun j ↦ m i j) (fun j ↦ f i j) μ :=
    fun i₀ ↦ hf.reindex_of_injective (Sigma.mk i₀) sigma_mk_injective
  rw [iIndepFun_iff_pi_map_eq_map] at hf ⊢; rotate_left
  · exact fun i ↦ measurable_pi_lambda _ (fun a ↦ f_meas _ _)
  · exact fun ij ↦ f_meas _ _
  symm
  calc
  μ.map (fun ω i j ↦ f i j ω)
    = (μ.map fun ω (ij : Σ i, κ i) ↦ f ij.1 ij.2 ω).map Sigma.curry := by
      rw [Measure.map_map]
      · rfl
      · exact measurable_sigmaCurry
      · exact measurable_pi_lambda _ (fun a ↦ f_meas _ _)
  _ = ((Measure.pi fun (ij : Σ i, κ i) ↦ μ.map (f ij.1 ij.2))).map Sigma.curry := by rw [← hf]
  _ = Measure.pi fun i ↦ μ.map (fun ω j ↦ f i j ω) := by
    rw [eq_comm]
    apply Measure.pi_eq_generateFrom (fun i ↦ generateFrom_pi) (fun i ↦ isPiSystem_pi)
        (fun i ↦ ?_)
    · intro s hs
      simp only [mem_image, mem_pi, mem_univ, mem_setOf_eq, forall_true_left] at hs
      choose! t ht h't using hs
      simp_rw [← h't]
      rw [Measure.map_apply measurable_sigmaCurry]; swap
      · apply MeasurableSet.univ_pi (fun i ↦ ?_)
        rw [← h't]
        exact MeasurableSet.pi countable_univ (fun i _hi ↦ ht _ _)
      have : Sigma.curry ⁻¹' Set.pi univ s = Set.pi univ (fun (ij : Σ i, κ i) ↦ t ij.1 ij.2) := by
        ext x
        simp only [mem_preimage, mem_pi, mem_univ, ← h't, forall_true_left, Sigma.forall]
        rfl
      simp only [this, pi_pi, Finset.prod_univ_prod (f := fun i j ↦ (μ.map (f i j)) (t i j))]
      congr 1 with i
      specialize I i
      rw [iIndepFun_iff_pi_map_eq_map _ _ (fun j ↦ f_meas _ _)] at I
      simp [← I]
    · refine ⟨fun _ ↦ univ, fun n ↦ ?_, ?_, ?_⟩
      · simp only [mem_image, mem_pi, mem_univ, mem_setOf_eq, forall_true_left]
        exact ⟨fun j ↦ univ, by simp⟩
      · simpa only [forall_const] using IsFiniteMeasure.measure_univ_lt_top
      · simpa using iUnion_const univ
