import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic
import PFR.Mathlib.Probability.Independence.Kernel

open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal

namespace ProbabilityTheory
variable {Ω ι β β' γ : Type*} {κ : ι → Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β}
  {g : Ω → β'}

lemma IndepFun.measureReal_inter_preimage_eq_mul {_mβ : MeasurableSpace β}
    {_mβ' : MeasurableSpace β'} (h : IndepFun f g μ) {s : Set β} {t : Set β'}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ.real (f ⁻¹' s ∩ g ⁻¹' t) = μ.real (f ⁻¹' s) * μ.real (g ⁻¹' t) := by
  rw [measureReal_def, h.measure_inter_preimage_eq_mul _ _ hs ht, ENNReal.toReal_mul]; rfl

end ProbabilityTheory

namespace ProbabilityTheory
variable {Ω ι β γ : Type*} {κ : ι → Type*}

section IndepFun
variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

section iIndepFun

variable {Ω ι ι' : Type*} [MeasurableSpace Ω] {α β : ι → Type*}
  [n : ∀ i, MeasurableSpace (α i)]
  [m : ∀ i, MeasurableSpace (β i)] {f : ∀ i, Ω → α i}
  {μ : Measure Ω}

variable (i : ι) [Inv (α i)] [MeasurableInv (α i)] [DecidableEq ι] in
@[to_additive]
lemma iIndepFun.inv (h : iIndepFun f μ) : iIndepFun (update f i (f i)⁻¹) μ := by
  convert h.comp (update (fun _ ↦ id) i (·⁻¹)) _ with j
  · by_cases hj : j = i
    · subst hj; ext x; simp
    · simp [hj]
  intro j
  by_cases hj : j = i
  · subst hj; simp [measurable_inv]
  · simp [hj, measurable_id]

/-- If `f` is a family of mutually independent random variables, `(S j)ⱼ` are pairwise disjoint
finite index sets, then the tuples formed by `f i` for `i ∈ S j` are mutually independent,
when seen as a family indexed by `J`. -/
lemma iIndepFun.finsets {f : ∀ i, Ω → β i} {J : Type*} [Fintype J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i)) :
    iIndepFun (fun (j : J) ↦ fun a (i : S j) ↦ f i a) μ :=
  Kernel.iIndepFun.finsets S h_disjoint hf_Indep hf_meas

/-- If `f` is a family of mutually independent random variables, `(S j)ⱼ` are pairwise disjoint
finite index sets, and `φ j` is a function that maps the tuple formed by `f i` for `i ∈ S j` to a
measurable space `γ j`, then the family of random variables formed by `φ j (f i)_{i ∈ S j}` and
indexed by `J` is iIndep. -/
lemma iIndepFun.finsets_comp {f : ∀ i, Ω → β i} {J : Type*} [Fintype J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i))
    {γ : J → Type*} {mγ : ∀ j, MeasurableSpace (γ j)}
    (φ : (j : J) → ((i : S j) → β i) → γ j) (hφ : ∀ j, Measurable (φ j)) :
    iIndepFun (fun (j : J) ↦ fun a ↦ φ j (fun (i : S j) ↦ f i a)) μ :=
  Kernel.iIndepFun.finsets_comp S h_disjoint hf_Indep hf_meas γ φ hφ

universe u
/-- A variant of iIndepFun.finsets_comp where we conclude the independence of just two functions rather than an entire family. -/
lemma iIndepFun.finsets_comp' {f : ∀ i, Ω → β i} {S S': Finset ι}  (h_disjoint : Disjoint S S')
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i))
    {γ γ': Type u} {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'}
    {φ : ((i : S) → β i) → γ} {φ' : ((i : S') → β i) → γ'} (hφ : Measurable φ) (hφ' : Measurable φ') :
    IndepFun (fun a ↦ φ (fun (i : S) ↦ f i a)) (fun a ↦ φ' (fun (i : S') ↦ f i a)) μ := by
  set S₂ := ![S,S']
  set γ₂ := ![γ,γ']
  set φ₂ : (j:Fin 2) → ((i: S₂ j) → β i) → γ₂ j :=
    fun j =>
      match j with
      | 0 => φ
      | 1 => φ'
  have h_disjoint₂ : Set.PairwiseDisjoint Set.univ S₂ := by
    simp_rw [Set.PairwiseDisjoint, Set.Pairwise, Fin.forall_fin_two, Function.onFun]
    simp [h_disjoint, h_disjoint.symm, S₂]
  set mγ₂ : (j:Fin 2) → MeasurableSpace (γ₂ j) := fun j ↦ match j with
  | 0 => mγ
  | 1 => mγ'
  have hφ₂ (j:Fin 2) : Measurable (φ₂ j) := match j with
  | 0 => hφ
  | 1 => hφ'
  have hneq : (0:Fin 2) ≠ (1:Fin 2) := by simp
  convert ProbabilityTheory.iIndepFun.indepFun (iIndepFun.finsets_comp S₂ h_disjoint₂ hf_Indep hf_meas φ₂ hφ₂) hneq

end iIndepFun

variable {Ω' α : Type*} [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]

@[simp] lemma indepFun_zero_measure {f : Ω → α} {g : Ω → β} : IndepFun f g (0 : Measure Ω) := by
  simp [IndepFun]

/-- Random variables are always independent of constants. -/
lemma indepFun_const [IsZeroOrProbabilityMeasure μ] (c : α) : IndepFun f (fun _ => c) μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rw [IndepFun_iff, MeasurableSpace.comap_const]
  intro t₁ t₂ _ ht₂
  rcases MeasurableSpace.measurableSet_bot_iff.mp ht₂ with h | h
  all_goals simp [h]

lemma indepFun_fst_snd [IsZeroOrProbabilityMeasure μ] {μ'} [IsZeroOrProbabilityMeasure μ'] :
    IndepFun (Prod.fst : Ω × Ω' → Ω) (Prod.snd : Ω × Ω' → Ω') (μ.prod μ') := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ' with rfl | hμ'
  · simp
  rw [IndepFun_iff]
  rintro _ _ ⟨s, _, rfl⟩ ⟨t, _, rfl⟩
  simp [← Set.prod_univ, ← Set.univ_prod, Set.top_eq_univ, Set.prod_inter_prod, Set.inter_univ,
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
  rw [preimage_comp, preimage_comp, ← preimage_inter, comap_apply, comap_apply, comap_apply,
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
    iIndepFun f μ ↔ ∀ (s : Finset ι) ⦃f' : ι → Set Ω⦄
      (_hf' : ∀ i, MeasurableSet[(m i).comap (f i)] (f' i)),
      μ (⋂ i ∈ s, f' i) = ∏ i ∈ s, μ (f' i) := by
  classical
  rw [iIndepFun_iff]
  refine forall_congr' fun s ↦ ⟨fun h f hf ↦ h fun i _ ↦ hf _, fun h f hf ↦ ?_⟩
  let g (i : ι) : Set Ω := if i ∈ s then f i else univ
  have (i : ι) (hi : i ∈ s) : f i = g i := (if_pos hi).symm
  convert @h g _ using 2
  · exact iInter₂_congr this
  · rw [this _ ‹_›]
  · rintro i
    by_cases hi : i ∈ s <;> simp [g, hi, hf]

end IndepFun
end ProbabilityTheory

namespace ProbabilityTheory
variable {ι Ω : Type*} {κ : ι → Type*} {α : ∀ i, κ i → Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [m : ∀ i j, MeasurableSpace (α i j)] {f : ∀ i j, Ω → α i j}

lemma measurable_sigmaCurry :
    Measurable (Sigma.curry : (∀ ij : Σ i, κ i, α ij.1 ij.2) → ∀ i j, α i j) := by
  measurability

variable [Fintype ι] [∀ i, Fintype (κ i)]


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
    (hf : iIndepFun (fun ij : Σ i, κ i ↦ f ij.1 ij.2) μ) :
    iIndepFun (fun i ω j ↦ f i j ω) μ := by
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
  simp only [mem_image, mem_pi, mem_univ, true_implies, exists_exists_and_eq_and] at hE
  have hE' (k : s) := hE k (Finset.coe_mem k)
  classical
  obtain ⟨sets, h_sets⟩ := Classical.axiomOfChoice hE'
  let sets' (i : ι) (j : κ i) : Set (α i j) := if h : i ∈ s then sets ⟨i, h⟩ j else Set.univ
  have box (i : ι) (hi : i ∈ s) : E i = ⋂ j : κ i, (f i j)⁻¹' (sets' i j) := by
    rw [← (h_sets ⟨i, hi⟩).right]
    simp_rw [sets', hi]
    ext : 1
    rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    exact ⟨fun hj j ↦ mem_preimage.mpr (hj j), fun hj j ↦ mem_preimage.mp (hj j)⟩

  let set (i : ι) (j : κ i) := f i j ⁻¹' sets' i j
  set set_σ := fun (ij : (i : ι) × κ i) ↦ set ij.fst ij.snd with set_σ_def
  let meas i j := μ (set i j)
  let meas_σ ij := μ (set_σ ij)
  suffices μ (⋂ i ∈ s, ⋂ j, set i j) = ∏ i ∈ s, μ (⋂ j, set i j) by
    convert this with k hk k hk ; all_goals { exact box k hk }

  let κ_σ (i : ι) := Finset.sigma {i} fun i ↦ Finset.univ (α := κ i)
  have reindex_prod (i : ι) : ∏ j, meas i j = ∏ ij : κ_σ i, meas_σ ij := by
    rw [Finset.prod_coe_sort, Finset.prod_sigma, Finset.prod_singleton]
  have reindex_inter (i : ι) : ⋂ j, set i j = ⋂ ij ∈ κ_σ i, set_σ ij := by
    rw [set_σ_def, Set.biInter_finsetSigma, Finset.set_biInter_singleton]
    simp
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf
  rw [Set.biInter_finsetSigma_univ', hf, Finset.prod_sigma]
  · apply Finset.prod_congr rfl
    intro i hi
    symm
    rw [reindex_prod, reindex_inter, Finset.prod_coe_sort]
    apply hf (κ_σ i) (sets := fun ij ↦ sets' ij.fst ij.snd)
    intro ij hij
    rw [← Finset.mem_singleton.mp (Finset.mem_sigma.mp hij).left] at hi
    convert (h_sets ⟨ij.fst, hi⟩).left ij.snd
    simp [sets', hi]
  intros ij hij
  obtain ⟨hi, _⟩ := Finset.mem_sigma.mp hij
  simp_rw [sets', hi]
  exact (h_sets ⟨ij.fst, hi⟩).1 ij.snd


/-- If a family of functions `(i, j) ↦ f i j` is independent, then the family of function tuples
`i ↦ (f i j)ⱼ` is independent. -/
lemma iIndepFun.pi' {f : ∀ ij : (Σ i, κ i), Ω → α ij.1 ij.2 }
    (f_meas : ∀ i, Measurable (f i))
    (hf : iIndepFun f μ) :
    iIndepFun (fun i ω ↦ (fun j ↦ f ⟨i, j⟩ ω)) μ :=
  iIndepFun.pi (fun _ _ ↦ f_meas _) hf

variable {ι ι' : Type*} {α : ι → Type*}
    {n : (i : ι) → MeasurableSpace (α i)} {f : (i : ι) → Ω → α i}

lemma iIndepFun.prod {hf : ∀ (i : ι), Measurable (f i)} {ST : ι' → Finset ι}
    (hS : Pairwise (Disjoint on ST)) (h : iIndepFun f μ) :
    let β := fun k ↦ Π i : ST k, α i
    iIndepFun (β := β) (fun (k : ι') (x : Ω) (i : ST k) ↦ f i x) μ := by
  let g : (i : ι') × ST i → ι := Subtype.val ∘' (Sigma.snd (α := ι'))
  have hg : Injective g := by
    intro x y hxy
    have : ¬(Disjoint on ST) x.fst y.fst := by
      refine not_forall.mpr ⟨{g y}, ?_⟩
      rewrite [_root_.not_imp, _root_.not_imp]
      repeat' apply And.intro
      · exact Finset.singleton_subset_iff.mpr (by rewrite [← hxy] ; exact Finset.coe_mem x.snd)
      · exact Finset.singleton_subset_iff.mpr (Finset.coe_mem y.snd)
      · rewrite [le_bot_iff] ; exact Finset.singleton_ne_empty (g y)
    exact Sigma.subtype_ext (not_ne_iff.mp ((@hS x.fst y.fst).mt this)) hxy
  let m (i : ι') (j : ST i) : MeasurableSpace (α j) := n j
  exact iIndepFun.pi' (m := m) (hf ∘' g) (h.precomp hg)

variable {β β' Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

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
  exact forall₂_congr ha

/-- TODO: a kernel version of this theorem-/
theorem iIndepFun.ae_eq {ι : Type*} {β : ι → Type*}
    {m : ∀ i, MeasurableSpace (β i)} {f g : ∀ i, Ω → β i}
    (hf_Indep : iIndepFun f μ) (hfg : ∀ i, f i =ᵐ[μ] g i) : iIndepFun g μ := by
  rw [iIndepFun_iff_iIndep, iIndep_iff] at hf_Indep ⊢
  intro s E H
  have (i : ι) : ∃ E' : Set Ω, i ∈ s → MeasurableSet[MeasurableSpace.comap (f i) (m i)] E' ∧ E' =ᵐ[μ] E i := by
    by_cases hi: i ∈ s
    · rcases H i hi with ⟨F, mF, hFE⟩
      use (f i)⁻¹' F
      simp [hi]
      constructor
      · use F
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
  · apply measure_congr
    apply EventuallyEq.finite_iInter
    intro i hi
    exact (hE''' i hi).symm
  apply Finset.prod_congr rfl
  intro i hi
  exact measure_congr (hE''' i hi).symm
