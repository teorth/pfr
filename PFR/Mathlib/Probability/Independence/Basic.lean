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

variable (g : ι' ≃ ι)
lemma iIndepFun.reindex (h : iIndepFun (n ∘' g) (f ∘' g) μ) : iIndepFun n f μ := by
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
  [IsProbabilityMeasure μ] {m : ∀ i j, MeasurableSpace (α i j)} {f : ∀ i j, Ω → α i j}
  [Fintype ι] [∀ i, Fintype (κ i)]

-- Below, two approaches

/-- If a family of functions `i j ↦ f i j` is independent, then the family of functions
`i ↦ ∀ j, f i j` is independent. -/
lemma iIndepFun.pi
    (hf : iIndepFun (fun ij : Σ i, κ i ↦ m ij.1 ij.2) (fun ij : Σ i, κ i ↦ f ij.1 ij.2) μ) :
    iIndepFun (fun i ↦ MeasurableSpace.pi) (fun i ω j ↦ f i j ω) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  rintro s t ht
  -- Here, we want to WLOG reduce to the case where the `t i` are boxes of the form
  -- `Set.univ.pi (fun j : κ i → (u i j : Set (α i j)))`
  sorry

lemma measurable_sigmaCurry :
    Measurable (Sigma.curry : (∀ ij : Σ i, κ i, α ij.1 ij.2) → ∀ i j, α i j) := sorry

lemma measurable_sigmaUncurry :
    Measurable (Sigma.uncurry : (∀ i j, α i j) → (∀ ij : Σ i, κ i, α ij.1 ij.2)) := sorry

/-- If a family of functions `i j ↦ f i j` is independent, then the family of functions
`i ↦ ∀ j, f i j` is independent. -/
lemma iIndepFun.pi'
    (hf : iIndepFun (fun ij : Σ i, κ i ↦ m ij.1 ij.2) (fun ij : Σ i, κ i ↦ f ij.1 ij.2) μ) :
    iIndepFun (fun i ↦ MeasurableSpace.pi) (fun i ω j ↦ f i j ω) μ := by
  rw [iIndepFun_iff_pi_map_eq_map] at hf ⊢
  symm
  calc
    μ.map (fun ω i j ↦ f i j ω)
      = (μ.map fun ω (ij : Σ i, κ i) ↦ f ij.1 ij.2 ω).map Sigma.curry := by
        rw [Measure.map_map]; rfl
        exact measurable_sigmaCurry
        sorry
    _ = _ := by rw [←hf]
    _ = _ := ?_
  sorry
  sorry
  sorry


-- The following lemma has a completely inefficient proof; should be done better

lemma exists_indexfn {ι ι': Type*} [hι': Nonempty ι'] {ST : ι' → Finset ι} (hS : Pairwise (Disjoint on ST)) : ∃ K : ι → ι', ∀ k : ι', ∀ i ∈ ST k, K i = k := by
  classical
  let inv (i : ι) : Set ι' := { k | i ∈ ST k }
  let K := fun i => if h : Set.Nonempty (inv i) then   (Classical.choice (Set.Nonempty.to_subtype h)).1 else Classical.choice hι'
  use K
  intro k i hi
  have : Set.Nonempty (inv i) :=  nonempty_of_mem hi
  simp [this]
  set k' := (Classical.choice (Set.Nonempty.to_subtype this)).1
  have : k' ∈ inv i := by
    exact Subtype.mem (Classical.choice (Nonempty.to_subtype this))
  have : i ∈ ST k' := by
    simp at this; assumption
  apply Pairwise.eq hS
  unfold Disjoint; simp
  use {i}
  simp [this, hi]

variable {ι ι' : Type*} {α : ι → Type*} [hι': Nonempty ι']
  {n : (i : ι) → MeasurableSpace (α i)} {f : (i : ι) → Ω → α i} {hf : (i : ι) → Measurable (f i)}  {ST : ι' → Finset ι} (hS : Pairwise (Disjoint on ST)) in
lemma iIndepFun.prod (h : iIndepFun n f μ) :
    let β := fun k ↦ Π i : ST k, α i
    iIndepFun (β := β) (fun k ↦ MeasurableSpace.pi)
      (fun (k : ι') (x : Ω) (i : ST k) ↦ f i x) μ := by
      set F := fun (k : ι') (x : Ω) (i : ST k) ↦ f i x
      set M := fun (k : ι') ↦ MeasurableSpace.pi (m := fun (i: ST k) ↦ n i)
      rw [iIndepFun_iff_iIndep]
      let πβ (k : ι') := Set.pi (Set.univ : Set (ST k)) ''
    Set.pi (Set.univ : Set (ST k)) fun i => { s : Set (α i) | MeasurableSet[n i] s }
      let π (k : ι') : Set (Set Ω) := { s : Set Ω | ∃ t ∈ (πβ k), (fun a (i : (ST k)) => f i a) ⁻¹' t = s }
      apply iIndepSets.iIndep (π := π)
      . intro k
        rw [<-measurable_iff_comap_le, measurable_pi_iff]
        intro i
        exact hf i
      . intro k
        apply IsPiSystem.comap
        apply isPiSystem_pi
      . intro k
        have : M k = MeasurableSpace.generateFrom (πβ k) :=  generateFrom_pi.symm
        rw [this, MeasurableSpace.comap_generateFrom]
        congr
      rw [iIndepSets_iff]
      intro s E hE
      simp at hE
      have hE' (k : s) := hE k (Finset.coe_mem k)
      classical
      obtain ⟨ sets, h_sets ⟩ := Classical.axiomOfChoice hE'
      rcases exists_indexfn hS with ⟨ K, hK ⟩
      let sets' (k : ι') (i : ι) : Set (α i) := if h : k ∈ s then (if h' : i ∈ ST k then sets ⟨k, h⟩ ⟨i, h'⟩ else Set.univ) else Set.univ
      let sets'' (i : ι) : Set (α i) := sets' (K i) i
      have box (k : ι') (hk : k ∈ s) : E k = ⋂ i ∈ ST k, (f i)⁻¹' (sets'' i) := by
        rw [<-(h_sets ⟨ k, hk ⟩).2]
        simp [hk]
        ext1 ω
        simp_rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
        constructor <;> intro h
        · intro i hi; rw [hK k i hi]; simp [hi, hk]; exact h ⟨ i, hi ⟩
        · intro i; have := h i; rw [hK k i.1 i.2] at this; simp [hk] at this; exact this
      suffices : μ (⋂ k ∈ s, ⋂ i ∈ ST k, (f i)⁻¹' (sets'' i) ) = ∏ k in s, μ (⋂ i ∈ ST k, (f i)⁻¹' (sets'' i))
      . convert this with k hk k hk
        all_goals {
          exact box k hk
        }
      rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h
      have hS' : PairwiseDisjoint s ST := by
        intro k _ k' _ hkk'
        exact hS hkk'
      set A : Finset ι := Finset.disjiUnion s ST hS'
      have big_inter : ⋂ k ∈ s, ⋂ i ∈ ST k, (f i)⁻¹' (sets'' i) = ⋂ i ∈ A, (f i)⁻¹' (sets'' i) := by
        simp
      rw [big_inter, h A _, Finset.prod_disjiUnion]
      . apply Finset.prod_congr rfl
        intro k hk
        symm
        apply h (ST k)
        intro i hi
        have := (h_sets ⟨k, hk⟩).1 i hi
        convert this
        simp
        rw [hK k i hi]
        simp [hi, hk]
      intro i hi
      simp at hi
      rcases hi with ⟨ k, hk, hik ⟩
      simp
      rw [hK k i hik]
      simp [hk, hik]
      exact (h_sets ⟨ k, hk ⟩).1 i hik
