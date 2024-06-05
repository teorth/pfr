import Mathlib.Probability.Independence.Kernel

open MeasureTheory MeasurableSpace

open scoped BigOperators MeasureTheory ENNReal

namespace ProbabilityTheory.kernel
variable {β β' γ γ' : Type*} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}
  {κ : kernel α Ω} {μ : Measure α} {f : Ω → β} {g : Ω → β'}


/-- in mathlib as of `4d385393cd569f08ac30425ef886a57bb10daaa5` (TODO: bump) -/
theorem IndepFun.ae_eq' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} {f f' : Ω → β}
    {g g' : Ω → β'} (hfg : IndepFun f g κ μ) (hf : ∀ᵐ a ∂μ, f =ᵐ[κ a] f')
    (hg : ∀ᵐ a ∂μ, g =ᵐ[κ a] g') : IndepFun f' g' κ μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  filter_upwards [hf, hg, hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩] with a hf' hg' hfg'
  have h1 : f ⁻¹' A =ᵐ[κ a] f' ⁻¹' A := hf'.fun_comp A
  have h2 : g ⁻¹' B =ᵐ[κ a] g' ⁻¹' B := hg'.fun_comp B
  rwa [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]


section iIndepFun

variable {β γ : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {mγ : ∀ i, MeasurableSpace (γ i)} {f : ∀ i, Ω → β i}

lemma iIndepFun.comp (h : iIndepFun m f κ μ) (g : ∀ i, β i → γ i) (hg : ∀ i, Measurable (g i)) :
    iIndepFun mγ (fun i ↦ g i ∘ f i) κ μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  refine fun t s hs ↦ ?_
  have := h t (sets := fun i ↦ g i ⁻¹' (s i)) (fun i a ↦ hg i (hs i a))
  filter_upwards [this] with a ha
  simp_rw [Set.preimage_comp]
  exact ha

-- #check kernel.iIndepFun.indepFun_finset
-- #check iIndepFun.indepFun_finset

#check kernel.iIndepFun.comp

-- maybe `Fintype J` is not necessary?
/-- If `f` is a family of mutually independent random variables, `(S j)ⱼ` are pairwise disjoint
finite index sets, then the tuples formed by `f i` for `i ∈ S j` are mutually independent,
when seen as a family indexed by `J`. -/
lemma iIndepFun.finsets [IsMarkovKernel κ] {J : Type*} [Fintype J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun m f κ μ) (hf_meas : ∀ i, Measurable (f i)) :
    iIndepFun (fun _ ↦ pi) (fun (j : J) ↦ fun a (i : S j) ↦ f i a) κ μ := by
  sorry

/-- If `f` is a family of mutually independent random variables, `(S j)ⱼ` are pairwise disjoint
finite index sets, and `φ j` is a function that maps the tuple formed by `f i` for `i ∈ S j` to a
measurable space `γ j`, then the family of random variables formed by `φ j (f i)_{i ∈ S j}` and
indexed by `J` is iIndep. -/
lemma iIndepFun.finsets_comp [IsMarkovKernel κ] {J : Type*} [Fintype J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun m f κ μ) (hf_meas : ∀ i, Measurable (f i))
    (γ : J → Type*) {mγ : ∀ j, MeasurableSpace (γ j)}
    (φ : (j : J) → ((i : S j) → β i) → γ j) (hφ : ∀ j, Measurable (φ j)) :
    iIndepFun mγ (fun (j : J) ↦ fun a ↦ φ j (fun (i : S j) ↦ f i a)) κ μ :=
  (kernel.iIndepFun.finsets S h_disjoint hf_Indep hf_meas).comp φ hφ

end iIndepFun
