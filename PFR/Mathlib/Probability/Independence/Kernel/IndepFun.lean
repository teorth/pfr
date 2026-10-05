module

public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Probability.Independence.Kernel.IndepFun

import Mathlib.MeasureTheory.MeasurableSpace.Pi

public section

open MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory.Kernel
variable {ι α β β' γ γ' Ω : Type*} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}
  {κ : Kernel α Ω} {μ : Measure α} {f : Ω → β} {g : Ω → β'}

section iIndepFun

variable {β γ : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {mγ : ∀ i, MeasurableSpace (γ i)}
  {f : ∀ i, Ω → β i}

/-- Tuples with pairwise disjoint coordinate ranges are independent.
The coordinate types may be infinite, and coordinates may repeat within a block. -/
lemma iIndepFun.blocks {J : Type*} {K : J → Type*}
    (S : ∀ j, K j → ι)
    (hS : Pairwise fun j j' ↦ Disjoint (Set.range (S j)) (Set.range (S j')))
    (hf : iIndepFun f κ μ) (hmeas : ∀ i, Measurable (f i)) :
    iIndepFun (fun j a k ↦ f (S j k) a) κ μ := by
  classical
  let M (j : J) : MeasurableSpace Ω := ⨆ i ∈ Set.range (S j), (m i).comap (f i)
  have hM : iIndep M κ μ := by
    intro t E
    induction t using Finset.induction_on with
    | empty =>
      intro _
      filter_upwards [hf.ae_isProbabilityMeasure] with a ha
      let := ha
      simp
    | @insert j t hj ih =>
      intro hE
      have ht : ∀ k ∈ t, MeasurableSet[M k] (E k) :=
        fun k hk ↦ hE k (Finset.mem_insert_of_mem hk)
      let B : Set ι := ⋃ k ∈ t, Set.range (S k)
      have hdis : Disjoint (Set.range (S j)) B := by
        apply Set.disjoint_left.mpr
        intro i hi hiB
        simp only [B, Set.mem_iUnion] at hiB
        obtain ⟨k, hk, hik⟩ := hiB
        exact Set.disjoint_left.mp (hS (by intro h; subst k; exact hj hk)) hi hik
      have hle (k : J) (hk : k ∈ t) : M k ≤ ⨆ i ∈ B, (m i).comap (f i) := by
        refine iSup₂_le fun i hi ↦ le_iSup_of_le i (le_iSup_of_le ?_ le_rfl)
        exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, hi⟩⟩
      have h_indep := indep_iSup_of_disjoint (fun i ↦ (hmeas i).comap_le) hf.iIndep hdis
      have h_inter := h_indep (E j) (⋂ k ∈ t, E k)
        (hE j (Finset.mem_insert_self j t))
        (t.measurableSet_biInter fun k hk ↦ hle k hk _ (ht k hk))
      filter_upwards [ih ht, h_inter] with a ha h_inter_a
      rw [Finset.set_biInter_insert, Finset.prod_insert hj, h_inter_a, ha]
  change iIndep (fun j ↦ MeasurableSpace.pi.comap (fun a k ↦ f (S j k) a)) κ μ
  simpa only [M, iSup_range, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def] using hM

/-- If `f` is a family of mutually independent random variables, `(S j)ⱼ` are pairwise disjoint
finite index sets, then the tuples formed by `f i` for `i ∈ S j` are mutually independent,
when seen as a family indexed by `J`. -/
lemma iIndepFun.finsets {J : Type*}
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i)) :
    iIndepFun (fun (j : J) ↦ fun a (i : S j) ↦ f i a) κ μ := by
  apply hf_Indep.blocks (fun j (i : S j) ↦ (i : ι)) ?_ hf_meas
  intro j j' hjj'
  apply Set.disjoint_left.mpr
  rintro _ ⟨a, rfl⟩ ⟨b, hab⟩
  exact Finset.disjoint_left.mp
    (h_disjoint (Set.mem_univ j) (Set.mem_univ j') hjj') a.property
    (by simpa only [show (b : ι) = (a : ι) from hab] using b.property)

/-- If `f` is a family of mutually independent random variables, `(S j)ⱼ` are pairwise disjoint
finite index sets, and `φ j` is a function that maps the tuple formed by `f i` for `i ∈ S j` to a
measurable space `γ j`, then the family of random variables formed by `φ j (f i)_{i ∈ S j}` and
indexed by `J` is iIndep. -/
lemma iIndepFun.finsets_comp {J : Type*}
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i))
    (γ : J → Type*) {mγ : ∀ j, MeasurableSpace (γ j)}
    (φ : (j : J) → ((i : S j) → β i) → γ j) (hφ : ∀ j, Measurable (φ j)) :
    iIndepFun (fun (j : J) ↦ fun a ↦ φ j (fun (i : S j) ↦ f i a)) κ μ :=
  (Kernel.iIndepFun.finsets S h_disjoint hf_Indep hf_meas).comp φ hφ

/-- Measurable functions of disjoint blocks, indexed by arbitrary dependent types,
form an independent family. -/
lemma iIndepFun.blocks_comp {J : Type*} {K : J → Type*}
    (S : ∀ j, K j → ι)
    (hS : Pairwise fun j j' ↦ Disjoint (Set.range (S j)) (Set.range (S j')))
    (hf : iIndepFun f κ μ) (hmeas : ∀ i, Measurable (f i))
    {γ : J → Type*} {mγ : ∀ j, MeasurableSpace (γ j)}
    (φ : (j : J) → ((k : K j) → β (S j k)) → γ j) (hφ : ∀ j, Measurable (φ j)) :
    iIndepFun (fun j a ↦ φ j (fun k ↦ f (S j k) a)) κ μ :=
  (hf.blocks S hS hmeas).comp φ hφ

end ProbabilityTheory.Kernel.iIndepFun
