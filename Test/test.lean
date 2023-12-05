import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Function Set BigOperators

namespace ProbabilityTheory

variable {Ω ι ι' : Type*} [MeasurableSpace Ω] {α : ι → Type*} [hι': Nonempty ι']
  {n : (i : ι) → MeasurableSpace (α i)} {f : (i : ι) → Ω → α i}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {hf : (i : ι) → Measurable (f i)}

-- The following lemma has a completely inefficient proof; should be done better

variable {ST : ι' → Finset ι} (hS : Pairwise (Disjoint on ST)) in
lemma exists_indexfn : ∃ K : ι → ι', ∀ k : ι', ∀ i ∈ ST k, K i = k := by
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


variable {ST : ι' → Finset ι} (hS : Pairwise (Disjoint on ST)) in
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
