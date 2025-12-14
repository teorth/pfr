import Mathlib.Data.Finset.Pairwise
import Mathlib.Probability.Independence.Kernel.IndepFun

open MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory.Kernel
variable {ι α β β' γ γ' Ω : Type*} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}
  {κ : Kernel α Ω} {μ : Measure α} {f : Ω → β} {g : Ω → β'}

section iIndepFun

variable {β γ : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {mγ : ∀ i, MeasurableSpace (γ i)}
  {f : ∀ i, Ω → β i}

-- maybe `Fintype J` is not necessary?
/-- If `f` is a family of mutually independent random variables, `(S j)ⱼ` are pairwise disjoint
finite index sets, then the tuples formed by `f i` for `i ∈ S j` are mutually independent,
when seen as a family indexed by `J`. -/
lemma iIndepFun.finsets {J : Type*} [Fintype J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i)) :
    iIndepFun (fun (j : J) ↦ fun a (i : S j) ↦ f i a) κ μ := by
  classical
  set F := fun (j : J) ↦ fun a (i : S j) ↦ f i a
  let M (j : J) := pi (m := fun (i : S j) ↦ m i)
  let πβ (j : J) := Set.pi Set.univ '' Set.pi Set.univ fun (i : S j) => { s | MeasurableSet[m i] s }
  apply iIndepSets.iIndep
  · intro j
    rw [← measurable_iff_comap_le, measurable_pi_iff]
    intro ω
    simpa [F] using hf_meas ω
  · exact fun i ↦ IsPiSystem.comap isPiSystem_pi (F i)
  · intro j
    change MeasurableSpace.comap _ (M j) = _
    have : M j = MeasurableSpace.generateFrom (πβ j) := generateFrom_pi.symm
    rewrite [this, MeasurableSpace.comap_generateFrom] ; rfl
  simp only [iIndepSets, Set.mem_image, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_const,
    Subtype.forall, exists_exists_and_eq_and]
  intro s E hE
  obtain ⟨sets, h_sets⟩ := Classical.axiomOfChoice (fun (j:s) ↦ hE j (Finset.coe_mem j))
  set E' := fun (j:s) (i:S j) ↦ f i ⁻¹' (sets j i)
  have Ej_eq (j : s) : E j = ⋂ (i : S j), E' j i := by rw [← (h_sets j).2]; ext ω; simp [E', F]
  suffices ∀ᵐ a ∂μ, κ a (⋂ j : s, ⋂ (i : S j), E' j i) = ∏ j : s, κ a (⋂ (i : S j), E' j i) by
    convert this with x
    · rw [Set.iInter_subtype]
      congr! with j hj
      exact Ej_eq ⟨j, hj⟩
    rw [Finset.prod_subtype s (p := fun j ↦ j ∈ s)]
    · apply Finset.prod_congr rfl
      intro j _
      rw [Ej_eq j]
    simp only [implies_true]
  set E'' := fun (i:ι) ↦ ⋂ (j:s) (h: i ∈ S j), E' j ⟨i, h⟩
  set h_disjoint' :
      (↑s:Set J).PairwiseDisjoint S := Set.PairwiseDisjoint.subset h_disjoint fun ⦃a⦄ _ ↦ trivial
  set t := Finset.disjiUnion s S h_disjoint'
  have Einter_eq : ⋂ (j:s), ⋂ (i : S j), E' j i = ⋂ i ∈ t, E'' i := by
    ext x
    simp only [Set.mem_iInter, Subtype.forall, E'']
    constructor
    · intro h i _ j hj hi
      exact h j hj i hi
    intro h j hj i hi
    have hit : i ∈ t := by simpa [t] using ⟨j, hj, hi⟩
    exact h i hit j hj hi
  have Ej_mes (j : s) : ∀ᵐ (a : α) ∂μ, (κ a) (⋂ (i : S j), E' j i) = ∏ i : S j, (κ a) (E' j i) := by
    convert Kernel.iIndepFun.meas_biInter hf_Indep (S := S j)
      (s := fun i:ι ↦ if h:i ∈ S j then E' j ⟨i, h⟩ else Set.univ) ?_ with x
    · simp +contextual [Set.iInter_subtype, E']
    · simp [Finset.prod_subtype (S j) (p := fun i ↦ i ∈ S j)]
    · intro i hi
      simp only [hi, ↓reduceDIte, E']
      apply MeasurableSet.preimage ((h_sets j).1 i hi) _
      apply Measurable.of_comap_le le_rfl
  have Einter_mes :
      ∀ᵐ a ∂μ, κ a (⋂ j : s, ⋂ i : S j, E' j i) = ∏ j : s, ∏ i : S j, κ a (E' j i) := by
    rw [Einter_eq]
    convert Kernel.iIndepFun.meas_biInter hf_Indep (S := t) (s := E'') ?_ with x
    · rw [Finset.prod_disjiUnion, Finset.prod_subtype s (p := fun j ↦ j ∈ s)]
      · simp only [Finset.univ_eq_attach, E'']
        apply Finset.prod_congr rfl
        intro i _hi
        rw [← Finset.prod_attach (S i)]
        apply Finset.prod_congr rfl
        intro j _hj
        congr
        have : E' i j = ⋂ i', if i' = i then E' i j else Set.univ := by
          rw [Set.iInter_ite]
          simp
        rw [this]
        apply Set.iInter_congr
        intro i'
        split_ifs with h
        · simp only [h, SetLike.coe_mem, subset_refl, Set.coe_inclusion, Set.iInter_true, E']
          ext x
          constructor
          · intro this
            convert this
          intro this
          convert this
          exact h.symm
        · have empty : IsEmpty ((j:ι) ∈ S i') := by
            rw [IsEmpty.prop_iff]
            contrapose! h
            ext
            exact Set.PairwiseDisjoint.elim_finset (f := S) h_disjoint (by trivial) (by trivial) _
              h j.property
          exact (Set.iInter_of_empty _).symm
      · simp only [implies_true]
      · exact FinsetCoe.fintype s
    · intro i _
      simp only [E'', E']
      apply MeasurableSet.iInter
      intro j
      apply MeasurableSet.iInter
      intro hi
      apply MeasurableSet.preimage ((h_sets j).1 i hi)
      apply Measurable.of_comap_le le_rfl
  rw [← Filter.eventually_all] at Ej_mes
  apply Filter.Eventually.mono (Filter.eventually_and.mpr ⟨Ej_mes, Einter_mes⟩)
  intro x ⟨h1, h2⟩
  rw [h2]
  apply Finset.prod_congr rfl
  intro i _
  rw [h1 i]

/-- If `f` is a family of mutually independent random variables, `(S j)ⱼ` are pairwise disjoint
finite index sets, and `φ j` is a function that maps the tuple formed by `f i` for `i ∈ S j` to a
measurable space `γ j`, then the family of random variables formed by `φ j (f i)_{i ∈ S j}` and
indexed by `J` is iIndep. -/
lemma iIndepFun.finsets_comp {J : Type*} [Fintype J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i))
    (γ : J → Type*) {mγ : ∀ j, MeasurableSpace (γ j)}
    (φ : (j : J) → ((i : S j) → β i) → γ j) (hφ : ∀ j, Measurable (φ j)) :
    iIndepFun (fun (j : J) ↦ fun a ↦ φ j (fun (i : S j) ↦ f i a)) κ μ :=
  (Kernel.iIndepFun.finsets S h_disjoint hf_Indep hf_meas).comp φ hφ

end ProbabilityTheory.Kernel.iIndepFun
