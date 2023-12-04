import PFR.ForMathlib.Graph
import PFR.Main
import Mathlib.Data.Set.Card

open Pointwise

variable {G G' : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [AddCommGroup G'] [ElementaryAddCommGroup G' 2] [Fintype G']

/-- Let $H_0$ be a subgroup of $G$.  Then every homomorphism $\phi: H_0 \to G'$ can be extended to a homomorphism $\tilde \phi: G \to G'$. -/
lemma hahn_banach (H₀ : AddSubgroup G) (φ : H₀ →+ G') : ∃ (φ' : G →+ G'), ∀ x : H₀, φ x = φ' x := by
  haveI : ElementaryAddCommGroup H₀ 2 := ElementaryAddCommGroup.subgroup _
  let ι := ElementaryAddCommGroup.linearMap H₀.subtype
  have hι : Function.Injective ι :=
    show Function.Injective H₀.subtype from AddSubgroup.subtype_injective H₀
  have : LinearMap.ker ι = ⊥ := by exact LinearMap.ker_eq_bot.mpr hι
  obtain ⟨g,hg⟩ := LinearMap.exists_leftInverse_of_injective ι this
  use φ.comp g.toAddMonoidHom
  intro x
  show φ x = φ ((g.comp ι) x)
  rw [hg]
  rfl

/-- Let $H$ be a subgroup of $G \times G'$.  Then there exists a subgroup $H_0$ of $G$, a subgroup $H_1$ of $G'$, and a homomorphism $\phi: G \to G'$ such that
$$ H := \{ (x, \phi(x) + y): x \in H_0, y \in H_1 \}.$$
In particular, $|H| = |H_0| |H_1|$. -/
lemma goursat (H : AddSubgroup (G × G')): ∃ (H₀ : AddSubgroup G) (H₁ : AddSubgroup G') (φ : G →+ G'),
    (∀ x : G × G', x ∈ H ↔ (x.1 ∈ H₀ ∧ x.2 - φ x.1 ∈ H₁)) ∧
    (Nat.card H) = (Nat.card H₀) * (Nat.card H₁) := by
  let π₁ := AddMonoidHom.fst G G'
  let π₂ := AddMonoidHom.snd G G'
  let p₁ := AddMonoidHom.addSubgroupMap π₁ H
  let p₂ := AddMonoidHom.addSubgroupMap π₂ (H ⊓ π₁.ker)
  let H₀ := AddSubgroup.map π₁ H
  let H₁ := AddSubgroup.map π₂ (H ⊓ π₁.ker)
  have : ElementaryAddCommGroup H 2 := ElementaryAddCommGroup.subgroup H
  have : ElementaryAddCommGroup H₀ 2 := ElementaryAddCommGroup.subgroup H₀
  let p₁' := ElementaryAddCommGroup.linearMap p₁
  obtain ⟨ φ', hφ' ⟩ := LinearMap.exists_rightInverse_of_surjective p₁'
    (LinearMap.range_eq_top.mpr (AddMonoidHom.addSubgroupMap_surjective π₁ H))
  obtain ⟨ φ, hφ ⟩ := hahn_banach H₀ ((π₂.restrict H).comp φ'.toAddMonoidHom)

  let bij (x : H) : G × G' := (x.val.1, x.val.2 - φ x.val.1)
  let bij_inv (x : H₀ × H₁) : G × G' := (x.1.val, φ x.1.val + x.2.val)
  have h_bij' : ∀ x : G × G', x ∈ H ↔ (x.1 ∈ H₀ ∧ x.2 - φ x.1 ∈ H₁) := by
    intro x
    constructor

    intro hx
    let x₁ : H₀ := ⟨ x.1, AddSubgroup.mem_map_of_mem π₁ hx ⟩
    let x₂ : H := { val := x, property := hx } - (φ' x₁)
    have h_ker : x₂.val ∈ π₁.ker := by
      show π₁ x - p₁'.comp φ' x₁ = 0
      rw [sub_eq_zero, hφ', show LinearMap.id x₁ = π₁ x from rfl]
    constructor
    exact AddSubgroup.mem_map_of_mem (K := H) π₁ hx
    rw [← hφ x₁]
    exact AddSubgroup.mem_map_of_mem (K := H ⊓ π₁.ker) π₂ (Set.mem_inter x₂.property h_ker)

    intro hx
    let x₁ : H₀ := ⟨ x.1, hx.left ⟩
    let x₂ : H₁ := ⟨ x.2 - φ x₁, hx.right ⟩
    let xₗ : H := φ' x₁
    let xᵣ : G × G' := (0, x₂.val)
    have hxₗ : xₗ.val = (x.1, φ x₁) := by
      have hx₁ : xₗ.val.1 = x.1 := by
        rw [show xₗ.val.1 = p₁'.comp φ' x₁ from rfl, hφ', show LinearMap.id x₁ = x.1 from rfl]
      exact Prod.ext hx₁ (hφ x₁)
    have hxᵣ : xᵣ ∈ H := by
      obtain ⟨ g, hg ⟩ := Set.Nonempty.preimage (Set.singleton_nonempty x₂)
        (AddMonoidHom.addSubgroupMap_surjective π₂ (H ⊓ π₁.ker))
      have h_ker : g.val ∈ H ∧ g.val ∈ π₁.ker := AddSubgroup.mem_inf.mp g.property
      have hg₁ : g.val.1 = xᵣ.1 := (AddMonoidHom.mem_ker π₁).mp h_ker.right
      have hg₂ : g.val.2 = xᵣ.2 := by { show (p₂ g).val = x₂.val ; rw [← hg] }
      rw [← Prod.ext hg₁ hg₂]
      exact h_ker.left
    let xᵣ : H := ⟨ xᵣ, hxᵣ ⟩
    have hx : x = xₗ.val + xᵣ.val := by
      rw [hxₗ, show xᵣ = _ from rfl, Prod.mk_add_mk, add_zero, ← add_comm_sub, sub_self, zero_add]
    rw [hx]
    exact (xₗ + xᵣ).property

  have h_bij_prop (x : H) : (bij x).1 ∈ H₀ ∧ (bij x).2 ∈ H₁ := (h_bij' x.val).mp x.property
  let bij (x : H) : H₀ × H₁ := (⟨ (bij x).1, (h_bij_prop x).1 ⟩, ⟨ (bij x).2, (h_bij_prop x).2 ⟩)
  have h_bij_inv_prop (x : H₀ × H₁) : bij_inv x ∈ H := (h_bij' (bij_inv x)).mpr
    ⟨ x.1.property, by simp only [x.2.property, add_comm, add_sub_assoc, sub_self, add_zero] ⟩
  let bij_inv (x : H₀ × H₁) : H := ⟨ bij_inv x, h_bij_inv_prop x ⟩
  have h_leftinv : Function.LeftInverse bij_inv bij := fun _ ↦ by
    simp_rw [← add_comm_sub, sub_self, zero_add]
  have h_rightinv : Function.RightInverse bij_inv bij := fun _ ↦ by
    simp_rw [add_comm, add_sub_assoc, sub_self, add_zero]
  have h_bij : Function.Bijective bij :=
    Function.bijective_iff_has_inverse.mpr ⟨ bij_inv, ⟨ h_leftinv, h_rightinv ⟩ ⟩

  use H₀, H₁, φ
  constructor
  exact h_bij'
  rw [Nat.card_eq_of_bijective bij h_bij, Nat.card_prod H₀ H₁]


/- TODO: Find an appropriate home for these lemmas -/
lemma Nat.card_image_le {α β: Type*} {s : Set α} {f : α → β} (hs : s.Finite) :
    Nat.card (f '' s) ≤ Nat.card s := by
  simp only [Set.Nat.card_coe_set_eq]
  exact Set.ncard_image_le hs

lemma Nat.card_singleton_prod {α β : Type*} (a : α) (B : Set β) : Nat.card ({a} ×ˢ B) = Nat.card B := by
  by_cases hB : Set.Finite B
  · rw[Set.singleton_prod, Nat.card_image_of_injective (Prod.mk.inj_left a) hB]
  · rw[Set.Infinite.card_eq_zero hB, Set.Infinite.card_eq_zero <| Set.Infinite.prod_right hB ⟨a,by rfl⟩]

lemma Nat.card_prod_singleton {α β : Type*} (A : Set α) (b : β) : Nat.card (A ×ˢ {b}) = Nat.card A := by
  by_cases hA : Set.Finite A
  · rw[Set.prod_singleton, Nat.card_image_of_injective (Prod.mk.inj_right b) hA]
  · rw[Set.Infinite.card_eq_zero hA, Set.Infinite.card_eq_zero <| Set.Infinite.prod_left hA ⟨b,by rfl⟩]

open Set Fintype in
-- variable [DecidableEq G] [DecidableEq G'] in
/-- Let $f: G \to G'$ be a function, and let $S$ denote the set
$$ S := \{ f(x+y)-f(x)-f(y): x,y \in G \}.$$
Then there exists a homomorphism $\phi: G \to G'$ such that
$$ |\{ f(x) - \phi(x)\}| \leq 4 |S|^{24}.$$ -/
theorem homomorphism_pfr (f : G → G') (S : Set G') (hS: ∀ x y : G, f (x+y) - (f x) - (f y) ∈ S):
  ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ 4 * (Nat.card S:ℝ)^(24:ℝ) ∧ ∀ x : G, (f x) - (φ x) ∈ T := by
  classical
  let A := graph f

  let B := A - {0}×ˢS

  have hAB : A + A ⊆ B
  · intro x hx
    obtain ⟨a, a', ha, ha', haa'⟩ := Set.mem_add.mp hx
    simp at ha ha'
    rw [Set.mem_sub]
    refine ⟨(x.1, f x.1), (0, f (a.1 + a'.1) - f a.1 - f a'.1), ?_, ?_⟩
    · simp
    · simp only [singleton_prod, mem_image, mem_neg,
      Prod.mk.injEq, true_and, exists_eq_right, Prod.mk_sub_mk,
      sub_zero]
      constructor
      · apply hS
      rw [←Prod.fst_add, ha, ha', sub_sub, ←Prod.snd_add, haa', ←sub_add, sub_self, zero_add]

  have hB_card : Nat.card B ≤ Nat.card S * Nat.card A
  · rw [mul_comm]
    simpa only [Nat.card_singleton_prod, Nat.card_neg] using (Nat.card_sub_le A ({0} ×ˢ S))

  have hA_le : Nat.card ((A:Set (G×G'))+(A:Set (G×G'))) ≤ (Nat.card S:ℝ) * Nat.card A
  · norm_cast
    exact (Nat.card_mono (toFinite B) hAB).trans hB_card

  have hA_nonempty : A.Nonempty
  · use (0, f 0)
    exact ⟨0, rfl⟩

  obtain ⟨H, c, hcS, hHA, hAcH⟩ := PFR_conjecture hA_nonempty hA_le
  obtain ⟨H₀, H₁, φ, hH₀₁, hH_card⟩ := goursat H

  let c' := (Prod.fst) '' c
  have hc'_card : Nat.card c' ≤ Nat.card c := Nat.card_image_le (toFinite c)
  have h_fstH : Prod.fst '' (H:Set (G × G')) = (H₀ : Set G)
  · ext x
    simp only [mem_image, SetLike.mem_coe, hH₀₁, Prod.exists,
      exists_and_right, exists_and_left, exists_eq_right, and_iff_left_iff_imp]
    intro _
    use φ x
    simp[AddSubgroup.zero_mem]

  have hG_cover : (univ : Set G) = c' + (H₀:Set G)
  · ext g
    refine ⟨fun _ => ?_, fun _ => mem_univ _⟩
    have := image_subset Prod.fst hAcH
    rw[←AddHom.coe_fst, Set.image_add] at this
    simp_rw[AddHom.coe_fst, image_fst_graph] at this
    rw[←h_fstH]
    convert this (mem_univ g)

  have hc'_card_real : Nat.card c' ≤ (Nat.card c:ℝ)
  · norm_cast

  have hG_card_le : Nat.card G ≤ 2*(Nat.card S:ℝ)^(12:ℝ) * Nat.card H₀
  · apply_fun Nat.card at hG_cover
    rw [Nat.card_coe_set_eq, Set.ncard_univ] at hG_cover
    rw [hG_cover]
    calc
      (Nat.card (c'+ (H₀:Set G)):ℝ) ≤ Nat.card c' * Nat.card H₀ := by norm_cast; apply Nat.card_add_le
      _ ≤  2*(Nat.card S:ℝ)^(12:ℝ) * Nat.card H₀ := by
        gcongr
        apply hc'_card_real.trans
        apply hcS.le

  have : Nat.card H₁ ≤ 2*(Nat.card S : ℝ)^(12:ℝ)
  · calc
      (Nat.card H₁:ℝ) = (Nat.card H:ℝ) / Nat.card H₀ := by
        field_simp[hH_card, mul_comm]
      _ ≤ (Nat.card G : ℝ) / Nat.card H₀ := by
        gcongr
        rw[card_graph f] at hHA
        exact hHA
      _ ≤ 2*(Nat.card S : ℝ)^(12:ℝ) := by
        rw[div_le_iff]
        · apply hG_card_le
        simp[Nat.pos_iff_ne_zero]

  have : (H:Set (G×G')) ⊆ ({0} ×ˢ (H₁:Set G')) + {(x, φ x) | x : G}
  · rintro ⟨g, g'⟩ hg
    rw [SetLike.mem_coe, hH₀₁] at hg
    simp only [] at hg
    rw [Set.mem_add]
    use (0, g' - φ g)
    use (g, φ g)
    refine ⟨?_,?_⟩
    · simp only [singleton_prod, mem_image, SetLike.mem_coe,
        Prod.mk.injEq, true_and, exists_eq_right, hg.2]
    · simp only [mem_setOf_eq, Prod.mk.injEq, exists_eq_left, Prod.mk_add_mk, zero_add, true_and,
        sub_add_cancel]

  have hA_sub : A ⊆ c + (({0} ×ˢ (H₁:Set G')) + {(x, φ x) | x : G})
  · calc
      A ⊆ c + (H : Set _) := hAcH
      _ ⊆ c + (({0} ×ˢ (H₁:Set G')) + {(x, φ x) | x : G}) := add_subset_add_left this
  rw[←add_assoc] at hA_sub

  let T := (fun p ↦ p.2 - φ p.1) '' (c + {0} ×ˢ (H₁: Set G'))
  have : A ⊆ ⋃ (c ∈ T), {(x, φ x + c) | x : G}
  · convert hA_sub
    rw[← Set.iUnion_add_left_image, ←graph_def]
    simp_rw[graph_add, Set.biUnion_image]
  use φ
  use T
  constructor
  · calc
      (Nat.card T:ℝ) ≤ Nat.card (c + {(0:G)} ×ˢ (H₁:Set G')) := by
        norm_cast; apply Nat.card_image_le (toFinite _)
      _ ≤ Nat.card c * Nat.card H₁ := by
        norm_cast
        apply (Nat.card_add_le _ _).trans
        rw[Nat.card_singleton_prod]
        rfl
      _ ≤ (2 * (Nat.card S) ^(12:ℝ)) * (2 * (Nat.card S) ^(12:ℝ)) := by
        gcongr
      _ ≤ _ := by
        ring_nf
        rw[sq, ←Real.rpow_add]
        · norm_num
        · norm_cast
          rw [Nat.card_pos_iff]
          refine ⟨⟨_, hS 0 0⟩, Subtype.finite⟩
  · intro g
    specialize this (⟨g, rfl⟩ : (g, f g) ∈ A)
    simp only [exists_eq_right, iUnion_exists, mem_iUnion, mem_setOf_eq,
      Prod.mk.injEq, exists_eq_left, exists_prop, exists_and_right] at this
    obtain ⟨t, ⟨ht, h⟩⟩ := this
    rw[←h]
    convert ht
    abel
