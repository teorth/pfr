import PFR.main
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
  let ι := ElementaryAddCommGroup.linearMap p₁
  obtain ⟨ φ', hφ' ⟩ := LinearMap.exists_rightInverse_of_surjective ι
    (LinearMap.range_eq_top.mpr (AddMonoidHom.addSubgroupMap_surjective π₁ H))
  obtain ⟨ φ, hφ ⟩ := hahn_banach H₀ ((π₂.restrict H).comp φ'.toAddMonoidHom)

  have h_bij : ∀ x : G × G', x ∈ H ↔ (x.1 ∈ H₀ ∧ x.2 - φ x.1 ∈ H₁) := by
    intro x
    constructor

    intro hx
    constructor
    exact AddSubgroup.mem_map_of_mem π₁ hx
    let x₁ : H₀ := { val := x.1, property := AddSubgroup.mem_map_of_mem π₁ hx }
    rw [← hφ x₁]
    let x' : H := { val := x, property := hx } - (φ' x₁)
    have h_ker : x'.val ∈ π₁.ker := by
      show π₁ x - ι.comp φ' x₁ = 0
      rw [hφ', sub_eq_zero, show LinearMap.id x₁ = π₁ x from rfl]
    exact AddSubgroup.mem_map_of_mem (K := H ⊓ π₁.ker) π₂ (Set.mem_inter x'.property h_ker)

    intro hx
    let x1 : H₀ := { val := x.1, property := hx.1 }
    let x2 : H₁ := { val := x.2 - φ x1, property := hx.2 }
    let y : H := φ'.toAddMonoidHom x1
    let z : G × G' := ((0 : G), x.2 - φ x1)
    have h_z : z ∈ H := by
      obtain ⟨ g, hg ⟩ := Set.Nonempty.preimage (Set.singleton_nonempty x2)
        (AddMonoidHom.addSubgroupMap_surjective π₂ (H ⊓ π₁.ker))
      have h_ker : g.val ∈ H ∧ g.val ∈ π₁.ker := AddSubgroup.mem_inf.mp g.property
      have h_gz1 : g.val.1 = z.1 := (AddMonoidHom.mem_ker π₁).mp h_ker.right
      have h_gz2 : g.val.2 = z.2 := by { show p₂ g = x2.val ; rw [← hg]}
      rw [← Prod.ext h_gz1 h_gz2]
      exact h_ker.left
    let z : H := { val := z, property := h_z }
    have h_y : y.val = (x.1, φ x1) := by
      have h_1 : y.val.1 = x.1 := by
        rw [show y.val.1 = ι.comp φ' x1 from rfl, hφ', show LinearMap.id x1 = x.1 from rfl]
      exact Prod.ext h_1 (hφ x1)
    have h_xw : x = y.val + z.val := by
      rw [h_y, show z.val = ((0 : G), x.2 - φ x1) from rfl, Prod.mk_add_mk, add_zero,
        ← add_sub_assoc, add_comm, add_sub_assoc, sub_self, add_zero]
    rw [h_xw]
    exact (y + z).property

  use H₀, H₁, φ
  constructor
  exact h_bij

  have h_bij_prop (x : H₀ × H₁) : (x.1.val, φ x.1.val + x.2.val) ∈ H := by
    have h_x2 : φ x.1.val + x.2.val - φ x.1.val ∈ H₁ := by
      rw [add_comm, add_sub_assoc, sub_self, add_zero]
      exact x.2.property
    exact (h_bij (x.1.val, φ x.1.val + x.2.val)).mpr (And.intro x.1.property h_x2)
  let bij (x : H₀ × H₁) : H := { val := (x.1.val, φ x.1.val + x.2.val), property := h_bij_prop x }
  have h_bij_inv_prop (x : H) : x.val.1 ∈ H₀ ∧ x.val.2 - φ x.val.1 ∈ H₁ :=
    (h_bij x.val).mp x.property
  let bij_inv (x : H) : H₀ × H₁ := (
    { val := x.val.1, property := (h_bij_inv_prop x).1 },
    { val := x.val.2 - φ x.val.1, property := (h_bij_inv_prop x).2 }
  )
  have h_leftinv : Function.LeftInverse bij_inv bij := by
    intro x
    simp_rw [add_comm, add_sub_assoc, sub_self, add_zero]
  have h_rightinv : Function.RightInverse bij_inv bij := by
    intro x
    simp_rw [← add_comm_sub, sub_self, zero_add]
  have h_bij : Function.Bijective bij :=
    Function.bijective_iff_has_inverse.mpr (Exists.intro bij_inv (And.intro h_leftinv h_rightinv))
  rw [← Nat.card_eq_of_bijective bij h_bij, Nat.card_prod H₀ H₁]


def graph (f : G → G') : Set (G×G') := {(x, f x) | x : G}

lemma card_graph (f : G → G') : Nat.card (graph f) = Nat.card G := by
  apply Nat.card_congr ⟨fun p => p.1.1, fun x => ⟨⟨x, f x⟩, ⟨x, rfl⟩⟩,
      by rintro ⟨p, ⟨h, hh⟩⟩; simp[←hh],
      by intro x; simp⟩

@[simp]
lemma mem_graph {f : G → G'} (x : G × G') : x ∈ graph f ↔ f x.1 = x.2 := by
  constructor
  · rintro ⟨_, rfl⟩; rfl
  · refine fun h ↦ ⟨x.1, ?_⟩
    rw[h]

@[simp]
lemma image_fst_graph {f : G → G'} : Prod.fst '' (graph f) = Set.univ := by
  ext x; simp


lemma Nat.card_image_le {α β: Type*} {s : Set α} {f : α → β} (hs : s.Finite) :
    Nat.card (f '' s) ≤ Nat.card s:= sorry

example (a b : Set G) : Nat.card (a ×ˢ b) = Nat.card a * Nat.card b := by
  sorry

#check PFR_conjecture
open Set Fintype in
-- variable [DecidableEq G] [DecidableEq G'] in
/-- Let $f: G \to G'$ be a function, and let $S$ denote the set
$$ S := \{ f(x+y)-f(x)-f(y): x,y \in G \}.$$
Then there exists a homomorphism $\phi: G \to G'$ such that
$$ |\{ f(x) - \phi(x)\}| \leq 4 |S|^{24}.$$ -/
theorem homomorphism_pfr (f : G → G') (S : Set G') (hS: ∀ x y : G, f (x+y) - (f x) - (f y) ∈ S):
  ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ 4 * (Nat.card S:ℝ)^(24:ℝ) ∧ ∀ x : G, (f x) - (φ x) ∈ T := by
  -- A = {(x, f x) | x ∈ G}
  classical
  let A := graph f
  have hA_card : Nat.card ↑A = Nat.card G := card_graph f
  save
  let g (p : G × G') : G × G' := (p.1, f p.1 + p.2)
  let B := A + ({0}×ˢ(-S))--{(x, f x - s) | (x : G) (s : G') (_:s ∈ S)}
  --let B := g '' (Set.univ ×ˢ S)
  have hAB : A + A ⊆ B
  · intro x hx
    obtain ⟨a, a', ha, ha', haa'⟩ := Set.mem_add.mp hx
    simp at ha ha'
    rw [Set.mem_add]
    refine ⟨(x.1, f x.1), (0, -f (a.1 + a'.1) + f a.1 + f a'.1), ?_, ?_⟩
    · simp
    · simp only [singleton_prod, mem_image, mem_neg,
      Prod.mk.injEq, true_and, exists_eq_right, Prod.mk_add_mk,
      add_zero]
      constructor
      · convert hS a.1 a'.1 using 1
        abel
      rw [←Prod.fst_add, ha, ha', add_assoc, ←Prod.snd_add, haa', ←add_assoc, add_neg_self, zero_add]

  have hB_card : Nat.card B ≤ Nat.card S * Nat.card A
  · rw [mul_comm]
    have := Nat.card_add_le A ({0} ×ˢ (-S))
    convert this using 2
    --rw [card_graph]
    · sorry

  have hA_le : Nat.card ((A:Set (G×G'))+(A:Set (G×G'))) ≤ (Nat.card S:ℝ) * Nat.card A
  · norm_cast
    trans Nat.card B
    · apply Nat.card_mono _ hAB
      exact toFinite B
    exact hB_card
  save

  obtain ⟨H, c, hcS, hHA, hAcH⟩ := PFR_conjecture sorry hA_le
  obtain ⟨H₀, H₁, φ, hH₀₁, hH_card⟩ := goursat H
  let c' := (Prod.fst) '' c
  have hc'_card : Nat.card c' ≤ Nat.card c := Nat.card_image_le (toFinite c)
    -- simp_rw [Nat.card_eq_fintype_card, Set.card_image_of_injective, Prod.snd_surjective]
    -- simp only [Nat.card_eq_fintype_card, card_ofFinset, Finset.filter_congr_decidable,
    -- Finset.mem_univ, forall_true_left, Prod.forall, ]
  have h_fstH : Prod.fst '' (H:Set (G × G')) = (H₀ : Set G)
  · ext x
    simp only [mem_image, SetLike.mem_coe, hH₀₁, Prod.exists,
      exists_and_right, exists_and_left, exists_eq_right, and_iff_left_iff_imp]
    intro hx
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
    -- apply (Nat.card_add_le _ _).trans

  have : Nat.card H₁ ≤ 2*(Nat.card S : ℝ)^(12:ℝ)
  · calc
      (Nat.card H₁:ℝ) = (Nat.card H:ℝ) / Nat.card H₀ := by
        rw [hH_card, Nat.cast_mul, mul_div_cancel_left]
        simp
      _ ≤ (Nat.card G : ℝ) / Nat.card H₀ := by
        gcongr
        rw[card_graph f] at hHA
        exact hHA
      _ ≤ 2*(Nat.card S : ℝ)^(12:ℝ) := by
        rw[div_le_iff]
        · apply hG_card_le
        simp[Nat.pos_iff_ne_zero]

  use φ
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
  have : A ⊆ c + (({0} ×ˢ (H₁:Set G')) + {(x, φ x) | x : G})
  · calc
      A ⊆ c + (H : Set _) := hAcH
      _ ⊆ c + (({0} ×ˢ (H₁:Set G')) + {(x, φ x) | x : G}) := add_subset_add_left this

  use (Prod.snd '' c) + (H₁ : Set G')
  sorry
