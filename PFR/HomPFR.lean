import Mathlib.Data.Set.Card
import PFR.ImprovedPFR
import PFR.ForMathlib.Graph
import PFR.Mathlib.LinearAlgebra.Basis.VectorSpace
import PFR.Mathlib.SetTheory.Cardinal.Finite

/-!
# The homomorphism form of PFR

Here we apply (improved) PFR to show that approximate homomorphisms f from a 2-group to a 2-group
are close to actual homomorphisms.  Here, approximate is in the sense that f(x+y)-f(x)-f(y) takes
few values.

## Main results

* `goursat`: A convenient description of the subspaces of $G \times G'$ when $G, G'$ are elementary
  abelian 2-groups.
* `homomorphism_pfr` : If $f : G → G'$ is a map between finite abelian elementary 2-groups such
  that $f(x+y)-f(x)-f(y)$ takes at most $K$ values, then there is a homomorphism $\phi: G \to G'$
  such that $f(x)-\phi(x)$ takes at most $K^{12}$ values.
-/

open Pointwise

variable {G G' : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup G'] [Fintype G']
  [ElementaryAddCommGroup G 2] [ElementaryAddCommGroup G' 2]

/-- Let $H_0$ be a subgroup of $G$.  Then every homomorphism $\phi: H_0 \to G'$ can be extended to a
homomorphism $\tilde \phi: G \to G'$. -/
lemma hahn_banach (H₀ : AddSubgroup G) (φ : H₀ →+ G') : ∃ (φ' : G →+ G'), ∀ x : H₀, φ x = φ' x := by
  let H₀ := AddSubgroup.toZModSubmodule 2 H₀
  let φ := (show H₀ →+ G' from φ).toZModLinearMap 2
  obtain ⟨φ', hφ'⟩ := φ.exists_extend
  use φ'; intro x; show φ x = φ'.comp H₀.subtype x; rw [hφ']

/-- Let $H$ be a subgroup of $G \times G'$.  Then there exists a subgroup $H_0$ of $G$, a
subgroup $H_1$ of $G'$, and a homomorphism $\phi: G \to G'$ such that
$$ H := \{ (x, \phi(x) + y): x \in H_0, y \in H_1 \}.$$
In particular, $|H| = |H_0| |H_1|$. -/
lemma goursat (H : AddSubgroup (G × G')): ∃ (H₀ : AddSubgroup G) (H₁ : AddSubgroup G') (φ : G →+ G'),
    (∀ x : G × G', x ∈ H ↔ (x.1 ∈ H₀ ∧ x.2 - φ x.1 ∈ H₁)) ∧
    (Nat.card H) = (Nat.card H₀) * (Nat.card H₁) := by
  let H := AddSubgroup.toZModSubmodule 2 H
  obtain ⟨S₁, S₂, f, φ, hf, hf_inv⟩ := H.exists_equiv_fst_sndModFst
  use S₁.toAddSubgroup, S₂.toAddSubgroup, φ
  constructor ; swap
  · show Nat.card H = _
    exact Eq.trans (Nat.card_eq_of_bijective f f.bijective) (Nat.card_prod S₁ S₂)
  · intro x
    · constructor
      · intro hx
        let x : H := { val := x, property := hx }
        · constructor
          · exact Set.mem_of_eq_of_mem (hf x).1.symm (f x).1.property
          · exact Set.mem_of_eq_of_mem (hf x).2.symm (f x).2.property
      · intro hx
        · let x₁ : S₁ := { val := x.1, property := hx.1 }
          let x₂ : S₂ := { val := x.2 - φ x.1, property := hx.2 }
          exact Set.mem_of_eq_of_mem (by rw [hf_inv, sub_add_cancel]) (f.symm (x₁, x₂)).property

open Set Fintype

/-- Let $f: G \to G'$ be a function, and let $S$ denote the set
$$ S := \{ f(x+y)-f(x)-f(y): x,y \in G \}.$$
Then there exists a homomorphism $\phi: G \to G'$ such that
$$ |\{f(x) - \phi(x)\}| \leq |S|^{12}. $$ -/
theorem homomorphism_pfr (f : G → G') (S : Set G') (hS: ∀ x y : G, f (x+y) - (f x) - (f y) ∈ S) :
  ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ (Nat.card S) ^ 12 ∧ ∀ x : G, (f x) - (φ x) ∈ T := by
  classical
  have : 0 < Nat.card G := Nat.card_pos
  let A := graph f
  have hA_le : (Nat.card ↥(A + A) : ℝ) ≤ Nat.card S * Nat.card A := by
    let B := A - {0}×ˢS
    have hAB : A + A ⊆ B := by
      intro x hx
      obtain ⟨a, ha, a', ha', haa'⟩ := Set.mem_add.mp hx
      simp at ha ha'
      rw [Set.mem_sub]
      refine ⟨(x.1, f x.1), ?_, (0, f (a.1 + a'.1) - f a.1 - f a'.1), ?_⟩
      · simp
      · simp only [singleton_prod, mem_image, Prod.mk.injEq, true_and,
          exists_eq_right, Prod.mk_sub_mk, sub_zero]
        exact ⟨hS a.1 a'.1,
          by rw [← Prod.fst_add, ha, ha', sub_sub, ← Prod.snd_add, haa', sub_sub_self]⟩
    have hB_card : Nat.card B ≤ Nat.card S * Nat.card A :=
      card_sub_le.trans_eq $ by simp only [mul_comm, Set.card_singleton_prod]
    norm_cast
    exact (Nat.card_mono (toFinite B) hAB).trans hB_card
  have hA_nonempty : A.Nonempty := by use (0, f 0) ; exact ⟨0, rfl⟩
  obtain ⟨H, c, hcS, -, -, hAcH⟩ := PFR_conjecture_improv_aux hA_nonempty hA_le
  have : 0 < Nat.card c := by
    have : c.Nonempty := by
      by_contra! H
      simp only [H, empty_add, subset_empty_iff] at hAcH
      simp [hAcH] at hA_nonempty
    exact this.card_pos c.toFinite
  obtain ⟨H₀, H₁, φ, hH₀₁, hH_card⟩ := goursat H
  have hG_card_le : Nat.card G ≤ Nat.card c * Nat.card H₀ := by
    let c' := (Prod.fst) '' c
    have hc'_card : Nat.card c' ≤ Nat.card c := Nat.card_image_le (toFinite c)
    have h_fstH : Prod.fst '' (H : Set (G × G')) = (H₀ : Set G) := by
      ext x
      simp only [mem_image, SetLike.mem_coe, hH₀₁, Prod.exists,
        exists_and_right, exists_and_left, exists_eq_right, and_iff_left_iff_imp]
      exact fun _ ↦ ⟨φ x, by simp only [sub_self, AddSubgroup.zero_mem]⟩
    have hG_cover : (univ : Set G) = c' + (H₀:Set G) := by
      apply (eq_univ_of_forall (fun g ↦ ?_)).symm
      have := image_subset Prod.fst hAcH
      rw [← AddHom.coe_fst, Set.image_add, AddHom.coe_fst, image_fst_graph] at this
      rw [← h_fstH]
      exact this (mem_univ g)
    apply_fun Nat.card at hG_cover
    rw [Nat.card_coe_set_eq, Set.ncard_univ] at hG_cover
    rw [hG_cover]
    calc
      (Nat.card (c'+ (H₀:Set G))) ≤ Nat.card c' * Nat.card H₀ := card_add_le
      _ ≤ Nat.card c * Nat.card H₀ := by gcongr
  have : (Nat.card H₁ : ℝ) ≤ (Nat.card H / Nat.card A) * Nat.card c := by calc
      (Nat.card H₁ : ℝ) = (Nat.card H : ℝ) / Nat.card H₀ := by field_simp [hH_card, mul_comm]
      _ ≤ (Nat.card H : ℝ) / (Nat.card G / Nat.card c) := by
        gcongr
        rw [div_le_iff' (by positivity)]
        exact_mod_cast hG_card_le
      _ = (Nat.card H / Nat.card G : ℝ) * Nat.card c := by field_simp
      _ = (Nat.card H / Nat.card A) * Nat.card c := by congr; exact (card_graph f).symm
  let T := (fun p ↦ p.2 - φ p.1) '' (c + {0} ×ˢ (H₁: Set G'))
  have : A ⊆ ⋃ (c ∈ T), {(x, φ x + c) | x : G} := by
    have : (H : Set (G × G')) ⊆ ({0} ×ˢ (H₁:Set G')) + {(x, φ x) | x : G} := by
      rintro ⟨g, g'⟩ hg
      simp only [SetLike.mem_coe, hH₀₁] at hg
      refine ⟨(0, g' - φ g), ?_, (g, φ g), ?_⟩
      · simp only [singleton_prod, mem_image, SetLike.mem_coe,
          Prod.mk.injEq, true_and, exists_eq_right, hg.2]
      · simp only [mem_setOf_eq, Prod.mk.injEq, exists_eq_left, Prod.mk_add_mk, zero_add, true_and,
          sub_add_cancel]
    have hA_sub : A ⊆ c + (({0} ×ˢ (H₁:Set G')) + {(x, φ x) | x : G})
    · calc
        A ⊆ c + (H : Set _) := hAcH
        _ ⊆ c + (({0} ×ˢ (H₁:Set G')) + {(x, φ x) | x : G}) := add_subset_add_left this
    rw [← add_assoc] at hA_sub
    convert hA_sub
    rw [← Set.iUnion_add_left_image, ← graph_def]
    simp_rw [graph_add, Set.biUnion_image]
  refine ⟨φ, T, ?_, ?_⟩
  · have : (Nat.card T : ℝ) ≤ (Nat.card S : ℝ) ^ (12 : ℝ) := by calc
      (Nat.card T:ℝ) ≤ Nat.card (c + {(0:G)} ×ˢ (H₁:Set G')) := by
        norm_cast; apply Nat.card_image_le (toFinite _)
      _ ≤ Nat.card c * Nat.card H₁ := by
        norm_cast
        apply card_add_le.trans
        rw [Set.card_singleton_prod] ; rfl
      _ ≤ Nat.card c * ((Nat.card H / Nat.card A) * Nat.card c) := by gcongr
      _ = (Nat.card c) ^ 2 * (Nat.card H / Nat.card A) := by ring
      _ ≤ ((Nat.card S) ^ (6 : ℝ) * (Nat.card A) ^ (1 / 2 : ℝ) * (Nat.card H) ^ (-1 / 2 : ℝ)) ^ 2
          * (Nat.card H / Nat.card A) := by gcongr; exact hcS
      _ = (Nat.card S : ℝ) ^ (12 : ℝ) := by
        rw [← Real.rpow_two, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        have : 0 < Nat.card S := by
          have : S.Nonempty := ⟨f (0 + 0) - f 0 - f 0, hS 0 0⟩
          exact this.card_pos S.toFinite
        have : 0 < Nat.card A := hA_nonempty.card_pos A.toFinite
        have : 0 < Nat.card H := H.coe_nonempty.card_pos $ toFinite _
        rpow_ring
        norm_num
    exact_mod_cast this
  · intro g
    specialize this (⟨g, rfl⟩ : (g, f g) ∈ A)
    simp only [mem_iUnion, mem_setOf_eq, Prod.mk.injEq, exists_eq_left] at this
    obtain ⟨t, ⟨ht, h⟩⟩ := this
    rw [← h]
    convert ht
    abel
